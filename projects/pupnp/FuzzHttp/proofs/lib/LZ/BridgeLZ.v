(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ.
Import ListNotations.
Import ITree.Exc.

Section BridgeLZ.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable hide : node -> resp -> (word -> bool) -> (word -> bool).
Variable allow : node -> resp -> list word -> list word.
Hypothesis Hwx : wx_segs_nowrap segs.

Notation tshape := (tshape node nstep nexit).
Notation twfP := (twfP node nstep nsafe).
Notation stwf := (stwf node nstep nexit nsafe).
Notation implL := (implL segs at_node hide).
Notation nretL := (@nretL node hide).

Record lzframe (H : word -> bool) (P : list word) (mo : Model) : Prop := mkLZF {
  lf_halt  : m_halted mo = None;
  lf_minv  : minv (perase P mo);
  lf_MInv  : MInv (ivl P) mo;
  lf_cover : lazy_cover H (m_vm_lazy mo) (ivl P);
  lf_al    : P_aligned P;
  lf_off   : H_off_segments segs H }.

#[using="Type"] Lemma lzframe_wf : forall H P mo, lzframe H P mo -> A_wf (ivl P).
Proof. intros H P mo F. apply A_wf_ivl. exact (lf_al _ _ _ F). Qed.

#[using="Type"] Lemma lzframe_same : forall H P mo mo',
  lzframe H P mo -> AsanAcct.MInv (ivl P) mo' -> same_but_materialized mo mo' -> lzframe H P mo'.
Proof.
  intros H P mo mo' [F1 F2 F3 F4 F5 F6] HI HS. pose proof (AsanAcct.same_but_materialized_frame _ _ HS) as FR.
  constructor; auto.
  - destruct FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E & _). rewrite E. exact F1.
  - rewrite (perase_same _ _ _ HS). exact F2.
  - destruct FR as (_ & _ & E & _). rewrite E. exact F4.
Qed.

Record node_soundL : Prop := mkNSL {
  nsl_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;

  nsl_complete : forall n msF mo H P e st,
      at_node n (restrict H msF) -> lzframe H P mo -> hzero H msF -> nsafe n (perase P mo) ->
      sstep_cfg segs ACFG (mkCfg msF mo) e st ->
        (exists rsp mo', st = SNext (mkCfg (nret msF rsp) mo')
           /\ nstep n (perase P mo) rsp (perase (allow n rsp P) mo') e
           /\ lzframe (hide n rsp H) (allow n rsp P) mo' /\ hzero (hide n rsp H) (nret msF rsp)
           /\ restrict (hide n rsp H) (nret msF rsp) = nretL n rsp H (restrict H msF))
     \/ (exists code mo', st = SNext (mkCfg msF mo') /\ nexit n (perase P mo) code (perase P mo')
           /\ e = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code);

  nsl_sound : forall n msF mo H P rsp moE' evs,
      at_node n (restrict H msF) -> lzframe H P mo -> hzero H msF -> nsafe n (perase P mo) ->
      nstep n (perase P mo) rsp moE' evs ->
      exists mo', perase (allow n rsp P) mo' = moE'
        /\ sstep_cfg segs ACFG (mkCfg msF mo) evs (SNext (mkCfg (nret msF rsp) mo'))
        /\ lzframe (hide n rsp H) (allow n rsp P) mo' /\ hzero (hide n rsp H) (nret msF rsp)
        /\ restrict (hide n rsp H) (nret msF rsp) = nretL n rsp H (restrict H msF);
  nsl_exit : forall n msF mo H P code moE',
      at_node n (restrict H msF) -> lzframe H P mo -> hzero H msF -> nsafe n (perase P mo) ->
      nexit n (perase P mo) code moE' ->
      exists mo', perase P mo' = moE' /\ m_halted mo' = Some code
        /\ sstep_cfg segs ACFG (mkCfg msF mo) [ExitEv code (m_fs moE')] (SNext (mkCfg msF mo'));
  nsl_progress : forall n msF mo H P,
      at_node n (restrict H msF) -> lzframe H P mo -> hzero H msF -> nsafe n (perase P mo) ->
      (exists rsp moE' evs, nstep n (perase P mo) rsp moE' evs) \/ (exists code moE', nexit n (perase P mo) code moE') }.

Hypothesis NSL : node_soundL.

#[using="Type"] Lemma node_ok_conv : forall c I evs nx, AsanAcct.node_ok segs c I evs nx -> node_ok segs c I evs nx.
Proof. intros c I evs nx [A B]. split; assumption. Qed.

#[using="Hwx"] Lemma lz_msteps : forall (Pc : config -> Prop) H P msF msr' mo,
  (forall c c', node_ok segs c unit (fun _ => []) (fun _ => c') -> Pc c' -> Pc c) ->
  lzframe H P mo -> msteps segs (restrict H msF) msr' ->
  (forall mo', MInv (ivl P) mo' -> same_but_materialized mo mo' -> hclean H msr' ->
               Pc (mkCfg (unrestrict H (ms_mem msF) msr') mo')) ->
  Pc (mkCfg msF mo).
Proof.
  intros Pc H P msF msr' mo Hsil HF HM HK. pose proof HF as [Hh Hm HI HC HW HO].
  apply (AsanAcct.rz_msteps_restricted' segs H HO Hwx Pc
           (fun c c' Hn Hr => Hsil c c' (node_ok_conv _ _ _ _ Hn) Hr)
           (ivl P) msF msr' mo HC (A_wf_ivl _ HW) HI Hh (msteps_cat segs _ _ HM) HK).
Qed.

#[using="Type"] Lemma rz_silent_closed : forall T c c',
  node_ok segs c unit (fun _ => []) (fun _ => c') -> realizes segs c' T -> realizes segs c T.
Proof. intros T c c' Hn Hr. exact (rz_silent1 segs c c' T Hn Hr). Qed.

#[using="Type"] Lemma sr_silent_closed : forall Q c c',
  node_ok segs c unit (fun _ => []) (fun _ => c') -> safe_reach segs Q c' -> safe_reach segs Q c.
Proof. intros Q c c' Hn Hr. apply (sr_node segs Q c unit (fun _ => c') tt Hn). intros _. exact Hr. Qed.

#[using="Type"] Lemma t_eq_alt_bi {I J} (f : I -> TSet) (g : J -> TSet) :
  (forall i, exists j, t_eq (f i) (g j)) -> (forall j, exists i, t_eq (f i) (g j)) -> t_eq (t_alt f) (t_alt g).
Proof.
  intros FG GF tr. unfold t_alt. split.
  - intros [i Hi]. destruct (FG i) as [j E]. exists j. apply E. exact Hi.
  - intros [j Hj]. destruct (GF j) as [i E]. exists i. apply E. exact Hj.
Qed.

#[using="allow Hwx NSL"] Theorem impl_realizesL {R} : forall (t : itree node R) Q H P msF mo (PP : R -> Model -> Prop) (K : R -> Model -> TSet),
  implL H t Q (restrict H msF) ->
  twfP t (perase P mo) PP ->
  lzframe H P mo -> hzero H msF ->
  (forall r H' P' msF' mo', Q r H' (restrict H' msF') -> PP r (perase P' mo') -> lzframe H' P' mo' -> hzero H' msF' ->
                            realizes segs (mkCfg msF' mo') (K r (perase P' mo'))) ->
  realizes segs (mkCfg msF mo) (tshape t (perase P mo) K).
Proof.
  induction t as [r | n k IH]; intros Q H P msF mo PP K Himpl Hwf HF HZ HK; cbn in Himpl, Hwf; cbn [Bridge.tshape].
  - destruct Himpl as (msr' & Hs & HQ).
    eapply (lz_msteps (fun c => realizes segs c _) H P); [apply rz_silent_closed| exact HF| exact Hs|].
    intros mo' HI' HS' Hcl.
    assert (ER : restrict H (unrestrict H (ms_mem msF) msr') = msr') by (apply AsanAcct.restrict_unrestrict_clean; exact Hcl).
    rewrite <- (perase_same P _ _ HS').
    apply (HK r H P); [rewrite ER; exact HQ| rewrite (perase_same P _ _ HS'); exact Hwf| eapply lzframe_same; eassumption| apply hzero_unrestrict; exact HZ].
  - destruct Himpl as (msr1 & Hs & Hat & Hk). destruct Hwf as [Hsafe Hwk].
    eapply (lz_msteps (fun c => realizes segs c _) H P); [apply rz_silent_closed| exact HF| exact Hs|].
    intros mo1 HI1 HS1 Hcl.
    set (ms1F := unrestrict H (ms_mem msF) msr1).
    assert (ER : restrict H ms1F = msr1) by (subst ms1F; apply AsanAcct.restrict_unrestrict_clean; exact Hcl).
    assert (HF1 : lzframe H P mo1) by (eapply lzframe_same; eassumption).
    assert (HZ1 : hzero H ms1F) by (subst ms1F; apply hzero_unrestrict; exact HZ).
    assert (EE : perase P mo1 = perase P mo) by (apply perase_same; exact HS1).
    rewrite <- EE in Hsafe, Hwk |- *.
    rewrite <- ER in Hat.
    set (moE := perase P mo1) in *.

    set (I1 := { p : resp * Model * list event |
                 sstep_cfg segs ACFG (mkCfg ms1F mo1) (snd p) (SNext (mkCfg (nret ms1F (fst (fst p))) (snd (fst p))))
                 /\ nstep n moE (fst (fst p)) (perase (allow n (fst (fst p)) P) (snd (fst p))) (snd p)
                 /\ lzframe (hide n (fst (fst p)) H) (allow n (fst (fst p)) P) (snd (fst p))
                 /\ hzero (hide n (fst (fst p)) H) (nret ms1F (fst (fst p)))
                 /\ restrict (hide n (fst (fst p)) H) (nret ms1F (fst (fst p))) = nretL n (fst (fst p)) H (restrict H ms1F) }).
    set (I2 := { p : word * Model |
                 sstep_cfg segs ACFG (mkCfg ms1F mo1) [ExitEv (fst p) (m_fs (snd p))] (SNext (mkCfg ms1F (snd p)))
                 /\ nexit n moE (fst p) (perase P (snd p)) /\ m_halted (snd p) = Some (fst p) }).
    set (nx := fun i : I1 + I2 =>
                 match i with
                 | inl (exist _ p _) => mkCfg (nret ms1F (fst (fst p))) (snd (fst p))
                 | inr (exist _ p _) => mkCfg ms1F (snd p)
                 end).
    set (evs := fun i : I1 + I2 =>
                 match i with
                 | inl (exist _ p _) => snd p
                 | inr (exist _ p _) => [ExitEv (fst p) (m_fs (snd p))]
                 end).
    set (TT := fun i : I1 + I2 =>
                 match i with
                 | inl (exist _ p _) => tshape (k (fst (fst p))) (perase (allow n (fst (fst p)) P) (snd (fst p))) K
                 | inr _ => t_nil
                 end).
    assert (Hnode : node_ok segs (mkCfg ms1F mo1) (I1 + I2) evs nx).
    { split.
      * intros [[[[rsp mo'] es] PF] | [[code mo'] PF]]; cbn; destruct PF as (Hss & _); exact Hss.
      * intros e st Hss.
        destruct (nsl_complete NSL n ms1F mo1 H P e st Hat HF1 HZ1 Hsafe Hss)
          as [(rsp & mo' & -> & Hst & HF' & HZ' & ERS) | (code & mo' & -> & Hex & -> & Hh')].
        -- unshelve eexists (inl (exist _ (rsp, mo', e) _)); [cbn; auto 6| cbn; auto].
        -- unshelve eexists (inr (exist _ (code, mo') _)); [cbn; auto| cbn; auto]. }
    assert (Hcont : forall i, realizes segs (nx i) (TT i)).
    { intros [[[[rsp mo'] es] PF] | [[code mo'] PF]]; cbn.
      * destruct PF as (Hss & Hst & HF' & HZ' & ERS). eapply (IH rsp Q (hide n rsp H) (allow n rsp P)).
        -- cbn in ERS. rewrite ERS, ER. apply Hk.
        -- eapply Hwk. exact Hst.
        -- exact HF'.
        -- exact HZ'.
        -- exact HK.
      * destruct PF as (Hss & Hex & Hh'). cbn in Hh'. apply rz_halt. cbn. rewrite Hh'. discriminate. }

    assert (Hi0 : inhabited (I1 + I2)).
    { destruct (nsl_progress NSL n ms1F mo1 H P Hat HF1 HZ1 Hsafe) as [(rsp0 & moE0 & evs0 & Hst0) | (code & moE' & Hex)].
      - destruct (nsl_sound NSL n ms1F mo1 H P rsp0 moE0 evs0 Hat HF1 HZ1 Hsafe Hst0) as (mo' & EQ & Hss & HF' & HZ' & ERS).
        constructor. left. exists (rsp0, mo', evs0). cbn. rewrite EQ. auto 6.
      - destruct (nsl_exit NSL n ms1F mo1 H P code moE' Hat HF1 HZ1 Hsafe Hex) as (mo' & EQ & Hh' & Hss).
        constructor. right. exists (code, mo'). cbn. rewrite <- EQ, m_fs_perase in Hss.
        split; [exact Hss|]. split; [subst moE; rewrite EQ; exact Hex| exact Hh']. }
    destruct Hi0 as [i0].
    apply (rz_conseq segs _ (t_alt (fun i : I1 + I2 => t_emit (evs i) (TT i)))).
    + exact (rz_node segs _ (I1 + I2) evs nx TT i0 Hnode Hcont).
    +
      apply t_eq_alt_bi.
      * intros [[[[rsp mo'] es] PF] | [[code mo'] PF]]; cbn.
        -- destruct PF as (Hss & Hst & HF' & HZ' & ERS). exists (inl (exist _ (rsp, perase (allow n rsp P) mo', es) Hst)). cbn. apply t_eq_refl.
        -- destruct PF as (Hss & Hex & Hh'). exists (inr (exist _ (code, perase P mo') Hex)). cbn. rewrite m_fs_perase. apply t_eq_refl.
      * intros [[[[rsp moE'] es] Hst] | [[code moE'] Hex]]; cbn.
        -- destruct (nsl_sound NSL n ms1F mo1 H P rsp moE' es Hat HF1 HZ1 Hsafe Hst) as (mo' & EQ & Hss & HF' & HZ' & ERS).
           unshelve eexists (inl (exist _ (rsp, mo', es) _)); [cbn; subst moE; rewrite EQ; auto 6| cbn].
           rewrite EQ. apply t_eq_refl.
        -- destruct (nsl_exit NSL n ms1F mo1 H P code moE' Hat HF1 HZ1 Hsafe Hex) as (mo' & EQ & Hh' & Hss).
           unshelve eexists (inr (exist _ (code, mo') _)); [cbn| cbn].
           { rewrite <- EQ, m_fs_perase in Hss. split; [exact Hss|]. split; [subst moE; rewrite EQ; exact Hex| exact Hh']. }
           rewrite <- EQ, m_fs_perase. apply t_eq_refl.
Qed.

Definition lzleaf {R} (Q : R -> (word -> bool) -> machine_state -> Prop) (PP : R -> Model -> Prop) (c : config) : Prop :=
  exists r H P, Q r H (restrict H (cfg_ms c)) /\ PP r (perase P (cfg_model c))
                /\ lzframe H P (cfg_model c) /\ hzero H (cfg_ms c).

#[using="allow Hwx NSL"] Theorem implL_stwf_safe_reach {R} : forall (t : itree node R) Q H P msF mo (PP : R -> Model -> Prop),
  implL H t Q (restrict H msF) ->
  stwf t (perase P mo) PP ->
  lzframe H P mo -> hzero H msF ->
  safe_reach segs (lzleaf Q PP) (mkCfg msF mo).
Proof.
  induction t as [r | n k IH]; intros Q H P msF mo PP Himpl Hwf HF HZ; cbn in Himpl, Hwf.
  - destruct Himpl as (msr' & Hs & HQ).
    eapply (lz_msteps (safe_reach segs _) H P); [apply sr_silent_closed| exact HF| exact Hs|].
    intros mo' HI' HS' Hcl. apply sr_done. exists r, H, P. cbn.
    rewrite (AsanAcct.restrict_unrestrict_clean _ _ _ Hcl), (perase_same P _ _ HS').
    split; [exact HQ|]. split; [exact Hwf|]. split; [eapply lzframe_same; eassumption| apply hzero_unrestrict; exact HZ].
  - destruct Himpl as (msr1 & Hs & Hat & Hk). destruct Hwf as (Hsafe & Hnx & Hwk).
    eapply (lz_msteps (safe_reach segs _) H P); [apply sr_silent_closed| exact HF| exact Hs|].
    intros mo1 HI1 HS1 Hcl.
    set (ms1F := unrestrict H (ms_mem msF) msr1).
    assert (ER : restrict H ms1F = msr1) by (subst ms1F; apply AsanAcct.restrict_unrestrict_clean; exact Hcl).
    assert (HF1 : lzframe H P mo1) by (eapply lzframe_same; eassumption).
    assert (HZ1 : hzero H ms1F) by (subst ms1F; apply hzero_unrestrict; exact HZ).
    assert (EE : perase P mo1 = perase P mo) by (apply perase_same; exact HS1).
    rewrite <- EE in Hsafe, Hnx, Hwk. rewrite <- ER in Hat.

    destruct (nsl_progress NSL n ms1F mo1 H P Hat HF1 HZ1 Hsafe) as [(rsp0 & moE0 & evs0 & Hst0) | (code & moE' & Hex)];
      [| exfalso; exact (Hnx _ _ Hex)].
    destruct (Hwk _ _ _ Hst0) as [-> _].
    destruct (nsl_sound NSL n ms1F mo1 H P rsp0 moE0 [] Hat HF1 HZ1 Hsafe Hst0) as (mo0 & EQ0 & Hss0 & HF0 & HZ0 & ERS0).
    rewrite <- EQ0 in Hst0.
    set (I1 := { p : resp * Model |
                 sstep_cfg segs ACFG (mkCfg ms1F mo1) [] (SNext (mkCfg (nret ms1F (fst p)) (snd p)))
                 /\ nstep n (perase P mo1) (fst p) (perase (allow n (fst p) P) (snd p)) []
                 /\ lzframe (hide n (fst p) H) (allow n (fst p) P) (snd p)
                 /\ hzero (hide n (fst p) H) (nret ms1F (fst p))
                 /\ restrict (hide n (fst p) H) (nret ms1F (fst p)) = nretL n (fst p) H (restrict H ms1F) }).
    apply (sr_node segs _ (mkCfg ms1F mo1) I1 (fun i => mkCfg (nret ms1F (fst (proj1_sig i))) (snd (proj1_sig i)))
             (exist _ (rsp0, mo0) (conj Hss0 (conj Hst0 (conj HF0 (conj HZ0 ERS0)))))).
    + split.
      * intros [[rsp mo'] PF]. cbn. destruct PF as (Hss & _). exact Hss.
      * intros e st Hss.
        destruct (nsl_complete NSL n ms1F mo1 H P e st Hat HF1 HZ1 Hsafe Hss)
          as [(rsp & mo' & -> & Hst & HF' & HZ' & ERS) | (code & mo' & -> & Hex & _)]; [| exfalso; exact (Hnx _ _ Hex)].
        destruct (Hwk _ _ _ Hst) as [-> _].
        unshelve eexists (exist _ (rsp, mo') _); [cbn; auto 6| cbn; auto].
    + intros [[rsp mo'] PF]. cbn. destruct PF as (Hss & Hst & HF' & HZ' & ERS).
      destruct (Hwk _ _ _ Hst) as [_ Hwf'].
      eapply (IH rsp Q (hide n rsp H) (allow n rsp P)); [| exact Hwf'| exact HF'| exact HZ'].
      cbn in ERS. rewrite ERS, ER. apply Hk.
Qed.

End BridgeLZ.
