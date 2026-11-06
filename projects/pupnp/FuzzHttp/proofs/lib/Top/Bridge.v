(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach.
Import ListNotations.
Import ITree.Exc.

Section Bridge.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : node_sound node segs ACFG at_node nstep nexit minv nsafe.

Definition mframe (mo : Model) : Prop := m_halted mo = None /\ minv mo.

#[using="node segs at_node nstep nexit nsafe NS"] Lemma mframe_nolazy : forall mo, mframe mo -> m_vm_lazy mo = [].
Proof. intros mo [_ H]. exact (ns_nolazy _ _ _ _ _ _ _ _ NS mo H). Qed.

#[using="node at_node nstep nexit nsafe NS"] Lemma sr_mstep : forall Q ms ms' mo,
  mframe mo -> mstep segs ms ms' ->
  safe_reach segs Q (mkCfg ms' mo) -> safe_reach segs Q (mkCfg ms mo).
Proof.
  intros Q ms ms' mo HF [Hsvc Hst] H. destruct HF as [Hh Hm].
  eapply sr_step; eauto. exact (ns_nolazy _ _ _ _ _ _ _ _ NS mo Hm).
Qed.

#[using="node at_node nstep nexit nsafe NS"] Lemma sr_msteps : forall Q ms ms' mo,
  mframe mo -> msteps segs ms ms' ->
  safe_reach segs Q (mkCfg ms' mo) -> safe_reach segs Q (mkCfg ms mo).
Proof.
  intros Q ms ms' mo HF H. induction H; intros HK; [exact HK|].
  eapply sr_mstep; eauto.
Qed.

#[using="node at_node nstep nexit nsafe NS"] Lemma sr_evt : forall (P : machine_state -> Prop) Q ms mo,
  mframe mo ->
  evt segs P ms ->
  (forall ms', P ms' -> safe_reach segs Q (mkCfg ms' mo)) ->
  safe_reach segs Q (mkCfg ms mo).
Proof.
  intros P Q ms mo HF (ms' & Hs & HP) K. eapply sr_msteps; eauto.
Qed.

Fixpoint stwf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo
               /\ (forall code mo', ~ nexit n mo code mo')
               /\ (forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ stwf (k rsp) mo' P)
  end.

#[using="Type"] Lemma stwf_mono {R} : forall (t : itree node R) mo (P P' : R -> Model -> Prop),
  stwf t mo P -> (forall r mo', P r mo' -> P' r mo') -> stwf t mo P'.
Proof.
  induction t as [r | n k IH]; intros mo P P' H HP; cbn in *.
  - auto.
  - destruct H as (Hs & Hx & Hk). split; [exact Hs|]. split; [exact Hx|].
    intros rsp mo' evs Hn. destruct (Hk rsp mo' evs Hn) as [-> Hk']. split; [reflexivity|].
    eapply IH; eauto.
Qed.

#[using="Type"] Lemma stwf_bind {A B} : forall (t : itree node A) (f : A -> itree node B) mo P,
  stwf t mo (fun a mo' => stwf (f a) mo' P) -> stwf (@bind node A B t f) mo P.
Proof.
  induction t as [r | n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as (Hs & Hx & Hk). split; [exact Hs|]. split; [exact Hx|].
    intros rsp mo' evs Hn. destruct (Hk rsp mo' evs Hn) as [-> Hk']. split; [reflexivity|].
    apply IH. exact Hk'.
Qed.

Definition sresp (n : node) (mo : Model) : Type :=
  { p : resp * Model | nstep n mo (fst p) (snd p) [] }.

#[using="NS"] Theorem impl_stwf_safe_reach {R} : forall (t : itree node R) Q ms mo (P : R -> Model -> Prop),
  impl segs at_node t Q ms ->
  stwf t mo P ->
  mframe mo ->
  safe_reach segs
    (fun c => exists r, Q r (cfg_ms c) /\ P r (cfg_model c) /\ mframe (cfg_model c))
    (mkCfg ms mo).
Proof.
  induction t as [r | n k IH]; intros Q ms mo P Himpl Hwf HF; cbn in Himpl, Hwf.
  - eapply sr_evt; [exact HF| exact Himpl|]. intros ms' HQ. apply sr_done. cbn. exists r. auto.
  - eapply sr_evt; [exact HF| exact Himpl|]. intros ms1 [Hat Hk].
    destruct Hwf as (Hsafe & Hnx & Hwk). destruct HF as [Hh Hm].

    destruct (ns_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hm Hsafe) as [(rsp0 & mo0 & evs0 & Hst0) | (code & mo' & Hex)];
      [| exfalso; exact (Hnx _ _ Hex)].
    destruct (Hwk _ _ _ Hst0) as [-> _].
    apply (sr_node segs _ (mkCfg ms1 mo) (sresp n mo)
             (fun i => mkCfg (nret ms1 (fst (proj1_sig i))) (snd (proj1_sig i)))
             (exist _ (rsp0, mo0) Hst0)).
    + split.
      * intros [[rsp mo'] Hst]. cbn.
        destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' [] Hat Hh Hm Hsafe Hst) as (_ & _ & Hss). exact Hss.
      * intros e st Hss.
        destruct (ns_complete _ _ _ _ _ _ _ _ NS n ms1 mo e st Hat Hh Hm Hsafe Hss)
          as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & _)]; [| exfalso; exact (Hnx _ _ Hex)].
        destruct (Hwk _ _ _ Hst) as [-> _].
        exists (exist _ (rsp, mo') Hst). cbn. auto.
    + intros [[rsp mo'] Hst]. cbn.
      destruct (Hwk _ _ _ Hst) as [_ Hwf'].
      destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' [] Hat Hh Hm Hsafe Hst) as (Hh' & Hm' & _).
      eapply IH; [apply Hk| exact Hwf'| split; assumption].
Qed.

Section WithRm.
Variable Rm : Model -> Model -> Prop.
Hypothesis Rm_refl : forall mo, Rm mo mo.
Hypothesis Rm_trans : forall a b c, Rm a b -> Rm b c -> Rm a c.

Fixpoint stwfR {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo
               /\ (forall code mo', ~ nexit n mo code mo')
               /\ (forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ Rm mo mo' /\ stwfR (k rsp) mo' P)
  end.

#[using="Type"] Lemma stwfR_stwf {R} : forall (t : itree node R) mo P, stwfR t mo P -> stwf t mo P.
Proof.
  induction t as [r | n k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as (Hs & Hx & Hk). split; [exact Hs|]. split; [exact Hx|].
  intros rsp mo' evs Hn. destruct (Hk rsp mo' evs Hn) as (E & _ & Hk'). split; [exact E|]. apply IH. exact Hk'.
Qed.

#[using="NS Rm_refl Rm_trans"] Theorem impl_stwfR_safe_reach {R} : forall (t : itree node R) Q ms mo (P : R -> Model -> Prop),
  impl segs at_node t Q ms ->
  stwfR t mo P ->
  mframe mo ->
  safe_reach segs
    (fun c => exists r, Q r (cfg_ms c) /\ P r (cfg_model c) /\ mframe (cfg_model c) /\ Rm mo (cfg_model c))
    (mkCfg ms mo).
Proof.
  induction t as [r | n k IH]; intros Q ms mo P Himpl Hwf HF; cbn in Himpl, Hwf.
  - eapply sr_evt; [exact HF| exact Himpl|]. intros ms' HQ. apply sr_done. cbn. exists r. auto.
  - eapply sr_evt; [exact HF| exact Himpl|]. intros ms1 [Hat Hk].
    destruct Hwf as (Hsafe & Hnx & Hwk). destruct HF as [Hh Hm].
    destruct (ns_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hm Hsafe) as [(rsp0 & mo0 & evs0 & Hst0) | (code & mo' & Hex)];
      [| exfalso; exact (Hnx _ _ Hex)].
    destruct (Hwk _ _ _ Hst0) as [-> _].
    apply (sr_node segs _ (mkCfg ms1 mo) (sresp n mo)
             (fun i => mkCfg (nret ms1 (fst (proj1_sig i))) (snd (proj1_sig i)))
             (exist _ (rsp0, mo0) Hst0)).
    + split.
      * intros [[rsp mo'] Hst]. cbn.
        destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' [] Hat Hh Hm Hsafe Hst) as (_ & _ & Hss). exact Hss.
      * intros e st Hss.
        destruct (ns_complete _ _ _ _ _ _ _ _ NS n ms1 mo e st Hat Hh Hm Hsafe Hss)
          as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & _)]; [| exfalso; exact (Hnx _ _ Hex)].
        destruct (Hwk _ _ _ Hst) as [-> _].
        exists (exist _ (rsp, mo') Hst). cbn. auto.
    + intros [[rsp mo'] Hst]. cbn.
      destruct (Hwk _ _ _ Hst) as (_ & HR & Hwf').
      destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' [] Hat Hh Hm Hsafe Hst) as (Hh' & Hm' & _).
      eapply sr_mono; [eapply IH; [apply Hk| exact Hwf'| split; assumption]|].
      intros c (r & HQ & HP & HF' & HR'). exists r. split; [exact HQ|]. split; [exact HP|]. split; [exact HF'|].
      eapply Rm_trans; eauto.
Qed.
End WithRm.
End Bridge.

Section BridgeRz.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : node_sound node segs ACFG at_node nstep nexit minv nsafe.

Fixpoint twfP {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ (forall rsp mo' evs, nstep n mo rsp mo' evs -> twfP (k rsp) mo' P)
  end.

#[using="Type"] Lemma twfP_mono {R} : forall (t : itree node R) mo (P P' : R -> Model -> Prop),
  twfP t mo P -> (forall r mo', P r mo' -> P' r mo') -> twfP t mo P'.
Proof.
  induction t as [r | n k IH]; intros mo P P' H HP; cbn in *; [auto|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hn. eapply IH; eauto.
Qed.

#[using="Type"] Lemma twfP_bind {A B} : forall (t : itree node A) (f : A -> itree node B) mo P,
  twfP t mo (fun a mo' => twfP (f a) mo' P) -> twfP (@bind node A B t f) mo P.
Proof.
  induction t as [r | n k IH]; intros f mo P H; cbn in *; [exact H|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hn. apply IH. eauto.
Qed.

Definition nindex (n : node) (mo : Model) : Type :=
  ({ p : resp * Model * list event | nstep n mo (fst (fst p)) (snd (fst p)) (snd p) }
   + { p : word * Model | nexit n mo (fst p) (snd p) })%type.

Definition ni_evs (n : node) (mo : Model) (i : nindex n mo) : list event :=
  match i with
  | inl (exist _ p _) => snd p
  | inr (exist _ p _) => [ExitEv (fst p) (m_fs (snd p))]
  end.

Fixpoint tshape {R} (t : itree node R) (mo : Model) (K : R -> Model -> TSet) : TSet :=
  match t with
  | Ret r => K r mo
  | Vis n k =>
      t_alt (fun i : nindex n mo =>
               t_emit (ni_evs n mo i)
                 (match i with
                  | inl (exist _ p _) => tshape (k (fst (fst p))) (snd (fst p)) K
                  | inr _ => t_nil
                  end))
  end.

#[using="Type"] Lemma realizes_msteps : forall ms ms' mo T,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  msteps segs ms ms' -> realizes segs (mkCfg ms' mo) T -> realizes segs (mkCfg ms mo) T.
Proof.
  intros ms ms' mo T Hh Hlz Hs. induction Hs; intros HR; [exact HR|].
  destruct H as [Hsvc Hst]. eapply rz_step; eauto.
Qed.

#[using="NS"] Theorem impl_realizes {R} : forall (t : itree node R) Q ms mo (P : R -> Model -> Prop) (K : R -> Model -> TSet),
  impl segs at_node t Q ms ->
  twfP t mo P ->
  mframe minv mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> mframe minv mo' -> realizes segs (mkCfg ms' mo') (K r mo')) ->
  realizes segs (mkCfg ms mo) (tshape t mo K).
Proof.
  induction t as [r | n k IH]; intros Q ms mo P K Himpl Hwf HF HK; cbn in Himpl, Hwf; cbn [tshape].
  - destruct HF as [Hh Hm]. destruct Himpl as (ms' & Hs & HQ).
    eapply realizes_msteps; [exact Hh| exact (ns_nolazy _ _ _ _ _ _ _ _ NS mo Hm)| exact Hs|].
    apply (HK r _ _ HQ Hwf). split; assumption.
  - destruct HF as [Hh Hm]. destruct Himpl as (ms1 & Hs & Hat & Hk).
    destruct Hwf as [Hsafe Hwk].
    eapply realizes_msteps; [exact Hh| exact (ns_nolazy _ _ _ _ _ _ _ _ NS mo Hm)| exact Hs|].
    set (nx := fun i : nindex n mo =>
                 match i with
                 | inl (exist _ p _) => mkCfg (nret ms1 (fst (fst p))) (snd (fst p))
                 | inr (exist _ p _) => mkCfg ms1 (snd p)
                 end).
    set (TT := fun i : nindex n mo =>
                 match i with
                 | inl (exist _ p _) => tshape (k (fst (fst p))) (snd (fst p)) K
                 | inr _ => t_nil
                 end).
    assert (Hnode : node_ok segs (mkCfg ms1 mo) (nindex n mo) (ni_evs n mo) nx).
    { split.
      * intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hex]]; cbn.
        -- destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hm Hsafe Hst) as (_ & _ & Hss). exact Hss.
        -- destruct (ns_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hm Hsafe Hex) as [_ Hss]. exact Hss.
      * intros e st Hss.
        destruct (ns_complete _ _ _ _ _ _ _ _ NS n ms1 mo e st Hat Hh Hm Hsafe Hss)
          as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & ->)].
        -- exists (inl (exist _ (rsp, mo', e) Hst)). cbn. auto.
        -- exists (inr (exist _ (code, mo') Hex)). cbn. auto. }
    assert (Hcont : forall i, realizes segs (nx i) (TT i)).
    { intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hex]]; cbn.
      * destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hm Hsafe Hst) as (Hh' & Hm' & _).
        eapply IH; [apply Hk| eapply Hwk; exact Hst| split; assumption| exact HK].
      * destruct (ns_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hm Hsafe Hex) as [Hh' _].
        apply rz_halt. cbn. rewrite Hh'. discriminate. }
    change (realizes segs (mkCfg ms1 mo) (t_alt (fun i : nindex n mo => t_emit (ni_evs n mo i) (TT i)))).
    destruct (ns_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hm Hsafe) as [(rsp0 & mo0 & evs0 & Hst0) | (code & mo' & Hex)].
    + exact (rz_node segs _ (nindex n mo) (ni_evs n mo) nx TT (inl (exist _ (rsp0, mo0, evs0) Hst0)) Hnode Hcont).
    + exact (rz_node segs _ (nindex n mo) (ni_evs n mo) nx TT (inr (exist _ (code, mo') Hex)) Hnode Hcont).
Qed.

End BridgeRz.
