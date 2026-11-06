(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Monad.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim DriverSim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ NodesLZSound NodesLZMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS A0Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma a0_wx : wx_segs_nowrap asegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Record gst := mkG { g_H : word -> bool; g_P : list word; g_V : VmState -> Prop }.

Definition VA (a : gst) (mo : Model) : Model := perase (g_P a) mo.
Definition INVA (c : config) (a : gst) : Prop :=
  lzframe asegs minvL (g_H a) (g_P a) (cfg_model c) /\ hzero (g_H a) (cfg_ms c)
  /\ g_V a (m_vm (perase (g_P a) (cfg_model c))).
Definition ATNA (n : node) (msF : machine_state) (a : gst) : Prop := at_node asegs n (restrict (g_H a) msF).

Lemma VA_meq : forall a mo, meq (VA a mo) mo.
Proof. intros a mo. unfold VA, meq. rewrite m_fds_perase, m_fs_perase. split; reflexivity. Qed.

Lemma VA_fs : forall a mo, m_fs (VA a mo) = m_fs mo.
Proof. intros a mo. unfold VA. apply m_fs_perase. Qed.

Definition GOODA (n : node) (rsp : resp) : Prop := exists mo mo' evs, nstep n mo rsp mo' evs.

Lemma strip_nocopies : forall eff r ws zs, strip eff = mkEffect r ws zs -> eff_copies eff = [].
Proof. intros eff r ws zs E. change (eff_copies eff) with (eff_copies (strip eff)). rewrite E. reflexivity. Qed.

Ltac nstep_cases ST :=
  cbn in ST; unfold efferr, eff0 in ST;
  repeat match goal with
         | H : context [match ?x with _ => _ end] |- _ => lazymatch x with eff_copies _ => fail | _ => destruct x end
         | H : context [if ?x then _ else _] |- _ => destruct x
         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : exists _, _ |- _ => destruct H
         | H : False |- _ => destruct H
         end;
  unfold open_result, efferr, eff0 in *;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : exists _, _ |- _ => destruct H
         end.

Lemma fdn_nstep_good : forall n mo rsp mo2 evs, fdn n -> nstep n mo rsp mo2 evs -> eff_copies rsp = [].
Proof.
  intros n mo rsp mo2 evs Hn ST. destruct n; cbn in Hn; try (destruct Hn as [[]|[]]); nstep_cases ST.
  all: try (eapply strip_nocopies; eassumption).
Qed.

Lemma m_vm_with_fds : forall f mo, m_vm (with_fds f mo) = m_vm mo. Proof. intros f mo. destruct mo; reflexivity. Qed.
Lemma fdn_nstep_vm : forall n mo rsp mo2 evs, fdn n -> nstep n mo rsp mo2 evs -> m_vm mo2 = m_vm mo.
Proof.
  intros n mo rsp mo2 evs Hn ST. destruct Hn as [Hf|Hx].
  - destruct (DriverSim.fd_transfer n mo mo rsp mo2 evs Hf eq_refl eq_refl ST) as (moB & _ & [[-> _]|(fds & -> & _)]); [reflexivity| apply m_vm_with_fds].
  - destruct n; cbn in Hx, ST; try contradiction.
Qed.

Lemma GOODA_nocopies : forall n rsp, fdn n -> GOODA n rsp -> eff_copies rsp = [].
Proof. intros n rsp Hn (mo & mo' & evs & ST). exact (fdn_nstep_good n mo rsp mo' evs Hn ST). Qed.

Lemma hclean_mrestrict : forall H ms, hclean H ms -> mrestrict H (ms_mem ms) = ms_mem ms.
Proof. intros H ms HC. rewrite <- restrict_mem. rewrite (hclean_restrict_id H ms HC). reflexivity. Qed.

Lemma hclean_nret_nomem : forall H ms r, hclean H ms -> hclean H (nret ms (mkEffect r [] [])).
Proof. intros H ms r HC a Ha. rewrite nret_mem_nomem. exact (HC a Ha). Qed.

Lemma hclean_nret_writes : forall H ms r ws,
  AsanAcct.ranges_avoid H (write_accesses ws) -> hclean H ms -> hclean H (nret ms (mkEffect r ws [])).
Proof. intros H ms r ws HR HC a Ha. rewrite nret_mem_writes, (apply_writes_hidden H ws _ a HR Ha). exact (HC a Ha). Qed.

Lemma GOODA_hclean : forall n H msr rsp,
  H_off_segments asegs H -> fdn n -> at_node asegs n msr -> hclean H msr -> GOODA n rsp -> hclean H (nret msr rsp).
Proof.
  intros n H msr rsp HH Hn HAT HC (mo & mo2 & evs & ST). rewrite <- nret_strip.
  destruct n; cbn in Hn; try (destruct Hn as [[]|[]]); pose proof HAT as HAT'; cbn in HAT; nstep_cases ST.
  all: lazymatch goal with E : strip ?r = _ |- _ => rewrite E end.
  all: try (apply hclean_nret_nomem; exact HC).

  destruct HAT' as (_ & _ & _ & _ & _ & Hc & Hbc & Hwr). pose proof Hwr as (Hb0 & _ & _).
  apply hclean_nret_writes; [| exact HC]. apply ranges_avoid_delivered; [exact Hb0|].
  intros i Hi. rewrite <- (hclean_mrestrict H msr HC) in Hwr. apply (wr_at_visible asegs H HH _ _ _ Hwr).
  lazymatch type of Hi with context [Fs.file_read ?d ?o _] => pose proof (length_file_read_le_count d o count ltac:(lia)) end. lia.
Qed.

Local Notation NSL := (nodesL_sound asegs).

Lemma fdn_nsafeL : forall n mo, fdn n -> nsafeL (LNode n) mo.
Proof. intros n mo Hn. destruct n; cbn in Hn |- *; try tauto; destruct Hn as [[]|[]]. Qed.

Lemma fdn_hideL : forall n rsp H, fdn n -> hideL (LNode n) rsp H = H.
Proof. intros n rsp H Hn. destruct n; cbn in Hn |- *; try reflexivity; destruct Hn as [[]|[]]. Qed.

Lemma fdn_allowL : forall n rsp P, fdn n -> allowL (LNode n) rsp P = P.
Proof. intros n rsp P Hn. destruct n; cbn in Hn |- *; try reflexivity; destruct Hn as [[]|[]]. Qed.

Theorem NODE_A : forall n ms mo a,
  fdn n -> ATNA n ms a -> INVA (mkCfg ms mo) a ->
  (forall e st, sstep_cfg asegs ACFG (mkCfg ms mo) e st ->
      (exists rsp mo', st = SNext (mkCfg (nret ms rsp) mo') /\ nstep n (VA a mo) rsp (VA a mo') e /\ INVA (mkCfg (nret ms rsp) mo') a /\ GOODA n rsp)
   \/ (exists code mo', st = SNext (mkCfg ms mo') /\ nexit n (VA a mo) code (VA a mo')
         /\ e = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code))
  /\ (forall rsp moE' evs, nstep n (VA a mo) rsp moE' evs ->
      exists mo', VA a mo' = moE' /\ sstep_cfg asegs ACFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo')) /\ INVA (mkCfg (nret ms rsp) mo') a /\ GOODA n rsp)
  /\ (forall code moE', nexit n (VA a mo) code moE' ->
      exists mo', VA a mo' = moE' /\ m_halted mo' = Some code
        /\ sstep_cfg asegs ACFG (mkCfg ms mo) [ExitEv code (m_fs moE')] (SNext (mkCfg ms mo')))
  /\ ((exists rsp moE' evs, nstep n (VA a mo) rsp moE' evs) \/ (exists code moE', nexit n (VA a mo) code moE')).
Proof.
  intros n msF mo [H P Vg] Hn HAT (HF & HZ & HV). unfold ATNA, VA, INVA in *. cbn [g_H g_P g_V cfg_ms cfg_model] in *.
  pose proof (fdn_nsafeL n (perase P mo) Hn) as Hsafe.
  change (at_node asegs n (restrict H msF)) with (at_nodeL asegs (LNode n) (restrict H msF)) in HAT.
  split; [|split; [|split]].
  - intros e st Hss.
    destruct (nsl_complete _ _ _ _ _ _ _ _ _ NSL (LNode n) msF mo H P e st HAT HF HZ Hsafe Hss)
      as [(rsp & mo' & -> & Hst & HF' & HZ' & _) | (code & mo' & -> & Hex & -> & Hh')].
    + left. exists rsp, mo'. rewrite fdn_hideL, fdn_allowL in * by exact Hn. cbn in Hst.
      assert (GOODA n rsp) by (eexists _, _, _; exact Hst).
      assert (HV' : Vg (m_vm (perase P mo'))) by (rewrite (fdn_nstep_vm n _ rsp _ e Hn Hst); exact HV). auto 8.
    + right. exists code, mo'. cbn in Hex. auto.
  - intros rsp moE' evs Hst.
    destruct (nsl_sound _ _ _ _ _ _ _ _ _ NSL (LNode n) msF mo H P rsp moE' evs HAT HF HZ Hsafe Hst)
      as (mo' & EQ & Hss & HF' & HZ' & _).
    exists mo'. rewrite fdn_hideL, fdn_allowL in * by exact Hn. assert (GOODA n rsp) by (eexists _, _, _; exact Hst).
    assert (HV' : Vg (m_vm (perase P mo'))) by (rewrite EQ, (fdn_nstep_vm n _ rsp _ evs Hn Hst); exact HV). auto 8.
  - intros code moE' Hex.
    destruct (nsl_exit _ _ _ _ _ _ _ _ _ NSL (LNode n) msF mo H P code moE' HAT HF HZ Hsafe Hex) as (mo' & EQ & Hh & Hss).
    exists mo'. auto.
  - destruct (nsl_progress _ _ _ _ _ _ _ _ _ NSL (LNode n) msF mo H P HAT HF HZ Hsafe) as [L | R]; [left; exact L | right; exact R].
Qed.

Local Notation SEAM := (RealizeS.SEAM asegs gst VA INVA).
Local Notation implS := (RealizeS.implS asegs gst VA INVA ATNA GOODA).

Definition SEAMr (P : machine_state -> gst -> Prop) (msr : machine_state) (a : gst) : Prop :=
  forall msF, hzero (g_H a) msF -> restrict (g_H a) msF = msr ->
    SEAM (fun msF' a' => P (restrict (g_H a') msF') a') msF a.

Definition implSr {R} (t : itree node R) (Q : R -> machine_state -> gst -> Prop) (msr : machine_state) (a : gst) : Prop :=
  forall msF, hzero (g_H a) msF -> restrict (g_H a) msF = msr ->
    implS t (fun r msF' a' => Q r (restrict (g_H a') msF') a') msF a.

Lemma SEAMr_ret : forall (P : machine_state -> gst -> Prop) msr a, P msr a -> SEAMr P msr a.
Proof. intros P msr a HP msF HZ ER. apply SEAM_ret. rewrite ER. exact HP. Qed.

Lemma SEAMr_mono : forall (P P' : machine_state -> gst -> Prop) msr a,
  SEAMr P msr a -> (forall ms' a', P ms' a' -> P' ms' a') -> SEAMr P' msr a.
Proof. intros P P' msr a H HP msF HZ ER. eapply SEAM_mono; [exact (H msF HZ ER)|]. intros ms' a' Q. apply HP. exact Q. Qed.

Lemma SEAMr_bind : forall (P P' : machine_state -> gst -> Prop) msr a,
  SEAMr P msr a -> (forall msr' a', P msr' a' -> SEAMr P' msr' a') -> SEAMr P' msr a.
Proof.
  intros P P' msr a H HP msF HZ ER. eapply SEAM_bind; [exact (H msF HZ ER)|].
  intros msF' a' HPa mo' (HF' & HZ' & HV'). exact (HP _ _ HPa msF' HZ' eq_refl mo' (conj HF' (conj HZ' HV'))).
Qed.

Lemma SEAMr_evt : forall (Pm : machine_state -> Prop) (P : machine_state -> gst -> Prop) msr a,
  evt asegs Pm msr -> (forall msr', Pm msr' -> SEAMr P msr' a) -> SEAMr P msr a.
Proof.
  intros Pm P msr [H Pg Vg] (msr' & HM & HPm) HK msF HZ ER mo (HF & HZ0 & HV0). cbn [g_H g_P g_V cfg_ms cfg_model] in *.
  subst msr.
  eapply (lz_msteps asegs minvL a0_wx (safe_reach asegs _) H Pg msF msr' mo).
  - apply sr_silent_closed.
  - exact HF.
  - exact HM.
  - intros mo' HI' HS' Hcl.
    assert (HF' : lzframe asegs minvL H Pg mo') by (eapply lzframe_same; eassumption).
    assert (HZ' : hzero H (unrestrict H (ms_mem msF) msr')) by (apply hzero_unrestrict; exact HZ).
    assert (ER' : restrict H (unrestrict H (ms_mem msF) msr') = msr') by (apply restrict_unrestrict_clean; exact Hcl).
    assert (HV' : Vg (m_vm (perase Pg mo'))) by (rewrite (perase_same Pg mo mo' HS'); exact HV0).
    pose proof (HK msr' HPm _ HZ' ER' mo' (conj HF' (conj HZ' HV'))) as SR. cbn [g_H g_P g_V] in SR.
    eapply sr_mono; [exact SR|]. intros c' (a' & HI & HM' & HP). exists a'. split; [exact HI|]. split; [|exact HP].
    eapply meq_trans; [|exact HM']. unfold VA. cbn [g_P]. rewrite (perase_same Pg mo mo' HS'). apply meq_refl.
Qed.

Local Notation implL := (ITreeLZ.implL asegs (at_nodeL asegs) hideL).
Local Notation stwfL := (Bridge.stwf nodeL nstepL nexitL nsafeL).

Theorem seam_of_implL {R} : forall (t : itree nodeL R) (Qw : R -> (word -> bool) -> machine_state -> Prop)
    (PP : Model -> R -> Model -> Prop) (P : machine_state -> gst -> Prop) msr a,
  ((forall x, g_H a x = true -> ms_mem msr x = None) -> H_off_segments asegs (g_H a) -> implL (g_H a) t Qw msr) ->
  (forall mo, lzframe asegs minvL (g_H a) (g_P a) mo -> g_V a (m_vm (perase (g_P a) mo)) ->
             stwfL t (perase (g_P a) mo) (PP (perase (g_P a) mo))) ->
  (forall moE r moE', PP moE r moE' -> meq moE moE') ->
  (forall r H' P' msr' moE moE', g_V a (m_vm moE) -> Qw r H' msr' -> PP moE r moE' ->
      exists V', V' (m_vm moE') /\ P msr' (mkG H' P' V')) ->
  SEAMr P msr a.
Proof.
  intros t Qw PP P msr [H Pg Vg] HI HWF HMEQ HQ msF HZ ER mo (HF & HZ0 & HV0). cbn [g_H g_P g_V cfg_ms cfg_model] in *. subst msr.
  assert (CL : forall x, H x = true -> ms_mem (restrict H msF) x = None).
  { intros x Hx. cbn [restrict ms_mem]. unfold mrestrict. rewrite Hx. reflexivity. }
  pose proof (implL_stwf_safe_reach nodeL asegs (at_nodeL asegs) nstepL nexitL minvL nsafeL hideL allowL a0_wx NSL
                t Qw H Pg msF mo (PP (perase Pg mo)) (HI CL (lf_off _ _ _ _ _ HF)) (HWF mo HF HV0) HF HZ0) as SR.
  eapply sr_mono; [exact SR|]. intros [msF' mo'] (r & H' & P' & HQw & HPP & HF' & HZ'). cbn [cfg_ms cfg_model] in *.
  destruct (HQ r H' P' _ _ _ HV0 HQw HPP) as (V' & HV' & HP').
  exists (mkG H' P' V'). split; [split; [assumption| split; assumption]|]. split.
  - unfold VA. cbn [g_P]. exact (HMEQ _ r _ HPP).
  - exact HP'.
Qed.

Lemma implS_intro_INV {R} : forall (t : itree node R) Q msF a,
  (forall mo, INVA (mkCfg msF mo) a -> implS t Q msF a) -> implS t Q msF a.
Proof. intros t Q msF a H. destruct t; cbn; intros mo HINV; exact (H mo HINV mo HINV). Qed.

Lemma dj_ret {R} : forall (Q : R -> machine_state -> gst -> Prop) r msr a, Q r msr a -> implSr (Ret r) Q msr a.
Proof. intros Q r msr a HQ msF HZ ER. apply implS_ret. rewrite ER. exact HQ. Qed.

Lemma dj_mono {R} : forall (t : itree node R) (Q Q' : R -> machine_state -> gst -> Prop) msr a,
  implSr t Q msr a -> (forall r ms' a', Q r ms' a' -> Q' r ms' a') -> implSr t Q' msr a.
Proof. intros t Q Q' msr a H HQ msF HZ ER. eapply implS_mono; [exact (H msF HZ ER)|]. intros r ms' a' X. apply HQ. exact X. Qed.

Lemma dj_seam {R} : forall (t : itree node R) Q (P : machine_state -> gst -> Prop) msr a,
  SEAMr P msr a -> (forall msr' a', P msr' a' -> implSr t Q msr' a') -> implSr t Q msr a.
Proof.
  intros t Q P msr a HS HK msF HZ ER. eapply implS_seam; [exact (HS msF HZ ER)|].
  intros msF' a' HP. apply implS_intro_INV. intros mo' (HF' & HZ' & _). exact (HK _ _ HP msF' HZ' eq_refl).
Qed.

Lemma dj_evt {R} : forall (t : itree node R) Q (Pm : machine_state -> Prop) msr a,
  evt asegs Pm msr -> (forall msr', Pm msr' -> implSr t Q msr' a) -> implSr t Q msr a.
Proof.
  intros t Q Pm msr a HE HK. apply (dj_seam t Q (fun msr' a' => a' = a /\ Pm msr')).
  - eapply SEAMr_evt; [exact HE|]. intros msr' HP. apply SEAMr_ret. auto.
  - intros msr' a' [-> HP]. apply HK. exact HP.
Qed.

Lemma dj_bind {A B} : forall (t : itree node A) (f : A -> itree node B) Q1 Q msr a,
  implSr t Q1 msr a -> (forall x msr' a', Q1 x msr' a' -> implSr (f x) Q msr' a') -> implSr (ITree.bind node t f) Q msr a.
Proof.
  intros t f Q1 Q msr a H HF msF HZ ER. eapply implS_bind; [exact (H msF HZ ER)|].
  intros x msF' a' HQ1. cbn beta in HQ1. apply implS_intro_INV. intros mo' (HF' & HZ' & _). exact (HF x _ a' HQ1 msF' HZ' eq_refl).
Qed.

Lemma dj_node {R} : forall n (k : resp -> itree node R) Q msr a,
  fdn n -> at_node asegs n msr ->
  (forall rsp, GOODA n rsp -> hclean (g_H a) msr -> implSr (k rsp) Q (nret msr rsp) a) ->
  implSr (Vis n k) Q msr a.
Proof.
  intros n k Q msr [H P Vg] Hn HAT HK msF HZ ER. cbn [g_H] in *.
  assert (HC : hclean H msr) by (rewrite <- ER; apply restrict_hclean).
  apply implS_node. apply SEAM_ret. split.
  - unfold ATNA. cbn [g_H]. rewrite ER. exact HAT.
  - intros rsp HG. apply implS_intro_INV. intros mo' (HF' & HZ' & _). cbn [g_H g_P cfg_ms cfg_model] in *.
    apply (HK rsp HG HC (nret msF rsp) HZ'). cbn [g_H].
    pose proof (restrict_nretL_same nodeL hideL (LNode n) rsp H msF (GOODA_nocopies n rsp Hn HG) (fdn_hideL n rsp H Hn)) as E.
    rewrite (fdn_hideL n rsp H Hn) in E. rewrite E, (nretL_same nodeL hideL (LNode n) rsp H) by (apply fdn_hideL; exact Hn).
    rewrite ER. apply hclean_restrict_id. apply (GOODA_hclean n H msr rsp (lf_off _ _ _ _ _ HF') Hn HAT HC HG).
Qed.

Lemma dj_of_impl {R} : forall (t : itree node R) (Q : R -> machine_state -> Prop) msr a,
  fdtree t -> ITree.impl asegs (at_node asegs) t Q msr -> implSr t (fun r msr' a' => Q r msr' /\ a' = a) msr a.
Proof.
  induction t as [r | n k IH]; intros Q msr a Ht HI; cbn [ITree.impl] in HI.
  - eapply dj_evt; [exact HI|]. intros msr' HQ. apply dj_ret. split; [exact HQ| reflexivity].
  - destruct Ht as [Hn Hk]. eapply dj_evt; [exact HI|]. intros ms1 [HAT HK1].
    apply dj_node; [exact Hn| exact HAT|]. intros rsp HG _. apply IH; [apply Hk| apply HK1].
Qed.

From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Shadow Contracts AllocA0.
From Stdlib Require Import Permutation.

Section AJ.
  Context {HC : HasCeiling}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Local Notation PS := (aps FI AI).
  Local Notation BL := (list (AllocIF.block (am_K FI AI))).

  Definition gh (s : PS) : gst := mkG (fst (am_ghost FI AI s)) (snd (am_ghost FI AI s)) (am_vm FI AI s).

  Definition AJA (Q : PS -> BL -> machine_state -> Prop) (msr : machine_state) (s : PS) (LB : BL) : Prop :=
    SEAMr (fun msr' g' => exists s' LB', g' = gh s' /\ Q s' LB' msr') msr (gh s).

  #[using="Type"] Lemma AJA_ret : forall (Q : PS -> BL -> machine_state -> Prop) ms s LB, Q s LB ms -> AJA Q ms s LB.
  Proof. intros Q ms s LB HQ. apply SEAMr_ret. exists s, LB. auto. Qed.

  #[using="Type"] Lemma AJA_mono : forall (P Q : PS -> BL -> machine_state -> Prop) ms s LB,
    AJA P ms s LB -> (forall s' LB' ms', P s' LB' ms' -> Q s' LB' ms') -> AJA Q ms s LB.
  Proof.
    intros P Q ms s LB H HPQ. eapply SEAMr_mono; [exact H|]. intros ms' a' (s' & LB' & E & HP). exists s', LB'. auto.
  Qed.

  #[using="Type"] Lemma AJA_bind : forall (P Q : PS -> BL -> machine_state -> Prop) ms s LB,
    AJA P ms s LB -> (forall s' LB' ms', P s' LB' ms' -> AJA Q ms' s' LB') -> AJA Q ms s LB.
  Proof.
    intros P Q ms s LB H HK. eapply SEAMr_bind; [exact H|]. intros msr' a' (s' & LB' & -> & HP). exact (HK s' LB' msr' HP).
  Qed.

  #[using="Type"] Lemma AJA_evt : forall (P : machine_state -> Prop) (Q : PS -> BL -> machine_state -> Prop) ms s LB,
    evt asegs P ms -> (forall ms', P ms' -> AJA Q ms' s LB) -> AJA Q ms s LB.
  Proof. intros P Q ms s LB HE HK. eapply SEAMr_evt; [exact HE| exact HK]. Qed.

  #[using="Type"] Lemma AJA_perm : forall Q ms s (LB LB' : BL), Permutation LB LB' -> AJA Q ms s LB' -> AJA Q ms s LB.
  Proof. intros Q ms s LB LB' _ H. exact H. Qed.

  Definition JA : a0_judg FI AI := mkAJ FI AI AJA AJA_ret AJA_mono AJA_bind AJA_evt AJA_perm.

  #[using="Type"] Lemma AJA_of_implL {R} : forall (t : itree nodeL R) (Qw : R -> (word -> bool) -> machine_state -> Prop)
      (PP : Model -> R -> Model -> Prop) (Q : PS -> BL -> machine_state -> Prop) msr s LB,
    ((forall x, fst (am_ghost FI AI s) x = true -> ms_mem msr x = None) -> H_off_segments asegs (fst (am_ghost FI AI s)) ->
       implL (fst (am_ghost FI AI s)) t Qw msr) ->
    (forall mo, lzframe asegs minvL (fst (am_ghost FI AI s)) (snd (am_ghost FI AI s)) mo ->
               am_vm FI AI s (m_vm (perase (snd (am_ghost FI AI s)) mo)) ->
               stwfL t (perase (snd (am_ghost FI AI s)) mo) (PP (perase (snd (am_ghost FI AI s)) mo))) ->
    (forall moE r moE', PP moE r moE' -> meq moE moE') ->
    (forall r H' P' msr' moE moE', am_vm FI AI s (m_vm moE) -> Qw r H' msr' -> PP moE r moE' ->
        exists s' LB', am_ghost FI AI s' = (H', P') /\ am_vm FI AI s' (m_vm moE') /\ Q s' LB' msr') ->
    AJA Q msr s LB.
  Proof.
    intros t Qw PP Q msr s LB HI HWF HMEQ HQ. unfold AJA.
    eapply (seam_of_implL t Qw PP); [exact HI | exact HWF | exact HMEQ |].
    intros r H' P' msr' moE moE' HV HQw HPP. destruct (HQ r H' P' msr' moE moE' HV HQw HPP) as (s' & LB' & E & HV' & HQ').
    exists (am_vm FI AI s'). split; [exact HV'|]. exists s', LB'. split; [| exact HQ']. unfold gh. rewrite E. reflexivity.
  Qed.
End AJ.
