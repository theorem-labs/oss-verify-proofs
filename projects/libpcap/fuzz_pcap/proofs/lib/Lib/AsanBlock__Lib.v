(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require StdioSymDrive.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim AllocSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AsanBlock.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import StdioSymDrive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance asanblock_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma munrestrict_visible : forall H full m' (a : word), H a = false -> munrestrict H full m' a = m' a.
Proof. intros H full m' a Ha. unfold munrestrict. rewrite Ha. reflexivity. Qed.

Lemma munrestrict_hidden : forall H full m' (a : word), H a = true -> munrestrict H full m' a = full a.
Proof. intros H full m' a Ha. unfold munrestrict. rewrite Ha. reflexivity. Qed.

Lemma mrestrict_visible' : forall H m (a : word), H a = false -> mrestrict H m a = m a.
Proof. intros H m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.

Lemma mrestrict_hidden' : forall H m (a : word), H a = true -> mrestrict H m a = None.
Proof. intros H m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.

Lemma mrestrict_idem : forall H m, mrestrict H (mrestrict H m) = mrestrict H m.
Proof. intros H m. extensionality a. unfold mrestrict. destruct (H a); reflexivity. Qed.

(* [comment removed for export] *)
Lemma mrestrict_munrestrict_clean : forall H full m',
  (forall a, H a = true -> m' a = None) -> mrestrict H (munrestrict H full m') = m'.
Proof.
  intros H full m' Hc. extensionality a. unfold mrestrict, munrestrict.
  destruct (H a) eqn:Ha; [symmetry; apply Hc; exact Ha | reflexivity].
Qed.

Lemma mrestrict_munrestrict : forall H full m', mrestrict H (munrestrict H full m') = mrestrict H m'.
Proof.
  intros H full m'. extensionality a. unfold mrestrict, munrestrict. destruct (H a); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma munrestrict_denot_hidden : forall H E M log (a : word),
  H a = true -> munrestrict H M (mem_denot E (mrestrict H M) log) a = M a.
Proof. intros. apply munrestrict_hidden. assumption. Qed.

Lemma munrestrict_denot_visible : forall H E M log (a : word),
  H a = false -> munrestrict H M (mem_denot E (mrestrict H M) log) a = mem_denot E (mrestrict H M) log a.
Proof. intros. apply munrestrict_visible. assumption. Qed.

(* [comment removed for export] *)
Lemma mrestrict_agree : forall H H' m (a : word), H a = H' a -> mrestrict H m a = mrestrict H' m a.
Proof. intros H H' m a E. unfold mrestrict. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hclean_mkst : forall H R (pc : word) M rom,
  hclean H (mkst R pc (mrestrict H M) rom).
Proof. intros H R pc M rom a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mrestrict_next : forall H R (pc : word) M V rom,
  hclean H (mkst R pc V rom) -> mrestrict H (munrestrict H M V) = V.
Proof. intros H R pc M V rom Hc. apply mrestrict_munrestrict_clean. intros a Ha. exact (Hc a Ha). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Blocks.
  Variable segs : list Segment.
  Variable H : word -> bool.
  Hypothesis HH : H_off_segments segs H.
  Hypothesis Hwx : wx_segs_nowrap segs.

  (* [comment removed for export] *)
  #[using="HH Hwx"] Theorem ms_run_A : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
    scs_denot segs (mrestrict H M) E scs -> scs_denot segs (mrestrict H M) E scs2 ->
    exists R', regs_ok E (s_regs ss') R'
      /\ know_ok segs E (mrestrict H (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss')))) kn'
      /\ msteps segs (restrict H (mkst R (Z_to_bv 64 pc) M rom))
                     (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E (mrestrict H M) (s_log ss')) rom)
      /\ hclean H (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E (mrestrict H M) (s_log ss')) rom).
  Proof.
    intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R Hex Hc HR HK Hsc Hsc2.
    destruct (ms_run segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E (mrestrict H M) rom R Hex Hc HR HK Hsc Hsc2)
      as (R' & HR' & HK' & MS).
    assert (HC : hclean H (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E (mrestrict H M) (s_log ss')) rom)).
    { rewrite <- (restrict_mkst H) in MS. apply (msteps_hclean segs H HH Hwx _ _ MS). apply hclean_mkst. }
    exists R'. split; [exact HR'|]. split; [rewrite (mrestrict_next H R' _ M _ rom HC); exact HK'|].
    rewrite restrict_mkst. split; [exact MS | exact HC].
  Qed.

  (* [comment removed for export] *)
  #[using="HH Hwx"] Theorem rz_run_A : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R (A : list (Z * Z)) model T,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
    scs_denot segs (mrestrict H M) E scs -> scs_denot segs (mrestrict H M) E scs2 ->
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    (forall R' model', regs_ok E (s_regs ss') R' ->
       know_ok segs E (mrestrict H (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss')))) kn' ->
       MInv A model' -> same_but_materialized model model' ->
       realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss'))) rom) model') T) ->
    realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
  Proof.
    intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R A model T Hex Hc HR HK Hsc Hsc2 HL HA HM Hh Hcont.
    destruct (ms_run_A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R Hex Hc HR HK Hsc Hsc2) as (R' & HR' & HK' & MS & HC).
    apply (rz_msteps_restricted_T segs H HH Hwx A (mkst R (Z_to_bv 64 pc) M rom) _ model T HL HA HM Hh MS).
    intros model' HM' HS _. exact (Hcont R' model' HR' HK' HM' HS).
  Qed.

  (* [comment removed for export] *)
  #[using="HH Hwx"] Theorem srz_run_A : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R (A : list (Z * Z)) model T,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
    scs_denot segs (mrestrict H M) E scs -> scs_denot segs (mrestrict H M) E scs2 ->
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    (forall R' model', regs_ok E (s_regs ss') R' ->
       know_ok segs E (mrestrict H (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss')))) kn' ->
       MInv A model' -> same_but_materialized model model' ->
       srealizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss'))) rom) model') T) ->
    srealizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
  Proof.
    intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R A model T Hex Hc HR HK Hsc Hsc2 HL HA HM Hh Hcont.
    destruct (ms_run_A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R Hex Hc HR HK Hsc Hsc2) as (R' & HR' & HK' & MS & HC).
    apply (srz_msteps_restricted_T segs H HH Hwx A (mkst R (Z_to_bv 64 pc) M rom) _ model T HL HA HM Hh MS).
    intros model' HM' HS _. exact (Hcont R' model' HR' HK' HM' HS).
  Qed.

  (* [comment removed for export] *)
  #[using="HH Hwx"] Theorem ts_msteps_restricted : forall (A : list (Z * Z)) msr0 msr',
    msteps segs msr0 msr' ->
    forall ms model,
    msr0 = restrict H ms ->
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    (forall model', MInv A model' -> same_but_materialized model model' -> hclean H msr' ->
                    to_spin segs (unrestrict H (ms_mem ms) msr') model') ->
    to_spin segs ms model.
  Proof.
    intros A msr0 msr' Hms.
    induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH]; intros ms model -> Hcov Hwf Hinv Hh Hk.
    - specialize (Hk model Hinv (same_but_materialized_refl model) (restrict_hclean H ms)).
      rewrite unrestrict_restrict in Hk. exact Hk.
    - rewrite restrict_svc_pending in Hsvc.
      destruct (node_instr_restricted segs H HH Hwx A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
        as (model1 & Hinv1 & Hsame1 & Hcl1 & Hacc & _).
      pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
      apply (ts_step segs ms model (unrestrict H (ms_mem ms) msr1) model1 Hsvc Hacc).
      apply (IH (unrestrict H (ms_mem ms) msr1) model1).
      + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
      + replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
      + exact Hwf.
      + exact Hinv1.
      + replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
      + intros model' Hinv' Hsame' Hcl'. rewrite unrestrict_mem, unrestrict_munrestrict.
        apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame') | exact Hcl'].
  Qed.

  #[using="HH Hwx"] Theorem ts_run_A : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R (A : list (Z * Z)) model,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
    scs_denot segs (mrestrict H M) E scs -> scs_denot segs (mrestrict H M) E scs2 ->
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    (forall R' model', regs_ok E (s_regs ss') R' ->
       know_ok segs E (mrestrict H (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss')))) kn' ->
       MInv A model' -> same_but_materialized model model' ->
       to_spin segs (mkst R' (Z_to_bv 64 (s_pc ss')) (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss'))) rom) model') ->
    to_spin segs (mkst R (Z_to_bv 64 pc) M rom) model.
  Proof.
    intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R A model Hex Hc HR HK Hsc Hsc2 HL HA HM Hh Hcont.
    destruct (ms_run_A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R Hex Hc HR HK Hsc Hsc2) as (R' & HR' & HK' & MS & HC).
    apply (ts_msteps_restricted A _ _ MS (mkst R (Z_to_bv 64 pc) M rom) model eq_refl HL HA HM Hh).
    intros model' HM' HS _. exact (Hcont R' model' HR' HK' HM' HS).
  Qed.

  (* [comment removed for export] *)
  #[using="HH Hwx"] Theorem ts_step_A : forall (A : list (Z * Z)) ms msr' model,
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
    (forall model', MInv A model' -> same_but_materialized model model' -> hclean H msr' ->
                    to_spin segs (unrestrict H (ms_mem ms) msr') model') ->
    to_spin segs ms model.
  Proof.
    intros A ms msr' model HL HA HM Hh Hsvc Hstep Hk.
    destruct (node_instr_restricted segs H HH Hwx A ms msr' model HL HA HM Hh Hsvc Hstep)
      as (model1 & Hinv1 & Hsame1 & Hcl1 & Hacc & _).
    apply (ts_step segs ms model (unrestrict H (ms_mem ms) msr') model1 Hsvc Hacc).
    exact (Hk model1 Hinv1 Hsame1 Hcl1).
  Qed.

  (* [comment removed for export] *)
  #[using="HH Hwx"] Theorem ts_step_A' : forall (A : list (Z * Z)) R (pc : word) M rom R' (pc' : word) V' model,
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    RiscvSemantics.step segs (mkst R pc (mrestrict H M) rom) = MachineOk (mkst R' pc' V' rom) ->
    (forall model', MInv A model' -> same_but_materialized model model' ->
                    mrestrict H (munrestrict H M V') = V' ->
                    to_spin segs (mkst R' pc' (munrestrict H M V') rom) model') ->
    to_spin segs (mkst R pc M rom) model.
  Proof.
    intros A R pc M rom R' pc' V' model HL HA HM Hh Hstep Hk.
    apply (ts_step_A A (mkst R pc M rom) (mkst R' pc' V' rom) model HL HA HM Hh eq_refl).
    - rewrite restrict_mkst. exact Hstep.
    - intros model' HM' HS' HC. exact (Hk model' HM' HS' (mrestrict_next H R' pc' M V' rom HC)).
  Qed.

  (* [comment removed for export] *)
  #[using="HH Hwx"] Theorem ts_msteps_A : forall (A : list (Z * Z)) ms msr' model,
    msteps segs (restrict H ms) msr' ->
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    (forall model', MInv A model' -> same_but_materialized model model' -> hclean H msr' ->
                    to_spin segs (unrestrict H (ms_mem ms) msr') model') ->
    to_spin segs ms model.
  Proof.
    intros A ms msr' model MS HL HA HM Hh Hk.
    exact (ts_msteps_restricted A (restrict H ms) msr' MS ms model eq_refl HL HA HM Hh Hk).
  Qed.

  #[using="HH Hwx"] Theorem ts_msteps_A' : forall (A : list (Z * Z)) R (pc : word) M rom R' (pc' : word) V' model,
    msteps segs (mkst R pc (mrestrict H M) rom) (mkst R' pc' V' rom) ->
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    (forall model', MInv A model' -> same_but_materialized model model' ->
                    mrestrict H (munrestrict H M V') = V' ->
                    to_spin segs (mkst R' pc' (munrestrict H M V') rom) model') ->
    to_spin segs (mkst R pc M rom) model.
  Proof.
    intros A R pc M rom R' pc' V' model MS HL HA HM Hh Hk.
    apply (ts_msteps_A A (mkst R pc M rom) (mkst R' pc' V' rom) model).
    - rewrite restrict_mkst. exact MS.
    - exact HL. - exact HA. - exact HM. - exact Hh.
    - intros model' HM' HS' HC. exact (Hk model' HM' HS' (mrestrict_next H R' pc' M V' rom HC)).
  Qed.

  (* [comment removed for export] *)
  #[using="HH Hwx"] Theorem srz_msteps_A' : forall (A : list (Z * Z)) R (pc : word) M rom R' (pc' : word) V' model T,
    msteps segs (mkst R pc (mrestrict H M) rom) (mkst R' pc' V' rom) ->
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    (forall model', MInv A model' -> same_but_materialized model model' ->
                    mrestrict H (munrestrict H M V') = V' ->
                    srealizes segs (mkCfg (mkst R' pc' (munrestrict H M V') rom) model') T) ->
    srealizes segs (mkCfg (mkst R pc M rom) model) T.
  Proof.
    intros A R pc M rom R' pc' V' model T MS HL HA HM Hh Hk.
    apply (srz_msteps_restricted_T segs H HH Hwx A (mkst R pc M rom) (mkst R' pc' V' rom) model T HL HA HM Hh).
    - rewrite restrict_mkst. exact MS.
    - intros model' HM' HS' HC. exact (Hk model' HM' HS' (mrestrict_next H R' pc' M V' rom HC)).
  Qed.

  #[using="HH Hwx"] Theorem rz_msteps_A' : forall (A : list (Z * Z)) R (pc : word) M rom R' (pc' : word) V' model T,
    msteps segs (mkst R pc (mrestrict H M) rom) (mkst R' pc' V' rom) ->
    lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
    (forall model', MInv A model' -> same_but_materialized model model' ->
                    mrestrict H (munrestrict H M V') = V' ->
                    realizes segs (mkCfg (mkst R' pc' (munrestrict H M V') rom) model') T) ->
    realizes segs (mkCfg (mkst R pc M rom) model) T.
  Proof.
    intros A R pc M rom R' pc' V' model T MS HL HA HM Hh Hk.
    apply (rz_msteps_restricted_T segs H HH Hwx A (mkst R pc M rom) (mkst R' pc' V' rom) model T HL HA HM Hh).
    - rewrite restrict_mkst. exact MS.
    - intros model' HM' HS' HC. exact (Hk model' HM' HS' (mrestrict_next H R' pc' M V' rom HC)).
  Qed.
End Blocks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_incl (A A' : list (Z * Z)) : Prop :=
  forall p : word, page_allowedb A p = true -> page_allowedb A' p = true.

Lemma MInv_mono : forall A A' m,
  A_incl A A' -> (eager_used m + A_bytes A' <= vm_limit (m_vmmaps m))%Z -> MInv A m -> MInv A' m.
Proof.
  intros A A' m Hincl Hb [Hnd Hal Hallow Hlz _]. constructor; try assumption.
  intros p Hp. apply Hincl. apply Hallow. exact Hp.
Qed.

(* [comment removed for export] *)
Section SBM.
  Variables (m m' : Model).
  Hypothesis S : same_but_materialized m m'.
  Let F := same_but_materialized_frame m m' S.
  #[using="S F"] Lemma sbm_vmmaps : m_vmmaps m' = m_vmmaps m.   Proof. exact (proj1 (proj2 F)). Qed.
  #[using="S F"] Lemma sbm_lazy : m_vm_lazy m' = m_vm_lazy m.   Proof. exact (proj1 (proj2 (proj2 F))). Qed.
  #[using="S F"] Lemma sbm_fds : m_fds m' = m_fds m.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 F))))))))). Qed.
  #[using="S F"] Lemma sbm_fs : m_fs m' = m_fs m.
  Proof. pose proof F as G. do 11 (apply proj2 in G). exact (proj1 G). Qed.
  #[using="S F"] Lemma sbm_halted : m_halted m' = m_halted m.
  Proof. pose proof F as G. do 12 (apply proj2 in G). exact (proj1 G). Qed.
  #[using="S F"] Lemma sbm_tid : m_tid m' = m_tid m.
  Proof. pose proof F as G. do 13 (apply proj2 in G). exact G || exact (proj1 G). Qed.
  #[using="S F"] Lemma sbm_lazy_cover : forall H A, lazy_cover H (m_vm_lazy m) A -> lazy_cover H (m_vm_lazy m') A.
  Proof. intros H A HL. rewrite sbm_lazy. exact HL. Qed.
  #[using="S F"] Lemma sbm_eager : eager_used m' = eager_used m.
  Proof. unfold eager_used. rewrite sbm_vmmaps, sbm_lazy. reflexivity. Qed.
End SBM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac run_block_A HR HK HM HL Hh HH Hwx HA fuel stops scr NX :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ (mrestrict ?H ?M) ?kn =>
      lazymatch goal with
      | |- ?REL (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            first
              [ eapply (srz_run_A segs H HH Hwx fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R _ model T)
              | eapply (rz_run_A segs H HH Hwx fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R _ model T) ];
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | exact HL | exact HA | exact HM | exact Hh
            | clear HR HK HM;
              let R' := fresh "R" in let mdl' := fresh "mdl" in let HS := fresh "HS" in
              intros R' mdl' HR HK HM HS; cbn [s_pc s_regs s_log] in HR, HK |- *;
              let M1 := fresh "M" in
              set (M1 := munrestrict H M (mem_denot _ (mrestrict H M) _)) in * ]
          end
        end
      | |- to_spin _ (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (ts_run_A segs H HH Hwx fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R _ model);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | exact HL | exact HA | exact HM | exact Hh
            | clear HR HK HM;
              let R' := fresh "R" in let mdl' := fresh "mdl" in let HS := fresh "HS" in
              intros R' mdl' HR HK HM HS; cbn [s_pc s_regs s_log] in HR, HK |- *;
              let M1 := fresh "M" in
              set (M1 := munrestrict H M (mem_denot _ (mrestrict H M) _)) in * ]
          end
        end
      end
    end
  end.
End AsanBlock.

(* [comment removed for export] *)
Module AsanBootTac.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require StdioSymDrive. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac expose_scs :=
  lazymatch goal with
  | |- scs_denot ?s ?m ?e ?l => let lv := eval lazy in l in change (scs_denot s m e lv)
  | |- _ => idtac
  end.

Ltac run_block_K HR HK HM HL Hh HH Hwx HA RUN CAR :=
  lazymatch type of RUN with
  | sym_exec ?segs ?fuel true ?stops ?scr (SSR ?pc ?sr [] ?kn ?nx None) [] = (?ss', ?scs, ?scr') =>
    lazymatch type of CAR with
    | carry _ _ [] = (?kn', ?scs2, ?hs2) =>
      lazymatch type of HR with
      | regs_ok ?E _ ?R =>
        lazymatch type of HK with
        | know_ok _ _ (mrestrict ?H ?M) _ =>
          lazymatch goal with
          | |- ?REL (mkCfg (mkst R (Z_to_bv 64 pc) M ?rom) ?model) ?T =>
            first
              [ eapply (srz_run_A segs H HH Hwx fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R _ model T)
              | eapply (rz_run_A segs H HH Hwx fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R _ model T) ];
            [ exact RUN | exact CAR | exact HR | exact HK
            | expose_scs; split_foralls
            | expose_scs; split_foralls
            | exact HL | exact HA | exact HM | exact Hh
            | clear HR HK HM;
              let R' := fresh "R" in let mdl' := fresh "mdl" in let HS := fresh "HS" in
              intros R' mdl' HR HK HM HS; cbn [s_pc s_regs s_log] in HR, HK |- *;
              let M1 := fresh "M" in
              set (M1 := munrestrict H M (mem_denot _ (mrestrict H M) _)) in * ]
          | |- to_spin _ (mkst R (Z_to_bv 64 pc) M ?rom) ?model =>
            eapply (ts_run_A segs H HH Hwx fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R _ model);
            [ exact RUN | exact CAR | exact HR | exact HK
            | expose_scs; split_foralls
            | expose_scs; split_foralls
            | exact HL | exact HA | exact HM | exact Hh
            | clear HR HK HM;
              let R' := fresh "R" in let mdl' := fresh "mdl" in let HS := fresh "HS" in
              intros R' mdl' HR HK HM HS; cbn [s_pc s_regs s_log] in HR, HK |- *;
              let M1 := fresh "M" in
              set (M1 := munrestrict H M (mem_denot _ (mrestrict H M) _)) in * ]
          end
        end
      end
    end
  end.
End AsanBootTac.

(* [comment removed for export] *)
Module MallocSymAux.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import StdioSymDrive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance mallocsymaux_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive mmode := MGrow | MUnmap.

(* [comment removed for export] *)
Definition mem_change (md : mmode) (M M' : word -> option byte) (lo n : Z) : Prop :=
  (forall x : word, (bv_unsigned x < lo \/ lo + n <= bv_unsigned x) -> M' x = M x)
  /\ match md with
     | MGrow => mem_grows M M'
     | MUnmap => forall x : word, (lo <= bv_unsigned x < lo + n) -> M' x = None
     end.

Lemma mem_change_zfill : forall M (a n : word),
  mem_change MGrow M (zfill a n M) (bv_unsigned a) (bv_unsigned n).
Proof.
  intros M a n. split.
  - intros x Hx. apply zfill_out. lia.
  - intros x Hx. unfold zfill, zmem. destruct (_ && _)%bool; [discriminate | exact Hx].
Qed.

Lemma mem_change_unfill : forall M (a n : word),
  mem_change MUnmap M (unfill a n M) (bv_unsigned a) (bv_unsigned n).
Proof.
  intros M a n. split.
  - intros x Hx. apply unfill_out. lia.
  - intros x Hx. unfold unfill.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma mem_change_wbytes : forall M (a : word) (bs : list byte),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64) ->
  mem_change MGrow M (wbytes M a bs) (bv_unsigned a) (Z.of_nat (length bs)).
Proof.
  intros M a bs Hnw. split.
  - intros x [Hx | Hx]; [apply wbytes_below; lia | apply wbytes_above; lia].
  - apply wbytes_grows.
Qed.

(* [comment removed for export] *)
Lemma store_ok_ext : forall segs M M' (a : word) n,
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> M' x = M x) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64) ->
  store_ok segs M' a n = store_ok segs M a n.
Proof.
  intros segs M M' a n. revert a. induction n as [|n IH]; intros a Heq Hnw; [reflexivity|].
  cbn [store_ok]. unfold wview at 1 2. rewrite (Heq a) by lia.
  destruct (match M a with Some b => Some b | None => _ end); [|reflexivity].
  pose proof (u64_range a).
  destruct (Z.eq_dec (bv_unsigned a + 1) (2 ^ 64)) as [E|NE].
  - destruct n; [reflexivity | exfalso; lia].
  - assert (Hu : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    apply IH; [intros x Hx; apply Heq; lia | lia].
Qed.

(* [comment removed for export] *)
Definition kapart_b (allkn : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_x allkn ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_x allkn ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_x allkn ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_x allkn ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_x allkn ub uk un b k l
  end.

Definition is_fact_b (K : kentry) : bool :=
  match K with KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true | _ => false end.
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition keep_b (md : mmode) (allkn : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  is_fact_b K
  || (match md with MGrow => kwr_b K | MUnmap => kimg_b K end)
  || kapart_b allkn ub uk un K.

(* [comment removed for export] *)
Definition kn_keep (md : mmode) (allkn kn : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  List.filter (keep_b md allkn ub uk un) kn.

Lemma kapart_b_sound : forall segs E M kn ub uk un K,
  know_ok segs E M kn -> kentry_ok segs E M K -> kapart_b kn ub uk un K = true ->
  is_fact_b K = false ->
  exists ka kl,
    match K with
    | KWord a w _ => ka = a /\ kl = elen w /\ (w <= 8)%nat
    | KZero a n => ka = a /\ kl = n
    | KBlob a n _ => ka = a /\ kl = n
    | KImg lo hi => ka = SA (ELit 0) lo /\ kl = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)
    | KAlign _ _ => True
    | KRange _ _ _ => True
    | KWr a n => ka = a /\ kl = n
    | KDisj _ _ _ _ => True
    | KFill a n _ => ka = a /\ kl = n
    | KUnk a n => ka = a /\ kl = n
    end
    /\ (estart E (SA ub uk) + elenZ E un <= estart E ka \/ estart E ka + elenZ E kl <= estart E (SA ub uk)).
Proof.
  intros segs E M kn ub uk un K Hkn HK Hb Hf.
  destruct K as [[b k] w v|[b k] l|[b k] l bk|lo hi|ae am|re rlo rhi|[b k] n|da1 dn1 da2 dn2|[b k] l c|[b k] l];
    cbn [kapart_b is_fact_b] in *; try discriminate.
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    exists (SA b k), (elen w). split; [repeat split; auto|].
    pose proof (ranges_apart_x_sound segs E M kn ub uk un b k (ELit (Z.of_nat w)) Hkn Hb) as A. unfold elen. exact A.
  - exists (SA b k), l. split; [auto|]. exact (ranges_apart_x_sound segs E M kn ub uk un b k l Hkn Hb).
  - exists (SA b k), l. split; [auto|]. exact (ranges_apart_x_sound segs E M kn ub uk un b k l Hkn Hb).
  - apply andb_prop in Hb as [Hb Hrg]. apply andb_prop in Hb as [Hb Hlh]. apply andb_prop in Hb as [H0 Hlohi].
    apply Z.ltb_lt in Hlh. unfold two64 in Hlh.
    exists (SA (ELit 0) lo), (ELit (hi - lo)). split; [repeat split; auto; lia|].
    exact (ranges_apart_x_sound segs E M kn ub uk un (ELit 0) lo (ELit (hi - lo)) Hkn Hrg).
  - exists (SA b k), n. split; [auto|]. exact (ranges_apart_x_sound segs E M kn ub uk un b k n Hkn Hb).
  - exists (SA b k), l. split; [auto|]. exact (ranges_apart_x_sound segs E M kn ub uk un b k l Hkn Hb).
  - exists (SA b k), l. split; [auto|]. exact (ranges_apart_x_sound segs E M kn ub uk un b k l Hkn Hb).
Qed.

(* [comment removed for export] *)
Lemma kentry_ok_mem_agree : forall segs E M M' K ka kl,
  kentry_ok segs E M K ->
  match K with
  | KWord a w _ => ka = a /\ kl = elen w /\ (w <= 8)%nat
  | KZero a n => ka = a /\ kl = n
  | KBlob a n _ => ka = a /\ kl = n
  | KImg lo hi => ka = SA (ELit 0) lo /\ kl = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)
  | KAlign _ _ => True
  | KRange _ _ _ => True
  | KWr a n => ka = a /\ kl = n
  | KDisj _ _ _ _ => True
  | KFill a n _ => ka = a /\ kl = n
  | KUnk a n => ka = a /\ kl = n
  end ->
  (is_fact_b K = false -> forall x : word, estart E ka <= bv_unsigned x < estart E ka + elenZ E kl -> M' x = M x) ->
  kentry_ok segs E M' K.
Proof.
  intros segs E M M' K ka kl HK Hshape Hag.
  destruct K as [[b k] w v|[b k] l|[b k] l bk|lo hi|ae am|re rlo rhi|[b k] n|da1 dn1 da2 dn2|[b k] l c|[b k] l];
    cbn [kentry_ok is_fact_b] in *; try exact HK.
  - destruct Hshape as (-> & -> & Hw). destruct HK as (Hw8 & Hfl & Hrd). split; [exact Hw8|]. split; [exact Hfl|].
    rewrite <- Hrd. pose proof (flat_u E (SA b k) _ Hfl) as Hu.
    unfold elen, elenZ in Hag. cbn [edenot] in Hag. rewrite u_small in Hag by lia.
    destruct Hfl as (F1 & F2 & F3 & F4).
    apply rdn_ext; [rewrite Hu; lia|]. intros x Hx. apply Hag; [reflexivity|]. rewrite Hu in Hx. lia.
  - destruct Hshape as (-> & ->). destruct HK as [Hfl Hz]. split; [exact Hfl|].
    intros i Hi. rewrite (Hag eq_refl); [apply Hz; exact Hi|].
    destruct Hfl as (F1 & F2 & F3 & F4). rewrite u_small by lia. lia.
  - destruct Hshape as (-> & ->). destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|].
    intros i Hi. rewrite (Hag eq_refl); [apply Hz; exact Hi|].
    destruct Hfl as (F1 & F2 & F3 & F4). rewrite u_small by lia. lia.
  - destruct Hshape as (-> & -> & Hhl). destruct HK as (H0 & Hhi & Hz). split; [exact H0|]. split; [exact Hhi|].
    intros i Hi. rewrite (Hag eq_refl); [apply Hz; exact Hi|].
    unfold estart, elenZ. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    rewrite !u_small by lia. lia.
  - destruct Hshape as (-> & ->). destruct HK as [Hfl Hst]. split; [exact Hfl|].
    intros d m Hd Hm. rewrite <- (Hst d m Hd Hm).
    destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_ext; [| rewrite u_small by lia; lia].
    intros x Hx. apply Hag; [reflexivity|]. rewrite u_small in Hx by lia. lia.
  - destruct Hshape as (-> & ->). destruct HK as [Hfl Hz]. split; [exact Hfl|].
    intros i Hi. rewrite (Hag eq_refl); [apply Hz; exact Hi|].
    destruct Hfl as (F1 & F2 & F3 & F4). rewrite u_small by lia. lia.
  - destruct Hshape as (-> & ->). destruct HK as [Hfl Hz]. split; [exact Hfl|].
    intros i Hi. rewrite (Hag eq_refl); [apply Hz; exact Hi|].
    destruct Hfl as (F1 & F2 & F3 & F4). rewrite u_small by lia. lia.
Qed.

Theorem kn_keep_sound : forall segs E M M' md allkn kn ub uk un,
  know_ok segs E M allkn -> know_ok segs E M kn ->
  mem_change md M M' (estart E (SA ub uk)) (elenZ E un) ->
  know_ok segs E M' (kn_keep md allkn kn ub uk un).
Proof.
  intros segs E M M' md allkn kn ub uk un Hall Hkn [Hout Hmd].
  unfold kn_keep. apply Forall_forall. intros K HK.
  apply filter_In in HK as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) Hkn K Hin) as HK.
  unfold keep_b in Hkeep.
  destruct (is_fact_b K) eqn:Hf.
  { destruct K; cbn [is_fact_b] in Hf; try discriminate; exact HK. }
  cbn [orb] in Hkeep. apply orb_prop in Hkeep as [Hsp | Hap].
  - destruct md.
    + (* [comment removed for export] *)
      destruct K; cbn [kwr_b] in Hsp; try discriminate.
      cbn [kentry_ok] in *. destruct HK as [Hfl Hst]. split; [exact Hfl|].
      intros d m Hd Hm. eapply store_ok_mono; [exact Hmd | apply Hst; assumption].
    + (* [comment removed for export] *)
      destruct K; cbn [kimg_b] in Hsp; try discriminate.
      cbn [kentry_ok] in *. destruct HK as (H0 & Hhi & Hz). split; [exact H0|]. split; [exact Hhi|].
      intros i Hi. pose proof (u64_range (Z_to_bv 64 i)) as Hr.
      destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 i)) (estart E (SA ub uk))) as [Hl|Hge].
      * rewrite Hout by lia. apply Hz. exact Hi.
      * destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 i)) (estart E (SA ub uk) + elenZ E un)) as [Hl2|Hge2].
        -- apply Hmd. lia.
        -- rewrite Hout by lia. apply Hz. exact Hi.
  - destruct (kapart_b_sound segs E M allkn ub uk un K Hall HK Hap Hf) as (ka & kl & Hshape & Hdis).
    eapply kentry_ok_mem_agree; [exact HK | exact Hshape |].
    intros _ x Hx. apply Hout. lia.
Qed.

Lemma know_ok_nil : forall segs E M, know_ok segs E M [].
Proof. intros. constructor. Qed.

(* [comment removed for export] *)
Lemma kzero_zfill : forall segs E M (e : expr) (a n : word),
  edenot E e = a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  kentry_ok segs E (zfill a n M) (KZero (SA e 0) (ELit (bv_unsigned n))).
Proof.
  intros segs E M e a n He Hn Hnw. pose proof (u64_range a). pose proof (u64_range n).
  eapply kzero_intro; [exact He | cbn [edenot]; apply u_small; lia | lia | lia | lia |].
  intros i Hi. unfold zfill, zmem. rewrite u_small by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma kwr_zfill : forall segs E M (e : expr) (a n : word),
  edenot E e = a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  kentry_ok segs E (zfill a n M) (KWr (SA e 0) (ELit (bv_unsigned n))).
Proof.
  intros segs E M e a n He Hn Hnw. pose proof (u64_range a). pose proof (u64_range n).
  cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite He, u_small by lia.
  split; [lia|]. intros d m Hd Hm. destruct m as [|m']; [reflexivity|].
  unfold zfill. apply store_ok_zmem; rewrite u_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma kzero_zfill_off : forall segs E M (e : expr) (off : Z) (a n : word),
  bv_unsigned (edenot E e) + off = bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  kentry_ok segs E (zfill a n M) (KZero (SA e off) (ELit (bv_unsigned n))).
Proof.
  intros segs E M e off a n He Hn Hnw. pose proof (u64_range a). pose proof (u64_range n).
  cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite He, u_small by lia.
  split; [lia|]. intros i Hi. unfold zfill, zmem. rewrite u_small by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma kwr_zfill_off : forall segs E M (e : expr) (off : Z) (a n : word),
  bv_unsigned (edenot E e) + off = bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  kentry_ok segs E (zfill a n M) (KWr (SA e off) (ELit (bv_unsigned n))).
Proof.
  intros segs E M e off a n He Hn Hnw. pose proof (u64_range a). pose proof (u64_range n).
  cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite He, u_small by lia.
  split; [lia|]. intros d m Hd Hm. destruct m as [|m']; [reflexivity|].
  unfold zfill. apply store_ok_zmem; rewrite u_small by lia; lia.
Qed.
End MallocSymAux.
