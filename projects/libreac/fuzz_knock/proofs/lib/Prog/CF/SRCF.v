(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module paths and module names changed; 167 of its 193 lines of code are new or changed and 130 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/SRCF.v, with its module paths changed; 76 of its 122 lines of code are new or changed and 147 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Exec MState Mem Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require AllocPack.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YK14.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require MState Mem Frame Exec Regs6ss RegisterBridge Bytes.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Img0.
From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Contract AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import AgreeLim AgreeRoom AgreeCap.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Uniform.
From Stdlib Require Import Wf_nat Wellfounded Lia.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0i YM06 YO03.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Exec MState Mem Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Contract FrameAPI KindBGlue AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Export SlotAgree AgreeLift AgreeLim.
Import ListNotations.
Local Open Scope Z_scope.

Definition seg_syms (segs : list Segment) : malloc_syms := MSyms segs (MPcs 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 None None) 0 0 None 0 0 0 0 0 None 0 0 0 0 0 0 None None 0.

Definition crz (segs : list Segment) (c : config) (T : TSet) : Prop := realizes segs c T /\ cut_free segs c /\ uniform segs c.

Definition SR (segs : list Segment) (c : config) (Q : config -> Prop) : Prop :=
  forall T, (forall c', Q c' -> crz segs c' T) -> crz segs c T.

Lemma SR_ret : forall segs c (Q : config -> Prop), Q c -> SR segs c Q.
Proof. intros segs c Q HQ. exact (SRcf_ret (seg_syms segs) c Q HQ). Qed.

Lemma SR_bind : forall segs c (R Q : config -> Prop), SR segs c R -> (forall c', R c' -> SR segs c' Q) ->
  SR segs c Q.
Proof. intros segs c R Q H1 H2. exact (SRcf_bind (seg_syms segs) c R Q H1 H2). Qed.

Lemma SR_mono : forall segs c (Q Q' : config -> Prop), SR segs c Q -> (forall c', Q c' -> Q' c') ->
  SR segs c Q'.
Proof. intros segs c Q Q' H HQ. exact (SRcf_mono (seg_syms segs) c Q Q' H HQ). Qed.

Lemma SR_realizes : forall segs c Q T, SR segs c Q ->
  (forall c', Q c' -> crz segs c' T) -> crz segs c T.
Proof. intros segs c Q T H HK. exact (H T HK). Qed.

Lemma SR_realizes_ms : forall (B : malloc_syms) segs, ms_segs B = segs -> forall c Q T, SR segs c Q ->
  (forall c', Q c' -> crealizes B c' T) -> crealizes B c T.
Proof. intros B segs E c Q T H HK. subst segs. exact (H T HK). Qed.

Lemma SR_msteps : forall segs ms ms' model Q, m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs ms ms' -> SR segs (mkCfg ms' model) Q -> SR segs (mkCfg ms model) Q.
Proof.
  intros segs ms ms' model Q Hh Hl Hms H T HK.
  exact (crealizes_msteps (seg_syms segs) ms ms' model T Hh Hl Hms (H T HK)).
Qed.

Lemma SR_step : forall segs ms model ms' Q, m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms' ->
  SR segs (mkCfg ms' model) Q -> SR segs (mkCfg ms model) Q.
Proof.
  intros segs ms model ms' Q Hh Hl Hs Hst H.
  exact (SR_msteps segs ms ms' model Q Hh Hl (mst_step segs ms ms' ms' Hs Hst (mst_refl segs ms')) H).
Qed.

Lemma SR_case : forall segs (A : Prop) c Q, (A \/ ~ A) -> (A -> SR segs c Q) -> (~ A -> SR segs c Q) ->
  SR segs c Q.
Proof. intros segs A c Q [a|na] H1 H2; [exact (H1 a) | exact (H2 na)]. Qed.

Lemma SR_wf : forall segs (W : Type) (R : W -> W -> Prop), well_founded R ->
  forall (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR segs c (fun c' => Q c' \/ exists w', R w' w /\ P w' c')) ->
  forall w c, P w c -> SR segs c Q.
Proof.
  intros segs W R Hwf P Q Hb w. induction (Hwf w) as [w _ IH]. intros c HP.
  apply (SR_bind segs c _ Q (Hb w c HP)). intros c' [HQ | (w' & HR & HP')].
  - exact (SR_ret segs c' Q HQ).
  - exact (IH w' HR c' HP').
Qed.

Lemma SR_loop : forall segs (W : Type) (m : W -> nat) (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR segs c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
  forall w c, P w c -> SR segs c Q.
Proof.
  intros segs W m P Q Hb. apply (SR_wf segs W (fun a b => (m a < m b)%nat)); [|exact Hb].
  apply (wf_inverse_image W nat lt m), PeanoNat.Nat.lt_wf_0.
Qed.

Lemma SR_loopZ : forall segs (W : Type) (m : W -> Z) (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR segs c (fun c' => Q c' \/ exists w', (0 <= m w' < m w)%Z /\ P w' c')) ->
  forall w c, P w c -> SR segs c Q.
Proof.
  intros segs W m P Q Hb. apply (SR_wf segs W (fun a b => (0 <= m a < m b)%Z)); [|exact Hb].
  apply (wf_inverse_image W Z (fun x y => (0 <= x < y)%Z) m). apply Z.lt_wf with (z := 0%Z).
Qed.

Lemma evt_SR : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SR segs (mkCfg ms' md) P) -> SR segs (mkCfg ms md) P.
Proof. intros segs ms Q md P H Hh Hl K. exact (evt_SRcf (seg_syms segs) ms Q md P H Hh Hl K). Qed.

Lemma evt_SR_canon : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR segs (mkCfg ms' md) P) ->
  SR segs (mkCfg ms md) P.
Proof. intros segs ms Q md P H Hh Hl K. exact (evt_SRcf_canon (seg_syms segs) ms Q md P H Hh Hl K). Qed.

Section KindBcf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Lemma kb_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt segs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom segs) /\ K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom segs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SR segs (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) P) ->
  SR segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SR_canon segs (mkst regs pc mem (seg_rom segs)) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply kb_getr_eqv. exact HR.
Qed.

End KindBcf.
