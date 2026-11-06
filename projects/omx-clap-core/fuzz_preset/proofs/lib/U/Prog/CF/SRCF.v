(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module paths and module names changed; 167 of its 193 lines of code are new or changed and 130 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require MState Exec Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue SlotAgree AgreeLift.
Import ListNotations.
Local Open Scope Z_scope.

Definition seg_syms (segs : list Segment) : malloc_syms :=
  MSyms segs (MPcs 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 None None) 0 0 None 0 0 0 0 0 None 0 0 0 0 0 0 None None 0.

Section d. Context {fx : YK11.FPState}.
Section e.
Variable segs : list Segment.

Definition SR (c : config) (Q : config -> Prop) : Prop := SRcf (seg_syms segs) c Q.

Lemma SR_ret : forall c (Q : config -> Prop), Q c -> SR c Q.
Proof. intros c Q HQ. exact (SRcf_ret (seg_syms segs) c Q HQ). Qed.

Lemma SR_bind : forall c (R Q : config -> Prop),
  SR c R -> (forall c', R c' -> SR c' Q) -> SR c Q.
Proof. intros c R Q H1 H2. exact (SRcf_bind (seg_syms segs) c R Q H1 H2). Qed.

Lemma SR_mono : forall c (Q Q' : config -> Prop),
  SR c Q -> (forall c', Q c' -> Q' c') -> SR c Q'.
Proof. intros c Q Q' H HQQ. exact (SRcf_mono (seg_syms segs) c Q Q' H HQQ). Qed.

Lemma SR_msteps : forall ms ms' model Q,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  SR (mkCfg ms' model) Q ->
  SR (mkCfg ms model) Q.
Proof.
  intros ms ms' model Q Hh Hl Hms H T HK.
  exact (crealizes_msteps (seg_syms segs) ms ms' model T Hh Hl Hms (H T HK)).
Qed.

Lemma SR_step : forall ms model ms' Q,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  SR (mkCfg ms' model) Q ->
  SR (mkCfg ms model) Q.
Proof.
  intros ms model ms' Q Hh Hl Hs Hst H.
  apply (SR_msteps ms ms' model Q Hh Hl); [apply msteps_one; [exact Hs | exact Hst] | exact H].
Qed.

Lemma SR_case : forall (A : Prop) c Q,
  (A \/ ~ A) -> (A -> SR c Q) -> (~ A -> SR c Q) -> SR c Q.
Proof. intros A c Q [a|na] H1 H2; auto. Qed.

Lemma SR_wf : forall (W : Type) (R : W -> W -> Prop),
  well_founded R ->
  forall (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR c (fun c' => Q c' \/ exists w', R w' w /\ P w' c')) ->
  forall w c, P w c -> SR c Q.
Proof.
  intros W R Hwf P Q Hbody w.
  induction (Hwf w) as [w _ IH].
  intros c HP. eapply SR_bind; [apply Hbody, HP|].
  intros c' [HQ | (w' & HR & HP')].
  - apply SR_ret, HQ.
  - apply (IH w' HR c' HP').
Qed.

Lemma SR_loop : forall (W : Type) (m : W -> nat)
  (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
  forall w c, P w c -> SR c Q.
Proof.
  intros W m P Q Hbody.
  apply (SR_wf W (fun a b => (m a < m b)%nat)).
  - apply (wf_inverse_image W nat lt m), PeanoNat.Nat.lt_wf_0.
  - exact Hbody.
Qed.

Lemma SR_loopZ : forall (W : Type) (m : W -> Z)
  (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR c (fun c' => Q c' \/ exists w', (0 <= m w' < m w)%Z /\ P w' c')) ->
  forall w c, P w c -> SR c Q.
Proof.
  intros W m P Q Hbody.
  apply (SR_wf W (fun a b => (0 <= m a < m b)%Z)).
  - apply (wf_inverse_image W Z (fun x y => (0 <= x < y)%Z) m). apply Z.lt_wf with (z := 0%Z).
  - exact Hbody.
Qed.

End e.

Lemma SR_SRcf : forall (B : malloc_syms) c (Q : config -> Prop), SR (ms_segs B) c Q -> SRcf B c Q.
Proof. intros B c Q H. exact H. Qed.

Lemma SRcf_SR : forall (B : malloc_syms) c (Q : config -> Prop), SRcf B c Q -> SR (ms_segs B) c Q.
Proof. intros B c Q H. exact H. Qed.

End d.

Lemma evt_SR : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SR segs (mkCfg ms' md) P) -> SR segs (mkCfg ms md) P.
Proof.
  intros segs ms Q md P H Hh Hl K.
  exact (evt_SRcf (seg_syms segs) ms Q md P H Hh Hl K).
Qed.

Lemma evt_SR_canon : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR segs (mkCfg ms' md) P) ->
  SR segs (mkCfg ms md) P.
Proof.
  intros segs ms Q md P H Hh Hl K.
  exact (evt_SR segs ms _ md P (RegisterBridge.canonical_contract_transport segs Q ms H) Hh Hl K).
Qed.

Section KindB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Let segs := ms_segs B.

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

End KindB.

Section Contracts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition free_null_contract : Prop :=
  forall regs mem md,
    YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 0 -> m_halted md = None -> m_vm_lazy md = [] ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => c' = mkCfg (mkst regs (getr regs 1) mem (seg_rom segs)) md).

Section Forms.
Variable F : ResForm.

Definition malloc_contract_r : Prop :=
  forall L A regs mem md n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem -> getr regs 10 = Z_to_bv 64 n ->
    rf_ok F A b -> rf_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
      (malloc_ret_r B API F ALLOC_STACK L A regs mem md n b).

Definition free_contract_r : Prop :=
  forall L A regs mem md p n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    rf_ok F A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rf_ok F A' (rf_free F b n)).

Definition realloc_contract_r (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    rf_ok F A b -> rf_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR REALLOC_STACK L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + k) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\ res mod 16 = 0 /\ fresh_block B res n /\
         (exists b1 b2 c1 c2, blocks L A = b1 ++ (ptr_addr L p, k) :: b2 /\ blocks L' A' = c1 ++ (res, n) :: c2 /\
            c1 ++ c2 = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k', In (q, k') (user_blocks A) -> q <> p -> In (q, k') (user_blocks A')) /\
         (forall i, 0 <= i < Z.min k n -> mbyte segs mem' (res + i) = nth_error old (Z.to_nat i)) /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rf_ok F A' (rf_realloc F b k n)).

Definition realloc_null_contract_r (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 <> Z_to_bv 64 (ms_malloc B) ->
    rf_ok F A b -> rf_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret_r B API F REALLOC_STACK L A regs mem md n b).

End Forms.
End Contracts.
