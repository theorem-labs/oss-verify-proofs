(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02 YK1a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0g YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YN03 YN02_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW01_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW03_cf YW0e_cf YW06_cf YW07_cf YW0c_cf YW09_cf YW08_cf YW0d_cf YY00_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YN3b YN0e_cf YN23_cf YN0i_cf YN10_cf YN06_cf YN0x_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_malloc_stub : fetch_word src0segs (Z_to_bv 64 src0_A_malloc) = Some (0x1910006f%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x1910006f%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_malloc_stub : decode_any (0x1910006f%bv : bv 32) = Some (Jal 0 (Z_to_bv 21 0x990), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma fetch_free_stub : fetch_word src0segs (Z_to_bv 64 src0_A_free) = Some (0x1440006f%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x1440006f%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_free_stub : decode_any (0x1440006f%bv : bv 32) = Some (Jal 0 324, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma step_malloc_stub regs mem :
RiscvSemantics.step src0segs (mkst regs (Z_to_bv 64 src0_A_malloc) mem (seg_rom src0segs)) =
MachineOk (mkst regs (Z_to_bv 64 src0_A_libc_malloc_impl) mem (seg_rom src0segs)).
Proof.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_malloc_stub eq_refl decode_malloc_stub). do 2 f_equal.
Qed.
Lemma step_free_stub regs mem :
RiscvSemantics.step src0segs (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs)) =
MachineOk (mkst regs (Z_to_bv 64 src0_A_libc_free) mem (seg_rom src0segs)).
Proof.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_free_stub eq_refl decode_free_stub). do 2 f_equal.
Qed.
Lemma src0_malloc_impl : malloc_realizes_cf src0_msyms (MRx src0_msyms) -> malloc_impl_realizes.
Proof.
intros HM L A regs mem md n PRE Hra H10 Hn.
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ (proj1 PRE))) as (Hh & Hlz & _).
apply (mreal_cf_step_inv src0segs (mkst regs (Z_to_bv 64 src0_A_malloc) mem (seg_rom src0segs)) md _ (malloc n A) _ Hh Hlz eq_refl (step_malloc_stub regs mem)).
- intros r (L' & regs' & mem' & md' & E & _). apply Hra.
  apply (f_equal (fun c => ms_pc_val (cfg_ms c))) in E. cbn in E. symmetry. exact E.
- exact (HM L A regs mem md n PRE H10 Hn).
Qed.
Lemma src0_free_impl : free_realizes_cf src0_msyms (MRx src0_msyms) -> free_impl_realizes.
Proof.
intros HF L A regs mem md p n PRE Hra Hin H10.
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ (proj1 PRE))) as (Hh & Hlz & _).
apply (mreal_cf_step_inv src0segs (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs)) md _ (free (Some p) A) _ Hh Hlz eq_refl (step_free_stub regs mem)).
- intros r (L' & regs' & mem' & md' & E & _). apply Hra.
  apply (f_equal (fun c => ms_pc_val (cfg_ms c))) in E. cbn in E. symmetry. exact E.
- exact (HF L A regs mem md p n PRE Hin H10).
Qed.
Lemma src0_memcpy_spec : memcpy_spec.
Proof. exact src0_memcpy. Qed.
Theorem src0_realloc_k3b_big : OBL_fb_gen ->
forall pc L A regs mem md p nold n g am idx fr,
ms_realloc src0_msyms = Some pc ->
call_pre_k src0_msyms (MRx src0_msyms) REALLOC_STACK L A regs mem md ->
In (p, nold) (user_blocks A) ->
getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
MMAP_THRESHOLD <= n < 2 ^ 62 ->
usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
fr_n fr = nold -> p = frame_ptr am idx fr -> am_sc am = 63 ->
mreal_cf (ms_segs src0_msyms) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs src0_msyms))) md)
(realloc (Some p) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md p nold n).
Proof using.
intros FB.
exact (src0_realloc_realizes FB src0_realloc_entry src0_realloc_eq (src0_realloc_node src0_realloc_ok src0_realloc_fb)).
Qed.
End a.
