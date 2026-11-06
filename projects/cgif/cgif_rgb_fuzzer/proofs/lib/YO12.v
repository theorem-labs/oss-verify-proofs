(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YQ0k YN06 YK0s YN02 YK1a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0r YP0u YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO02 YO03 YO2f YO30
YO16 YO0y YO0z YO14 YO11
YO10 YO15
YO3m YO0f YO28 YO0i YO19 YO07 YO0x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma fetch_malloc_stub : fetch_word src2segs (Z_to_bv 64 src2_A_malloc) = Some (0x1910006f%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x1910006f%bv : bv 32)). apply src2tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_malloc_stub : decode_any (0x1910006f%bv : bv 32) = Some (Jal 0 (Z_to_bv 21 0x990), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma fetch_free_stub : fetch_word src2segs (Z_to_bv 64 src2_A_free) = Some (0x1440006f%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x1440006f%bv : bv 32)). apply src2tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_free_stub : decode_any (0x1440006f%bv : bv 32) = Some (Jal 0 324, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma step_malloc_stub regs mem :
RiscvSemantics.step src2segs (mkst regs (Z_to_bv 64 src2_A_malloc) mem (seg_rom src2segs)) =
MachineOk (mkst regs (Z_to_bv 64 src2_A_libc_malloc_impl) mem (seg_rom src2segs)).
Proof.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_malloc_stub eq_refl decode_malloc_stub). do 2 f_equal.
Qed.
Lemma step_free_stub regs mem :
RiscvSemantics.step src2segs (mkst regs (Z_to_bv 64 src2_A_free) mem (seg_rom src2segs)) =
MachineOk (mkst regs (Z_to_bv 64 src2_A_libc_free) mem (seg_rom src2segs)).
Proof.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_free_stub eq_refl decode_free_stub). do 2 f_equal.
Qed.
Lemma src2_malloc_impl : malloc_realizes src2_msyms (MRx src2_msyms) -> malloc_impl_realizes.
Proof.
intros HM L A regs mem md n PRE H10 Hn.
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ (proj1 PRE))) as (Hh & Hlz & _).
apply (mreal_step_inv src2segs (mkst regs (Z_to_bv 64 src2_A_malloc) mem (seg_rom src2segs)) md _ (malloc n A) _ Hh Hlz eq_refl (step_malloc_stub regs mem)).
exact (HM L A regs mem md n PRE H10 Hn).
Qed.
Lemma src2_free_impl : free_realizes src2_msyms (MRx src2_msyms) -> free_impl_realizes.
Proof.
intros HF L A regs mem md p n PRE Hin H10.
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ (proj1 PRE))) as (Hh & Hlz & _).
apply (mreal_step_inv src2segs (mkst regs (Z_to_bv 64 src2_A_free) mem (seg_rom src2segs)) md _ (free (Some p) A) _ Hh Hlz eq_refl (step_free_stub regs mem)).
exact (HF L A regs mem md p n PRE Hin H10).
Qed.
Lemma src2_memcpy_spec : memcpy_spec.
Proof. exact src2_memcpy. Qed.
Theorem src2_realloc_of_api :
malloc_realizes src2_msyms (MRx src2_msyms) -> free_realizes src2_msyms (MRx src2_msyms) ->
realloc_realizes src2_msyms (MRx src2_msyms).
Proof.
intros HM HF.
exact (src2_realloc_realizes (src2_malloc_impl HM) (src2_free_impl HF) src2_memcpy_spec
src2_realloc_entry src2_realloc_eq (src2_realloc_node src2_realloc_ok src2_realloc_fb)).
Qed.
Theorem src2_realloc : realloc_realizes src2_msyms (MRx src2_msyms).
Proof.
exact (src2_realloc_of_api (src2_malloc_realizes_of_hyps src2_alloc_meta src2_alloc_slot) src2_free_realizes_closed).
Qed.
End a.
