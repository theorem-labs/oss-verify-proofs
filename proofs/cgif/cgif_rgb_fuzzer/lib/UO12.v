(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YQ0k YN06 YK0s YN02 YK1a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0r YP0u YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO02 YO03 YO2f YO30
UO16 UO0y UO0z UO14 UO11
UO10 UO15
UO3m UO0f UO28 UO0i UO19 UO07 UO0x.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma fetch_malloc_stub : fetch_word ubs2segs (Z_to_bv 64 ubs2_A_malloc) = Some (0x1910006f%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x1910006f%bv : bv 32)). apply ubs2tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_malloc_stub : decode_any (0x1910006f%bv : bv 32) = Some (Jal 0 (Z_to_bv 21 0x990), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma fetch_free_stub : fetch_word ubs2segs (Z_to_bv 64 ubs2_A_free) = Some (0x1440006f%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x1440006f%bv : bv 32)). apply ubs2tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_free_stub : decode_any (0x1440006f%bv : bv 32) = Some (Jal 0 324, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma step_malloc_stub regs mem :
RiscvSemantics.step ubs2segs (mkst regs (Z_to_bv 64 ubs2_A_malloc) mem (seg_rom ubs2segs)) =
MachineOk (mkst regs (Z_to_bv 64 ubs2_A_libc_malloc_impl) mem (seg_rom ubs2segs)).
Proof.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_malloc_stub eq_refl decode_malloc_stub). do 2 f_equal.
Qed.
Lemma step_free_stub regs mem :
RiscvSemantics.step ubs2segs (mkst regs (Z_to_bv 64 ubs2_A_free) mem (seg_rom ubs2segs)) =
MachineOk (mkst regs (Z_to_bv 64 ubs2_A_libc_free) mem (seg_rom ubs2segs)).
Proof.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_free_stub eq_refl decode_free_stub). do 2 f_equal.
Qed.
Lemma ubs2_malloc_impl : malloc_realizes ubs2_msyms (MRx ubs2_msyms) -> malloc_impl_realizes.
Proof.
intros HM L A regs mem md n PRE H10 Hn.
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ (proj1 PRE))) as (Hh & Hlz & _).
apply (mreal_step_inv ubs2segs (mkst regs (Z_to_bv 64 ubs2_A_malloc) mem (seg_rom ubs2segs)) md _ (malloc n A) _ Hh Hlz eq_refl (step_malloc_stub regs mem)).
exact (HM L A regs mem md n PRE H10 Hn).
Qed.
Lemma ubs2_free_impl : free_realizes ubs2_msyms (MRx ubs2_msyms) -> free_impl_realizes.
Proof.
intros HF L A regs mem md p n PRE Hin H10.
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ (proj1 PRE))) as (Hh & Hlz & _).
apply (mreal_step_inv ubs2segs (mkst regs (Z_to_bv 64 ubs2_A_free) mem (seg_rom ubs2segs)) md _ (free (Some p) A) _ Hh Hlz eq_refl (step_free_stub regs mem)).
exact (HF L A regs mem md p n PRE Hin H10).
Qed.
Lemma ubs2_memcpy_spec : memcpy_spec.
Proof. exact ubs2_memcpy. Qed.
Theorem ubs2_realloc_of_api :
malloc_realizes ubs2_msyms (MRx ubs2_msyms) -> free_realizes ubs2_msyms (MRx ubs2_msyms) ->
realloc_realizes ubs2_msyms (MRx ubs2_msyms).
Proof.
intros HM HF.
exact (ubs2_realloc_realizes (ubs2_malloc_impl HM) (ubs2_free_impl HF) ubs2_memcpy_spec
ubs2_realloc_entry ubs2_realloc_eq (ubs2_realloc_node ubs2_realloc_ok ubs2_realloc_fb)).
Qed.
Theorem ubs2_realloc : realloc_realizes ubs2_msyms (MRx ubs2_msyms).
Proof.
exact (ubs2_realloc_of_api (ubs2_malloc_realizes_of_hyps ubs2_alloc_meta ubs2_alloc_slot) ubs2_free_realizes_closed).
Qed.
End a.
