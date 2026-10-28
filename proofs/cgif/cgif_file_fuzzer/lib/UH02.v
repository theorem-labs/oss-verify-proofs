(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 UH00 UH03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ubs0_tp : Z := 0x30ab0.
Definition ubs0_mpcs : malloc_pcs :=
MPcs ubs0_A_libc_malloc_impl ubs0_A_libc_free ubs0_A_get_meta ubs0_A_nontrivial_free ubs0_A_alloc_meta
ubs0_A_alloc_slot ubs0_A_enframe ubs0_A_vm_wait ubs0_A_mmap ubs0_A_mprotect ubs0_A_munmap
ubs0_A_syscall_ret ubs0_A_errno_location ubs0_A_stack_chk_fail ubs0_A_lock ubs0_A_unlock
ubs0_A_memcpy ubs0_A_memset None None.
Definition ubs0_msyms : malloc_syms :=
MSyms ubs0segs ubs0_mpcs ubs0_A_malloc ubs0_A_free None ubs0_D_malloc_context ubs0_D_malloc_lock ubs0_D_libc
ubs0_D_got_stack_chk_guard ubs0_D_stack_chk_guard None
ubs0_D_size_classes ubs0_D_small_cnt_tab ubs0_D_med_cnt_tab ubs0_D_debruijn32 ubs0_tp (-164) None.
Lemma ubs0_syms_check : syms_check ubs0_msyms = true.
Proof using. vm_compute. reflexivity. Qed.
Theorem ubs0_syms_ok : syms_ok ubs0_msyms.
Proof using. apply syms_ok_of_check. apply ubs0_syms_check. Qed.
End a.
