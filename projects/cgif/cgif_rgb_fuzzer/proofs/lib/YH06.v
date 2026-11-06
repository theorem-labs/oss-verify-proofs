(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YO04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition src2_tp : Z := 0x31d20.
Definition src2_mpcs : malloc_pcs :=
MPcs src2_A_libc_malloc_impl src2_A_libc_free src2_A_get_meta src2_A_nontrivial_free src2_A_alloc_meta
src2_A_alloc_slot src2_A_enframe src2_A_vm_wait src2_A_mmap src2_A_mprotect src2_A_munmap
src2_A_syscall_ret src2_A_errno_location src2_A_stack_chk_fail src2_A_lock src2_A_unlock
src2_A_memcpy src2_A_memset None (Some src2_A_mremap).
Definition src2_msyms : malloc_syms :=
MSyms src2segs src2_mpcs src2_A_malloc src2_A_free None src2_D_malloc_context src2_D_malloc_lock src2_D_libc
src2_D_got_stack_chk_guard src2_D_stack_chk_guard None
src2_D_size_classes src2_D_small_cnt_tab src2_D_med_cnt_tab src2_D_debruijn32 src2_tp (-164) (Some src2_A_realloc).
Lemma src2_syms_check : syms_check src2_msyms = true.
Proof. vm_compute. reflexivity. Qed.
Theorem src2_syms_ok : syms_ok src2_msyms.
Proof. apply syms_ok_of_check. apply src2_syms_check. Qed.
End a.
