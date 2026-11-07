(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: tp for libtasn1/asn1_get_length_der_fuzzer's plain binary, no realloc or mremap (it links neither), and module names. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YH04 YH07 YO04.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0c.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition src2_tp : Z := 0x2d1d0.
Definition src2_mpcs : malloc_pcs :=
MPcs src2_A_libc_malloc_impl src2_A_libc_free src2_A_get_meta src2_A_nontrivial_free src2_A_alloc_meta
src2_A_alloc_slot src2_A_enframe src2_A_vm_wait src2_A_mmap src2_A_mprotect src2_A_munmap
src2_A_syscall_ret src2_A_errno_location src2_A_stack_chk_fail src2_A_lock src2_A_unlock
src2_A_memcpy src2_A_memset None None.
Definition src2_msyms : malloc_syms :=
MSyms src2segs src2_mpcs src2_A_malloc src2_A_free None src2_D_malloc_context src2_D_malloc_lock src2_D_libc
src2_D_got_stack_chk_guard src2_D_stack_chk_guard None
src2_D_size_classes src2_D_small_cnt_tab src2_D_med_cnt_tab src2_D_debruijn32 src2_tp (-164) None.
Lemma src2_syms_check : syms_check src2_msyms = true.
Proof. vm_compute. reflexivity. Qed.
Theorem src2_syms_ok : syms_ok src2_msyms.
Proof. apply syms_ok_of_check. apply src2_syms_check. Qed.
End a.
