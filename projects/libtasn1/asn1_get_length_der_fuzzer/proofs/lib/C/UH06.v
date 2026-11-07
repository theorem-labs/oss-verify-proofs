(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Trevor Hansen, 2026-11: tp for libtasn1/asn1_get_length_der_fuzzer's UBSan binary, no realloc or mremap (it links neither), and module names. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import UH04 UH07 YO04.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0c.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ubs2_tp : Z := 0x2d200.
Definition ubs2_mpcs : malloc_pcs :=
MPcs ubs2_A_libc_malloc_impl ubs2_A_libc_free ubs2_A_get_meta ubs2_A_nontrivial_free ubs2_A_alloc_meta
ubs2_A_alloc_slot ubs2_A_enframe ubs2_A_vm_wait ubs2_A_mmap ubs2_A_mprotect ubs2_A_munmap
ubs2_A_syscall_ret ubs2_A_errno_location ubs2_A_stack_chk_fail ubs2_A_lock ubs2_A_unlock
ubs2_A_memcpy ubs2_A_memset None None.
Definition ubs2_msyms : malloc_syms :=
MSyms ubs2segs ubs2_mpcs ubs2_A_malloc ubs2_A_free None ubs2_D_malloc_context ubs2_D_malloc_lock ubs2_D_libc
ubs2_D_got_stack_chk_guard ubs2_D_stack_chk_guard None
ubs2_D_size_classes ubs2_D_small_cnt_tab ubs2_D_med_cnt_tab ubs2_D_debruijn32 ubs2_tp (-164) None.
Lemma ubs2_syms_check : syms_check ubs2_msyms = true.
Proof. vm_compute. reflexivity. Qed.
Theorem ubs2_syms_ok : syms_ok ubs2_msyms.
Proof. apply syms_ok_of_check. apply ubs2_syms_check. Qed.
End a.
