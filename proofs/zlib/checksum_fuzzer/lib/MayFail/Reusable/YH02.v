(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH02.v, with its module paths and addresses changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition src0_tp : Z := 0x2fab0.
Definition src0_mpcs : malloc_pcs :=
MPcs src0_A_libc_malloc_impl src0_A_libc_free src0_A_get_meta src0_A_nontrivial_free src0_A_alloc_meta
src0_A_alloc_slot src0_A_enframe src0_A_vm_wait src0_A_mmap src0_A_mprotect src0_A_munmap
src0_A_syscall_ret src0_A_errno_location src0_A_stack_chk_fail src0_A_lock src0_A_unlock
src0_A_memcpy src0_A_memset None None.
Definition src0_msyms : malloc_syms :=
MSyms src0segs src0_mpcs src0_A_malloc src0_A_free None src0_D_malloc_context src0_D_malloc_lock src0_D_libc
src0_D_got_stack_chk_guard src0_D_stack_chk_guard None
src0_D_size_classes src0_D_small_cnt_tab src0_D_med_cnt_tab src0_D_debruijn32 src0_tp (-164) None.
Lemma src0_syms_check : syms_check src0_msyms = true.
Proof. vm_compute. reflexivity. Qed.
Theorem src0_syms_ok : syms_ok src0_msyms.
Proof. apply syms_ok_of_check. apply src0_syms_check. Qed.
End a.
