(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: moved from libreac/fuzz_grant (port-grant's pg-rt AF0r.v) to fuzz_identity.asan: the shared code table only, for stack_malloc classes 0, 3 and 4 and their helpers, at fuzz_identity.asan's addresses. *)
(* Modified by Theorem Labs, 2026-10: image B: hex addresses for fuzz_identity.asan-ubsan (baf1a4d065e0), each relocated by function symbol + offset (code) or by image read-back / containing symbol (data); the entries and helpers used here sit at A + 0x68, which is NOT a rule for other code (memset: A 0x94a18, B 0x94d04); modules lib.B. *)
(* Modified by Theorem Labs, 2026-10: image B on the release two-image layout: Requires of lib.B.A<x> are lib.ReusableB.Y<x>, image-specific Reusable modules are lib.ReusableB. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/B/Rt/StackMallocTbl.v at origin/ossv/recipes 8356d546c708; moved to reac-pw/fuzz_rate's asan-ubsan build (fuzz_rate.asan-ubsan sha256 c30584a72149; __asan_stack_malloc_4 at 0x3d300, code identical to fuzz_identity.asan-ubsan's at 0x3d308 but for pc-relative fields) by alreloc a5c53bb2bed4, cross-checked numeral by numeral with port_core 1e42da8952ec; modules lib.B -> lib.AU, the B kit copy lib.ReusableB.YCe5 -> the shared lib.Reusable.YCe5, the B core lib.ReusableB.Y<x> -> lib.AU.Y<x>; the code table drops the rows of __asan_stack_malloc_0 and __asan_stack_malloc_3, which this image does not link. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YCe5.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YE34 YF0l YF0m YF0x YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition fs_ranges : list (Z * nat) :=
[(0x3d300, 115%nat); (0x61d88, 2%nat); (0x46b68, 31%nat); (0x95e50, 9%nat);
(0x5c0c8, 8%nat); (0x54c14, 6%nat); (0x96f04, 7%nat); (0x697dc, 140%nat); (0x3d4cc, 28%nat)].
Definition tbl_fs : ctable := Eval vm_compute in build_ranges fs_ranges tbl_icpt.
Lemma tbl_fs_eq : tbl_fs = build_ranges fs_ranges tbl_icpt. Proof. vm_cast_no_check (eq_refl tbl_fs). Qed.
Lemma tbl_fs_ok : table_ok tfibsegs tbl_fs.
Proof. rewrite tbl_fs_eq. apply build_ranges_ok; [unfold fs_ranges; repeat constructor; cbn; discriminate | exact tbl_icpt_ok]. Qed.
End e.
