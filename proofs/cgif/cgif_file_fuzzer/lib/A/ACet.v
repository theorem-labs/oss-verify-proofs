(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACei ACem ACep ACes ACex ACew ACey ACev Nrfc6 Nrfc45 Nrfc23 ACeu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B MT.
Hypothesis AFREE4 : afree04_rule tfibsegs B MT.
Hypothesis AFREEN4 : afree_null04_rule tfibsegs B MT.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_asan_memcpy_tfb.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet A_asan_memset_tfb.
Theorem tfib_read_frameconfigX : trfc_specX B MT.
Proof.
assert (RI : RFC_I_stmt B MT) by (apply rfc_I_ok; assumption).
assert (RJ : RFC_J_stmt B MT) by (apply rfc_J_ok; assumption).
assert (RC3 : RFC_C3_stmt B MT) by (apply rfc_C3_ok; assumption).
assert (RC1 : RFC_C1_stmt B MT) by (apply rfc_C1_ok; assumption).
apply rfc_A_ok; assumption.
Qed.
End b.
End a.
