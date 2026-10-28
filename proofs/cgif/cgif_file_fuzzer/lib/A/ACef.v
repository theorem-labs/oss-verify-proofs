(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_lib_start : Z := 0x7fff0.
Definition tfib_lib_count : nat := 6907.
Definition tfib_memcmp_start : Z := 0x97194.
Definition tfib_memcmp_count : nat := 13.
Definition tfibtbl_lib : ctable :=
Eval vm_compute in (build_table tfibsegs tfib_memcmp_start tfib_memcmp_count
(build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty)).
Lemma tfibtbl_lib_eq : tfibtbl_lib = build_table tfibsegs tfib_memcmp_start tfib_memcmp_count
(build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibtbl_lib). Qed.
Lemma tfibtbl_lib_ok : table_ok tfibsegs tfibtbl_lib.
Proof.
rewrite tfibtbl_lib_eq. apply build_table_ok; [cbv; discriminate|].
apply build_table_ok0. cbv. discriminate.
Qed.
