(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02 YB1v.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_lib_start : Z := 0x80020.
Definition tfib_lib_count : nat := 7052.
Definition tfib_memcmp_start : Z := 0x97408.
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
