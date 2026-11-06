(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YCef.v, with its module paths, addresses and numbers changed; 3 of its 15 lines of code are new or changed and 10 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP02 YB1v.
From OSSVerify.libreac.fuzz_disco.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_lib_start : Z := 0x80fbc.
Definition tfib_lib_count : nat := 8769.
Definition tfibtbl_lib : ctable :=
Eval vm_compute in (build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty).
Lemma tfibtbl_lib_eq : tfibtbl_lib = build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty.
Proof. vm_cast_no_check (eq_refl tfibtbl_lib). Qed.
Lemma tfibtbl_lib_ok : table_ok tfibsegs tfibtbl_lib.
Proof. rewrite tfibtbl_lib_eq. apply build_table_ok0. cbv. discriminate. Qed.
