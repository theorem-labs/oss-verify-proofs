(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YB0z.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition tra_lib_start : Z := 0x80b0c.
Definition tra_lib_count : nat := 10419.
Definition tra_memcmp_start : Z := 0x9b390.
Definition tra_memcmp_count : nat := 13.
Definition tratbl_lib : ctable :=
Eval vm_compute in (build_table trasegs tra_memcmp_start tra_memcmp_count
(build_table trasegs tra_lib_start tra_lib_count TEmpty)).
Lemma tratbl_lib_eq : tratbl_lib = build_table trasegs tra_memcmp_start tra_memcmp_count
(build_table trasegs tra_lib_start tra_lib_count TEmpty).
Proof. vm_cast_no_check (eq_refl tratbl_lib). Qed.
Lemma tratbl_lib_ok : table_ok trasegs tratbl_lib.
Proof.
rewrite tratbl_lib_eq. apply build_table_ok; [cbv; discriminate|].
apply build_table_ok0. cbv. discriminate.
Qed.
