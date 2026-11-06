(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YB1u.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition trb_lib_start : Z := 0x80dd0.
Definition trb_lib_count : nat := 11285.
Definition trb_memcmp_start : Z := 0x9c47c.
Definition trb_memcmp_count : nat := 13.
Definition trbtbl_lib : ctable :=
Eval vm_compute in (build_table trbsegs trb_memcmp_start trb_memcmp_count
(build_table trbsegs trb_lib_start trb_lib_count TEmpty)).
Lemma trbtbl_lib_eq : trbtbl_lib = build_table trbsegs trb_memcmp_start trb_memcmp_count
(build_table trbsegs trb_lib_start trb_lib_count TEmpty).
Proof. vm_cast_no_check (eq_refl trbtbl_lib). Qed.
Lemma trbtbl_lib_ok : table_ok trbsegs trbtbl_lib.
Proof.
rewrite trbtbl_lib_eq. apply build_table_ok; [cbv; discriminate|].
apply build_table_ok0. cbv. discriminate.
Qed.
