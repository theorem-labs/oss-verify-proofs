(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition trbsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition trbmusl_text_start : Z := 0x91c04.
Definition trbmusl_text_count : nat := 16388.
Definition trbguard_start : Z := 0x811f8.
Definition trbguard_count : nat := 4.
Definition trbmusl_tbl : ctable := Eval vm_compute in
(build_table trbsegs trbguard_start trbguard_count (build_table trbsegs trbmusl_text_start trbmusl_text_count TEmpty)).
Lemma trbmusl_tbl_eq : trbmusl_tbl = build_table trbsegs trbguard_start trbguard_count (build_table trbsegs trbmusl_text_start trbmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl trbmusl_tbl). Qed.
Lemma trbmusl_tbl_ok : table_ok trbsegs trbmusl_tbl.
Proof. rewrite trbmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
