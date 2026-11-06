(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for omx-clap-core/fuzz_manifest's asan-ubsan image by gen_yb1v.py: tfibmusl_text_start = sysconf, tfibmusl_text_count = (.text end + 12 - start) / 4, tfibguard_start = oft_exit_guard (its 4-instruction fast path checked); module paths changed *)
(* Read from: fuzz_manifest.asan-ubsan (omx-clap-core/fuzz_manifest asan-ubsan) sha256 ca61e5c9eabc00501d5cebab7618d8c03e73419f52c9f0b9be51c8bedff96e5e; unstripped twin sha256 b9568e38145a50214b3744e4f26bfc2ec9f670eca737d4da9be2dca6a0cfc2de *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP02.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x88410.
Definition tfibmusl_text_count : nat := 16574.
Definition tfibguard_start : Z := 0x80904.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
