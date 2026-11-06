(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: generated from proofs/cgif/cgif_file_fuzzer/lib/YB1v.v (commit 25e3d17bdb50) by boxb1.py (sha256 0fe1e96732e2) from reac-repacer/fuzz_uci's asan-ubsan image: tfibmusl_text_start = sysconf+0 = 0x85ffc, count (.text end 0x95b90 - 0x85ffc)/4 + 3 = 16104 (cgif's rule, its own 16403), tfibguard_start = oft_exit_guard+0 = 0x7f270, count 4 (cgif's); module paths changed. *)
(* Read from: fuzz_uci.asan-ubsan (the reac-repacer/fuzz_uci asan-ubsan pin) sha256 a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc; unstripped twin sha256 8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16 *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YP02.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x85ffc.
Definition tfibmusl_text_count : nat := 16104.
Definition tfibguard_start : Z := 0x7f270.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
