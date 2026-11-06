(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/YB1v.v (commit 25e3d17bdb50) by boxb1.py (sha256 0fe1e96732e2) from reac-repacer/fuzz_wire's asan-ubsan image: tfibmusl_text_start = sysconf+0 = 0x87748, count (.text end 0x972e0 - 0x87748)/4 + 3 = 16105 (cgif's rule, its own 16403), tfibguard_start = oft_exit_guard+0 = 0x7fb80, count 4 (cgif's); module paths changed. *)
(* Read from: fuzz_wire.asan-ubsan (reac-repacer/fuzz_wire asan-ubsan) sha256 af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6; unstripped twin sha256 51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3 *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP02.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x87748.
Definition tfibmusl_text_count : nat := 16105.
Definition tfibguard_start : Z := 0x7fb80.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
