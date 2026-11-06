(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v at origin/ossv/recipes c8557374ad2e, with its module paths changed to libreac/fuzz_decode's split library and every image numeral recomputed from fuzz_decode.asan by the rule the donor's own numeral follows (the rule reproduces cgif's released text on cgif's image: the control). tfibmusl_text_start = sysconf+0 = 0x87c10 and tfibguard_start = oft_exit_guard+0 = 0x7ffec in fuzz_decode.asan's symbol table; the musl count is cgif's rule ((.text end - sysconf)/4 + 3 = (0x977a8 - 0x87c10)/4 + 3 = 16105, which gives cgif's own 16403); the guard count 4 is cgif's. *)
(* Read from: fuzz_decode.asan (libreac/fuzz_decode asan) sha256 5973b76807d8d2e14b82dc6afde70a2c882923658406aeca43681719cb4e8036; unstripped twin sha256 4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2 *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP02.
From OSSVerify.libreac.fuzz_decode.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := Asan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x87c10.
Definition tfibmusl_text_count : nat := 16105.
Definition tfibguard_start : Z := 0x7ffec.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
