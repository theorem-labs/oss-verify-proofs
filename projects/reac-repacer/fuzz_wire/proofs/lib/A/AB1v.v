(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v at commit 25e3d17bdb50 (the same blob as at c8557374ad2e), with its module paths changed to reac-repacer/fuzz_wire's split library and every image numeral recomputed from fuzz_wire.asan by the rule the donor's own numeral follows (the rule reproduces cgif's released text on cgif's image: the control). tfibmusl_text_start = sysconf+0 = 0x876b4 and tfibguard_start = oft_exit_guard+0 = 0x7fde0 in fuzz_wire.asan's symbol table; the musl count is cgif's rule ((.text end - sysconf)/4 + 3 = (0x9724c - 0x876b4)/4 + 3 = 16105, which gives cgif's own 16403); the guard count 4 is cgif's. *)
(* Read from: fuzz_wire.asan (reac-repacer/fuzz_wire asan) sha256 2f8f8697cd4f99bd15999cce4963a6fcc39b308444bd58e2bf526ec7c1ad5fa1; unstripped twin sha256 d2f662a229626fd402f1018631498190e800834bad837fa4027204b79088b128 *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP02.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := Asan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x876b4.
Definition tfibmusl_text_count : nat := 16105.
Definition tfibguard_start : Z := 0x7fde0.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
