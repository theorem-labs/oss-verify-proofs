(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v at origin/ossv/recipes c8557374ad2e, with its module paths changed to reac-repacer/fuzz_uci's split library and every image numeral recomputed from fuzz_uci.asan by the rule the donor's own numeral follows (the rule reproduces cgif's released text on cgif's image: the control). tfibmusl_text_start = sysconf+0 = 0x85ef4 and tfibguard_start = oft_exit_guard+0 = 0x7f270 in fuzz_uci.asan's symbol table; the musl count is cgif's rule ((.text end - sysconf)/4 + 3 = (0x95a88 - 0x85ef4)/4 + 3 = 16104, which gives cgif's own 16403); the guard count 4 is cgif's. *)
(* Read from: fuzz_uci.asan (reac-repacer/fuzz_uci asan) sha256 6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d; unstripped twin sha256 56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YP02.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := Asan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x85ef4.
Definition tfibmusl_text_count : nat := 16104.
Definition tfibguard_start : Z := 0x7f270.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
