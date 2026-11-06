(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v at origin/ossv/recipes c8557374ad2e, with its module paths changed to libdiginet/fuzz_transport's split library and every image numeral recomputed from fuzz_transport.asan by the rule the donor's own numeral follows (the rule reproduces cgif's released text on cgif's image: the control). tfibmusl_text_start = sysconf+0 = 0x92db0 and tfibguard_start = oft_exit_guard+0 = 0x811ec in fuzz_transport.asan's symbol table; the musl count is cgif's rule ((.text end - sysconf)/4 + 3 = (0xa2948 - 0x92db0)/4 + 3 = 16105, which gives cgif's own 16403); the guard count 4 is cgif's. *)
(* Read from: fuzz_transport.asan (libdiginet/fuzz_transport asan) sha256 e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350; unstripped twin sha256 86efc3a80314981197619c115e313dbde50e8b86a6c5fefad4e5cc420250c792 *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP02.
From OSSVerify.libdiginet.fuzz_transport.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := Asan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x92db0.
Definition tfibmusl_text_count : nat := 16105.
Definition tfibguard_start : Z := 0x811ec.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
