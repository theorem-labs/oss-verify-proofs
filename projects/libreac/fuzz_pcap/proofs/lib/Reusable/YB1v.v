(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for libreac/fuzz_pcap's asan-ubsan image by mkfiles.py (sha256 8e6d8a8535c7; internal record) (the musl instruction table (sysconf .. the end of the executable segment) and the exit guard are this image's own); module paths changed *)
(* gated: a Theorem Labs lane PASS A+B at c061542723f / 731386609e0.  Every literal is read from the asan-ubsan image named above; nothing is filled.  Control: mkfiles.py (sha256 8e6d8a8535c7; internal record) --control regenerates the donor's own file byte for byte. *)
(* Before commit 5098883da0b3 (2026-10-29) brought YF0l and YB13 into this tree, the asan-ubsan files built ONLY in a union that also included a working branch 27d40cfe97f76cd158308a2aef684e7e509db360: lib/Reusable/YF0m.v Requires YF0l and lib/Reusable/YD2i.v Requires YB13, both of them core files of that branch. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP02.
From OSSVerify.libreac.fuzz_pcap.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition tfibmusl_text_start : Z := Eval compute in Symbols.AsanUbsan.s_sysconf.
Definition tfibmusl_text_count : nat := 16749.
Definition tfibguard_start : Z := Eval compute in Symbols.AsanUbsan.s_oft_exit_guard.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
