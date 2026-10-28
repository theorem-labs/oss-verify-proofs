(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ubs0segs : list Segment := Ubsan.M.loaded_segments.
Definition ubs0text_start : Z := 0x12864.
Definition ubs0text_count : nat := 12175.
Definition ubs0tbl : ctable := Eval vm_compute in (build_table ubs0segs ubs0text_start ubs0text_count TEmpty).
Lemma ubs0tbl_eq : ubs0tbl = build_table ubs0segs ubs0text_start ubs0text_count TEmpty.
Proof. vm_cast_no_check (eq_refl ubs0tbl). Qed.
Lemma ubs0tbl_ok : table_ok ubs0segs ubs0tbl.
Proof. rewrite ubs0tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
