(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ubs2segs : list Segment := Ubsan.M.loaded_segments.
Definition ubs2text_start : Z := 0x12aa8.
Definition ubs2text_count : nat := 14443.
Definition ubs2tbl : ctable := Eval vm_compute in (build_table ubs2segs ubs2text_start ubs2text_count TEmpty).
Lemma ubs2tbl_eq : ubs2tbl = build_table ubs2segs ubs2text_start ubs2text_count TEmpty.
Proof. vm_cast_no_check (eq_refl ubs2tbl). Qed.
Lemma ubs2tbl_ok : table_ok ubs2segs ubs2tbl.
Proof. rewrite ubs2tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
