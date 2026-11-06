(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0segs : list Segment := Plain.M.loaded_segments.
Definition src0text_start : Z := 0x127e4.
Definition src0text_count : nat := 11622.
Definition src0tbl : ctable := Eval vm_compute in (build_table src0segs src0text_start src0text_count TEmpty).
Lemma src0tbl_eq : src0tbl = build_table src0segs src0text_start src0text_count TEmpty.
Proof. vm_cast_no_check (eq_refl src0tbl). Qed.
Lemma src0tbl_ok : table_ok src0segs src0tbl.
Proof. rewrite src0tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
