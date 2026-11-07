(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Trevor Hansen, 2026-11: the image and text range of libtasn1/asn1_get_length_der_fuzzer's UBSan binary, and module names. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YQ03.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ubs2segs : list Segment := Ubsan.M.loaded_segments.
Definition ubs2text_start : Z := 0x12468.
Definition ubs2text_count : nat := 8799.
Definition ubs2tbl : ctable := Eval vm_compute in (build_table ubs2segs ubs2text_start ubs2text_count TEmpty).
Lemma ubs2tbl_eq : ubs2tbl = build_table ubs2segs ubs2text_start ubs2text_count TEmpty.
Proof. vm_cast_no_check (eq_refl ubs2tbl). Qed.
Lemma ubs2tbl_ok : table_ok ubs2segs ubs2tbl.
Proof. rewrite ubs2tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
