(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: the image and text range of libtasn1/asn1_get_length_der_fuzzer's plain binary, and module names. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YQ03.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src2segs : list Segment := Plain.M.loaded_segments.
Definition src2text_start : Z := 0x12468.
Definition src2text_count : nat := 8788.
Definition src2tbl : ctable := Eval vm_compute in (build_table src2segs src2text_start src2text_count TEmpty).
Lemma src2tbl_eq : src2tbl = build_table src2segs src2text_start src2text_count TEmpty.
Proof. vm_cast_no_check (eq_refl src2tbl). Qed.
Lemma src2tbl_ok : table_ok src2segs src2tbl.
Proof. rewrite src2tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
