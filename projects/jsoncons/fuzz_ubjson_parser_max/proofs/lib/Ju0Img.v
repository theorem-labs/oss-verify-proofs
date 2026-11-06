(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0Img () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1cons"; "1list"; "1nil"; "1option"; "2eq"; "3word_to_le_bytes"; "4rdn"; "5loaded_segments"; "6Z_to_bv"; "6bv"]]).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Lemma img_10040_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPR0%2271u4%;4:521(1&7+6%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10050_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPR@%2271u8%;4:521(1&7+RPR0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10078_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPSH%2271u4%;4:521(1&7+1%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_100b0_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPU@%2271u4%;4:521(1&7+1%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_100e8_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPW8%2271u4%;4:521(1&7+1%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10120_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPY0%2271u4%;4:521(1&7+1%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10158_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPZH%2271u4%;4:521(1&7+QbWYiZB%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10190_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RP\@%2271u4%;4:521(1&7+QbWYiZ@%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_101c8_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RP^8%2271u4%;4:521(1&7+QbWYiZA%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_101f0_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RP_@%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10200_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RP`0%2271u4%;4:521(1&7+4%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10238_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPaH%2271u4%;4:521(1&7+QhPPPP3%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b0218_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fP`H%2271u8%;4:521(1&7+V_XH%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5d88_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fg\8%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5d90_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fg\@%2271u8%;4:521(1&7+V_`L%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5d98_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fg\H%2271u8%;4:521(1&7+cT]H%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5da0_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fg]0%2271u8%;4:521(1&7+cVfD%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5da8_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fg]8%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5ef0_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fgg@%2271u8%;4:521(1&7+iRo0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5ef8_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fggH%2271u8%;4:521(1&7+mSiH%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5f00_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fgh0%2271u8%;4:521(1&7+mSi@%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5f08_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fgh8%2271u8%;4:521(1&7+fPa0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5f10_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fgh@%2271u8%;4:521(1&7+fP`H%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b5f18_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fghH%2271u8%;4:521(1&7+mSi0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b7210_4 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fl`@%2271u4%;4:521(1&7+TPP0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b7230_1 : ltac2:(TCodec.tc2 tcn__Ju0Img "M'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fla@%2271u1%;4:521(1(2z%82C1(4%11D%53E31%72E1%L3E91").
Proof. vm_refl_bv. Qed.
Lemma img_e8cc8_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+mSV8%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e8cd8_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+mSVH%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e8ce0_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+mSW0%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e8f28_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+mSi8%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e8f50_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+mSj@%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e8f68_8 : ltac2:(TCodec.tc2 tcn__Ju0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+mSk8%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
