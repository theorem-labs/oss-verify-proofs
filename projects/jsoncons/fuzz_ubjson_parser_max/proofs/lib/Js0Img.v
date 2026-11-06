(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Img () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1cons"; "1list"; "1nil"; "1option"; "2eq"; "3word_to_le_bytes"; "4rdn"; "5loaded_segments"; "6Z_to_bv"; "6bv"]]).
Abbreviation SEGS := Plain.M.loaded_segments.
Lemma img_10040_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPR0%2271u4%;4:521(1&7+6%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10050_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPR@%2271u8%;4:521(1&7+RPR0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10078_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPSH%2271u4%;4:521(1&7+1%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_100b0_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPU@%2271u4%;4:521(1&7+1%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_100e8_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPW8%2271u4%;4:521(1&7+1%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10120_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPY0%2271u4%;4:521(1&7+1%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10158_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPZH%2271u4%;4:521(1&7+QbWYiZB%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10190_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RP\@%2271u4%;4:521(1&7+QbWYiZ@%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_101c8_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RP^8%2271u4%;4:521(1&7+QbWYiZA%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_101f0_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RP_@%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10200_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RP`0%2271u4%;4:521(1&7+4%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_10238_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+RPaH%2271u4%;4:521(1&7+QhPPPP3%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_af1c8_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+el^8%2271u8%;4:521(1&7+V^e8%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4d38_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fcYH%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4d40_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fcZ0%2271u8%;4:521(1&7+V^m<%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4d48_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fcZ8%2271u8%;4:521(1&7+cP[4%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4d50_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fcZ@%2271u8%;4:521(1&7+cRd0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4d58_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fcZH%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4ea0_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fce0%2271u8%;4:521(1&7+hnl@%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4ea8_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fce8%2271u8%;4:521(1&7+log8%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4eb0_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fce@%2271u8%;4:521(1&7+log0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4eb8_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fceH%2271u8%;4:521(1&7+el^@%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4ec0_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fcf0%2271u8%;4:521(1&7+el^8%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b4ec8_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fcf8%2271u8%;4:521(1&7+lof@%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b61c0_4 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fh^0%2271u4%;4:521(1&7+TPP0%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_b61e0_1 : ltac2:(TCodec.tc2 tcn__Js0Img "M'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+fh_0%2271u1%;4:521(1(2z%82C1(4%11D%53E31%72E1%L3E91").
Proof. vm_refl_bv. Qed.
Lemma img_e7c78_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+loSH%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e7c88_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+loT8%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e7c90_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+loT@%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e7ed8_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+lofH%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e7f00_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+loh0%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
Lemma img_e7f18_8 : ltac2:(TCodec.tc2 tcn__Js0Img "K'6'5'3';y8%211%411%611&8&9yR0%811(0%118q031&:+lohH%2271u8%;4:521(1&7z%82=1%3261%52C1%J3C71").
Proof. vm_refl_bv. Qed.
