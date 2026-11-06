(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk StreamSim ArtMem ArtRuns ArtRunsMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatFxImg () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFxImg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "1true"; "2eq"; "3Z"; "0M"; "4wr"; "5art_iatab_n"; "6wseg_ok"; "7loaded_segments"; "8add"; "8le"; "8of_nat"; "0a"; "0n"; "9Z_to_bv"]; ["9bv"]]).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_iatab_n : nat := Z.to_nat 0x81030.
Lemma art_wseg_iatab : ltac2:(TCodec.tc2 tcn__JatFxImg "<'3'0&8&9&?yR0+QW_h0%3221&7%73621(2%;3:21").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma art_iatab_n_Z : ltac2:(TCodec.tc2 tcn__JatFxImg "7'3'4&<&7%211+`TQ@%63521"). Proof. unfold art_iatab_n. apply Z2Nat.id. lia. Qed.
Global Opaque art_iatab_n.
Lemma art_wseg_iaflag : ltac2:(TCodec.tc2 tcn__JatFxImg "<'3'0&8&9&?yR0+QiYl8%3221u4%73621(2%;3:21").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma art_img_wr_iatab : ltac2:(TCodec.tc2 tcn__JatFxImg "Q1'@yR0%211'1y8%511%311p051'4&;+QW_h0r2%3221z%5213&:r4r3%3221+`TQ@%52:1%<231&6&9r6r5%44321:p061p0>1p0A1pNF1pLG1p<I1").
Proof.
intros M a n Ha Hn0 Hn d k Hd Hk.
apply (store_ok_window ASEGS M (Z_to_bv 64 0x13bf00) (Z_to_bv 64 (a + d)) art_iatab_n k 0x13bf00 (0x13bf00 + 0x81030));
first [exact art_wseg_iatab | (rewrite art_iatab_n_Z; reflexivity) | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.
Lemma art_img_wr_iaflag : ltac2:(TCodec.tc2 tcn__JatFxImg "Q1'@yR0%211'1y8%511%311p051'4&;+QiYl8r2%3221z%5213&:r4r3%3221+4%52:1%<231&6&9r6r5%44321:p061p0>1p0A1pNF1pLG1p<I1").
Proof.
intros M a n Ha Hn0 Hn d k Hd Hk.
apply (store_ok_window ASEGS M (Z_to_bv 64 0x1ca788) (Z_to_bv 64 (a + d)) 4%nat k 0x1ca788 (0x1ca788 + 4));
first [exact art_wseg_iaflag | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.
