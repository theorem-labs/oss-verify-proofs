(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtAtomics ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatCombAlloc () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCombAlloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCombAlloc.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4bvmap"; "0M"; "5wr"; "6msteps"; "8art_ca_entry_kept"; "7art_ca_frame"; "9getr"; "9mkst"; ":loaded_segments"]; [";add"; ";div"; ";le"; ";lt"; ";pow"; ";sub"; "0fx"; "0r"; "0regs"; "0regs'"; "0rom"; "0s"; "0sp"; "<BV"; "<Z_to_bv"; "<bv"]; ["<bv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
Definition art_ca_frame (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) ra) (sp - 16) s0) (sp - 24) s1) (sp - 32) s2) (sp - 40) s3) (sp - 48) s4.
Section FPX. Context {fx : PropExec.FPState}.
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_ca_entry_kept (r : reg) : Prop := r <> 2%bv /\ r <> 12%bv /\ r <> 14%bv /\ r <> 15%bv.
Section SE.
Local Abbreviation SEC_T_art_ca_entry8 := (ltac2:(TCodec.tc2 tcn__JatCombAlloc "TC&7y5'OyR0%211%5241'0y8%611%311p061'6'3&=r5(M+2(1%33A21%6251&Nr2%22C1%;3C41r6+<%;3I19%>231%@3H16r7+=%@3N1>%C231+8%>2O1%G3O31&B+Q@%221H&C&D+R0%22J1%42C1'2+1%:21F+RPP0%<2H1%5231&9&?r:&Er8%221B%64541C'4':&>vFr=+ZhiL%Q@3QL1Q>/01QLr<r;%8576321r1+Zhn0%QG3R31QE/01R3&<&Q0%QK3R9MQI%QN2>1%32R91%QN3R<Q<QL%R12A1%62R<1+9%R23R@1R0%R52E1%:2R@1+B%R63RD1R4%R92I1%>2RD1+C%R:3RH1R8%R=2M1%B2RH1+D%R>3RL1R<%RA2Q11%F2RL1%H8OQ<DA=951%Q65Q5MJ1O%Q83Q?O1%RF2ORA%Q?2Q@QO%RA2S21%RJ3S231+>%RI3S71RG%RL2Q51r9%RG2S81%S03S831%S02Q9RC+`0%RK2S<1%S43S<31+?%S33SA1S1%S62Q?1%S02SAR5%S93SA21%SD1SE&;%11QDr3%S=21S5r?%S?21S7%SA3SI31p061pQ@91%RD2;1%RE2A1%RF2F1%RG2M1%RH2Q21qQDT01%R=2T11p0R?1p0RG1p0RN1p0S41p0S81p0S@1p0SF1pQHT31pQJT41pQFT61pBT71pQBT=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ca_entry8) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ca_entry8) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ca_entry8) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_ca_entry8) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_ca_entry8) 4%nat 0%nat).
Lemma art_ca_entry8 : ltac:(sec_stmt2 constr:(SEC_T_art_ca_entry8) 5%nat 0%nat).
Proof using Type regs M rom sp s.
intros H2 H12 H13 Hsp Hsp' Hs W.
eexists. split.
- zstep (ltac:(oF' 0x5633c%Z)) (ltac:(oD' 0x5633c%Z)).
zsd (ltac:(oF' 0x56340%Z)) (ltac:(oD' 0x56340%Z)) (sp - 8) (U (getr regs 1)) ltac:(rewok W).
zsd (ltac:(oF' 0x56344%Z)) (ltac:(oD' 0x56344%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x56348%Z)) (ltac:(oD' 0x56348%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x5634c%Z)) (ltac:(oD' 0x5634c%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x56350%Z)) (ltac:(oD' 0x56350%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x56354%Z)) (ltac:(oD' 0x56354%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zstep (ltac:(oF' 0x56358%Z)) (ltac:(oD' 0x56358%Z)).
zstep (ltac:(oF' 0x5635c%Z)) (ltac:(oD' 0x5635c%Z)).
zstep (ltac:(oF' 0x56360%Z)) (ltac:(oD' 0x56360%Z)).
zbtk (ltac:(oF' 0x56364%Z)) (ltac:(oD' 0x56364%Z)).
zstep (ltac:(oF' 0x56388%Z)) (ltac:(oD' 0x56388%Z)).
zstep (ltac:(oF' 0x5638c%Z)) (ltac:(oD' 0x5638c%Z)).
zbtk (ltac:(oF' 0x56390%Z)) (ltac:(oD' 0x56390%Z)).
zstep (ltac:(oF' 0x563b0%Z)) (ltac:(oD' 0x563b0%Z)).
zbft (ltac:(oF' 0x563b4%Z)) (ltac:(oD' 0x563b4%Z)).
zbft (ltac:(oF' 0x563b8%Z)) (ltac:(oD' 0x563b8%Z)).
zstep (ltac:(oF' 0x563bc%Z)) (ltac:(oD' 0x563bc%Z)).
apply mst_refl.
- repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
intros r Hr; unfold art_ca_entry_kept in Hr; destruct Hr as (?&?&?&?); gres; try reflexivity;
repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.
End SE.
#[using="Type"] Lemma art_ca_small : ltac2:(TCodec.tc2 tcn__JatCombAlloc "RO&7y5'OyR0%211%5241'0y8%611%311p061'6'3&=r4(M+>(1%33A21%6251&Nr1%22C1%;3C41r5+<%;3I19%>231+`0%92J1%B3J31'2&B+1r3%3221%4228%6221'4':&?&>vFr8+Zhn0%N3Q:1L/01Q:r7r6%8576321+ZiV@%Q43Q@1Q2/01Q@%<5;Q0165%?3>51+8%Q93QG1Q7%Q<2Q41&A&@+O%22Q51+Q0%5221%Q<2QM1%QE3QM81%QE2Q=Q@%Q?2R06%QH3R021%R31R4&5%QK32QB?%211r2%QN351QH%511%QO2QNQ:r;%R121Q<%R33R;31p051p091pQ@=1%QD2?1%QE2C1%QF2O1qQDRA1%QA2RB1p0QC1p0QK1p0R31pQHR@1pQFRB1pBRC1pQBRI1").
Proof.
intros regs M rom s H14 H12 Hs.
eexists. split.
- zbft (ltac:(oF' 0x563c0%Z)) (ltac:(oD' 0x563c0%Z)).
zstep (ltac:(oF' 0x563c4%Z)) (ltac:(oD' 0x563c4%Z)).
stepn (ltac:(oF' 0x563c8%Z)) (ltac:(oD' 0x563c8%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
stepn (ltac:(oF' 0x563cc%Z)) (ltac:(oD' 0x563cc%Z)).
apply mst_refl.
- repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
intros r H1 H2; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.
#[using="Type"] Lemma art_ca_big : ltac2:(TCodec.tc2 tcn__JatCombAlloc "QM&7y5'OyR0%211%5241'0y8%611%311p061'6'3&=r4(M+>(1%33A21%6251&Nr1%22C1%;3C41r5+<%;3I19%>231+`0%92J1%B3J31'2&B+`1r3%3221+RPP0%5231%7231':&?&>vFr7+Zhn0%N3Q:1L/01Q:r6%756521H+ZhoD%Q33Q?1Q1/01Q?%;5:915L%>3=51p0@1p0I1p0Q11pQHQ>1pQFQ@1pBQA1pQBQG1").
Proof.
intros regs M rom s H14 H12 Hs.
zbtk (ltac:(oF' 0x563c0%Z)) (ltac:(oD' 0x563c0%Z)).
apply mst_refl.
Qed.
End FPX.
