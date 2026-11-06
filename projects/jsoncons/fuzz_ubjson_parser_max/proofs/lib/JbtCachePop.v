(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtAtomics ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtCachePop () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCachePop.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wok"; "6msteps"; "7ret_ok"; "8art_pop_kept"]; ["9getr"; "9mkst"; ":loaded_segments"; ";add"; ";land"; ";le"; ";lt"; ";modulo"; ";mul"; ";pow"; ";sub"; "0c"; "0ca"; "0ch"; "0cnt"; "0csz"]; ["0fx"; "0ia"; "0r"; "0raw"; "0regs"; "0regs'"; "0res"; "0rom"; "0s0v"; "0s1v"; "0s2v"; "0s3v"; "0s4v"; "0sp"; "0spb"; "0st"]; ["<BV"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_cache_pop_core := (ltac2:(TCodec.tc2 tcn__JbtCachePop "W7&7y5'QByR0%211%5241'0y8%611%311p061'6'3&@r;(Q@+8(1%33A21%6251&QAr8%22C1%;3C41r<+;%;3I19%>231%@3H16r=+:%@3N1>%C231%E3M1;'2&E+1%221G+O%42I1%6231z%721L&F&C+TP0%22F1&I+2+R0%3221%8251&G%12HQ5%Q:3Q;1=%D2>Jr>%=21<%?218%H2G3+@%J251%L231%L2F7%E28>%O221+Q0%D2C1%I2<1%Q3261&;&BrHrE&H+R@rF%3221%Q2251u4rC%;5:9321rIrG%:291%Q9291%Q:21R6u8%B5A6218rJ%@2?B%Q?281%Q@21Q0+4&J%12FQK%F231%QE251%L5K91CBrK+R`@%QI2M1%Q05O31?FrL%QL2Q0Q6%Q35Q221BI&<rM%Q22Q19%R12D1%44Q731OrN%R42=<%74Q:21J&:%Q92Q88%R82=1%R92BQC%442I1S6%R;2<C%R<2AQF%742S91S9'4'=&AvQ0rQ3+Zim0%SA3SM1S?/01SMrQ2rQ1%8576321r1+ZioL%SH3T41SF/01T4&9rOrQ0%R22R11%S1231%Q@2Q3S:%64R0=21%S426Q<%S52QHQ:%94QK321%G5F>;1@%I3R=@1%T82@SF%R<2;RC%S;2R51%R>2QERL%S=221%T62TG1%T?3TG61%TJ1TK&5%TB32IT<%211r2+9%TC3U11TA%TG3731%711r3%TJ3:1T7%:11r4%TM3=1T?%=11r5+<%TN3U<1TL%U23B31%B11r6+>%U33UA1U1%U73G31%G11r7%U92U11rQ:%U;213%U=3UE31p061p0<1p0B1p0F1p0J1p0Q01pR6Q41%TO2Q61%U02Q>1qR<UN1%R:2UO1p0R<1p0R@1p0RF1p0RJ1p0S01p0S41p0S91p0SD1p0SL1p0T=1p0T>1p0T;1p0T@1p0TD1p0TI1p0TM1p0TO1p0U31p0U=1p0U@1p0UH1p0UN1p0V41pRNVA1pS0VB1pQLVC1pR0VD1pQNVE1pR4VF1pQJVG1pQHVH1pR@VJ1pBVK1pR:W11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 2%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 3%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 5%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 6%nat 0%nat).
Variable csz : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 7%nat 0%nat).
Variable ch : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 8%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 9%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cache_pop_core) 10%nat 0%nat).
Lemma art_cache_pop_core : ltac:(sec_stmt2 constr:(SEC_T_art_cache_pop_core) 11%nat 0%nat).
Proof using Type regs M rom c ca ia cnt csz ch st spb.
intros H8 H11 H10 Hc Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
Ccnt Ccsz Cch Cst Cspb Wcnt Wst Ap1 Ap2.
eexists. split.
- zbft (ltac:(oF' 0x567a0%Z)) (ltac:(oD' 0x567a0%Z)).
zstep (ltac:(oF' 0x567a4%Z)) (ltac:(oD' 0x567a4%Z)).
zbft (ltac:(oF' 0x567a8%Z)) (ltac:(oD' 0x567a8%Z)).
zstep (ltac:(oF' 0x567ac%Z)) (ltac:(oD' 0x567ac%Z)).
zstep (ltac:(oF' 0x567b0%Z)) (ltac:(oD' 0x567b0%Z)).
zstep (ltac:(oF' 0x567b4%Z)) (ltac:(oD' 0x567b4%Z)).
zlw (ltac:(oF' 0x567b8%Z)) (ltac:(oD' 0x567b8%Z)) (ca + 80 * c) Ccnt.
zbft (ltac:(oF' 0x567bc%Z)) (ltac:(oD' 0x567bc%Z)).
zstep (ltac:(oF' 0x567c0%Z)) (ltac:(oD' 0x567c0%Z)).
zstep (ltac:(oF' 0x567c4%Z)) (ltac:(oD' 0x567c4%Z)).
zstep (ltac:(oF' 0x567c8%Z)) (ltac:(oD' 0x567c8%Z)).
zsw (ltac:(oF' 0x567cc%Z)) (ltac:(oD' 0x567cc%Z)) (ca + 80 * c) (cnt - 1) ltac:(exact Wcnt).
zstep (ltac:(oF' 0x567d0%Z)) (ltac:(oD' 0x567d0%Z)).
assert (Ccsz1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 8) 8 csz) by recell Ccsz.
assert (Cch1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by recell Cch.
assert (Cst1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8 st) by recell Cst.
assert (Wst1 : wokA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8) by rewok Wst.
zld (ltac:(oF' 0x567d4%Z)) (ltac:(oD' 0x567d4%Z)) (ca + 80 * c + 8) Ccsz1.
stepn (ltac:(oF' 0x567d8%Z)) (ltac:(oD' 0x567d8%Z)). rewrite (art_zb_srli_exact _ 30 (4 * (cnt - 1))) by lia.
zstep (ltac:(oF' 0x567dc%Z)) (ltac:(oD' 0x567dc%Z)).
zlwu (ltac:(oF' 0x567e0%Z)) (ltac:(oD' 0x567e0%Z)) (ca + 80 * c + 16 + 4 * (cnt - 1)) Cch1.
zamoadd_d (ltac:(oF' 0x567e4%Z)) (ltac:(oD' 0x567e4%Z)) (ca + 2576) st csz Cst1 ltac:(exact Wst1).
assert (Cspb2 : cellA (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) (ia + 32) 8 spb) by recell Cspb.
zld (ltac:(oF' 0x567e8%Z)) (ltac:(oD' 0x567e8%Z)) (ia + 32) Cspb2.
zstep (ltac:(oF' 0x567ec%Z)) (ltac:(oD' 0x567ec%Z)).
zstep (ltac:(oF' 0x567f0%Z)) (ltac:(oD' 0x567f0%Z)).
zstep (ltac:(oF' 0x567f4%Z)) (ltac:(oD' 0x567f4%Z)).
zstep (ltac:(oF' 0x567f8%Z)) (ltac:(oD' 0x567f8%Z)).
apply mst_refl.
- split; [gres; f_equal; lia|].
intros r N8 N9 N10 N11 N12 N14; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.
End SE.
Definition art_pop_kept (r : reg) : Prop :=
r <> 1%bv /\ r <> 2%bv /\ r <> 8%bv /\ r <> 9%bv /\ r <> 18%bv /\ r <> 19%bv /\ r <> 20%bv /\ r <> 11%bv /\ r <> 13%bv.
#[local] Ltac post_kept :=
intros r Hr; unfold art_pop_kept in Hr; destruct Hr as (?&?&?&?&?&?&?&?&?); gres; try reflexivity;
repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
#[using="Type"] Lemma art_cache_pop_tail8 : ltac2:(TCodec.tc2 tcn__JbtCachePop "U7&7y5'QByR0%211%5241'0y8%611%311p061'6'3&@r:(Q@+=(1%33A21%6251&QA+8%22C1%;3C41r;+2%;3I19%>231r8%92J1%B3J31&Ezr9%3221&F&C+Q@%22H1&I+R0%22@1%7241&;&Br=+Q8%;2G1u8&QC%12Q?Q4%8576431&>%11Mr?+Q0%D2;1%>5=319Q1r@r>+H%I221%C5B41>Q6rA+@%M2;1%G5F31BQ:rB%Q02:Q?%J5I21EQ=rC%L5K18GQ?'4'2'=&AvQ0rF+ZioL%R03R<1QN/01R<rErD%8576321r1%:591B43%<3Q:31+:%R93RG1R7%R<251%R=2=2%R?3RG21%R?28R2%QI2GQH%R:2RK1%RC3RK31+1%RB3S01R@%RE2>1%RG3RO1Q0%RE3S3R?RC%RH2A1%RB2S3Q7%RK3S321+9%RJ3S81RH%RM2F1%RG2S8QA%S03S821+B%RO3S=1RM%S22K1%RL2S=QJ%S53S=21+C%S43SB1S2%S72Q01%S12SBQJ%S:3SB21+D%S93SG1S7%S<2Q51%S62SGR=%S?3SG21%SJ1SK&?%11Q:r3r2%SD221rH%SF213%SH3T031p071pR6:1%QN2<1%QO2B1%R02H1%R12N1%R22Q41%R32Q91%R42Q>1%R52QC1%R62QI1qR<T;1%R92T<1p0R;1p0R>1p0RB1p0RG1p0RM1p0S21p0S51p0S?1p0SH1p0SM1p0T51pRJTB1pRHTC1pRFTD1pRDTE1pRBTF1pR8TN1pRLTH1pR@TJ1pBTK1pR:U11").
Proof.
intros regs M rom sp raw s0v s1v s2v s3v s4v H13 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
eexists. split.
- zstep (ltac:(oF' 0x567fc%Z)) (ltac:(oD' 0x567fc%Z)).
zbtk (ltac:(oF' 0x56800%Z)) (ltac:(oD' 0x56800%Z)).
zld (ltac:(oF' 0x56810%Z)) (ltac:(oD' 0x56810%Z)) (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56814%Z)) (ltac:(oD' 0x56814%Z)) (sp + 32) C0.
zld (ltac:(oF' 0x56818%Z)) (ltac:(oD' 0x56818%Z)) (sp + 24) C1.
zld (ltac:(oF' 0x5681c%Z)) (ltac:(oD' 0x5681c%Z)) (sp + 16) C2.
zld (ltac:(oF' 0x56820%Z)) (ltac:(oD' 0x56820%Z)) (sp + 8) C3.
zld (ltac:(oF' 0x56824%Z)) (ltac:(oD' 0x56824%Z)) sp C4.
zstep (ltac:(oF' 0x56828%Z)) (ltac:(oD' 0x56828%Z)).
stepret (ltac:(oF' 0x5682c%Z)) (ltac:(oD' 0x5682c%Z)) raw ltac:(rwH; reflexivity).
apply mst_refl.
- repeat (split; [gres; reflexivity|]). post_kept.
Qed.
#[using="Type"] Lemma art_land15_of_mod16 : ltac2:(TCodec.tc2 tcn__JbtCachePop "C'6&Ezr1%3221'3&Gr2+@%3221%53:18&D+?r3%3221%:3?1=p061p0=1pS:B1").
Proof.
intros x Hx Hm. rewrite Z.land_comm. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. exact Hm.
Qed.
#[using="Type"] Lemma art_cache_pop_tail16 : ltac2:(TCodec.tc2 tcn__JbtCachePop "UF&7y5'QByR0%211%5241'0y8%611%311p061'6'3&@r;(Q@+=(1%33A21%6251&QA+@%22C1%;3C41r<+2%;3I19%>231r9%92J1%B3J31r=+:%B3Q01@%E231%G3O16&Ez%221H&F&C+Q@%22B1&I+R0%22D1%7241'2%<2;H%:2I4%3221&G%12EO%Q93Q:1@&;&BrAr?+Q8%C221u8&QC%12QKO%9587431&>r>%211rC+Q0%M2=1%@5?31:5rDrB+H%Q2221%E5D41?:rE%Q52:QH%H5G21B=rF+8%Q92:1%L5K31FArG%N5M18HC'4'=&AvQ0rJ+ZioL%R<3RH1R:/01RHrIrH%8576321r1%:591E43%<3Q;31%RF23R2%RG2;R3%RI3S121%RI26R<%QO2DQN%RD2S51%RM3S531+1%RL3S:1RJ%RO2<1%S13S91Q1%RO3S=NRM%S22?1%RL2S=Q9%S53S=21+9%S43SB1S2%S72D1%S12SBQB%S:3SB21+B%S93SG1S7%S<2I1%S62SGQB%S?3SG21+C%S>3SL1S<%SA2N1%S;2SLR7%SD3SL21+D%SC3T11SA%SF2Q31r@%SA2T21%SJ3T231%T51T6&?%11Q9r3r2%SO221rL%T1213%T33T;31p071pR6:1%S32<1%S42C1%S52I1%S62O1%S72Q51%S82Q:1%S92Q?1%S:2QD1%S;2QH1qR<TF1%R72TG1p0R91p0R<1p0RA1p0RE1p0RK1p0S01p0S41p0S?1p0SC1p0SH1p0T11p0T51p0T;1p0TC1pRJU01pRHU11pRFU21pRDU31pRBU41pR8U<1pR>U61pRLU71pR@U91pBU:1pR:U@1").
Proof.
intros regs M rom sp res raw s0v s1v s2v s3v s4v H13 H2 H10 Hsp Hsp' Hres Hres16 Cra Hret C0 C1 C2 C3 C4.
eexists. split.
- zstep (ltac:(oF' 0x567fc%Z)) (ltac:(oD' 0x567fc%Z)).
zbft (ltac:(oF' 0x56800%Z)) (ltac:(oD' 0x56800%Z)).
zstep (ltac:(oF' 0x56804%Z)) (ltac:(oD' 0x56804%Z)).
stepn (ltac:(oF' 0x56808%Z)) (ltac:(oD' 0x56808%Z)). rwH. rewrite art_zb_and by lia. rewrite (art_land15_of_mod16 res) by lia.
zbft (ltac:(oF' 0x5680c%Z)) (ltac:(oD' 0x5680c%Z)).
zld (ltac:(oF' 0x56810%Z)) (ltac:(oD' 0x56810%Z)) (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56814%Z)) (ltac:(oD' 0x56814%Z)) (sp + 32) C0.
zld (ltac:(oF' 0x56818%Z)) (ltac:(oD' 0x56818%Z)) (sp + 24) C1.
zld (ltac:(oF' 0x5681c%Z)) (ltac:(oD' 0x5681c%Z)) (sp + 16) C2.
zld (ltac:(oF' 0x56820%Z)) (ltac:(oD' 0x56820%Z)) (sp + 8) C3.
zld (ltac:(oF' 0x56824%Z)) (ltac:(oD' 0x56824%Z)) sp C4.
zstep (ltac:(oF' 0x56828%Z)) (ltac:(oD' 0x56828%Z)).
stepret (ltac:(oF' 0x5682c%Z)) (ltac:(oD' 0x5682c%Z)) raw ltac:(rwH; reflexivity).
apply mst_refl.
- repeat (split; [gres; rwH; reflexivity|]). post_kept.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
