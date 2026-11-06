(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtAllocB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocSecB () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6msteps"; "7art_alloc_memB"; "8getr"; "8mkst"; "8regupd"; "9loaded_segments"]; [":add"; ":div"; ":le"; ":lt"; ":max"; ":modulo"; ":mul"; ":pow"; ":sub"; "0ab"; "0ctx"; "0fx"; "0n"; "0ob"; "0regs"; "0rom"]; ["0rs"; "0rz"; "0sp"; ";BV"; ";Z_to_bv"; ";bv"; "0stk"; "0szt"; "0t"; "0trp"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_b_sec_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocSecB "YH&5y5'Q5yR0%211%5241'0y8%611%311p061'4'3&<r>(Q3+2(1%33A21%6251&Q4r;%22C1%;3C41r?+:%;3I19%>231%@3H16r@+9%@3N1>%C231%E3M1;rA+C%E3Q31C%H231&@r:%22C1%3212%F2Q71%O3Q761rB+D%O3Q=1M%Q2231%Q43Q<1JrC+E%Q43QB1Q2%Q7231%Q12QBQ7%Q:3QB21rD+G%Q:3QH1Q8%Q=231r<%Q82QI1%QA3QI31rE+I%QA3QO1Q?%QD231+7%Q?2R01%QH3R031rF+J%QH3R61QF%QK231r=%QF2R71%QO3R731rG+K%QO3R=1QM%R2231+1%QM2R>1%R63R>31&Bz%221G&C+T0%QB2C1&G+R0%22R;1%6241+TP0%;21I%QI2CQ1%QJ21Q9%QK21Q:+Q?%:2RC1%>231&ErH+@%3221%RM3RN1E'2%H2K5+Q8%D2RM1%H281%5241&F&A&DrI+8%3221%R@21QD%6213%8214%S=3S>C1%Q72CD+RP0%Q92F1%C231%I2;G%SC3SD1Q;rKrJ%RL221%RM212%Q>21G%QB2Q84%S026O%QA21Q<%QE2Q;8rL%S421Q=%QE21Q@%QI2Q?3rM%S821QA%QI21QD%QM2QL3+X0%QL251%Q9231%QN27QI%Q;251&9&?rQ:&HrQ7rQ4%SF221%421QF%84761QG&8rQ;rQ8rQ5%SM221+?%<221u1rQ1%95A8321rQ<%T42BR3u8%=5E321R5rQ=%?5G1<3CrQ>%T:2>QLu4%C5K321RNrQ?%E5M1C9IrQ@rQ9%TA21R3%I5Q131=M&7%TD2;J%Q221RD%341RE9S5%TG2:D%Q521RG%641RHQ7R;%TJ2;C%Q821RJ%TL2Q:R>+4%;43RM21rQA%U021G%Q>21S0%?41S1KS1':&=vKrQF+ZXZD%UO3V;1UM/01V;rQErQD%8576321&>%V53VCT4V3+ZXc0%V73VC1V5/01VC%53<41%V52VFR1%732V01+;%V=3VK1V;%V92VJQ7%;3421+<%VA3VO1V?%V=2VNT=%?3421+>%VE3W31VCrQB%V021QA%V121QD%V221QE%VE2W61%G3861+B%VM3W;1VK%VI2W:8%K3421%V92:QL%VL2W=1%N33V31%RI23T;%VO2W@1%Q133V11+H%W73WE1W5%Q4331F%VB29QC%W52WF1%Q733UJ1+cVYL%W=3WI1W;/01WI&;%15Q?JR<QJRO%QF5QE631Q?%QH3S:Q?1p0QJ1p0QO1p0R51p0R91p0R>1p0RC1p0RF1p0RK1p0RN1p0S31p0S>1p0SH1p0SI1p0SL1p0T11p0T51p0T71p0T;1p0T=1p0T@1p0TB1p0TH1p0TK1p0U01p0U;1p0UB1p0UH1p0UO1p0V21p0V:1p0V>1p0VF1p0VN1p0W61p0W>1p0WE1p0WK1p0X61p0X<1p0XB1pR@XO1pRDY01pQLY11pQFY21pRBY31pR>Y41pR4Y51pR2Y61pQJY71pQDY81pR6Y91pR0Y;1p>Y<1pQNYB1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_sec_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_sec_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_sec_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_sec_fn) 3%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_sec_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_sec_fn) 5%nat 0%nat).
Lemma art_alloc_b_sec_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_b_sec_fn) 6%nat 0%nat).
Proof using Type regs M rom sp ab n.
intros rs rz stk t ctx ob trp szt H2 H10 H9 H19 H20 H21 H23 H25 H26 H27 Hsp Hsp' Hab Hab' Hab16 Hn Hrs Hrz Hrz16 Hprim
Hstk Hstk' Ht Ht' Hctx Hctx' Hob Htrp Hszt W Cob C16 Cctx Ctid Ctrp Cszt A1 A2 A3 A4.
assert (Hrsn : n <= rs /\ rs <= n + 15) by (subst rs; split; [|]; lia).
pose proof (art_hdr_b1a_range ob Hob) as Rb1a. pose proof (art_hdr_b1_range ob Hob) as Rb1.
zstep (ltac:(oF' 0x52154%Z)) (ltac:(oD' 0x52154%Z)).
zbft (ltac:(oF' 0x52158%Z)) (ltac:(oD' 0x52158%Z)).
zstep (ltac:(oF' 0x5215c%Z)) (ltac:(oD' 0x5215c%Z)).
stepn (ltac:(oF' 0x52160%Z)) (ltac:(oD' 0x52160%Z)). rwH. rewrite art_zb_and by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
replace ((ab + rz) mod 8) with 0 by lia.
zstep (ltac:(oF' 0x52164%Z)) (ltac:(oD' 0x52164%Z)).
zbtk (ltac:(oF' 0x52168%Z)) (ltac:(oD' 0x52168%Z)).
zstep (ltac:(oF' 0x52174%Z)) (ltac:(oD' 0x52174%Z)).
zbft (ltac:(oF' 0x52178%Z)) (ltac:(oD' 0x52178%Z)).
zlbu (ltac:(oF' 0x5217c%Z)) (ltac:(oD' 0x5217c%Z)) (ab + rz - 15) Cob.
stepn (ltac:(oF' 0x52180%Z)) (ltac:(oD' 0x52180%Z)). rwH. rewrite art_zb_andi by lia. change (Z.land 1 3) with 1.
stepn (ltac:(oF' 0x52184%Z)) (ltac:(oD' 0x52184%Z)). rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612.
pose proof (land_le_l ob 18446744073709551612 ltac:(lia) ltac:(lia)) as Lb.
stepn (ltac:(oF' 0x52188%Z)) (ltac:(oD' 0x52188%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia.
change (Z.lor (Z.land ob 18446744073709551612) 1) with (art_hdr_b1a ob).
stepn (ltac:(oF' 0x5218c%Z)) (ltac:(oD' 0x5218c%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x52190%Z)) (ltac:(oD' 0x52190%Z)). rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small n (2 ^ 48)) by lia.
zsb (ltac:(oF' 0x52194%Z)) (ltac:(oD' 0x52194%Z)) (ab + rz - 15) (art_hdr_b1a ob) ltac:(rewok W).
zsh (ltac:(oF' 0x52198%Z)) (ltac:(oD' 0x52198%Z)) (ab + rz - 14) (n / 2 ^ 32) ltac:(rewok W).
zsw (ltac:(oF' 0x5219c%Z)) (ltac:(oD' 0x5219c%Z)) (ab + rz - 12) n ltac:(rewok W).
zbft (ltac:(oF' 0x521a0%Z)) (ltac:(oD' 0x521a0%Z)).
zstep (ltac:(oF' 0x521a4%Z)) (ltac:(oD' 0x521a4%Z)).
stepn (ltac:(oF' 0x521a8%Z)) (ltac:(oD' 0x521a8%Z)). rwH. rewrite art_zb_andi by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (sp + 16) 8 16) by (unfold apart in *; recell C16) end.
zld (ltac:(oF' 0x521ac%Z)) (ltac:(oD' 0x521ac%Z)) (sp + 16) C16'.
pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)) as Lb2.
stepn (ltac:(oF' 0x521b0%Z)) (ltac:(oD' 0x521b0%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia.
change (Z.lor (Z.land (art_hdr_b1a ob) 143) 16) with (art_hdr_b1 ob).
zsb (ltac:(oF' 0x521b4%Z)) (ltac:(oD' 0x521b4%Z)) (ab + rz - 16 + 1) (art_hdr_b1 ob) ltac:(rewok W).
zbft (ltac:(oF' 0x521b8%Z)) (ltac:(oD' 0x521b8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cctx' : cellA X t 8 ctx) by (unfold apart in *; recell Cctx);
assert (Ctid' : cellA X (ctx + 8) 4 0) by (unfold apart in *; recell Ctid);
assert (Ctrp' : cellA X stk 8 trp) by (unfold apart in *; recell Ctrp);
assert (Cszt' : cellA X (stk + 8) 8 szt) by (unfold apart in *; recell Cszt) end.
zld (ltac:(oF' 0x521bc%Z)) (ltac:(oD' 0x521bc%Z)) t Cctx'.
zlw (ltac:(oF' 0x521c0%Z)) (ltac:(oD' 0x521c0%Z)) (ctx + 8) Ctid'.
zstep (ltac:(oF' 0x521c4%Z)) (ltac:(oD' 0x521c4%Z)).
stepn (ltac:(oF' 0x521c8%Z)) (ltac:(oD' 0x521c8%Z)).
zld (ltac:(oF' 0x52254%Z)) (ltac:(oD' 0x52254%Z)) stk Ctrp'.
zld (ltac:(oF' 0x52258%Z)) (ltac:(oD' 0x52258%Z)) (stk + 8) Cszt'.
stepn (ltac:(oF' 0x5225c%Z)) (ltac:(oD' 0x5225c%Z)).
unfold art_alloc_memB. zret.
Qed.
End SE.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
