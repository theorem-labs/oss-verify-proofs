(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JatLeaf JatAllocG JatPoison ArtRuns ArtRunsMem JatFp JatFree1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatFxDrain () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFxDrain."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1cons"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0F"; "0GB"; "0GL"; "0L"; "4bvmap"]; ["0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_drain_mem"; "9getr"; "9mkst"; "9regupd"; ":loaded_segments"; ";In"; "<add"; "<le"; "<lt"]; ["<pow"; "<sub"; "0bytes"; "0c"; "0fx"; "0gb"; "0gbytes"; "0msz"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0sp"; "=BV"; "=Z_to_bv"]; ["=bv"; "=bv_unsigned"; "0x18"; "0x19"; "0x8"; "0x9"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_drain_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)).
Definition art_drain_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (c L F B bytes GL GB gbytes : Z) : word -> option byte :=
let M2 := Wn 4 (art_drain_frame M sp raw regs) (0x137970 + 152) 1 in
let M3 := if GL =? 0 then Wn 8 (Wn 8 (Wn 8 M2 (0x137970 + 176) B) (0x137970 + 168) F) (0x137970 + 160) L
else Wn 8 (Wn 8 (Wn 8 M2 GB F) (0x137970 + 160) (GL + L)) (0x137970 + 176) B in
Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M3 c 0) (c + 8) 0) (c + 16) 0) (0x137970 + 184) (gbytes + bytes)) (c + 24) 0) (0x137970 + 152) 0.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_drain_pre := (ltac2:(TCodec.tc2 tcn__JatFxDrain "XO&?y5'Q@yR0%211%5241'3y8%611%311p061':'6&Hr=(Q>+1(4%33A21%6251r:%93A21r>+2%93G17%<231&Q?%12H7%@3H31r?+:%@3N1>%C231+QVn[@%82O1%G3O31r@+;%G3Q51E%J231r;%?2Q61%N3Q631&N&M+VbTP0+Q@%3221%521Q2&O&Q0+R0%22M1%42O1z%<21Q1+Q0%=2L1%9216'9%@2H4+RPP0%C221%D2BK%5221&B&Q1rB%221FrA%542H1>'5%M2QH3+QO%H2QC1%J261%5241%Q22G8%M29J%8221%Q52JQCrC%Q62Q>1%Q221O%Q92N3rDrH%Q;221%Q721>&8rE%R?3R@1Q5%311%QB2Q@3+8%QC251%Q?21Q<rL%Q021QD%Q241QE95rK%Q441Q=;7&D&KrO%3421?;%Q3251%Q4281%Q52<1%Q62@1p0B1%9487=R1rQ0%;4:1@QIrQ1+TH%R82RC1+Q8%@4?421&CrQ2u4%35C261R4rQ3u8rN%75G3F21rQ4%RD2@Q2%:5J2154rQ5+@%RH2B1%>5N3198rQ6+H%RL2@1%B5Q231=<rQ7+U0%S02S;1%F5Q631A@%T23T3Q6RH%QF11rQ9+U@%S62SA1%L5Q<31GQ;p051+UH%S:2SE1%Q05Q@71KJ'7'E&IvQ4rQ<+Z^U@%T?3TK1T=/01TKrQ;rQ:%8576321r1+Z^[D%TF3U21TD/01U2&GrQ8%2<91I=OQ3Q7Q:Q>QAQGQI%@5?7419%B3R491%TO29TD%S;25SO%TD2U;1%U33U;31%U32=TA%U53U=1T?%U@1UA&L(1+3%U73UE1U5+4%U93UG1U7%U:3UHRKU8+9%U<3UJ1U:+<%U>3UL1U<+=%U@3UN1U>+B%UB3V01U@+C%UD3V21UB+D%UF3V41UD+E%UH3V61UF+F%UJ3V81UH+G%UL3V:1UJ%UM3V;R5UK+I%UO3V=1UM+J%V13V?1UO+K%V33VA1V1(2%11Q2%Q13Q331%Q23Q461%Q33Q591%Q43Q6<1%Q53Q7>1%Q63Q8A1%Q73Q9D1%Q83Q:G1%Q93Q;J1%Q:3Q<M1%Q;3Q=Q01%Q<3Q>Q31%Q=3Q?Q61%Q>3Q@Q91%Q?3QAQ;1%Q@3QBQ>1%QA3QCVC1%QC3QDR31r3r2%VL221rQ>%VN213%W03W831p071pRBQL1%U82QN1%U92R11%U:2R61qRHW=1%RK2W>1p0RM1p0S11p0S91p0S>1p0SC1p0SH1p0SL1p0T11p0T61p0T<1p0T?1p0TA1p0U81p0U=1p0U?1p0UC1p0UG1p0UF1p0UG1p0UK1p0V21p0V91p0V@1p0VD1p0VG1p0VM1p0W41p0W<1p0WD1p0WL1pR>X71pJX81pLX91pR6X:1p2X;1pHX<1pNX=1pR8X>1pRLX?1pRDXG1pRJXB1pQ2XC1pRFXI1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 5%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 6%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 7%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 8%nat 0%nat).
Variable bytes : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 9%nat 0%nat).
Variable GL : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 10%nat 0%nat).
Variable GB : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 11%nat 0%nat).
Variable gbytes : ltac:(sec_ty2 constr:(SEC_T_art_drain_pre) 12%nat 0%nat).
Lemma art_drain_pre : ltac:(sec_stmt2 constr:(SEC_T_art_drain_pre) 13%nat 0%nat).
Proof using Type regs M rom raw sp c L F B bytes GL GB gbytes.
intros H1 H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb Hgb' HGL HGL' HGB W Wc Wq Clk CL CF CB Cby CGL CGB Cgb.
destruct (Z.eq_dec GL 0) as [EG|NG].
-
eexists. split.
{
zstep (ltac:(oF' 0x538b0%Z)) (ltac:(oD' 0x538b0%Z)).
zsd (ltac:(oF' 0x538b4%Z)) (ltac:(oD' 0x538b4%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x538b8%Z)) (ltac:(oD' 0x538b8%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x538bc%Z)) (ltac:(oD' 0x538bc%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x538c0%Z)) (ltac:(oD' 0x538c0%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x538c4%Z)) (ltac:(oD' 0x538c4%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zstep (ltac:(oF' 0x538c8%Z)) (ltac:(oD' 0x538c8%Z)). zstep (ltac:(oF' 0x538cc%Z)) (ltac:(oD' 0x538cc%Z)).
stepn (ltac:(oF' 0x538d0%Z)) (ltac:(oD' 0x538d0%Z)). rwH. zclosed (0x137970 + 152).
zstep (ltac:(oF' 0x538d4%Z)) (ltac:(oD' 0x538d4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x137970 + 152) 4 0) by zcell; assert (Wlk' : wokA X (0x137970 + 152) 4) by zwok end.
zcas6 (ltac:(oF' 0x538d8%Z)) (ltac:(oD' 0x538d8%Z)) (ltac:(oF' 0x538dc%Z)) (ltac:(oD' 0x538dc%Z)) (ltac:(oF' 0x538e0%Z)) (ltac:(oD' 0x538e0%Z)) (ltac:(oF' 0x538e4%Z)) (ltac:(oD' 0x538e4%Z)) (ltac:(oF' 0x538e8%Z)) (ltac:(oD' 0x538e8%Z)) (ltac:(oF' 0x538ec%Z)) (ltac:(oD' 0x538ec%Z)) (0x137970 + 152) 0 1 1 1 Clk' Wlk'.
zbft (ltac:(oF' 0x538f0%Z)) (ltac:(oD' 0x538f0%Z)).
stepn (ltac:(oF' 0x538f4%Z)) (ltac:(oD' 0x538f4%Z)). rwH. zclosed 0.
zbft (ltac:(oF' 0x538f8%Z)) (ltac:(oD' 0x538f8%Z)).
zstep (ltac:(oF' 0x538fc%Z)) (ltac:(oD' 0x538fc%Z)).
zbft (ltac:(oF' 0x53900%Z)) (ltac:(oD' 0x53900%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell; assert (CGL' : cellA X (0x137970 + 160) 8 GL) by zcell end.
zld (ltac:(oF' 0x53904%Z)) (ltac:(oD' 0x53904%Z)) c CL'.
zbft (ltac:(oF' 0x53908%Z)) (ltac:(oD' 0x53908%Z)).
zld (ltac:(oF' 0x5390c%Z)) (ltac:(oD' 0x5390c%Z)) (0x137970 + 160) CGL'.
zbtk (ltac:(oF' 0x53910%Z)) (ltac:(oD' 0x53910%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CB' : cellA X (c + 16) 8 B) by zcell; assert (CF' : cellA X (c + 8) 8 F) by zcell; assert (CL2 : cellA X c 8 L) by zcell end.
zld (ltac:(oF' 0x53934%Z)) (ltac:(oD' 0x53934%Z)) (c + 16) CB'.
zsd (ltac:(oF' 0x53938%Z)) (ltac:(oD' 0x53938%Z)) (0x137970 + 176) B ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF2 : cellA X (c + 8) 8 F) by zcell end.
zld (ltac:(oF' 0x5393c%Z)) (ltac:(oD' 0x5393c%Z)) (c + 8) CF2.
zsd (ltac:(oF' 0x53940%Z)) (ltac:(oD' 0x53940%Z)) (0x137970 + 168) F ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL3 : cellA X c 8 L) by zcell end.
zld (ltac:(oF' 0x53944%Z)) (ltac:(oD' 0x53944%Z)) c CL3.
zsd (ltac:(oF' 0x53948%Z)) (ltac:(oD' 0x53948%Z)) (0x137970 + 160) L ltac:(zwok').
zsd (ltac:(oF' 0x5394c%Z)) (ltac:(oD' 0x5394c%Z)) c 0 ltac:(zwok'). zsd (ltac:(oF' 0x53950%Z)) (ltac:(oD' 0x53950%Z)) (c + 8) 0 ltac:(zwok'). zsd (ltac:(oF' 0x53954%Z)) (ltac:(oD' 0x53954%Z)) (c + 16) 0 ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell; assert (Cgb' : cellA X (0x137970 + 184) 8 gbytes) by zcell end.
zld (ltac:(oF' 0x53958%Z)) (ltac:(oD' 0x53958%Z)) (c + 24) Cby'.
zld (ltac:(oF' 0x5395c%Z)) (ltac:(oD' 0x5395c%Z)) (0x137970 + 184) Cgb'.
zstep (ltac:(oF' 0x53960%Z)) (ltac:(oD' 0x53960%Z)).
zsd (ltac:(oF' 0x53964%Z)) (ltac:(oD' 0x53964%Z)) (0x137970 + 184) (gbytes + bytes) ltac:(zwok').
zsd (ltac:(oF' 0x53968%Z)) (ltac:(oD' 0x53968%Z)) (c + 24) 0 ltac:(zwok').
stepfence (ltac:(oF' 0x5396c%Z)) (ltac:(oD' 0x5396c%Z)).
zsb (ltac:(oF' 0x53970%Z)) (ltac:(oD' 0x53970%Z)) (0x137970 + 152) 0 ltac:(zwok').
unfold art_drain_mem, art_drain_frame. rewrite (proj2 (Z.eqb_eq GL 0) EG). apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity|reflexivity|zmem_eq]. }
split; [gres; f_equal; lia|]. split; [gres; exact H10|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
-
destruct (HGB NG) as (GB0 & GB1 & AGs & AGc & WGB). specialize (CGB NG).
eexists. split.
{
zstep (ltac:(oF' 0x538b0%Z)) (ltac:(oD' 0x538b0%Z)).
zsd (ltac:(oF' 0x538b4%Z)) (ltac:(oD' 0x538b4%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x538b8%Z)) (ltac:(oD' 0x538b8%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x538bc%Z)) (ltac:(oD' 0x538bc%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x538c0%Z)) (ltac:(oD' 0x538c0%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x538c4%Z)) (ltac:(oD' 0x538c4%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zstep (ltac:(oF' 0x538c8%Z)) (ltac:(oD' 0x538c8%Z)). zstep (ltac:(oF' 0x538cc%Z)) (ltac:(oD' 0x538cc%Z)).
stepn (ltac:(oF' 0x538d0%Z)) (ltac:(oD' 0x538d0%Z)). rwH. zclosed (0x137970 + 152).
zstep (ltac:(oF' 0x538d4%Z)) (ltac:(oD' 0x538d4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x137970 + 152) 4 0) by zcell; assert (Wlk' : wokA X (0x137970 + 152) 4) by zwok end.
zcas6 (ltac:(oF' 0x538d8%Z)) (ltac:(oD' 0x538d8%Z)) (ltac:(oF' 0x538dc%Z)) (ltac:(oD' 0x538dc%Z)) (ltac:(oF' 0x538e0%Z)) (ltac:(oD' 0x538e0%Z)) (ltac:(oF' 0x538e4%Z)) (ltac:(oD' 0x538e4%Z)) (ltac:(oF' 0x538e8%Z)) (ltac:(oD' 0x538e8%Z)) (ltac:(oF' 0x538ec%Z)) (ltac:(oD' 0x538ec%Z)) (0x137970 + 152) 0 1 1 1 Clk' Wlk'.
zbft (ltac:(oF' 0x538f0%Z)) (ltac:(oD' 0x538f0%Z)).
stepn (ltac:(oF' 0x538f4%Z)) (ltac:(oD' 0x538f4%Z)). rwH. zclosed 0.
zbft (ltac:(oF' 0x538f8%Z)) (ltac:(oD' 0x538f8%Z)).
zstep (ltac:(oF' 0x538fc%Z)) (ltac:(oD' 0x538fc%Z)).
zbft (ltac:(oF' 0x53900%Z)) (ltac:(oD' 0x53900%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell; assert (CGL' : cellA X (0x137970 + 160) 8 GL) by zcell end.
zld (ltac:(oF' 0x53904%Z)) (ltac:(oD' 0x53904%Z)) c CL'.
zbft (ltac:(oF' 0x53908%Z)) (ltac:(oD' 0x53908%Z)).
zld (ltac:(oF' 0x5390c%Z)) (ltac:(oD' 0x5390c%Z)) (0x137970 + 160) CGL'.
zbft (ltac:(oF' 0x53910%Z)) (ltac:(oD' 0x53910%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CGB' : cellA X (0x137970 + 176) 8 GB) by zcell; assert (CB' : cellA X (c + 16) 8 B) by zcell; assert (CF' : cellA X (c + 8) 8 F) by zcell end.
zld (ltac:(oF' 0x53914%Z)) (ltac:(oD' 0x53914%Z)) (0x137970 + 176) CGB'.
zld (ltac:(oF' 0x53918%Z)) (ltac:(oD' 0x53918%Z)) (c + 8) CF'.
zld (ltac:(oF' 0x5391c%Z)) (ltac:(oD' 0x5391c%Z)) (c + 16) CB'.
zstep (ltac:(oF' 0x53920%Z)) (ltac:(oD' 0x53920%Z)).
zsd (ltac:(oF' 0x53924%Z)) (ltac:(oD' 0x53924%Z)) GB F ltac:(zwok').
zsd (ltac:(oF' 0x53928%Z)) (ltac:(oD' 0x53928%Z)) (0x137970 + 160) (GL + L) ltac:(zwok').
zsd (ltac:(oF' 0x5392c%Z)) (ltac:(oD' 0x5392c%Z)) (0x137970 + 176) B ltac:(zwok').
stepn (ltac:(oF' 0x53930%Z)) (ltac:(oD' 0x53930%Z)).
zsd (ltac:(oF' 0x5394c%Z)) (ltac:(oD' 0x5394c%Z)) c 0 ltac:(zwok'). zsd (ltac:(oF' 0x53950%Z)) (ltac:(oD' 0x53950%Z)) (c + 8) 0 ltac:(zwok'). zsd (ltac:(oF' 0x53954%Z)) (ltac:(oD' 0x53954%Z)) (c + 16) 0 ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell; assert (Cgb' : cellA X (0x137970 + 184) 8 gbytes) by zcell end.
zld (ltac:(oF' 0x53958%Z)) (ltac:(oD' 0x53958%Z)) (c + 24) Cby'.
zld (ltac:(oF' 0x5395c%Z)) (ltac:(oD' 0x5395c%Z)) (0x137970 + 184) Cgb'.
zstep (ltac:(oF' 0x53960%Z)) (ltac:(oD' 0x53960%Z)).
zsd (ltac:(oF' 0x53964%Z)) (ltac:(oD' 0x53964%Z)) (0x137970 + 184) (gbytes + bytes) ltac:(zwok').
zsd (ltac:(oF' 0x53968%Z)) (ltac:(oD' 0x53968%Z)) (c + 24) 0 ltac:(zwok').
stepfence (ltac:(oF' 0x5396c%Z)) (ltac:(oD' 0x5396c%Z)).
zsb (ltac:(oF' 0x53970%Z)) (ltac:(oD' 0x53970%Z)) (0x137970 + 152) 0 ltac:(zwok').
unfold art_drain_mem, art_drain_frame. rewrite (proj2 (Z.eqb_neq GL 0) NG). apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity|reflexivity|zmem_eq]. }
split; [gres; f_equal; lia|]. split; [gres; exact H10|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
#[using="Type"] Lemma art_drain_ret_fn : ltac2:(TCodec.tc2 tcn__JatFxDrain "TK&?y5'Q@yR0%211%5241'3y8%611%311p061':'6&Hr:(Q>+2(4%33A21%6251&Q?&Q1r6+Q@%3221%52F1%>3F71r;+:%>3L1<%A231+QVn[@%<2M1%E3M31&Fr9%211&N%12?3&O&Q0+R0%22J1%42M1'5z%921Q0+L%82Q01%<2Q31%6241%7258&C&KrC&M+UH%22J1u8r?%8576321rD%72OE%;5:215?rErB+8%Q>221&QA%12R2?%B5A63<1rF+@%QD2C1rA%G5F42A1rG+H%QI2A1%K5J31E5rH+Q0%QM2B1%O5N31I9rI+Q8%R12?1%Q35Q231M='E&IvQ4rK+Z^[D%R>3RJ1R</01RJrJ%756521<&J+1%RD3S21RB%3391D%RA2S2I%532RD1%RH3S6Q5RF%RD2S5Q8%83321+9%RL3S:1RJ%RH2S9Q?%<3421+;%S03S>1RN%RL2S=Q9%@3421+>%S43SB1S2%S02SAR4%D3421+B%S83SF1S6%S42SER2%H3421+C%S<3SJ1S:%S82SIQK%L3421%Q55Q41Q>OQ:%Q73R:O1p0Q91p0Q>1p0QC1p0QH1p0QN1p0R61p0R:1p0RD1p0RE1p0RF1p0RG1p0RI1p0S11p0S71p0S:1p0S>1p0SF1pS8T61pS6T71pS<T81pS:T91pR<T:1pRLT;1pRDTC1pRJT>1pQ2T?1pRFTE1").
Proof.
intros regs M rom raw sp gb x8 x9 x18 x19 H2 H10 Hret Hsp Hsp' Hgb Hx8 Hx9 Hx18 Hx19 Cgb Cmax F1 F8 F9 F18 F19.
zld (ltac:(oF' 0x53974%Z)) (ltac:(oD' 0x53974%Z)) (0x137970 + 184) Cgb.
zld (ltac:(oF' 0x53978%Z)) (ltac:(oD' 0x53978%Z)) (0x137970 + 64) Cmax.
zbtk (ltac:(oF' 0x5397c%Z)) (ltac:(oD' 0x5397c%Z)).
zld (ltac:(oF' 0x539c8%Z)) (ltac:(oD' 0x539c8%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x539cc%Z)) (ltac:(oD' 0x539cc%Z)) (sp - 16) F8. zld (ltac:(oF' 0x539d0%Z)) (ltac:(oD' 0x539d0%Z)) (sp - 24) F9. zld (ltac:(oF' 0x539d4%Z)) (ltac:(oD' 0x539d4%Z)) (sp - 32) F18. zld (ltac:(oF' 0x539d8%Z)) (ltac:(oD' 0x539d8%Z)) (sp - 40) F19.
zstep (ltac:(oF' 0x539dc%Z)) (ltac:(oD' 0x539dc%Z)).
stepret (ltac:(oF' 0x539e0%Z)) (ltac:(oD' 0x539e0%Z)) raw ltac:(gres; reflexivity).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_drain_rcy_fn := (ltac2:(TCodec.tc2 tcn__JatFxDrain "V4&?y5'Q@yR0%211%5241'3y8%611%311p061':'6&Hr;(Q>+2(4%33A21%6251&Q?&Q1r7+Q@%3221%52F1%>3F71r<+:%>3L1<%A231+QVn[@%<2M1%E3M31&Nr9%22=1&Or:&Q0+R0%22I1%5241'5+L%62M1%9218%4215z%?21;%7218&M+VbTP0%221NrA%E221&C&KrE+UH%92M1u8%6554218rF%=2Q1H%958214DrG+R8%A2Q51rB%>5=4291rH+TH%F2Q:1u4%C5B421K&DrI+4%34F261rJ+8%QM2@1&QA%12RA=%M5L53H1rK+@%R32A1%Q15Q031LOrL+H%R72?1%Q55Q431Q0Q3rM+Q0%R;2@1%Q95Q831Q4Q7rN+Q8%R?2>1%Q=5Q<31Q8Q;'E&IvQ4rQ0+Z^[D%RL3S81RJ/01S8rO%756521<&J+1%S23S@1S0%3391D%RO2S@I%532S21+5%S73SE1S5%S32SDR7%93421%S:3SHQ8S8%S62SGQ=%<3321+9%S>3SL1S<%S:2SKQG%@3421+;%SB3T01S@%S>2SOQB%D3421+>%SF3T41SD+Qoh0%SC2T41%I3531+?%SK3T91SI+X0%SH2T91%N3531%SO3T=QGSM+QVn`8%SL2T=1%Q23431+A%T43TB1T2%Q5331M+B%T73TE1T5%T32TDRE%Q93421+C%T;3TI1T9%T72THRL%Q=3421+Z^bD%T?3TK1T=/01TK&A%14RGQDRHF%QK5QJ631R0%QM3S:QE1p0QO1p0R41p0R91p0R>1p0RC1p0RJ1p0RO1p0S51p0S;1p0S?1p0SG1p0SM1p0SN1p0SO1p0T01p0T11p0T51p0T;1p0TB1p0TF1p0TN1pS8U>1pS6U?1pS<U@1pS:UA1pR@UB1pR<UC1pRLUD1pRDUL1pRJUG1pQ2UH1pRFUN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 4%nat 0%nat).
Variable gb : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 5%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 6%nat 0%nat).
Variable x8 : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 7%nat 0%nat).
Variable x9 : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 8%nat 0%nat).
Variable x18 : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 9%nat 0%nat).
Variable x19 : ltac:(sec_ty2 constr:(SEC_T_art_drain_rcy_fn) 10%nat 0%nat).
Lemma art_drain_rcy_fn : ltac:(sec_stmt2 constr:(SEC_T_art_drain_rcy_fn) 11%nat 0%nat).
Proof using Type regs M rom raw sp gb msz x8 x9 x18 x19.
intros H2 H10 Hsp Hsp' Hgb Hmsz Hx8 Hx9 Hx18 Hx19 IMG Cgb Cmax Cmin Clk Wlk F1 F8 F9 F18 F19.
zld (ltac:(oF' 0x53974%Z)) (ltac:(oD' 0x53974%Z)) (0x137970 + 184) Cgb.
zld (ltac:(oF' 0x53978%Z)) (ltac:(oD' 0x53978%Z)) (0x137970 + 64) Cmax.
zbft (ltac:(oF' 0x5397c%Z)) (ltac:(oD' 0x5397c%Z)).
zstep (ltac:(oF' 0x53980%Z)) (ltac:(oD' 0x53980%Z)). zstep (ltac:(oF' 0x53984%Z)) (ltac:(oD' 0x53984%Z)). zstep (ltac:(oF' 0x53988%Z)) (ltac:(oD' 0x53988%Z)).
stepn (ltac:(oF' 0x5398c%Z)) (ltac:(oD' 0x5398c%Z)). rwH. zclosed (0x137970 + 152).
stepn (ltac:(oF' 0x53990%Z)) (ltac:(oD' 0x53990%Z)). rwH. zclosed 1.
stepn (ltac:(oF' 0x53994%Z)) (ltac:(oD' 0x53994%Z)). rwH. zclosed 8.
stepn (ltac:(oF' 0x53998%Z)) (ltac:(oD' 0x53998%Z)). rwH. zclosed 65280.
stepn (ltac:(oF' 0x5399c%Z)) (ltac:(oD' 0x5399c%Z)). rwH. zclosed 256.
assert (Wlk' : wokA M (0x137970 + 152) 4) by (apply (wr_wok _ _ _ _ Wlk); cbn; lia).
zcas6 (ltac:(oF' 0x539a0%Z)) (ltac:(oD' 0x539a0%Z)) (ltac:(oF' 0x539a4%Z)) (ltac:(oD' 0x539a4%Z)) (ltac:(oF' 0x539a8%Z)) (ltac:(oD' 0x539a8%Z)) (ltac:(oF' 0x539ac%Z)) (ltac:(oD' 0x539ac%Z)) (ltac:(oF' 0x539b0%Z)) (ltac:(oD' 0x539b0%Z)) (ltac:(oF' 0x539b4%Z)) (ltac:(oD' 0x539b4%Z)) (0x137970 + 152) 0 256 256 256 Clk Wlk'.
zbft (ltac:(oF' 0x539b8%Z)) (ltac:(oD' 0x539b8%Z)).
stepn (ltac:(oF' 0x539bc%Z)) (ltac:(oD' 0x539bc%Z)). rwH. zclosed 0.
stepn (ltac:(oF' 0x539c0%Z)) (ltac:(oD' 0x539c0%Z)). rwH. zclosed 0.
zbtk (ltac:(oF' 0x539c4%Z)) (ltac:(oD' 0x539c4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cmin' : cellA X (0x137970 + 72) 8 msz) by zcell; assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell;
assert (F9' : cellA X (sp - 24) 8 x9) by zcell; assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell end.
zld (ltac:(oF' 0x539e4%Z)) (ltac:(oD' 0x539e4%Z)) (0x137970 + 72) Cmin'.
zld (ltac:(oF' 0x539e8%Z)) (ltac:(oD' 0x539e8%Z)) (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x539ec%Z)) (ltac:(oD' 0x539ec%Z)) (sp - 16) F8'. zld (ltac:(oF' 0x539f0%Z)) (ltac:(oD' 0x539f0%Z)) (sp - 24) F9'. zld (ltac:(oF' 0x539f4%Z)) (ltac:(oD' 0x539f4%Z)) (sp - 32) F18'. zld (ltac:(oF' 0x539f8%Z)) (ltac:(oD' 0x539f8%Z)) (sp - 40) F19'.
zstep (ltac:(oF' 0x539fc%Z)) (ltac:(oD' 0x539fc%Z)).
stepn (ltac:(oF' 0x53a00%Z)) (ltac:(oD' 0x53a00%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_drain_mem_lock : ltac2:(TCodec.tc2 tcn__JatFxDrain "RE'Q@yR0%211'3y8%511%311p051':&?y5%2219&N&M+VbTP0+Q@%3221r;%6221&Or<&Q0+2+R0%3221%6251zr:%@221+Q0%A2=1%<217'9%D2=4+RPP0%G221%H2F@%5221&8'6r8%23Q11?%411'5%Q02N4+8%Q1261%L21G%5241p071&C&K&GrBrAr@r?r>r=r9r7%9<876543Q9Q<Q22E1+QVn[@+TH%QC221u4%@5?521Q8p0B1p0O1p0Q61p0Q:1p0Q>1p0QF1pR>R11pJR21pLR31pR6R41p2R51pHR61pNR71pR8R81pRFR61pRDR@1pRLR;1pQ2R=1").
Proof.
intros M sp raw regs c L F B bytes GL GB gbytes IMG Hsp' Hc Hc' Hci HGB.
change (cellA (art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) (0x137970 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
apply cell4_join; [lia|lia|lia|lia|lia| | | ].
- unfold art_drain_mem. apply cell_Wn_hit; [lia|cbn; lia].
- unfold art_drain_mem. destruct (Z.eqb_spec GL 0) as [EG|NG].
+ do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x137970 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
destruct (cell4_split X (0x137970 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & Cb1 & _) end. exact Cb1.
+ destruct (HGB NG) as (GB0 & GB1).
do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x137970 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
destruct (cell4_split X (0x137970 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & Cb1 & _) end. exact Cb1.
- unfold art_drain_mem. destruct (Z.eqb_spec GL 0) as [EG|NG].
+ do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x137970 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
destruct (cell4_split X (0x137970 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & _ & Cb2) end. exact Cb2.
+ destruct (HGB NG) as (GB0 & GB1).
do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x137970 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
destruct (cell4_split X (0x137970 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & _ & Cb2) end. exact Cb2.
Qed.
Section SE.
Local Abbreviation SEC_T_art_drain_nr_run := (forall regs (M rom : word -> option byte) (raw : word) (sp c L F B bytes GL GB gbytes : Z), getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x137970 -> getr regs 11 = Z_to_bv 64 c ->
0x691000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x691000 <= c) -> apart (sp - 48) 48 c 32 ->
1 <= L < 2 ^ 63 -> 0 <= F < 2 ^ 64 -> 0 <= B < 2 ^ 64 -> 0 <= bytes -> 0 <= gbytes -> gbytes + bytes <= 2 ^ 28 -> 0 <= GL -> GL + L < 2 ^ 63 ->
(GL <> 0 -> 0x691000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart c 32 GB 8 /\ wrA M GB 8) ->
wrA M (sp - 48) 48 -> wrA M c 32 -> wrA M (0x137970 + 152) 40 ->
cellA M (0x137970 + 152) 4 0 -> cellA M (0x137970 + 64) 8 (2 ^ 28) ->
cellA M c 8 L -> cellA M (c + 8) 8 F -> cellA M (c + 16) 8 B -> cellA M (c + 24) 8 bytes ->
cellA M (0x137970 + 160) 8 GL -> (GL <> 0 -> cellA M (0x137970 + 176) 8 GB) -> cellA M (0x137970 + 184) 8 gbytes ->
exists regs' (M' : word -> option byte),
msteps ASEGS (mkst regs (0x538b0 : word) M rom) (mkst regs' raw M' rom)
/\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
/\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
/\ mem_grows M M' /\ art_agree [(sp - 48, 48); (0x137970 + 152, 16); (0x137970 + 176, 16); (c, 32); ((if GL =? 0 then 0x137970 + 168 else GB), 8)] M M'
/\ cellA M' c 8 0 /\ cellA M' (c + 8) 8 0 /\ cellA M' (c + 16) 8 0 /\ cellA M' (c + 24) 8 0
/\ cellA M' (0x137970 + 160) 8 (GL + L) /\ cellA M' (0x137970 + 176) 8 B /\ cellA M' (0x137970 + 184) 8 (gbytes + bytes) /\ cellA M' (0x137970 + 152) 4 0
/\ (GL = 0 -> cellA M' (0x137970 + 168) 8 F) /\ (GL <> 0 -> cellA M' GB 8 F)) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 5%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 6%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 7%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 8%nat 0%nat).
Variable bytes : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 9%nat 0%nat).
Variable GL : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 10%nat 0%nat).
Variable GB : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 11%nat 0%nat).
Variable gbytes : ltac:(sec_ty2 constr:(SEC_T_art_drain_nr_run) 12%nat 0%nat).
Lemma art_drain_nr_run : ltac:(sec_stmt2 constr:(SEC_T_art_drain_nr_run) 13%nat 0%nat).
Proof using Type regs M rom raw sp c L F B bytes GL GB gbytes.
intros H1 Hret H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb Hgb' HGL HGL' HGB W Wc Wq Clk Cmax CL CF CB Cby CGL CGB Cgb.
destruct (art_drain_pre regs M rom raw sp c L F B bytes GL GB gbytes H1 H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb ltac:(lia) HGL HGL' HGB W Wc Wq Clk CL CF CB Cby CGL CGB Cgb)
as (r1 & RUN1 & R2 & R10 & RK).
set (M1 := art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) in *.
pose proof Ac as Xc. unfold apart in Xc.
assert (FACTS : mem_grows M M1 /\ art_agree [(sp - 48, 48); (0x137970 + 152, 16); (0x137970 + 176, 16); (c, 32); ((if GL =? 0 then 0x137970 + 168 else GB), 8)] M M1
/\ cellA M1 c 8 0 /\ cellA M1 (c + 8) 8 0 /\ cellA M1 (c + 16) 8 0 /\ cellA M1 (c + 24) 8 0
/\ cellA M1 (0x137970 + 160) 8 (GL + L) /\ cellA M1 (0x137970 + 176) 8 B /\ cellA M1 (0x137970 + 184) 8 (gbytes + bytes)
/\ (GL = 0 -> cellA M1 (0x137970 + 168) 8 F) /\ (GL <> 0 -> cellA M1 GB 8 F)
/\ cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
/\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (0x137970 + 64) 8 (2 ^ 28)).
{ unfold M1, art_drain_mem, art_drain_frame. destruct (Z.eqb_spec GL 0) as [EG|NG].
- split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|].
repeat split; try (intros E; try contradiction); try zcell. rewrite EG. zcell.
- destruct (HGB NG) as (GB0 & GB1 & AGs & AGc & WGB). unfold apart in AGs, AGc.
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|].
repeat split; try (intros E; try contradiction); try zcell. }
destruct FACTS as (G1 & A1 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & F1 & F8 & F9 & F18 & F19 & Cmax').
pose proof (art_drain_ret_fn r1 M1 rom raw sp (gbytes + bytes) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) R2 R10 Hret ltac:(lia) ltac:(lia) ltac:(lia)
(u64_range _) (u64_range _) (u64_range _) (u64_range _) C7 Cmax' F1 F8 F9 F18 F19) as RUN2.
eexists. exists M1. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
split; [gres; reflexivity|]. split; [gres; reflexivity|].
split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; first [apply Z_to_bv_bv_unsigned | apply RK; inl]. }
split; [exact G1|]. split; [exact A1|].
repeat (split; [assumption|]). split; [|split; assumption].
unfold M1. apply art_drain_mem_lock; try assumption. intros NG. destruct (HGB NG) as (GB0 & GB1 & _). split; assumption.
Qed.
End SE.
End FPX.
