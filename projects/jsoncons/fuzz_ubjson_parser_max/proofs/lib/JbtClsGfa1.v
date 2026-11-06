(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG JbtRefill1 JbtPopulate4 JbtFp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtClsGfa1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtClsGfa1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRefill1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "3le"; "3lt"; "4nth"; "5Z"]; ["6bvmap"; "0M"; "0M'"; "7apart"; "7cell"; "7wr"; "8msteps"; "9ret_ok"; ":art_gfa_fcells"; ";art_agree"; ";art_gap"; "<art_gfa_frame"; "<art_w4s"; "=getr"; "=mkst"; ">mem_grows"]; ["?loaded_segments"; "@add"; "@le"; "@lt"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0W"; "0c"; "0chp"; "0dst"; "0fx"; "0g18"; "0g19"; "0g20"]; ["0g21"; "0g22"; "0g23"; "0g24"; "0g25"; "0g26"; "0g27"; "0g8"; "0g9"; "0j"; "0n"; "0na"; "0qris"; "0r"; "0raw"; "0regs"]; ["0regs'"; "0ris"; "0rom"; "0sp"; "0spb"; "0src"; "0st"; "ABV"; "AZ_to_bv"; "Abv"; "0ws"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_agree_w4s : ltac2:(TCodec.tc2 tcn__JbtClsGfa1 "QF'2'?%211'R9yR0%211'5y8%511%311p051&Q2zr1%3221&Q3&Q1r2&Q4+4&Q5&1r4%22F1%411%7261%:291&Q6+2+R0%3221%@251&I(0'7%12Q2Q2(6r3r5%B2Q61%D11%G2F1%64Q9Q951(4%119%<3:31&L%13I:9%@33J1p0B1p0Q41pRHQB1pQ4Q:1pTFQC1").
Proof. intros ws M dst Hd Hd' x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_w4s_outside; [exact Hd|exact Hd'|exact Hx]. Qed.
Definition art_gfa_fcells (M : word -> option byte) (sp : Z) (raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 : word) : Prop :=
cellA M (sp - 8) 8 (U raw) /\ cellA M (sp - 16) 8 (U g8) /\ cellA M (sp - 24) 8 (U g9) /\ cellA M (sp - 32) 8 (U g18) /\ cellA M (sp - 40) 8 (U g19)
/\ cellA M (sp - 48) 8 (U g20) /\ cellA M (sp - 56) 8 (U g21) /\ cellA M (sp - 64) 8 (U g22) /\ cellA M (sp - 72) 8 (U g23) /\ cellA M (sp - 80) 8 (U g24)
/\ cellA M (sp - 88) 8 (U g25) /\ cellA M (sp - 96) 8 (U g26) /\ cellA M (sp - 104) 8 (U g27).
Lemma art_gfa_fcells_tr : ltac2:(TCodec.tc2 tcn__JbtClsGfa1 "R5'2'7'?%2211%411'R9yR0%211'5y8%511%311p051&IrAr@r?%43321&JrB&Q7+S8%2261%53412&Q2%124:&Q3&Q6+2+R0%3221%52A1&HrDr>r=r<r;r:r9r8r7r6r5%<?;INML:987654321rC%>?=1KQ0ON<;:987654p031p0A1p0H1p0K1p0Q21pS>Q=1pS<Q>1pS:Q?1pS8Q@1pS6QA1pS4QB1pS2QC1pS0QD1pRNQE1pRLQF1pSBQG1pS@QH1pSNQI1pT8QO1pQ6QF1pQ4QG1pRBR01").
Proof.
intros W M M' sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 A G Hsp Hsp' F.
assert (T : forall a v, sp - 104 <= a -> a + 8 <= sp -> cellA M a 8 v -> cellA M' a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact C]. }
destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
unfold art_gfa_fcells. repeat split; apply T; first [lia | assumption].
Qed.
Section SE.
Local Abbreviation SEC_T_art_gfa_fcells_frame := (ltac2:(TCodec.tc2 tcn__JbtClsGfa1 "R:'R9yR0%211'5y8%511%311p051'?&@y5%2219&Q2+S8r3%3221&Q3r4&Q6+2+R0%3221%6251&H&Kr6r5%3421:=&M(R7+8(8%33F21%52C1+9%63I14%82F1+B%93L17%;2I1+C%<3O1:%>2L1+D%?3Q21=%A2O1+E%B3Q51@%D2Q21+F%E3Q81C%G2Q51+G%H3Q;1F%J2Q81+H%K3Q>1I%M2Q;1+I%N3QA1L%Q02Q>1+J%Q13QD1O%Q32QA1+K%Q43QG1Q2%Q62QD1%Q<?Q8Q9QBQ2OLIFC@=:741p0Q>1p0QF1pT0QK1pSNR51pT8R01pQ4R21")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_gfa_fcells_frame) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_gfa_fcells_frame) 1%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_gfa_fcells_frame) 2%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_gfa_fcells_frame) 3%nat 0%nat).
Lemma art_gfa_fcells_frame : ltac:(sec_stmt2 constr:(SEC_T_art_gfa_fcells_frame) 4%nat 0%nat).
Proof.
intros Hsp Hsp'.
unfold art_gfa_fcells, art_gfa_frame. repeat split; zcell. Qed.
End SE.
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_clsgfa_finish : ltac2:(TCodec.tc2 tcn__JbtClsGfa1 "\4'2'?%211&@y5'R9yR0%211%5241'5y8%611%311p061':&MrH(R7+2(8%33@21%6251&R8&Q7rD+T0%3221%52E1%>3E71rI+8%>3K1<%A231%;2K9%D3K21rJ+;%D3Q11B%G231&Q1rA&Q4+4&Q5&1rK%22Q=1%411%7261%:291%L2Q<1%Q53Q<=1+=%Q43QA1Q2%Q7291rB%Q22QB1%Q;3QB31rL+>%Q;3QH1Q9%Q>231rM%C2QN1%E11%Q;2QK1%QD3QK51+C%QC3R01QA%QF271&Q6+QM%22QF1%QC2R31%QL3R351rN+D%QL3R91QJ%QO231%R13R81Q>&G%11G'9'<u1rQ1%Q:2RE1%4231u8%6231%8231&Q2+Vb\P0%QF21R4%321Q0&Q3+Q?%K2R?1%32G1%QJ2R:QF%QM2Q61%RG3S4J1%QM2R=Q8%RI3S6L1zrO%?221+1%A21Q1+O%C2Q31%M231rQ2%R:21RHrQ3%RL21RJ%I231+TP0%K21=rQ0+R0%RB221rQ5%S421S2%Q1231%Q22E6%RG2Q96rQ7%S921S7%Q6231&CrQ=%RH2T31%RJ11%RM2RL1%54E?G1rQ4rQ8%842B1SA+RQP0%:4BD1S>%QB2Q55%R82SLF%Q@271%QN231&E&Q0rQ?rQA%S92TD1%S;11%S>2S=1%7465I1rQ@rQ<%:4921T2'3&=r1rQD%SD2TO1%4231&>r2rQE%34U421QM%R;2QN1%S12TEQJ%R9231%RG231&DrQCrQ:%T21:%T52T41%T8231u4%75O621<%S0291p0B1pSDH1rQBrQ>+R8%TA221%?5Q741S1Q@+QL%SE2U91%B5Q:AQ9S41+ZooooPPPPoooO%D5Q<OQCS61&HrQ9rQ6%3?N=GF2QIR31R8QJR@RBS=R;RI';'F&NvQ<rQI+Zkn@%UH3V31UF/01V3rQHrQG%8576321rQF%:59Q<1QA3%<3QN31+:%V13V>1UO%V42Q@1%UN2V>S9%V73V>21%V72QCV2%V12VAQC%V:3VA21%V83VES>V6%V;2QG1%V=3VD1=%V=2QIUM%V?3VF1RJ+9%V>3VK1V<%VA2QM1%VC3VJ1R7+B%VB3VO1V@%VE2R11rQ;%VH3VO21%VH2R4U3%VJ3W11QL%VJ2R6TL%VL3W31Q:+E%VK3W81VI%VN2R:1%W03W71S5+F%VO3W<1VM%W22R>1%W43W;1SC+G%W33W@1W1%W62RB1%W83W?1QE+H%W73WD1W5%W:2RF1%W<3WC1T0+I%W;3WH1W9%W>2RJ1%W@3WG1SF+J%W?3WL1W=%WB2RN1%WD3WK1T@+K%WC3X01WA%WF2S21%WH3WO1TF+3%WG3X41WE%WJ2S61%WK2R32%WM3X421%WK3X8W2WI%WN2S:1%WO2R72%X13X821&O%12R6SC&I(0'7%12XDXD(6rQJ%W<2XG1%W>11%WA2W@1%54XJXJT21%WE2SMS5%74XLXL1WO%84XMXMSOX0(4%11;%>3<31%?3=51%@3>81%B31RIT6rQK%WJ2Y51%T:2T91r3%X22SDSKrQL%T94Y:T81V3%T25TJ43SL1p061pSDTB1%X82SIF%T65TNTBDVH1%T75TOTCTBVIV9%W0221%W1251%W22@1%W32Q41%W42Q71%W52Q<1%W62QB1%W72QG1%W82QL1%W92R11%W:2R61%W;2R;1%W<2R@1%W=2RE1%W>2RH1%W?2RK1%W@2S11%WA2S61%WB2S91%WC2S=1%WD2SA1%WE2SG1qQ6YK1%T62YL1qT2Z21%T82Z31p0T:1p0T?1p0TB1p0TF1p0TL1p0UF1p0UJ1p0V31p0V81p0V;1p0V?1p0VF1p0VK1p0VM1p0W41p0W71p0W=1p0WC1p0WG1p0WJ1p0WN1p0X31p0X81p0XB1p0XE1p0XK1p0Y41p0Y>1p0YE1p0Z71p0Z>1pS>[41pS<[51pS:[61pS8[71pS6[81pS4[91pS2[:1pS0[;1pRN[<1pRL[=1pSB[>1pS@[?1pSH[F1pT<[G1pRF[H1pRD[I1pSJ[J1pT4[K1pSL[L1pT8[M1pSN[H1pT6[C1pQ4[D1pT0[J1pTF\11").
Proof.
intros ws regs M rom raw sp r ris qris c chp src na g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27
H2 H8 H11 H13 H14 H19 H20 Hret Hlen IMG Hsp' Er Eris Hris Hc Hr' Hchp Hchp' Hsrc Hsrc' Acs Acr Acd Hna Wch Wr Cws Cna Cmx Crd F.
set (n := Z.of_nat (length ws)) in *. assert (Hn : 1 <= n <= 8) by (unfold n; lia).
destruct (art_gfa_copy ws regs M rom chp src (chp + 4 * n) H13 H20 H11 ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Hsrc ltac:(lia) Hchp
ltac:(unfold apart in Acs |- *; lia) Wch Cws) as (r1 & RUN1 & P13 & P20 & K1).
set (M1 := art_w4s M chp ws) in *.
assert (A1 : art_agree [(chp, 4 * n)] M M1) by (apply art_agree_w4s; lia).
assert (G1 : mem_grows M M1) by apply art_w4s_grows.
assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
pose proof (art_gfa_fcells_tr _ M M1 sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 A1 ltac:(zgap) ltac:(lia) ltac:(lia) F) as F1.
destruct F1 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
unfold apart in Acr, Acd.
pose proof (art_gfa_tail_fn r1 M1 rom raw sp r n na ris qris c (U g8) (U g9) (U g18) (U g19) (U g20) (U g21) (U g22) (U g23) (U g24) (U g25) (U g26) (U g27)
ltac:(rewrite K1 by (intros E; discriminate E); exact H2) ltac:(rewrite K1 by (intros E; discriminate E); exact H8)
ltac:(rewrite K1 by (intros E; discriminate E); exact H14) ltac:(rewrite K1 by (intros E; discriminate E); exact H19)
ltac:(lia) ltac:(lia) IMG Er Eris Hris Hc ltac:(lia) ltac:(unfold apart; lia) ltac:(lia) Hna Hret
(UB g8) (UB g9) (UB g18) (UB g19) (UB g20) (UB g21) (UB g22) (UB g23) (UB g24) (UB g25) (UB g26) (UB g27)
ltac:(eapply wr_grows; [exact G1|exact Wr]) ltac:(ztr) ltac:(ztr) ltac:(ztr)
F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13) as RUN2.
match type of RUN2 with msteps _ _ (mkst ?R _ ?MM _) => set (r2 := R) in RUN2; set (M2 := MM) in RUN2 end.
assert (A2 : art_agree [(r + 72, 8); (r, 8)] M1 M2). { unfold M2. eapply art_agree_sub; [zagree|]. zsub. }
assert (G2 : mem_grows M1 M2) by (unfold M2; zgrows).
exists r2, M2. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|].
do 12 (split; [unfold r2; gres; apply Z_to_bv_bv_unsigned|]).
split; [unfold r2; gres; apply K1; intros E; discriminate E|]. split; [unfold r2; gres; apply K1; intros E; discriminate E|].
split; [eapply mem_grows_trans; [exact G1|exact G2]|].
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A2]|]. zsub. }
split. { intros j Hj. assert (C1 : cellA M1 (chp + 4 * Z.of_nat j) 4 (nth j ws 0)).
{ unfold M1. apply cell_w4s_nth; [lia|lia|exact Hj|]. intros jj Hjj. destruct (Cws jj Hjj) as [R _]. lia. }
pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. ztr. }
unfold M2. split; zcell.
Qed.
#[using="Type"] Lemma art_clsgfa_lock : ltac2:(TCodec.tc2 tcn__JbtClsGfa1 "YI&@y5'R9yR0%211%5241'5y8%611%311p061'?':&Mr<(R7+1(8%33A21%6251r9%93A21r=+2%93G17%<231&R8%12H7%@3H31r>+:%@3N1>%C231+QWTnH%82O1%G3O31r?+;%G3Q51E%J231r:%?2Q61%N3Q631r@+<%N3Q<1L%Q1231%Q33Q;16rA+=%Q33QA1Q1%Q6231%Q83Q@1;rB+>%Q83QF1Q6%Q;231%Q=3QE1@&Q2&Q1+Vb\P0+T0%3221%521K&Q3&Q6+Q?%22Q<1%42I1'9%<2QFQ2+O%>2Q41%4231z%A21QE+Q5%<2QF1%C2QA1%?21<%F26QC&Q4+R0%22F1%I2Q@1%E21B%52IQB%R;3R<Q<1rE%82L1%O2Q:1%Q021N&Q7rG%221Q1%Q5241%Q62F3%Q02R:?%Q2251%N231rF%Q;2K1%Q6225%Q2221&E&Q0rNrK%@21Q?%54431Q@rOrJ%O2QC1%QF2=1%:4941QE&DrQ0+Q0%QK2RE1u8rH%65@5321rQ1+Q@%R12RK1%:5D3165rQ2rIrM%Q@2R41%R7231%@5J51<QI';'F&NvQ<rQ6+ZkbL%SK3T71SI/01T7rQ5rQ4%8576321r2+Zkm<%T23T>1T0/01T>r1%>5=5217%@3Q<71%T927SN%QK2IRJ%SN2TE1%T=3TE31+8%T<3TJ1T:%T?2=1rL%R=2S1Q:%S4221%T62TM1%TE3TM51+9%TD3U21TB%TG2E1%TI3U11T3%TI2GT7%S<28=%T>2U51%TM3U531%TM2KT4%TA2U8QA%U03U821%U02NT0%TD2U;QJ%U33U;21%U32Q1SN%TG2U>R3%U63U>21%U62Q4SL%TJ2UAR:%U93UA21+C%U83UF1U6%U;2Q91+QM%SI2U31%U12UH1%U@3UH41+D%U?3UM1U=%UB2Q@1%SO2U9R;%S@2R=1%T72R21+S`PPPP0%T9221%U;2V21%UJ3V271+3%UI3V71UG%UL2QJ1%UM2R22%UO3V721+4%UN3V<1UL%V12QO1%V22R72%V43V<21&O%12R6QO&I(0'7%12V;V;(6%14V=V=R1TK%24V>V>QJQO(4%115%83631%93751%;31RBR;&HrQ3%VD2RIR6%VE2RJQO+B%VE3W31VC%VH2RM1%VI2RNQ?%VJ2ROQ9+E%VJ3W81VH%VM2S21+F%VM3W;1VK%W02S51+G%W03W>1VN%W32S81+H%W33WA1W1%W62S;1+I%W63WD1W4%W92S>1+J%W93WG1W7%W<2SA1+K%W<3WJ1W:%W?2SD1%N?S:SOMLKHGFC@=:741+QL%UN2W81%T=5TGS=S1T91%UL241%UM2Q41%UN2QA1%UO2QD1%V02QJ1%V12R01%V22R;1%V32RC1%V42RG1%V52RK1%V62RO1%V72S31%V82S81%V92S=1%V:2SF1%V;2SK1qQ6X71%T>2X81qT2X>1%T@2X?1p0TB1p0TI1p0TN1p0U61p0U<1p0UC1p0UD1p0UI1p0UN1p0V71p0V:1p0V@1p0VB1p0VG1p0VJ1p0W01p0W61p0W=1p0WC1p0WI1p0WO1p0X71p0X?1p0XG1pSJY21pT4Y31pT:Y41pSFY51pRFY61pRDY71pT>Y81pT8Y91pSNYA1pT6Y<1pQ4Y=1pT0YC1").
Proof.
intros regs M rom raw sp st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 IMG Hsp' Hc Hspb Hspb' Hris Hris' Eris Hr' Hst Hchp Hn W Wr Cspb Cris Cmx.
pose proof (art_gfa_lock_fn regs M rom raw sp 1283032 st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 ltac:(lia) ltac:(lia) IMG ltac:(lia) ltac:(lia) Hc Hspb Hspb' Hris Hris' Eris
ltac:(unfold apart; lia) Hst Hchp Hn W Wr Cspb Cris Cmx) as RUN.
match type of RUN with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN; set (M1 := MM) in RUN end.
exists r1, M1. split; [exact RUN|].
split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|].
split; [unfold r1; gres; exact H11|]. split; [unfold r1; gres; exact H12|]. split; [unfold r1; gres; exact H13|]. split; [unfold r1; gres; exact H14|].
split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|].
split; [unfold M1, art_gfa_frame; zgrows|].
split. { unfold M1, art_gfa_frame. eapply art_agree_sub; [zagree|]. zsub. }
split. { pose proof (art_gfa_fcells_frame M sp raw regs ltac:(lia) ltac:(lia)) as F.
assert (AW : art_agree [(ris + 128 * c, 8)] (art_gfa_frame M sp raw regs) M1). { unfold M1. eapply art_agree_sub; [zagree|]. zsub. }
eapply (art_gfa_fcells_tr [(ris + 128 * c, 8)]); [exact AW|zgap|lia|lia|exact F]. }
unfold M1. apply cell_Wn_hit; [lia|cbn; lia].
Qed.
End FPX.
