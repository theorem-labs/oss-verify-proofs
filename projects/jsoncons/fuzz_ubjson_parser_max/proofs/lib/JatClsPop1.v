(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatAllocG JatPoison JatPoisonRun ArtRuns ArtRunsMem JatMmapFixed JatPopulate1 JatPopulate2 JatPopulate3 JatFp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatClsPop1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "0M'"; "5apart"; "5cell"; "5wr"]; ["6art_mmap_args"; "7class_size"; "8msteps"; "9art_agree"; ":art_tsd"; ";art_layout"; ";kHighMemBeg"; "<getr"; "<mkst"; "=mem_grows"; ">loaded_segments"; "?In"; "@add"; "@div"; "@le"; "@lt"]; ["@modulo"; "@mul"; "@pow"; "@sub"; "0a"; "0addr"; "0au"; "0b"; "0c"; "0ctx"; "0fx"; "0j"; "0key"; "0km"; "0m1"; "0m2"]; ["0mu"; "0need"; "0new"; "0nf"; "0qs"; "0r"; "0raw"; "0regs"; "0regs'"; "0rem"; "0req"; "0rom"; "0shb"; "0sp"; "0spb"; "0st"]; ["ABV"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0sv"; "0sz"; "0t"; "0tp"; "0tsd"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_mod4096_lin : ltac2:(TCodec.tc2 tcn__JatClsPop1 "H'9'7&Q0&L&Q1+TP0r3%3221r2&Q2+2+Q0%3221%9251%;271r1%<2;1%>231%@21=z%C3D21pRBE1pR@F1pR:G1").
Proof. intros a b c. replace (4096 * a + b * 2 ^ 32 + 4096 * c) with ((a + b * 2 ^ 20 + c) * 4096) by lia. apply Z_mod_mult. Qed.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_clspop_A := (ltac2:(TCodec.tc2 tcn__JatClsPop1 "]1&:y5'R2yR0%211%5241'2y8%611%311p061'9'7&Gr?(R0+1(5%33A21%6251r<%93A21r@+2%93G17%<231&R1%12H7%@3H31rA+:%@3N1>%C231+QVmdH%82O1%G3O31rB+;%G3Q51E%J231r=%?2Q61%N3Q631rC+<%N3Q<1L%Q1231%Q33Q;16rD+=%Q33QA1Q1%Q6231%Q83Q@1;rE+>%Q83QF1Q6%Q;231%Q=3QE1@&N&L+VbTP0+^@%3221%521K&O&Q2+Q?%22Q<1%42I1'6z%=21L+R0%82QB1%:2O1%6241%B2QLQ1+N%D2Q31%:231%F2DQ5+T0%G2Q21%C21@%J2R4Q4+8%L2Q61%B231&Q1&ArG%211%421Q7%RA3RBR?1%Q42HQ9rF+Q5%Q02R:1%Q7231%Q321Q0+RPP0%=216%RJ3RK<1+XPP0%@21QH%RM3RNQD1%Q@2Q4@rH%QB21BrI%QC21?%Q?241+B%Q@2RJ1%QH2H1rJ%QI213+S`PPPP0%QL221&=&Q3rQ3%221QMrQ0%542QO1Q;&?&JrQ7rQ4%921R4%54431R5&>rQ8+Q0%R;2S51u8%55:421=rQ9%R?2A5rO%95>3251rQ:+Q@%RD2?1%=5B3195rQ;rQ5+QH%RI221%B5G41>R?rQ<%RL2SF4u1%F5K321RCrQ=+Q8%S12SK1u4+SoooooO%L5Q15321rQ>+QVY`H+QiYm0%Q05Q532L1rQ?+TP0%Q35Q824O1rQ@+QVYa8+QibQ8%Q75Q<32Q31rQA+X4%SB241%Q;5Q@31FS8'8'B&HvQ:rQE+ZkdD%U63UB1U4/01UBrQDrQC%8576321r2+a\i8%U=3UI1U;/01UIr1%>5=5217%@3R271&@%T12U;QM%S;2O1%T92Q>1%T:21QL+QB%64=2S01%UK2>UF+adW8%U@2V71%UO3V731%UO2BUD%RE2Q2T5%RF21SM%UE2V<1%V43V<41%V23V@SLV0%V52H1%UI2V@S<%V83V@21+E%V73VE1V5%V:2M1%SO1QD%UO2VF1%V>3VF31+F%V=3VK1V;%V@2Q31%VB3VJ1UL%VM1VN&K(0+3%VD3W21VB+4%VF3W41VD+G%VH3W61VF+H%VJ3W81VH+I%VL3W:1VJ+J%VN3W<1VL+K%W03W>1VN(1%11B%A3C31%B3D61%C3E91%D3F<1%E3G?1%F3HB1%G3IE1%I3JQK1r4%W>21R1rQG%W@21R3%WB3WJ31p061pTDQ11&I%12R;R4&C'4%12WJWJ(3%T?2RLV:%24WMWM1V;%I14%Q93521%831RDR=%TD2S1UG&R3rQB%22X<1%T=5TBRB4T91+@%TJ2S71%X62S0R2%72XA1%TB5TGRG3T>1%TN2S;Q>+9%X93XG1X7%X<2S61%=2XG1%TH5TMRM5TD1%U42SATG%X>3XLU=X<%XA2S;1%B2XL1%TM5U2S24TI1%U92SFT6+C%XD3Y21XB%XG2SA1%H2Y21%U35U8S85TO1%U?2SLTI+D%XJ3Y81XH%XM2SG1%N2Y81%U95U>S>5U51%UE2T2TJ%Y12SKRH%Q22Y<1%U=5UBSB3U91%Y42SNRE%Q52Y?1%U@5UESES6U<1%UL2S7VO+ZkmD%UC5UHSH2U?1%UO2S:Q6%UE5UJSJ1UATH%V12S<RA%UG5ULSL1UCTC%V32S>UF%UI5UNSN1UESH%V52S@U2+bde0%Y@3YL1Y>/01YL%QD2YN1%UO5V4T45UK1%V;2SFUE%V15V6T61UMVM%V=2SHUB%V35V8T81UOT1%V?2SJWO%V55V:T:1V1T4+R8%VB2SM1%V85V=T=1V4W4+R@%VE2T01%V;5V@T@1V7T9%X:241%X;281%X<2;1%X=2>1%X>2A1%X?2H1%X@2K1%XA2N1%XB2Q11%XC2Q51%XD2Q91%XE2Q>1%XF2QE1%XG2QL1%XH2R21%XI2R91%XJ2R?1%XK2RE1%XL2RO1%XM2S21%XN2T51%XO2T:1%Y02TA1%Y12TF1%Y22TL1%Y32U11%Y42U91qJ[01%UL2[11qSB[71%UN2[81p0V01p0V51p0V:1p0V>1p0VC1p0VJ1p0VO1p0W51p0W:1p0W?1p0WF1p0WM1p0X41p0X91p0X=1p0XA1p0XD1p0XF1p0XJ1p0XN1p0Y41p0Y61p0Y=1p0YB1p0YF1p0YH1p0YM1p0Z51p0Z;1p0ZB1p0ZH1p0ZN1p0[41p0[<1p0[D1p0[L1pS4\71pRL\81pS2\91pR>\:1pS:\;1pSN\<1pSF\=1pS<\>1pRB\?1pT0\@1pSL\A1pS>\I1pSH\D1pH\E1pS@\K1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 4%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 6%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 7%nat 0%nat).
Variable req : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 8%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 9%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 10%nat 0%nat).
Variable au : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 11%nat 0%nat).
Variable mu : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 12%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 13%nat 0%nat).
Variable need : ltac:(sec_ty2 constr:(SEC_T_art_clspop_A) 14%nat 0%nat).
Lemma art_clspop_A : ltac:(sec_stmt2 constr:(SEC_T_art_clspop_A) 15%nat 0%nat).
Proof using Type regs M rom raw sp st c r req spb qs au mu km need.
intros H1 H2 H10 H11 H12 H13 H14 IMG Hsp' Hst Hc Hr Hr' Hreq Eneed Hspb Hspb' Espb Emu Hau Haumu Hneed Hneed' Hex A W
Cspb Cau Cmu Cmm Cpm Crel Cpg1 Cpg2 Ccf Cdec.
destruct (art_pop_a_run regs M rom raw sp 1275544 st c r req spb au mu need 0 H1 H2 H10 H11 H12 H13 H14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst Hc Hr Hr'
Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' ltac:(lia) ltac:(lia) ltac:(unfold apart in A |- *; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Cspb Cau Cmu Cmm Cpm Crel)
as (rA & RUNA & A1 & A2 & A8 & A9 & A11 & A12 & A13 & A18 & A19 & A20 & A21 & A22 & KA).
set (MF := art_pop_frame M sp raw regs) in *.
assert (AF : art_agree [(sp - 464, 464)] M MF).
{ eapply art_agree_sub; [unfold MF, art_pop_frame; zagree|]. zsub. }
assert (GF : mem_grows M MF) by (unfold MF, art_pop_frame; zgrows).
assert (Haddr : (spb + c * 2 ^ 32 + mu) mod 4096 = 0).
{ rewrite Espb, Emu. replace (65536 * qs + c * 2 ^ 32 + 262144 * km) with (4096 * (16 * qs) + c * 2 ^ 32 + 4096 * (64 * km)) by lia. apply art_mod4096_lin. }
pose proof (art_rar_map_pre_fn rA MF rom (0x56fb4 : bv 64)%bv (sp - 64) (spb + c * 2 ^ 32 + mu) 262144 97176 0x1cc828 0 A1 A2 A11 A12 A13
ltac:(lia) ltac:(lia) ltac:(lia) Haddr ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
ltac:(eapply wr_grows; [exact GF|]; eapply wr_sub; [exact W|lia|lia])
ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUNB.
set (MB := art_rar_map_mem MF (sp - 64) (0x56fb4 : bv 64)%bv rA (spb + c * 2 ^ 32 + mu) 262144 97176) in *.
assert (AB : art_agree [(sp - 464, 464)] MF MB).
{ intros x Hx. cbn in Hx. destruct Hx as [Hx _]. unfold MB. apply art_rar_map_mem_agree; [lia|lia|lia]. }
assert (GB : mem_grows MF MB) by (apply art_rar_map_mem_grows).
destruct (art_rar_map_mem_cells MF (sp - 64) (0x56fb4 : bv 64)%bv rA (spb + c * 2 ^ 32 + mu) 262144 97176 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (F1 & G8 & G9 & G18 & F0 & F8 & F9 & F18 & F19 & F20).
fold MB in F1, G8, G9, G18, F0, F8, F9, F18, F19, F20.
eexists. exists MB. split; [eapply msteps_trans; [exact RUNA | exact RUNB]|].
split. { unfold art_mmap_args. repeat split; gres; reflexivity. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split; [gres; exact A21|]. split; [gres; exact A22|].
split. { intros x Hx. rewrite <- (KA x Hx). cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; gres; reflexivity. }
split; [eapply mem_grows_trans; [exact GF | exact GB]|].
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AF | exact AB]|]. zsub. }
assert (TB : forall a (k : nat) v, sp - 64 <= a -> a + Z.of_nat k <= sp -> cellA MF a k v -> cellA MB a k v).
{ intros a k v Ha Hk C. apply (art_cell_agree _ MF MB); [|lia|lia|exact C]. intros x Hx. unfold MB. apply art_rar_map_mem_agree; [lia|lia|lia]. }
split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|]. split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|].
split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|]. split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|].
split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|]. split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|].
split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|]. split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|].
rewrite A8 in G8. rewrite A9 in G9. rewrite A18 in G18, F18. rewrite A19 in F19. rewrite A20 in F20.
rewrite art_u_lit in G8, G9, G18, F18, F19, F20 by lia.
split; [exact F1|]. split; [exact G8|]. split; [exact G9|]. split; [exact G18|].
split; [exact F0|]. split; [exact F8|]. split; [exact F9|]. split; [exact F18|]. split; [exact F19|]. exact F20.
Qed.
End SE.
#[using="Type"] Lemma art_div8_lin : ltac2:(TCodec.tc2 tcn__JatClsPop1 "Q2'9'7&M&L&Q1+RPP0r3%3221r2&Q2+2+Q0%3221%9251%;271+XPP0r1%=221%?241+8%B221+XP0%B21@+M%?2>1%E2A1%G241+QPP0%H21<%J231%M3N:1pRLO1pRBQ01pS:Q11").
Proof. intros. replace (65536 * qs + c * 2 ^ 32 + 262144 * km) with ((8192 * qs + c * 2 ^ 29 + 32768 * km) * 8) by lia. apply Z_div_mult. lia. Qed.
#[using="Type"] Lemma art_mod8_lin : ltac2:(TCodec.tc2 tcn__JatClsPop1 "J'9'7&Q0&L&Q1+RPP0r3%3221r2&Q2+2+Q0%3221%9251%;271+XPP0r1%=221%?241+8%B221z%E3F21pRLG1pRBH1pS:I1").
Proof. intros. replace (65536 * qs + c * 2 ^ 32 + 262144 * km) with ((8192 * qs + c * 2 ^ 29 + 32768 * km) * 8) by lia. apply Z_mod_mult. Qed.
Section SE.
Local Abbreviation SEC_T_art_clspop_B := (ltac2:(TCodec.tc2 tcn__JatClsPop1 "b9&:y5'R2yR0%211%5241'2y8%611%311p061'9'7r2&Lr>&Q1r?&Q2+2+Q0%3221%6251%9281r;%;221%>3?=1+QoooPP0+XP0%=21>%@231r@+M%?2>1%B231%E251+QPP0%E21=%H231%K3LJ1&GrK(R0+1(5%33Q<21%6251&R1+adW8%22Q>1%Q63Q>41rL%:3QCQ18%=221&Q3rI+R0%3221+T0%5221%=2QI1%QA3QI81rM+4%F3QO1D%I231%C2QO;%QG3QO21rN+8%L3R51J%O231+XPP0%J2R61%QN3R631rO+:%Q33R<1Q1%Q6231r8%Q12R=1%R53R=31rQ0+E%Q:3RC1Q8%Q=231%Q72RCR5%R;3RC21rQ1+F%Q@3RI1Q>%QC231+QVmdH%Q>2RJ1%RB3RJ31&N+VbTP0+^@%RD221%421H&O+Q?%RD2RC1%32E1'6rJ%;2QO1+N%=231%5231+RPP0%RO21QH%S43S571rHrG%S32Q;1%S83S931z%G215&F%I21QJ+Q5%S82S71%S=2QG1%H21F+B%S<2S;1%SA2R<1+S`PPPP0%Q2221%Q32S>I%Q42JE%L221%Q62@QJ%Q72QDQK%SI2QEQO%RB21Q@%SI2RFR;%SL21S1%SO3T031%Q=2GRI%Q92RJR9%Q6221%Q@2JR;%QA2KQH%Q=2QISL%Q:221%T12T0RK%Q@2R@1%Q=261+TP0rQ=%QI221rQ>%T<214rQC%S621QK%QN231&Q0rQ?+Rg8%TC221%421RM%TG3TH1Q>%R52R45rQ@%TH21S<rQF%SB21R7%R:231&=rQBrQA%342G1SC+RPX0rQG%RA221rQH%U421S=%RD21RC%RE2R65+QP0%U8251%RH21RG%RI2Q27rQI%U<21Q4rQM%T621RK%RN231rQ9%E41TK6Q9rQ:%G41TM8T7rQ;rQL%J42U01Q>rQ<%UH21U2rR1%TB21S7%S:231&?&JrR4rR2%TH21S=+\@%645421rR5%8471QIU>rR6rQO+RiH%V8221+@%>4=521rR7rR0%V=21QK%B4A31TGrR8%D4C14U4&ErR9%211&DrR:rR3%362<BDI1&>rR;%UB28U@%UC21U4u8+ZkmD%65Q15321rR<%UH2;UF%UI21H%:5Q5316Q4rR=%UL2;UJ+H%UN221+Rf@%W82Q31%A5Q<63=1rR>%V32<V1%V421W6%W;2Q:W6%W>2Q@1%G5QB53C1rR?%V92>V7+Q8%V;221&R3+bde0%VJ3X11VH/01X1%42X31%Q15QL96M1rR@%VC2AVA+Q@%VE221%Q65R141Q2V4rRA%VH2@VF+QH%VJ221rQK%Q<5R752Q81rRB%VN2<VL%VO21VM%X62QFX1%X92QJ1%QB5R=53Q>1rRC%W42=W2+R8%W6221%QG5RB41QCVErRD%W92<W7+R@%W;221rQN%QM5RH52QI1rRE+QVYa8+QibQ8%R15RL32QM1rRF+T@%XL241%R55S031R1UFrRG%XO2Q5RH%R85S321R4S2rRH+Rj0%Y32Q41%R<5S731R8S6rRI%Y62Q1TD%R?5S:21R;S9rRJ%Y92Q4Q=%RB5S=21R>R7rRK%Y<2Q1Y6%RE5S@21RAQMrRL%Y?2OS6%RH5SC21RDR='8'B&HvQ:rS0+a\i<%XK3Z21XI/01Z2rROrRN%8576321+ZbjH%Y13Z81XO/01Z8r1%=5<Z1216%?3T461%Y82Z3Y3+ZlQ8%Y83Z?1Y6/01Z?%Z83Z@41%Y=2Z8Y1rRM%Y121XO%Y92ZE1%Z=3ZE41%YB2Z=XJ%Y<2ZHO%Z@3ZH21%YE2Z@XG%Y?2ZKQB%ZC3ZK21+9%YG3[01YE%YJ2ZE1%ZE2RKS;%YE2[11%ZI3[131%YN2ZIXI%ZK3[31X:+;%YO3[81YM%Z22ZM1%ZO3[71=+<%Z33[<1Z1%Z62[11%ZO2R7ZJ%[22R<1%Z22[>1%[63[>41+=%Z:3[C1Z8%Z=2[81%[:3[B1B%Z=3[FWJZ;%Z@2[;1%[=3[E18+C%ZA3[J1Z?%ZD2[?1%Z>2[JT5%[B3[J21+D%ZF3[O1ZD%ZI2[D1%[D2S?YJ%Z=21S:%ZE2\11%[I3\141%ZN2[IYB%ZH2\4T9%[L3\421%[12[LY?%[N3\61Y=%\91\:&K(0+3%[53\>1[3+G%[73\@1[5%[83\ATO[6+I%[:3\C1[8+J%[<3\E1[:+K%[>3\G1[<(1%11?%>3@31%?3A61%@3B91%A3C<1%B3D>1%C3EA1%E3FRD1r4%[K21\FrS2%[M21\H%\J3]231p061pTDM1&I%12S3RM&C'4%12]2]2(3%[I2RIZ>%24]5]51W1%34]6]6VD\=%]42T3VM%54]8]81VL%]62T5XD%74]:]:1[@%]82T:U<%94]<]<1[B%O1;%Q<3<21%Q=3=51%Q>3>81%Q?3?;1%Q@3@=1%C31SGSA%[02Z:SB%ZL2SC\L%ZI221r3%]E2W0]Fu1+WJ%W05WK4321p061pRH]M1%]K2VL\N%W45WOSMHW01%]M2TLTK%]N2W5\4%W75X2T02W31%^02W;\6%W95X4T2KW51%W:5X5T3JW6R>%[9221%[:251%[;291%[<2<1%[=2G1%[>2Q<1%[?2Q?1%[@2R>1%[A2RA1%[B2RE1%[C2RM1%[D2S31%[E2S71%[F2S<1%[G2SD1%[H2SI1%[I2SL1%[J2T31%[K2T71%[L2T;1%[M2TA1%[N2TG1qJ^M1%U92^N1qSB_41%U;2_51p0U=1p0UA1p0UE1p0UI1p0UM1p0V21p0V61p0V;1p0V@1p0VG1p0VM1p0W41p0W;1p0WA1p0WL1p0X31p0X;1p0X@1p0XH1p0XM1p0Y11p0Y41p0Y91p0Y@1p0YC1p0YK1p0Z11p0Z51p0Z81p0Z;1p0ZA1p0ZC1p0ZG1p0ZI1p0ZM1p0[11p0[61p0[<1p0[>1p0[E1p0[K1p0[O1p0\01p0\11p0\51p0\91p0\;1p0\?1p0\E1p0\G1p0\I1p0\M1p0]31p0]81p0];1p0]>1p0]C1p0]G1p0]N1p0^31p0^91p0^A1p0^H1p0_01p0_81p0_?1p0_K1p0`71p0`E1pSJa51pR<a61pT:a71pS0a81pRNa91pSDa:1pS6a;1pT<a<1pS8a=1pRLa>1pS2a?1pR>a@1pS:aA1pSNaB1pRBaC1pS<aD1pT>aE1pRDaF1pTBaG1pRJaH1pT@aI1pSLaJ1pSHaL1pHaM1pS@b31")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 3%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 4%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 5%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 6%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 7%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 8%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 9%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 10%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 11%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 12%nat 0%nat).
Variable au : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 13%nat 0%nat).
Variable mu : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 14%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 15%nat 0%nat).
Variable nf : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 16%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 17%nat 0%nat).
Variable new : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 18%nat 0%nat).
Variable rem : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 19%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 20%nat 0%nat).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 21%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 22%nat 0%nat).
Variable addr : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 23%nat 0%nat).
Variable shb : ltac:(sec_ty2 constr:(SEC_T_art_clspop_B) 24%nat 0%nat).
Lemma art_clspop_B : ltac:(sec_stmt2 constr:(SEC_T_art_clspop_B) 25%nat 0%nat).
Proof using Type regs M rom sp tp key tsd ctx t r c spb qs au mu km nf sz new rem m1 m2 sv addr shb.
intros Haddr Hshb H1 H2 H4 H8 H10 H21 H22 IMG Hsp' Hc Espb Emu Hkm Hspb Hspb' Hex Hsz Hau Haumu Enew Hrem Hnew Hnf
Hm1 Hm2 Hsv Ht Ht' Hst8 Hr Hr' Atr Htp Htp' Htsd Htsd' Hctx Hctx' Ast Asr Asc Hshsp W Wsh Wts Wsv Wr L T F1 F8 F9 F18 F0 K8 K9 K18 F19 F20 Ccf Clim Cm1 Cm2 Csv Cmu Cau Cnf.
unfold kHighMemBeg in Hspb.
assert (Eshb : SB + addr / 8 = shb). { rewrite Haddr, Hshb. unfold SB. rewrite Espb, Emu, art_div8_lin. lia. }
pose proof (art_rar_map_post_fn regs M rom (0x56fb4 : bv 64)%bv (Z_to_bv 64 r) (Z_to_bv 64 (t + 2768)) (Z_to_bv 64 (spb + c * 2 ^ 32)) (Z_to_bv 64 262144) (Z_to_bv 64 addr)
(sp - 64) 262144 addr addr 0x1cc828 H1 H2 H8 H10 ltac:(unfold ret_ok; bveq) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(eapply wr_sub; [exact W|lia|lia])
ltac:(exact F1) ltac:(rewrite art_u_lit by lia; exact F8) ltac:(rewrite art_u_lit by lia; exact F9) ltac:(rewrite art_u_lit by lia; exact F18)
F0 K8 K9 ltac:(rewrite art_u_lit by lia; exact K18) ltac:(rewrite art_u_lit by lia; exact F19) ltac:(rewrite art_u_lit by lia; exact F20)
Ccf Clim) as RUN1.
match type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN1; set (M1 := MM) in RUN1 end.
assert (A1 : art_agree [(sp - 464, 400)] M M1). { eapply art_agree_sub; [unfold M1; zagree|]. zsub. }
assert (G1 : mem_grows M M1) by (unfold M1; zgrows).
pose proof (art_pop_b_fn r1 M1 rom addr ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(lia)) as RUN2.
match type of RUN2 with msteps _ _ (mkst ?R _ _ _) => set (r2 := R) in RUN2 end.
assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact L]. intros z Hz. cbn. repeat split; lia. }
destruct (art_poison_hi_run r2 M1 rom (0x56fd0 : bv 64)%bv (sp - 64) addr 262144 250
ltac:(unfold r2; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r2, r1; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
ltac:(unfold r2; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia]) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
L1 ltac:(unfold kHighMemBeg; lia) ltac:(unfold kHighMemEnd; lia)
ltac:(rewrite Haddr, Espb, Emu; apply art_mod8_lin) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(intros E; discriminate E)
ltac:(rewrite Eshb; change (262144 / 8) with 32768; eapply wr_grows; [exact G1|exact Wsh]))
as (r3 & RUN3 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
match type of RUN3 with msteps _ _ (mkst _ _ ?MM _) => set (M3 := MM) in RUN3 end.
assert (A3 : art_agree [(sp - 464, 400); (shb, 32768)] M1 M3).
{ unfold M3, art_poison_frame. rewrite Eshb. change (262144 / 8) with 32768. eapply art_agree_sub; [zagree|]. rewrite Z2Nat.id by lia. zsub. }
assert (G3 : mem_grows M1 M3) by (unfold M3, art_poison_frame; zgrows).
assert (A13 : art_agree [(sp - 464, 400); (shb, 32768)] M M3). { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A3]|]. zsub. }
assert (G13 : mem_grows M M3) by (eapply mem_grows_trans; eassumption).
assert (Hqs : 0 <= qs) by lia.
assert (T3 : art_tsd M3 tp key tsd ctx t).
{ eapply art_tsd_fp; [exact A13| | |exact Htp|exact Htp'|exact Htsd|exact Htsd'|exact T].
- intros z Hz. cbn. repeat split; lia.
- intros z Hz. cbn. unfold apart in Asc. repeat split; lia. }
assert (R3_4 : getr r3 4 = Z_to_bv 64 tp). { rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E). unfold r2, r1; gres. exact H4. }
assert (R3_22 : getr r3 22 = Z_to_bv 64 1275544). { rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E). unfold r2, r1; gres. exact H22. }
assert (R3_8 : getr r3 8 = Z_to_bv 64 r). { rewrite P8. unfold r2, r1; gres. reflexivity. }
assert (R3_9 : getr r3 9 = Z_to_bv 64 (t + 2768)). { rewrite P9. unfold r2, r1; gres. reflexivity. }
assert (R3_18 : getr r3 18 = Z_to_bv 64 (spb + c * 2 ^ 32)). { rewrite P18. unfold r2, r1; gres. reflexivity. }
assert (R3_19 : getr r3 19 = Z_to_bv 64 262144). { rewrite P19. unfold r2, r1; gres. reflexivity. }
assert (R3_21 : getr r3 21 = Z_to_bv 64 sz). { rewrite P21. unfold r2, r1; gres. exact H21. }
pose proof (art_pop_c_fn r3 M3 rom (sp - 64) tp key tsd ctx t 1275544 (t + 2768) r (spb + c * 2 ^ 32) sz au mu nf new rem m1 m2 sv
P2 R3_4 R3_8 R3_9 R3_18 R3_19 R3_21 R3_22
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (t + 2768 + 24) with (t + 2792) by lia; exact Hst8) ltac:(lia) ltac:(lia) ltac:(lia)
Hsz Hau Haumu ltac:(lia) Enew Hrem Hnew Hnf Hm1 Hm2 Hsv ltac:(lia) ltac:(lia)
ltac:(eapply wr_grows; [exact G13|]; eapply wr_sub; [exact W|lia|lia]) T3
ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; destruct T as (_ & _ & _ & _ & _ & _ & _ & Hk & _); lia) ltac:(unfold apart; lia)
ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart in Atr |- *; lia) ltac:(unfold apart in Atr |- *; lia)
ltac:(eapply wr_grows; [exact G13|exact Wts]) ltac:(eapply wr_grows; [exact G13|]; replace (t + 2768 + 24) with (t + 2792) by lia; exact Wsv) ltac:(eapply wr_grows; [exact G13|exact Wr])
ltac:(unfold apart in Ast; ztr) ltac:(unfold apart in Ast; ztr) ltac:(replace (t + 2768 + 24) with (t + 2792) by lia; unfold apart in Ast; ztr)
ltac:(unfold apart in Asr; ztr) ltac:(unfold apart in Asr; ztr) ltac:(unfold apart in Asr; ztr)) as RUN4.
match type of RUN4 with msteps _ _ (mkst ?R _ ?MM _) => set (r4 := R) in RUN4; set (M4 := MM) in RUN4 end.
assert (A4 : art_agree [(sp - 464, 400); (t + 2872, 16); (t + 2792, 8); (r + 48, 8)] M3 M4).
{ unfold M4, art_pop_c_mem. eapply art_agree_sub; [zagree|]. zsub. }
assert (G4 : mem_grows M3 M4) by (unfold M4, art_pop_c_mem; zgrows).
exists r4, M4. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|exact RUN4]|].
split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; exact R3_4|]. split; [unfold r4; gres; exact R3_8|].
split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|].
split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; exact R3_18|]. split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|].
split; [unfold r4; gres; exact R3_21|]. split; [unfold r4; gres; exact R3_22|].
split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end;
(unfold r4; gres; rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E); unfold r2, r1; gres; reflexivity). }
split; [eapply mem_grows_trans; [exact G13|exact G4]|].
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A13|exact A4]|]. zsub. }
split. { intros j Hj. assert (C3 : cellA M3 (shb + j) 1 250).
{ unfold M3. rewrite Eshb. apply cell_Wf_in; [lia|change (262144 / 8) with 32768; rewrite Z2Nat.id by lia; lia|change (262144 / 8) with 32768; rewrite Z2Nat.id by lia; lia|lia]. }
unfold apart in Ast, Asr. ztr. }
unfold M4, art_pop_c_mem. unfold apart in Atr.
split; [zcell|]. split; [zcell|]. split; [replace (t + 2792) with (t + 2768 + 24) by lia; zcell|]. zcell.
Qed.
End SE.
End FPX.
