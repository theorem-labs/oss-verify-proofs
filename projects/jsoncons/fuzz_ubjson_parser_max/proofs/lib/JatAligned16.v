(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatPoison JatAllocG JatUnwind JatDepotA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAligned16 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "0M1"; "5Wn"; "5apart"; "5cell"]; ["5wr"; "6msteps"; "7ret_ok"; "8hid"; "9art_tsd"; ":getr"; ":mkst"; ":regupd"; ";mem_grows"; "<loaded_segments"; "0S"; "=In"; ">add"; ">land"; ">le"; ">lt"]; [">modulo"; ">pow"; ">sub"; "0bot"; "0ctx"; "0f23"; "0f24"; "0fx"; "0g16"; "0g24"; "0g32"; "0g40"; "0g48"; "0g56"; "0g64"; "0key"]; ["0n"; "0r"; "0raw0"; "0regs"; "0regs1"; "0rom"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_unsigned"; "0t"; "0top"; "0tp"; "0tsd"; "0ub"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_land15_mod16 : ltac2:(TCodec.tc2 tcn__JatAligned16 "C'9&Nzr1%3221'5&Q0r2+@%3221%53:18&Mr3+?%3221%:3?1=p061p0=1pS2B1").
Proof. intros n Hn H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact H. Qed.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_icu1_16 := (ltac2:(TCodec.tc2 tcn__JatAligned16 "^>&:y5'QHyR0%211%5241'2y8%611%311p061'9'5&Er=(QF+1(3%33A21%6251r:%93A21r>+2%93G17%<231&QG%12H7%@3H31r?+4%@3N1>%C231r9%82O1%G3O31r@+:%G3Q51E%J231+@%?2Q61%N3Q631rA+;%N3Q<1L%Q1231r<%F2Q=1%Q53Q=31&N&L+`PQoooPP0+XP0%3221%521Q1&Q1+Q?%22Q31%92N1'4z%<21Q1&O+R0%92Q:1%32Q51%7251+TP0r;%D221%D2H3%921>&C'8%H2QM7+RPP0%K221+VbTP0%M21R1%6231%811&>&Q2rD%221A%44R0B1Q1rE%521D%74QEE1Q4%Q72Q?F%Q921?%Q:2>QA%C221%E11rB%>4QEL1L+RPX0rF%QA221rG+8%QC221%QE21I%QF2L6+QP0%QG261%QI21M%QJ2Q?H%Q>2IF%QB221+QO%QH2RI1%QB2?1&@&IrQ1rN%Q321QB%54431QCrQ2rI%84721QF&DrQ3rMrLrKrJ%665<4321&?rQ4+QW^^Hu1%45C321SFrQ5+QW^_Lu4+N%95H4321rQ6+QVYa8u8+QibQ8%>5M4321rQ7+Q2%S0241%B5Q131?T4rQ8rO+SS0%S5221%G5Q641DRLrQ9rQ0+Q8%S:221%L5Q;41IS1rQ:%S=2Q<QK%O5Q>21C6rQ;%S@2Q;SK%Q25QA21F9'6'A&FvQ7rQ?+_U`8%TL3U81TJ/01U8rQ>rQ=%8576321r2+cWoH%U33U?1U1/01U?r1%>5=5217%@3R371%U:27U5+`Ub0%U:3UF1U8/01UF%U?3UG41%U?2<U4+RU@%S;2L1%U52UL1%UD3UL41%UD2ATK+RRH%S@2Q11%U:2V11%UI3V141%UI2FTI+_Ue0%U>2V51%UM3V531+<%UL3V:1UJ%UO2L1%UC2V:Q;%V23V:21+=%V13V?1UO%V42Q11%UH2V?R?%V73V?21+>%V63VD1V4%V92Q61%UM2VDRK%V<3VD21+?%V;3VI1V9%V>2Q;1%V22VIRB%VA3VI21+H%V@3VN1V>%VC2Q@1+QoO%U?2RK1%V92W01%VH3W041%VH2QEV6%V<2W3R<%VK3W321%W61W7&K(0+3%VM3W;1VK+I%VO3W=1VM+J%W13W?1VO+K%W33WA1W1(1%11<%;3=31%<3>61%=3?91%>3@<1%@3AR51r4%W>21R;rQA%W@21R=%WB3WJ31p061pS4H1&H%12RER>&7rQ<+RW@%UC221&QI%12X5RD%VG231%V;226%V?221%911%62X:RM%VK2SMSG%X33X421%=11r3%H11%G12%X83X;21p051p0:1pT0XC1%V52SFUC%B2XFE%TH5U7S62T<1%V82SIWC%X=3XKUGX;%X@2SD1%G2XK1%TM5U<S;4TA1%V=2SNR2+9%XC3Y11XA%XF2SJ1%M2Y11%U35UBSA5TG1+Q0%VD2T51+B%XJ3Y81XH%XM2T11%Q42Y81%U:5UISH5TN1%VJ2T;TA+C%Y03Y>1XN%Y32T71%Q:2Y>1%U@5UOSN5U41+Q@%W12TB1+D%Y73YE1Y5%Y:2T>1%QA2YE1%UG5V6T55U;1+QH%W82TI1+E%Y>3YL1Y<%YA2TE1%QH2YL1%UN5V=T<5UB1%W>2TOX1+F%YD3Z21YB%YG2TK1%QN2Z21%V45VCTB5UH1+RS8%WE2U61+_UgL%V85VGTF2UL1+RS@%WI2U:1%V;5VJTI1UOU;+RSH%WL2U=1%V>5VMTL1V2UA+RT0%WO2U@1%VA5W0TO1V5Y;+RT8%X22UC1%Z73ZCT?Z5/01ZC%RA2ZE1%VG5W6U54V;1+RT@%X82UI1%VJ5W9U81V>Z<+RTH%X;2UL1%VM5W<U;1VATL+RU0%X>2UO1+RI%X@2V11%W25WAU@3VF1+RU8%XC2V41+G%ZI3[71ZG%ZL2V01%S32[71%W95WHUG5VM1%ZO2V3T=%S62[:1%W<5WKUJU@W01+RR8%XM2V>1%W?5WNUMU>W31+RR@%Y02VA1%WB5X1V01W;YG+RR<%Y32VD1%WE5X4V31W>YJ%Y52VFYD%X74X6V51YE%YN231%YO271%Z02;1%Z12?1%Z22C1%Z32K1%Z42Q11%Z52Q51%Z62Q91%Z72Q@1%Z82QD1%Z92QH1%Z:2QL1%Z;2R11%Z<2R81%Z=2R@1%Z>2RH1%Z?2RO1%Z@2S71%ZA2S>1%ZB2SD1%ZC2SH1%ZD2T>1%ZE2TA1%ZF2U;1%ZG2U?1%ZH2UG1%ZI2UM1%ZJ2V31%ZK2V91%ZL2V?1%ZM2VD1%ZN2VJ1%ZO2W01%[02W61qJ\C1%WI2\D1qS:\J1%WK2\K1p0WM1p0X11p0X51p0X;1p0XA1p0XF1p0XL1p0Y21p0Y81p0Y@1p0YD1p0YK1p0YO1p0Z31p0Z71p0Z91p0Z>1p0ZB1p0ZE1p0ZK1p0ZO1p0[51p0[?1p0[B1p0[F1p0[O1p0\41p0\;1p0\C1p0\K1p0]31p0];1pR8]F1pSH]G1pSF]H1pR:]I1pSL]J1pS0]K1pSJ]L1pS2]M1pQF]N1pS6^61pS<^11pH^21pS8^81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 3%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 5%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 6%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 7%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 8%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 9%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 10%nat 0%nat).
Variable top : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 11%nat 0%nat).
Variable bot : ltac:(sec_ty2 constr:(SEC_T_art_icu1_16) 12%nat 0%nat).
Lemma art_icu1_16 : ltac:(sec_stmt2 constr:(SEC_T_art_icu1_16) 13%nat 0%nat).
Proof using Type regs M rom raw0 S n tp key tsd ctx t top bot.
intros H1 H2 H4 H10 H11 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
eexists _, _. split.
- zstep (ltac:(oF' 0x79608%Z)) (ltac:(oD' 0x79608%Z)).
zsd (ltac:(oF' 0x7960c%Z)) (ltac:(oD' 0x7960c%Z)) (S - 8) (U raw0) ltac:(rewok W). zsd (ltac:(oF' 0x79610%Z)) (ltac:(oD' 0x79610%Z)) (S - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x79614%Z)) (ltac:(oD' 0x79614%Z)) (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x79618%Z)) (ltac:(oD' 0x79618%Z)) (S - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x7961c%Z)) (ltac:(oD' 0x7961c%Z)) (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x79620%Z)) (ltac:(oD' 0x79620%Z)) (S - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x79624%Z)) (ltac:(oD' 0x79624%Z)) (S - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x79628%Z)) (ltac:(oD' 0x79628%Z)) (S - 64) (U (getr regs 22)) ltac:(rewok W).
zstep (ltac:(oF' 0x7962c%Z)) (ltac:(oD' 0x7962c%Z)). zstep (ltac:(oF' 0x79630%Z)) (ltac:(oD' 0x79630%Z)). zstep (ltac:(oF' 0x79634%Z)) (ltac:(oD' 0x79634%Z)). zstep (ltac:(oF' 0x79638%Z)) (ltac:(oD' 0x79638%Z)). zstep (ltac:(oF' 0x7963c%Z)) (ltac:(oD' 0x7963c%Z)).
zstep (ltac:(oF' 0x79640%Z)) (ltac:(oD' 0x79640%Z)). zstep (ltac:(oF' 0x79644%Z)) (ltac:(oD' 0x79644%Z)). zstep (ltac:(oF' 0x79648%Z)) (ltac:(oD' 0x79648%Z)). zstep (ltac:(oF' 0x7964c%Z)) (ltac:(oD' 0x7964c%Z)). zstep (ltac:(oF' 0x79650%Z)) (ltac:(oD' 0x79650%Z)).
zsd (ltac:(oF' 0x79654%Z)) (ltac:(oD' 0x79654%Z)) (S - 80) 0 ltac:(rewok W).
zsd (ltac:(oF' 0x79658%Z)) (ltac:(oD' 0x79658%Z)) (S - 2136) (S - 2120) ltac:(rewok W).
zsd (ltac:(oF' 0x7965c%Z)) (ltac:(oD' 0x7965c%Z)) (S - 2128) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2128)) by lia. replace (S - 2128 + 4) with (S - 2124) by lia.
stepn (ltac:(oF' 0x79660%Z)) (ltac:(oD' 0x79660%Z)).
zcall (art_malloc_ctx_fn _ _ _ _).
zstep (ltac:(oF' 0x79664%Z)) (ltac:(oD' 0x79664%Z)).
zbtk (ltac:(oF' 0x79668%Z)) (ltac:(oD' 0x79668%Z)).
stepn (ltac:(oF' 0x7969c%Z)) (ltac:(oD' 0x7969c%Z)).
zcall (art_get_pc_fn _ _ _ _).
zstep (ltac:(oF' 0x796a0%Z)) (ltac:(oD' 0x796a0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x132628 8 0x1cc828) by zcell; assert (Cfast' : cellA X (0x1cc828 + 34) 1 1) by zcell end.
zld (ltac:(oF' 0x796a4%Z)) (ltac:(oD' 0x796a4%Z)) 0x132628 Cg38'. zlbu (ltac:(oF' 0x796a8%Z)) (ltac:(oD' 0x796a8%Z)) (0x1cc828 + 34) Cfast'.
zstep (ltac:(oF' 0x796ac%Z)) (ltac:(oD' 0x796ac%Z)).
stepn (ltac:(oF' 0x796b0%Z)) (ltac:(oD' 0x796b0%Z)).
zcall (art_malloc_ctx_fn _ _ _ _).
zstep (ltac:(oF' 0x796b4%Z)) (ltac:(oD' 0x796b4%Z)). zstep (ltac:(oF' 0x796b8%Z)) (ltac:(oD' 0x796b8%Z)). zstep (ltac:(oF' 0x796bc%Z)) (ltac:(oD' 0x796bc%Z)).
stepn (ltac:(oF' 0x796c0%Z)) (ltac:(oD' 0x796c0%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
zstep (ltac:(oF' 0x796c4%Z)) (ltac:(oD' 0x796c4%Z)).
zsd (ltac:(oF' 0x796c8%Z)) (ltac:(oD' 0x796c8%Z)) (S - 80) S ltac:(rewok W).
zbtk (ltac:(oF' 0x796cc%Z)) (ltac:(oD' 0x796cc%Z)).
zstep (ltac:(oF' 0x796e0%Z)) (ltac:(oD' 0x796e0%Z)). zstep (ltac:(oF' 0x796e4%Z)) (ltac:(oD' 0x796e4%Z)). zstep (ltac:(oF' 0x796e8%Z)) (ltac:(oD' 0x796e8%Z)). zstep (ltac:(oF' 0x796ec%Z)) (ltac:(oD' 0x796ec%Z)). zstep (ltac:(oF' 0x796f0%Z)) (ltac:(oD' 0x796f0%Z)). zstep (ltac:(oF' 0x796f4%Z)) (ltac:(oD' 0x796f4%Z)).
stepn (ltac:(oF' 0x796f8%Z)) (ltac:(oD' 0x796f8%Z)).
zstep (ltac:(oF' 0x81524%Z)) (ltac:(oD' 0x81524%Z)).
zsd (ltac:(oF' 0x81528%Z)) (ltac:(oD' 0x81528%Z)) (S - 2152) 0x796fc ltac:(rewok W). zsd (ltac:(oF' 0x8152c%Z)) (ltac:(oD' 0x8152c%Z)) (S - 2160) S ltac:(rewok W). zsd (ltac:(oF' 0x81530%Z)) (ltac:(oD' 0x81530%Z)) (S - 2168) n ltac:(rewok W).
zsd (ltac:(oF' 0x81534%Z)) (ltac:(oD' 0x81534%Z)) (S - 2176) 16 ltac:(rewok W). zsd (ltac:(oF' 0x81538%Z)) (ltac:(oD' 0x81538%Z)) (S - 2184) (U (0x796a0 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x8153c%Z)) (ltac:(oD' 0x8153c%Z)) (S - 2192) 1 ltac:(rewok W).
zsd (ltac:(oF' 0x81540%Z)) (ltac:(oD' 0x81540%Z)) (S - 2200) (S - 2136) ltac:(rewok W). zsd (ltac:(oF' 0x81544%Z)) (ltac:(oD' 0x81544%Z)) (S - 2208) (S - 89) ltac:(rewok W).
zsd (ltac:(oF' 0x81548%Z)) (ltac:(oD' 0x81548%Z)) (S - 2216) (U (getr regs 23)) ltac:(rewok W). zsd (ltac:(oF' 0x8154c%Z)) (ltac:(oD' 0x8154c%Z)) (S - 2224) (U (getr regs 24)) ltac:(rewok W).
zstep (ltac:(oF' 0x81550%Z)) (ltac:(oD' 0x81550%Z)). zstep (ltac:(oF' 0x81554%Z)) (ltac:(oD' 0x81554%Z)). zstep (ltac:(oF' 0x81558%Z)) (ltac:(oD' 0x81558%Z)). zstep (ltac:(oF' 0x8155c%Z)) (ltac:(oD' 0x8155c%Z)). zstep (ltac:(oF' 0x81560%Z)) (ltac:(oD' 0x81560%Z)). zstep (ltac:(oF' 0x81564%Z)) (ltac:(oD' 0x81564%Z)).
zsw (ltac:(oF' 0x81568%Z)) (ltac:(oD' 0x81568%Z)) (S - 2128) 0 ltac:(rewok W).
stepn (ltac:(oF' 0x8156c%Z)) (ltac:(oD' 0x8156c%Z)).
zcall (art_asan_inited_fn _ _ _ _).
zbft (ltac:(oF' 0x81570%Z)) (ltac:(oD' 0x81570%Z)).
stepn (ltac:(oF' 0x81574%Z)) (ltac:(oD' 0x81574%Z)).
zcall (art_cur_thread_fn _ _ _ _ (S - 2224) tp key tsd ctx t).
{ unfold art_tsd. repeat split; try lia; zcell. }
zbft (ltac:(oF' 0x81578%Z)) (ltac:(oD' 0x81578%Z)).
zstep (ltac:(oF' 0x8157c%Z)) (ltac:(oD' 0x8157c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cunw' : cellA X (t + 2047 + 1121) 1 0) by (replace (t + 2047 + 1121) with (t + 3168) by lia; zcell) end.
zlbu (ltac:(oF' 0x81580%Z)) (ltac:(oD' 0x81580%Z)) (t + 2047 + 1121) Cunw'.
zstep (ltac:(oF' 0x81584%Z)) (ltac:(oD' 0x81584%Z)).
zsb (ltac:(oF' 0x81588%Z)) (ltac:(oD' 0x81588%Z)) (t + 2047 + 1121) 1 ltac:(rewok Wt).
zbft (ltac:(oF' 0x8158c%Z)) (ltac:(oD' 0x8158c%Z)).
zstep (ltac:(oF' 0x81590%Z)) (ltac:(oD' 0x81590%Z)).
stepn (ltac:(oF' 0x81594%Z)) (ltac:(oD' 0x81594%Z)).
zcall (art_stack_top_fn _ _ _ _ t top bot).
zstep (ltac:(oF' 0x81598%Z)) (ltac:(oD' 0x81598%Z)). zstep (ltac:(oF' 0x8159c%Z)) (ltac:(oD' 0x8159c%Z)).
stepn (ltac:(oF' 0x815a0%Z)) (ltac:(oD' 0x815a0%Z)).
zcall (art_stack_bottom_fn _ _ _ _ t top bot).
zstep (ltac:(oF' 0x815a4%Z)) (ltac:(oD' 0x815a4%Z)).
zbft (ltac:(oF' 0x815a8%Z)) (ltac:(oD' 0x815a8%Z)).
zstep (ltac:(oF' 0x815ac%Z)) (ltac:(oD' 0x815ac%Z)). zstep (ltac:(oF' 0x815b0%Z)) (ltac:(oD' 0x815b0%Z)). zstep (ltac:(oF' 0x815b4%Z)) (ltac:(oD' 0x815b4%Z)). zstep (ltac:(oF' 0x815b8%Z)) (ltac:(oD' 0x815b8%Z)). zstep (ltac:(oF' 0x815bc%Z)) (ltac:(oD' 0x815bc%Z)). zstep (ltac:(oF' 0x815c0%Z)) (ltac:(oD' 0x815c0%Z)). zstep (ltac:(oF' 0x815c4%Z)) (ltac:(oD' 0x815c4%Z)).
stepn (ltac:(oF' 0x815c8%Z)) (ltac:(oD' 0x815c8%Z)).
stepn (ltac:(oF' 0x8163c%Z)) (ltac:(oD' 0x8163c%Z)).
zcall (art_unwind_fn _ _ _ _ (S - 2224) (S - 2136) 0x796a0 S top bot).
apply mst_refl.
- zsplit.
all: lazymatch goal with
| |- getr _ _ = _ => gres; rwH; first [reflexivity | f_equal; lia | bveq]
| |- forall r : reg, In r _ -> _ => intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; gres; reflexivity
| |- mem_grows _ _ => repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl
| |- forall x : word, _ => intros x N1 N2; zagree
| |- wr _ _ _ _ => zwr
| |- cell _ _ _ _ _ => zcell
end.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_icu2_16_fn := (ltac2:(TCodec.tc2 tcn__JatAligned16 "X0&:y5'QHyR0%211%5241'2y8%611%311p061'9'5&Er8(QF+2(3%33A21%6251&QG&Q2r5+RU@%3221%52F1%>3F71r9+H%>3L1<%A231&Lr4+QoO%3221%?2Q01%H3Q061&N+XP0r7%3221&Q1+Q?%22K1%72N1'4z%:21Q1&O+R0%92Q21%32Q51%7251&Q0+@%22L1%Q<3Q=1:+TP0%E21Or:%M213%=21;&>r;r=%Q<218%44391L%N2E4%D25B%H221&@&IrBr@%QE21A%54431BrCr?%84721E&?rD+RS8%QM2:1u8+_UgL%65>5321rE+RS@%R32<1%:5B316=rF+RSH%R72<1%>5F31:ArG+RT0%R;2:1%B5J31>Q;rH+RT8%R?2:1&QI+_Ue0%RH3S41RF/01S4%42S61%K5Q386G1rI+RT@%RH2?1+1%Q05Q842L1rJ+RTH%RM2@1+RRH%RO2B1%Q65Q>53Q21rK+RU0%S32=1+RI%S52?1%Q<5QD53Q81rL+RU8%S92>1%Q@5QH31Q<Q1rM%S<2;S:%QC5QK21Q?Q4'A&FvQ7rO+`Ub0%SI3T51SG/01T5rN%756521;&G%SN3T<OSL+ZYn4%T03T<1SN/01T<%53;41%SM2FQC%SO2T@1%833T21+8%T73TE1T5%T22KQ4%T42TE1%=3531+9%T<3TJ1T:%T82TIS6%A3421+:%T@3TN1T>+QVmdH%T=2TN1%F3531+;%TE3U31TC%TA2U2Q?%J3421+<%TI3U71TG%M331=+=%TL3U:1TJ%Q0331D+>%TO3U=1TM%TK2U<R1%Q43421+?%U33UA1U1%Q73314+B%U63UD1U4%Q:331J+C%U93UG1U7%U52UFR@%Q>3421+D%U=3UK1U;%QA331>+E%U@3UN1U>%QD331Q8+F%UC3V11UA%U>2R7R:%U@2V11%QI3531+G%UH3V61UF%UD2V5RM%QM3421%UF2V7S8%QO32U>1+ZVo4%UN3V:1UL/01V:&=u1+SS0%UC2S21%443R91U5%UO2RHT3+_Uh@%V73VC1V5/01VC%SC2VE1%:4T6651%V52RNT3%<4T821RO%V72S0T1%>4T:21S7%?4T;1R<U8%RK5RJDA1RO%RM3TIRE1p0RO1p0S31p0S81p0S?1p0SF1p0SL1p0T61p0T;1p0T@1p0TE1p0TM1p0U11p0U81p0U91p0U=1p0UC1p0UG1p0UJ1p0UO1p0V81p0V=1p0VB1p0VM1pR>W=1pR<W>1pSFW?1pS2W@1pQFWA1pS<WC1pHWD1pS8WJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_icu2_16_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_icu2_16_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_icu2_16_fn) 2%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_icu2_16_fn) 3%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_icu2_16_fn) 4%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_icu2_16_fn) 5%nat 0%nat).
Variable f23 : ltac:(sec_ty2 constr:(SEC_T_art_icu2_16_fn) 6%nat 0%nat).
Variable f24 : ltac:(sec_ty2 constr:(SEC_T_art_icu2_16_fn) 7%nat 0%nat).
Lemma art_icu2_16_fn : ltac:(sec_stmt2 constr:(SEC_T_art_icu2_16_fn) 8%nat 0%nat).
Proof using Type regs M rom S n t f23 f24.
intros H2 H24 HS HS' Hn Hn16 Ht Ht' Atsp Hf23 Hf24 W Wt C52 C60 C68 C76 C84 C92 C00 C08 C16 C24.
zsb (ltac:(oF' 0x81640%Z)) (ltac:(oD' 0x81640%Z)) (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (D52 : cellA X (S - 2152) 8 0x796fc) by zcell; assert (D60 : cellA X (S - 2160) 8 S) by zcell; assert (D68 : cellA X (S - 2168) 8 n) by zcell;
assert (D76 : cellA X (S - 2176) 8 16) by zcell; assert (D84 : cellA X (S - 2184) 8 (U (0x796a0 : bv 64)%bv)) by zcell;
assert (D92 : cellA X (S - 2192) 8 1) by zcell; assert (D00 : cellA X (S - 2200) 8 (S - 2136)) by zcell;
assert (D08 : cellA X (S - 2208) 8 (S - 89)) by zcell; assert (D16 : cellA X (S - 2216) 8 f23) by zcell; assert (D24 : cellA X (S - 2224) 8 f24) by zcell end.
zld (ltac:(oF' 0x81644%Z)) (ltac:(oD' 0x81644%Z)) (S - 2152) D52. zld (ltac:(oF' 0x81648%Z)) (ltac:(oD' 0x81648%Z)) (S - 2160) D60. zld (ltac:(oF' 0x8164c%Z)) (ltac:(oD' 0x8164c%Z)) (S - 2168) D68. zld (ltac:(oF' 0x81650%Z)) (ltac:(oD' 0x81650%Z)) (S - 2176) D76.
zld (ltac:(oF' 0x81654%Z)) (ltac:(oD' 0x81654%Z)) (S - 2184) D84. zld (ltac:(oF' 0x81658%Z)) (ltac:(oD' 0x81658%Z)) (S - 2192) D92. zld (ltac:(oF' 0x8165c%Z)) (ltac:(oD' 0x8165c%Z)) (S - 2200) D00. zld (ltac:(oF' 0x81660%Z)) (ltac:(oD' 0x81660%Z)) (S - 2208) D08.
zld (ltac:(oF' 0x81664%Z)) (ltac:(oD' 0x81664%Z)) (S - 2216) D16. zld (ltac:(oF' 0x81668%Z)) (ltac:(oD' 0x81668%Z)) (S - 2224) D24.
zstep (ltac:(oF' 0x8166c%Z)) (ltac:(oD' 0x8166c%Z)).
stepjr (ltac:(oF' 0x81670%Z)) (ltac:(oD' 0x81670%Z)) (0x796fc : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x796fc%Z)) (ltac:(oD' 0x796fc%Z)). zstep (ltac:(oF' 0x79700%Z)) (ltac:(oD' 0x79700%Z)). zstep (ltac:(oF' 0x79704%Z)) (ltac:(oD' 0x79704%Z)). zstep (ltac:(oF' 0x79708%Z)) (ltac:(oD' 0x79708%Z)).
stepn (ltac:(oF' 0x7970c%Z)) (ltac:(oD' 0x7970c%Z)).
zstep (ltac:(oF' 0x52778%Z)) (ltac:(oD' 0x52778%Z)).
zsd (ltac:(oF' 0x5277c%Z)) (ltac:(oD' 0x5277c%Z)) (S - 2152) (U (0x79710 : bv 64)%bv) ltac:(rewok W).
zsd (ltac:(oF' 0x52780%Z)) (ltac:(oD' 0x52780%Z)) (S - 2160) S ltac:(rewok W).
zsd (ltac:(oF' 0x52784%Z)) (ltac:(oD' 0x52784%Z)) (S - 2168) n ltac:(rewok W).
zsd (ltac:(oF' 0x52788%Z)) (ltac:(oD' 0x52788%Z)) (S - 2176) 16 ltac:(rewok W).
zstep (ltac:(oF' 0x5278c%Z)) (ltac:(oD' 0x5278c%Z)). zstep (ltac:(oF' 0x52790%Z)) (ltac:(oD' 0x52790%Z)). zstep (ltac:(oF' 0x52794%Z)) (ltac:(oD' 0x52794%Z)).
zstep (ltac:(oF' 0x52798%Z)) (ltac:(oD' 0x52798%Z)).
zbft (ltac:(oF' 0x5279c%Z)) (ltac:(oD' 0x5279c%Z)).
stepn (ltac:(oF' 0x527a0%Z)) (ltac:(oD' 0x527a0%Z)). rwH. rewrite art_zb_and by lia. rewrite (art_land15_mod16 n) by lia.
zbft (ltac:(oF' 0x527a4%Z)) (ltac:(oD' 0x527a4%Z)).
zstep (ltac:(oF' 0x527a8%Z)) (ltac:(oD' 0x527a8%Z)). zstep (ltac:(oF' 0x527ac%Z)) (ltac:(oD' 0x527ac%Z)). zstep (ltac:(oF' 0x527b0%Z)) (ltac:(oD' 0x527b0%Z)). zstep (ltac:(oF' 0x527b4%Z)) (ltac:(oD' 0x527b4%Z)). zstep (ltac:(oF' 0x527b8%Z)) (ltac:(oD' 0x527b8%Z)). zstep (ltac:(oF' 0x527bc%Z)) (ltac:(oD' 0x527bc%Z)).
stepn (ltac:(oF' 0x527c0%Z)) (ltac:(oD' 0x527c0%Z)).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic3_16_fn := (ltac2:(TCodec.tc2 tcn__JatAligned16 "V9&:y5'QHyR0%211%5241'2y8%611%311p061'9'5&Er>(QF+2(3%33A21%6251&QG&Q2r:+RT0%3221%52F1%>3F71r?+:%>3L1<%A231r9%<2M1%E3M31'4&N+1%221?&O&Q1+R0%22I1%42D1%9261+XP0r=%;221+Q?%92Q01%>2Q31&Br@%211z%C21K%A2L>%F221%F24Q;%D2Q<A%I221&?&IrKrH+RS8%Q<221u8&QI+_Uh@%QF3R21QD/01R2%42R41%<5;:761rLrI+RS@%QG221%A5@41;3rMrJ+RSH%QL221%F5E41@8rN%QO2FQM+@%J5I32D1rO+8%R42@1%G2RG<%O5N42I1rQ0%R82?8%Q25Q121L?rQ1+H%R<2>1%Q65Q531Q0CrQ2+Q0%R@2>1%Q:5Q931Q4GrQ3+Q8%RD2=1%Q>5Q=31Q8KrQ4+Q@%RH2>1%QB5QA31Q<OrQ5+QH%RL2>1%QF5QE31Q@Q3rQ6%RO2=R<%QI5QH21QCQ6'A&FvQ7rQ8+ZYn4%S<3SH1S:/01SHrQ7%756521;&G%SA3SORLS?%2381B%S>2SOG%432SA1%SE3T3Q<SC%SA2T2Q6%73321+9%SI3T71SG%SE2T6Q=%;3421+B%SM3T;1SK%SI2T:QF%?3421+C%T13T?1SO%SM2T>QN%C3421+D%T53TC1T3%T12TBR7%G3421+E%T93TG1T7%T52TFR@%K3421+F%T=3TK1T;%T92TJRO%O3421%Q85Q71Q@Q2Q<%Q:3S3Q21p0Q<1p0Q@1p0QE1p0QJ1p0QO1p0R41p0R91p0R=1p0RC1p0RH1p0RN1p0S41p0SB1p0SC1p0SD1p0SE1p0SF1p0SG1p0SH1p0SL1p0T11p0T51p0T91p0T=1p0TH1p0U01pRNU@1pRLUA1pRJUB1pRHUC1pRFUD1pRDUE1pRBUF1pSNUG1pS2UH1pQFUI1pS6V11pS<UL1pHUM1pS8V31")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 3%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 5%nat 0%nat).
Variable ub : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 6%nat 0%nat).
Variable g16 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 7%nat 0%nat).
Variable g24 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 8%nat 0%nat).
Variable g32 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 9%nat 0%nat).
Variable g40 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 10%nat 0%nat).
Variable g48 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 11%nat 0%nat).
Variable g56 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 12%nat 0%nat).
Variable g64 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_16_fn) 13%nat 0%nat).
Lemma art_ic3_16_fn : ltac:(sec_stmt2 constr:(SEC_T_art_ic3_16_fn) 14%nat 0%nat).
Proof using Type regs M rom raw0 S n ub g16 g24 g32 g40 g48 g56 g64.
intros H2 H10 Hub HS HS' Hret Hn Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Hg64 C52 C60 C68 C76 C8 C16 C24 C32 C40 C48 C56 C64.
zbft (ltac:(oF' 0x527c4%Z)) (ltac:(oD' 0x527c4%Z)).
zld (ltac:(oF' 0x527c8%Z)) (ltac:(oD' 0x527c8%Z)) (S - 2152) C52. zld (ltac:(oF' 0x527cc%Z)) (ltac:(oD' 0x527cc%Z)) (S - 2160) C60. zld (ltac:(oF' 0x527d0%Z)) (ltac:(oD' 0x527d0%Z)) (S - 2168) C68. zld (ltac:(oF' 0x527d4%Z)) (ltac:(oD' 0x527d4%Z)) (S - 2176) C76.
zstep (ltac:(oF' 0x527d8%Z)) (ltac:(oD' 0x527d8%Z)).
stepjr (ltac:(oF' 0x527dc%Z)) (ltac:(oD' 0x527dc%Z)) (0x79710 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x79710%Z)) (ltac:(oD' 0x79710%Z)).
zld (ltac:(oF' 0x79714%Z)) (ltac:(oD' 0x79714%Z)) (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x79718%Z)) (ltac:(oD' 0x79718%Z)) (S - 16) C16. zld (ltac:(oF' 0x7971c%Z)) (ltac:(oD' 0x7971c%Z)) (S - 24) C24. zld (ltac:(oF' 0x79720%Z)) (ltac:(oD' 0x79720%Z)) (S - 32) C32.
zld (ltac:(oF' 0x79724%Z)) (ltac:(oD' 0x79724%Z)) (S - 40) C40. zld (ltac:(oF' 0x79728%Z)) (ltac:(oD' 0x79728%Z)) (S - 48) C48. zld (ltac:(oF' 0x7972c%Z)) (ltac:(oD' 0x7972c%Z)) (S - 56) C56. zld (ltac:(oF' 0x79730%Z)) (ltac:(oD' 0x79730%Z)) (S - 64) C64.
zstep (ltac:(oF' 0x79734%Z)) (ltac:(oD' 0x79734%Z)).
stepret (ltac:(oF' 0x79738%Z)) (ltac:(oD' 0x79738%Z)) raw0 ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
End FPX.
