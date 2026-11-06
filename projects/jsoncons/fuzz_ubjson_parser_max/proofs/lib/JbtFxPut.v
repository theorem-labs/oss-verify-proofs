(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac JbtLeaf JbtPoison JbtAllocG JbtUnwind JbtFree1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtFxPut () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxPut."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_fx_fq1_mem"; "9art_layout"; ":getr"; ":mkst"]; [":regupd"; ":v_or"; ";loaded_segments"; "0S"; "<add"; "<div"; "<le"; "<lor"; "<lt"; "<mul"; "<pow"; "<sub"; "0b1"; "0c"; "0ca"; "0cbc"]; ["0cbs"; "0csz"; "0f22"; "0fx"; "0g16"; "0g24"; "0g32"; "0g40"; "0g48"; "0g56"; "0id"; "0m"; "0n"; "0p"; "0q"; "0raw0"]; ["0regs"; "0rom"; "0st"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0t"; "0x"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac zlhu F D a HYP :=
chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].
Lemma art_fx_zb_or2 : ltac2:(TCodec.tc2 tcn__JbtFxPut "Q0'4'2&Fzr2%3221&H&J+2+R0%3221%5271%;271'3'QEyR0%211&A&QDr4%2251r3%4271%6231&G%1264%82;1%>3;41p0@1p0A1pSDN1pSBO1").
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.
Definition art_fx_fq1_mem (M : word -> option byte) (S p t id f22 : Z) : word -> option byte :=
(Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M p id) (S - 2136) 0x79344) (S - 2144) S) (S - 2152) p) (S - 2160) 0x792d4) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2208) (t + 208)) (S - 2200) (S - 2128)).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_fx_fq1_fn := (ltac2:(TCodec.tc2 tcn__JbtFxPut "Z0&5y5'QEyR0%211%5241'0y8%611%311p061'4'3&>r:(QC+2(1%33A21%6251&QD&Kr7+RT0%3221%52F1%>3F71r;+8%>3L1<%A231+@%;2:1%=2N1%F3N41r<+9%F3Q41D%I231r9+RR@%D221%F2Q71%O3Q751r=+:%O3Q=1M%Q2231r5%M2Q>1%Q63Q>31r>+B%Q63QD1Q4%Q9231+QWTnH%Q42QE1%Q=3QE31r?+C%Q=3QK1Q;%Q@231z%Q;2QL1%QD3QL31r@+D%QD3R21QB%QG231%QA2R2N%QJ3R221rA+E%QJ3R81QH%QM231+RA%QG2I1%QI2R:1%R23R:41rB+F%R23R@1R0%R5231%R73R?1>&F&D+`PQoooPP0+XP0%3221%521H&H&J+Q?%22R=1%42G1+Vb\P0%;21R1%=21J%=2CR6%9216'2%A2Q7F+X0%=2H1%4231+1%F21K+L%A2RL1%C2N1%:241%K2QAQ8+Q0%F2S11%H2Q;1%?241+TP0rC%Q2221rD%Q3214+R0%O2S:1%Q1231&7rH%S921RO+HrI%S<21=%64431Q;%Q?2R5<%Q:2=:%Q1221&9&BrMrK%SE21F%54431GrN%SH24S>%84721?&=rO%211&8rQ0+RRH%T0291u8&QF+_Tj4%T:3TF1T8/01TF%42TH1%:5E9761rQ1+RS0%T:2?1%>5I31:@rQ2+RS8%T>2@1%B5M31>DrQ3+RS@%TB2:1+_TfD%TJ3U61TH/01U6%D2U81%J5Q575F1rQ4+RSH%TJ2>1%N5Q931JR7rQ5%TM2=TK%TN2>T;%Q25Q=32N1rQ6%U12ATGu4+3&I%12RDI%S6231%Q:5QE7651rQ7+<%U:2B1%Q>5QI319OrQ8+QWUe@+R@%S?221%S:2UET3%QD5QO52Q@1rQ9%SC26R?%QG5R221QCRMrQ:+QWXaH+Q@%SH221%QL5R741GT@':&?vQ3rQ<+ZhZH%V53VA1V3/01VArQ;%756521=&@%V:3VHS@V8+ZiP4%V<3VH1V:/01VH%53;41+RU0%V:2H1%V<2VM1%934V?1%V>2VOQ0%;32V61%T?2QCQ1%VA2W21%>33V11%VC2W4Q6%@32UJ1+;%VK3W91VI&E+7%TH2QH1%321VB%QF21VC%VL2W=1%I3971%W33WAQDW1+WM%W02WA1%M3431+=%W83WF1W6%Q0331UI+>%W;3WI1W9%W62QJVL%W82WI1%Q53531+?%W@3WN1W>%W<2WMR;%Q93421%Q:31V=2%W>2QLVK%W@2X11%Q=33V91+V@%UB2RF1%WD2X51%QA34V61%QB31V1>%WG2X8R6%QD32UK1+_YU@%WO3X;1WM/01X;&<%16QKR:R@S0S4S<%R25R1631R8%R43T<QL1p0R61p0R<1p0R@1p0RG1p0RL1p0S51p0S:1p0S?1p0SH1p0SM1p0T21p0T>1p0TB1p0TF1p0TM1p0U11p0U91p0U?1p0UC1p0UI1p0V01p0V61p0V91p0V=1p0VC1p0VJ1p0W01p0W91p0W@1p0WH1p0X01p0X81p0XB1p0XK1pR6Y;1pRFY<1pS@Y=1pRJY>1pQJY?1pRLY@1pQ8YA1pS4YC1p>YD1pS2YJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 2%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 4%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 6%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 7%nat 0%nat).
Variable id : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 8%nat 0%nat).
Variable f22 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq1_fn) 9%nat 0%nat).
Lemma art_fx_fq1_fn : ltac:(sec_stmt2 constr:(SEC_T_art_fx_fq1_fn) 10%nat 0%nat).
Proof using Type regs M rom S p b1 n t id f22.
intros H2 H8 H9 H10 H18 H19 H20 H21 H22 HS HS' Hp Hp' Hb1 Hn Hid Ht Ht' Apsp Hf22 W Wp L C36 C44 C52 C60 C68 C76 Chw Cn Cqc Cqm Cff.
pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
stepn (ltac:(oF' 0x56158%Z)) (ltac:(oD' 0x56158%Z)). rwH. try rewrite art_zb_slli by lia.
stepn (ltac:(oF' 0x5615c%Z)) (ltac:(oD' 0x5615c%Z)). rwH. try rewrite art_zb_slli by lia.
stepn (ltac:(oF' 0x56160%Z)) (ltac:(oD' 0x56160%Z)). rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
stepn (ltac:(oF' 0x56164%Z)) (ltac:(oD' 0x56164%Z)). rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
zsd (ltac:(oF' 0x56168%Z)) (ltac:(oD' 0x56168%Z)) (p - 16 + 16) id ltac:(rewok Wp).
zstep (ltac:(oF' 0x5616c%Z)) (ltac:(oD' 0x5616c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia);
assert (Cn' : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
zlhu (ltac:(oF' 0x56170%Z)) (ltac:(oD' 0x56170%Z)) (p - 16 + 2) Chi.
zlwu (ltac:(oF' 0x56174%Z)) (ltac:(oD' 0x56174%Z)) (p - 16 + 4) Cn'.
zstep (ltac:(oF' 0x56178%Z)) (ltac:(oD' 0x56178%Z)). zstep (ltac:(oF' 0x5617c%Z)) (ltac:(oD' 0x5617c%Z)).
stepn (ltac:(oF' 0x56180%Z)) (ltac:(oD' 0x56180%Z)). rwH. try rewrite art_zb_slli by lia.
stepn (ltac:(oF' 0x56184%Z)) (ltac:(oD' 0x56184%Z)). rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
zstep (ltac:(oF' 0x56188%Z)) (ltac:(oD' 0x56188%Z)). zstep (ltac:(oF' 0x5618c%Z)) (ltac:(oD' 0x5618c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (E36 : cellA X (S - 2136) 8 (U (0x79344 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x792d4 : bv 64)%bv)) by zcell;
assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
zld (ltac:(oF' 0x56190%Z)) (ltac:(oD' 0x56190%Z)) (S - 2136) E36. zld (ltac:(oF' 0x56194%Z)) (ltac:(oD' 0x56194%Z)) (S - 2144) E44. zld (ltac:(oF' 0x56198%Z)) (ltac:(oD' 0x56198%Z)) (S - 2152) E52.
zld (ltac:(oF' 0x5619c%Z)) (ltac:(oD' 0x5619c%Z)) (S - 2160) E60. zld (ltac:(oF' 0x561a0%Z)) (ltac:(oD' 0x561a0%Z)) (S - 2168) E68. zld (ltac:(oF' 0x561a4%Z)) (ltac:(oD' 0x561a4%Z)) (S - 2176) E76.
zstep (ltac:(oF' 0x561a8%Z)) (ltac:(oD' 0x561a8%Z)).
stepn (ltac:(oF' 0x561ac%Z)) (ltac:(oD' 0x561ac%Z)).
zstep (ltac:(oF' 0x56278%Z)) (ltac:(oD' 0x56278%Z)).
zsd (ltac:(oF' 0x5627c%Z)) (ltac:(oD' 0x5627c%Z)) (S - 2136) (U (0x79344 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x56280%Z)) (ltac:(oD' 0x56280%Z)) (S - 2144) S ltac:(rewok W). zsd (ltac:(oF' 0x56284%Z)) (ltac:(oD' 0x56284%Z)) (S - 2152) p ltac:(rewok W).
zsd (ltac:(oF' 0x56288%Z)) (ltac:(oD' 0x56288%Z)) (S - 2160) (U (0x792d4 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x5628c%Z)) (ltac:(oD' 0x5628c%Z)) (S - 2168) 1 ltac:(rewok W). zsd (ltac:(oF' 0x56290%Z)) (ltac:(oD' 0x56290%Z)) (S - 2176) (S - 2128) ltac:(rewok W).
zsd (ltac:(oF' 0x56294%Z)) (ltac:(oD' 0x56294%Z)) (S - 2184) (S - 81) ltac:(rewok W). zsd (ltac:(oF' 0x56298%Z)) (ltac:(oD' 0x56298%Z)) (S - 2192) f22 ltac:(rewok W).
zstep (ltac:(oF' 0x5629c%Z)) (ltac:(oD' 0x5629c%Z)).
zsd (ltac:(oF' 0x562a0%Z)) (ltac:(oD' 0x562a0%Z)) (S - 2208) (t + 208) ltac:(rewok W). zsd (ltac:(oF' 0x562a4%Z)) (ltac:(oD' 0x562a4%Z)) (S - 2208 + 8) (S - 2128) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0x1396b0 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0x1396b0 + 64) 8 (2 ^ 28)) by zcell end.
zld (ltac:(oF' 0x562a8%Z)) (ltac:(oD' 0x562a8%Z)) (0x1396b0 + 80) Cqc'.
zstep (ltac:(oF' 0x562ac%Z)) (ltac:(oD' 0x562ac%Z)).
zbft (ltac:(oF' 0x562b0%Z)) (ltac:(oD' 0x562b0%Z)).
zld (ltac:(oF' 0x562b4%Z)) (ltac:(oD' 0x562b4%Z)) (0x1396b0 + 64) Cqm'.
zbtk (ltac:(oF' 0x562b8%Z)) (ltac:(oD' 0x562b8%Z)).
zstep (ltac:(oF' 0x5637c%Z)) (ltac:(oD' 0x5637c%Z)). zstep (ltac:(oF' 0x56380%Z)) (ltac:(oD' 0x56380%Z)). zstep (ltac:(oF' 0x56384%Z)) (ltac:(oD' 0x56384%Z)). zstep (ltac:(oF' 0x56388%Z)) (ltac:(oD' 0x56388%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G40' : cellA X 0x134398 8 0x13a238) by zcell; assert (Cff' : cellA X (0x13a238 + 48) 4 0) by zcell end.
zld (ltac:(oF' 0x5638c%Z)) (ltac:(oD' 0x5638c%Z)) 0x134398 G40'.
zlw (ltac:(oF' 0x56390%Z)) (ltac:(oD' 0x56390%Z)) (0x13a238 + 48) Cff'.
zbtk (ltac:(oF' 0x56394%Z)) (ltac:(oD' 0x56394%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi2);
replace ((3 + 256 * b1) / 65536) with 0 in Chi2 by (symmetry; apply Z.div_small; lia);
assert (Cn2 : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
zlhu (ltac:(oF' 0x563dc%Z)) (ltac:(oD' 0x563dc%Z)) (p - 16 + 2) Chi2.
zlwu (ltac:(oF' 0x563e0%Z)) (ltac:(oD' 0x563e0%Z)) (p - 16 + 4) Cn2.
zstep (ltac:(oF' 0x563e4%Z)) (ltac:(oD' 0x563e4%Z)).
stepn (ltac:(oF' 0x563e8%Z)) (ltac:(oD' 0x563e8%Z)). rwH. try rewrite art_zb_slli by lia.
stepn (ltac:(oF' 0x563ec%Z)) (ltac:(oD' 0x563ec%Z)). rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
zstep (ltac:(oF' 0x563f0%Z)) (ltac:(oD' 0x563f0%Z)).
stepn (ltac:(oF' 0x563f4%Z)) (ltac:(oD' 0x563f4%Z)). rwH. unfold v_andi. rewrite (art_u_lit (n + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
zstep (ltac:(oF' 0x563f8%Z)) (ltac:(oD' 0x563f8%Z)). zstep (ltac:(oF' 0x563fc%Z)) (ltac:(oD' 0x563fc%Z)).
stepn (ltac:(oF' 0x56400%Z)) (ltac:(oD' 0x56400%Z)).
unfold art_fx_fq1_mem. zret.
Qed.
End SE.
#[using="Type"] Lemma art_fx_fq2a_fn : ltac2:(TCodec.tc2 tcn__JbtFxPut "S3&5y5'QEyR0%211%5241'0y8%611%311p061'4'3&>r8(QC+9(1%33A21%6251&QDr5%22C1%;3C41r9+D%;3I19%>231%@3H16r:+C%@3N1>%C231%E3M1;r;+E%E3Q31C%H231%J3Q21@r<+B%J3Q81H%M231%O3Q71E':&B&?vQ3r=+ZiP4%Q33Q?1Q1/01Q?%65541=B&@+1%Q83QF1Q6+ZiPL%Q52QF1%53:31+:%Q=3QK1Q;%Q92QJQ0%93421+;%QA3QO1Q?%Q=2QNQ9%=3421+<%QE3R31QC%QA2R2QG%A3421+=%QI3R71QGr7%QF2R71%F3531+>%QN3R<1QLr6%QK2R<1%K3531+ZiQ8%R33R?1R1/01R?%Q65Q541Q=QB%Q93Q8Q11p0Q;1p0QA1p0QG1p0QM1p0R31pRJR@1pRHRA1pS6RB1pQNRC1pQLRD1pS4RF1p>RG1pS2RM1").
Proof.
intros regs M rom c ca st m n H9 H20 H19 H21 H18.
zstep (ltac:(oF' 0x56404%Z)) (ltac:(oD' 0x56404%Z)). zstep (ltac:(oF' 0x56408%Z)) (ltac:(oD' 0x56408%Z)). zstep (ltac:(oF' 0x5640c%Z)) (ltac:(oD' 0x5640c%Z)). zstep (ltac:(oF' 0x56410%Z)) (ltac:(oD' 0x56410%Z)). zstep (ltac:(oF' 0x56414%Z)) (ltac:(oD' 0x56414%Z)).
stepn (ltac:(oF' 0x56418%Z)) (ltac:(oD' 0x56418%Z)).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_fx_fq2e_fn := (ltac2:(TCodec.tc2 tcn__JbtFxPut "V?&5y5'QEyR0%211%5241'0y8%611%311p061'4'3&>r=(QC+2(1%33A21%6251&QD&Kr9+RU0%3221%52F1%>3F71&;r;%211&F&D+`PQoooPP0+XP0%3221%5217&Hr<&J+Q?%22H1%5241'2z%>217+R0%82N1%;2:1%6241&8&BrHrE+RRH%Q1221u8+_Tj4%8576321rIrF+RS0%Q8221%=5<4173rJrG+RS8%Q=221%B5A41<8rK+RS@%QA2C1+_TfD%G5F42A1rL+RSH%QF2A1+1%L5K42F1rM+RT0%QK2A1+RR@%QM2C1%Q25Q153L1rN+RT8%R12B1+RA%R32D1%Q85Q753Q21rO+RT@%R72C1%Q<5Q;31Q6NrQ0+8%R;2B1&QF%12RO>%QB5QA53Q<1rQ1+@%RA2B1%QF5QE31Q@Q3rQ2+H%RE2@1%QJ5QI31QDQ7rQ3+Q0%RI2@1%QN5QM31QHQ;rQ4+Q8%RM2>1%R25R131QLQ?rQ5+Q@%S12>1%R65R531R0QCrQ6+QH%S52>1%R:5R931R4QG':&?vQ3rQ8+ZhjD%SB3SN1S@/01SNrQ7%756521<&@%SG3T5QJSE%2381C%SD2T5H%432SG1%SK3T9Q;SI%SG2T8Q7%73321+9%SO3T=1SM%SK2T<QA%;3421+B%T33TA1T1%SO2T@QI%?3421+C%T73TE1T5%T32TDR3%C3421+D%T;3TI1T9%T72THR=%G3421+E%T?3TM1T=%T;2TLRF%K3421+F%TC3U11TA%T?2U0QK%O3421%Q85Q71QAQ2Q=%Q:3SDQ21p0Q<1p0QA1p0QF1p0QK1p0R01p0R51p0R:1p0RA1p0RF1p0RM1p0S41p0S:1p0S@1p0SF1p0SL1p0T61p0T71p0T81p0T91p0T:1p0T;1p0T<1p0T=1p0TE1p0TL1p0U31p0U71pRDUG1pRBUH1pR@UI1pR>UJ1pR<UK1pR:UL1pR6UM1pRLUN1pQ8UO1pS0V71pS4V21p>V31pS2V91")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 3%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 5%nat 0%nat).
Variable f22 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 6%nat 0%nat).
Variable g16 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 7%nat 0%nat).
Variable g24 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 8%nat 0%nat).
Variable g32 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 9%nat 0%nat).
Variable g40 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 10%nat 0%nat).
Variable g48 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 11%nat 0%nat).
Variable g56 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fq2e_fn) 12%nat 0%nat).
Lemma art_fx_fq2e_fn : ltac:(sec_stmt2 constr:(SEC_T_art_fx_fq2e_fn) 13%nat 0%nat).
Proof using Type regs M rom raw0 S p f22 g16 g24 g32 g40 g48 g56.
intros H2 Hret HS HS' Hp Hf22 Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
zld (ltac:(oF' 0x56354%Z)) (ltac:(oD' 0x56354%Z)) (S - 2136) E36. zld (ltac:(oF' 0x56358%Z)) (ltac:(oD' 0x56358%Z)) (S - 2144) E44. zld (ltac:(oF' 0x5635c%Z)) (ltac:(oD' 0x5635c%Z)) (S - 2152) E52. zld (ltac:(oF' 0x56360%Z)) (ltac:(oD' 0x56360%Z)) (S - 2160) E60.
zld (ltac:(oF' 0x56364%Z)) (ltac:(oD' 0x56364%Z)) (S - 2168) E68. zld (ltac:(oF' 0x56368%Z)) (ltac:(oD' 0x56368%Z)) (S - 2176) E76. zld (ltac:(oF' 0x5636c%Z)) (ltac:(oD' 0x5636c%Z)) (S - 2184) E84. zld (ltac:(oF' 0x56370%Z)) (ltac:(oD' 0x56370%Z)) (S - 2192) E92.
zstep (ltac:(oF' 0x56374%Z)) (ltac:(oD' 0x56374%Z)).
stepjr (ltac:(oF' 0x56378%Z)) (ltac:(oD' 0x56378%Z)) (0x79344 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x79344%Z)) (ltac:(oD' 0x79344%Z)).
zld (ltac:(oF' 0x79348%Z)) (ltac:(oD' 0x79348%Z)) (S - 8) F8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7934c%Z)) (ltac:(oD' 0x7934c%Z)) (S - 16) F16. zld (ltac:(oF' 0x79350%Z)) (ltac:(oD' 0x79350%Z)) (S - 24) F24. zld (ltac:(oF' 0x79354%Z)) (ltac:(oD' 0x79354%Z)) (S - 32) F32.
zld (ltac:(oF' 0x79358%Z)) (ltac:(oD' 0x79358%Z)) (S - 40) F40. zld (ltac:(oF' 0x7935c%Z)) (ltac:(oD' 0x7935c%Z)) (S - 48) F48. zld (ltac:(oF' 0x79360%Z)) (ltac:(oD' 0x79360%Z)) (S - 56) F56.
zstep (ltac:(oF' 0x79364%Z)) (ltac:(oD' 0x79364%Z)).
stepret (ltac:(oF' 0x79368%Z)) (ltac:(oD' 0x79368%Z)) raw0 ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_fx_fq2n_fn : ltac2:(TCodec.tc2 tcn__JbtFxPut "WD&5y5'QEyR0%211%5241'0y8%611%311p061'4'3&>r?(QC+2(1%33A21%6251&QD&Kr;+RU0%3221%52F1%>3F71r@+9%>3L1<%A231r:%<2M1%E3M31rA+F%E3Q31C%H231&J+D%22H1%E2Q61%N3Q651&;%11N&F&D+`PQoooPP0+XP0%3221%521Q4&H+Q?%?2Q51%32K1'2z%<21N+R0%E2Q;1%92Q11%6241r>%B271%=225%:221%E2:Q0rB+Q0%G221%C21;%J2?4%K25Q0%B221%G2Q8?%D291&8&BrOrJ+H%Q3221u8rI%8576321rQ0rM+RRH%R3221+_Tj4%>5=5281rQ1rN+RS0%R9221%C5B41=3rQ2+RS8%R=2D1%G5F31A7rQ3+RS@%RA2A1+_TfD%L5K42F1rQ4+RSH%RF2@1+1%Q15Q042K1rQ5+RT0%RK2@1+RR@%RM2B1%Q75Q653Q11rQ6+RT8%S12B1+RA%S32D1%Q=5Q<53Q71rQ7+RT@%S72C1%QA5Q@31Q;Q8rQ8+8%S;2B1&QF%12SO>%QG5QF53QA1rQ9+@%SA2B1%QK5QJ31QEQ<rQ:%SD2?QI%QN5QM21QHQ?rQ;%SG2>R8%R15R021QKQBrQ<+Q8%SK2<1%R55R431QOQFrQ=+Q@%SO2<1%R95R831R3QJrQ>+QH%T32=1%R=5R<31R7QN':&?vQ3rQ@+ZiPL%T@3TL1T>/01TLrQ?%756521<&@%TE3U3QHTC%2381C%TB2U3H%432TE1%TI3U7Q9TG%TE2U6Q?%73321%TG2U8QG%932T?1+:%TO3U=1TM%TK2U<Q;%=3421+B%U33UA1U1%TO2U@R5%A3421+C%U73UE1U5%U32UDR>%E3421%U:3UHTBU8%U62UGRF%H3321+E%U>3UL1U<%U:2UKRN%L3421%U<2UMR2%N32TM1%Q75Q61Q@Q1Q<%Q93SFQ11p0Q;1p0Q@1p0QE1p0QJ1p0QN1p0R21p0R71p0R>1p0RC1p0RJ1p0S11p0S71p0S=1p0SB1p0SH1p0SO1p0T91p0T:1p0T;1p0T<1p0T=1p0T>1p0TA1p0TE1p0TJ1p0TL1p0U11p0U91p0U>1p0UE1p0UH1p0V21p0V:1pRDVJ1pRBVK1pR@VL1pR>VM1pR<VN1pR:VO1pR6W01pR4W11pQLW21pRLW31pQ8W41pS0W<1pS4W71p>W81pS2W>1").
Proof.
intros regs M rom raw0 S p c csz f22 g16 g24 g32 g40 g48 g56 H2 H9 H22 Hret HS HS' Hp Hf22 Hc Hc' Hcsz Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Ccsz E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
zld (ltac:(oF' 0x5641c%Z)) (ltac:(oD' 0x5641c%Z)) (c + 24) Ccsz.
zbft (ltac:(oF' 0x56420%Z)) (ltac:(oD' 0x56420%Z)).
stepn (ltac:(oF' 0x56424%Z)) (ltac:(oD' 0x56424%Z)).
zcall (art_fx_fq2e_fn _ _ _ raw0 S p f22 g16 g24 g32 g40 g48 g56).
zret.
Qed.
#[using="Type"] Lemma art_fx_fq2d_fn : ltac2:(TCodec.tc2 tcn__JbtFxPut "TA&5y5'QEyR0%211%5241'0y8%611%311p061'4'3&>r9(QC+2(1%33A21%6251&QD&Kr6+RU0%3221%52F1%>3F71r:+8%>3L1<%A231r5%<2M1%E3M31r;+9%E3Q31C%H231r7%C2Q41%L3Q431r<+F%L3Q:1J%O231&J+D%22O1%L2Q=1%Q53Q=51&F&D+`PQoooPP0+XP0%3221%521L&H+Q?%=2Q:1%32I1z%;21K+Q0%<2F1+R0%D2QA1%:231'2%<2EQ2%=2Q34%3221&8&BrAr>+H%I221u8%756521Q5rBr@%QL21QJ%;5:315Q9rC+RTH%R02<1%?5>319Q=':&?vQ3rE+ZiPL%R=3RI1R;/01RIrD%756521<&@+1%RC3S11RA+ZhjD%R@2S11%53;31+:%RH3S61RF%RD2S5H%93421+;%RL3S:1RJ%RH2S9Q3%=3421+<%S03S>1RN%RL2S=Q6%A3421+=%S43SB1S2r=%S12SB1%F3531+Z^l0%S93SE1S7/01SE%Q25Q141LQ7%Q43QCL1p0Q61p0Q;1p0Q@1p0QI1p0QN1p0R41p0R71p0R<1p0RC1p0RM1p0S51p0S=1pR2SM1pR0SN1pR4SO1pRNT01pQLT11pQ8T21pS4T41p>T51pS2T;1").
Proof.
intros regs M rom S c q csz cbc cbs H2 H8 H9 H22 HS HS' Hc Hc' Hcsz Ccsz Ccbc Ccbs.
zld (ltac:(oF' 0x5641c%Z)) (ltac:(oD' 0x5641c%Z)) (c + 24) Ccsz.
zbtk (ltac:(oF' 0x56420%Z)) (ltac:(oD' 0x56420%Z)).
zld (ltac:(oF' 0x56340%Z)) (ltac:(oD' 0x56340%Z)) (S - 2208) Ccbc.
zld (ltac:(oF' 0x56344%Z)) (ltac:(oD' 0x56344%Z)) (S - 2200) Ccbs.
zstep (ltac:(oF' 0x56348%Z)) (ltac:(oD' 0x56348%Z)). zstep (ltac:(oF' 0x5634c%Z)) (ltac:(oD' 0x5634c%Z)).
stepn (ltac:(oF' 0x56350%Z)) (ltac:(oD' 0x56350%Z)).
zret.
Qed.
End FPX.
