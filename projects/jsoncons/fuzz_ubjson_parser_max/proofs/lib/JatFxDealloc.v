(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatPoison JatAllocG JatUnwind JatFree1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatFxDealloc () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFxDealloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2or"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6msteps"; "7hid"; "8art_fx_fcu2_mem"; "9art_tsd"; ":getr"]; [":mkst"; ":regupd"; ":v_or"; ";loaded_segments"; "0S"; "<add"; "<le"; "<lor"; "<lt"; "<modulo"; "<mul"; "<pow"; "<sub"; "0b1"; "0ctx"; "0f22"]; ["0f23"; "0f24"; "0fr1"; "0fr2"; "0fx"; "0key"; "0n"; "0p"; "0regs"; "0rom"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0sz"; "0t"]; ["0tp"; "0tsd"; "0x"; "0y"]]).
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
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Ltac zlhu F D a HYP :=
chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].
Lemma art_fx_zb_or : ltac2:(TCodec.tc2 tcn__JatFxDealloc "Q0'5'2&Fzr2%3221&H&K+2+R0%3221%5271%;271'3'Q<yR0%211&B&Q;r4%2251r3%4271%6231&G%1264%82;1%>3;41p0@1p0A1pS8N1pS6O1").
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.
Definition art_fx_fcu2_mem (M : word -> option byte) (S p b1 n sz t fr1 fr2 f22 f23 f24 : Z) : word -> option byte :=
(Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) 495732) (S - 2144) S) (S - 2152) p) (S - 2160) 495620) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2192 - 8) 334108) (S - 2192 - 16) (S - 2128)) (S - 2192 - 24) p) (p - 16) (3 + 256 * b1)) (p - 16 + 16) (2 ^ 64 - 2 ^ 32)) (S - 2192 - 8) 334600) (S - 2192 - 24) 532836) (t + 2800 + 24) (fr1 + 1)) (t + 2800 + 32) (n + fr2)) (S - 2136) 495732) (S - 2144) S) (S - 2152) p) (S - 2160) 495620) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2176 - 8) 351848).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_fx_fcu2_fn := (ltac2:(TCodec.tc2 tcn__JatFxDealloc "\I&6y5'Q<yR0%211%5241'0y8%611%311p061'5'3&?rB(Q:+2(1%33A21%6251&Q;&Lr?+RU0%3221%52F1%>3F71rC+H%>3L1<%A231&Er;+QoO%3221%?2Q01%H3Q061rD+4%H3Q61F%K231%E2Q69%N3Q621&F+`PQoooPP0+XP0%?221%421Q1&H&K+Q?%22Q31%42I1+VbTP0+@%H221%=21M+8%K2E1%;218&IrE%2218z%QD3QE21'2%G235+X0%D271%4231rF%;21Q1+1%QM3QN21%O224+Q0%K2QL1%M271%=241+N%Q52:1%@271+TP0%Q821=rG%QF213+R0%Q62R71%Q8231&8rHrM%R721:%443;1Q@%R923Q8rN%R;21>%843R51QD%R=23Q<rJ%;42R81BrQ0%RA21D%>4CE1QJrL%@41G?GrQ1%RF21QErI%D42RA1K&<'4%RA2=N+RPP0%R7221%R82QN@%5221%711rO%RH21Q5%R=217%R>2R43%;221%=11+RPX0%RB217%RO2IR5%RD21R:%RE2?:+QP0%S32M1%RH21R>%RI2R5>%RE2?Q>%R5221&:&CrQ@rQ>%SF21QI%54431QJrQArQ:%84721QMrQBrQ?%SM21RL%<4;31SG&>rQCrQ;rQ9rQ8rQ<%6654<321&9rQD+RRH%T92>1u8+_TS0%65I5321rQE+RS0%T?2?1%:5M316@rQF+RS8%TC2<1%>5Q131:DrQG+RS@%TG2:1&Q=+_TP4%U03U<1TN/01U<%42U>1%G5Q:86C1rQH+RSH%U02?1%K5Q>31GS>rQI+RT0%U42?1+RR@%U62A1%Q15QD53M1rQJ+RT8%U:2<1+RA%U<2>1%Q75QJ53Q31rQK+RT@%U@2>1rQ=%Q<5QO42Q81rQL+RTH%UE2=1%Q@5R331Q<5rQM%UH2:UF%QC5R621Q?8rQN%UK28F+RR0%UM2:1%QH5R;43QD1rQO+RR8%V12:1%QL5R?31QHQ0rR0%V42=U3u4&J%12TID%UN2V=1%R35RF6541rR1+<%V<2B1%R75RJ318JrR2+Qian8%R:5RM21R6U6rR3%R<5RO1OR8QDrR4%V:2QBU@%R?5S221@U;rR5+Rh8%V>2N1%RC5S631R?QGrR6+Rh@%VB2M1%RG5S:31RCQK';&@vQ4rR8+`Ub0%W93WE1W7/01WErR7%756521<&A%W>3WLUEW<+Zgd8%W@3WL1W>/01WL%53;41%W=2GR:%W?2X01%833WB1%WF3X4V<WD%WA2NV@%WC2X41%<3431+9%WK3X91WI%WF2Q0RA%WH2X91%A3531+:%X03X>1WN%WK2Q5QO%WM2X>1%F3531+;%X53XC1X3%X12XBQF%J3421%X83XFQGX6%L3217+=%X;3XI1X9%X72XHRC%Q03421+>%X?3XM1X=%X02RLVG%X<2XM1%Q53531+?%XD3Y21XB+WO%XA2Y21%Q:3531%XH3Y6WAXF+3%XE2Y61%Q>3431+A%XM3Y;1XK%XI2Y:W>%QB3421+B%Y13Y?1XO+QVmdH%XN2Y?1%QG3531+C%Y63YD1Y4%QJ3319+D%Y93YG1Y7%Y52YFS1%QN3421+E%Y=3YK1Y;%Y82RBSM%Y:2YK1%R33531+F%YB3Z01Y@%Y>2YOT;%R73421+G%YF3Z41YD%YB2Z3TC%R;3421%YD2Z5TN%R=32Y<1+cUc<%YL3Z81YJ/01Z8&=%1<RDS3S6S8S;S?SFT;TATGTKU4%RK5RJ631S0%RM3V8RE1p0RO1p0S41p0S91p0S=1p0S@1p0SD1p0SI1p0T11p0T61p0T<1p0T@1p0TE1p0TK1p0U21p0U91p0U>1p0UH1p0UM1p0V21p0V:1p0VB1p0VG1p0VK1p0W21p0W31p0W41p0W51p0W61p0W:1p0W>1p0W@1p0WC1p0WF1p0WM1p0X61p0X;1p0X>1p0XB1p0XF1p0XK1p0Y11p0Y71p0Y:1p0Y>1p0YD1p0YI1p0YO1p0Z51p0Z91p0Z>1p0ZD1p0ZJ1p0[11p0[<1pR4[L1pR2[M1pR0[N1pR8[O1pR6\01pQN\11pS4\21pR<\31pS2\41pS0\51pRN\61pR>\71pQL\81pR@\91pQ:\:1pRD\<1p@\=1pRB\C1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 2%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 4%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 6%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 7%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 8%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 9%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 10%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 11%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 12%nat 0%nat).
Variable fr1 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 13%nat 0%nat).
Variable fr2 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 14%nat 0%nat).
Variable f22 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 15%nat 0%nat).
Variable f23 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 16%nat 0%nat).
Variable f24 : ltac:(sec_ty2 constr:(SEC_T_art_fx_fcu2_fn) 17%nat 0%nat).
Lemma art_fx_fcu2_fn : ltac:(sec_stmt2 constr:(SEC_T_art_fx_fcu2_fn) 18%nat 0%nat).
Proof using Type regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24.
intros H2 H24 H4 HS HS' Hp Hp' Hp16 Hb1 Hb14 Hn Hsz Ht Ht' Atsp Apsp Apt Actx Atctx Apctx Cimg Timg
Htp0 Htp1 Htsd0 Htsd Hfr1 Hfr2 Hf22 Hf23 Hf24 W Wt Wp TSD C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 C28 C20 Chw Cn Cfh Ctctx Ctid Cfr1 Cfr2.
pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR). pose proof Timg as Timg'; unfold hid in Timg'.
zsb (ltac:(oF' 0x81640%Z)) (ltac:(oD' 0x81640%Z)) (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (D36 : cellA X (S - 2136) 8 0x79060) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 p) by zcell;
assert (D60 : cellA X (S - 2160) 8 (U (0x79004 : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
zld (ltac:(oF' 0x81644%Z)) (ltac:(oD' 0x81644%Z)) (S - 2136) D36. zld (ltac:(oF' 0x81648%Z)) (ltac:(oD' 0x81648%Z)) (S - 2144) D44. zld (ltac:(oF' 0x8164c%Z)) (ltac:(oD' 0x8164c%Z)) (S - 2152) D52. zld (ltac:(oF' 0x81650%Z)) (ltac:(oD' 0x81650%Z)) (S - 2160) D60.
zld (ltac:(oF' 0x81654%Z)) (ltac:(oD' 0x81654%Z)) (S - 2168) D68. zld (ltac:(oF' 0x81658%Z)) (ltac:(oD' 0x81658%Z)) (S - 2176) D76. zld (ltac:(oF' 0x8165c%Z)) (ltac:(oD' 0x8165c%Z)) (S - 2184) D84. zld (ltac:(oF' 0x81660%Z)) (ltac:(oD' 0x81660%Z)) (S - 2192) D92.
zld (ltac:(oF' 0x81664%Z)) (ltac:(oD' 0x81664%Z)) (S - 2200) D00. zld (ltac:(oF' 0x81668%Z)) (ltac:(oD' 0x81668%Z)) (S - 2208) D08.
zstep (ltac:(oF' 0x8166c%Z)) (ltac:(oD' 0x8166c%Z)).
stepjr (ltac:(oF' 0x81670%Z)) (ltac:(oD' 0x81670%Z)) (0x79060 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x79060%Z)) (ltac:(oD' 0x79060%Z)). zstep (ltac:(oF' 0x79064%Z)) (ltac:(oD' 0x79064%Z)). zstep (ltac:(oF' 0x79068%Z)) (ltac:(oD' 0x79068%Z)). zstep (ltac:(oF' 0x7906c%Z)) (ltac:(oD' 0x7906c%Z)).
stepn (ltac:(oF' 0x79070%Z)) (ltac:(oD' 0x79070%Z)).
zstep (ltac:(oF' 0x518a8%Z)) (ltac:(oD' 0x518a8%Z)). zstep (ltac:(oF' 0x518ac%Z)) (ltac:(oD' 0x518ac%Z)). zstep (ltac:(oF' 0x518b0%Z)) (ltac:(oD' 0x518b0%Z)). zstep (ltac:(oF' 0x518b4%Z)) (ltac:(oD' 0x518b4%Z)). zstep (ltac:(oF' 0x518b8%Z)) (ltac:(oD' 0x518b8%Z)). zstep (ltac:(oF' 0x518bc%Z)) (ltac:(oD' 0x518bc%Z)).
zstep (ltac:(oF' 0x518c0%Z)) (ltac:(oD' 0x518c0%Z)). zstep (ltac:(oF' 0x518c4%Z)) (ltac:(oD' 0x518c4%Z)). zstep (ltac:(oF' 0x518c8%Z)) (ltac:(oD' 0x518c8%Z)).
stepn (ltac:(oF' 0x518cc%Z)) (ltac:(oD' 0x518cc%Z)).
zstep (ltac:(oF' 0x518d0%Z)) (ltac:(oD' 0x518d0%Z)).
zsd (ltac:(oF' 0x518d4%Z)) (ltac:(oD' 0x518d4%Z)) (S - 2136) (U (0x79074 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x518d8%Z)) (ltac:(oD' 0x518d8%Z)) (S - 2144) S ltac:(rewok W). zsd (ltac:(oF' 0x518dc%Z)) (ltac:(oD' 0x518dc%Z)) (S - 2152) p ltac:(rewok W).
zsd (ltac:(oF' 0x518e0%Z)) (ltac:(oD' 0x518e0%Z)) (S - 2160) (U (0x79004 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x518e4%Z)) (ltac:(oD' 0x518e4%Z)) (S - 2168) 1 ltac:(rewok W). zsd (ltac:(oF' 0x518e8%Z)) (ltac:(oD' 0x518e8%Z)) (S - 2176) (S - 2128) ltac:(rewok W).
zsd (ltac:(oF' 0x518ec%Z)) (ltac:(oD' 0x518ec%Z)) (S - 2184) (S - 81) ltac:(rewok W). zsd (ltac:(oF' 0x518f0%Z)) (ltac:(oD' 0x518f0%Z)) (S - 2192) f22 ltac:(rewok W).
zbft (ltac:(oF' 0x518f4%Z)) (ltac:(oD' 0x518f4%Z)).
zstep (ltac:(oF' 0x518f8%Z)) (ltac:(oD' 0x518f8%Z)). zstep (ltac:(oF' 0x518fc%Z)) (ltac:(oD' 0x518fc%Z)). zstep (ltac:(oF' 0x51900%Z)) (ltac:(oD' 0x51900%Z)). zstep (ltac:(oF' 0x51904%Z)) (ltac:(oD' 0x51904%Z)). zstep (ltac:(oF' 0x51908%Z)) (ltac:(oD' 0x51908%Z)). zstep (ltac:(oF' 0x5190c%Z)) (ltac:(oD' 0x5190c%Z)). zstep (ltac:(oF' 0x51910%Z)) (ltac:(oD' 0x51910%Z)). zstep (ltac:(oF' 0x51914%Z)) (ltac:(oD' 0x51914%Z)).
stepn (ltac:(oF' 0x51918%Z)) (ltac:(oD' 0x51918%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cfh' : cellA X 0x1cc7c8 8 0) by (unfold hid in Timg; zcell) end.
zcall (art_run_free_hooks_fn _ _ _ _ (S - 2192)).
zbtk (ltac:(oF' 0x5191c%Z)) (ltac:(oD' 0x5191c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chw' : cellA X (p - 16) 4 (2 + 256 * b1)) by zcell; assert (Wp' : wrA X (p - 16) 24) by zwr end.
assert (Hm16 : (p - 16) mod 16 = 0) by (replace (p - 16) with (p + (-1) * 16) by lia; rewrite Z_mod_plus_full; exact Hp16).
zcall (art_cas23_fn _ _ _ (p - 16) b1).
zstep (ltac:(oF' 0x51998%Z)) (ltac:(oD' 0x51998%Z)). zstep (ltac:(oF' 0x5199c%Z)) (ltac:(oD' 0x5199c%Z)).
zsd (ltac:(oF' 0x519a0%Z)) (ltac:(oD' 0x519a0%Z)) (p - 16 + 16) (2 ^ 64 - 2 ^ 32) ltac:(rewok Wp).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (Cst & Cb1 & Chi) end.
replace ((3 + 256 * b1) mod 256) with 3 in Cst by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity).
replace ((3 + 256 * b1) / 256 mod 256) with b1 in Cb1 by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_div_plus_full, (Z.div_small 3) by lia; rewrite Z.mod_small by lia; lia).
replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia).
zlbu (ltac:(oF' 0x519a4%Z)) (ltac:(oD' 0x519a4%Z)) (p - 16 + 1) Cb1.
stepn (ltac:(oF' 0x519a8%Z)) (ltac:(oD' 0x519a8%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land b1 3) with 1 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia).
zbft (ltac:(oF' 0x519ac%Z)) (ltac:(oD' 0x519ac%Z)).
stepn (ltac:(oF' 0x519b0%Z)) (ltac:(oD' 0x519b0%Z)). rwH. unfold v_andi. rewrite art_u_lit by lia. change (Z_to_bv 64 (Z.land 1 (bv_wrap 64 (-2)))) with (Z_to_bv 64 0 : word).
zstep (ltac:(oF' 0x519b4%Z)) (ltac:(oD' 0x519b4%Z)).
zbtk (ltac:(oF' 0x519b8%Z)) (ltac:(oD' 0x519b8%Z)).
stepn (ltac:(oF' 0x51b04%Z)) (ltac:(oD' 0x51b04%Z)).
zcall (art_thread_stats_fn _ _ _ _ (S - 2192) tp key tsd ctx t).
{ unfold art_tsd. repeat split; try lia; zcell. }
all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi');
replace ((3 + 256 * b1) / 65536) with 0 in Chi' by (symmetry; apply Z.div_small; lia); replace (p - 16 + 2) with (p - 14) in Chi' by lia;
assert (Cn' : cellA X (p - 12) 4 n) by zcell;
assert (Cfr1' : cellA X (t + 2800 + 24) 8 fr1) by (replace (t + 2800 + 24) with (t + 2824) by lia; zcell);
assert (Cfr2' : cellA X (t + 2800 + 32) 8 fr2) by (replace (t + 2800 + 32) with (t + 2832) by lia; zcell) end.
zlhu (ltac:(oF' 0x51b08%Z)) (ltac:(oD' 0x51b08%Z)) (p - 14) Chi'.
zlwu (ltac:(oF' 0x51b0c%Z)) (ltac:(oD' 0x51b0c%Z)) (p - 12) Cn'.
zld (ltac:(oF' 0x51b10%Z)) (ltac:(oD' 0x51b10%Z)) (t + 2800 + 32) Cfr2'. zld (ltac:(oF' 0x51b14%Z)) (ltac:(oD' 0x51b14%Z)) (t + 2800 + 24) Cfr1'.
zstep (ltac:(oF' 0x51b18%Z)) (ltac:(oD' 0x51b18%Z)).
stepn (ltac:(oF' 0x51b1c%Z)) (ltac:(oD' 0x51b1c%Z)). rwH. rewrite art_fx_zb_or by lia. rewrite Z.lor_0_l.
zstep (ltac:(oF' 0x51b20%Z)) (ltac:(oD' 0x51b20%Z)). zstep (ltac:(oF' 0x51b24%Z)) (ltac:(oD' 0x51b24%Z)).
zsd (ltac:(oF' 0x51b28%Z)) (ltac:(oD' 0x51b28%Z)) (t + 2800 + 24) (fr1 + 1) ltac:(rewok Wt).
zsd (ltac:(oF' 0x51b2c%Z)) (ltac:(oD' 0x51b2c%Z)) (t + 2800 + 32) (n + fr2) ltac:(rewok Wt).
zstep (ltac:(oF' 0x51b30%Z)) (ltac:(oD' 0x51b30%Z)). zstep (ltac:(oF' 0x51b34%Z)) (ltac:(oD' 0x51b34%Z)). zstep (ltac:(oF' 0x51b38%Z)) (ltac:(oD' 0x51b38%Z)). zstep (ltac:(oF' 0x51b3c%Z)) (ltac:(oD' 0x51b3c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (E36 : cellA X (S - 2136) 8 (U (0x79074 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x79004 : bv 64)%bv)) by zcell;
assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell;
assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell end.
zld (ltac:(oF' 0x51b40%Z)) (ltac:(oD' 0x51b40%Z)) (S - 2136) E36. zld (ltac:(oF' 0x51b44%Z)) (ltac:(oD' 0x51b44%Z)) (S - 2144) E44. zld (ltac:(oF' 0x51b48%Z)) (ltac:(oD' 0x51b48%Z)) (S - 2152) E52. zld (ltac:(oF' 0x51b4c%Z)) (ltac:(oD' 0x51b4c%Z)) (S - 2160) E60.
zld (ltac:(oF' 0x51b50%Z)) (ltac:(oD' 0x51b50%Z)) (S - 2168) E68. zld (ltac:(oF' 0x51b54%Z)) (ltac:(oD' 0x51b54%Z)) (S - 2176) E76. zld (ltac:(oF' 0x51b58%Z)) (ltac:(oD' 0x51b58%Z)) (S - 2184) E84. zld (ltac:(oF' 0x51b5c%Z)) (ltac:(oD' 0x51b5c%Z)) (S - 2192) E92.
zstep (ltac:(oF' 0x51b60%Z)) (ltac:(oD' 0x51b60%Z)).
stepn (ltac:(oF' 0x51b64%Z)) (ltac:(oD' 0x51b64%Z)).
zstep (ltac:(oF' 0x55e30%Z)) (ltac:(oD' 0x55e30%Z)).
zsd (ltac:(oF' 0x55e34%Z)) (ltac:(oD' 0x55e34%Z)) (S - 2136) (U (0x79074 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x55e38%Z)) (ltac:(oD' 0x55e38%Z)) (S - 2144) S ltac:(rewok W). zsd (ltac:(oF' 0x55e3c%Z)) (ltac:(oD' 0x55e3c%Z)) (S - 2152) p ltac:(rewok W).
zsd (ltac:(oF' 0x55e40%Z)) (ltac:(oD' 0x55e40%Z)) (S - 2160) (U (0x79004 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x55e44%Z)) (ltac:(oD' 0x55e44%Z)) (S - 2168) 1 ltac:(rewok W). zsd (ltac:(oF' 0x55e48%Z)) (ltac:(oD' 0x55e48%Z)) (S - 2176) (S - 2128) ltac:(rewok W).
zstep (ltac:(oF' 0x55e4c%Z)) (ltac:(oD' 0x55e4c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Hhw3 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw3) as (Cst' & _ & _);
replace ((3 + 256 * b1) mod 256) with 3 in Cst' by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity) end.
zlb (ltac:(oF' 0x55e50%Z)) (ltac:(oD' 0x55e50%Z)) (p - 16) Cst'.
zstep (ltac:(oF' 0x55e54%Z)) (ltac:(oD' 0x55e54%Z)).
zbft (ltac:(oF' 0x55e58%Z)) (ltac:(oD' 0x55e58%Z)).
zstep (ltac:(oF' 0x55e5c%Z)) (ltac:(oD' 0x55e5c%Z)). zstep (ltac:(oF' 0x55e60%Z)) (ltac:(oD' 0x55e60%Z)).
stepn (ltac:(oF' 0x55e64%Z)) (ltac:(oD' 0x55e64%Z)).
zcall (art_cur_thread_fn _ _ _ _ (S - 2176) tp key tsd ctx t).
{ unfold art_tsd. repeat split; try lia; zcell. }
all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
zbft (ltac:(oF' 0x55e68%Z)) (ltac:(oD' 0x55e68%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Ctctx' : cellA X t 8 ctx) by zcell;
assert (C28' : cellA X (S - 2128) 8 (S - 2112)) by zcell;
assert (C20' : cellA X (S - 2128 + 8) 8 sz) by (replace (S - 2128 + 8) with (S - 2120) by lia; zcell);
assert (Ctid' : cellA X (ctx + 8) 4 0) by zcell end.
zld (ltac:(oF' 0x55e6c%Z)) (ltac:(oD' 0x55e6c%Z)) t Ctctx'. zld (ltac:(oF' 0x55e70%Z)) (ltac:(oD' 0x55e70%Z)) (S - 2128) C28'. zld (ltac:(oF' 0x55e74%Z)) (ltac:(oD' 0x55e74%Z)) (S - 2128 + 8) C20'.
zlw (ltac:(oF' 0x55e78%Z)) (ltac:(oD' 0x55e78%Z)) (ctx + 8) Ctid'.
zstep (ltac:(oF' 0x55e7c%Z)) (ltac:(oD' 0x55e7c%Z)). zstep (ltac:(oF' 0x55e80%Z)) (ltac:(oD' 0x55e80%Z)).
stepn (ltac:(oF' 0x55e84%Z)) (ltac:(oD' 0x55e84%Z)).
unfold art_fx_fcu2_mem. zret.
Qed.
End SE.
End FPX.
