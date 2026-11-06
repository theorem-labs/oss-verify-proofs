(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.GcFlush06.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import muslA.Ja0SumsMemset_code muslA.Ja0SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JatPoison JatPoisonRun JatPoison2G.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAnnotate () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAnnotate."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAnnotate.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoisonRun."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "0M'"; "5cell"; "5wr"; "6msteps"; "7ret_ok"]; ["9art_ann_lo"; "9art_ann_n"; "9art_ann_v"; "8art_ann_kept"; ":SB"; ":art_layout"; ":art_poison_frame"; ";art_poison_kept"; "<getr"; "<mkst"; "<v_andi"; "=mem_grows"; ">loaded_segments"; "?add"; "?div"; "?le"]; ["?lt"; "?modulo"; "?pow"; "?sub"; "0b"; "0c"; "0fx"; "0g16"; "0g24"; "0g32"; "0g40"; "0g48"; "0g56"; "0i"; "0r"; "0ra"]; ["0raw"; "0regs"; "0regs'"; "0rom"; "0s0"; "0s1"; "0s2"; "0s3"; "0s4"; "0s5"; "0sp"; "0sp0"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"]; ["0u"; "0u'"; "0x"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_ann_kept (r : reg) : Prop := r = 3%bv \/ r = 4%bv \/ r = 22%bv \/ r = 23%bv \/ r = 24%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv.
Lemma art_ann_andim8 : ltac2:(TCodec.tc2 tcn__JatAnnotate "Q0'8'3&Ozr1%3221&Q0&Q2+2+R0%3221%5271%;271'4&Q1r2+8%3221%53B1?'QNyR0%211&J&QMr3%2251-8%5221%?3713p0;1p0B1pT6O1").
Proof.
intros x Hx H8. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
f_equal. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.
Lemma art_ann_andim8_up : ltac2:(TCodec.tc2 tcn__JatAnnotate "Q5'8&Ozr1%3221&Q0&Mr2+7%3221&Q2+2+R0%3221%9251'4&Q1r3+8%3221%53D1B'QNyR0%211&J&QMr4%E21C%3261-8%6221%6295%A3921p0=1p0D1p0O1pT6Q41").
Proof.
intros x Hx Hx' H8. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
f_equal. pose proof (Z.div_mod x 8 ltac:(lia)) as D. rewrite H8, Z.add_0_r in D.
replace (x + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.div_add by lia. change (7 / 8) with 0. lia.
Qed.
Lemma art_ann_and7 : ltac2:(TCodec.tc2 tcn__JatAnnotate "Q1'8'3&Ozr1%3221&Q0&Q2+2+R0%3221%5271%;271'4&Q1r2+8%3221%53B1?'QNyR0%211&J&QMr3%2251+7%5221%528I%@3821p0<1p0C1pT6Q01").
Proof.
intros x Hx H8. rewrite art_zb_andi by lia. f_equal. rewrite Z.land_ones with (n := 3) by lia. change (2 ^ 3) with 8. exact H8.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_ann_pre := (ltac2:(TCodec.tc2 tcn__JatAnnotate "W4&9y5'QNyR0%211%5241'1y8%611%311p061'8'4&Hr9(QL+1(2%33A21%6251r6%93A21r:+2%93G17%<231&QM%12H7%@3H31r;+:%@3N1>%C231%E3M16r<+;%E3Q31C%H231&Mr7%221D%?2Q61%N3Q651r=+<%N3Q<1L%Q1231r8%:21L%G2Q>1%Q63Q>41r>+=%Q63QD1Q4%Q9231%A2Q9Q3%N2QE1%Q=3QE31&Oz%221Q6%G2Q0Q7&Q2+Q?%22Q91%7241'3%92Q=Q6%2281%;2Q?Q3%42:1&Q0+Q8%;2QB1%32O1+VbTP0+RT@%Q7221r@%E221rA+QO%D2QK1%<231&=&LrE&Q3rB%221=%64541>&<rF+QVYa@u8+QWQWH%55;4321rG+S0%QM241u1%:5@421RErH+QVYd8+QiYlH%>5D32;1rIu4%A5G241QA'5'>&IvQ6rL+_\Y4%S43S@1S2/01S@rKrJ%8576321r1+_\aL%S;3SG1S9/01SG&F&QO%12SKD+8%SA3SO1S?%SD2@1%52SO1+9%SE3T31SC%SH2D1%92T31+B%SI3T71SG%SL2H1%=2T71+C%SM3T;1SK%T02L1%A2T;1+D%T13T?1SO%T42Q01%E2T?1+E%T53TC1T3%T82Q41%I2TC1%K9Q2QAIEA=951%Q95Q8Q0M1Q2%Q;3R4Q21%T=2Q2T8%T?3TG1QA%T?2Q4T4+RR@%R72QH1%T52TL1%TD3TL41%TD2Q9Q1%T82TOQL%TG3TO21%TG2Q<Q0%T;2U2R4%TJ3U221%TJ2Q?OrD%T32R81%T@2U71%TO3U741%TO2QDQ0%T72R<RG%TD2U;1%U33U;31%U32QHQ0%T;2R@RE%TH2U?1%U73U?31%UB1UC&C%11QNr3r2%U<221rN%U>213%U@3UH31p071pRN:1%SM2<1%SN2A1%SO2F1%T02L1%T12Q01%T22Q41%T32Q:1%T42Q=1qS6V21%RK2V31p0RM1p0S11p0S61p0S<1p0SC1p0SK1p0T01p0T61p0T;1p0T>1p0TB1p0TH1p0TL1p0U41p0U=1p0UG1p0UM1p0V51pT4V@1pT2VA1pR<VB1pR:VC1pSHVD1pS2VL1pS8VG1pFVH1pS4VN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 3%nat 0%nat).
Variable sp0 : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 4%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 6%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 7%nat 0%nat).
Variable u' : ltac:(sec_ty2 constr:(SEC_T_art_ann_pre) 8%nat 0%nat).
Lemma art_ann_pre : ltac:(sec_stmt2 constr:(SEC_T_art_ann_pre) 9%nat 0%nat).
Proof using Type regs M rom raw sp0 b c u u'.
intros H1 H2 H10 H11 H12 H13 Hb Hbc Hu Hu' Hc40 Hsp Hsp' W CG CF CV CV0.
eexists. split.
{ zstep (ltac:(oF' 0x7b124%Z)) (ltac:(oD' 0x7b124%Z)).
zsd (ltac:(oF' 0x7b128%Z)) (ltac:(oD' 0x7b128%Z)) (sp0 - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x7b12c%Z)) (ltac:(oD' 0x7b12c%Z)) (sp0 - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x7b130%Z)) (ltac:(oD' 0x7b130%Z)) (sp0 - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x7b134%Z)) (ltac:(oD' 0x7b134%Z)) (sp0 - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x7b138%Z)) (ltac:(oD' 0x7b138%Z)) (sp0 - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x7b13c%Z)) (ltac:(oD' 0x7b13c%Z)) (sp0 - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x7b140%Z)) (ltac:(oD' 0x7b140%Z)) (sp0 - 56) (U (getr regs 21)) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (C1 : cellA X 0x132630 8 0x1384f8) by zcell; assert (C2 : cellA X (0x1384f8 + 96) 1 1) by zcell;
assert (C3 : cellA X 0x132688 8 0x1ca798) by zcell; assert (C4 : cellA X 0x1ca798 4 0) by zcell end.
zstep (ltac:(oF' 0x7b144%Z)) (ltac:(oD' 0x7b144%Z)). zstep (ltac:(oF' 0x7b148%Z)) (ltac:(oD' 0x7b148%Z)). zstep (ltac:(oF' 0x7b14c%Z)) (ltac:(oD' 0x7b14c%Z)).
zstep (ltac:(oF' 0x7b150%Z)) (ltac:(oD' 0x7b150%Z)). zld (ltac:(oF' 0x7b154%Z)) (ltac:(oD' 0x7b154%Z)) 0x132630 C1.
zlbu (ltac:(oF' 0x7b158%Z)) (ltac:(oD' 0x7b158%Z)) (0x1384f8 + 96) C2.
zbft (ltac:(oF' 0x7b15c%Z)) (ltac:(oD' 0x7b15c%Z)).
zstep (ltac:(oF' 0x7b160%Z)) (ltac:(oD' 0x7b160%Z)). zstep (ltac:(oF' 0x7b164%Z)) (ltac:(oD' 0x7b164%Z)). zstep (ltac:(oF' 0x7b168%Z)) (ltac:(oD' 0x7b168%Z)).
zstep (ltac:(oF' 0x7b16c%Z)) (ltac:(oD' 0x7b16c%Z)). zld (ltac:(oF' 0x7b170%Z)) (ltac:(oD' 0x7b170%Z)) 0x132688 C3. zlw (ltac:(oF' 0x7b174%Z)) (ltac:(oD' 0x7b174%Z)) 0x1ca798 C4.
zstep (ltac:(oF' 0x7b178%Z)) (ltac:(oD' 0x7b178%Z)). zbft (ltac:(oF' 0x7b17c%Z)) (ltac:(oD' 0x7b17c%Z)).
zbtk (ltac:(oF' 0x7b180%Z)) (ltac:(oD' 0x7b180%Z)).
zbft (ltac:(oF' 0x7b21c%Z)) (ltac:(oD' 0x7b21c%Z)). zbft (ltac:(oF' 0x7b220%Z)) (ltac:(oD' 0x7b220%Z)). zbft (ltac:(oF' 0x7b224%Z)) (ltac:(oD' 0x7b224%Z)).
zstep (ltac:(oF' 0x7b228%Z)) (ltac:(oD' 0x7b228%Z)). zstep (ltac:(oF' 0x7b22c%Z)) (ltac:(oD' 0x7b22c%Z)). zstep (ltac:(oF' 0x7b230%Z)) (ltac:(oD' 0x7b230%Z)). zstep (ltac:(oF' 0x7b234%Z)) (ltac:(oD' 0x7b234%Z)).
zbft (ltac:(oF' 0x7b238%Z)) (ltac:(oD' 0x7b238%Z)).
apply mst_refl. }
zsplit; try kept_solve.
intros r Hr. unfold art_ann_kept in Hr. destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ann_grow := (ltac2:(TCodec.tc2 tcn__JatAnnotate "UB&9y5'QNyR0%211%5241'1y8%611%311p061'8'4&Hr8(QL+2(2%33A21%6251&QM&Q3r5+RR@%3221%52F1%>3F71r9+9%>3L1<%A231%;2L9%D3L21r:+B%D3Q21B%G231&Mr6r3%3221%E2Q61%N3Q661r;+C%N3Q<1L%Q1231r7%;21J%M2Q>1%Q63Q>41r<+D%Q63QD1Q4%Q9231%B2Q98%Q42QE1%Q=3QE31&Q1+8%22Q11z%QB3QC21&Or=%2241r>%N213&Q2+Q?%22QF1%8241&Q0%1279r@%<291'5'3'>&L&IvQ6rG+_\aL%R53RA1R3/01RArFrE%8576321r1+_X_0%R<3RH1R:/01RH%=5<4176%@3?61+1%RA3RO1R?%RD281+_\k<%R?2S01%RH3S031%RH2<RCrD%RB21R@%RD2S51%RM3S541+:%RL3S:1RJ%RO2C1rCrA%R:221%RL2S=1%S53S=51+;%S43SB1S2%S72K1%S02Q;7%S22SC1%S;3SC31+<%S:3SH1S8%S=2Q11%S72SHQN%S@3SH21%S>3SLR2S<%SA2Q51%SB2Q=2%SD3SL21%SD2Q8S4%RM2EQH%S?2T01%SH3T031%SH2Q<S2%SJ3T213%T51T6&C%11Q@r2%SN2S41rI%T0213%T23T:31p061pRN91%R42;1%R52>1%R62C1%R72H1%R82N1%R92Q51%R:2Q>1%R;2QD1%R<2QK1qS6TE1%R?2TF1p0RA1p0RD1p0RM1p0RH1p0RO1p0S31p0S41p0S51p0S61p0S<1p0SD1p0SM1p0T81p0T?1pT4TO1pT2U01pR<U11pR:U21pSHU31pS8U51pFU61pS4U<1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ann_grow) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ann_grow) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ann_grow) 2%nat 0%nat).
Variable sp0 : ltac:(sec_ty2 constr:(SEC_T_art_ann_grow) 3%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_ann_grow) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_ann_grow) 5%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_ann_grow) 6%nat 0%nat).
Variable u' : ltac:(sec_ty2 constr:(SEC_T_art_ann_grow) 7%nat 0%nat).
Lemma art_ann_grow : ltac:(sec_stmt2 constr:(SEC_T_art_ann_grow) 8%nat 0%nat).
Proof using Type regs M rom sp0 b c u u'.
intros H2 H9 H18 H19 H20 Hb8 Hc8 Hu8 Hu8' Hb Hbc Hu Huu Hu'.
assert (Ebc : (b + c) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hc8; reflexivity).
assert (Ebu : (b + u) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hu8; reflexivity).
assert (Ebu' : (b + u') mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hu8'; reflexivity).
eexists. split.
{ zbft (ltac:(oF' 0x7b23c%Z)) (ltac:(oD' 0x7b23c%Z)).
stepn (ltac:(oF' 0x7b240%Z)) (ltac:(oD' 0x7b240%Z)). rwH. rewrite art_ann_and7 by lia.
zbft (ltac:(oF' 0x7b244%Z)) (ltac:(oD' 0x7b244%Z)).
zstep (ltac:(oF' 0x7b248%Z)) (ltac:(oD' 0x7b248%Z)). zstep (ltac:(oF' 0x7b24c%Z)) (ltac:(oD' 0x7b24c%Z)). zstep (ltac:(oF' 0x7b250%Z)) (ltac:(oD' 0x7b250%Z)).
stepn (ltac:(oF' 0x7b254%Z)) (ltac:(oD' 0x7b254%Z)). rwH. rewrite art_ann_and7 by lia.
zbft (ltac:(oF' 0x7b258%Z)) (ltac:(oD' 0x7b258%Z)).
zstep (ltac:(oF' 0x7b25c%Z)) (ltac:(oD' 0x7b25c%Z)). zstep (ltac:(oF' 0x7b260%Z)) (ltac:(oD' 0x7b260%Z)).
zbtk (ltac:(oF' 0x7b264%Z)) (ltac:(oD' 0x7b264%Z)).
stepn (ltac:(oF' 0x7b334%Z)) (ltac:(oD' 0x7b334%Z)). rwH. rewrite art_ann_andim8 by lia.
zbft (ltac:(oF' 0x7b338%Z)) (ltac:(oD' 0x7b338%Z)).
zstep (ltac:(oF' 0x7b33c%Z)) (ltac:(oD' 0x7b33c%Z)).
stepn (ltac:(oF' 0x7b340%Z)) (ltac:(oD' 0x7b340%Z)). rwH. rewrite art_ann_andim8 by lia.
zstep (ltac:(oF' 0x7b344%Z)) (ltac:(oD' 0x7b344%Z)).
stepn (ltac:(oF' 0x7b348%Z)) (ltac:(oD' 0x7b348%Z)). rwH. rewrite art_ann_andim8_up by lia.
zbtk (ltac:(oF' 0x7b34c%Z)) (ltac:(oD' 0x7b34c%Z)).
zstep (ltac:(oF' 0x7b280%Z)) (ltac:(oD' 0x7b280%Z)). zstep (ltac:(oF' 0x7b284%Z)) (ltac:(oD' 0x7b284%Z)). zstep (ltac:(oF' 0x7b288%Z)) (ltac:(oD' 0x7b288%Z)). zstep (ltac:(oF' 0x7b368%Z)) (ltac:(oD' 0x7b368%Z)).
apply mst_refl. }
zsplit; try kept_solve.
intros r Hr. unfold art_ann_kept in Hr. destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ann_shrink := (ltac2:(TCodec.tc2 tcn__JatAnnotate "UC&9y5'QNyR0%211%5241'1y8%611%311p061'8'4&Hr8(QL+2(2%33A21%6251&QM&Q3r5+RR@%3221%52F1%>3F71r9+9%>3L1<%A231%;2L9%D3L21r:+B%D3Q21B%G231&Mr6r3%3221%E2Q61%N3Q661r;+C%N3Q<1L%Q1231r7%;21J%M2Q>1%Q63Q>41r<+D%Q63QD1Q4%Q9231%B2Q98%Q42QE1%Q=3QE31&Q1+8%22Q11z%QB3QC21&Or=%2241r>%N213&Q2+Q?%22QF1%8241%92;E&Q0%12:8r?r@%>221'5'3'>&L&IvQ6rG+_\aL%R73RC1R5/01RCrFrE%8576321r1+_X_0%R>3RJ1R</01RJ%=5<4176%@3?61+1%RC3S11RA%RF281+_\k<%RA2S21%RJ3S231%RJ2<RErD%RD21RB%RF2S71%RO3S741+:%RN3S<1RL%S12C1rC%R;21Q4%RM2S>1%S63S>41+;%S53SC1S3%S82J1rA%S221Q;%S42SE1%S=3SE41+<%S<3SJ1S:%S?2Q11+WL%S:2SK1%SC3SK31%SA3SOR5S?%SD2Q61%SE2Q>2%SG3SO21%SG2Q9S7%SI3T11D%SI2Q;S3%SK3T31F%T61T7&C%11Q?r2%SO2S51rI%T1213%T33T;31p061pRN91%R32;1%R42>1%R52A1%R62F1%R72M1%R82Q51%R92Q=1%R:2QC1%R;2QJ1qS6TF1%R>2TG1p0R@1p0RD1p0RG1p0RI1p0S01p0S41p0S51p0S61p0S71p0S=1p0SE1p0SN1p0T91p0T@1pT4U01pT2U11pR<U21pR:U31pSHU41pS8U61pFU71pS4U=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ann_shrink) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ann_shrink) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ann_shrink) 2%nat 0%nat).
Variable sp0 : ltac:(sec_ty2 constr:(SEC_T_art_ann_shrink) 3%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_ann_shrink) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_ann_shrink) 5%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_ann_shrink) 6%nat 0%nat).
Variable u' : ltac:(sec_ty2 constr:(SEC_T_art_ann_shrink) 7%nat 0%nat).
Lemma art_ann_shrink : ltac:(sec_stmt2 constr:(SEC_T_art_ann_shrink) 8%nat 0%nat).
Proof using Type regs M rom sp0 b c u u'.
intros H2 H9 H18 H19 H20 Hb8 Hc8 Hu8 Hu8' Hb Hbc Hu Huu Hu'.
assert (Ebc : (b + c) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hc8; reflexivity).
assert (Ebu : (b + u) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hu8; reflexivity).
assert (Ebu' : (b + u') mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hu8'; reflexivity).
eexists. split.
{ zbft (ltac:(oF' 0x7b23c%Z)) (ltac:(oD' 0x7b23c%Z)).
stepn (ltac:(oF' 0x7b240%Z)) (ltac:(oD' 0x7b240%Z)). rwH. rewrite art_ann_and7 by lia.
zbft (ltac:(oF' 0x7b244%Z)) (ltac:(oD' 0x7b244%Z)).
zstep (ltac:(oF' 0x7b248%Z)) (ltac:(oD' 0x7b248%Z)). zstep (ltac:(oF' 0x7b24c%Z)) (ltac:(oD' 0x7b24c%Z)). zstep (ltac:(oF' 0x7b250%Z)) (ltac:(oD' 0x7b250%Z)).
stepn (ltac:(oF' 0x7b254%Z)) (ltac:(oD' 0x7b254%Z)). rwH. rewrite art_ann_and7 by lia.
zbft (ltac:(oF' 0x7b258%Z)) (ltac:(oD' 0x7b258%Z)).
zstep (ltac:(oF' 0x7b25c%Z)) (ltac:(oD' 0x7b25c%Z)). zstep (ltac:(oF' 0x7b260%Z)) (ltac:(oD' 0x7b260%Z)).
zbft (ltac:(oF' 0x7b264%Z)) (ltac:(oD' 0x7b264%Z)).
stepn (ltac:(oF' 0x7b268%Z)) (ltac:(oD' 0x7b268%Z)). rwH. rewrite art_ann_andim8 by lia.
zbft (ltac:(oF' 0x7b26c%Z)) (ltac:(oD' 0x7b26c%Z)).
stepn (ltac:(oF' 0x7b270%Z)) (ltac:(oD' 0x7b270%Z)). rwH. rewrite art_ann_andim8 by lia.
zstep (ltac:(oF' 0x7b274%Z)) (ltac:(oD' 0x7b274%Z)).
stepn (ltac:(oF' 0x7b278%Z)) (ltac:(oD' 0x7b278%Z)). rwH. rewrite art_ann_andim8_up by lia.
zbtk (ltac:(oF' 0x7b27c%Z)) (ltac:(oD' 0x7b27c%Z)).
zstep (ltac:(oF' 0x7b350%Z)) (ltac:(oD' 0x7b350%Z)).
stepn (ltac:(oF' 0x7b354%Z)) (ltac:(oD' 0x7b354%Z)). rwH. rewrite art_ann_andim8_up by lia.
zbft (ltac:(oF' 0x7b358%Z)) (ltac:(oD' 0x7b358%Z)).
zstep (ltac:(oF' 0x7b35c%Z)) (ltac:(oD' 0x7b35c%Z)). zstep (ltac:(oF' 0x7b360%Z)) (ltac:(oD' 0x7b360%Z)). zstep (ltac:(oF' 0x7b364%Z)) (ltac:(oD' 0x7b364%Z)). zstep (ltac:(oF' 0x7b368%Z)) (ltac:(oD' 0x7b368%Z)).
apply mst_refl. }
zsplit; try kept_solve.
intros r Hr. unfold art_ann_kept in Hr. destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; kept_solve.
Qed.
End SE.
#[using="Type"] Lemma art_ann_eq0 : ltac2:(TCodec.tc2 tcn__JatAnnotate "Q:&9y5'QNyR0%211%5241'1y8%611%311p061'4&Hr3(QL+C(2%33@21%6251+B%63C14%9281%;3B41'>&L&IvQ6r4+_\aL%?3J1=/01Jr2%75652C1+_\l<%D3O1B/01O%;5:91G5%>3=51p0@1pS8M1pFN1pS4Q41").
Proof. intros regs M rom E. zbtk (ltac:(oF' 0x7b23c%Z)) (ltac:(oD' 0x7b23c%Z)). apply mst_refl. Qed.
#[using="Type"] Lemma art_ann_tail0 : ltac2:(TCodec.tc2 tcn__JatAnnotate "Q:&9y5'QNyR0%211%5241'1y8%611%311p061'4&Hr3(QL+B(2%33@21%6251+9%63C14%9281%;3B41'>&L&IvQ6r4+_\k<%?3J1=/01Jr2%75652C1+_\l<%D3O1B/01O%;5:91G5%>3=51p0@1pS8M1pFN1pS4Q41").
Proof. intros regs M rom E. zbtk (ltac:(oF' 0x7b36c%Z)) (ltac:(oD' 0x7b36c%Z)). apply mst_refl. Qed.
#[using="Type"] Lemma art_ann_epi : ltac2:(TCodec.tc2 tcn__JatAnnotate "UF&9y5'QNyR0%211%5241'1y8%611%311p061'8'4&Hr;(QL+2(2%33A21%6251&QM&Q3r7+RR@%3221%52F1%>3F71&Or8%2261&Q0r9&Q2+QO%22B1%5241&?%11G'3zr:%>221+R0%;2K1%>241%7241&<&LrDrA+8%N221u8&QOrB%22QD1%:598541rE+@%Q6251%>5=318;rFrC+H%Q;221%C5B41=@rG+Q0%Q?2D1%G5F31ADrH+Q8%QC2?1%K5J31EHrI+Q@%QG2?1%O5N31ILrJ+QH%QK2>1%Q35Q231MQ0'5'>&IvQ6rM+_\l<%R93RE1R7/01RErLrK%8576321r1%:591@43%<3Q@31+1%RB3S01R@%RE251%RG3RO1E%RG27RB%RA2S2K%RJ3S221%RH3S6QERF%RK2;1%RE2S6Q3%RN3S621+9%RM3S;1RK%S02@1%RJ2S;Q<%S33S;21+B%S23S@1S0%S52E1%RO2S@QF%S83S@21+C%S73SE1S5%S:2J1%S42SEQO%S=3SE21+D%S<3SJ1S:%S?2O1%S92SJR=%SB3SJ21+E%SA3SO1S?%SD2Q41%S>2SOR4%SG3SO21%T21T3&C%11Q9r3r2%SL221rO%SN213%T03T831p071pRN:1%S92<1%S:2B1%S;2H1%S<2N1%S=2Q41%S>2Q:1%S?2Q?1%S@2QC1%SA2QH1qS6TC1%R72TD1p0R91p0R>1p0RC1p0RH1p0RM1p0S31p0S81p0SD1p0SE1p0SF1p0SG1p0SH1p0SI1p0T21p0T51p0T<1p0T@1pRJU01pRHU11pRFU21pRDU31pRBU41pR@U51pSHU61pS2U>1pS8U91pFU:1pS4U@1").
Proof.
intros regs M rom raw sp0 g16 g24 g32 g40 g48 g56 H2 Hsp Hsp' Hret Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 C8 C16 C24 C32 C40 C48 C56.
eexists. split.
{ zstep (ltac:(oF' 0x7b38c%Z)) (ltac:(oD' 0x7b38c%Z)).
zld (ltac:(oF' 0x7b390%Z)) (ltac:(oD' 0x7b390%Z)) (sp0 - 8) C8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7b394%Z)) (ltac:(oD' 0x7b394%Z)) (sp0 - 16) C16. zld (ltac:(oF' 0x7b398%Z)) (ltac:(oD' 0x7b398%Z)) (sp0 - 24) C24. zld (ltac:(oF' 0x7b39c%Z)) (ltac:(oD' 0x7b39c%Z)) (sp0 - 32) C32.
zld (ltac:(oF' 0x7b3a0%Z)) (ltac:(oD' 0x7b3a0%Z)) (sp0 - 40) C40. zld (ltac:(oF' 0x7b3a4%Z)) (ltac:(oD' 0x7b3a4%Z)) (sp0 - 48) C48. zld (ltac:(oF' 0x7b3a8%Z)) (ltac:(oD' 0x7b3a8%Z)) (sp0 - 56) C56.
zstep (ltac:(oF' 0x7b3ac%Z)) (ltac:(oD' 0x7b3ac%Z)).
stepret (ltac:(oF' 0x7b3b0%Z)) (ltac:(oD' 0x7b3b0%Z)) raw ltac:(rwH; reflexivity).
apply mst_refl. }
zsplit; try kept_solve.
intros r Hr. unfold art_ann_kept in Hr. destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; kept_solve.
Qed.
Section SE.
Local Abbreviation SEC_T_art_ann_kept_poison := (ltac2:(TCodec.tc2 tcn__JatAnnotate ";'QNy5%211&Cr1%211&Gr2%211p041pRN81")) (only parsing).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_ann_kept_poison) 0%nat 0%nat).
Lemma art_ann_kept_poison : ltac:(sec_stmt2 constr:(SEC_T_art_ann_kept_poison) 1%nat 0%nat).
Proof.
intros Hr.
unfold art_ann_kept in Hr. unfold art_poison_kept.
destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; repeat split; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Qed.
End SE.
Lemma art_pf_grows : ltac2:(TCodec.tc2 tcn__JatAnnotate "O'QNyR0%211'1y8%511%311p051'8&Kr9&Fr8r7r6r5r4r3r2r1%99:87654321%<2;1pSD>1pSB?1pS@@1pS>A1pS<B1pS:C1pS0D1pSFE1pFG1").
Proof. intros. unfold art_poison_frame. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. Qed.
Lemma art_ann_mod8 : ltac2:(TCodec.tc2 tcn__JatAnnotate "H'8'4&Q1r2+8%3221z%63721'3&Mr4r3%3221%;219%=3>18&Q3%1265%?21=%A3B1<%;251p0=1p0>1pT8F1pT6G1").
Proof. intros x y Hx Hy. split; [rewrite Z.add_mod by lia|rewrite Zminus_mod]; rewrite Hx, Hy; reflexivity. Qed.
Definition art_ann_lo (b u u' : Z) : Z := b + Z.min u u'.
Definition art_ann_n (u u' : Z) : Z := Z.abs (u - u').
Definition art_ann_v (u u' : Z) : Z := if u <? u' then 0 else 252.
Lemma art_ann_ret_7b36c : ltac2:(TCodec.tc2 tcn__JatAnnotate "6&?&QMyR0+_\k<%3221%511").
Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_art_annotate_run := (ltac2:(TCodec.tc2 tcn__JatAnnotate "Y8&9y5'QNyR0%211%5241'1y8%611%311p061'8'4&Hr9(QL+1(2%33A21%6251r6%93A21&?r7%211r;+2%<3J1:%?231&QM%12K7%C3K31r<+:%C3Q11A%F231%H3Q016r=+;%H3Q61F%K231&Mr8%221D%?2Q91%Q13Q951r>+<%Q13Q?1O%Q4231%92Q4K%F2Q@1%Q83Q@31r?+=%Q83QF1Q6%Q;231r:%A21Q3%N2QH1%Q@3QH41&O+TP0%221Q6&Q1+8%22Q21z%QH3QI21'3%923H%:2IB%3221r@%=2L1%6251rBrA%Q5221&Q2+Q?%22QG1%E241&Q0+Q8%62QK1%32:1'7rDrC%QA221+QoonlP0%O221+`PQoooPP0%Q1216%8231+RT@%QH241rF%Q6221rG+QO%G2R<1%D231&=&LrK&Q3rH%221=%64541>&ErL%211&<rM+QWQWH+S0%R=221u1%65?521S8rN+QVYd8u8+QiYlH%;5D4321rOu4%>5G241QMrQ0&D&N&@rJrI%33G21%521R7%S0271&A%1265%921R;%Q54Q4<41'5'>&IvQ6rQ4+_\Y4%T53TA1T3/01TArQ3rQ2%8576321r2rQ1r1%<5;3215%>3QD51%TA25T<%TC3TK15%TC27T5%T42TNQ0%TF3TN21%TD3U2S2TB%TG2;1%TH2C2%TJ3U221+9%TI3U71TG%TL2@1%TM2H2%TO3U721+B%TN3U<1TL%U12E1%U22M2%U43U<21+C%U33UA1U1%U62J1%U72Q22%U93UA21+D%U83UF1U6%U;2O1%U<2Q72%U>3UF21+E%U=3UK1U;%U@2Q41%UA2Q<2%UC3UK21%UN1UO&C%11Q7r4%UG21Q;rQ6%UI21Q=%UK3V331p061pRN91&K%12QEQ@&6%S22QCS=&QO%12V<QD%TC231%SN22QG%T=221%711%R@3QJRFRK%RB21TD%U=2RD1%92VDQN%TK221%R?2RKS0%RG21TI%UB251%T9251%TH251%B11r3%M11%L12%VF3VI21p051p0A1pT6W11%U92U3R;%RM2S>SD%S521U7%TF2R>1%U5241%V22ERB%V?2W91%>11(0&B%12SBSG%VD2W:1%42W:1%W73W:61p0:1pRLW:1%UA2A1%UB2Q<1%UC2Q?1%UD2QJ1%UE2R01%UF2R61%UG2R<1%UH2RB1%UI2RH1%UJ2RM1%UK2S11%UL2S41qHWH1%SE2WI1qS6WO1%SG2X01p0SI1p0T71p0T;1p0TA1p0TI1p0TM1p0U51p0U:1p0U?1p0UI1p0UN1p0V61p0V:1p0V?1p0V@1p0VA1p0VB1p0VH1p0VL1p0W51p0W=1p0WG1p0WM1p0X51p0X91pT4XD1pT2XE1pR<XF1pR:XG1pSHXH1pS2Y01pS8XK1pFXL1pS4Y21")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 3%nat 0%nat).
Variable sp0 : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 4%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 6%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 7%nat 0%nat).
Variable u' : ltac:(sec_ty2 constr:(SEC_T_art_annotate_run) 8%nat 0%nat).
Theorem art_annotate_run : ltac:(sec_stmt2 constr:(SEC_T_art_annotate_run) 9%nat 0%nat).
Proof using Type regs M rom raw sp0 b c u u'.
intros H1 Hret H2 H10 H11 H12 H13 Hb Hb8 Hc8 Hu8 Hu8' Hu Hu' Hbc Hc40 Hplace Hsp Hsp' W L CF CV CV0 Wsh.
pose proof L as L'. destruct L' as (_ & _ & _ & _ & _ & _ & _ & _ & CG & _).
destruct (art_ann_pre regs M rom raw sp0 b c u u' H1 H2 H10 H11 H12 H13 ltac:(lia) Hbc Hu Hu' Hc40 ltac:(lia) Hsp' W CG CF CV CV0)
as (r1 & RUN1 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & PK).
set (M2 := art_poison_frame M sp0 (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) in *.
assert (GR2 : mem_grows M M2) by (apply art_pf_grows).
assert (FR2 : forall x : word, ~ (sp0 - 56 <= U x < sp0) -> M2 x = M x).
{ intros x Hx. unfold M2, art_poison_frame. rewrite !Wn_outside by (cbn; lia). reflexivity. }
assert (C8 : cellA M2 (sp0 - 8) 8 (U raw)) by (unfold M2, art_poison_frame; zcell).
assert (C16 : cellA M2 (sp0 - 16) 8 (U (getr regs 8))) by (unfold M2, art_poison_frame; zcell).
assert (C24 : cellA M2 (sp0 - 24) 8 (U (getr regs 9))) by (unfold M2, art_poison_frame; zcell).
assert (C32 : cellA M2 (sp0 - 32) 8 (U (getr regs 18))) by (unfold M2, art_poison_frame; zcell).
assert (C40 : cellA M2 (sp0 - 40) 8 (U (getr regs 19))) by (unfold M2, art_poison_frame; zcell).
assert (C48 : cellA M2 (sp0 - 48) 8 (U (getr regs 20))) by (unfold M2, art_poison_frame; zcell).
assert (C56 : cellA M2 (sp0 - 56) 8 (U (getr regs 21))) by (unfold M2, art_poison_frame; zcell).
assert (RG : forall r : reg, 0 <= U (getr regs r) < 2 ^ 64) by (intros r; apply bv_unsigned_in_range).
destruct (Z.lt_trichotomy u u') as [Lt|[Eq|Gt]].
-
destruct (art_ann_grow r1 M2 rom sp0 b c u u' P2 P9 P18 P19 P20 Hb8 Hc8 Hu8 Hu8' ltac:(lia) Hbc ltac:(lia) Lt ltac:(lia))
as (r1' & RUNG & G1 & G2 & G10 & G11 & G12 & G8 & G9 & G18 & GK).
assert (ELo : art_ann_lo b u u' = (b + u)) by (unfold art_ann_lo; rewrite Z.min_l by lia; reflexivity).
assert (En : art_ann_n u u' = (u' - u)) by (unfold art_ann_n; rewrite Z.abs_neq by lia; lia).
assert (Ev : art_ann_v u u' = 0) by (unfold art_ann_v; rewrite (proj2 (Z.ltb_lt u u') Lt); reflexivity).
rewrite ELo, En, Ev in *.
assert (Hp8 : (b + u) mod 8 = 0) by (apply (art_ann_mod8 _ _ Hb8 Hu8)).
assert (Hn8 : (u' - u) mod 8 = 0) by (apply (art_ann_mod8 _ _ Hu8' Hu8)).
assert (L2 : art_layout M2) by (unfold M2, art_poison_frame; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
assert (W2 : wrA M2 (sp0 - 2128 - 64) 64) by (unfold M2, art_poison_frame; repeat apply wr_Wn; eapply wr_sub; [exact W|lia|lia]).
assert (Wsh2 : wrA M2 (SB + (b + u) / 8) ((u' - u) / 8)) by (unfold M2, art_poison_frame; repeat apply wr_Wn; exact Wsh).
assert (PLC : art_poison_lo_okG (b + u) (u' - u) \/ art_poison_hi_okG (b + u) (u' - u)).
{ destruct Hplace as [Lo|Hi]; [left; unfold art_poison_lo_okG, SB|right; unfold art_poison_hi_okG, kHighMemBeg, kHighMemEnd]; lia. }
destruct (art_poison_runG r1' M2 rom (Z_to_bv 64 0x7b36c) (sp0 - 2128) (b + u) (u' - u) 0 G1 art_ann_ret_7b36c G2 G10 G11 G12 ltac:(lia) ltac:(lia) W2
ltac:(unfold apart; lia) ltac:(unfold apart; lia) L2 PLC Hp8 Hn8 ltac:(lia) ltac:(lia)
ltac:(intros _; apply Z.div_lt_upper_bound; lia) Wsh2)
as (r2 & RUNP & Q10 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK).
set (M3 := Wf (art_poison_frame M2 (sp0 - 2128) (U (Z_to_bv 64 0x7b36c)) (U (getr r1' 8)) (U (getr r1' 9)) (U (getr r1' 18)) (U (getr r1' 19)) (U (getr r1' 20)) (U (getr r1' 21)))
(SB + (b + u) / 8) (Z.to_nat ((u' - u) / 8)) 0) in *.
assert (ET : getr r2 18 = getr r2 9) by (rewrite Q18, Q9, G18, G9; reflexivity).
assert (NB : 0 <= SB + (b + u) / 8 /\ SB + (b + u) / 8 + Z.of_nat (Z.to_nat ((u' - u) / 8)) < 2 ^ 64).
{ unfold SB. pose proof (Z.div_pos (b + u) 8 ltac:(lia) ltac:(lia)). assert ((b + u) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
assert ((u' - u) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
assert (APS : forall a k, sp0 - 2192 <= a -> a + k <= sp0 -> 0 <= k -> apart (SB + (b + u) / 8) (Z.of_nat (Z.to_nat ((u' - u) / 8))) a k).
{ intros a k Ha Hk Hk0. unfold apart, SB. rewrite Z2Nat.id by (apply Z.div_pos; lia).
pose proof (Z.div_mod (b + u) 8 ltac:(lia)) as DP. pose proof (Z.div_mod (u' - u) 8 ltac:(lia)) as DN. rewrite Hp8, Z.add_0_r in DP. rewrite Hn8, Z.add_0_r in DN. lia. }
assert (D8 : cellA M3 (sp0 - 8) 8 (U raw)).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D16 : cellA M3 (sp0 - 16) 8 (U (getr regs 8))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D24 : cellA M3 (sp0 - 24) 8 (U (getr regs 9))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D32 : cellA M3 (sp0 - 32) 8 (U (getr regs 18))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D40 : cellA M3 (sp0 - 40) 8 (U (getr regs 19))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D48 : cellA M3 (sp0 - 48) 8 (U (getr regs 20))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D56 : cellA M3 (sp0 - 56) 8 (U (getr regs 21))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
destruct (art_ann_epi r2 M3 rom raw sp0 _ _ _ _ _ _ Q2 ltac:(lia) Hsp' Hret (RG 8%bv) (RG 9%bv) (RG 18%bv) (RG 19%bv) (RG 20%bv) (RG 21%bv) D8 D16 D24 D32 D40 D48 D56)
as (r3 & RUN3 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & EK).
exists r3, M3. split.
{ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNG|]. eapply msteps_trans; [exact RUNP|].
replace (Z_to_bv 64 0x7b36c) with (0x7b36c%bv : word) by (apply bv_eq; vm_compute; reflexivity).
eapply msteps_trans; [exact (art_ann_tail0 r2 M3 rom ET)|exact RUN3]. }
rewrite !Z_to_bv_bv_unsigned in E8, E9, E18, E19, E20, E21.
split; [exact E1|]. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E19|]. split; [exact E20|]. split; [exact E21|].
split; [intros r Hr; rewrite (EK r Hr), (QK r (art_ann_kept_poison r Hr)), (GK r Hr); exact (PK r Hr)|].
split. { eapply mem_grows_trans; [exact GR2|]. unfold M3. eapply mem_grows_trans; [|apply Wf_grows]. apply art_pf_grows. }
split. { intros x Hx Hy. unfold M3. rewrite Wf_outside by (try rewrite Z2Nat.id by (apply Z.div_pos; lia); lia).
unfold art_poison_frame. rewrite !Wn_outside by (cbn; lia). apply FR2. lia. }
intros i Hi. unfold M3. apply Wf_inside; [lia|lia|rewrite Z2Nat.id by (apply Z.div_pos; lia); lia].
-
subst u'.
assert (E19 : getr r1 19 = getr r1 18) by (rewrite P18, P19; reflexivity).
destruct (art_ann_epi r1 M2 rom raw sp0 _ _ _ _ _ _ P2 ltac:(lia) Hsp' Hret (RG 8%bv) (RG 9%bv) (RG 18%bv) (RG 19%bv) (RG 20%bv) (RG 21%bv) C8 C16 C24 C32 C40 C48 C56)
as (r3 & RUN3 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK).
exists r3, M2. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact (art_ann_eq0 r1 M2 rom E19)|exact RUN3]|].
rewrite !Z_to_bv_bv_unsigned in Q8, Q9, Q18, Q19, Q20, Q21.
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|].
split; [intros r Hr; rewrite (QK r Hr); exact (PK r Hr)|]. split; [exact GR2|].
split; [intros x Hx _; apply FR2; lia|]. intros i Hi. unfold art_ann_n in Hi. rewrite Z.sub_diag in Hi. cbn in Hi. lia.
-
destruct (art_ann_shrink r1 M2 rom sp0 b c u u' P2 P9 P18 P19 P20 Hb8 Hc8 Hu8 Hu8' ltac:(lia) Hbc ltac:(lia) Gt ltac:(lia))
as (r1' & RUNG & G1 & G2 & G10 & G11 & G12 & G8 & G9 & G18 & GK).
assert (ELo : art_ann_lo b u u' = (b + u')) by (unfold art_ann_lo; rewrite Z.min_r by lia; reflexivity).
assert (En : art_ann_n u u' = (u - u')) by (unfold art_ann_n; rewrite Z.abs_eq by lia; lia).
assert (Ev : art_ann_v u u' = 252) by (unfold art_ann_v; rewrite (proj2 (Z.ltb_ge u u') ltac:(lia)); reflexivity).
rewrite ELo, En, Ev in *.
assert (Hp8 : (b + u') mod 8 = 0) by (apply (art_ann_mod8 _ _ Hb8 Hu8')).
assert (Hn8 : (u - u') mod 8 = 0) by (apply (art_ann_mod8 _ _ Hu8 Hu8')).
assert (L2 : art_layout M2) by (unfold M2, art_poison_frame; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
assert (W2 : wrA M2 (sp0 - 2128 - 64) 64) by (unfold M2, art_poison_frame; repeat apply wr_Wn; eapply wr_sub; [exact W|lia|lia]).
assert (Wsh2 : wrA M2 (SB + (b + u') / 8) ((u - u') / 8)) by (unfold M2, art_poison_frame; repeat apply wr_Wn; exact Wsh).
assert (PLC : art_poison_lo_okG (b + u') (u - u') \/ art_poison_hi_okG (b + u') (u - u')).
{ destruct Hplace as [Lo|Hi]; [left; unfold art_poison_lo_okG, SB|right; unfold art_poison_hi_okG, kHighMemBeg, kHighMemEnd]; lia. }
destruct (art_poison_runG r1' M2 rom (Z_to_bv 64 0x7b36c) (sp0 - 2128) (b + u') (u - u') 252 G1 art_ann_ret_7b36c G2 G10 G11 G12 ltac:(lia) ltac:(lia) W2
ltac:(unfold apart; lia) ltac:(unfold apart; lia) L2 PLC Hp8 Hn8 ltac:(lia) ltac:(lia)
ltac:(intros _; apply Z.div_lt_upper_bound; lia) Wsh2)
as (r2 & RUNP & Q10 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK).
set (M3 := Wf (art_poison_frame M2 (sp0 - 2128) (U (Z_to_bv 64 0x7b36c)) (U (getr r1' 8)) (U (getr r1' 9)) (U (getr r1' 18)) (U (getr r1' 19)) (U (getr r1' 20)) (U (getr r1' 21)))
(SB + (b + u') / 8) (Z.to_nat ((u - u') / 8)) 252) in *.
assert (ET : getr r2 18 = getr r2 9) by (rewrite Q18, Q9, G18, G9; reflexivity).
assert (NB : 0 <= SB + (b + u') / 8 /\ SB + (b + u') / 8 + Z.of_nat (Z.to_nat ((u - u') / 8)) < 2 ^ 64).
{ unfold SB. pose proof (Z.div_pos (b + u') 8 ltac:(lia) ltac:(lia)). assert ((b + u') / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
assert ((u - u') / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
assert (APS : forall a k, sp0 - 2192 <= a -> a + k <= sp0 -> 0 <= k -> apart (SB + (b + u') / 8) (Z.of_nat (Z.to_nat ((u - u') / 8))) a k).
{ intros a k Ha Hk Hk0. unfold apart, SB. rewrite Z2Nat.id by (apply Z.div_pos; lia).
pose proof (Z.div_mod (b + u') 8 ltac:(lia)) as DP. pose proof (Z.div_mod (u - u') 8 ltac:(lia)) as DN. rewrite Hp8, Z.add_0_r in DP. rewrite Hn8, Z.add_0_r in DN. lia. }
assert (D8 : cellA M3 (sp0 - 8) 8 (U raw)).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D16 : cellA M3 (sp0 - 16) 8 (U (getr regs 8))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D24 : cellA M3 (sp0 - 24) 8 (U (getr regs 9))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D32 : cellA M3 (sp0 - 32) 8 (U (getr regs 18))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D40 : cellA M3 (sp0 - 40) 8 (U (getr regs 19))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D48 : cellA M3 (sp0 - 48) 8 (U (getr regs 20))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
assert (D56 : cellA M3 (sp0 - 56) 8 (U (getr regs 21))).
{ unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
destruct (art_ann_epi r2 M3 rom raw sp0 _ _ _ _ _ _ Q2 ltac:(lia) Hsp' Hret (RG 8%bv) (RG 9%bv) (RG 18%bv) (RG 19%bv) (RG 20%bv) (RG 21%bv) D8 D16 D24 D32 D40 D48 D56)
as (r3 & RUN3 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & EK).
exists r3, M3. split.
{ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNG|]. eapply msteps_trans; [exact RUNP|].
replace (Z_to_bv 64 0x7b36c) with (0x7b36c%bv : word) by (apply bv_eq; vm_compute; reflexivity).
eapply msteps_trans; [exact (art_ann_tail0 r2 M3 rom ET)|exact RUN3]. }
rewrite !Z_to_bv_bv_unsigned in E8, E9, E18, E19, E20, E21.
split; [exact E1|]. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E19|]. split; [exact E20|]. split; [exact E21|].
split; [intros r Hr; rewrite (EK r Hr), (QK r (art_ann_kept_poison r Hr)), (GK r Hr); exact (PK r Hr)|].
split. { eapply mem_grows_trans; [exact GR2|]. unfold M3. eapply mem_grows_trans; [|apply Wf_grows]. apply art_pf_grows. }
split. { intros x Hx Hy. unfold M3. rewrite Wf_outside by (try rewrite Z2Nat.id by (apply Z.div_pos; lia); lia).
unfold art_poison_frame. rewrite !Wn_outside by (cbn; lia). apply FR2. lia. }
intros i Hi. unfold M3. apply Wf_inside; [lia|lia|rewrite Z2Nat.id by (apply Z.div_pos; lia); lia].
Qed.
End SE.
End FPX.
