(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Js0StdioDefs Js0StdioWrite_run1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0StdioWrite_run2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite_run2.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1list"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4store_ok"; "4word_to_le_bytes"; "5bvmap"; "6wbytes"; "7msteps"]; ["8ret_ok"; "9mem_sw2"; "9sw_regs_but"; ":getr"; ":mkst"; ":rdn"; ";loaded_segments"; "<add"; "<le"; "<lt"; "<pow"; "<sub"; "0b0"; "0b1"; "0bufp"; "0bufsz"]; ["0can"; "0cnt"; "0f"; "0fd"; "0fx"; "0ic"; "0io"; "0k"; "0l"; "0mem"; "0n0"; "0n1"; "0regs"; "0regs'"; "0rem"; "0ret"]; ["0rom"; "0s0v"; "0s1v"; "0s2v"; "0s3v"; "0s4v"; "0s5v"; "0s6v"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0su"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
/\ getr regs' 21 = getr regs 21
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Section SE.
Local Abbreviation SEC_T_sw_c1_eq := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run2 "RO&=y5'QJyR0%211%5241'3y8%611%311p061':'7&Cr4(QH+:(5%33A21%6251&QIr1%22C1%;3C41r5+F%;3I19%>231r2%92J1%B3J31'6&Hzr3%3221&I+RPPPPP0%2241%8241'8'?&F&DvQ4r8+cgV4%Q03Q<1N/01Q<r7r6%8576321+cgV<%Q63QB1Q4/01QB%<5;Q2165%?3>51%Q<2Q4Q7%Q62QGQ2%Q?3QG21+C%Q>3QL1Q<%QA2Q91%QB2B2%QD3QL21+D%QC3R11QA%QF2Q>1%QG2G2%QI3R121+B%QH3R61QF%QK2QC1%QL2L2%QN3R621%QN2QFQA%QO2OQB%R13R921&B%12Q2QJ%QA231%QB271%QC2=1%QD2C1%QE2I1%QF2M1qRLRA1%Q?2RB1p0QA1p0QK1p0R31pR@R@1pS2RB1pRDRC1pRJRI1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sw_c1_eq) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_sw_c1_eq) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sw_c1_eq) 2%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_sw_c1_eq) 3%nat 0%nat).
Lemma sw_c1_eq : ltac:(sec_stmt2 constr:(SEC_T_sw_c1_eq) 4%nat 0%nat).
Proof.
intros Ha0 Hs6 K.
eexists. split.
- stepn (ltac:(oF' 0x9dcc4%Z)) (ltac:(oD' 0x9dcc4%Z)).
stepn (ltac:(oF' 0x98c90%Z)) (ltac:(oD' 0x98c90%Z)).
stepn (ltac:(oF' 0x98c94%Z)) (ltac:(oD' 0x98c94%Z)).
stepb_tk (ltac:(oF' 0x98c98%Z)) (ltac:(oD' 0x98c98%Z)) ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret (ltac:(oF' 0x98cc4%Z)) (ltac:(oD' 0x98cc4%Z)) (0x9dcc8 : word) ltac:(bveq).
stepb_ft (ltac:(oF' 0x9dcc8%Z)) (ltac:(oD' 0x9dcc8%Z)) ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.
End SE.
Lemma sw_c1_ne : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run2 "S;&=y5'QJyR0%211%5241'3y8%611%311p061':'7&Cr5(QH+:(5%33A21%6251&QIr2%22C1%;3C41r6+F%;3I19%>231%@3H16'6&Hzr4%3221&I+RPPPPP0%2241%8241&J+2+R0%3221%82:1%>2:1&9%Q13Q2EO%211'8'?&F&DvQ4r;+cgV4%Q73QC1Q5/01QCr:r9%8576321r1+cgZH%Q>3QJ1Q</01QJ%=5<4176%@3?61%QD26Q?r8%Q?2R01%QH3R031+C%QG3R51QE%QJ2<1%QK2D2%QM3R521+D%QL3R:1QJ%QO2A1%R02I2%R23R:21+B%R13R?1QO%R42F1%R52N2%R73R?21%R72IQJ%R82Q1QK%R:3RB21&B%12Q4M%QL231%QM271%QN2=1%QO2C1%R02I1%R12N1qRLRJ1%QA2RK1p0QC1p0QG1p0QN1p0R81p0R>1pRNRK1pR@RL1pS2RN1pRDRO1pRJS51").
Proof.
intros regs mem rom k rem Ha0 Hs6 K REM NE.
eexists. split.
- stepn (ltac:(oF' 0x9dcc4%Z)) (ltac:(oD' 0x9dcc4%Z)).
stepn (ltac:(oF' 0x98c90%Z)) (ltac:(oD' 0x98c90%Z)).
stepn (ltac:(oF' 0x98c94%Z)) (ltac:(oD' 0x98c94%Z)).
stepb_tk (ltac:(oF' 0x98c98%Z)) (ltac:(oD' 0x98c98%Z)) ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret (ltac:(oF' 0x98cc4%Z)) (ltac:(oD' 0x98cc4%Z)) (0x9dcc8 : word) ltac:(bveq).
stepb_tk (ltac:(oF' 0x9dcc8%Z)) (ltac:(oD' 0x9dcc8%Z)) ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.
Lemma sw_c2_eq : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run2 "RN&=y5'QJyR0%211%5241'3y8%611%311p061':'7&Cr4(QH+:(5%33A21%6251&QIr1%22C1%;3C41r5+F%;3I19%>231r2%92J1%B3J31'6&Hzr3%3221&I+RPPPPP0%2241%8241'8'?&F&DvQ4r8+cgZ<%Q03Q<1N/01Q<r7r6%8576321+cgV<%Q63QB1Q4/01QB%<5;Q2165%?3>51%Q<2Q4Q7%Q62QGQ2%Q?3QG21+C%Q>3QL1Q<%QA2Q91+D%QA3QO1Q?%QD2D1%QF3QN41%QF2Q>3%QH3R013+B%QG3R51QE%QJ2QB1%QK2K2%QM3R521%QM2QEQ@%QN2NQA%R03R821&B%12Q1QI%Q@231%QA271%QB2=1%QC2@1%QD2H1%QE2L1qRLR@1%Q>2RA1p0Q@1p0QJ1p0R21pR@R?1pS2RA1pRDRB1pRJRH1").
Proof.
intros regs mem rom k Ha0 Hs6 K.
eexists. split.
- stepn (ltac:(oF' 0x9dd4c%Z)) (ltac:(oD' 0x9dd4c%Z)).
stepn (ltac:(oF' 0x98c90%Z)) (ltac:(oD' 0x98c90%Z)).
stepn (ltac:(oF' 0x98c94%Z)) (ltac:(oD' 0x98c94%Z)).
stepb_tk (ltac:(oF' 0x98c98%Z)) (ltac:(oD' 0x98c98%Z)) ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret (ltac:(oF' 0x98cc4%Z)) (ltac:(oD' 0x98cc4%Z)) (0x9dd50 : word) ltac:(bveq).
stepn (ltac:(oF' 0x9dd50%Z)) (ltac:(oD' 0x9dd50%Z)).
stepb_tk (ltac:(oF' 0x9dd54%Z)) (ltac:(oD' 0x9dd54%Z)) ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.
Lemma sw_c2_ne : ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run2 "S:&=y5'QJyR0%211%5241'3y8%611%311p061':'7&Cr5(QH+:(5%33A21%6251&QIr2%22C1%;3C41r6+F%;3I19%>231%@3H16'6&Hzr4%3221&I+RPPPPP0%2241%8241&J+2+R0%3221%82:1%>2:1&9%Q13Q2EO%211'8'?&F&DvQ4r;+cgZ<%Q73QC1Q5/01QCr:r9%8576321r1+cgZH%Q>3QJ1Q</01QJ%=5<4176%@3?61%QD26Q?r8%Q?2R01%QH3R031+C%QG3R51QE%QJ2<1+D%QJ3R81QH%QM2F1%QO3R741%QO2A3%R13R913+B%R03R>1QN%R32E1%R42M2%R63R>21%R62HQI%R72Q0QJ%R93RA21&B%12Q3L%QK231%QL271%QM2=1%QN2@1%QO2H1%R02M1qRLRI1%Q@2RJ1p0QB1p0QF1p0QM1p0R71p0R=1pRNRJ1pR@RK1pS2RM1pRDRN1pRJS41").
Proof.
intros regs mem rom k rem Ha0 Hs6 K REM NE.
eexists. split.
- stepn (ltac:(oF' 0x9dd4c%Z)) (ltac:(oD' 0x9dd4c%Z)).
stepn (ltac:(oF' 0x98c90%Z)) (ltac:(oD' 0x98c90%Z)).
stepn (ltac:(oF' 0x98c94%Z)) (ltac:(oD' 0x98c94%Z)).
stepb_tk (ltac:(oF' 0x98c98%Z)) (ltac:(oD' 0x98c98%Z)) ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret (ltac:(oF' 0x98cc4%Z)) (ltac:(oD' 0x98cc4%Z)) (0x9dd50 : word) ltac:(bveq).
stepn (ltac:(oF' 0x9dd50%Z)) (ltac:(oD' 0x9dd50%Z)).
stepb_ft (ltac:(oF' 0x9dd54%Z)) (ltac:(oD' 0x9dd54%Z)) ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.
Section SE.
Local Abbreviation SEC_T_sw_retry_a := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run2 "X6&=y5'QJyR0%211%5241'3y8%611%311p061':'7&Cr<(QH+:(5%33A21%6251&QIr4%22C1%;3C41r=+C%;3I19%>231r7%92J1%B3J31r>+B%B3Q01@%E231%G3O16r?+F%G3Q51E%J231r5%E2Q61%N3Q631r@+9%N3Q<1L%Q1231%K2Q<Q1%Q43Q<21rA+2%Q43QB1Q2%Q7231&K+S@%22H1%Q42QE1%Q=3QE51&H&G+TPPPPP0%2217%421J+TPPPPPPPP0%62E1+fdP0%821G+W8%92C1+lof@%<221rC+S8%D221%@21O+@%A2K1rD+R8%J221%F241'6+1%I21Q2%J2Q3Q2%4221%L2Q5Q;%6241&I&J+QN%22Q91%42Q;1%Q32FQ<rB%7214&QK%12RN3%Q721E+R0%;2QB1%Q;231'1&;&FrMrK%QF21QE%RH2S91uS@%746521(4%S43:21'2%11S:%S=11&ErNrI%S32SD1u8%54A421(0&<%124Q?%32;1%SB3;51rOrJ+8%R7221%S?2T01%@4L51<rG%SB2T31%<2?1%>2F1%SM3F51rQ0+SH%RA2Q31%SI2T:1u4%K4Q7521rL%SM2T>1%G241%I2Q11%T83Q151z%QN21Q=+RPPPPP0%R02Q?1%R8231'8'?&DvQ4rQ4+cgZH%TA3TM1T?/01TMrQ3rQ2%8576321r1+cgZ8%TH3U41TF/01U4&>%TF2U7QE%R;2U8QE%SA21L%TI2U:1%QC2QF1%63=51%SE2QKQ?%TM2U>1%SM2R8Q2%TO2U@1%QI2QL1%<3641%J5IA>1C%L3R?C1+A%U:3UH1U8%U=2E1+R2%U82UI1%UA3UI31%UA2IU<%U;2ULR0%UD3UL21+;%UC3V11UA%UF2N1%UH3V01J+<%UG3V51UE%UJ2Q21%UD2V5RO%UM3V521%UM2Q5U9%UO3V713%UO2Q7UB%V13V91Q3+D%V03V>1UN%V32Q;1%V53V=1Q7%V52Q=U<%TN2RCR3%V02VA1%V93VA31&B%12QIQB%T7231%T8281%T92=1%T:2@1%T;2C1%T<2I1%T=2N1%T>2Q21%T?2Q91qRLVL1%R82VM1p0R:1p0R@1p0RL1p0S81p0SG1p0T31p0T:1p0T=1p0T?1p0TE1p0TH1p0TN1p0U51p0U:1p0U?1p0UB1p0UE1p0UK1p0V51p0V<1p0VD1p0VJ1p0W21pQJWF1pRNW@1pRFWA1pR4WB1pR<WC1pR>WD1pR8WE1pR6WF1pSJWG1pS2WI1pRDWJ1pRJX01")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 2%nat 0%nat).
Variable su : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 3%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 4%nat 0%nat).
Variable fd : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 5%nat 0%nat).
Variable io : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 6%nat 0%nat).
Variable ic : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 7%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 8%nat 0%nat).
Variable n0 : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 9%nat 0%nat).
Variable rem : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 10%nat 0%nat).
Variable b0 : ltac:(sec_ty2 constr:(SEC_T_sw_retry_a) 11%nat 0%nat).
Lemma sw_retry_a : ltac:(sec_stmt2 constr:(SEC_T_sw_retry_a) 12%nat 0%nat).
Proof.
intros
Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
pose proof (u64_range b0) as Hb0.
eexists. split.
-
stepb_ft (ltac:(oF' 0x9dd58%Z)) (ltac:(oD' 0x9dd58%Z)) ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
stepLD8 (ltac:(oF' 0x9dd5c%Z)) (ltac:(oD' 0x9dd5c%Z)) (Z_to_bv 64 n0).
stepn (ltac:(oF' 0x9dd60%Z)) (ltac:(oD' 0x9dd60%Z)). rewrite Ha0, (sltu_ge n0 cnt) by lia.
stepn (ltac:(oF' 0x9dd64%Z)) (ltac:(oD' 0x9dd64%Z)).
stepn (ltac:(oF' 0x9dd68%Z)) (ltac:(oD' 0x9dd68%Z)). rewrite Hs3.
stepLD8 (ltac:(oF' 0x9dd6c%Z)) (ltac:(oD' 0x9dd6c%Z)) b0.
stepn (ltac:(oF' 0x9dd70%Z)) (ltac:(oD' 0x9dd70%Z)).
stepn (ltac:(oF' 0x9dd74%Z)) (ltac:(oD' 0x9dd74%Z)). rewrite v_and_0_l.
stepn (ltac:(oF' 0x9dd78%Z)) (ltac:(oD' 0x9dd78%Z)). rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.
stepn (ltac:(oF' 0x9dd7c%Z)) (ltac:(oD' 0x9dd7c%Z)). rewrite (v_add_wZ b0 cnt) by lia.
stepST (ltac:(oF' 0x9dd80%Z)) (ltac:(oD' 0x9dd80%Z)) (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).
stepb_tk (ltac:(oF' 0x9dd84%Z)) (ltac:(oD' 0x9dd84%Z)) ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).
stepn (ltac:(oF' 0x9dd1c%Z)) (ltac:(oD' 0x9dd1c%Z)).
stepn (ltac:(oF' 0x9dd20%Z)) (ltac:(oD' 0x9dd20%Z)).
stepn (ltac:(oF' 0x9dd24%Z)) (ltac:(oD' 0x9dd24%Z)). rewrite Hs3, (v_add_ZZ' io 8) by lia.
stepLD8 (ltac:(oF' 0x9dd28%Z)) (ltac:(oD' 0x9dd28%Z)) (Z_to_bv 64 n0).
stepn (ltac:(oF' 0x9dd2c%Z)) (ltac:(oD' 0x9dd2c%Z)). rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
stepLD (ltac:(oF' 0x9dd30%Z)) (ltac:(oD' 0x9dd30%Z)) (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn (ltac:(oF' 0x9dd34%Z)) (ltac:(oD' 0x9dd34%Z)). rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.
stepn (ltac:(oF' 0x9dd38%Z)) (ltac:(oD' 0x9dd38%Z)). rewrite (v_sub_Z n0 cnt) by lia.
stepST (ltac:(oF' 0x9dd3c%Z)) (ltac:(oD' 0x9dd3c%Z)) (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).
stepn (ltac:(oF' 0x9dd40%Z)) (ltac:(oD' 0x9dd40%Z)).
stepn (ltac:(oF' 0x9dd44%Z)) (ltac:(oD' 0x9dd44%Z)).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_sw_retry_b := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run2 "XF&=y5'QJyR0%211%5241'3y8%611%311p061':'7&Cr<(QH+:(5%33A21%6251&QIr5%22C1%;3C41r=+C%;3I19%>231r7%92J1%B3J31r>+B%B3Q01@%E231+2%@2Q11%I3Q131r?+F%I3Q71G%L231%N3Q61Dr@+9%N3Q<1L%Q1231%K2Q<Q1%Q43Q<21rA%Q33QA?Q1%Q6221&K+S@%22G1%Q32QD1%Q<3QD51&H&G+TPPPPP0%2217%421G+TPPPPPPPP0%62D1+fdP0%821F+W8%92B1+lof@%<221rC+S8%D221%@21N+Q0%A2J1rD+R8%J221%F241'6z%I21Q7&I%12Q9Q3%5231rB%N21QA&J+QN%22QG1%82Q@1%Q82@F%Q4217%;2H4&QK%12RM:%Q721E+R0%;2R01%Q;231'1&;&FrMrK%QF21QE%RG2S81uS@%746521(4%S33:21'2%11S9%S<11&ErNrI+8%QM221%S42SE1u8%74C621(0&<rG%S:2SK1%3261%52?1%SE3?71rOrJ+@%R;221%SB2T31%D4Q051>rE%=2@1%?2I1%SO3I41rQ0+H%RD2Q51%SK2T<1%M4Q941GrH%SN2T?1%G2J1%I2Q31%T93Q351rQ1+SH%RN2Q41%T52TF1u4%Q84QD521%T82TIQD%Q1231%Q32Q=1%TC3Q=41%R=2R?Q<+RPPPPP0%R?2Q>1%RC231'8'?&DvQ4rQ5+cgZH%TK3U71TI/01U7rQ4rQ3%8576321r1+cgZ8%U23U>1U0/01U>&>%SJ2QBQ@%U12UB1%RG2UCQC%T32R3R?%SN221%U52UF1%QN2R11%83?61%T22QJQ?%U92UJ1rL%T;218%U<2UM1%R52R81%?3751%M5LDA1F%O3RMF1+A%UG3V51UE%UJ2H1+R2%UE2V61%UN3V631%UN2LUI%UH2V9R0%V13V921+;%V03V>1UN%V32Q11%V53V=1L+<%V43VB1V2%V72Q51+1%V22VC1%V;3VC31%V;2Q9UG%V=3VE13%V=2Q;V0%V72VHRI%V@3VH21+D%V?3VM1V=%VB2Q@1%VD3VL1Q;%VD2QBUI%U>2SIS>%V?2W01%VH3W031&B%12QNQG%TG231%TH281%TI2=1%TJ2A1%TK2D1%TL2K1%TM2Q01%TN2Q41%TO2Q;1qRLW;1%R=2W<1p0R?1p0RD1p0RO1p0S:1p0SE1p0T81p0TD1p0TK1p0TM1p0U01p0U51p0U81p0U?1p0UF1p0UK1p0V01p0V31p0V61p0V<1p0VE1p0VL1p0W21p0W:1p0WB1pQLX61pRNX01pRHX11pRFX21pR4X31pR>X41pR8X51pR6X61pSJX71pS2X91pRDX:1pRJX@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 2%nat 0%nat).
Variable su : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 3%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 4%nat 0%nat).
Variable fd : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 5%nat 0%nat).
Variable io : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 6%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 7%nat 0%nat).
Variable n0 : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 8%nat 0%nat).
Variable n1 : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 9%nat 0%nat).
Variable rem : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 10%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_sw_retry_b) 11%nat 0%nat).
Lemma sw_retry_b : ltac:(sec_stmt2 constr:(SEC_T_sw_retry_b) 12%nat 0%nat).
Proof.
intros
Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
pose proof (u64_range b1) as Hb1.
eexists. split.
-
stepb_ft (ltac:(oF' 0x9dd58%Z)) (ltac:(oD' 0x9dd58%Z)) ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
stepLD8 (ltac:(oF' 0x9dd5c%Z)) (ltac:(oD' 0x9dd5c%Z)) (Z_to_bv 64 n0).
stepn (ltac:(oF' 0x9dd60%Z)) (ltac:(oD' 0x9dd60%Z)). rewrite Ha0, (sltu_lt n0 cnt) by lia.
stepn (ltac:(oF' 0x9dd64%Z)) (ltac:(oD' 0x9dd64%Z)).
stepn (ltac:(oF' 0x9dd68%Z)) (ltac:(oD' 0x9dd68%Z)). rewrite Hs3, (v_add_ZZ' io 16) by lia.
stepLD8 (ltac:(oF' 0x9dd6c%Z)) (ltac:(oD' 0x9dd6c%Z)) b1.
stepn (ltac:(oF' 0x9dd70%Z)) (ltac:(oD' 0x9dd70%Z)).
stepn (ltac:(oF' 0x9dd74%Z)) (ltac:(oD' 0x9dd74%Z)). rewrite (v_and_m1_l n0) by lia.
stepn (ltac:(oF' 0x9dd78%Z)) (ltac:(oD' 0x9dd78%Z)). rewrite Ha0, (v_sub_Z cnt n0) by lia.
stepn (ltac:(oF' 0x9dd7c%Z)) (ltac:(oD' 0x9dd7c%Z)). rewrite (v_add_wZ b1 (cnt - n0)) by lia.
stepST (ltac:(oF' 0x9dd80%Z)) (ltac:(oD' 0x9dd80%Z)) (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).
stepb_ft (ltac:(oF' 0x9dd84%Z)) (ltac:(oD' 0x9dd84%Z)) ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).
stepn (ltac:(oF' 0x9dd88%Z)) (ltac:(oD' 0x9dd88%Z)).
stepn (ltac:(oF' 0x9dd8c%Z)) (ltac:(oD' 0x9dd8c%Z)).
stepn (ltac:(oF' 0x9dd20%Z)) (ltac:(oD' 0x9dd20%Z)).
stepn (ltac:(oF' 0x9dd24%Z)) (ltac:(oD' 0x9dd24%Z)). rewrite Hs3, (v_add_ZZ' io 24) by lia.
stepLD8 (ltac:(oF' 0x9dd28%Z)) (ltac:(oD' 0x9dd28%Z)) (Z_to_bv 64 n1).
stepn (ltac:(oF' 0x9dd2c%Z)) (ltac:(oD' 0x9dd2c%Z)). rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
stepLD (ltac:(oF' 0x9dd30%Z)) (ltac:(oD' 0x9dd30%Z)) (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn (ltac:(oF' 0x9dd34%Z)) (ltac:(oD' 0x9dd34%Z)). rewrite Hs2. vals_lit.
stepn (ltac:(oF' 0x9dd38%Z)) (ltac:(oD' 0x9dd38%Z)). rewrite (v_sub_Z n1 (cnt - n0)) by lia.
stepST (ltac:(oF' 0x9dd3c%Z)) (ltac:(oD' 0x9dd3c%Z)) (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).
stepn (ltac:(oF' 0x9dd40%Z)) (ltac:(oD' 0x9dd40%Z)).
stepn (ltac:(oF' 0x9dd44%Z)) (ltac:(oD' 0x9dd44%Z)).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.
End SE.
Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
wbytes (wbytes (wbytes mem1
(Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
(Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
(Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).
Section SE.
Local Abbreviation SEC_T_sw_done := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite_run2 "Y1&=y5'QJyR0%211%5241'3y8%611%311p061':'7&CrA(QH+2(5%33A21%6251&QI&Kr>+S@%3221%52F1%>3F71rB+8%>3L1<%A231r=%D3L21rC+9%D3Q21B%G231r?%B2Q31%K3Q331rD+E%K3Q91I%N231+lof@%I2Q:1%Q23Q:31&H&G+TPPPPP0%221K%421H+TPPPPPPPP0%62D1+fdP0%821F+W8%92A1%;21>&@r@%211'2%11QG%QJ11&E&FrIrG%Q@21Q9%QB2R31u8%746521(0&<%124QM%32=1%R13=51rJrH+@%QL221%QN2R?1%B4A51<%R83D18rK+H%R22D1%R42RE1%H4G41B%R>3J1>rL+Q0%R82?1%R:2RK1%N4M41H%RD3Q01DrM+Q8%R>2>1%R@2S11%Q44Q341N%RJ3Q61JrN+Q@%RD2>1%RF2S71%Q:4Q941Q4%S03Q<1Q0rO+QH%RJ2>1%RL2S=1%Q@4Q?41Q:%S63QB1Q6rQ0+R0%S02>1%S22SC1%QF4QE41Q@%S<3QH1Q<rQ1+R8%S62>1%S82SI1%QL4QK41QF%QD2QGQ@%QF2R01%SD3R031rQ2%R14R01REQK%QI2QLQ>%QK2R51%SI3R531rQ3+RH%RH2E1%SE2T61%R94R841R3%R12R4Q4%R32R=1%T13R=31rQ4+S0%S02G1%SM2T>1%RA4R@41R;%T73RC17'8'6'?&DvQ4rQ7+cgV<%T<3TH1T:/01THrQ6rQ5%8576321r1&A%145LQ9Q?%<5;3QL15%>3S251+:%TG3U51TE%TJ271%TL3U41Q7%TL29TG%TF2U7L%TO3U721+1%TN3U<1TL%U12>1%U33U;1R8%U32@TC%U53U=1R@%U52BT?%U73U?1RH+B%U63UD1U4%U92F1%U;3UC1S2+C%U:3UH1U8%U=2J1%U?3UG1S=+D%U>3UL1U<%UA2N1%UC3UK1SL%UC2Q0TF%UE3UM1SB+F%UD3V21UB%UG2Q41%UI3V11T1+3%UH3V61UF%UK2Q81%UL2Q@2%UN3V621+4%UM3V;1UK%V02Q=1%V12QE2%V33V;21+G%V23V@1V0%V52QB1%V62QJ2%V83V@21%V63VDSOV4%V92QF1%V:2QN2%V<3VD21+I%V;3VI1V9%V>2QK1%V?2R32%VA3VI21+J%V@3VN1V>%VC2R01%VD2R82%VF3VN21+K%VE3W31VC%VH2R51%VI2R=2%VK3W321%RC261%RD2<1%RE2B1%RF2G1%RG2M1%RH2Q31%RI2Q91%RJ2Q>1%RK2QA1%RL2QF1%RM2QK1%RN2R01%RO2R31%S02R61%S12R;1%S22R?1%S32RD1qRLWD1%S62WE1p0S81p0S?1p0SH1p0SN1p0T71p0T>1p0TE1p0TL1p0U31p0U:1p0UA1p0UI1p0V:1p0V>1p0VB1p0VE1p0VH1p0VN1p0W61p0W>1p0WE1pS@X<1pS>X=1pS<X>1pS:X?1pS8X@1pS6XA1pS4XB1pS0XC1pR2XD1pR0XE1pQNXF1pRBXG1pR6XA1pSJXB1pS2XD1pRDXE1pRJXK1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sw_done) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_sw_done) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sw_done) 2%nat 0%nat).
Variable su : ltac:(sec_ty2 constr:(SEC_T_sw_done) 3%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_sw_done) 4%nat 0%nat).
Variable l : ltac:(sec_ty2 constr:(SEC_T_sw_done) 5%nat 0%nat).
Variable bufp : ltac:(sec_ty2 constr:(SEC_T_sw_done) 6%nat 0%nat).
Variable bufsz : ltac:(sec_ty2 constr:(SEC_T_sw_done) 7%nat 0%nat).
Variable can : ltac:(sec_ty2 constr:(SEC_T_sw_done) 8%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_sw_done) 9%nat 0%nat).
Variable s0v : ltac:(sec_ty2 constr:(SEC_T_sw_done) 10%nat 0%nat).
Variable s1v : ltac:(sec_ty2 constr:(SEC_T_sw_done) 11%nat 0%nat).
Variable s2v : ltac:(sec_ty2 constr:(SEC_T_sw_done) 12%nat 0%nat).
Variable s3v : ltac:(sec_ty2 constr:(SEC_T_sw_done) 13%nat 0%nat).
Variable s4v : ltac:(sec_ty2 constr:(SEC_T_sw_done) 14%nat 0%nat).
Variable s5v : ltac:(sec_ty2 constr:(SEC_T_sw_done) 15%nat 0%nat).
Variable s6v : ltac:(sec_ty2 constr:(SEC_T_sw_done) 16%nat 0%nat).
Lemma sw_done : ltac:(sec_stmt2 constr:(SEC_T_sw_done) 17%nat 0%nat).
Proof.
intros
Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
unfold mem_sw2. eexists. split.
-
stepLD (ltac:(oF' 0x9dccc%Z)) (ltac:(oD' 0x9dccc%Z)) (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dcd0%Z)) (ltac:(oD' 0x9dcd0%Z)) (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x9dcd4%Z)) (ltac:(oD' 0x9dcd4%Z)).
stepST (ltac:(oF' 0x9dcd8%Z)) (ltac:(oD' 0x9dcd8%Z)) (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
stepST (ltac:(oF' 0x9dcdc%Z)) (ltac:(oD' 0x9dcdc%Z)) (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
stepST (ltac:(oF' 0x9dce0%Z)) (ltac:(oD' 0x9dce0%Z)) (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).
stepn (ltac:(oF' 0x9dce4%Z)) (ltac:(oD' 0x9dce4%Z)). rewrite Hs0.
stepLD (ltac:(oF' 0x9dce8%Z)) (ltac:(oD' 0x9dce8%Z)) (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dcec%Z)) (ltac:(oD' 0x9dcec%Z)) (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x9dcf0%Z)) (ltac:(oD' 0x9dcf0%Z)) ltac:(apply c_eq_refl).
stepLD (ltac:(oF' 0x9dcf4%Z)) (ltac:(oD' 0x9dcf4%Z)) (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dcf8%Z)) (ltac:(oD' 0x9dcf8%Z)) (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dcfc%Z)) (ltac:(oD' 0x9dcfc%Z)) (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dd00%Z)) (ltac:(oD' 0x9dd00%Z)) (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dd04%Z)) (ltac:(oD' 0x9dd04%Z)) (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dd08%Z)) (ltac:(oD' 0x9dd08%Z)) (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dd0c%Z)) (ltac:(oD' 0x9dd0c%Z)) (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD (ltac:(oF' 0x9dd10%Z)) (ltac:(oD' 0x9dd10%Z)) (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepn (ltac:(oF' 0x9dd14%Z)) (ltac:(oD' 0x9dd14%Z)). rewrite Hsp. sp_renorm.
replace (su - 0)%Z with su by lia.
stepret (ltac:(oF' 0x9dd18%Z)) (ltac:(oD' 0x9dd18%Z)) ret ltac:(reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End SE.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
