(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtPopulate1 JbtPopulate2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtPopulate3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPopulate3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3le"; "4Z"; "0E"; "5bvmap"; "0M"; "6Wn"; "6apart"; "6cell"; "6wr"]; ["7msteps"; "8ret_ok"; "9art_carve"; ":getr"; ":mkst"; ":regupd"; ";mem_grows"; "<loaded_segments"; "=add"; "=div"; "=le"; "=lt"; "=mul"; "=of_nat"; "=pow"; "=sub"]; ["0am"; "0au"; "0b"; "0free_bytes"; "0fx"; "0g18"; "0g19"; "0g20"; "0g21"; "0g22"; "0g8"; "0g9"; "0i"; "0j"; "0k"; "0m"]; ["0mm"; "0mu"; "0new"; "0nf"; "0nsz"; "0r"; "0raw"; "0rb"; "0regs"; "0regs'"; "0rom"; "0sp"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"]; ["0sz"; "0tot"; "0u"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Fixpoint art_carve (M : word -> option byte) (E au sz i : Z) (k : nat) : word -> option byte :=
match k with O => M | S k' => art_carve (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) E au sz (i + 1) k' end.
Lemma art_carve_grows : ltac2:(TCodec.tc2 tcn__JbtPopulate3 "J'0'QNyR0%211'1y8%511%311p051'8&Fr5&Br4r3r2r1r6%66754321%9281pRJ;1pT2<1pR4=1pD>1pH@1pRNI1").
Proof. induction k as [|k IH]; intros; cbn [art_carve]. apply mem_grows_refl. eapply mem_grows_trans; [apply Wn_grows | apply IH]. Qed.
Lemma art_carve_outside : ltac2:(TCodec.tc2 tcn__JbtPopulate3 "R5'0'QNyR0%211'1y8%511%311p051'8&Jzr2%3221&Or6&L+4&Hr3&Mr8%211%5241%8271%;2:1%@2?1&Kr7&N+2+R0%3221%6251&6'3r5r:%B11%E231%H2G1%K2D1&QOr4%22Q:1%Q3241%N2M:%Q12J1%E241%>241%@11'4&Br9r;%37B2Q2KQ81C%C1D%63QB21p081p0J1p0Q21p0Q@1pT8QK1pRJQF1pT2QG1pR4QH1pDQI1pHQK1pRNR41").
Proof.
induction k as [|k IH]; intros M E au sz i x Hi Hlo Hhi N; cbn [art_carve]. reflexivity.
rewrite Nat2Z.inj_succ in Hlo, N. rewrite IH; [|lia|lia|lia|lia]. rewrite Wn_outside; [reflexivity|lia|cbn; lia|cbn; lia].
Qed.
Lemma cell_carve_other : ltac2:(TCodec.tc2 tcn__JbtPopulate3 "R<'0'QNyR0%211'1y8%511%311p051'8&Jzr4%3221&Or8&L+4&Hr5&Mr:%211%5241%8271%;2:1%@2?1&Kr9&N+2+R0%3221%6251r6%I2H1r7%A13%D221%<217&=r<r>%G11%J2@1%M2L1%Q0251%O2N4%L1<%9432Q21&>&G%251:HQ5@&Br?r=r;r@%564@3A21%9581Q6OQ<p081p0<1p0G1p0L1p0O1p0Q71p0QE1pT6QJ1pS0R41pR6QL1pRJQM1pT2QN1pR4QO1pDR01pHR21pRNR;1").
Proof.
induction k as [|k IH]; intros M E au sz i b m u Hi Hlo Hhi Hb Hm A C; cbn [art_carve]. exact C.
rewrite Nat2Z.inj_succ in Hlo, A. unfold apart in A. apply IH; [lia|lia|lia|lia|lia|unfold apart; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|exact C].
Qed.
Lemma cell_carve_hit : ltac2:(TCodec.tc2 tcn__JbtPopulate3 "R7'0'QNyR0%211'1y8%511%311p051'8&Jzr2%3221&Or6&L+4&Hr3&Mr8%211%5241%8271%;2:1%@2?1&Kr7&N+2+R0%3221%6251'3r5r4%K221r:%C11%F251%>251%8251&>&G&Br9r;%36:2KDQ11+1%Q02?1%Q32Q21%Q6261u4&I%Q72DK%Q62Q31+@%4221%@5?;761p0B1p0L1p0Q41p0QB1pRLQG1pRJQH1pT2QI1pR4QJ1pDQK1pHQM1pRNR61").
Proof.
induction k as [|k IH]; intros M E au sz i j Hi Hlo Hhi Hj; cbn [art_carve]. lia.
rewrite Nat2Z.inj_succ in Hlo, Hj. destruct (Z.eq_dec j i) as [->|NE].
- apply cell_carve_other; [lia|lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; cbn; lia.
- apply IH; lia.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_pop_loop : ltac2:(TCodec.tc2 tcn__JbtPopulate3 "U?'0&:y5'QNyR0%211%5241'1y8%611%311p061'8'4&Cr8(QL+:(2%33A21%6251&QMr2%22C1%;3C41r9+;%;3I19%>231r6%92J1%B3J31r:+<%B3Q01@%E231&H&Lr4r5%3221%52<1%E2Q61%N3Q681r;+C%N3Q<1L%Q1231%K2Q<:%Q43Q<21r<+E%Q43QB1Q2%Q7231r7%Q22QC1%Q;3QC31&Mr>%211%H261%Q@3QAQ01'7u1r?%3221&Jz%221Q;%322C'3+Q0%621F+RPP0%82H1%5231r=%Q82Q11%Q:2D1&N+2%221:%@241+Vb\P0&Or@+4%QB21Q5%4231%G261&KrA+Q?%>2=1%4231&?&GrDrB%QN2=Q9%@221rF%Q=11%R22A1%948741'5'@&DvQ4rG+Zli0%RO3S;1RM/01S;rE%75652=1r1+Zlj0%S53SA1S3/01SA&BrCrH%36EI2HO1%@5?851:%B3L:1%SJ1SK&6%SB32<S<%211%SD34S;RO%411r3+>%SE3T31SC%SI3931%911+?%SI3T71SG%SM3=S41%=11%SN2S?S5rL%T021S7%T23T:31p051p0:1p0@1p0C1pS<G1%R?2I1qSDT@1%Q>2TA1p0Q@1p0QK1p0R11p0R91p0RA1p0RH1p0RJ1p0RN1p0S31p0S91p0SA1p0SH1p0T51p0T=1pS6TJ1pRJTK1pT2TL1pR4TM1pDTN1pSFU01pHU11pSBU71pRNU>1").
Proof.
induction k as [|k IH]; intros regs M rom E au sz i new H10 H11 H12 H19 H21 Enew Hk Hi Hau Hsz Hfit Hlo Hhi W. lia.
rewrite Nat2Z.inj_succ in Enew, W.
assert (Hisz : 0 <= i * sz <= new * sz) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hq : 0 <= (au + i * sz) / 16 < 2 ^ 28).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x57320 : word) M rom) (mkst regs1 (0x5733c : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom)
/\ getr regs1 10 = Z_to_bv 64 (i + 1) /\ getr regs1 11 = Z_to_bv 64 E /\ getr regs1 12 = Z_to_bv 64 (au + (i + 1) * sz) /\ getr regs1 19 = Z_to_bv 64 new /\ getr regs1 21 = Z_to_bv 64 sz
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs1 r = getr regs r)).
{ eexists. split.
- stepn (ltac:(oF' 0x57320%Z)) (ltac:(oD' 0x57320%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 4) with 16.
zstep (ltac:(oF' 0x57324%Z)) (ltac:(oD' 0x57324%Z)). zstep (ltac:(oF' 0x57328%Z)) (ltac:(oD' 0x57328%Z)). zstep (ltac:(oF' 0x5732c%Z)) (ltac:(oD' 0x5732c%Z)). zstep (ltac:(oF' 0x57330%Z)) (ltac:(oD' 0x57330%Z)).
replace (Z_to_bv 64 (E + (2 ^ 64 - 1 - i) * 2 ^ 2)) with (Z_to_bv 64 (E - 4 * (i + 1)))
by (apply art_zb_eq; replace (E + (2 ^ 64 - 1 - i) * 2 ^ 2) with (E - 4 * (i + 1) + 4 * 2 ^ 64) by lia; rewrite Z_mod_plus_full; reflexivity).
zsw (ltac:(oF' 0x57334%Z)) (ltac:(oD' 0x57334%Z)) (E - 4 * (i + 1)) ((au + i * sz) / 16) ltac:(eapply (wr_wok _ _ _ _ W); cbn; lia).
zstep (ltac:(oF' 0x57338%Z)) (ltac:(oD' 0x57338%Z)). apply mst_refl.
- repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
destruct STEP as (regs1 & RUN1 & P10 & P11 & P12 & P19 & P21 & K1).
destruct k as [|k2].
- cbn [art_carve]. eexists. split.
+ eapply msteps_trans; [exact RUN1|]. zbft (ltac:(oF' 0x5733c%Z)) (ltac:(oD' 0x5733c%Z)). apply mst_refl.
+ intros r N10 N12 N14 N15. apply K1; assumption.
- assert (RUNb : msteps ASEGS (mkst regs1 (0x5733c : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom) (mkst regs1 (0x57320 : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom)).
{ zbtk (ltac:(oF' 0x5733c%Z)) (ltac:(oD' 0x5733c%Z)). apply mst_refl. }
destruct (IH regs1 (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom E au sz (i + 1) new P10 P11 P12 P19 P21 ltac:(lia) ltac:(lia) ltac:(lia) Hau Hsz Hfit Hlo Hhi
ltac:(apply wr_Wn; eapply wr_sub; [exact W|lia|lia])) as (regs' & RUN2 & K2).
exists regs'. split.
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. cbn [art_carve]. exact RUN2.
+ intros r N10 N12 N14 N15. rewrite K2 by assumption. apply K1; assumption.
Qed.
#[using="Type"] Lemma art_pop_d_fn : ltac2:(TCodec.tc2 tcn__JbtPopulate3 "U1&:y5'QNyR0%211%5241'1y8%611%311p061'8'4&Cr9(QL+:(2%33A21%6251&QM+1%22C1%;3C41r:+8%;3I19%>231r7%92J1%B3J31r;+9%B3Q01@%E231r4%@2Q11%I3Q131r<+B%I3Q71G%L231r8%G2Q81%Q03Q831r=+D%Q03Q>1N%Q3231r5%N2Q?1%Q73Q?31r>+E%Q73QE1Q5%Q:231%Q42QEQ:%Q=3QE21&J+Vb\P0%221F&K&H+T0%22C1&N+2+Q?%3221%8251z%=21J+Q0%8271%<2F1%>217'3%C25I+RPP0%E2K1%4231r?%H21Q<+R0%C2B1%H2Q?1%:241%M2A6%K274%=221%M29A%?241&>&GrFrD%Q221Hu8rA%7565321'@&DvQ4rH+ZlgH%RJ3S61RH/01S6rG%756521>&E&L%Q>2Q=Q=%22>1%RM2S>1%53;RA1%RO2S@Q=%732S21+;%S73SE1S5+S`PPPP0%QJ2I1%QK219%S62SG1%>3751+<%S>3SL1S<rB%S;2SL1%C3531+=%SC3T11SA%F3314+Zli0%SF3T21SD/01T2%Q25Q141LQ9%Q43Q;L1p0Q61p0Q?1p0QB1p0QF1p0QM1p0R31p0R81p0R;1p0RE1p0RI1p0S01p0S81p0S@1p0SH1p0T01pR8T=1pT4T>1pR4T?1pT2T@1pS@TA1pS<TB1pSFTD1pHTE1pSBTK1").
Proof.
intros regs M rom r rb sz au tot free_bytes H10 H8 H9 H18 H20 H21 Hr Hr' Hrb Hrb' Hsz Hfb Hau Htot Cau.
zbft (ltac:(oF' 0x572f8%Z)) (ltac:(oD' 0x572f8%Z)).
zld (ltac:(oF' 0x572fc%Z)) (ltac:(oD' 0x572fc%Z)) (r + 32) Cau.
zbft (ltac:(oF' 0x57300%Z)) (ltac:(oD' 0x57300%Z)).
zstep (ltac:(oF' 0x57304%Z)) (ltac:(oD' 0x57304%Z)). zstep (ltac:(oF' 0x57308%Z)) (ltac:(oD' 0x57308%Z)). zstep (ltac:(oF' 0x5730c%Z)) (ltac:(oD' 0x5730c%Z)). zstep (ltac:(oF' 0x57310%Z)) (ltac:(oD' 0x57310%Z)). zstep (ltac:(oF' 0x57314%Z)) (ltac:(oD' 0x57314%Z)). zstep (ltac:(oF' 0x57318%Z)) (ltac:(oD' 0x57318%Z)). zstep (ltac:(oF' 0x5731c%Z)) (ltac:(oD' 0x5731c%Z)).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_pop_e_fn := (ltac2:(TCodec.tc2 tcn__JbtPopulate3 "XG&:y5'QNyR0%211%5241'1y8%611%311p061'8'4&CrE(QL+2(2%33A21%6251&QM&OrA+R0%3221%52F1%>3F71rF+8%>3L1<%A231%;2L9%D3L21rG+=%D3Q21B%G231r?%B2Q31%K3Q331rH+C%K3Q91I%N231%Q03Q81=rI+E%Q03Q>1N%Q3231rC%N2Q?1%Q73Q?31&J%12NJ&K&N%12Q8Q1%32H1+Vb\P0%721J&H+T0%22F1+Q?%92Q@1%;231'3+Q0%@21L+RPP0%B2N1%5231z%E21Q1&LrJ%22O1%R13R2L1%J26Q1%C24R1%L21Q8%K2Q4IrK%O2;1rLrN%J221%Q121O%Q426=%G261%Q428Q2&ArQ5%211%L2;4&=rQ<%R<21R:rQ;%442R<1Q6&?&GrQ@%34217Q:&>rQArQ=+@%Q@221u8rQ9%75:6321rQBrQ>+Q@%QG221%<5?4176rQCrQ?+Q8%QL221%A5D41<;rQD+QH%R02F1%E5H31@?rQE%S:2?S3&QO%12SN<%J5M43E1rQF%S?2?I%M5Q021HGrQG+H%SC2>1%Q15Q431LKrQH%SF2=R8%Q45Q721ONrQI%SI2;G%Q75Q:21Q2Q1rQJ%SL2;O%Q:5Q=21Q5Q4rQK%SO2:I%Q=5Q@21Q8Q7rQL%T22:T0%Q@5QC21Q;Q:'@&DvQ4rQN+Zlj0%T?3TK1T=/01TKrQM%756521;&E+1%TE3U31TC%3391B%TB2U3F%532TE1%TD2U5R2%732T<1+9%TL3U:1TJ%TH2U9QF%;3421+:%U03U>1TN%TL2U==%?3421+;%U43UB1U2%B3314%U12UBR0%D32TC1+>%U93UG1U7%U52UFR9%H3421+B%U=3UK1U;%U92UJR<%L3421%U;2ULRE%N32TF1+D%UC3V11UA%U?2V0S3%Q23421%UA2V2S3%Q432TG1+F%UI3V71UGrQ:%UF2V71%Q93531&<u1%TB2R1S3%TC2RAR9%44S3Q@21%TE2R4T>%TF2R?S9%74S6321+R4%TI2R81%:4931T>%QM5QL<R41R1%QO3SCQG1p0R11p0R51p0R91p0R=1p0RA1p0RE1p0RJ1p0RN1p0S41p0S91p0S?1p0SE1p0SN1p0T31p0T91p0T:1p0T;1p0T<1p0T=1p0T>1p0T?1p0TA1p0TE1p0TG1p0TJ1p0TO1p0U21p0U41p0U71p0U91p0U>1p0UA1p0UH1p0UO1p0V21p0V71p0V:1p0VB1p0VH1p0W01p0W71pRDWG1pRBWH1pR@WI1pR>WJ1pR<WK1pRHWL1pRFWM1pS:WN1pS2WO1pR2X01pS4X11pS8X21pR4X31pS6X41pT2X51pS<X61pSHX71pS>X?1pSFX:1pHX;1pSBXA1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 4%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 5%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 6%nat 0%nat).
Variable new : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 7%nat 0%nat).
Variable au : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 8%nat 0%nat).
Variable nf : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 9%nat 0%nat).
Variable mu : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 10%nat 0%nat).
Variable am : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 11%nat 0%nat).
Variable mm : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 12%nat 0%nat).
Variable nsz : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 13%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 14%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 15%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 16%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 17%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 18%nat 0%nat).
Variable g21 : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 19%nat 0%nat).
Variable g22 : ltac:(sec_ty2 constr:(SEC_T_art_pop_e_fn) 20%nat 0%nat).
Lemma art_pop_e_fn : ltac:(sec_stmt2 constr:(SEC_T_art_pop_e_fn) 21%nat 0%nat).
Proof using Type regs M rom raw sp r sz new au nf mu am mm nsz g8 g9 g18 g19 g20 g21 g22.
intros H2 H8 H13 H19 H21 Hsp Hsp' Hr Hr' Hsz Hnew Ensz Hau Haumu Hmu Hnf Hnf' Ham Hmm Hret
Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 A Wr Cnf Cmu Cam Cmm F8 F16 F24 F32 F40 F48 F56 F64.
zld (ltac:(oF' 0x57340%Z)) (ltac:(oD' 0x57340%Z)) (r + 16) Cnf.
zstep (ltac:(oF' 0x57344%Z)) (ltac:(oD' 0x57344%Z)). rewrite <- Ensz.
zld (ltac:(oF' 0x57348%Z)) (ltac:(oD' 0x57348%Z)) (r + 48) Cmu.
zstep (ltac:(oF' 0x5734c%Z)) (ltac:(oD' 0x5734c%Z)). zstep (ltac:(oF' 0x57350%Z)) (ltac:(oD' 0x57350%Z)).
zsd (ltac:(oF' 0x57354%Z)) (ltac:(oD' 0x57354%Z)) (r + 16) (nf + new) ltac:(rewok Wr).
zsd (ltac:(oF' 0x57358%Z)) (ltac:(oD' 0x57358%Z)) (r + 32) (au + nsz) ltac:(rewok Wr).
zbft (ltac:(oF' 0x5735c%Z)) (ltac:(oD' 0x5735c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cam' : cellA X (r + 40) 8 am) by zcell; assert (Cmm' : cellA X (r + 56) 8 mm) by zcell end.
zld (ltac:(oF' 0x57360%Z)) (ltac:(oD' 0x57360%Z)) (r + 40) Cam'. zld (ltac:(oF' 0x57364%Z)) (ltac:(oD' 0x57364%Z)) (r + 56) Cmm'.
zbft (ltac:(oF' 0x57368%Z)) (ltac:(oD' 0x57368%Z)).
zsb (ltac:(oF' 0x5736c%Z)) (ltac:(oD' 0x5736c%Z)) (r + 68) 0 ltac:(rewok Wr).
zstep (ltac:(oF' 0x57370%Z)) (ltac:(oD' 0x57370%Z)). zstep (ltac:(oF' 0x57374%Z)) (ltac:(oD' 0x57374%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => set (ME := X) end.
assert (TE : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> sp - 64 <= a -> a + Z.of_nat k <= sp -> cellA M a k v -> cellA ME a k v).
{ intros a k v Ha Hak Hlo Hhi C. unfold ME. unfold apart in A. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
assert (E8 : cellA ME (sp - 8) 8 (U raw)) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F8]).
assert (E16 : cellA ME (sp - 16) 8 g8) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F16]).
assert (E24 : cellA ME (sp - 24) 8 g9) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F24]).
assert (E32 : cellA ME (sp - 32) 8 g18) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F32]).
assert (E40 : cellA ME (sp - 40) 8 g19) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F40]).
assert (E48 : cellA ME (sp - 48) 8 g20) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F48]).
assert (E56 : cellA ME (sp - 56) 8 g21) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F56]).
assert (E64 : cellA ME (sp - 64) 8 g22) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F64]).
zld (ltac:(oF' 0x57378%Z)) (ltac:(oD' 0x57378%Z)) (sp - 8) E8. zld (ltac:(oF' 0x5737c%Z)) (ltac:(oD' 0x5737c%Z)) (sp - 16) E16. zld (ltac:(oF' 0x57380%Z)) (ltac:(oD' 0x57380%Z)) (sp - 24) E24. zld (ltac:(oF' 0x57384%Z)) (ltac:(oD' 0x57384%Z)) (sp - 32) E32.
zld (ltac:(oF' 0x57388%Z)) (ltac:(oD' 0x57388%Z)) (sp - 40) E40. zld (ltac:(oF' 0x5738c%Z)) (ltac:(oD' 0x5738c%Z)) (sp - 48) E48. zld (ltac:(oF' 0x57390%Z)) (ltac:(oD' 0x57390%Z)) (sp - 56) E56. zld (ltac:(oF' 0x57394%Z)) (ltac:(oD' 0x57394%Z)) (sp - 64) E64.
rewrite !Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x57398%Z)) (ltac:(oD' 0x57398%Z)).
stepret (ltac:(oF' 0x5739c%Z)) (ltac:(oD' 0x5739c%Z)) raw ltac:(rwH; reflexivity).
subst ME. zret.
Qed.
End SE.
End FPX.
