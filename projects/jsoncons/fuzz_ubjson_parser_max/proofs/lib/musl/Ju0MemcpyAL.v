(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib Ju0MemcpyBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__musl_Ju0MemcpyAL () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.musl.Ju0MemcpyBase."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4bvmap"; "5wbytes"; "6msteps"; "7at_"; "7ret_ok"; "8getr"; "8mkst"; "9keeps"]; [":memk"; ";loaded_segments"; "<add"; "<land"; "<le"; "<lt"; "<modulo"; "<mul"; "<of_nat"; "<pow"; "<sub"; "0bs"; "0dst"; "0e8"; "0fx"; "0k"]; ["0m"; "0mem"; "0mem0"; "0n"; "0q"; "0regs"; "0regs'"; "0ret"; "0rom"; "0src"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Section AL.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.
#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
#[local] Notation B := (b_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.
Lemma al_entry : ltac2:(TCodec.tc2 tcn__musl_Ju0MemcpyAL "RK&8y5'Q<yR0%211%5241'1y8%611%311p061'4&=r2(Q:+:(2%33@21%6251vL%93@21r3+;%93F17%<231vQ9%?3F21'7&F&Q=%12K5+4%4221z%G3721%62Q0@%8215%J3:14'5'3':&A&>vNr7+eX]D%Q03Q;1N/01Q;r6vQ8%8576321r1+eXfD%Q73QB1Q5/01QB%=5<4176%@3?61+=%Q<3QI1Q:%Q?281&;%12Q:L%QC3QJ31%QC2<Q8%42Q7O%QF3QM21+<%QE3R21QC%QH2A1%QI2I2%QK3R221+1%QJ3R71QH%QM2F1%QN2N2%R03R721&?%12Q1J%Q7231%Q8291%Q92?1%Q:2C1%Q;2J1qR>R>1%Q>2R?1p0Q@1p0QD1p0QM1p0R41pR4R?1pR<RE1").
Proof using HOK.
intros regs mem H10 H11 Hs4 Hd4.
pose proof (u64_range src). pose proof (u64_range dst).
eexists. split.
- stepn (ltac:(oF' 0xaa1b4%Z)) (ltac:(oD' 0xaa1b4%Z)).
stepb_tk (ltac:(oF' 0xaa1b8%Z)) (ltac:(oD' 0xaa1b8%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
stepn (ltac:(oF' 0xaa2c8%Z)) (ltac:(oD' 0xaa2c8%Z)).
stepn (ltac:(oF' 0xaa2cc%Z)) (ltac:(oD' 0xaa2cc%Z)).
stepb_ft (ltac:(oF' 0xaa2d0%Z)) (ltac:(oD' 0xaa2d0%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
apply mst_refl.
- repeat split; gres; rwH; rewrite ?at_0; try reflexivity. solve_keeps.
Qed.
Lemma b1_run : ltac2:(TCodec.tc2 tcn__musl_Ju0MemcpyAL "R>&8y5'Q<yR0%211%5241'7&<r2%211'4&=r4(Q:+1(2%33?21%6251r3%93?21r5+;%93E17%<231&;vQ9%2218%A3G41r6+=%A3M1?%D231vL%921E%H3N31&Dz%221A&B%12;IvQ3%O3Q321'5'3':&A&>vNr:+eY]<%Q53Q?1Q3/01Q?&@vQ2vKr8%443H21vQ8%<5;:721r1r9%948M7E%@5?3215%C3B51&?%12A6%G231qR>QN1%J2QO1p0L1p0Q11p0Q51p0Q=1p0QF1p0R11pR0R51pR@R81pR<R81").
Proof.
intros regs ret k Hret H1 H11 H13 Hk Hkn.
eexists. split.
- mlbu (ltac:(oF' 0xaa5ac%Z)) (ltac:(oD' 0xaa5ac%Z)) k.
msb (ltac:(oF' 0xaa5b0%Z)) (ltac:(oD' 0xaa5b0%Z)) k ltac:(apply sb_val_plain).
replace (k + 1)%Z with n by lia.
stepret (ltac:(oF' 0xaa5b4%Z)) (ltac:(oD' 0xaa5b4%Z)) ret ltac:(exact H1).
apply mst_refl.
- solve_keeps.
Qed.
Section SE.
Local Abbreviation SEC_T_t2_run := (ltac2:(TCodec.tc2 tcn__musl_Ju0MemcpyAL "SB&8y5'Q<yR0%211%5241'7&<r3%211'4&=r5(Q:+1(2%33?21%6251r4%93?21r6+;%93E17%<231&;vQ9%2218%A3G41r7+=%A3M1?%D231vL%921E%H3N31r8+<%H3Q41F%K231&Q;%12Q5L%O3Q531'3&Dz%221I&E&I+2+R0%3221%52O1%:271'6&C%12K7%Q>3QB1<%Q?3QC29%5221%52HQ=%QB3QF1@%QC3QG2Q?%9221r:%E2D1&JvQ3r;%3221&B%@27F%A28QI%3221%QO3R351'5':&A&>vNr?+eY[D%R43R>1R2/01R>&@vQ2vKr=%443QG21vQ8%<5;:721r1r>%948QL7J%@5?3215%C3B51&?%12A6%QG231qR>RM1%I2RN1p0K1p0Q51p0Q81p0Q=1p0QD1p0R01p0R81p0R@1p0RI1p0S41pR2S81pR0S91pR@S<1pR<S<1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_t2_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_t2_run) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_t2_run) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_t2_run) 3%nat 0%nat).
Lemma t2_run : ltac:(sec_stmt2 constr:(SEC_T_t2_run) 4%nat 0%nat).
Proof.
intros Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
-
eexists. split.
+ stepn (ltac:(oF' 0xaa574%Z)) (ltac:(oD' 0xaa574%Z)).
stepb_ft (ltac:(oF' 0xaa578%Z)) (ltac:(oD' 0xaa578%Z)) ltac:(cond).
stepn (ltac:(oF' 0xaa57c%Z)) (ltac:(oD' 0xaa57c%Z)).
stepb_ft (ltac:(oF' 0xaa580%Z)) (ltac:(oD' 0xaa580%Z)) ltac:(cond).
stepret (ltac:(oF' 0xaa584%Z)) (ltac:(oD' 0xaa584%Z)) ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa5ac : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xaa574%Z)) (ltac:(oD' 0xaa574%Z)).
stepb_ft (ltac:(oF' 0xaa578%Z)) (ltac:(oD' 0xaa578%Z)) ltac:(cond).
stepn (ltac:(oF' 0xaa57c%Z)) (ltac:(oD' 0xaa57c%Z)).
stepb_tk (ltac:(oF' 0xaa580%Z)) (ltac:(oD' 0xaa580%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
eexists. split.
+ stepn (ltac:(oF' 0xaa574%Z)) (ltac:(oD' 0xaa574%Z)).
stepb_tk (ltac:(oF' 0xaa578%Z)) (ltac:(oD' 0xaa578%Z)) ltac:(cond).
mlbu (ltac:(oF' 0xaa588%Z)) (ltac:(oD' 0xaa588%Z)) k.
mlbu (ltac:(oF' 0xaa58c%Z)) (ltac:(oD' 0xaa58c%Z)) (k + 1)%Z.
stepn (ltac:(oF' 0xaa590%Z)) (ltac:(oD' 0xaa590%Z)).
stepn (ltac:(oF' 0xaa594%Z)) (ltac:(oD' 0xaa594%Z)).
msb (ltac:(oF' 0xaa598%Z)) (ltac:(oD' 0xaa598%Z)) k ltac:(apply sb_val_plain).
msb (ltac:(oF' 0xaa59c%Z)) (ltac:(oD' 0xaa59c%Z)) (k + 1)%Z ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0xaa5a0%Z)) (ltac:(oD' 0xaa5a0%Z)).
stepn (ltac:(oF' 0xaa5a4%Z)) (ltac:(oD' 0xaa5a4%Z)).
stepb_tk (ltac:(oF' 0xaa5a8%Z)) (ltac:(oD' 0xaa5a8%Z)) ltac:(cond).
stepret (ltac:(oF' 0xaa584%Z)) (ltac:(oD' 0xaa584%Z)) ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa5ac : word) (MK (k + 2)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xaa574%Z)) (ltac:(oD' 0xaa574%Z)).
stepb_tk (ltac:(oF' 0xaa578%Z)) (ltac:(oD' 0xaa578%Z)) ltac:(cond).
mlbu (ltac:(oF' 0xaa588%Z)) (ltac:(oD' 0xaa588%Z)) k.
mlbu (ltac:(oF' 0xaa58c%Z)) (ltac:(oD' 0xaa58c%Z)) (k + 1)%Z.
stepn (ltac:(oF' 0xaa590%Z)) (ltac:(oD' 0xaa590%Z)).
stepn (ltac:(oF' 0xaa594%Z)) (ltac:(oD' 0xaa594%Z)).
msb (ltac:(oF' 0xaa598%Z)) (ltac:(oD' 0xaa598%Z)) k ltac:(apply sb_val_plain).
msb (ltac:(oF' 0xaa59c%Z)) (ltac:(oD' 0xaa59c%Z)) (k + 1)%Z ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0xaa5a0%Z)) (ltac:(oD' 0xaa5a0%Z)).
stepn (ltac:(oF' 0xaa5a4%Z)) (ltac:(oD' 0xaa5a4%Z)).
stepb_ft (ltac:(oF' 0xaa5a8%Z)) (ltac:(oD' 0xaa5a8%Z)) ltac:(cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
| gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_al4_run := (ltac2:(TCodec.tc2 tcn__musl_Ju0MemcpyAL "SJ&8y5'Q<yR0%211%5241'7'4&=r4(Q:+1(2%33<21%6251r3%93<21r5+;%93B17%<231&;vQ9%2218%A3D41r6+=%A3J1?%D231vL%921E%H3K31r7+<%H3Q11F%K231&Q;%12Q2L%O3Q231'3&Dz%221I&E&I+2+R0%3221%52O1%:271%:29B'6&C+4%22F1%Q@3QA1>%QA3QB23&Br8%2216vQ3%E221%G261%<281'5':&A&>vNr<+eXi@%QM3R41QK/01R4&@vQ2vKr:%443Q@21vQ8%<5;:721r1+eY[D%R83R?1R6/01R?r9%Q121Q0%M2:1%>4=QJ<1%E5D851:%H3G:1%RB2:R=r;%RE3RH21%RE2=R:%R92R88%RH3RK21%RH2@R5%R<2R4;%RK3RN21%RK2CR1%R02S1@%RN3S121&?%12Q2G%R1231%R2271%R32;1%R42?1%R52C1qR>S81%Q>2S91p0Q@1p0QN1p0R01p0R<1p0RD1p0RL1p0S51pR2S@1pR0SA1pR@SD1pR<SD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_al4_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_al4_run) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_al4_run) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_al4_run) 3%nat 0%nat).
Lemma al4_run : ltac:(sec_stmt2 constr:(SEC_T_al4_run) 4%nat 0%nat).
Proof.
intros H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
- eexists. split.
+ stepn (ltac:(oF' 0xaa330%Z)) (ltac:(oD' 0xaa330%Z)).
stepb_tk (ltac:(oF' 0xaa334%Z)) (ltac:(oD' 0xaa334%Z)) ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn (ltac:(oF' 0xaa330%Z)) (ltac:(oD' 0xaa330%Z)).
stepb_ft (ltac:(oF' 0xaa334%Z)) (ltac:(oD' 0xaa334%Z)) ltac:(cond).
mlw (ltac:(oF' 0xaa338%Z)) (ltac:(oD' 0xaa338%Z)) k.
stepn (ltac:(oF' 0xaa33c%Z)) (ltac:(oD' 0xaa33c%Z)).
msw (ltac:(oF' 0xaa340%Z)) (ltac:(oD' 0xaa340%Z)) k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0xaa344%Z)) (ltac:(oD' 0xaa344%Z)).
stepn (ltac:(oF' 0xaa348%Z)) (ltac:(oD' 0xaa348%Z)).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_al8_run := (ltac2:(TCodec.tc2 tcn__musl_Ju0MemcpyAL "SL&8y5'Q<yR0%211%5241'7'4&=r5(Q:+1(2%33<21%6251r4%93<21r6+;%93B17%<231&;vQ9%2218%A3D41r7+=%A3J1?%D231vL%921E%H3K31r8+<%H3Q11F%K231&Q;%12Q2L%O3Q231'3&Dz%221I&E&I+2+R0%3221%52O1%:271%:29B'6+8%:2E1%Q?3Q@M=%@221%@24H%QB3QCQ05&Br9%2218vQ3%F221%H261%I281%>2:1'5':&A&>vNr=+eXh@%QO3R61QM/01R6&@vQ2vKr;%443QB21vQ8%<5;:721r1+eXi@%R:3RA1R8/01RA%L28K%<4;QJ:1%C5B6318%F3E81%RB28R=r<%RE3RH21%RE2;R:%R92R88%RH3RK21%RH2>R5%R<2R4;%RK3RN21%RK2AR1r:%R12S21%RO3S231&?%12Q1F%R2231%R3281%R42<1%R52@1%R62D1qR>S91%Q=2S:1p0Q?1p0QO1p0R11p0R=1p0RE1p0RM1p0S61pQLSA1pR2SB1pR0SC1pR@SF1pR<SF1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_al8_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_al8_run) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_al8_run) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_al8_run) 3%nat 0%nat).
Variable e8 : ltac:(sec_ty2 constr:(SEC_T_al8_run) 4%nat 0%nat).
Lemma al8_run : ltac:(sec_stmt2 constr:(SEC_T_al8_run) 5%nat 0%nat).
Proof.
intros H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
- eexists. split.
+ stepn (ltac:(oF' 0xaa310%Z)) (ltac:(oD' 0xaa310%Z)).
stepb_tk (ltac:(oF' 0xaa314%Z)) (ltac:(oD' 0xaa314%Z)) ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn (ltac:(oF' 0xaa310%Z)) (ltac:(oD' 0xaa310%Z)).
stepb_ft (ltac:(oF' 0xaa314%Z)) (ltac:(oD' 0xaa314%Z)) ltac:(cond).
mlw (ltac:(oF' 0xaa318%Z)) (ltac:(oD' 0xaa318%Z)) k.
mlw (ltac:(oF' 0xaa31c%Z)) (ltac:(oD' 0xaa31c%Z)) (k + 4)%Z.
msw (ltac:(oF' 0xaa320%Z)) (ltac:(oD' 0xaa320%Z)) k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0xaa324%Z)) (ltac:(oD' 0xaa324%Z)) (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0xaa328%Z)) (ltac:(oD' 0xaa328%Z)).
stepn (ltac:(oF' 0xaa32c%Z)) (ltac:(oD' 0xaa32c%Z)).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.
End SE.
Lemma al_loop : ltac2:(TCodec.tc2 tcn__musl_Ju0MemcpyAL "T0'0&8y5'Q<yR0%211%5241'7'4&=r3(Q:+1(2%33<21%6251r2%93<21r4+;%93B17%<231&;vQ9%2218%A3D41r5+=%A3J1?%D231vL%921E%H3K31r6+<%H3Q11F%K231&Q;&JvQ3%221F%42Q51%Q23Q561r7+>%Q23Q;1Q0%Q5231+?%;2Q<1%Q93Q<31&Dz%221C'3&G+@&B&Hr:%211%421Q@%7261%H2GC%=221&E%924:%2241%>241'5':&A&>vNr;+eXg0%R03R71QN/01R7&@vQ2vKr9%443QC21vQ8%<5;:721r1+eXh@%R;3RB1R9/01RBr<%Q011%Q221R>%Q52Q41%Q42<1%@4?QO>1%G5F:71<%J3I<1%RG2<RB%RI3RL1Q7%RI2>R>%R=2R<7%RL3RO21%RL2AR9%R@2R8:%RO3S221%RO2DR5%R32R2=%R52S61%S33S631&?%12Q4I%QI231%QJ281%QK2<1%QL2@1%QM2C1qR>S=1%Q@2S>1p0QB1p0R21p0R61p0R>1p0RI1p0S11p0S:1pR0SE1pR@SH1pR<SH1pR:SO1").
Proof.
induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
-
eexists. split.
+ mlw (ltac:(oF' 0xaa2e0%Z)) (ltac:(oD' 0xaa2e0%Z)) k.
mlw (ltac:(oF' 0xaa2e4%Z)) (ltac:(oD' 0xaa2e4%Z)) (k + 4)%Z.
mlw (ltac:(oF' 0xaa2e8%Z)) (ltac:(oD' 0xaa2e8%Z)) (k + 8)%Z.
mlw (ltac:(oF' 0xaa2ec%Z)) (ltac:(oD' 0xaa2ec%Z)) (k + 12)%Z.
stepn (ltac:(oF' 0xaa2f0%Z)) (ltac:(oD' 0xaa2f0%Z)).
stepn (ltac:(oF' 0xaa2f4%Z)) (ltac:(oD' 0xaa2f4%Z)).
msw (ltac:(oF' 0xaa2f8%Z)) (ltac:(oD' 0xaa2f8%Z)) k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0xaa2fc%Z)) (ltac:(oD' 0xaa2fc%Z)) (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0xaa300%Z)) (ltac:(oD' 0xaa300%Z)) (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0xaa304%Z)) (ltac:(oD' 0xaa304%Z)) (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0xaa308%Z)) (ltac:(oD' 0xaa308%Z)).
stepb_ft (ltac:(oF' 0xaa30c%Z)) (ltac:(oD' 0xaa30c%Z)) ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
* unfold v_addi. unorm. f_equal. lia.
* solve_keeps.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa2e0 : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
/\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* mlw (ltac:(oF' 0xaa2e0%Z)) (ltac:(oD' 0xaa2e0%Z)) k.
mlw (ltac:(oF' 0xaa2e4%Z)) (ltac:(oD' 0xaa2e4%Z)) (k + 4)%Z.
mlw (ltac:(oF' 0xaa2e8%Z)) (ltac:(oD' 0xaa2e8%Z)) (k + 8)%Z.
mlw (ltac:(oF' 0xaa2ec%Z)) (ltac:(oD' 0xaa2ec%Z)) (k + 12)%Z.
stepn (ltac:(oF' 0xaa2f0%Z)) (ltac:(oD' 0xaa2f0%Z)).
stepn (ltac:(oF' 0xaa2f4%Z)) (ltac:(oD' 0xaa2f4%Z)).
msw (ltac:(oF' 0xaa2f8%Z)) (ltac:(oD' 0xaa2f8%Z)) k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0xaa2fc%Z)) (ltac:(oD' 0xaa2fc%Z)) (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0xaa300%Z)) (ltac:(oD' 0xaa300%Z)) (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0xaa304%Z)) (ltac:(oD' 0xaa304%Z)) (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0xaa308%Z)) (ltac:(oD' 0xaa308%Z)).
stepb_tk (ltac:(oF' 0xaa30c%Z)) (ltac:(oD' 0xaa30c%Z)) ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
-- unfold v_addi. unorm. f_equal. lia.
-- solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split.
* replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
* replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section SE.
Local Abbreviation SEC_T_al16_run := (ltac2:(TCodec.tc2 tcn__musl_Ju0MemcpyAL "S9&8y5'Q<yR0%211%5241'7'4&=r3(Q:+1(2%33<21%6251r2%93<21r4+;%93B17%<231&;vQ9%2218%A3D41r5+=%A3J1?%D231vL%921E%H3K31r6+<%H3Q11F%K231&Q;&JvQ3%221F%42Q51%Q23Q561'3&Dz%221D%32E8%5221'5':&A&>vNr9+eXfD%Q=3QD1Q;/01QD&@vQ2vKr7%443Q021vQ8%<5;:721r1+eXh@%QH3QO1QF/01QO&F%Q02O9+@%3221%Q32Q21%@4?Q<>1%G5F:71<%J3I<1%R42<QOr8%R73R:21%R72?QL%QK2QJ8%R:3R=21%R:2BQG%QN2QF;%R=3R@21%R=2EQC%QB2RC?%R@3RC21&?%12Q4I%Q@231%QA271%QB2;1%QC2?1%QD2C1qR>RJ1%Q@2RK1p0QB1p0QI1p0R41p0R<1p0RE1pR0S01pR@S31pR<S31")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_al16_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_al16_run) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_al16_run) 2%nat 0%nat).
Lemma al16_run : ltac:(sec_stmt2 constr:(SEC_T_al16_run) 3%nat 0%nat).
Proof.
intros H1 H11 H13 H12 Hk.
destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
-
eexists. split.
+ stepn (ltac:(oF' 0xaa2d4%Z)) (ltac:(oD' 0xaa2d4%Z)).
stepb_tk (ltac:(oF' 0xaa2d8%Z)) (ltac:(oD' 0xaa2d8%Z)) ltac:(cond).
replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
apply mst_refl.
+ rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
repeat split; gres; rwH; try reflexivity. solve_keeps.
- set (q := Z.to_nat ((n - k) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa2e0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
/\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xaa2d4%Z)) (ltac:(oD' 0xaa2d4%Z)).
stepb_ft (ltac:(oF' 0xaa2d8%Z)) (ltac:(oD' 0xaa2d8%Z)) ltac:(cond).
stepn (ltac:(oF' 0xaa2dc%Z)) (ltac:(oD' 0xaa2dc%Z)).
apply mst_refl.
* cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_memcpy_aligned := (ltac2:(TCodec.tc2 tcn__musl_Ju0MemcpyAL "RC&8y5'Q<yR0%211%5241&<r1%211'4&=r3(Q:+1(2%33>21%6251r2%93>21r4+:%93D17%<231vL%?3D21r5+;%?3J1=%B231vQ9%E3J21r6+<%E3Q01C%H231&Q;vQ3%22Q21%M3Q241'7&F&Q=%12Q7=+4%4221z%Q53721%62Q<H%8215%Q83:14'5'3':&A&>vNr:+eX]D%Q>3QG1Q</01QGvQ2vQ8%8576321r9&9vK%236Q;1%=5<QL416%@3?61&?%12>QO%D231qR>R31%G2R41p0I1p0M1p0Q61p0Q?1p0QF1p0QM1p0R81pR@R=1pR<R=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_memcpy_aligned) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_memcpy_aligned) 1%nat 0%nat).
Theorem memcpy_aligned : ltac:(sec_stmt2 constr:(SEC_T_memcpy_aligned) 2%nat 0%nat).
Proof.
intros Hret H1 H10 H11 H12 Hs4 Hd4.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
set (m := (n mod 16)%Z).
pose proof (Z.mod_pos_bound n 16 ltac:(lia)) as Hm16.
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (Hl16 : Z.land m 16 = 0%Z).
{ destruct B16 as [E|E]; [exact E|]. exfalso.
pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa2d4 : word) (MK 0) rom)
(fun r => getr r 13 = at_ dst 0 /\ getr r 11 = at_ src 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ getr r 1 = ret /\ keeps regs r)).
{ destruct (al_entry regs (MK 0) H10 H11 Hs4 Hd4) as (r & R & P). exists r. split; [exact R|].
decompose [and] P. rewrite Z.sub_0_r. repeat split; try assumption; congruence. }
cbv beta. intros r1 (R13 & R11 & R12 & R1 & K1).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa310 : word) (MK (n - m)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al16_run r1 ret 0 R1 R11 R13 R12 ltac:(lia)) as (r & R & P). exists r.
subst m. rewrite Z.sub_0_r in R, P. split; [exact R|]. decompose [and] P. repeat split; try assumption.
eapply keeps_trans; eassumption. }
cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa330 : word) (MK (n - m + Z.land m 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al8_run r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r & R & P).
{ pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa574 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al4_run r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia)) as (r & R & P).
{ pose proof (Z.land_nonneg m 8). lia. }
{ pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). pose proof (Z.land_nonneg m 8). lia. }
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
destruct (t2_run r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1) as (r & R & P).
{ pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). lia. }
{ lia. }
exists r. split; [exact R | eapply keeps_trans; eassumption].
Qed.
End SE.
End AL.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
