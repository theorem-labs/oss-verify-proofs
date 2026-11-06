(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib AsanMemcpyBaseKB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMemcpyALKB0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemcpyALKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemcpyBaseKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4bvmap"; "5asanreflect_fx"; "6memk"; "7wbytes"; "8msteps"; "9at_"; "9ret_ok"; ":getr"]; [":mkst"; ";keeps"; "<loaded_segments"; "=add"; "=land"; "=le"; "=lt"; "=modulo"; "=mul"; "=of_nat"; "=pow"; "=sub"; "0bs"; "0dst"; "0e8"; "0k"]; ["0m"; "0mem"; "0mem0"; "0n"; "0q"; "0regs"; "0regs'"; "0ret"; "0rom"; "0src"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
Lemma al_entry : ltac2:(TCodec.tc2 tcn__AsanMemcpyALKB0 "RK&8y5'Q<yR0%211%5241'1y8%611%311p061'4&?r2(Q:+:(2%33@21%6251vM%93@21r3+;%93F17%<231vQ9%?3F21'7&G&Q=%12K5+4%4221z%G3721%62Q0@%8215%J3:14'5'3'<&B&@&9r7+QTio4%Q03Q;1N/01Q;r6vQ8%8576321r1+QTjX4%Q73QB1Q5/01QB%=5<4176%@3?61+=%Q<3QI1Q:%Q?281&=%12Q:L%QC3QJ31%QC2<Q8%42Q7O%QF3QM21+<%QE3R21QC%QH2A1%QI2I2%QK3R221+1%QJ3R71QH%QM2F1%QN2N2%R03R721&A%12Q1J%Q7231%Q8291%Q92?1%Q:2C1%Q;2J1qR>R>1%Q>2R?1p0Q@1p0QD1p0QM1p0R41pR4R?1pR<RE1").
Proof.
intros regs mem H10 H11 Hs4 Hd4.
pose proof (u64_range src). pose proof (u64_range dst).
eexists. split.
- stepn (ltac:(oF' 0x1267e4%Z)) (ltac:(oD' 0x1267e4%Z)).
stepb_tk (ltac:(oF' 0x1267e8%Z)) (ltac:(oD' 0x1267e8%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
stepn (ltac:(oF' 0x1268f8%Z)) (ltac:(oD' 0x1268f8%Z)).
stepn (ltac:(oF' 0x1268fc%Z)) (ltac:(oD' 0x1268fc%Z)).
stepb_ft (ltac:(oF' 0x126900%Z)) (ltac:(oD' 0x126900%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
apply mst_refl.
- repeat split; gres; rwH; rewrite ?at_0; try reflexivity. solve_keeps.
Qed.
Lemma b1_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyALKB0 "R>&8y5'Q<yR0%211%5241'7&>r2%211'4&?r4(Q:+1(2%33?21%6251r3%93?21r5+;%93E17%<231&=vQ9%2218%A3G41r6+=%A3M1?%D231vM%921E%H3N31&Ez%221A&C%12;IvQ3%O3Q321'5'3'<&B&@&9r:+QTjnL%Q53Q?1Q3/01Q?&:vQ2vLr8%443H21vQ8%<5;:721r1r9%948M7E%@5?3215%C3B51&A%12A6%G231qR>QN1%J2QO1p0L1p0Q11p0Q51p0Q=1p0QF1p0R11pR0R51pR@R81pR<R81").
Proof.
intros regs ret k Hret H1 H11 H13 Hk Hkn.
eexists. split.
- mlbu (ltac:(oF' 0x126bdc%Z)) (ltac:(oD' 0x126bdc%Z)) k.
msb (ltac:(oF' 0x126be0%Z)) (ltac:(oD' 0x126be0%Z)) k ltac:(apply sb_val_plain).
replace (k + 1)%Z with n by lia.
stepret (ltac:(oF' 0x126be4%Z)) (ltac:(oD' 0x126be4%Z)) ret ltac:(exact H1).
apply mst_refl.
- solve_keeps.
Qed.
Lemma t2_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyALKB0 "SB&8y5'Q<yR0%211%5241'7&>r3%211'4&?r5(Q:+1(2%33?21%6251r4%93?21r6+;%93E17%<231&=vQ9%2218%A3G41r7+=%A3M1?%D231vM%921E%H3N31r8+<%H3Q41F%K231&Q;%12Q5L%O3Q531'3&Ez%221I&F&J+2+R0%3221%52O1%:271'6&D%12K7%Q>3QB1<%Q?3QC29%5221%52HQ=%QB3QF1@%QC3QG2Q?%9221r:%E2D1&KvQ3r;%3221&C%@27F%A28QI%3221%QO3R351'5'<&B&@&9r?+QTjm4%R43R>1R2/01R>&:vQ2vLr=%443QG21vQ8%<5;:721r1r>%948QL7J%@5?3215%C3B51&A%12A6%QG231qR>RM1%I2RN1p0K1p0Q51p0Q81p0Q=1p0QD1p0R01p0R81p0R@1p0RI1p0S41pR2S81pR0S91pR@S<1pR<S<1").
Proof.
intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
-
eexists. split.
+ stepn (ltac:(oF' 0x126ba4%Z)) (ltac:(oD' 0x126ba4%Z)).
stepb_ft (ltac:(oF' 0x126ba8%Z)) (ltac:(oD' 0x126ba8%Z)) ltac:(cond).
stepn (ltac:(oF' 0x126bac%Z)) (ltac:(oD' 0x126bac%Z)).
stepb_ft (ltac:(oF' 0x126bb0%Z)) (ltac:(oD' 0x126bb0%Z)) ltac:(cond).
stepret (ltac:(oF' 0x126bb4%Z)) (ltac:(oD' 0x126bb4%Z)) ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126bdc : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x126ba4%Z)) (ltac:(oD' 0x126ba4%Z)).
stepb_ft (ltac:(oF' 0x126ba8%Z)) (ltac:(oD' 0x126ba8%Z)) ltac:(cond).
stepn (ltac:(oF' 0x126bac%Z)) (ltac:(oD' 0x126bac%Z)).
stepb_tk (ltac:(oF' 0x126bb0%Z)) (ltac:(oD' 0x126bb0%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
eexists. split.
+ stepn (ltac:(oF' 0x126ba4%Z)) (ltac:(oD' 0x126ba4%Z)).
stepb_tk (ltac:(oF' 0x126ba8%Z)) (ltac:(oD' 0x126ba8%Z)) ltac:(cond).
mlbu (ltac:(oF' 0x126bb8%Z)) (ltac:(oD' 0x126bb8%Z)) k.
mlbu (ltac:(oF' 0x126bbc%Z)) (ltac:(oD' 0x126bbc%Z)) (k + 1)%Z.
stepn (ltac:(oF' 0x126bc0%Z)) (ltac:(oD' 0x126bc0%Z)).
stepn (ltac:(oF' 0x126bc4%Z)) (ltac:(oD' 0x126bc4%Z)).
msb (ltac:(oF' 0x126bc8%Z)) (ltac:(oD' 0x126bc8%Z)) k ltac:(apply sb_val_plain).
msb (ltac:(oF' 0x126bcc%Z)) (ltac:(oD' 0x126bcc%Z)) (k + 1)%Z ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0x126bd0%Z)) (ltac:(oD' 0x126bd0%Z)).
stepn (ltac:(oF' 0x126bd4%Z)) (ltac:(oD' 0x126bd4%Z)).
stepb_tk (ltac:(oF' 0x126bd8%Z)) (ltac:(oD' 0x126bd8%Z)) ltac:(cond).
stepret (ltac:(oF' 0x126bb4%Z)) (ltac:(oD' 0x126bb4%Z)) ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126bdc : word) (MK (k + 2)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x126ba4%Z)) (ltac:(oD' 0x126ba4%Z)).
stepb_tk (ltac:(oF' 0x126ba8%Z)) (ltac:(oD' 0x126ba8%Z)) ltac:(cond).
mlbu (ltac:(oF' 0x126bb8%Z)) (ltac:(oD' 0x126bb8%Z)) k.
mlbu (ltac:(oF' 0x126bbc%Z)) (ltac:(oD' 0x126bbc%Z)) (k + 1)%Z.
stepn (ltac:(oF' 0x126bc0%Z)) (ltac:(oD' 0x126bc0%Z)).
stepn (ltac:(oF' 0x126bc4%Z)) (ltac:(oD' 0x126bc4%Z)).
msb (ltac:(oF' 0x126bc8%Z)) (ltac:(oD' 0x126bc8%Z)) k ltac:(apply sb_val_plain).
msb (ltac:(oF' 0x126bcc%Z)) (ltac:(oD' 0x126bcc%Z)) (k + 1)%Z ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0x126bd0%Z)) (ltac:(oD' 0x126bd0%Z)).
stepn (ltac:(oF' 0x126bd4%Z)) (ltac:(oD' 0x126bd4%Z)).
stepb_ft (ltac:(oF' 0x126bd8%Z)) (ltac:(oD' 0x126bd8%Z)) ltac:(cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
| gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
Lemma al4_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyALKB0 "SJ&8y5'Q<yR0%211%5241'7'4&?r4(Q:+1(2%33<21%6251r3%93<21r5+;%93B17%<231&=vQ9%2218%A3D41r6+=%A3J1?%D231vM%921E%H3K31r7+<%H3Q11F%K231&Q;%12Q2L%O3Q231'3&Ez%221I&F&J+2+R0%3221%52O1%:271%:29B'6&D+4%22F1%Q@3QA1>%QA3QB23&Cr8%2216vQ3%E221%G261%<281'5'<&B&@&9r<+QTj[0%QM3R41QK/01R4&:vQ2vLr:%443Q@21vQ8%<5;:721r1+QTjm4%R83R?1R6/01R?r9%Q121Q0%M2:1%>4=QJ<1%E5D851:%H3G:1%RB2:R=r;%RE3RH21%RE2=R:%R92R88%RH3RK21%RH2@R5%R<2R4;%RK3RN21%RK2CR1%R02S1@%RN3S121&A%12Q2G%R1231%R2271%R32;1%R42?1%R52C1qR>S81%Q>2S91p0Q@1p0QN1p0R01p0R<1p0RD1p0RL1p0S51pR2S@1pR0SA1pR@SD1pR<SD1").
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
- eexists. split.
+ stepn (ltac:(oF' 0x126960%Z)) (ltac:(oD' 0x126960%Z)).
stepb_tk (ltac:(oF' 0x126964%Z)) (ltac:(oD' 0x126964%Z)) ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn (ltac:(oF' 0x126960%Z)) (ltac:(oD' 0x126960%Z)).
stepb_ft (ltac:(oF' 0x126964%Z)) (ltac:(oD' 0x126964%Z)) ltac:(cond).
mlw (ltac:(oF' 0x126968%Z)) (ltac:(oD' 0x126968%Z)) k.
stepn (ltac:(oF' 0x12696c%Z)) (ltac:(oD' 0x12696c%Z)).
msw (ltac:(oF' 0x126970%Z)) (ltac:(oD' 0x126970%Z)) k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0x126974%Z)) (ltac:(oD' 0x126974%Z)).
stepn (ltac:(oF' 0x126978%Z)) (ltac:(oD' 0x126978%Z)).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.
Lemma al8_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyALKB0 "SL&8y5'Q<yR0%211%5241'7'4&?r5(Q:+1(2%33<21%6251r4%93<21r6+;%93B17%<231&=vQ9%2218%A3D41r7+=%A3J1?%D231vM%921E%H3K31r8+<%H3Q11F%K231&Q;%12Q2L%O3Q231'3&Ez%221I&F&J+2+R0%3221%52O1%:271%:29B'6+8%:2E1%Q?3Q@M=%@221%@24H%QB3QCQ05&Cr9%2218vQ3%F221%H261%I281%>2:1'5'<&B&@&9r=+QTjZ0%QO3R61QM/01R6&:vQ2vLr;%443QB21vQ8%<5;:721r1+QTj[0%R:3RA1R8/01RA%L28K%<4;QJ:1%C5B6318%F3E81%RB28R=r<%RE3RH21%RE2;R:%R92R88%RH3RK21%RH2>R5%R<2R4;%RK3RN21%RK2AR1r:%R12S21%RO3S231&A%12Q1F%R2231%R3281%R42<1%R52@1%R62D1qR>S91%Q=2S:1p0Q?1p0QO1p0R11p0R=1p0RE1p0RM1p0S61pQNSA1pR2SB1pR0SC1pR@SF1pR<SF1").
Proof.
intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
- eexists. split.
+ stepn (ltac:(oF' 0x126940%Z)) (ltac:(oD' 0x126940%Z)).
stepb_tk (ltac:(oF' 0x126944%Z)) (ltac:(oD' 0x126944%Z)) ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn (ltac:(oF' 0x126940%Z)) (ltac:(oD' 0x126940%Z)).
stepb_ft (ltac:(oF' 0x126944%Z)) (ltac:(oD' 0x126944%Z)) ltac:(cond).
mlw (ltac:(oF' 0x126948%Z)) (ltac:(oD' 0x126948%Z)) k.
mlw (ltac:(oF' 0x12694c%Z)) (ltac:(oD' 0x12694c%Z)) (k + 4)%Z.
msw (ltac:(oF' 0x126950%Z)) (ltac:(oD' 0x126950%Z)) k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0x126954%Z)) (ltac:(oD' 0x126954%Z)) (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0x126958%Z)) (ltac:(oD' 0x126958%Z)).
stepn (ltac:(oF' 0x12695c%Z)) (ltac:(oD' 0x12695c%Z)).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.
Lemma al_loop : ltac2:(TCodec.tc2 tcn__AsanMemcpyALKB0 "T0'0&8y5'Q<yR0%211%5241'7'4&?r3(Q:+1(2%33<21%6251r2%93<21r4+;%93B17%<231&=vQ9%2218%A3D41r5+=%A3J1?%D231vM%921E%H3K31r6+<%H3Q11F%K231&Q;&KvQ3%221F%42Q51%Q23Q561r7+>%Q23Q;1Q0%Q5231+?%;2Q<1%Q93Q<31&Ez%221C'3&H+@&C&Ir:%211%421Q@%7261%H2GC%=221&F%924:%2241%>241'5'<&B&@&9r;+QTjX@%R03R71QN/01R7&:vQ2vLr9%443QC21vQ8%<5;:721r1+QTjZ0%R;3RB1R9/01RBr<%Q011%Q221R>%Q52Q41%Q42<1%@4?QO>1%G5F:71<%J3I<1%RG2<RB%RI3RL1Q7%RI2>R>%R=2R<7%RL3RO21%RL2AR9%R@2R8:%RO3S221%RO2DR5%R32R2=%R52S61%S33S631&A%12Q4I%QI231%QJ281%QK2<1%QL2@1%QM2C1qR>S=1%Q@2S>1p0QB1p0R21p0R61p0R>1p0RI1p0S11p0S:1pR0SE1pR@SH1pR<SH1pR:SO1").
Proof.
induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
-
eexists. split.
+ mlw (ltac:(oF' 0x126910%Z)) (ltac:(oD' 0x126910%Z)) k.
mlw (ltac:(oF' 0x126914%Z)) (ltac:(oD' 0x126914%Z)) (k + 4)%Z.
mlw (ltac:(oF' 0x126918%Z)) (ltac:(oD' 0x126918%Z)) (k + 8)%Z.
mlw (ltac:(oF' 0x12691c%Z)) (ltac:(oD' 0x12691c%Z)) (k + 12)%Z.
stepn (ltac:(oF' 0x126920%Z)) (ltac:(oD' 0x126920%Z)).
stepn (ltac:(oF' 0x126924%Z)) (ltac:(oD' 0x126924%Z)).
msw (ltac:(oF' 0x126928%Z)) (ltac:(oD' 0x126928%Z)) k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0x12692c%Z)) (ltac:(oD' 0x12692c%Z)) (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0x126930%Z)) (ltac:(oD' 0x126930%Z)) (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0x126934%Z)) (ltac:(oD' 0x126934%Z)) (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0x126938%Z)) (ltac:(oD' 0x126938%Z)).
stepb_ft (ltac:(oF' 0x12693c%Z)) (ltac:(oD' 0x12693c%Z)) ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
* unfold v_addi. unorm. f_equal. lia.
* solve_keeps.
- eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126910 : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
/\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* mlw (ltac:(oF' 0x126910%Z)) (ltac:(oD' 0x126910%Z)) k.
mlw (ltac:(oF' 0x126914%Z)) (ltac:(oD' 0x126914%Z)) (k + 4)%Z.
mlw (ltac:(oF' 0x126918%Z)) (ltac:(oD' 0x126918%Z)) (k + 8)%Z.
mlw (ltac:(oF' 0x12691c%Z)) (ltac:(oD' 0x12691c%Z)) (k + 12)%Z.
stepn (ltac:(oF' 0x126920%Z)) (ltac:(oD' 0x126920%Z)).
stepn (ltac:(oF' 0x126924%Z)) (ltac:(oD' 0x126924%Z)).
msw (ltac:(oF' 0x126928%Z)) (ltac:(oD' 0x126928%Z)) k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0x12692c%Z)) (ltac:(oD' 0x12692c%Z)) (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0x126930%Z)) (ltac:(oD' 0x126930%Z)) (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw (ltac:(oF' 0x126934%Z)) (ltac:(oD' 0x126934%Z)) (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0x126938%Z)) (ltac:(oD' 0x126938%Z)).
stepb_tk (ltac:(oF' 0x12693c%Z)) (ltac:(oD' 0x12693c%Z)) ltac:(unfold v_addi; cond).
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
Lemma al16_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyALKB0 "S9&8y5'Q<yR0%211%5241'7'4&?r3(Q:+1(2%33<21%6251r2%93<21r4+;%93B17%<231&=vQ9%2218%A3D41r5+=%A3J1?%D231vM%921E%H3K31r6+<%H3Q11F%K231&Q;&KvQ3%221F%42Q51%Q23Q561'3&Ez%221D%32E8%5221'5'<&B&@&9r9+QTjX4%Q=3QD1Q;/01QD&:vQ2vLr7%443Q021vQ8%<5;:721r1+QTjZ0%QH3QO1QF/01QO&G%Q02O9+@%3221%Q32Q21%@4?Q<>1%G5F:71<%J3I<1%R42<QOr8%R73R:21%R72?QL%QK2QJ8%R:3R=21%R:2BQG%QN2QF;%R=3R@21%R=2EQC%QB2RC?%R@3RC21&A%12Q4I%Q@231%QA271%QB2;1%QC2?1%QD2C1qR>RJ1%Q@2RK1p0QB1p0QI1p0R41p0R<1p0RE1pR0S01pR@S31pR<S31").
Proof.
intros regs ret k H1 H11 H13 H12 Hk.
destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
-
eexists. split.
+ stepn (ltac:(oF' 0x126904%Z)) (ltac:(oD' 0x126904%Z)).
stepb_tk (ltac:(oF' 0x126908%Z)) (ltac:(oD' 0x126908%Z)) ltac:(cond).
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
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126910 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
/\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x126904%Z)) (ltac:(oD' 0x126904%Z)).
stepb_ft (ltac:(oF' 0x126908%Z)) (ltac:(oD' 0x126908%Z)) ltac:(cond).
stepn (ltac:(oF' 0x12690c%Z)) (ltac:(oD' 0x12690c%Z)).
apply mst_refl.
* cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.
Theorem memcpy_aligned : ltac2:(TCodec.tc2 tcn__AsanMemcpyALKB0 "RC&8y5'Q<yR0%211%5241&>r1%211'4&?r3(Q:+1(2%33>21%6251r2%93>21r4+:%93D17%<231vM%?3D21r5+;%?3J1=%B231vQ9%E3J21r6+<%E3Q01C%H231&Q;vQ3%22Q21%M3Q241'7&G&Q=%12Q7=+4%4221z%Q53721%62Q<H%8215%Q83:14'5'3'<&B&@&9r:+QTio4%Q>3QG1Q</01QGvQ2vQ8%8576321r9&;vL%236Q;1%=5<QL416%@3?61&A%12>QO%D231qR>R31%G2R41p0I1p0M1p0Q61p0Q?1p0QF1p0QM1p0R81pR@R=1pR<R=1").
Proof.
intros regs ret Hret H1 H10 H11 H12 Hs4 Hd4.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
set (m := (n mod 16)%Z).
pose proof (Z.mod_pos_bound n 16 ltac:(lia)) as Hm16.
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (Hl16 : Z.land m 16 = 0%Z).
{ destruct B16 as [E|E]; [exact E|]. exfalso.
pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126904 : word) (MK 0) rom)
(fun r => getr r 13 = at_ dst 0 /\ getr r 11 = at_ src 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ getr r 1 = ret /\ keeps regs r)).
{ destruct (al_entry regs (MK 0) H10 H11 Hs4 Hd4) as (r & R & P). exists r. split; [exact R|].
decompose [and] P. rewrite Z.sub_0_r. repeat split; try assumption; congruence. }
cbv beta. intros r1 (R13 & R11 & R12 & R1 & K1).
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126940 : word) (MK (n - m)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al16_run r1 ret 0 R1 R11 R13 R12 ltac:(lia)) as (r & R & P). exists r.
subst m. rewrite Z.sub_0_r in R, P. split; [exact R|]. decompose [and] P. repeat split; try assumption.
eapply keeps_trans; eassumption. }
cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126960 : word) (MK (n - m + Z.land m 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al8_run r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r & R & P).
{ pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126ba4 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
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
End AL.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
