(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib Ja0MemcpyBase Ja0MemcpyAL Ja0MemcpyMIS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__muslA_Ja0MemcpyC1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.muslA.Ja0MemcpyBase."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "5msteps"; "6at_"; "7getr"; "7mkst"; "8LWv"; "8keeps"; "9memk"; "9sb_"; ":loaded_segments"]; [";add"; ";land"; ";le"; ";lt"; ";mul"; ";of_nat"; ";sub"; "0bs"; "0dst"; "0fx"; "0ja"; "0jw"; "0k"; "0kk"; "0m"; "0mem0"]; ["0n"; "0q"; "0regs"; "0regs'"; "0ret"; "0rom"; "0src"; "<BV"; "<Z_to_bv"; "<bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Section C1.
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
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].
Section SE.
Local Abbreviation SEC_T_c1_pro := (ltac2:(TCodec.tc2 tcn__muslA_Ja0MemcpyC1 "T1&6y5'Q9yR0%211%5241'5'3&9r3(Q7+1(1%33<21%6251r2%93<21r4+;%93B17%<231&8vQ6%2218%A3D41r5+=%A3J1?%D231vH%921E%H3K31r6+<%H3Q11F%K231&Q8&FvQ0%221F%42Q51%Q23Q561r7+?%Q23Q;1Q0%Q5231%:2Q;Q3%Q83Q;21&Bz%221B+Q0%?2>:%5221'4'2'7&?&:vIr;+QTba0%QD3QK1QB/01QK&=vOvGr9%443Q721vQ5%<5;:721r1+QTbo<%QO3R61QM/01R6&@+3%22:1%>4=QA<1%E5D851:%H3G:1%R92:R4r:%R<3R?21%R<2=R1+@%;2C1%R22R11%RA3RD41%RA2BQN%R52QM=%RD3RG21%RD2EQJ%QH2QG@%QJ2RK1%RH3RK31+>%RG3S01RE%RJ2K1&;&>u4%23Q4Q31%411%S13S461%S12Q2QM%R62S7E%S43S721&<%12QAQ6%QG231%QH271%QI2A1%QJ2F1%QK2J1%QL2Q01%QM2Q41qR8S@1%R02SA1p0R21p0R61p0R:1p0RA1p0RL1p0S41p0S=1pQJSH1pR:SK1pR6SK1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c1_pro) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_c1_pro) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_c1_pro) 2%nat 0%nat).
Lemma c1_pro : ltac:(sec_stmt2 constr:(SEC_T_c1_pro) 3%nat 0%nat).
Proof.
intros H1 H11 H13 H12 H15 Hk Hnk.
eexists. split.
- mlw (ltac:(oF' 0x124a20%Z)) (ltac:(oD' 0x124a20%Z)) k.
stepn (ltac:(oF' 0x124a24%Z)) (ltac:(oD' 0x124a24%Z)).
stepb_ft (ltac:(oF' 0x124a28%Z)) (ltac:(oD' 0x124a28%Z)) ltac:(cond).
stepn (ltac:(oF' 0x124a2c%Z)) (ltac:(oD' 0x124a2c%Z)).
stepb_tk (ltac:(oF' 0x124a30%Z)) (ltac:(oD' 0x124a30%Z)) ltac:(cond).
stepn (ltac:(oF' 0x124bc8%Z)) (ltac:(oD' 0x124bc8%Z)).
stepn (ltac:(oF' 0x124bcc%Z)) (ltac:(oD' 0x124bcc%Z)).
stepn (ltac:(oF' 0x124bd0%Z)) (ltac:(oD' 0x124bd0%Z)).
msb (ltac:(oF' 0x124bd4%Z)) (ltac:(oD' 0x124bd4%Z)) k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb (ltac:(oF' 0x124bd8%Z)) (ltac:(oD' 0x124bd8%Z)) (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
msb (ltac:(oF' 0x124bdc%Z)) (ltac:(oD' 0x124bdc%Z)) (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0x124be0%Z)) (ltac:(oD' 0x124be0%Z)).
stepn (ltac:(oF' 0x124be4%Z)) (ltac:(oD' 0x124be4%Z)).
stepn (ltac:(oF' 0x124be8%Z)) (ltac:(oD' 0x124be8%Z)).
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.
End SE.
Lemma c1_loop : ltac2:(TCodec.tc2 tcn__muslA_Ja0MemcpyC1 "TH'0&6y5'Q9yR0%211%5241'5'3&9r5(Q7+1(1%33<21%6251r4%93<21r6+;%93B17%<231&8vQ6r3%3221%B3E51r7+=%B3K1@%E231vH%:21F%I3L31r8+<%I3Q21G%L231&Q8&FvQ0%221G%42Q61%Q33Q661r9+>%Q33Q<1Q1%Q6231&;&>vGu4%332Q:1%511%Q>3QA71r:+?%Q>3QG1Q<%QA231+@%F2QH1%QE3QH31&@%12CQ3%QH3QIN1+3%K2;1%QK3QLQ11&Br;%2251'2&D&Er?%211%>21R0%52B1%@21R2r<%Q92Q81%=231&C+A%F271%3251%?251'4'7&?&:vIr@+QTbo<%RC3RJ1RA/01RJ&=vOr>%342R4QA1vQ5%;5:9621r1+QTcR<%RM3S41RK/01S4rA%Q211%Q>21S0%Q52QB1%Q@2<1%?4>R@QM1%F5E:71<%I3H<1%S92<S4%S;3S>1Q9%S;2>S0%QG27RI%S02RO1%S?3SB31%S?2BRK%S32RJ;%SB3SE21%SB2ERG%RE2RD>%RG2SI1%SF3SI31&<%12Q4J%QJ231%QK281%QL2<1%QM2A1%QN2D1qR8T01%Q@2T11p0QB1p0R31p0R71p0R;1p0R?1p0RG1p0S31p0S>1p0SF1p0T01pQHT;1pQFT<1pQLT=1pR:T@1pR6T@1pR4TG1").
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn (ltac:(oF' 0x124bec%Z)) (ltac:(oD' 0x124bec%Z)).
mlw (ltac:(oF' 0x124bf0%Z)) (ltac:(oD' 0x124bf0%Z)) (kk + 1)%Z.
mlw (ltac:(oF' 0x124bf4%Z)) (ltac:(oD' 0x124bf4%Z)) (kk + 5)%Z.
mlw (ltac:(oF' 0x124bf8%Z)) (ltac:(oD' 0x124bf8%Z)) (kk + 9)%Z.
mlw (ltac:(oF' 0x124bfc%Z)) (ltac:(oD' 0x124bfc%Z)) (kk + 13)%Z.
stepn (ltac:(oF' 0x124c00%Z)) (ltac:(oD' 0x124c00%Z)). stepn (ltac:(oF' 0x124c04%Z)) (ltac:(oD' 0x124c04%Z)). stepn (ltac:(oF' 0x124c08%Z)) (ltac:(oD' 0x124c08%Z)).
stepn (ltac:(oF' 0x124c0c%Z)) (ltac:(oD' 0x124c0c%Z)). stepn (ltac:(oF' 0x124c10%Z)) (ltac:(oD' 0x124c10%Z)). stepn (ltac:(oF' 0x124c14%Z)) (ltac:(oD' 0x124c14%Z)).
stepn (ltac:(oF' 0x124c18%Z)) (ltac:(oD' 0x124c18%Z)). stepn (ltac:(oF' 0x124c1c%Z)) (ltac:(oD' 0x124c1c%Z)). stepn (ltac:(oF' 0x124c20%Z)) (ltac:(oD' 0x124c20%Z)).
stepn (ltac:(oF' 0x124c24%Z)) (ltac:(oD' 0x124c24%Z)). stepn (ltac:(oF' 0x124c28%Z)) (ltac:(oD' 0x124c28%Z)).
stepn (ltac:(oF' 0x124c2c%Z)) (ltac:(oD' 0x124c2c%Z)).
msw (ltac:(oF' 0x124c30%Z)) (ltac:(oD' 0x124c30%Z)) kk ltac:(m24).
msw (ltac:(oF' 0x124c34%Z)) (ltac:(oD' 0x124c34%Z)) (kk + 4)%Z ltac:(m24).
msw (ltac:(oF' 0x124c38%Z)) (ltac:(oD' 0x124c38%Z)) (kk + 8)%Z ltac:(m24).
msw (ltac:(oF' 0x124c3c%Z)) (ltac:(oD' 0x124c3c%Z)) (kk + 12)%Z ltac:(m24).
stepn (ltac:(oF' 0x124c40%Z)) (ltac:(oD' 0x124c40%Z)).
stepn (ltac:(oF' 0x124c44%Z)) (ltac:(oD' 0x124c44%Z)).
stepb_ft (ltac:(oF' 0x124c48%Z)) (ltac:(oD' 0x124c48%Z)) ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x124bec : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
/\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x124bec%Z)) (ltac:(oD' 0x124bec%Z)).
mlw (ltac:(oF' 0x124bf0%Z)) (ltac:(oD' 0x124bf0%Z)) (kk + 1)%Z.
mlw (ltac:(oF' 0x124bf4%Z)) (ltac:(oD' 0x124bf4%Z)) (kk + 5)%Z.
mlw (ltac:(oF' 0x124bf8%Z)) (ltac:(oD' 0x124bf8%Z)) (kk + 9)%Z.
mlw (ltac:(oF' 0x124bfc%Z)) (ltac:(oD' 0x124bfc%Z)) (kk + 13)%Z.
stepn (ltac:(oF' 0x124c00%Z)) (ltac:(oD' 0x124c00%Z)). stepn (ltac:(oF' 0x124c04%Z)) (ltac:(oD' 0x124c04%Z)). stepn (ltac:(oF' 0x124c08%Z)) (ltac:(oD' 0x124c08%Z)).
stepn (ltac:(oF' 0x124c0c%Z)) (ltac:(oD' 0x124c0c%Z)). stepn (ltac:(oF' 0x124c10%Z)) (ltac:(oD' 0x124c10%Z)). stepn (ltac:(oF' 0x124c14%Z)) (ltac:(oD' 0x124c14%Z)).
stepn (ltac:(oF' 0x124c18%Z)) (ltac:(oD' 0x124c18%Z)). stepn (ltac:(oF' 0x124c1c%Z)) (ltac:(oD' 0x124c1c%Z)). stepn (ltac:(oF' 0x124c20%Z)) (ltac:(oD' 0x124c20%Z)).
stepn (ltac:(oF' 0x124c24%Z)) (ltac:(oD' 0x124c24%Z)). stepn (ltac:(oF' 0x124c28%Z)) (ltac:(oD' 0x124c28%Z)).
stepn (ltac:(oF' 0x124c2c%Z)) (ltac:(oD' 0x124c2c%Z)).
msw (ltac:(oF' 0x124c30%Z)) (ltac:(oD' 0x124c30%Z)) kk ltac:(m24).
msw (ltac:(oF' 0x124c34%Z)) (ltac:(oD' 0x124c34%Z)) (kk + 4)%Z ltac:(m24).
msw (ltac:(oF' 0x124c38%Z)) (ltac:(oD' 0x124c38%Z)) (kk + 8)%Z ltac:(m24).
msw (ltac:(oF' 0x124c3c%Z)) (ltac:(oD' 0x124c3c%Z)) (kk + 12)%Z ltac:(m24).
stepn (ltac:(oF' 0x124c40%Z)) (ltac:(oD' 0x124c40%Z)).
stepn (ltac:(oF' 0x124c44%Z)) (ltac:(oD' 0x124c44%Z)).
stepb_tk (ltac:(oF' 0x124c48%Z)) (ltac:(oD' 0x124c48%Z)) ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Section SE.
Local Abbreviation SEC_T_c1_exit := (ltac2:(TCodec.tc2 tcn__muslA_Ja0MemcpyC1 "SI&6y5'Q9yR0%211%5241'5'3&9r3(Q7+1(1%33<21%6251r2%93<21r4+;%93B17%<231&8vQ6&@+=%22:1%5241%D3G71r5%C3L5A%F221vH%;21G%J3M31r6+<%J3Q31H%M231&Q8&FvQ0%221H%42Q71%Q43Q761&Bz%221B&C%928>+Q0%3221r7%821<r8%?2>1'4'2'7&?&:vIr<+QTcR<%QE3QL1QC/01QL&=vOvGr:%443Q621vQ5%<5;:721r1+QTc[<%R03R71QN/01R7&A+@%22QO1%QH2;1+8%52R21%QK231+4%82R51%QN231%E4DQGC1%L5K?<1A%O3NA1%RA2AR<r;%RD3RG21%RD2DR9%R82R78%RG3RJ21%RG2GR2%R;2R1;%RJ3RM21%RJ2JQN%QM2S0RD%RM3S021&<%12Q9N%Q?231%Q@271%QA2;1%QB2?1%QC2C1qR8S71%QF2S81tQNS8QH1p0QK1p0QN1p0R31p0R71p0RB1p0RI1p0S51pQLS@1pR:SC1pR6SC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c1_exit) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_c1_exit) 1%nat 0%nat).
Variable kk : ltac:(sec_ty2 constr:(SEC_T_c1_exit) 2%nat 0%nat).
Lemma c1_exit : ltac:(sec_stmt2 constr:(SEC_T_c1_exit) 3%nat 0%nat).
Proof.
intros H1 H11 H13 H12 Hkk Hm Hkn m.
subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x124a0c : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x124c4c%Z)) (ltac:(oD' 0x124c4c%Z)).
stepn (ltac:(oF' 0x124c50%Z)) (ltac:(oD' 0x124c50%Z)).
stepb_tk (ltac:(oF' 0x124c54%Z)) (ltac:(oD' 0x124c54%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x124c58 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x124c4c%Z)) (ltac:(oD' 0x124c4c%Z)).
stepn (ltac:(oF' 0x124c50%Z)) (ltac:(oD' 0x124c50%Z)).
stepb_ft (ltac:(oF' 0x124c54%Z)) (ltac:(oD' 0x124c54%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x124ce4 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
End SE.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section SE.
Local Abbreviation SEC_T_c1_run := (ltac2:(TCodec.tc2 tcn__muslA_Ja0MemcpyC1 "SK&6y5'Q9yR0%211%5241'5'3&9r3(Q7+1(1%33<21%6251r2%93<21r4+;%93B17%<231&8vQ6%2218%A3D41r5+=%A3J1?%D231vH%921E%H3K31r6+<%H3Q11F%K231&Q8&FvQ0%221F%42Q51%Q23Q561r7+?%Q23Q;1Q0%Q5231%:2Q;Q3%Q83Q;21&Bz%221B+Q0%?2>:%5221'4'2'7&?&:vIr<+QTba0%QD3QK1QB/01QK&=vOvGr:%443Q721vQ5%<5;:721+QTc[<%QN3R51QL/01R5&@&Ar1+2%3221%423R4%6221%Q<2Q;1%B4AQE@1%I5HR4:1>%L3K>1%Q52Q49&C%12;Q4%Q1231%RA2R:R<r;%RD3RG21%RD2R=R9%R82R7<%RG3RJ21%RG2R@R4%R;2R3?%RJ3RM21%RJ2RCR0%QO2S0G%RM3S021&<%12Q:RG%Q@231%QA271%QB2;1%QC2?1%QD2C1%QE2H1qQNS71%QH2S81qR8S:1%QJ2S;1p0QL1p0R01p0R41p0R;1p0RF1p0RN1p0S71pQJSB1pR:SE1pR6SE1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c1_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_c1_run) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_c1_run) 2%nat 0%nat).
Lemma c1_run : ltac:(sec_stmt2 constr:(SEC_T_c1_run) 3%nat 0%nat).
Proof.
intros H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.
End SE.
End C1.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
