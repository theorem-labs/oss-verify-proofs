(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib AsanMemcpyBaseK AsanMemcpyALK AsanMemcpyMISK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMemcpyC2K () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemcpyBaseK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemcpyC2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "5memk"; "5sb_"; "6asanreflect_fx"; "7msteps"; "8at_"; "9getr"; "9mkst"; ":LWv"; ":keeps"]; [";loaded_segments"; "<add"; "<land"; "<le"; "<lt"; "<mul"; "<of_nat"; "<sub"; "0bs"; "0dst"; "0ja"; "0jw"; "0k"; "0kk"; "0m"; "0mem0"]; ["0n"; "0q"; "0regs"; "0regs'"; "0ret"; "0rom"; "0src"; "=BV"; "=Z_to_bv"; "=bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section C2.
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
Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].
Lemma c2_pro : ltac2:(TCodec.tc2 tcn__AsanMemcpyC2K "T2&6y5'Q9yR0%211%5241'5'3&<r3(Q7+1(1%33<21%6251r2%93<21r4+;%93B17%<231&;vQ6%2218%A3D41r5+=%A3J1?%D231vI%921E%H3K31r6+<%H3Q11F%K231&Q8&GvQ0%221F%42Q51%Q23Q561r7+?%Q23Q;1Q0%Q5231+2%;2Q<1%Q93Q<31&Cz%221C+Q0%@2?;%5221'4'2':&@&=&9r;+QTba0%QE3QL1QC/01QL&7vOvHr9%443Q821vQ5%<5;:721r1+QTbb@%R03R71QN/01R7&A%129O%=4<QA;1%D5C7419%G3F91%R929R4r:%R<3R?21%R<2<R1+@%:2B1%R22R11%RA3RD41%RA2AQN%R52QM=%RD3RG21%RD2DQJ%QH2QG@%QJ2RK1%RH3RK31+>%RG3S01RE%RJ2J1&>&8u4%23Q3Q21%411%S13S461%S12Q1QM+A%R72S81%S53S831&?%12QAQ6%QG231%QH281%QI2B1%QJ2G1%QK2K1%QL2Q11%QM2Q51qR8SA1%R02SB1p0R21p0R61p0R:1p0RB1p0RM1p0S51p0S>1pQJSI1pR:SL1pR6SL1").
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw (ltac:(oF' 0x124a20%Z)) (ltac:(oD' 0x124a20%Z)) k.
stepn (ltac:(oF' 0x124a24%Z)) (ltac:(oD' 0x124a24%Z)).
stepb_ft (ltac:(oF' 0x124a28%Z)) (ltac:(oD' 0x124a28%Z)) ltac:(cond).
stepn (ltac:(oF' 0x124a2c%Z)) (ltac:(oD' 0x124a2c%Z)).
stepb_ft (ltac:(oF' 0x124a30%Z)) (ltac:(oD' 0x124a30%Z)) ltac:(cond).
stepn (ltac:(oF' 0x124a34%Z)) (ltac:(oD' 0x124a34%Z)).
stepn (ltac:(oF' 0x124a38%Z)) (ltac:(oD' 0x124a38%Z)).
msb (ltac:(oF' 0x124a3c%Z)) (ltac:(oD' 0x124a3c%Z)) k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb (ltac:(oF' 0x124a40%Z)) (ltac:(oD' 0x124a40%Z)) (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
stepn (ltac:(oF' 0x124a44%Z)) (ltac:(oD' 0x124a44%Z)).
stepn (ltac:(oF' 0x124a48%Z)) (ltac:(oD' 0x124a48%Z)).
stepn (ltac:(oF' 0x124a4c%Z)) (ltac:(oD' 0x124a4c%Z)).
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.
Lemma c2_loop : ltac2:(TCodec.tc2 tcn__AsanMemcpyC2K "TI'0&6y5'Q9yR0%211%5241'5'3&<r5(Q7+1(1%33<21%6251r4%93<21r6+;%93B17%<231&;vQ6r3%3221%B3E51r7+=%B3K1@%E231vI%:21F%I3L31r8+<%I3Q21G%L231&Q8&GvQ0%221G%42Q61%Q33Q661r9+>%Q33Q<1Q1%Q6231&>&8vHu4%332Q:1%511%Q>3QA71r:+?%Q>3QG1Q<%QA231+A%F2QH1%QE3QH31&A%12CB%QH3QIN1+2%K2;1%QK3QLQ11&Cr;%2251'2&E+@&Fr?%211%?21R1%6251%A21>r<%Q:2Q91%>231&D+B%G271%3251%@251'4':&@&=&9r@+QTbb@%RD3RK1RB/01RK&7vOr>%342R5QB1vQ5%;5:9621r1+QTbe@%RN3S51RL/01S5rA%Q211%Q?21S1%Q62Q51%QA2<1%?4>RAQN1%F5E:71<%I3H<1%S:2<S5%S<3S?1Q9%S<2>S1%QH27R9%S12S01%S@3SC31%S@2BRL%S42RK;%SC3SF21%SC2ERH%RF2RE>%RH2SJ1%SG3SJ31&?%12Q4J%QK231%QL281%QM2<1%QN2A1%QO2D1qR8T11%Q@2T21p0QB1p0R41p0R81p0R<1p0R@1p0RH1p0S41p0S?1p0SG1p0T11pQHT<1pQFT=1pQLT>1pR:TA1pR6TA1pR4TH1").
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn (ltac:(oF' 0x124a50%Z)) (ltac:(oD' 0x124a50%Z)).
mlw (ltac:(oF' 0x124a54%Z)) (ltac:(oD' 0x124a54%Z)) (kk + 2)%Z.
mlw (ltac:(oF' 0x124a58%Z)) (ltac:(oD' 0x124a58%Z)) (kk + 6)%Z.
mlw (ltac:(oF' 0x124a5c%Z)) (ltac:(oD' 0x124a5c%Z)) (kk + 10)%Z.
mlw (ltac:(oF' 0x124a60%Z)) (ltac:(oD' 0x124a60%Z)) (kk + 14)%Z.
stepn (ltac:(oF' 0x124a64%Z)) (ltac:(oD' 0x124a64%Z)). stepn (ltac:(oF' 0x124a68%Z)) (ltac:(oD' 0x124a68%Z)). stepn (ltac:(oF' 0x124a6c%Z)) (ltac:(oD' 0x124a6c%Z)).
stepn (ltac:(oF' 0x124a70%Z)) (ltac:(oD' 0x124a70%Z)). stepn (ltac:(oF' 0x124a74%Z)) (ltac:(oD' 0x124a74%Z)). stepn (ltac:(oF' 0x124a78%Z)) (ltac:(oD' 0x124a78%Z)).
stepn (ltac:(oF' 0x124a7c%Z)) (ltac:(oD' 0x124a7c%Z)). stepn (ltac:(oF' 0x124a80%Z)) (ltac:(oD' 0x124a80%Z)). stepn (ltac:(oF' 0x124a84%Z)) (ltac:(oD' 0x124a84%Z)).
stepn (ltac:(oF' 0x124a88%Z)) (ltac:(oD' 0x124a88%Z)). stepn (ltac:(oF' 0x124a8c%Z)) (ltac:(oD' 0x124a8c%Z)).
stepn (ltac:(oF' 0x124a90%Z)) (ltac:(oD' 0x124a90%Z)).
msw (ltac:(oF' 0x124a94%Z)) (ltac:(oD' 0x124a94%Z)) kk ltac:(m16).
msw (ltac:(oF' 0x124a98%Z)) (ltac:(oD' 0x124a98%Z)) (kk + 4)%Z ltac:(m16).
msw (ltac:(oF' 0x124a9c%Z)) (ltac:(oD' 0x124a9c%Z)) (kk + 8)%Z ltac:(m16).
msw (ltac:(oF' 0x124aa0%Z)) (ltac:(oD' 0x124aa0%Z)) (kk + 12)%Z ltac:(m16).
stepn (ltac:(oF' 0x124aa4%Z)) (ltac:(oD' 0x124aa4%Z)).
stepn (ltac:(oF' 0x124aa8%Z)) (ltac:(oD' 0x124aa8%Z)).
stepb_ft (ltac:(oF' 0x124aac%Z)) (ltac:(oD' 0x124aac%Z)) ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x124a50 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
/\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x124a50%Z)) (ltac:(oD' 0x124a50%Z)).
mlw (ltac:(oF' 0x124a54%Z)) (ltac:(oD' 0x124a54%Z)) (kk + 2)%Z.
mlw (ltac:(oF' 0x124a58%Z)) (ltac:(oD' 0x124a58%Z)) (kk + 6)%Z.
mlw (ltac:(oF' 0x124a5c%Z)) (ltac:(oD' 0x124a5c%Z)) (kk + 10)%Z.
mlw (ltac:(oF' 0x124a60%Z)) (ltac:(oD' 0x124a60%Z)) (kk + 14)%Z.
stepn (ltac:(oF' 0x124a64%Z)) (ltac:(oD' 0x124a64%Z)). stepn (ltac:(oF' 0x124a68%Z)) (ltac:(oD' 0x124a68%Z)). stepn (ltac:(oF' 0x124a6c%Z)) (ltac:(oD' 0x124a6c%Z)).
stepn (ltac:(oF' 0x124a70%Z)) (ltac:(oD' 0x124a70%Z)). stepn (ltac:(oF' 0x124a74%Z)) (ltac:(oD' 0x124a74%Z)). stepn (ltac:(oF' 0x124a78%Z)) (ltac:(oD' 0x124a78%Z)).
stepn (ltac:(oF' 0x124a7c%Z)) (ltac:(oD' 0x124a7c%Z)). stepn (ltac:(oF' 0x124a80%Z)) (ltac:(oD' 0x124a80%Z)). stepn (ltac:(oF' 0x124a84%Z)) (ltac:(oD' 0x124a84%Z)).
stepn (ltac:(oF' 0x124a88%Z)) (ltac:(oD' 0x124a88%Z)). stepn (ltac:(oF' 0x124a8c%Z)) (ltac:(oD' 0x124a8c%Z)).
stepn (ltac:(oF' 0x124a90%Z)) (ltac:(oD' 0x124a90%Z)).
msw (ltac:(oF' 0x124a94%Z)) (ltac:(oD' 0x124a94%Z)) kk ltac:(m16).
msw (ltac:(oF' 0x124a98%Z)) (ltac:(oD' 0x124a98%Z)) (kk + 4)%Z ltac:(m16).
msw (ltac:(oF' 0x124a9c%Z)) (ltac:(oD' 0x124a9c%Z)) (kk + 8)%Z ltac:(m16).
msw (ltac:(oF' 0x124aa0%Z)) (ltac:(oD' 0x124aa0%Z)) (kk + 12)%Z ltac:(m16).
stepn (ltac:(oF' 0x124aa4%Z)) (ltac:(oD' 0x124aa4%Z)).
stepn (ltac:(oF' 0x124aa8%Z)) (ltac:(oD' 0x124aa8%Z)).
stepb_tk (ltac:(oF' 0x124aac%Z)) (ltac:(oD' 0x124aac%Z)) ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma c2_exit : ltac2:(TCodec.tc2 tcn__AsanMemcpyC2K "SJ&6y5'Q9yR0%211%5241'5'3&<r3(Q7+1(1%33<21%6251r2%93<21r4+;%93B17%<231&;vQ6&A+>%22:1%5241%D3G71r5+=%D3M1B%G231vI%<21H%K3N31r6+<%K3Q41I%N231&Q8&GvQ0%221I%42Q81%Q53Q861&Cz%221C&D%928>+Q0%3221r7%821<r8%?2>1'4'2':&@&=&9r<+QTbe@%QF3QM1QD/01QM&7vOvHr:%443Q621vQ5%<5;:721r1+QTc[<%R13R81QO/01R8&B+@%22R01%QI2;1+8%52R31%QL231+4%82R61%QO231%E4DQGC1%L5K?<1A%O3NA1%RB2AR=r;%RE3RH21%RE2DR:%R92R88%RH3RK21%RH2GR2%R<2R1;%RK3RN21%RK2JQN%QM2S1RE%RN3S121&?%12Q9N%Q?231%Q@271%QA2;1%QB2?1%QC2C1qR8S81%QF2S91tQNS9QH1p0QK1p0QN1p0R31p0R71p0RB1p0RJ1p0S61pQLSA1pR:SD1pR6SD1").
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x124a0c : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x124ab0%Z)) (ltac:(oD' 0x124ab0%Z)).
stepn (ltac:(oF' 0x124ab4%Z)) (ltac:(oD' 0x124ab4%Z)).
stepb_tk (ltac:(oF' 0x124ab8%Z)) (ltac:(oD' 0x124ab8%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x124c58 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x124ab0%Z)) (ltac:(oD' 0x124ab0%Z)).
stepn (ltac:(oF' 0x124ab4%Z)) (ltac:(oD' 0x124ab4%Z)).
stepb_ft (ltac:(oF' 0x124ab8%Z)) (ltac:(oD' 0x124ab8%Z)) ltac:(cond).
stepn (ltac:(oF' 0x124abc%Z)) (ltac:(oD' 0x124abc%Z)).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x124ce4 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma c2_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyC2K "SK&6y5'Q9yR0%211%5241'5'3&<r3(Q7+1(1%33<21%6251r2%93<21r4+;%93B17%<231&;vQ6%2218%A3D41r5+=%A3J1?%D231vI%921E%H3K31r6+<%H3Q11F%K231&Q8&GvQ0%221F%42Q51%Q23Q561r7+?%Q23Q;1Q0%Q5231+2%;2Q<1%Q93Q<31&Cz%221C+Q0%@2?;%5221'4'2':&@&=&9r<+QTba0%QE3QL1QC/01QL&7vOvHr:%443Q821vQ5%<5;:721+QTc[<%QO3R61QM/01R6&A&Br1%221Q0%322R4%5221%Q<2Q;1%A4@QE?1%H5GR491=%K3J=1%Q42Q38&D%12:Q3%Q0231%RA2R:R<r;%RD3RG21%RD2R=R9%R82R7<%RG3RJ21%RG2R@R4%R;2R3?%RJ3RM21%RJ2RCR0%QO2S0F%RM3S021&?%12Q9RG%Q?231%Q@271%QA2;1%QB2?1%QC2C1%QD2H1qQNS71%QG2S81qR8S:1%QI2S;1p0QK1p0QO1p0R31p0R;1p0RF1p0RN1p0S71pQJSB1pR:SE1pR6SE1").
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.
End C2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
