(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Ja0MemIsZero Ja0RegionPoisoned Ja0AsanMemset Ja0AsanMemcpy Ja0Readers Ja0StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0ReadIcpt () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ReadIcpt.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ReadIcpt.FPX_1.RDPOST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ReadIcpt.FPX_1.RDPRE."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2True"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"]; ["4bytes_le_to_Z"; "5store_ok"; "5word_to_le_bytes"; "6bvmap"; "0M"; "0M'"; "0M1"; "0M2"; "7msteps"; "8ret_ok"; ":FR"; ":c2_pre"; ":cR_post"; ":cR_pre"; ":cRqa_post"; ":out_agree"]; [":qlR_inv"; ":qlR_post"; ":slots_ok"; ";RDA"; "9RIPL"; "<HIGHEND"; "<SB"; "<frame_only"; "<keeps_but"; "<rt_layout_globs"; "=getr"; "=mkst"; "=rdn"; ">mem_grows"; "?loaded_segments"; "@add"]; ["@div"; "@le"; "@lor"; "@lt"; "@of_nat"; "@pow"; "@sub"; "0a"; "0cnt"; "0fS"; "0faS"; "0fd"; "0fx"; "0i"; "0j"; "0k"]; ["0kS"; "0lS"; "0laS"; "0mem0"; "0n"; "0p"; "0q"; "0ra"; "0regs"; "0regs'"; "0regs0"; "0rg"; "0rom"; "0s"; "0sp"; "ABV"]; ["AZ_to_bv"; "Abv"; "Abv_unsigned"; "0u0"; "0u1"; "0w0"; "0w1"; "0x"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac peel0 :=
rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].
#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20]%bv.
Section RDPRE.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables s fd p cnt : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2200)) 2200%nat = true.
Hypothesis Hfd : (0 <= fd < 2 ^ 64)%Z.
Hypothesis Hp : (0 <= p < 2 ^ 64)%Z.
Hypothesis Hcnt : (0 <= cnt < 2 ^ 64)%Z.
Hypothesis HI : rdn ASEGS mem0 (0x13b9d8 : word) 1%nat = Some [Z_to_bv 8 1].
Hypothesis HR : rdn ASEGS mem0 (0x134490 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b3b0)).
Lemma sp_sA : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "9';'RAyR0%211vR>&R@vR=%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Definition RDA (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
(Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
(Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
(Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
(Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
(Z_to_bv 64 (s - 2136)) (word_to_le_bytes 8 (0x64c48 : word)))
(Z_to_bv 64 (s - 2144)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
(Z_to_bv 64 (s - 2136)) (word_to_le_bytes 8 (0x64c64 : word)).
Section SE.
Local Abbreviation SEC_T_RDA_out := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "Q2&Cy5'RAyR0%211%5241'>&QC&RBr1%2271&QFvR=+RS0%3221%8251&QA%1257%<231';'6y8%D11%311&Q3r3r2%3221vR3%113%;3731p0=1pU@L1pTHL1")) (only parsing).
Variable rg : ltac:(sec_ty2 constr:(SEC_T_RDA_out) 0%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_RDA_out) 1%nat 0%nat).
Lemma RDA_out : ltac:(sec_stmt2 constr:(SEC_T_RDA_out) 2%nat 0%nat).
Proof.
intros Hx.
unfold RDA. pose proof (u64_range x).
destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
| rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
Qed.
End SE.
Lemma RDA_grows : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "=&Cy5'RAyR0%211%5241&Q=vR3&Q3r1%211%5241pTH71").
Proof. intros rg. unfold RDA. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
#[local] Ltac slot := repeat peel0; apply rdn_wbytes_hit8; unorm; lia.
Section SE.
Local Abbreviation SEC_T_RDA_slots := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "S6&Cy5'RAyR0%211%5241':';'6'3y8%911%311%511&Q<&Q>&Q3r1%211&R@&QFvR=+8%3221%52E1u8%<4;821(0&BvR7%2251%42C1%I3C61+@%>2=1%@2Q01%F4EB1;&Q:(R?(8%23Q7B1%42H1%>2A1%@2O1%Q53O81+H%J2I1%L2Q<1%Q24Q1N1G+9%<3QA1;%>2Q21%H2K1%J2Q91%Q?3Q961+Q0%Q42Q31%Q62QF1%Q<4Q;Q81Q1+B%F3QK1E%H2Q<1%Q22Q51%Q42QC1%QI3QC61+Q8%Q>2Q=1%Q@2R01%QF4QEQB1Q;+C%Q03R51O%Q22QF1%Q<2Q?1%Q>2QM1%R33QM61+Q@%QH2QG1%QJ2R:1%R04QOQL1QE+D%Q:3R?1Q9%Q<2R01%QF2QI1%QH2R71%R=3R761+RRH%R22R11%R42RD1%R:4R9R61QO+\cS4%QD3RG1QC/01RG%R02R31%R22RA1%RG3RA61%RI2;1%RJ2F1%RK2Q11%RL2Q<1%RM2QG1%RN2R41pTHS01")) (only parsing).
Variable rg : ltac:(sec_ty2 constr:(SEC_T_RDA_slots) 0%nat 0%nat).
Lemma RDA_slots : ltac:(sec_stmt2 constr:(SEC_T_RDA_slots) 1%nat 0%nat).
Proof.
destruct Hs as [S1' S2']. unfold RDA. repeat split; slot. Qed.
End SE.
#[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2200)) _ 2200%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].
Section SE.
Local Abbreviation SEC_T_read_icpt_pre_run := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "TI&Cy5'RAyR0%211%5241';&Q:r1(R?+:(8%33;21%6251&R@vQK%22=1%;3=41r2+;%;3C19%>231vR5%92D1%B3D31r3+<%B3J1@%E231vQH%@2K1%I3K31r4+2%I3Q11G%L231vR>%O3Q121r5+1%O3Q71M%Q2231vR7%Q53Q721'<':'H&Q>&Q;vQLr7+\cPD%Q;3QA1Q9/01QAvR3vR<%8576321+QTf\4%QA3QG1Q?/01QG&Q3%11;%>5=QF317%A3@71+A%QH3R01QF%QK2QJ1+QO%QF2R11%QO3R131%QO2QNQB%R13R31Q@%R12R0Q=%R33R51Q;+=%R23R:1R0%R52R41z%R02R;1%R93R;31+>%R83R@1R6%R;2R:1%R=3R?15+?%R<3RD1R:%R?2R>1%RA3RC19+@%R@3RH1R>%RC2RB1%RE3RG1=%RE2RDQJ&QFvR=+RS0%3221%RC2RN1%RL3RN61%RL2RKQK+QU\nH%RL3S21RJ/01S2%S13S341+8%S03S81RN%S32S21%RM2S8=%S63S821+9%S53S=1S3%S82S71%S:3S<1RI+B%S93SA1S7%S<2S;1%S>3S@1RF+C%S=3SE1S;%S@2S?1%SB3SD1S8+D%SA3SI1S?%SD2SC1%S>2SIRE%SG3SI21&Q8&Q4%231R>SH%RD241%RE2:1%RF2?1%RG2D1%RH2I1%RI2O1%RJ2Q51%RK2Q=1%RL2QB1%RM2QG1%RN2QL1%RO2R31%S02R61%S12SM1%S22R:1%S32RA1qTDT<1%S62T=1p0S81p0S?1p0SF1p0SN1p0T61pTBTC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_read_icpt_pre_run) 0%nat 0%nat).
Theorem read_icpt_pre_run : ltac:(sec_stmt2 constr:(SEC_T_read_icpt_pre_run) 1%nat 0%nat).
Proof.
intros H10 H11 H12 H2 H1.
rewrite sp_sA in H2. destruct Hs as [S1' S2'].
assert (Hra : ret_ok (0x64c48 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
set (M6 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
(Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
(Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))) (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))) (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20))).
assert (HI6 : rdn ASEGS M6 (0x13b9d8 : word) 1%nat = Some [Z_to_bv 8 1]) by (unfold M6; repeat peel0; exact HI).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x64c14 : word) mem0 rom) (mkst r1 (0x8078c : word) M6 rom)
/\ (getr r1 18 = Z_to_bv 64 cnt /\ getr r1 9 = Z_to_bv 64 p /\ getr r1 19 = Z_to_bv 64 fd /\ getr r1 8 = Z_to_bv 64 s
/\ getr r1 2 = Z_to_bv 64 (s - 2128) /\ getr r1 1 = (0x64c48 : word) /\ keeps_but RIPL regs r1)).
{ unfold M6. eexists. split.
- stepiv (ltac:(oF' 0x64c14%Z)) (ltac:(oD' 0x64c14%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepsd (ltac:(oF' 0x64c18%Z)) (ltac:(oD' 0x64c18%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(sok).
stepsd (ltac:(oF' 0x64c1c%Z)) (ltac:(oD' 0x64c1c%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok).
stepsd (ltac:(oF' 0x64c20%Z)) (ltac:(oD' 0x64c20%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok).
stepsd (ltac:(oF' 0x64c24%Z)) (ltac:(oD' 0x64c24%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok).
stepsd (ltac:(oF' 0x64c28%Z)) (ltac:(oD' 0x64c28%Z)) (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok).
stepsd (ltac:(oF' 0x64c2c%Z)) (ltac:(oD' 0x64c2c%Z)) (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok).
stepiv (ltac:(oF' 0x64c30%Z)) (ltac:(oD' 0x64c30%Z)) (Z_to_bv 64 s) ltac:(wval).
stepiv (ltac:(oF' 0x64c34%Z)) (ltac:(oD' 0x64c34%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepiv (ltac:(oF' 0x64c38%Z)) (ltac:(oD' 0x64c38%Z)) (Z_to_bv 64 cnt) ltac:(wval).
stepiv (ltac:(oF' 0x64c3c%Z)) (ltac:(oD' 0x64c3c%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x64c40%Z)) (ltac:(oD' 0x64c40%Z)) (Z_to_bv 64 fd) ltac:(wval).
stepn (ltac:(oF' 0x64c44%Z)) (ltac:(oD' 0x64c44%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q18 & Q9 & Q19 & Q8 & Q2 & Q1 & K1).
destruct (tryinit_fast_run r1 M6 rom (0x64c48 : word) (s - 2128) Q2 Q1 Hra ltac:(lia) ltac:(lia)
ltac:(replace (s - 2128 - 16)%Z with (s - 2144)%Z by lia; unfold M6; sok) HI6) as (r2 & RUN2 & T10 & T2 & T8 & T1 & K2).
replace (s - 2128 - 8)%Z with (s - 2136)%Z in RUN2 by lia. replace (s - 2128 - 16)%Z with (s - 2144)%Z in RUN2 by lia.
rewrite Q8 in RUN2. rewrite Q8 in T8.
set (M8 := wbytes (wbytes M6 (Z_to_bv 64 (s - 2136)) (word_to_le_bytes 8 (0x64c48 : word))) (Z_to_bv 64 (s - 2144)) (word_to_le_bytes 8 (Z_to_bv 64 s))) in RUN2.
assert (HR8 : rdn ASEGS M8 (0x134490 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b3b0))) by (unfold M8, M6; repeat peel0; exact HR).
assert (T18 : getr r2 18 = Z_to_bv 64 cnt) by (rewrite (K2 18%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q18).
assert (T9 : getr r2 9 = Z_to_bv 64 p) by (rewrite (K2 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q9).
assert (T19 : getr r2 19 = Z_to_bv 64 fd) by (rewrite (K2 19%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q19).
eexists. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepn (ltac:(oF' 0x64c48%Z)) (ltac:(oD' 0x64c48%Z)).
mld (ltac:(oF' 0x64c4c%Z)) (ltac:(oD' 0x64c4c%Z)) (0x134490 : word) HR8.
stepiv (ltac:(oF' 0x64c50%Z)) (ltac:(oD' 0x64c50%Z)) (Z_to_bv 64 1) ltac:(wval).
stepiv (ltac:(oF' 0x64c54%Z)) (ltac:(oD' 0x64c54%Z)) (Z_to_bv 64 fd) ltac:(wval).
stepiv (ltac:(oF' 0x64c58%Z)) (ltac:(oD' 0x64c58%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x64c5c%Z)) (ltac:(oD' 0x64c5c%Z)) (Z_to_bv 64 cnt) ltac:(wval).
stepjr (ltac:(oF' 0x64c60%Z)) (ltac:(oD' 0x64c60%Z)) (Z_to_bv 64 0x12b3b0) ltac:(gres; reflexivity).
vnorm.
stepiv (ltac:(oF' 0x12b3b0%Z)) (ltac:(oD' 0x12b3b0%Z)) (Z_to_bv 64 (s - 2144)) ltac:(wval).
stepsd (ltac:(oF' 0x12b3b4%Z)) (ltac:(oD' 0x12b3b4%Z)) (Z_to_bv 64 (s - 2136)) (Z_to_bv 64 0x64c64) ltac:(unfold M8, M6; sok).
stepiv (ltac:(oF' 0x12b3b8%Z)) (ltac:(oD' 0x12b3b8%Z)) (Z_to_bv 64 cnt) ltac:(wval).
stepiv (ltac:(oF' 0x12b3bc%Z)) (ltac:(oD' 0x12b3bc%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x12b3c0%Z)) (ltac:(oD' 0x12b3c0%Z)) (Z_to_bv 64 fd) ltac:(wval).
stepn (ltac:(oF' 0x12b3c4%Z)) (ltac:(oD' 0x12b3c4%Z)).
stepn (ltac:(oF' 0x12b3c8%Z)) (ltac:(oD' 0x12b3c8%Z)).
stepn (ltac:(oF' 0x12b3cc%Z)) (ltac:(oD' 0x12b3cc%Z)).
stepn (ltac:(oF' 0x12b3d0%Z)) (ltac:(oD' 0x12b3d0%Z)).
stepn (ltac:(oF' 0x12b3d4%Z)) (ltac:(oD' 0x12b3d4%Z)).
stepn (ltac:(oF' 0x12598c%Z)) (ltac:(oD' 0x12598c%Z)).
stepiv (ltac:(oF' 0x125968%Z)) (ltac:(oD' 0x125968%Z)) (Z_to_bv 64 63) ltac:(wval).
stepiv (ltac:(oF' 0x12596c%Z)) (ltac:(oD' 0x12596c%Z)) (Z_to_bv 64 fd) ltac:(wval).
stepiv (ltac:(oF' 0x125970%Z)) (ltac:(oD' 0x125970%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x125974%Z)) (ltac:(oD' 0x125974%Z)) (Z_to_bv 64 cnt) ltac:(wval).
stepiv (ltac:(oF' 0x125978%Z)) (ltac:(oD' 0x125978%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x12597c%Z)) (ltac:(oD' 0x12597c%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x125980%Z)) (ltac:(oD' 0x125980%Z)) (Z_to_bv 64 0) ltac:(wval).
unfold M8, M6. fold (RDA regs). apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end).
eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [| solve_keeps_but].
intros r Hr HL. apply K2; [exact Hr|]. cbv in HL |- *. intuition.
Qed.
End SE.
Corollary wrap_read_pre_run : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "TI&Cy5'RAyR0%211%5241';&Q:r1(R?+:(8%33;21%6251&R@vQK%22=1%;3=41r2+;%;3C19%>231vR5%92D1%B3D31r3+<%B3J1@%E231vQH%@2K1%I3K31r4+2%I3Q11G%L231vR>%O3Q121r5+1%O3Q71M%Q2231vR7%Q53Q721'<':'H&Q>&Q;vQLr7+\ZaH%Q;3QA1Q9/01QAvR3vR<%8576321+QTf\4%QA3QG1Q?/01QG&Q3%11;%>5=QF317%A3@71+A%QH3R01QF%QK2QJ1+QO%QF2R11%QO3R131%QO2QNQB%R13R31Q@%R12R0Q=%R33R51Q;+=%R23R:1R0%R52R41z%R02R;1%R93R;31+>%R83R@1R6%R;2R:1%R=3R?15+?%R<3RD1R:%R?2R>1%RA3RC19+@%R@3RH1R>%RC2RB1%RE3RG1=%RE2RDQJ&QFvR=+RS0%3221%RC2RN1%RL3RN61%RL2RKQK+QU\nH%RL3S21RJ/01S2%S13S341+8%S03S81RN%S32S21%RM2S8=%S63S821+9%S53S=1S3%S82S71%S:3S<1RI+B%S93SA1S7%S<2S;1%S>3S@1RF+C%S=3SE1S;%S@2S?1%SB3SD1S8+D%SA3SI1S?%SD2SC1%S>2SIRE%SG3SI21&Q8&Q4%231R>SH%RD241%RE2:1%RF2?1%RG2D1%RH2I1%RI2O1%RJ2Q51%RK2Q=1%RL2QB1%RM2QG1%RN2QL1%RO2R31%S02R61%S12SM1%S22R:1%S32RA1qTDT<1%S62T=1p0S81p0S?1p0SF1p0SN1p0T61pTBTC1").
Proof.
intros regs H10 H11 H12 H2 H1.
destruct (read_icpt_pre_run regs H10 H11 H12 H2 H1) as (r' & RUN & REST).
exists r'. split; [|exact REST].
eapply msteps_trans; [|exact RUN].
stepn (ltac:(oF' 0x62a38%Z)) (ltac:(oD' 0x62a38%Z)).
apply mst_refl.
Qed.
End RDPRE.
Section RDPOST.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables ra : word.
Variables p n s : Z.
Variables kS fS lS faS laS : Z.
Hypothesis HfS_def : fS = (SB + p / 8)%Z. Hypothesis HlS_def : lS = (SB + (p + n - 1) / 8)%Z.
Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z. Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
Hypothesis HnB : (0 < n < 2 ^ 40)%Z.
Hypothesis HappS : in_app8 p n.
Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis HshS : (lS + 8 <= s - 2200)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2200)) 2200%nat = true.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : rt_layout_globs mem0.
Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0).
Hypothesis HLS : (0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
Hypothesis HkS : kS = 0%Z \/ ((p + n - 1) mod 8 < kS <= 7)%Z.
Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1.
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac hide_dj := try hide HkS; try hide HappS.
Lemma Hn : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt ";':&QAzvR4%3221&QE+2+Q8%3221%8261%:261"). Proof. hide_dj. lia. Qed.
Lemma pS_facts : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "N':&QAzvR5%3221&Q?vR4%2241+8%4221&Q5%:221&Q@%12:5%=2<1%>225%@221&QC%12@<&QF+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof.
hide_dj.
unhide HappS.
unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappS as [[H1 H2]|[H1 H2]];
(repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
Qed.
Lemma pD_facts : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "N':&QAzvR5%3221&Q?vR4%2241+8%4221&Q5%:221&Q@%12:5%=2<1%>225%@221&QC%12@<&QF+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof. hide_dj. exact pS_facts. Qed.
Lemma flS_facts : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "Q3&QCzvR4%3221':&QA&Q6vQI%3221vR1%5231%7231&Q?+8%2251&QFvR=+RTH%3221%>251+7%62>1vQJ%B221%C22A%E221%;2A6vR2%G221%H22D%J221%K261%L2=1%M2F1p0O1").
Proof.
hide_dj.
intros Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). repeat split; lia.
Qed.
Definition out_agree (M : word -> option byte) : Prop :=
forall x : word, (bv_unsigned x < s - 2200 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
Lemma out_agree_refl : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "3&OvR3%211"). Proof. hide_dj. intros x _. reflexivity. Qed.
Lemma out_agree_rdn : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "Q:'RAyR0%211'6y8%511%311p051'4&Or3%211&QA&Q?&RB%12>5&QDr2%211%6241&QFvR=+RTH%3221%<251';'3%11F%I11&Q<&Q>r5r4%44321GvR3%64513I%;3831p0=1p0K1pT0O1pS@Q61pQ:Q21").
Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
Lemma out_agree_globs : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "C'RAyR0%211'6y8%511%311p051&Or1%211':&Q9r2%211'9%5221p071pQ:;1").
Proof.
hide_dj.
intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
unfold rt_layout_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
repeat split; assumption.
Qed.
Lemma out_agree_store_ok : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "Q:'RAyR0%211'6y8%511%311p051'?'4&Q=vR3r3%3221':&QA&QDr2%211%4217+RTH%6291%8231';'1&A&Q>r5&R@&QFvR=r4%3221%52Q01%94871F(7%=3<21p0?1p0I1pSNN1pT0Q01pQ:Q21").
Proof.
hide_dj.
intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2200)) _ 2200%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
Qed.
Definition slots_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)).
Definition FR (regs0 : bvmap 5 word) (M : word -> option byte) : Prop := out_agree M /\ mem_grows mem0 M /\ slots_ok regs0 M.
Lemma rdn_slot_ext : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "QE'RAyR0%211'6y8%511%311p051'?':&QA&QFvR=+RR@%3221&RBr1%22@1%8241&QC%1238%<231';r5r2%211r4%113%63F31p081pU@L1+8%F218%G29D%I221'3%11O%Q211&Q<&Q>&R@r3%O2N1%32Q:1u8%746F21%847D32%I3:21p0>1p0C1pT0Q:1pQ@Q<1pQ>Q=1").
Proof.
hide_dj.
intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
Qed.
Lemma slots_ok_ext : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "Q:&Cy5'RAyR0%211%5241'6y8%611%311p061':&QA&QFvR=+RR@%3221&RBr1%22@1%8241&QC%1238%<231';r3r2%211r4%113%63E31p081pU@L1&Q2%1269r5%321;p031p061pQ@M1pQ>N1pTFQ41").
Proof.
hide_dj.
intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6). unfold slots_ok.
rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
Qed.
Lemma FR_region : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "Q0&Cy5'RAyR0%211%5241'6y8%611%311p061&Jr3r2%3221&Q7&QFvR=+RR@%3221%53817&Q=r4%221;r6%>213p031p071p0>1pQ<C1pQ:D1pTFJ1").
Proof.
hide_dj.
intros regs0 M M' (O & G & R) HF HGr. split; [|split].
- intros x Hx. rewrite (HF x) by lia. apply O. exact Hx.
- eapply mem_grows_trans; [exact G | exact HGr].
- apply (slots_ok_ext regs0 M M'); [|exact R]. intros x Hx. apply HF. lia.
Qed.
Lemma rdnWS : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "R0'RAyR0%211'6y8%511%311p051&Or1%211':&QCzvR4%3221&QA+R0%2241%8241'<'3%11A';%E12&Q<&Q>r5&R@vQJ%22M1u8%746521(0r2%22=1%=3<41vR2%:2Q51%>4=<18%72BO%B3A21&@%119%L2O1&QE+2%221N%Q4251%Q6251%81Q9%Q32Q61%Q8225%Q:221%Q;251%Q<2>1%Q=2D1qU>Q31%Q62Q41qU<Q51%Q82Q61p0Q:1p0QD1pQ:QH1").
Proof.
hide_dj.
intros M HO Hn64. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
destruct (HWS Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
Qed.
Lemma rdn1S : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "QA'RAyR0%211'6y8%511%311p051'?&Or2%211&QCzvR4%3221':&QAvQIr3%3221vR1%:231%7231';'3%11E%H11&Q<&Q>r5&R@r4%22Q01u1%746521(0(2%72Q2I(5%11Q3%43Q431%62@1%C3@81p0E1p0N1p0Q31pUBQ71pQ:Q91").
Proof.
hide_dj.
intros M z HO Hn0 Hz. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZS Hn0) by (unorm; lia). reflexivity.
Qed.
Lemma rdnLS : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "Q='RAyR0%211'6y8%511%311p051'?&Or2%211&QCzvR4%3221';r3vR1%33;21'3%11@%C11&Q<&Q>r5&R@r4%22K1u1%746521(0(2vR0%82N1(5%11O%53Q031%72A1%G3A91p0E1p0J1p0O1pUBQ31pQ:Q51").
Proof.
hide_dj.
intros M z HO Hn0 ->. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLS Hn0). reflexivity.
Qed.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mlbu0 F D z RD :=
chain_step; [reflexivity
| eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
| step_simpl; vnorm].
#[local] Ltac mlbk F D z RD k :=
chain_step; [reflexivity
| eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
| step_simpl; vnorm; rewrite (v_lb_k k ltac:(lia))].
#[local] Ltac mldw F D z R w :=
chain_step; [reflexivity
| eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
| step_simpl; vnorm].
Definition cR_pre (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 n /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2128).
Definition cR_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).
Lemma ret_ok_64d70 : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt ":&I(R?yR0+\c[@(8%43321'RA%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_cRr_run := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "QO&Cy5'RAyR0%211%5241'6y8%611%311p061&Mr1%211&Jr4r3%3221&QC+R0vR4%3221'<':'H&Q>&Q;vQLr6(R?+\cS<(8%33M21/01Mr7vR<%:598321r2+\cV4%:3Q418/01Q4%?5>41M6%B3A61&L%117&Q8&Q4%231C:r8%Q321Q5%K231%L271%M2:1qQ<Q;1%Q02Q<1qTDQB1%Q22QC1p0Q41p0Q91p0Q>1pTBQG1pQ:QC1pTFQI1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 2%nat 0%nat).
Lemma cRr_run : ltac:(sec_stmt2 constr:(SEC_T_cRr_run) 3%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H9 & H8 & H2) HFR Hn64.
pose proof HFR as (HO & HGr & HR).
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x64c6c : word) M rom) (mkst r1 (0x7ab68 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2128) /\ getr r1 1 = (0x64d70 : word)
/\ getr r1 18 = Z_to_bv 64 n /\ getr r1 9 = Z_to_bv 64 p /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 20 = Z_to_bv 64 (s - 2120) /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepiv (ltac:(oF' 0x64c6c%Z)) (ltac:(oD' 0x64c6c%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepiv (ltac:(oF' 0x64c70%Z)) (ltac:(oD' 0x64c70%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x64c74%Z)) (ltac:(oD' 0x64c74%Z)) (Z_to_bv 64 (s - 2120)) ltac:(wval).
stepb_ft (ltac:(oF' 0x64c78%Z)) (ltac:(oD' 0x64c78%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x64c7c%Z)) (ltac:(oD' 0x64c7c%Z)) (Z_to_bv 64 (n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepn (ltac:(oF' 0x64c80%Z)) (ltac:(oD' 0x64c80%Z)).
stepb_tk (ltac:(oF' 0x64c84%Z)) (ltac:(oD' 0x64c84%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x64d60%Z)) (ltac:(oD' 0x64d60%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x64d64%Z)) (ltac:(oD' 0x64d64%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x64d68%Z)) (ltac:(oD' 0x64d68%Z)) (Z_to_bv 64 n) ltac:(wval).
stepn (ltac:(oF' 0x64d6c%Z)) (ltac:(oD' 0x64d6c%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q18 & Q9 & Q8 & Q20 & K1).
pose proof (out_agree_globs M HO) as (HGM & _).
pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2128)) (0x64d70 : word) p n (s - 2128)
ltac:(unorm; reflexivity) ltac:(lia) HappS ltac:(lia) ltac:(unfold SB in *; lia)
ltac:(replace (s - 2128 - 72)%Z with (s - 2200)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
(ret_ok_64d70) HGM kS) as RP.
specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZS; [lia | unfold SB in *; lia])).
specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlS_def; apply HLS; lia) HkS).
destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
assert (S18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
assert (S9 : getr r2 9 = Z_to_bv 64 p) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
assert (S8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x64d70%Z)) (ltac:(oD' 0x64d70%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x64d74%Z)) (ltac:(oD' 0x64d74%Z)) (Z_to_bv 64 n) ltac:(wval).
stepb_tk (ltac:(oF' 0x64d78%Z)) (ltac:(oD' 0x64d78%Z)) ltac:(cond).
apply mst_refl.
- unfold cR_post. post.
- eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
Qed.
End SE.
Definition cRqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
getr rg 11 = Z_to_bv 64 fS /\ getr rg 12 = Z_to_bv 64 lS /\ getr rg 13 = Z_to_bv 64 (p + n - 1) /\ getr rg 14 = Z_to_bv 64 (Z.lor u1 u0)
/\ getr rg 10 = Z_to_bv 64 n /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2128).
Section SE.
Local Abbreviation SEC_T_cRqa_run := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "S1'RAyR0%211'6y8%511%311p051&Cy5%2218'3%117&Mr3%211&Or5%211':&QCzvR4%3221&QA+R0%2241%8241';%J1A&Q<&Q>r7&R@vQJ%22Q21u8%746521(0%12KF%<3;31r8vR2%:2Q:1%>4=318%A3@16&@%11?%H2K1&QE+2%221J%Q0251%Q2251'<'H&Q;vQLr;(R?+\cS<(8%33QM21/01QMr<vR<%:598321r1+\cV0%:3R418/01R4%?5>4176%A3Q961&Nr:%M11r9%O11%5331;&Q8&Q4%231G>%QO241%R02;1qTDR:1%O2R;1p0Q11p0Q21p0Q;1p0QA1p0QO1p0R91p0R=1pU>RA1pU<RB1pTBRE1pQ:RI1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 1%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 2%nat 0%nat).
Variable w1 : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 3%nat 0%nat).
Lemma cRqa_run : ltac:(sec_stmt2 constr:(SEC_T_cRqa_run) 4%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H9 & H8 & H2) HO Hn64 R0 R1 B0 B1.
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
unfold SB, HIGHEND in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as Ml.
pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
eexists. split.
- stepiv (ltac:(oF' 0x64c6c%Z)) (ltac:(oD' 0x64c6c%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepiv (ltac:(oF' 0x64c70%Z)) (ltac:(oD' 0x64c70%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x64c74%Z)) (ltac:(oD' 0x64c74%Z)) (Z_to_bv 64 (s - 2120)) ltac:(wval).
stepb_ft (ltac:(oF' 0x64c78%Z)) (ltac:(oD' 0x64c78%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x64c7c%Z)) (ltac:(oD' 0x64c7c%Z)) (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x64c80%Z)) (ltac:(oD' 0x64c80%Z)).
stepb_ft (ltac:(oF' 0x64c84%Z)) (ltac:(oD' 0x64c84%Z)) ltac:(cond).
stepn (ltac:(oF' 0x64c88%Z)) (ltac:(oD' 0x64c88%Z)).
mld (ltac:(oF' 0x64c8c%Z)) (ltac:(oD' 0x64c8c%Z)) (0x132638 : word) G1.
stepiv (ltac:(oF' 0x64c90%Z)) (ltac:(oD' 0x64c90%Z)) (Z_to_bv 64 (p + n)) ltac:(wval).
mld (ltac:(oF' 0x64c94%Z)) (ltac:(oD' 0x64c94%Z)) (0x13acf8 : word) G2.
stepiv (ltac:(oF' 0x64c98%Z)) (ltac:(oD' 0x64c98%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x64c9c%Z)) (ltac:(oD' 0x64c9c%Z)) (Z_to_bv 64 (p + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x64ca0%Z)) (ltac:(oD' 0x64ca0%Z)) (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x64ca4%Z)) (ltac:(oD' 0x64ca4%Z)) (Z_to_bv 64 fS) ltac:(wval).
stepiv (ltac:(oF' 0x64ca8%Z)) (ltac:(oD' 0x64ca8%Z)) (Z_to_bv 64 lS) ltac:(wval).
stepiv (ltac:(oF' 0x64cac%Z)) (ltac:(oD' 0x64cac%Z)) (Z_to_bv 64 faS)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
stepiv (ltac:(oF' 0x64cb0%Z)) (ltac:(oD' 0x64cb0%Z)) (Z_to_bv 64 laS)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
mldw (ltac:(oF' 0x64cb4%Z)) (ltac:(oD' 0x64cb4%Z)) faS R0 w0.
mldw (ltac:(oF' 0x64cb8%Z)) (ltac:(oD' 0x64cb8%Z)) laS R1 w1.
stepov (ltac:(oF' 0x64cbc%Z)) (ltac:(oD' 0x64cbc%Z)) (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
apply mst_refl.
- unfold cRqa_post. split; [post | solve_keeps_but].
Qed.
End SE.
Definition qlR_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 11 = Z_to_bv 64 (fS + i) /\ getr rg 12 = Z_to_bv 64 lS /\ getr rg 13 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 n /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2128).
Definition qlR_post (rg : bvmap 5 word) : Prop :=
getr rg 13 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 n /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2128).
Section SE.
Local Abbreviation SEC_T_qloopR_run := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "R='RAyR0%211'6y8%511%311p051'4&Cy5%2219'?&Or4%211&QCzvR4%3221&Q0r3%2281&QA%127:';&Q?vQIr5%3221&QDr7%211%7241+1%9221vR1%<3I21'<':'H&Q>&Q;vQLr8(R?+\ca8(8%33Q?21/01Q?r:vR<%:598321r1+\caH%:3QF18/01QF%?5>4176%B3A61&Q1%117&Q8&Q4%231C:%I241%J271qTDQG1%M2QH1p0O1p0Q=1p0Q@1p0QD1p0QI1pSLQM1pTBQO1pT>R31pQ:R51")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_qloopR_run) 0%nat 0%nat).
Lemma qloopR_run : ltac:(sec_stmt2 constr:(SEC_T_qloopR_run) 1%nat 0%nat).
Proof.
hide_dj.
intros q.
induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H9 & H8 & H2) Hi Hq;
pose proof (flS_facts Hn0) as (F1 & F2 & _); unfold SB in *.
- eexists. split.
+ mlbu0 (ltac:(oF' 0x64e28%Z)) (ltac:(oD' 0x64e28%Z)) (fS + i)%Z rdn1S.
stepiv (ltac:(oF' 0x64e2c%Z)) (ltac:(oD' 0x64e2c%Z)) (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x64e30%Z)) (ltac:(oD' 0x64e30%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_ft (ltac:(oF' 0x64e34%Z)) (ltac:(oD' 0x64e34%Z)) ltac:(cond).
apply mst_refl.
+ unfold qlR_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x64e28 : word) M rom) (fun rg => qlR_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
+ eexists. split.
* mlbu0 (ltac:(oF' 0x64e28%Z)) (ltac:(oD' 0x64e28%Z)) (fS + i)%Z rdn1S.
stepiv (ltac:(oF' 0x64e2c%Z)) (ltac:(oD' 0x64e2c%Z)) (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x64e30%Z)) (ltac:(oD' 0x64e30%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x64e34%Z)) (ltac:(oD' 0x64e34%Z)) ltac:(cond).
apply mst_refl.
* unfold qlR_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
Qed.
End SE.
Lemma cRqf_run : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "R5'RAyR0%211'6y8%511%311p051&Cy5%2218'?&Nr2r1r3%43321':&QAz&QB%1286%4231&QC&QE+2+R0%3221%5271%<271';r4%<2A1%33F1>'<'H&Q>&Q;vQLr7(R?+\cV0(8%33Q:21/01Q:r8vR<%:598321+\cV4%93Q@17/01Q@%>5=Q5165%A3@51&L%11Q8&Q8&Q4%231BQ;%Q9241%Q:271qTDQB1%K2QC1p0M1p0Q21p0Q@1pU:QF1pU8QG1pTBQI1pQ:QM1").
Proof.
hide_dj.
intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H9 & H8 & H2) BL E.
eexists. split.
- stepb_ft (ltac:(oF' 0x64cc0%Z)) (ltac:(oD' 0x64cc0%Z)) ltac:(cond).
apply mst_refl.
- unfold cR_post. post.
Qed.
Section SE.
Local Abbreviation SEC_T_cRqs_run := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "RA'RAyR0%211'6y8%511%311p051&Cy5%2218'?&Nr2r1r3%43321&Or5%211':&QCzvR4%3221&QA+R0%2241%8241&QBr4%221=%72:1&QE+2%2219%?251%A251&=';r6%<2G1%33O1D%511'<'H&Q>&Q;vQLr9(R?+\cV0(8%33QD21/01QDr:vR<%:598321+\cV4%93QJ17/01QJ%>5=Q?165%A3@51&L%11QB&Q8&Q4%231BQE%Q@241%QA271qTDQL1%K2QM1p0M1p0Q41p0Q>1p0QH1p0QL1pU:R21pU8R31pTBR51pQ:R91")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 1%nat 0%nat).
Variable u0 : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 2%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 3%nat 0%nat).
Lemma cRqs_run : ltac:(sec_stmt2 constr:(SEC_T_cRqs_run) 4%nat 0%nat).
Proof.
hide_dj.
intros (H13 & H14 & HL' & H15 & H10 & H9 & H8 & H2) HO Hn64 BL NE.
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x64e24 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
{ unhide HkS. destruct HkS as [K0|K7].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x64cc0%Z)) (ltac:(oD' 0x64cc0%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x64e0c%Z)) (ltac:(oD' 0x64e0c%Z)) lS rdnLS kS.
stepiv (ltac:(oF' 0x64e10%Z)) (ltac:(oD' 0x64e10%Z)) (Z_to_bv 64 ((p + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x64e14%Z)) (ltac:(oD' 0x64e14%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepov (ltac:(oF' 0x64e18%Z)) (ltac:(oD' 0x64e18%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((p + n - 1) mod 8 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepiv (ltac:(oF' 0x64e1c%Z)) (ltac:(oD' 0x64e1c%Z)) (Z_to_bv 64 1) ltac:(vlit).
stepov (ltac:(oF' 0x64e20%Z)) (ltac:(oD' 0x64e20%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlR_inv. post.
- eexists. split.
+ stepb_tk (ltac:(oF' 0x64cc0%Z)) (ltac:(oD' 0x64cc0%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x64e0c%Z)) (ltac:(oD' 0x64e0c%Z)) lS rdnLS kS.
stepiv (ltac:(oF' 0x64e10%Z)) (ltac:(oD' 0x64e10%Z)) (Z_to_bv 64 ((p + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x64e14%Z)) (ltac:(oD' 0x64e14%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepov (ltac:(oF' 0x64e18%Z)) (ltac:(oD' 0x64e18%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((p + n - 1) mod 8 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepiv (ltac:(oF' 0x64e1c%Z)) (ltac:(oD' 0x64e1c%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepov (ltac:(oF' 0x64e20%Z)) (ltac:(oD' 0x64e20%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlR_inv. post. }
cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I9 & I8 & I2) & K1).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x64e38 : word) M rom) (fun rg => qlR_post rg /\ keeps_but RIPL regs rg)).
{ destruct (Z.lt_ge_cases fS lS) as [Hfl|Hfl].
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x64e28 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x64e24%Z)) (ltac:(oD' 0x64e24%Z)) ltac:(cond).
apply mst_refl.
* split; [unfold qlR_inv; repeat split; assumption | exact K1].
+ cbv beta. intros r2 (I2' & K2).
destruct (qloopR_run M (Z.to_nat (lS - fS - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x64e24%Z)) (ltac:(oD' 0x64e24%Z)) ltac:(cond).
apply mst_refl.
+ split; [unfold qlR_post; repeat split; assumption | exact K1]. }
cbv beta. intros r4 ((J15 & J10 & J9 & J8 & J2) & K4).
eexists. split.
- stepiv (ltac:(oF' 0x64e38%Z)) (ltac:(oD' 0x64e38%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x64e3c%Z)) (ltac:(oD' 0x64e3c%Z)) ltac:(cond).
apply mst_refl.
- unfold cR_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
Qed.
End SE.
Lemma cR_run : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "QJ&Cy5'RAyR0%211%5241'6y8%611%311p061&Mr1%211&Jr4r3%3221'<':'H&Q>&Q;vQLr5(R?+\cS<(8%33I21/01Ir6vR<%:598321r2+\cV4%:3Q018/01Q0%?5>41I6%B3A61&L%117&Q8&Q4%231C:r7%O21Q1%K231%L271%M2:1qQ<Q71%Q02Q81qTDQ>1%Q22Q?1p0Q41p0Q91pTBQB1pQ:Q>1pTFQD1").
Proof.
hide_dj.
intros regs0 M regs P1 HFR. pose proof HFR as (HO & HGr & HR).
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
{ exfalso. lia. }
destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
- destruct (rdnWS M HO ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
destruct (cRqa_run M regs w0 w1 P1 HO ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
pose proof (lor_bound64 _ _ B1 B0) as BL.
destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
+ destruct (cRqf_run M r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, M.
split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
+ destruct (cRqs_run M r2 _ _ P2 HO ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, M.
split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
- exact (cRr_run regs0 M regs P1 HFR Hgt).
Qed.
Definition c2_pre (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144) /\ getr rg 1 = (0x12b3d8 : word)
/\ getr rg 8 = Z_to_bv 64 s /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 20 = Z_to_bv 64 1.
Lemma ret_ok_12b3d8 : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt ":&I(R?yR0+QU\nH(8%43321'RA%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ret_ok_64c64 : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt ":&I(R?yR0+\cS4(8%43321'RA%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_c2_run := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "R5&Cy5'RAyR0%211%5241'6y8%611%311p061&Kr2%211';'3%118%;11&Q<&Q>&R@&QFvR=+RRH%3221%52F1u8%948?21(0&B(R?+\cS4(8%33N21/01N%6291%82D1%G3D:1'<':'H&Q;vQLr5+QTf\8%?3Q:1=/01Q:r4vR<%8576321r1+\cS<%F3QA1D/01QA%=5<4176%?3Q461&M%117&Q8&Q4%231A:%F241%G271qTDQJ1%J2QK1p0L1p0QE1pQ:QI1pTBQO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c2_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_c2_run) 1%nat 0%nat).
Lemma c2_run : ltac:(sec_stmt2 constr:(SEC_T_c2_run) 2%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H2 & H1 & H8 & H9 & H20) RA.
destruct Hs as [S1' S2'].
pose proof ret_ok_12b3d8 as Rce. pose proof ret_ok_64c64 as R4e.
eexists. split.
- stepret (ltac:(oF' 0x125988%Z)) (ltac:(oD' 0x125988%Z)) (0x12b3d8 : word) ltac:(rwH; reflexivity).
stepld (ltac:(oF' 0x12b3d8%Z)) (ltac:(oD' 0x12b3d8%Z)) (0x64c64 : word) ltac:(maddr (s - 2136)%Z; exact RA).
stepiv (ltac:(oF' 0x12b3dc%Z)) (ltac:(oD' 0x12b3dc%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepn (ltac:(oF' 0x12b3e0%Z)) (ltac:(oD' 0x12b3e0%Z)).
stepn (ltac:(oF' 0x113c7c%Z)) (ltac:(oD' 0x113c7c%Z)).
stepn (ltac:(oF' 0x113c80%Z)) (ltac:(oD' 0x113c80%Z)).
stepb_tk (ltac:(oF' 0x113c84%Z)) (ltac:(oD' 0x113c84%Z)) ltac:(cond).
stepret (ltac:(oF' 0x113cb0%Z)) (ltac:(oD' 0x113cb0%Z)) (0x64c64 : word) ltac:(rwH; reflexivity).
stepb_ft (ltac:(oF' 0x64c64%Z)) (ltac:(oD' 0x64c64%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x64c68%Z)) (ltac:(oD' 0x64c68%Z)) ltac:(rwH; unfold c_lts, bv_lts; rewrite !signed64_small by lia;
first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.leb_le | apply Z.leb_gt]; lia).
apply mst_refl.
- unfold cR_pre. post.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_c3_run := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "S3&Cy5'RAyR0%211%5241'6y8%611%311p061&Lr2%211&Jr4%2214'<':'H&Q>&Q;vQLr5(R?+\cV4(8%33H21/01HvR<%95872?1r1vR7%<5;21B4%?3>41';&Q:+:%>3Q51<%3281&R@vR4%22Q71%83Q741+2%E3Q<1C%:2?1vR=%82Q=1%>3Q=31+1%K3QB1I%@2E1%B3QA1E+8%O3QF1M%D2I1r6%F213%H3QG31+9%Q53QL1Q3%J2O1%K262%M3QL21+B%Q:3R11Q8%O2Q41%Q02;2%Q23R121+C%Q?3R61Q=%Q42Q91%Q52@2%Q73R621+D%QD3R;1QB%Q92Q>1%Q:2E2%Q<3R;21&Q8&Q4%231QKQC%R1241%R22:1%R32@1%R42F1%R52L1%R62Q31%R72Q81%R82Q?1%R92QI1qTDRG1%R<2RH1p0R>1p0RB1pQ:RF1pTBRL1pTFRM1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c3_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c3_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_c3_run) 2%nat 0%nat).
Lemma c3_run : ltac:(sec_stmt2 constr:(SEC_T_c3_run) 3%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H2) (HO & HGr & (R1 & R2 & R3 & R4 & R5 & R6)).
destruct Hs as [S1' S2'].
eexists. split.
- stepiv (ltac:(oF' 0x64cc4%Z)) (ltac:(oD' 0x64cc4%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepld (ltac:(oF' 0x64cc8%Z)) (ltac:(oD' 0x64cc8%Z)) ra ltac:(maddr (s - 8)%Z; exact R1).
stepld (ltac:(oF' 0x64ccc%Z)) (ltac:(oD' 0x64ccc%Z)) (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
stepld (ltac:(oF' 0x64cd0%Z)) (ltac:(oD' 0x64cd0%Z)) (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
stepld (ltac:(oF' 0x64cd4%Z)) (ltac:(oD' 0x64cd4%Z)) (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
stepld (ltac:(oF' 0x64cd8%Z)) (ltac:(oD' 0x64cd8%Z)) (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
stepld (ltac:(oF' 0x64cdc%Z)) (ltac:(oD' 0x64cdc%Z)) (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
stepiv (ltac:(oF' 0x64ce0%Z)) (ltac:(oD' 0x64ce0%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x64ce4%Z)) (ltac:(oD' 0x64ce4%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity; [exact H10 | solve_keeps_but].
Qed.
End SE.
Theorem read_icpt_post_run : ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "SL&Cy5'RAyR0%211%5241'6y8%611%311p061&Kr2%211&Jr4%2214';'3%11;%>11&Q<&Q>r3&R@&QFvR=+RRH%3221%52J1u8%:49821(0&B(R?+\cS4(8%33Q221/01Q2%6291%82E1%H3E:1'<':'H&Q;vQLr7+QTf\8%?3Q>1=/01Q>r6vR<%8576321vR7r1%;5:Q<214%=3Q341&Q:+:%J3QK1H%32QA1vR4%Q72QL1%Q?3QL31+2%Q03R11N%92QG1%Q<2R1Q:%QD3R121+1%Q53R61Q3%>2QL1%QH3R51C+8%Q93R:1Q7%B2R01r8%D213%QN3R;31+9%Q?3R@1Q=%H2R61%I262%R33R@21+B%QD3RE1QB%M2R;1%N2;2%R83RE21+C%QI3RJ1QG%Q22R@1%Q32@2%R=3RJ21+D%QN3RO1QL%Q72RE1%Q82E2%RB3RO21&Q8&Q4%231QGRJ%RI2JQ@%QM221%QN261%QO2<1%R02B1%R12H1%R22N1%R32Q51%R42Q:1%R52Q@1%R62QH1qQ<S81%R92S91qTDS?1%R;2S@1p0R=1p0S71p0S;1pQ:S?1pTBSE1pTFSF1").
Proof.
hide_dj.
intros regs0 regs M P2 HFR RA.
destruct (c2_run regs M P2 RA) as (r1 & RUN1 & P1 & K1).
destruct (cR_run regs0 M r1 P1 HFR) as (r2 & M2 & RUN2 & Q2 & K2 & F2).
destruct (c3_run regs0 r2 M2 Q2 F2) as (r3 & RUN3 & T10 & T2 & T1 & T8 & T9 & T18 & T19 & T20 & K3).
exists r3, M2. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- split; [exact T10|]. split; [exact T2|]. split; [exact T1|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
split; [exact T19|]. split; [exact T20|]. split; [|exact F2].
eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. exact K3.
Qed.
End RDPOST.
Section RDPOST0.
Variable rom : word -> option byte.
Variables ra : word.
Variable s : Z.
Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hret : ret_ok ra.
Section SE.
Local Abbreviation SEC_T_read_icpt_post0_run := (ltac2:(TCodec.tc2 tcn__Ja0ReadIcpt "V5&Cy5'RAyR0%211%5241'6y8%611%311p061';&Q:r2(R?+:(8%33@21%6251&R@z%22B1%;3B41r3+2%;3H19%>231&QFvR=+RS0%3221%<2L1%E3L61r4+1%E3Q21C%H231+QU\nH%H3Q31F/01Q3%M3Q441r5+8%M3Q:1K%Q0231%J2Q:A%Q33Q:21r6+D%Q33Q@1Q1%Q6231%Q02Q@A%Q93Q@21'3%11Q>%QA11&Q<&Q>+RRH%Q02O1%Q92QI1u8%645?21(0&B+\cS4%QD3QO1QB/01QO%4271%62?1%QK3?81r7%Q=2Q<N%QF2R61%B4A31=vR7%<2?1%>2G1%R33G41r8+@%QF2QE1%QO2R?1%K4J41Fr:%R921Q:%F2I1%H2Q11%R=3Q151r9+H%R02QO1%R92RI1%Q54Q441Q0r;+9%RB3RO1R@%RE231%Q22Q51%Q42Q=1%RI3Q=71+Q0%R;2R:1%RD2S41%Q@4Q?D1Q;r<+B%RM3S:1RK%S0231%Q=2Q@1%Q?2QH1%S43QH71+Q8%RF2RE1%RO2S?1%QK4QJE1QFr=+C%S83SE1S6%S;231%QH2QK1%QJ2R31%S?3R371+Q@%S12S01%S:2SJ1%R64R5E1R1r>%SD21R?%R12R41%R32R<1%SH3R<51'<':'H&Q;vQLr?+QTf\8%SM3T81SK/01T8vR<%75652?1r1%9581R5A3%;3RH31%T623T1%T83T?1SN%T825SK%T:3TA1S8%T:27SC%T<3TC1R<%T<29S=r@%T>21S?%T@3TG31%T@2=QL%TA24QM%TC3TJ21%TC2@QD%TD27QE%TF3TM21%TF2CQ<%TG2:Q=%TI3U021%TI2FSD%TJ2=SE%TL3U321&Q8&Q4%231Q1K%Q6241%Q7281%Q82<1%Q92@1%Q:2D1%Q;2I1%Q<2L1%Q=2O1%Q>2Q21qTDU?1%QA2U@1p0QC1p0QM1p0R91p0RE1p0S21p0S=1p0SF1p0T91p0T@1p0TG1p0U01p0U;1pQ:UH1pTBUN1pTFUO1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_read_icpt_post0_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_read_icpt_post0_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_read_icpt_post0_run) 2%nat 0%nat).
Theorem read_icpt_post0_run : ltac:(sec_stmt2 constr:(SEC_T_read_icpt_post0_run) 3%nat 0%nat).
Proof.
intros H10 H2 H1 H8 H20 RA R1 R2 R3 R4 R5 R6.
destruct Hs as [S1' S2'].
assert (Rce : ret_ok (0x12b3d8 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (R4e : ret_ok (0x64c64 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
#[local] Ltac maddr0 z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
eexists. split.
- stepret (ltac:(oF' 0x125988%Z)) (ltac:(oD' 0x125988%Z)) (0x12b3d8 : word) ltac:(rwH; reflexivity).
stepld (ltac:(oF' 0x12b3d8%Z)) (ltac:(oD' 0x12b3d8%Z)) (0x64c64 : word) ltac:(maddr0 (s - 2136)%Z; exact RA).
stepiv (ltac:(oF' 0x12b3dc%Z)) (ltac:(oD' 0x12b3dc%Z)) (Z_to_bv 64 (s - 2128)) ltac:(wval).
stepn (ltac:(oF' 0x12b3e0%Z)) (ltac:(oD' 0x12b3e0%Z)).
stepn (ltac:(oF' 0x113c7c%Z)) (ltac:(oD' 0x113c7c%Z)).
stepn (ltac:(oF' 0x113c80%Z)) (ltac:(oD' 0x113c80%Z)).
stepb_tk (ltac:(oF' 0x113c84%Z)) (ltac:(oD' 0x113c84%Z)) ltac:(cond).
stepret (ltac:(oF' 0x113cb0%Z)) (ltac:(oD' 0x113cb0%Z)) (0x64c64 : word) ltac:(rwH; reflexivity).
stepb_ft (ltac:(oF' 0x64c64%Z)) (ltac:(oD' 0x64c64%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x64c68%Z)) (ltac:(oD' 0x64c68%Z)) ltac:(rwH; unfold c_lts, bv_lts; rewrite !signed64_small by lia;
first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.leb_le | apply Z.leb_gt]; lia).
stepiv (ltac:(oF' 0x64cc4%Z)) (ltac:(oD' 0x64cc4%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepld (ltac:(oF' 0x64cc8%Z)) (ltac:(oD' 0x64cc8%Z)) ra ltac:(maddr0 (s - 8)%Z; exact R1).
stepld (ltac:(oF' 0x64ccc%Z)) (ltac:(oD' 0x64ccc%Z)) (getr regs0 8) ltac:(maddr0 (s - 16)%Z; exact R2).
stepld (ltac:(oF' 0x64cd0%Z)) (ltac:(oD' 0x64cd0%Z)) (getr regs0 9) ltac:(maddr0 (s - 24)%Z; exact R3).
stepld (ltac:(oF' 0x64cd4%Z)) (ltac:(oD' 0x64cd4%Z)) (getr regs0 18) ltac:(maddr0 (s - 32)%Z; exact R4).
stepld (ltac:(oF' 0x64cd8%Z)) (ltac:(oD' 0x64cd8%Z)) (getr regs0 19) ltac:(maddr0 (s - 40)%Z; exact R5).
stepld (ltac:(oF' 0x64cdc%Z)) (ltac:(oD' 0x64cdc%Z)) (getr regs0 20) ltac:(maddr0 (s - 48)%Z; exact R6).
stepiv (ltac:(oF' 0x64ce0%Z)) (ltac:(oD' 0x64ce0%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x64ce4%Z)) (ltac:(oD' 0x64ce4%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.
End SE.
End RDPOST0.
End FPX_1.
