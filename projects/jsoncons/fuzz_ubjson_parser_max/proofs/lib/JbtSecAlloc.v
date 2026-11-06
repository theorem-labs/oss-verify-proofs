(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac JbtDepotA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtSecAlloc () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtSecAlloc.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1andb"; "1bool"; "1option"; "2I"; "2and"; "2eq"; "3Z"; "0F"; "4bvmap"; "0M"; "5cell"; "5wr"; "6msteps"; "7art_sec_pre_mem"; "8getr"; "8mkst"]; ["8regupd"; "9loaded_segments"; ":add"; ":land"; ":le"; ":leb"; ":lt"; ":ltb"; ":modulo"; ":mul"; ":pow"; ":sub"; ":testbit"; "0fb"; "0fx"; "0i"]; ["0j"; "0k"; "0n"; "0nm"; "0q"; "0r"; "0raw"; "0regs"; "0rom"; "0s"; "0sec"; "0stat"; ";BV"; ";Z_to_bv"; ";bv"; "0x"]]).
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
Lemma sa_testbit_drop_low : ltac2:(TCodec.tc2 tcn__JbtSecAlloc "Q5'6&Dzr2%3221'4r4%6251&F&J+2r3%3221%5271%9271%>294'5'1&L&B&Ir7r5%>2=1%4231r6%7221%921E%:24F%=3<21p0?1p0A1p0L1pR0Q11pR2Q21pR<Q31pR:Q41").
Proof.
intros q r j i Hj Hr Hi.
replace i with ((i - j) + j)%Z by lia.
rewrite <- !Z.div_pow2_bits by lia.
f_equal. rewrite Z.div_add_l by lia. rewrite (Z.div_small r) by lia.
rewrite Z_div_mult by lia. lia.
Qed.
Lemma sa_testbit_mask : ltac2:(TCodec.tc2 tcn__JbtSecAlloc "Q1'6'4&Dzr2%3221r3%5231%7231'5'1&L&K&J+2r5%3221r4%5241%7231%921>&0&E%126A&G%12C:%5231%B3A71p0G1p0E1pR0N1pR2O1pR4Q01").
Proof.
intros k j i Hjk Hi.
replace (2 ^ k - 2 ^ j)%Z with (Z.ones (k - j) * 2 ^ j)%Z.
2:{ unfold Z.ones. rewrite Z.shiftl_1_l, <- Z.sub_1_r, Z.mul_sub_distr_r, <- Z.pow_add_r by lia. replace (k - j + j)%Z with k by lia. lia. }
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
- rewrite Z.mul_pow2_bits by lia. replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
destruct (Z.lt_ge_cases i k) as [Hk|Hk].
+ rewrite Z.ones_spec_low by lia. symmetry. apply Z.ltb_lt. lia.
+ rewrite Z.ones_spec_high by lia. symmetry. apply Z.ltb_ge. lia.
Qed.
Lemma sa_land_down : ltac2:(TCodec.tc2 tcn__JbtSecAlloc "Q0'6'4&Dzr2%3221r3%5231%7231&F&J+2r4%3221%52:1%>2:1'5&C&Kr5%:291%3218%52@1&H%12B;%72C1%:3J41p0<1p0D1pS0M1pR2N1pR4O1").
Proof.
intros k j x Hjk Hx.
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hm.
set (q := (x / 2 ^ j)%Z) in *. set (r := (x mod 2 ^ j)%Z) in *.
replace (x - r)%Z with (q * 2 ^ j)%Z by lia.
rewrite Hdm. replace (2 ^ j * q + r)%Z with (q * 2 ^ j + r)%Z by lia.
assert (Hq : (0 <= q)%Z) by lia.
assert (Hqk : (q * 2 ^ j < 2 ^ k)%Z) by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, sa_testbit_mask by lia.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- replace (j <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
rewrite andb_false_r. symmetry. apply Z.mul_pow2_bits_low. lia.
- rewrite sa_testbit_drop_low by lia. replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
destruct (Z.lt_ge_cases i k) as [Hik|Hik].
+ replace (i <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia). now rewrite andb_true_r.
+ replace (i <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
symmetry. destruct (Z.eq_dec (q * 2 ^ j) 0) as [E|NE]; [rewrite E; apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2 ^ k)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
Definition art_sec_pre_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (stat sec msz n nm : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4
(Wn 8 (Wn 8 (Wn 8 (Wn 8
(Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
(s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
(s - 56) (U (getr rg 21))) (s - 64) (U (getr rg 22))) (s - 72) (U (getr rg 23))) (s - 80) (U (getr rg 24))) (s - 88) (U (getr rg 25)))
(s - 104) 0x569a0) (s - 112) stat) (s - 120) sec) (s - 128) msz)
(s - 132) 34)
(s - 152) 0x8cf2c) (s - 160) nm) (s - 168) msz) (s - 176) 0x1cc4e0) (s - 184) n) (s - 192) (U (getr rg 20))) (s - 200) 8.
Section SE.
Local Abbreviation SEC_T_art_sec_pre_fn := (ltac2:(TCodec.tc2 tcn__JbtSecAlloc "WI&8y5'Q>yR0%211%5241'2y8%611%311p061'6'5&>r<(Q<+1(3%33A21%6251r9%93A21r=+2%93G17%<231&Q=%12H7%@3H31r>+:%@3N1>%C231%E3M16r?+;%E3Q31C%H231%J3Q21;r@+<%J3Q81H%M231%O3Q71@rA+=%O3Q=1M%Q2231+8%G2Q>1%Q63Q>31&D+Vb\P0&K+]0%22J1%5241&F&J+Q?%22Q51%42K1'4+RPP0%721Q:+Q8%82Q;1%:2Q=1%6241&I+TP0%221QA%C21Q;%D221%QN3QOQ=1%F2Q>QK%7261%D21Q;%928QA%L2Q=1%B231rB%O2C1&BrC+QP0%3221%N21Q3%Q52IQA%Q02QBM%L221+`0%92Q@1%Q421Q9z%Q<21QC+X0%Q82QE1%Q4231&C%12CRD%RI3RJ17&;&ArMrJ%QE21QD%54431QE&:rNu8%358261Q9rO+QV`l8+QVho8%75<3251rQ0rH%:5?2481rQ1+QV`l0+QiaW0%>5C32<1rQ2%@5E13>QFrQ3+QV`l@%C5H21AFrQ4rK+X4%Q@221u1%I5N521L'<&?vNrQ6+ZjW4%SL3T81SJ/01T8rQ5%756521>&@+acj8%SG2T>1%339T01+T@%RO2I1%SK2TB1%734SN1%T83TFS7T6%SN2TEQ@%:3321+9%T<3TJ1T:%RG2RFQ?%R:21RG%T42TK1%@3641%T62TMR2%B32T21%C31SN4+3%T:2U11%F33SL1+Q2%T=2U41%I33SJ1+>%TK3U91TI+R0%SB2TE1%SH21TM%TD2U;1%Q03751+?%U23U@1U0%Q3331B+A%U53UC1U3+VN%TL2UC1%Q83531+B%U:3UH1U8%U02UGR1%Q<3421+C%U>3UL1U<%U42UKR>%Q@3421+D%UB3V01U@%UE2QI1%QD3421+E%UF3V41UD%QG331TE+H%UI3V71UG+7%U@2V71%QL3531+a]_H%UN3V:1UL/01V:&=%19R3RERCR7RLRIQCS0S8%R:5R9631RA%R<3S;R41p0R>1p0RE1p0RI1p0RL1p0S11p0S51p0S:1p0S?1p0SF1p0SJ1p0T01p0T61p0T51p0T91p0T?1p0TB1p0TI1p0U01p0U81p0U>1p0UE1p0UM1p0V31p0V91p0V?1p0VG1pQLW21p@W31pR8W41pR:W51pR6W61pRHW71pRFW81pRDW91pR>WA1pRBW<1pDW=1pR@WC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 4%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 5%nat 0%nat).
Variable stat : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 7%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 8%nat 0%nat).
Variable nm : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 9%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 10%nat 0%nat).
Variable fb : ltac:(sec_ty2 constr:(SEC_T_art_sec_pre_fn) 11%nat 0%nat).
Lemma art_sec_pre_fn : ltac:(sec_stmt2 constr:(SEC_T_art_sec_pre_fn) 12%nat 0%nat).
Proof using Type regs M rom raw s sec stat n q nm F fb.
intros H1 H2 H10 H11 H12 H13 Hs Hs' Hn Hq Hq' Hsec Hsec' Hnm HF HF' Hfb Hfb1 W Cpg Cg30 Cnm Cg28 Cpc Cg38 Cfl.
zstep (ltac:(oF' 0x568e4%Z)) (ltac:(oD' 0x568e4%Z)).
zsd (ltac:(oF' 0x568e8%Z)) (ltac:(oD' 0x568e8%Z)) (s - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x568ec%Z)) (ltac:(oD' 0x568ec%Z)) (s - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x568f0%Z)) (ltac:(oD' 0x568f0%Z)) (s - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x568f4%Z)) (ltac:(oD' 0x568f4%Z)) (s - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x568f8%Z)) (ltac:(oD' 0x568f8%Z)) (s - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x568fc%Z)) (ltac:(oD' 0x568fc%Z)) (s - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x56900%Z)) (ltac:(oD' 0x56900%Z)) (s - 56) (U (getr regs 21)) ltac:(rewok W).
zsd (ltac:(oF' 0x56904%Z)) (ltac:(oD' 0x56904%Z)) (s - 64) (U (getr regs 22)) ltac:(rewok W).
zsd (ltac:(oF' 0x56908%Z)) (ltac:(oD' 0x56908%Z)) (s - 72) (U (getr regs 23)) ltac:(rewok W).
zsd (ltac:(oF' 0x5690c%Z)) (ltac:(oD' 0x5690c%Z)) (s - 80) (U (getr regs 24)) ltac:(rewok W).
zsd (ltac:(oF' 0x56910%Z)) (ltac:(oD' 0x56910%Z)) (s - 88) (U (getr regs 25)) ltac:(rewok W).
zstep (ltac:(oF' 0x56914%Z)) (ltac:(oD' 0x56914%Z)).
zstep (ltac:(oF' 0x56918%Z)) (ltac:(oD' 0x56918%Z)).
zstep (ltac:(oF' 0x5691c%Z)) (ltac:(oD' 0x5691c%Z)).
zbft (ltac:(oF' 0x56920%Z)) (ltac:(oD' 0x56920%Z)).
zstep (ltac:(oF' 0x56924%Z)) (ltac:(oD' 0x56924%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg1 : cellA X sec 8 4096) by zcell end.
zld (ltac:(oF' 0x56928%Z)) (ltac:(oD' 0x56928%Z)) sec Cpg1.
zstep (ltac:(oF' 0x5692c%Z)) (ltac:(oD' 0x5692c%Z)).
zstep (ltac:(oF' 0x56930%Z)) (ltac:(oD' 0x56930%Z)).
zbft (ltac:(oF' 0x56934%Z)) (ltac:(oD' 0x56934%Z)).
zstep (ltac:(oF' 0x56938%Z)) (ltac:(oD' 0x56938%Z)).
zstep (ltac:(oF' 0x5693c%Z)) (ltac:(oD' 0x5693c%Z)).
zstep (ltac:(oF' 0x56940%Z)) (ltac:(oD' 0x56940%Z)).
zstep (ltac:(oF' 0x56944%Z)) (ltac:(oD' 0x56944%Z)).
assert (RU : (n + 4095) mod 4096 = n + 4095 - 4096 * q) by (symmetry; apply (Z.mod_unique_pos (n + 4095) 4096 q); lia).
stepn (ltac:(oF' 0x56948%Z)) (ltac:(oD' 0x56948%Z)). rwH.
replace (n + 4096 + -1) with (n + 4095) by lia.
rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
replace (n + 4095 - (n + 4095) mod 4096) with (4096 * q) by lia.
zstep (ltac:(oF' 0x5694c%Z)) (ltac:(oD' 0x5694c%Z)).
zstep (ltac:(oF' 0x56950%Z)) (ltac:(oD' 0x56950%Z)).
zstep (ltac:(oF' 0x56954%Z)) (ltac:(oD' 0x56954%Z)).
zstep (ltac:(oF' 0x56958%Z)) (ltac:(oD' 0x56958%Z)).
zstep (ltac:(oF' 0x5695c%Z)) (ltac:(oD' 0x5695c%Z)).
zbtk (ltac:(oF' 0x56960%Z)) (ltac:(oD' 0x56960%Z)).
zstep (ltac:(oF' 0x56988%Z)) (ltac:(oD' 0x56988%Z)).
stepn (ltac:(oF' 0x5698c%Z)) (ltac:(oD' 0x5698c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (C30 : cellA X 0x134388 8 0x1363e8) by zcell; assert (Cnm' : cellA X 0x1363e8 8 nm) by zcell;
assert (C28 : cellA X 0x134380 8 0x1cc4e0) by zcell; assert (Cpc' : cellA X 0x1cc4e0 8 4096) by zcell;
assert (C38 : cellA X 0x134390 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
zld (ltac:(oF' 0x56990%Z)) (ltac:(oD' 0x56990%Z)) 0x134388 C30.
zld (ltac:(oF' 0x56994%Z)) (ltac:(oD' 0x56994%Z)) 0x1363e8 Cnm'.
zstep (ltac:(oF' 0x56998%Z)) (ltac:(oD' 0x56998%Z)).
stepn (ltac:(oF' 0x5699c%Z)) (ltac:(oD' 0x5699c%Z)).
zstep (ltac:(oF' 0x8cec0%Z)) (ltac:(oD' 0x8cec0%Z)).
zsd (ltac:(oF' 0x8cec4%Z)) (ltac:(oD' 0x8cec4%Z)) (s - 104) 0x569a0 ltac:(rewok W).
zsd (ltac:(oF' 0x8cec8%Z)) (ltac:(oD' 0x8cec8%Z)) (s - 112) stat ltac:(rewok W).
zsd (ltac:(oF' 0x8cecc%Z)) (ltac:(oD' 0x8cecc%Z)) (s - 120) sec ltac:(rewok W).
zsd (ltac:(oF' 0x8ced0%Z)) (ltac:(oD' 0x8ced0%Z)) (s - 128) (4096 * q + 4096) ltac:(rewok W).
zstep (ltac:(oF' 0x8ced4%Z)) (ltac:(oD' 0x8ced4%Z)).
stepn (ltac:(oF' 0x8ced8%Z)) (ltac:(oD' 0x8ced8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C28b : cellA X 0x134380 8 0x1cc4e0) by zcell; assert (Cpcb : cellA X 0x1cc4e0 8 4096) by zcell end.
zld (ltac:(oF' 0x8cedc%Z)) (ltac:(oD' 0x8cedc%Z)) 0x134380 C28b.
zld (ltac:(oF' 0x8cee0%Z)) (ltac:(oD' 0x8cee0%Z)) 0x1cc4e0 Cpcb.
zstep (ltac:(oF' 0x8cee4%Z)) (ltac:(oD' 0x8cee4%Z)).
zbtk (ltac:(oF' 0x8cee8%Z)) (ltac:(oD' 0x8cee8%Z)).
zstep (ltac:(oF' 0x8cef8%Z)) (ltac:(oD' 0x8cef8%Z)). zstep (ltac:(oF' 0x8cefc%Z)) (ltac:(oD' 0x8cefc%Z)).
zbft (ltac:(oF' 0x8cf00%Z)) (ltac:(oD' 0x8cf00%Z)).
zstep (ltac:(oF' 0x8cf04%Z)) (ltac:(oD' 0x8cf04%Z)). zstep (ltac:(oF' 0x8cf08%Z)) (ltac:(oD' 0x8cf08%Z)). zstep (ltac:(oF' 0x8cf0c%Z)) (ltac:(oD' 0x8cf0c%Z)).
stepn (ltac:(oF' 0x8cf10%Z)) (ltac:(oD' 0x8cf10%Z)). rwH.
replace (4096 * q + 4096 + 4096 + -1) with (4096 * q + 8191) by lia.
rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
replace (4096 * q + 8191 - (4096 * q + 8191) mod 4096) with (4096 * q + 4096)
by (rewrite (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) || (symmetry; erewrite <- (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) by lia; lia); lia).
zstep (ltac:(oF' 0x8cf14%Z)) (ltac:(oD' 0x8cf14%Z)).
zsw (ltac:(oF' 0x8cf18%Z)) (ltac:(oD' 0x8cf18%Z)) (s - 132) 34 ltac:(rewok W).
zstep (ltac:(oF' 0x8cf1c%Z)) (ltac:(oD' 0x8cf1c%Z)). zstep (ltac:(oF' 0x8cf20%Z)) (ltac:(oD' 0x8cf20%Z)). zstep (ltac:(oF' 0x8cf24%Z)) (ltac:(oD' 0x8cf24%Z)).
stepn (ltac:(oF' 0x8cf28%Z)) (ltac:(oD' 0x8cf28%Z)).
zstep (ltac:(oF' 0x8d9a0%Z)) (ltac:(oD' 0x8d9a0%Z)).
zsd (ltac:(oF' 0x8d9a4%Z)) (ltac:(oD' 0x8d9a4%Z)) (s - 152) 0x8cf2c ltac:(rewok W).
zsd (ltac:(oF' 0x8d9a8%Z)) (ltac:(oD' 0x8d9a8%Z)) (s - 160) nm ltac:(rewok W).
zsd (ltac:(oF' 0x8d9ac%Z)) (ltac:(oD' 0x8d9ac%Z)) (s - 168) (4096 * q + 4096) ltac:(rewok W).
zsd (ltac:(oF' 0x8d9b0%Z)) (ltac:(oD' 0x8d9b0%Z)) (s - 176) 0x1cc4e0 ltac:(rewok W).
zsd (ltac:(oF' 0x8d9b4%Z)) (ltac:(oD' 0x8d9b4%Z)) (s - 184) n ltac:(rewok W).
zsd (ltac:(oF' 0x8d9b8%Z)) (ltac:(oD' 0x8d9b8%Z)) (s - 192) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x8d9bc%Z)) (ltac:(oD' 0x8d9bc%Z)) (s - 200) 8 ltac:(rewok W).
zstep (ltac:(oF' 0x8d9c0%Z)) (ltac:(oD' 0x8d9c0%Z)).
zstep (ltac:(oF' 0x8d9c4%Z)) (ltac:(oD' 0x8d9c4%Z)).
zbft (ltac:(oF' 0x8d9c8%Z)) (ltac:(oD' 0x8d9c8%Z)).
zstep (ltac:(oF' 0x8d9cc%Z)) (ltac:(oD' 0x8d9cc%Z)).
stepn (ltac:(oF' 0x8d9d0%Z)) (ltac:(oD' 0x8d9d0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x134390 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
zld (ltac:(oF' 0x8d9d4%Z)) (ltac:(oD' 0x8d9d4%Z)) 0x134390 C38c.
zlbu (ltac:(oF' 0x8d9d8%Z)) (ltac:(oD' 0x8d9d8%Z)) (F + 260) Cflc.
stepn (ltac:(oF' 0x8d9dc%Z)) (ltac:(oD' 0x8d9dc%Z)). rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
zbtk (ltac:(oF' 0x8d9e0%Z)) (ltac:(oD' 0x8d9e0%Z)).
stepn (ltac:(oF' 0x8daf0%Z)) (ltac:(oD' 0x8daf0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (R1 : cellA X (s - 152) 8 0x8cf2c) by zcell; assert (R2 : cellA X (s - 160) 8 nm) by zcell;
assert (R3 : cellA X (s - 168) 8 (4096 * q + 4096)) by zcell; assert (R4 : cellA X (s - 176) 8 0x1cc4e0) by zcell;
assert (R5 : cellA X (s - 184) 8 n) by zcell; assert (R6 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
assert (R7 : cellA X (s - 200) 8 8) by zcell; assert (R8 : cellA X (s - 132) 4 34) by zcell end.
zld (ltac:(oF' 0x8daf4%Z)) (ltac:(oD' 0x8daf4%Z)) (s - 152) R1.
zld (ltac:(oF' 0x8daf8%Z)) (ltac:(oD' 0x8daf8%Z)) (s - 160) R2.
zld (ltac:(oF' 0x8dafc%Z)) (ltac:(oD' 0x8dafc%Z)) (s - 168) R3.
zld (ltac:(oF' 0x8db00%Z)) (ltac:(oD' 0x8db00%Z)) (s - 176) R4.
zld (ltac:(oF' 0x8db04%Z)) (ltac:(oD' 0x8db04%Z)) (s - 184) R5.
zld (ltac:(oF' 0x8db08%Z)) (ltac:(oD' 0x8db08%Z)) (s - 192) R6. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8db0c%Z)) (ltac:(oD' 0x8db0c%Z)) (s - 200) R7.
zstep (ltac:(oF' 0x8db10%Z)) (ltac:(oD' 0x8db10%Z)).
stepret (ltac:(oF' 0x8db14%Z)) (ltac:(oD' 0x8db14%Z)) (Z_to_bv 64 0x8cf2c : word) ltac:(rwH; reflexivity).
zlw (ltac:(oF' 0x8cf2c%Z)) (ltac:(oD' 0x8cf2c%Z)) (s - 132) R8.
zstep (ltac:(oF' 0x8cf30%Z)) (ltac:(oD' 0x8cf30%Z)). zstep (ltac:(oF' 0x8cf34%Z)) (ltac:(oD' 0x8cf34%Z)). zstep (ltac:(oF' 0x8cf38%Z)) (ltac:(oD' 0x8cf38%Z)). zstep (ltac:(oF' 0x8cf3c%Z)) (ltac:(oD' 0x8cf3c%Z)). zstep (ltac:(oF' 0x8cf40%Z)) (ltac:(oD' 0x8cf40%Z)).
stepn (ltac:(oF' 0x8cf44%Z)) (ltac:(oD' 0x8cf44%Z)).
zstep (ltac:(oF' 0x8b5f4%Z)) (ltac:(oD' 0x8b5f4%Z)).
unfold art_sec_pre_mem. zret.
Qed.
End SE.
End FPX.
