(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0MemIsZero () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0MemIsZero.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0MemIsZero.FPX_1.Walk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1andb"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3repeat"; "4Z"]; ["5word_to_le_bytes"; "6bvmap"; "7wbytes"; "8msteps"; ":l1_inv"; ":l1_post"; ":l2_inv"; ":l2_post"; ":l3_inv"; ":l3_post"; ":mid_post"; ":pro_post"; "9kcs2"; ";getr"; ";mkst"; ";rdn"]; [";regupd"; "<callee_saved"; "<keeps_cs"; "=loaded_segments"; ">In"; "?add"; "?land"; "?le"; "?leb"; "?lt"; "?ltb"; "?max"; "?min"; "?modulo"; "?mul"; "?of_nat"]; ["?pow"; "?sub"; "?testbit"; "0ab"; "0ae"; "0b"; "0beg"; "0e"; "0fx"; "0i"; "0j"; "0k"; "0mem0"; "0n"; "0q"; "0r"]; ["0r1"; "0r2"; "0r3"; "0ra"; "0rd"; "0regs"; "0regs'"; "0rom"; "0s"; "0sp"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0v"; "0x"]; ["0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Lemma testbit_drop_low' : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "Q5'?&Q7zr2%3221'9r4%6251&Q9&Q@+2r3%3221%5271%9271%>294':'2&QB&Q5&Q>r7r5%>2=1%4231r6%7221%921E%:24F%=3<21p0?1p0A1p0L1pSDQ11pSFQ21pT0Q31pSNQ41").
Proof.
intros q r j i Hj Hr Hi.
replace i with ((i - j) + j)%Z by lia.
rewrite <- !Z.div_pow2_bits by lia.
f_equal. rewrite Z.div_add_l by lia. rewrite (Z.div_small r) by lia.
rewrite Z_div_mult by lia. lia.
Qed.
Lemma testbit_m8 : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "K'?&Q7zr1%3221':'2&QB&QA&Q@+2+R0%3221+8%6221r2%9221&1&Q8+3%2215&Q:%127;%6231%C3B81p0E1pSDJ1").
Proof.
intros i Hi.
replace (2 ^ 64 - 8)%Z with ((2 ^ 61 - 1) * 2 ^ 3)%Z by reflexivity.
destruct (Z.lt_ge_cases i 3) as [Hlt|Hge].
- rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
- rewrite Z.mul_pow2_bits by lia. replace (2 ^ 61 - 1)%Z with (Z.ones 61) by reflexivity.
replace (3 <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
destruct (Z.lt_ge_cases i 64) as [H64|H64].
+ rewrite Z.ones_spec_low by lia. symmetry. apply Z.ltb_lt. lia.
+ rewrite Z.ones_spec_high by lia. symmetry. apply Z.ltb_ge. lia.
Qed.
Lemma land_down8 : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "J'?'9&Q7zr1%3221&Q9&Q@+2+R0%3221%5271%;271':&Q6r2&QA+8%2281%5241&Q=%1264%6271%:3G41p0<1pU0I1").
Proof.
intros x Hx.
pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
set (q := (x / 8)%Z) in *. set (r := (x mod 8)%Z) in *.
replace (x - r)%Z with (q * 2 ^ 3)%Z by lia.
rewrite Hdm. replace (8 * q + r)%Z with (q * 2 ^ 3 + r)%Z by lia.
assert (Hq : (0 <= q < 2 ^ 61)%Z) by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_m8 by lia.
destruct (Z.lt_ge_cases i 3) as [Hlt|Hge].
- replace (3 <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
rewrite andb_false_r. symmetry. apply Z.mul_pow2_bits_low. lia.
- rewrite testbit_drop_low' by lia. replace (3 <=? i)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
+ replace (i <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). now rewrite andb_true_r.
+ replace (i <? 64)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
rewrite Z.mul_pow2_bits by lia. symmetry.
destruct (Z.eq_dec q 0) as [->|Hq0]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 61); [apply Z.log2_lt_pow2; lia | lia].
Qed.
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
gres; rwH; unfold at_, v_addi, v_add, v_sub; imm_norm; unorm; first [reflexivity | f_equal; lia].
Definition kcs2 (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, In r callee_saved -> r <> 2%bv -> getr regs' r = getr regs r.
#[using="Type"] Lemma kcs2_refl : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero ":&Ay5'R<yR0%211%5241&Lr1%2211pT<41"). Proof. intros regs r _ _. reflexivity. Qed.
#[using="Type"] Lemma kcs2_trans : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "A&Ay5'R<yR0%211%5241&Lr3r2%3221r5%5214p031p041pT691pT4:1pT2;1").
Proof. intros r1 r2 r3 A B r Hr H2. rewrite (B r Hr H2). apply A; assumption. Qed.
#[using="Type"] Lemma kcs2_upd : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "Q3&Ay5'R<yR0%211%5241%415&Lr4r3%3221'=&<&Q4&Q1%23961%411':(R:+2(8%33D21%53@=1%<271r6&Q0r5%231CB%E241p061p0D1pTNK1pT:J1pT>L1pT<M1").
Proof.
intros regs regs' rd v K Hn r Hr H2. rewrite getr_other; [apply K; assumption|]. intros ->. destruct Hn as [Hn|Hn]; [exact (Hn Hr)|exact (H2 Hn)].
Qed.
#[using="Type"] Lemma kcs2_keeps_cs : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "M&Ay5'R<yR0%211%5241&Lr3r2%3221':&Mr4(R:+2(8%33?21%6251%83>1:&Q2r5&Q0%13:6?%4231p061p0@1pTNF1pT>F1pT<G1").
Proof.
intros regs regs' v K Hv r Hr. destruct (decide (r = 2%bv)) as [->|Hne].
- rewrite getr_same by (intro X; discriminate X). symmetry. exact Hv.
- rewrite getr_other by exact Hne. apply K; assumption.
Qed.
#[using="Type"] Lemma kcs2_upd_same : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "Q4&Ay5'R<yR0%211%5241%415&Lr4r3%3221':&Mr5%2215r2%53<21&<(R:z(8%33D21%;3@>1%611r7&Q0r6%231>C%E241p061p0>1p0E1pTNL1pT:K1pT>M1pT<N1").
Proof.
intros regs regs' rd v K Hv Hnz r Hr H2. destruct (decide (r = rd)) as [->|Hne].
- rewrite getr_same by exact Hnz. symmetry. exact Hv.
- rewrite getr_other by exact Hne. apply K; assumption.
Qed.
#[using="Type"] Lemma kcs2_to_keeps_cs : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "K&Ay5'R<yR0%211%5241&Lr2r1%3221':&M(R:+2(8%33>21%5291r3%7213%93?31&Q2r4%2215p041p0?1pT>D1pT<E1").
Proof.
intros regs regs' K H2 r Hr. destruct (decide (r = 2%bv)) as [->|Hne]; [exact H2 | apply K; assumption].
Qed.
Ltac solve_kcs2 :=
repeat (first [ apply kcs2_upd; [| first [right; reflexivity | left; not_kept] ]
| apply kcs2_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
first [apply kcs2_refl | assumption].
Section Walk.
Variable mem0 : word -> option byte.
Variables beg sp ra : word.
Variables n b s e ab ae : Z.
Variable rom : word -> option byte.
Hypothesis Hb_def : bv_unsigned beg = b.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis He_def : e = (b + n)%Z.
Hypothesis Hab_def : ab = (b + 7 - (b + 7) mod 8)%Z.
Hypothesis Hae_def : ae = (e - e mod 8)%Z.
Hypothesis Hn : (0 < n <= 2 ^ 40)%Z.
Hypothesis He : (b + n + 8 < 2 ^ 64)%Z.
Hypothesis Hs : (16 <= s)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hdisj : (b + n <= s - 8 \/ s <= b)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 8)) 8%nat = true.
Hypothesis Hret : ret_ok ra.
Hypothesis HZ : forall x : word, (b <= bv_unsigned x < b + n)%Z -> mem0 x = Some (Z_to_bv 8 0).
#[local] Notation M1 := (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (only parsing).
#[using="beg Hb_def"] Lemma b_range : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "<'9&Q7zvQE%3221&Q9&Q@+2+R0%3221%5271%;271"). Proof. rewrite <- Hb_def. apply u64_range. Qed.
#[using="Hb_def"] Lemma beg_b : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "9':'R<yR0%211vQF&R;vQE%2251%83541"). Proof. rewrite <- Hb_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="Hs_def"] Lemma sp_s : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "9':'R<yR0%211vR9&R;vR8%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="n s e He_def Hab_def Hn Hs"] Lemma ab_range : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "B'9&Q7vQEvQC%3221&Q5+7%2251%7251%9251':'?&Q=+8%22;1z%63521%A281").
Proof. rewrite Hab_def. pose proof (Z.mod_pos_bound (b + 7) 8 ltac:(lia)). pose proof (Z.div_mod (b+7) 8 ltac:(lia)).
split; [lia|]. replace (b + 7 - (b + 7) mod 8)%Z with (8 * ((b + 7) / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
#[using="beg n b s Hb_def He_def Hae_def Hn Hs"] Lemma ae_range : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "D'9&Q7&Q;z&QAvQG+7%3221%6251vQD%9221%:226%<221':'?&Q=+8%2281%5341?%C271").
Proof. rewrite Hae_def. pose proof (Z.mod_pos_bound e 8 ltac:(lia)). pose proof (Z.div_mod e 8 ltac:(lia)). pose proof b_range.
assert (0 <= e / 8)%Z by (apply Z.div_pos; lia).
split; [lia|]. replace (e - e mod 8)%Z with (8 * (e / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
#[using="beg e Hb_def He_def Hn Hs Hdisj HZ"] Lemma M1_zero : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "Q:'R<yR0%211'9&Q7vQE&R=r1%2271%5241&Q9&Q5vQM%2281%4261%<261':'7y8%C11%311&BvQL&R;&QAvR8+8%3221%52K1&@u8vR3%3221r2%=4<621(0z%>2C1%32C1%G3C51p0I1pU0Q71").
Proof.
intros x Hx. pose proof b_range.
destruct Hdisj as [Hd|Hd].
- rewrite wbytes_below; [apply HZ; exact Hx | rewrite length_N_to_le_bytes; cbn [Z.of_nat]; unorm; lia | unorm; lia].
- rewrite wbytes_above; [apply HZ; exact Hx | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
#[using="beg e Hb_def He_def Hn He Hs Hdisj HZ"] Lemma rdn1_M1 : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "QC'?'9&Q7vQEr1%3221&Q9&Q5vQM%2261%4261%:261':'7'4'R<y8%211%411%611&O&Q3&BvQL&R;yR0&QAvR8+8%3221%6251&@u8vR3%3221%=3<51r2%=2<1u1%C4B421(0(3z%C2K1(6%11L%53M31%72M1%Q43M91p0Q61pU2QB1").
Proof.
intros z Hz. pose proof b_range. cbn [rdn]. rewrite (M1_zero (Z_to_bv 64 z)) by (unorm; lia). reflexivity.
Qed.
#[using="beg e Hb_def He_def Hn He Hs Hdisj HZ"] Lemma rdn8_M1 : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "Q@'?&Q7vQEr1%3221&Q5r2+8%3221vQM%5281%:231':'7'4'R<y8%211%411%611&O&Q3&BvQL&R;yR0&QAvR8%221E%5241&@u8vR3%3221%<3;51r3%<2;1%A4@316(0&>z%A2I1%33I1;%52I1%Q03I71p0Q21p0Q:1pU2Q?1").
Proof.
intros z Hz1 Hz2. pose proof b_range. apply rdn_const; [cbn [Z.of_nat Pos.to_nat]; unorm; lia|].
intros x Hx. apply M1_zero. cbn [Z.of_nat Pos.to_nat] in Hx. rewrite u_Z2bv in Hx by lia. lia.
Qed.
Definition pro_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = beg /\ getr rg 11 = Z_to_bv 64 0 /\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 13 = Z_to_bv 64 n
/\ getr rg 14 = Z_to_bv 64 e /\ getr rg 15 = Z_to_bv 64 ab /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
Section SE.
Local Abbreviation SEC_T_pro_run := (ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "R=&Ay5'R<yR0%211%5241':&Mr1(R:+:(8%33;21%6251vQF%93;21r2+;%93A17%<231&R;vQM%22C1%A3C41r3+2%A3I1?%D231vR9%G3I21r4+1%G3O1E%J231vR3%M3O21';'9'C&Q3&NvQHr6+a\RD%Q33Q91Q1/01Q9vQLvR7%8576321+a\T4%Q93Q?1Q7/01Q?&B&QAvR8+8%3221%Q52QF1&@u8%221J%93?41%F5EQF;1?%I3H?1&K%11QI&L%12IQK%O231%Q0261qT>R11%Q32R21p0Q51p0Q<1p0QC1p0QL1pT<R71")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_pro_run) 0%nat 0%nat).
Lemma pro_run : ltac:(sec_stmt2 constr:(SEC_T_pro_run) 1%nat 0%nat).
Proof using b Hb_def Hs_def He_def Hab_def Hae_def Hn He Hs Hdisj Hok regs.
intros H10 H11 H2 H1.
pose proof b_range as Hb. pose proof ab_range as Hab. pose proof ae_range as Hae.
rewrite beg_b in H10. rewrite sp_s in H2.
eexists. split.
- stepiv (ltac:(oF' 0x8b054%Z)) (ltac:(oD' 0x8b054%Z)) (Z_to_bv 64 (s - 16)) ltac:(wval).
stepsd (ltac:(oF' 0x8b058%Z)) (ltac:(oD' 0x8b058%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(exact Hok).
stepiv (ltac:(oF' 0x8b05c%Z)) (ltac:(oD' 0x8b05c%Z)) (Z_to_bv 64 n) ltac:(wval).
stepn (ltac:(oF' 0x8b060%Z)) (ltac:(oD' 0x8b060%Z)).
stepn (ltac:(oF' 0x8b064%Z)) (ltac:(oD' 0x8b064%Z)).
stepn (ltac:(oF' 0x8b068%Z)) (ltac:(oD' 0x8b068%Z)).
stepb_ft (ltac:(oF' 0x8b06c%Z)) (ltac:(oD' 0x8b06c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x8b070%Z)) (ltac:(oD' 0x8b070%Z)).
stepiv (ltac:(oF' 0x8b074%Z)) (ltac:(oD' 0x8b074%Z)) (Z_to_bv 64 e) ltac:(rewrite He_def; wval).
stepiv (ltac:(oF' 0x8b078%Z)) (ltac:(oD' 0x8b078%Z)) (Z_to_bv 64 (b + 7)) ltac:(wval).
stepiv (ltac:(oF' 0x8b07c%Z)) (ltac:(oD' 0x8b07c%Z)) (Z_to_bv 64 ab)
ltac:(gres; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; rewrite Hab_def; reflexivity).
stepiv (ltac:(oF' 0x8b080%Z)) (ltac:(oD' 0x8b080%Z)) (Z_to_bv 64 ae)
ltac:(gres; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; rewrite Hae_def; reflexivity).
apply mst_refl.
- split.
+ unfold pro_post. repeat split; gres; rwH; try reflexivity. symmetry; apply beg_b.
+ solve_kcs2.
Qed.
End SE.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mlbu0 F D z :=
chain_step; [reflexivity
| eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply rdn1_M1; lia]
| step_simpl; vnorm].
#[local] Ltac mld0 F D z :=
chain_step; [reflexivity
| eapply step_ld with (v := Z_to_bv 64 0); [exact F | reflexivity | exact D | maddr z; apply rdn8_M1; lia | reflexivity]
| step_simpl; vnorm].
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_kcs2.
Definition l1_inv (rg : bvmap 5 word) (k : Z) : Prop :=
getr rg 13 = Z_to_bv 64 (b + k + 1) /\ getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e /\ getr rg 15 = Z_to_bv 64 ab
/\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
Definition l1_post (rg : bvmap 5 word) : Prop :=
getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e /\ getr rg 15 = Z_to_bv 64 ab
/\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
#[using="beg n Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ"] Lemma loop1_run : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "R='5&Ay5'R<yR0%211%5241'?&Dr2r1%3221&Q7z%2215':&Q5r3&Q?r5%211%5241+1%7221&QA&Q<vQCvQG%3221vQE%6221%@3H81';'9'C&Q3&NvQHr6(R:+a\TD(8%33Q621/01Q6&BvQL&R;vR8+8%I221%42Q>1&@u8vR3%3221%;3:51vR7%E5DC>21+a\U<%D3QG1B/01QG%I5HQC165%L3K51&E%11QF&L%12LQH%Q2231%Q3261qT>QO1%Q62R01p0Q81p0QJ1p0QN1pSHR31pT<R51pSNR<1").
Proof.
induction q as [|q IH]; intros regs k (H13 & H11 & H14 & H15 & H12 & H10 & H2 & H1) Hk Hq;
pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
-
destruct (Z.le_gt_cases ab e) as [Hle|Hgt].
+
eexists. split.
* stepiv (ltac:(oF' 0x8b094%Z)) (ltac:(oD' 0x8b094%Z)) (Z_to_bv 64 (b + k + 1)) ltac:(wval).
mlbu0 (ltac:(oF' 0x8b098%Z)) (ltac:(oD' 0x8b098%Z)) (b + k)%Z.
stepn (ltac:(oF' 0x8b09c%Z)) (ltac:(oD' 0x8b09c%Z)).
stepb_tk (ltac:(oF' 0x8b0a0%Z)) (ltac:(oD' 0x8b0a0%Z)) ltac:(cond).
apply mst_refl.
* unfold l1_post. post.
+
eexists. split.
* stepiv (ltac:(oF' 0x8b094%Z)) (ltac:(oD' 0x8b094%Z)) (Z_to_bv 64 (b + k + 1)) ltac:(wval).
mlbu0 (ltac:(oF' 0x8b098%Z)) (ltac:(oD' 0x8b098%Z)) (b + k)%Z.
stepn (ltac:(oF' 0x8b09c%Z)) (ltac:(oD' 0x8b09c%Z)).
stepb_ft (ltac:(oF' 0x8b0a0%Z)) (ltac:(oD' 0x8b0a0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x8b0a4%Z)) (ltac:(oD' 0x8b0a4%Z)) (Z_to_bv 64 (b + k + 2)) ltac:(wval).
stepb_ft (ltac:(oF' 0x8b0a8%Z)) (ltac:(oD' 0x8b0a8%Z)) ltac:(cond).
apply mst_refl.
* unfold l1_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8b094 : word) M1 rom) (fun rg => l1_inv rg (k + 1) /\ kcs2 regs rg)).
+ eexists. split.
* stepiv (ltac:(oF' 0x8b094%Z)) (ltac:(oD' 0x8b094%Z)) (Z_to_bv 64 (b + k + 1)) ltac:(wval).
mlbu0 (ltac:(oF' 0x8b098%Z)) (ltac:(oD' 0x8b098%Z)) (b + k)%Z.
stepn (ltac:(oF' 0x8b09c%Z)) (ltac:(oD' 0x8b09c%Z)).
stepb_ft (ltac:(oF' 0x8b0a0%Z)) (ltac:(oD' 0x8b0a0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x8b0a4%Z)) (ltac:(oD' 0x8b0a4%Z)) (Z_to_bv 64 (b + k + 2)) ltac:(wval).
stepb_tk (ltac:(oF' 0x8b0a8%Z)) (ltac:(oD' 0x8b0a8%Z)) ltac:(cond).
apply mst_refl.
* unfold l1_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (k + 1)%Z I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]].
Qed.
Definition l2_inv (rg : bvmap 5 word) (j : Z) : Prop :=
getr rg 15 = Z_to_bv 64 (ab + 8 * j) /\ getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e
/\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
Definition l2_post (rg : bvmap 5 word) : Prop :=
getr rg 15 = Z_to_bv 64 ae /\ getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e
/\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
#[using="beg n Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ"] Lemma loop2_run : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "R<'5&Ay5'R<yR0%211%5241'?&Fr2r1%3221&Q7z%2215':&Q5vQC&Q>+8r3&Q?r5%211%8241+1%:221%9281%<2;1vQD%?3G21';'9'C&Q3&NvQHr6(R:+a\U@(8%33Q521/01Q5&BvQL&R;&QAvR8%221M%42Q=1&@u8vR3%3221%;3:51vR7%E5DC>21+a\V0%D3QF1B/01QF%I5HQB165%L3K51&G%11QE&L%12LQG%Q2231%Q3261qT>QN1%Q62QO1p0Q81p0QI1p0QM1pSFR21pT<R41pSNR;1").
Proof.
induction q as [|q IH]; intros regs j (H15 & H11 & H14 & H12 & H10 & H2 & H1) Hj Hq;
pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
- eexists. split.
+ mld0 (ltac:(oF' 0x8b0b0%Z)) (ltac:(oD' 0x8b0b0%Z)) (ab + 8 * j)%Z.
stepiv (ltac:(oF' 0x8b0b4%Z)) (ltac:(oD' 0x8b0b4%Z)) (Z_to_bv 64 (ab + 8 * (j + 1))) ltac:(wval).
stepn (ltac:(oF' 0x8b0b8%Z)) (ltac:(oD' 0x8b0b8%Z)).
stepb_ft (ltac:(oF' 0x8b0bc%Z)) (ltac:(oD' 0x8b0bc%Z)) ltac:(cond).
apply mst_refl.
+ unfold l2_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8b0b0 : word) M1 rom) (fun rg => l2_inv rg (j + 1) /\ kcs2 regs rg)).
+ eexists. split.
* mld0 (ltac:(oF' 0x8b0b0%Z)) (ltac:(oD' 0x8b0b0%Z)) (ab + 8 * j)%Z.
stepiv (ltac:(oF' 0x8b0b4%Z)) (ltac:(oD' 0x8b0b4%Z)) (Z_to_bv 64 (ab + 8 * (j + 1))) ltac:(wval).
stepn (ltac:(oF' 0x8b0b8%Z)) (ltac:(oD' 0x8b0b8%Z)).
stepb_tk (ltac:(oF' 0x8b0bc%Z)) (ltac:(oD' 0x8b0bc%Z)) ltac:(cond).
apply mst_refl.
* unfold l2_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (j + 1)%Z I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]].
Qed.
Definition l3_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 12 = Z_to_bv 64 (ae + i) /\ getr rg 14 = Z_to_bv 64 (e - ae - i) /\ getr rg 11 = Z_to_bv 64 0
/\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
Definition l3_post (rg : bvmap 5 word) : Prop :=
getr rg 11 = Z_to_bv 64 0 /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
#[using="beg n ab Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ"] Lemma loop3_run : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "R='5&Ay5'R<yR0%211%5241'?&Hr2r1%3221&Q7z%2215':&Q5vQDr3%3221&Q?r5%211%7241+1%9221vQG%<3D21vQE%A21<';'9'C&Q3&NvQHr7(R:+a\V<(8%33Q421/01Q4&BvQL&R;&QAvR8+8%3221%52Q=1&@u8vR3%3221%<3;51vR7%F5ED?21+a\W0%E3QF1C/01QF%J5IQB165%M3L51&I%11QE&L%12MQG%Q3231%Q4261qT>QN1%Q72QO1p0Q91p0Q<1p0QJ1p0QN1pSDR31pT<R51pSNR<1").
Proof.
induction q as [|q IH]; intros regs i (H12 & H14 & H11 & H2 & H1) Hi Hq Hbae;
pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
- eexists. split.
+ mlbu0 (ltac:(oF' 0x8b0cc%Z)) (ltac:(oD' 0x8b0cc%Z)) (ae + i)%Z.
stepiv (ltac:(oF' 0x8b0d0%Z)) (ltac:(oD' 0x8b0d0%Z)) (Z_to_bv 64 (e - ae - (i + 1))) ltac:(wval).
stepn (ltac:(oF' 0x8b0d4%Z)) (ltac:(oD' 0x8b0d4%Z)).
stepiv (ltac:(oF' 0x8b0d8%Z)) (ltac:(oD' 0x8b0d8%Z)) (Z_to_bv 64 (ae + (i + 1))) ltac:(wval).
stepb_ft (ltac:(oF' 0x8b0dc%Z)) (ltac:(oD' 0x8b0dc%Z)) ltac:(cond).
apply mst_refl.
+ unfold l3_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8b0cc : word) M1 rom) (fun rg => l3_inv rg (i + 1) /\ kcs2 regs rg)).
+ eexists. split.
* mlbu0 (ltac:(oF' 0x8b0cc%Z)) (ltac:(oD' 0x8b0cc%Z)) (ae + i)%Z.
stepiv (ltac:(oF' 0x8b0d0%Z)) (ltac:(oD' 0x8b0d0%Z)) (Z_to_bv 64 (e - ae - (i + 1))) ltac:(wval).
stepn (ltac:(oF' 0x8b0d4%Z)) (ltac:(oD' 0x8b0d4%Z)).
stepiv (ltac:(oF' 0x8b0d8%Z)) (ltac:(oD' 0x8b0d8%Z)) (Z_to_bv 64 (ae + (i + 1))) ltac:(wval).
stepb_tk (ltac:(oF' 0x8b0dc%Z)) (ltac:(oD' 0x8b0dc%Z)) ltac:(cond).
apply mst_refl.
* unfold l3_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (i + 1)%Z I1 ltac:(lia) ltac:(lia) Hbae) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]].
Qed.
#[using="beg b e Hb_def Hs_def Hs Hret"] Lemma epi_run : ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "R0&Ay5'R<yR0%211%5241&Ir1%211';'9'C&Q3&NvQHr3(R:+a\W0(8%33@21/01@&BvQL&R;&QAvR8+8%3221%52I1&@u8vR3%3221%<3;51vR7%F5ED?21%G5FM532%J3I21':&M+:%I3Q81G%32Q31+1%E2Q91%73Q931+2%O3Q>1M%92Q91vR9%<3Q>21%Q33QB8Q1%=2Q=1%?3QA1F&L%12Q8Q@%Q>231%Q?271%Q@2=1%QA2F1qT>QG1%QD2QH1p0QF1pT<QJ1").
Proof.
intros regs (H11 & H2 & H1). pose proof b_range as Hb.
eexists. split.
- stepiv (ltac:(oF' 0x8b0e0%Z)) (ltac:(oD' 0x8b0e0%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; reflexivity).
stepld (ltac:(oF' 0x8b0e4%Z)) (ltac:(oD' 0x8b0e4%Z)) ra ltac:(maddr (s - 8)%Z; apply rdn_wbytes_hit8; unorm; lia).
stepiv (ltac:(oF' 0x8b0e8%Z)) (ltac:(oD' 0x8b0e8%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x8b0ec%Z)) (ltac:(oD' 0x8b0ec%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- post. all: try (symmetry; apply sp_s). all: solve_kcs2.
Qed.
Definition mid_post (rg : bvmap 5 word) : Prop :=
getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e
/\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
Section SE.
Local Abbreviation SEC_T_mid_run := (ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "QC&Ay5'R<yR0%211%5241&Er1%211';'9'C&Q3&NvQHr3(R:+a\U<(8%33@21/01@&BvQL&R;&QAvR8+8%3221%52I1&@u8vR3%3221%<3;51vR7%F5ED?21+a\V0%E3Q21C/01Q2%J5IQ0165%M3L51&J%11Q3&L%12MQ5%Q3231%Q4261qT>Q:1%Q72Q;1p0Q91pT<Q=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_mid_run) 0%nat 0%nat).
Lemma mid_run : ltac:(sec_stmt2 constr:(SEC_T_mid_run) 1%nat 0%nat).
Proof using beg n Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ regs.
intros (H11 & H14 & H15 & H12 & H10 & H2 & H1).
pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
destruct (Z.le_gt_cases ae ab) as [Hskip|Hgo].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x8b0ac%Z)) (ltac:(oD' 0x8b0ac%Z)) ltac:(cond).
apply mst_refl.
+ unfold mid_post. post.
- assert (Hq : exists q : nat, (ab + 8 * (0 + Z.of_nat q + 1) = ae)%Z).
{ destruct Hab as [Hab1 Hab2]. destruct Hae as [Hae1 Hae2].
pose proof (Z.div_mod ab 8 ltac:(lia)) as Dab. pose proof (Z.div_mod ae 8 ltac:(lia)) as Dae.
rewrite Hab2 in Dab. rewrite Hae2 in Dae.
exists (Z.to_nat (ae / 8 - ab / 8 - 1)). rewrite Z2Nat.id; lia. }
destruct Hq as (q & Hq).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8b0b0 : word) M1 rom) (fun rg => l2_inv rg 0 /\ kcs2 regs rg)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x8b0ac%Z)) (ltac:(oD' 0x8b0ac%Z)) ltac:(cond).
apply mst_refl.
* unfold l2_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (loop2_run q r1 0 I1 ltac:(lia) Hq) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN|]. split; [|eapply kcs2_trans; eassumption].
destruct P2 as (Q15 & Q11 & Q14 & Q12 & Q10 & Q2 & Q1). unfold mid_post. repeat split; assumption.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_tail_run := (ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "QC&Ay5'R<yR0%211%5241&Jr1%211';'9'C&Q3&NvQHr3(R:+a\V0(8%33@21/01@&BvQL&R;&QAvR8+8%3221%52I1&@u8vR3%3221%<3;51vR7%F5ED?21+a\W0%E3Q21C/01Q2%J5IQ0165%M3L51&I%11Q3&L%12MQ5%Q3231%Q4261qT>Q:1%Q72Q;1p0Q91pT<Q=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_tail_run) 0%nat 0%nat).
Lemma tail_run : ltac:(sec_stmt2 constr:(SEC_T_tail_run) 1%nat 0%nat).
Proof using beg n ab Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ regs.
intros (H11 & H14 & H12 & H10 & H2 & H1).
pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
destruct (Z.lt_ge_cases ae b) as [Hlow|Hhigh].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x8b0c0%Z)) (ltac:(oD' 0x8b0c0%Z)) ltac:(cond).
apply mst_refl.
+ unfold l3_post. post.
- destruct (Z.le_gt_cases e ae) as [Hskip|Hgo].
+ eexists. split.
* stepb_ft (ltac:(oF' 0x8b0c0%Z)) (ltac:(oD' 0x8b0c0%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x8b0c4%Z)) (ltac:(oD' 0x8b0c4%Z)) ltac:(cond).
apply mst_refl.
* unfold l3_post. post.
+ assert (Hq : exists q : nat, (ae + 0 + Z.of_nat q + 1 = e)%Z) by (exists (Z.to_nat (e - ae - 1)); rewrite Z2Nat.id; lia).
destruct Hq as (q & Hq).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8b0cc : word) M1 rom) (fun rg => l3_inv rg 0 /\ kcs2 regs rg)).
* eexists. split.
-- stepb_ft (ltac:(oF' 0x8b0c0%Z)) (ltac:(oD' 0x8b0c0%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x8b0c4%Z)) (ltac:(oD' 0x8b0c4%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x8b0c8%Z)) (ltac:(oD' 0x8b0c8%Z)) (Z_to_bv 64 (e - ae - 0)) ltac:(wval).
apply mst_refl.
-- unfold l3_inv. post.
* cbv beta. intros r1 (I1 & K1).
destruct (loop3_run q r1 0 I1 ltac:(lia) Hq Hhigh) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_mem_is_zero_run := (ltac2:(TCodec.tc2 tcn__Ja0MemIsZero "R@&Ay5'R<yR0%211%5241':&Mr1(R:+:(8%33;21%6251vQF%93;21r2+;%93A17%<231&R;vQM%22C1%A3C41r3+2%A3I1?%D231vR9%G3I21r4+1%G3O1E%J231vR3%M3O21';'9'C&Q3&NvQHr6+a\RD%Q33Q91Q1/01Q9vQLvR7%8576321&B&QAvR8+8%3221%Q22QC1&@u8%221G%93<41%C5BQCI1<%F3E<1%Q92QJN%QH3QJQA1%QH2QGQ5%QJ3QL1Q4%QJ2QIQ1%QL3QN1Q0&Q2%12JQL%Q0231%Q1261%Q2291%Q32<1qT>R41%Q62R51p0Q81p0Q?1p0QF1p0QO1pT<R:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_mem_is_zero_run) 0%nat 0%nat).
Theorem mem_is_zero_run : ltac:(sec_stmt2 constr:(SEC_T_mem_is_zero_run) 1%nat 0%nat).
Proof using b e ab ae Hb_def Hs_def He_def Hab_def Hae_def Hn He Hs Hdisj Hok Hret HZ regs.
intros H10 H11 H2 H1.
pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
assert (STEP : forall (pcA pcB : word) (PA PB : bvmap 5 word -> Prop),
(exists r1, msteps ASEGS (mkst regs (0x8b054 : word) mem0 rom) (mkst r1 pcA M1 rom) /\ (PA r1 /\ kcs2 regs r1)) ->
(forall r1, PA r1 -> exists r2, msteps ASEGS (mkst r1 pcA M1 rom) (mkst r2 pcB M1 rom) /\ PB r2 /\ kcs2 r1 r2) ->
exists r2, msteps ASEGS (mkst regs (0x8b054 : word) mem0 rom) (mkst r2 pcB M1 rom) /\ (PB r2 /\ kcs2 regs r2)).
{ intros pcA pcB PA PB HA HB.
eapply (runs_trans ASEGS _ (fun rg => mkst rg pcA M1 rom) (fun rg => PA rg /\ kcs2 regs rg)); [exact HA|].
cbv beta. intros r1 (P1 & K1). destruct (HB r1 P1) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]]. }
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x8b054 : word) mem0 rom) (mkst r1 (0x8b084 : word) M1 rom) /\ (pro_post r1 /\ kcs2 regs r1)).
{ destruct (pro_run regs H10 H11 H2 H1) as (r1 & RUN & P & K). exists r1. split; [exact RUN | split; assumption]. }
assert (S2 : exists r1, msteps ASEGS (mkst regs (0x8b054 : word) mem0 rom) (mkst r1 (0x8b0ac : word) M1 rom) /\ (l1_post r1 /\ kcs2 regs r1)).
{ apply (STEP (0x8b084 : word) (0x8b0ac : word) pro_post l1_post S1).
intros r1 (P10 & P11 & P12 & P13 & P14 & P15 & P2 & P1). rewrite beg_b in P10.
destruct (Z.le_gt_cases ab b) as [Hal|Hunal].
-
eexists. split.
+ stepb_tk (ltac:(oF' 0x8b084%Z)) (ltac:(oD' 0x8b084%Z)) ltac:(cond).
apply mst_refl.
+ unfold l1_post. post.
-
assert (Hq : exists q : nat, (0 + Z.of_nat q + 1 = Z.min ab e - b)%Z) by (exists (Z.to_nat (Z.min ab e - b - 1)); rewrite Z2Nat.id; lia).
destruct Hq as (q & Hq).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8b094 : word) M1 rom) (fun rg => l1_inv rg 0 /\ kcs2 r1 rg)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x8b084%Z)) (ltac:(oD' 0x8b084%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x8b088%Z)) (ltac:(oD' 0x8b088%Z)) ltac:(cond).
stepn (ltac:(oF' 0x8b08c%Z)) (ltac:(oD' 0x8b08c%Z)).
stepiv (ltac:(oF' 0x8b090%Z)) (ltac:(oD' 0x8b090%Z)) (Z_to_bv 64 (b + 0 + 1)) ltac:(wval).
apply mst_refl.
* unfold l1_inv. post.
+ cbv beta. intros r2 (I2 & K2).
destruct (loop1_run q r2 0 I2 ltac:(lia) Hq) as (r3 & RUN & P3 & K3).
exists r3. split; [exact RUN | split; [exact P3 | eapply kcs2_trans; eassumption]]. }
pose proof (STEP _ _ _ _ S2 mid_run) as S3.
pose proof (STEP _ _ _ _ S3 tail_run) as S4.
destruct S4 as (r4 & RUN4 & P4 & K4).
destruct (epi_run r4 P4) as (r5 & RUN5 & Q10 & Q2 & Q1 & K5).
exists r5. split; [eapply msteps_trans; [exact RUN4 | exact RUN5]|].
repeat split; try assumption.
apply kcs2_to_keeps_cs; [eapply kcs2_trans; eassumption | rewrite Q2, H2; reflexivity].
Qed.
End SE.
End Walk. End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
