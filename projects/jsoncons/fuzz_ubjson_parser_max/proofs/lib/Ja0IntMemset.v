(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0IntMemset () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1list"; "1nat"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2iff"; "3repeat"; "4Z"; "0L"; "5bvmap"; "6wbytes"; "7msteps"]; ["8at_"; "9c64"; "9cbyte"; "9cfill"; "9ms_agree"; ":getr"; ":mkst"; ":v_add"; ":v_or"; ":v_slli"; ";loaded_segments"; "<add"; "<land"; "<le"; "<lor"; "<lt"]; ["<modulo"; "<mul"; "<of_nat"; "<pow"; "<to_nat"; "0a"; "0b"; "0cv"; "0d"; "0fx"; "0k"; "0mem0"; "0n"; "0q"; "0regs"; "0regs'"]; ["0ret"; "0rom"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Lemma lor_lt_pow2 : ltac2:(TCodec.tc2 tcn__Ja0IntMemset "N';'6&Mzr3%3221&O&Q3+2r1%3221%5271%;271r2%7261%92;1%?2;1&Nr5r4%3221%C2B1%?2>B%A231%G231p091p0>1pRFK1pR>L1pR<M1").
Proof.
intros a b k Ha Hb.
assert (Hk : (0 <= k)%Z \/ (k < 0)%Z) by lia. destruct Hk as [Hk|Hk]; [|rewrite Z.pow_neg_r in Ha by lia; lia].
split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
Lemma land15_lor : ltac2:(TCodec.tc2 tcn__Ja0IntMemset "L';&Mzr2%3221&9'7&L&Nr4r3%3221+?%6221%83>1<'6&Q0+@%2291%=3C1A%42:3%?3E1C%7231%B291p0D1p0E1pR>J1pR<K1").
Proof.
intros a b Ha Hb. rewrite Z.land_lor_distr_l.
change 15%Z with (Z.ones 4). rewrite !Z.land_ones by lia. change (2 ^ 4)%Z with 16%Z.
rewrite Z.lor_eq_0_iff. tauto.
Qed.
Lemma lor_disjoint_shift : ltac2:(TCodec.tc2 tcn__Ja0IntMemset "N';&Mzr3%3221'6&O&Q3+2r5%3221%5281%7281'7&N&Q1r6%:291%3291r4%6221&K%1243%:3G31p0<1p0E1p0F1pR>K1pR<L1pRFM1").
Proof.
intros k a b Hk Ha Hb.
assert (Hl : Z.land (a * 2 ^ k) b = 0%Z).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k).
- rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
- rewrite (Z_testbit_high k b) by lia. apply andb_false_r. }
rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma v_or_slli : ltac2:(TCodec.tc2 tcn__Ja0IntMemset "QA'QDyR0%211';&Mzr1%3221'6&QEr3%22:1%8271&O&Q3+2r2%3221%5271%;271&K&Q1r4%>2F1%:29>%4221%6213+R0%>2=1%@231'7&H&Ir5%221<%4212&QC%L2Q44%H2G@+1%D221%D241%62Q91%=3Q981p0?1p0J1p0Q71pRFQ<1pS>Q>1").
Proof.
intros x k Hk Hx Hw. unfold v_or, v_slli. f_equal.
rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by nia.
rewrite lor_disjoint_shift by lia. lia.
Qed.
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
rwH; unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Section Walk.
Variable mem0 : word -> option byte.
Variables d cv ret : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 d (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ret.
#[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
#[local] Ltac msb F D oo :=
chain_step; [reflexivity
| eapply (cf_sb ASEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| lia | lia]
| step_simpl].
#[local] Ltac msd F D oo :=
chain_step; [reflexivity
| eapply (cf_sd ASEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| apply wleb8_c64
| lia | lia]
| step_simpl].
#[local] Ltac mret := stepret (ltac:(oF' 0x8ab64%Z)) (ltac:(oD' 0x8ab64%Z)) ret ltac:(rwH; reflexivity).
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.
#[local] Ltac ms_cov_eq :=
intros i Hi; rewrite !ms_cov_cons;
match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
apply eq_true_iff_eq; rewrite ?orb_true_iff, !ms_inb_true; lia.
Lemma bloop_run : ltac2:(TCodec.tc2 tcn__Ja0IntMemset "SA'2&=y5'QDyR0%211%5241'1'4';%2211%411'7&Er3(QB+:(5%33@21%6251&@vQ8z%3221%<3C51r4+;%<3I1:%?231vQ7%B3I21r5+<%B3O1@%E231vQ<%@2?1%I3Q031r6+=%I3Q61G%L231%F2EA%O3Q621r7+1%O3Q<1M%Q2231vQ@%Q53Q<21&M%12M=&K&Q2r:%211%42<1%521<%Q>3QA1G'8'6'?&J&FvQ9r;+aZi0%QD3QO1QB/01QO&CvQ;&B%11Q;%453QDQ61CvQA%<5;:721r1+aZi<%QO3R:1QM/01R:(0(3r9r<%O11%Q121Q8%54R=R=41%73R=1Q1%C5BR3QE@1%J5I=:1?%M3L?1%R>2?R9%R@3RG1R5%R@2AQ?%RB3RI1Q>&D%12OD%Q5231%Q6261%Q7291qS0RN1%Q:2RO1p0Q<1p0QD1p0QG1p0QN1p0R51p0R=1p0RD1pR<S41pJS31pRNS91pRLS@1").
Proof.
induction q as [|q IH]; intros regs L a H10 H11 H12 H13 H1 Ha Hq; pose proof (u64_range d) as Hd.
- eexists. split.
+ msb (ltac:(oF' 0x8ab20%Z)) (ltac:(oD' 0x8ab20%Z)) a.
stepiv (ltac:(oF' 0x8ab24%Z)) (ltac:(oD' 0x8ab24%Z)) (at_ d (a + 1)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_ft (ltac:(oF' 0x8ab28%Z)) (ltac:(oD' 0x8ab28%Z)) ltac:(cond).
replace (CF ((a, Z.of_nat 0 + 1)%Z :: L)) with (CF ((a, 1)%Z :: L)) by (apply cfill_ext; ms_cov_eq).
apply mst_refl.
+ post.
- eapply (runs_trans ASEGS _
(fun rg => mkst rg (0x8ab20 : word) (CF ((a, 1)%Z :: L)) rom)
(fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = cv /\ getr rg 12 = at_ d n /\ getr rg 13 = at_ d (a + 1)
/\ getr rg 1 = ret /\ ms_agree regs rg)).
+ cbv beta. eexists. split.
* msb (ltac:(oF' 0x8ab20%Z)) (ltac:(oD' 0x8ab20%Z)) a.
stepiv (ltac:(oF' 0x8ab24%Z)) (ltac:(oD' 0x8ab24%Z)) (at_ d (a + 1)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_tk (ltac:(oF' 0x8ab28%Z)) (ltac:(oD' 0x8ab28%Z)) ltac:(cond).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R10 & R11 & R12 & R13 & R1 & AG).
destruct (IH r1 ((a, 1)%Z :: L) (a + 1)%Z R10 R11 R12 R13 R1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
exists r2. split.
* replace (CF ((a, Z.of_nat (S q) + 1)%Z :: L))
with (CF ((a + 1, Z.of_nat q + 1)%Z :: (a, 1)%Z :: L)) by (apply cfill_ext; ms_cov_eq).
exact RUN.
* repeat split; try assumption. eapply ms_agree_trans; eassumption.
Qed.
Lemma wloop_run : ltac2:(TCodec.tc2 tcn__Ja0IntMemset "SG'2&=y5'QDyR0%211%5241'1'4';%2211%411'7&Er3(QB+:(5%33@21%6251&@vQ8z%3221%<3C51r4+;%<3I1:%?231&AvQ7%211%D3K41r5+<%D3Q11B%G231vQ<%B2A1%K3Q231r6+=%K3Q81I%N231%H2GC%Q13Q821r7+1%Q13Q>1O%Q4231vQ@%Q73Q>21&M%12O=&K&Q1+@&Q2r:%211%621=%6251%82@1%QC3QF1J'8'6'?&J&FvQ9r;+aZjD%QI3R41QG/01R4&CvQ;&B%11Q?%453QIQ91DvQA%<5;:721r1+aZk4%R43R?1R2/01R?(0(3r9r<%Q011%Q421Q;%Q42Q31%64RCRC51%83RC1Q3%D5CR9QIA1%K5J>;1@%N3M@1%RD2@R?%RF3RM1R;%RF2BQC%RH3RO1QB&D%12Q0E%Q6231%Q7261%Q8291qS0S41%Q;2S51p0Q=1p0QH1p0QK1p0R21p0R91p0RA1p0RJ1pR<S:1pJS91pRNS?1pRLSF1").
Proof.
induction q as [|q IH]; intros regs L a H10 H11 H12 H13 H1 Ha Hq; pose proof (u64_range d) as Hd.
- eexists. split.
+ msd (ltac:(oF' 0x8ab54%Z)) (ltac:(oD' 0x8ab54%Z)) a.
msd (ltac:(oF' 0x8ab58%Z)) (ltac:(oD' 0x8ab58%Z)) (a + 8)%Z.
stepiv (ltac:(oF' 0x8ab5c%Z)) (ltac:(oD' 0x8ab5c%Z)) (at_ d (a + 16)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_ft (ltac:(oF' 0x8ab60%Z)) (ltac:(oD' 0x8ab60%Z)) ltac:(cond).
replace (CF ((a, 16 * (Z.of_nat 0 + 1))%Z :: L)) with (CF ((a + 8, 8)%Z :: (a, 8)%Z :: L)) by (apply cfill_ext; ms_cov_eq).
apply mst_refl.
+ post.
- eapply (runs_trans ASEGS _
(fun rg => mkst rg (0x8ab54 : word) (CF ((a + 8, 8)%Z :: (a, 8)%Z :: L)) rom)
(fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = c64 cv /\ getr rg 12 = at_ d n /\ getr rg 13 = at_ d (a + 16)
/\ getr rg 1 = ret /\ ms_agree regs rg)).
+ cbv beta. eexists. split.
* msd (ltac:(oF' 0x8ab54%Z)) (ltac:(oD' 0x8ab54%Z)) a.
msd (ltac:(oF' 0x8ab58%Z)) (ltac:(oD' 0x8ab58%Z)) (a + 8)%Z.
stepiv (ltac:(oF' 0x8ab5c%Z)) (ltac:(oD' 0x8ab5c%Z)) (at_ d (a + 16)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_tk (ltac:(oF' 0x8ab60%Z)) (ltac:(oD' 0x8ab60%Z)) ltac:(cond).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R10 & R11 & R12 & R13 & R1 & AG).
destruct (IH r1 ((a + 8, 8)%Z :: (a, 8)%Z :: L) (a + 16)%Z R10 R11 R12 R13 R1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
exists r2. split.
* replace (CF ((a, 16 * (Z.of_nat (S q) + 1))%Z :: L))
with (CF ((a + 16, 16 * (Z.of_nat q + 1))%Z :: (a + 8, 8)%Z :: (a, 8)%Z :: L)) by (apply cfill_ext; ms_cov_eq).
exact RUN.
* repeat split; try assumption. eapply ms_agree_trans; eassumption.
Qed.
Lemma v_add_dn : ltac2:(TCodec.tc2 tcn__Ja0IntMemset "='7'QDyR0%211&GvQ8&QCvQ<%2261%5241&@%1264%<3931").
Proof.
pose proof (u64_range d). unfold v_add, at_. f_equal. rewrite !u_Z2bv by lia. lia.
Qed.
#[local] Ltac cond15 H :=
rwH; unfold v_andi, v_or, c_eq, bv_eqb; change (bv_wrap 64 15) with 15%Z; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq]; exact H.
Section SE.
Local Abbreviation SEC_T_int_memset_run := (ltac2:(TCodec.tc2 tcn__Ja0IntMemset "R>&=y5'QDyR0%211%5241'7&Er1(QB+:(5%33;21%6251vQ8%93;21r2+;%93A17%<231vQ7%?3A21r3+<%?3G1=%B231&QCvQ<%22I1%G3I41r4+1%G3O1E%J231vQ@%M3O21&O&QE%12Q3B+X0%4221'8'6'?&J&FvQ9r7+aZh8%Q83Q>1Q6/01Q>vQ;vQA%8576321&>&:y8%QG11&B%11Q7&Q4%11Q2%73531%93<QA1%C5BQHN1<%F3E<1&D%12DQK%J2QE1%K241qS0R11%N2R21p0Q01p0Q61p0Q=1p0QF1p0QM1pRNR81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_int_memset_run) 0%nat 0%nat).
Theorem int_memset_run : ltac:(sec_stmt2 constr:(SEC_T_int_memset_run) 1%nat 0%nat).
Proof.
intros H10 H11 H12 H1 Hcv.
pose proof (u64_range d) as Hd. pose proof (u64_range cv) as Hcvr.
replace (mkst regs (0x8ab08 : word) mem0 rom) with (mkst regs (0x8ab08 : word) (CF []) rom)
by (rewrite (cfill_nil mem0 d n (cbyte cv)); reflexivity).
assert (Hlor : (0 <= Z.lor n (bv_unsigned d) < 2 ^ 64)%Z) by (apply lor_lt_pow2; lia).
assert (Hland : (0 <= Z.land (Z.lor n (bv_unsigned d)) 15 <= 15)%Z).
{ split; [apply Z.land_nonneg; right; lia|].
change 15%Z with (Z.ones 4) at 1. rewrite Z.land_ones by lia.
pose proof (Z.mod_pos_bound (Z.lor n (bv_unsigned d)) (2 ^ 4) ltac:(lia)). lia. }
destruct (Z.eq_dec (Z.land (Z.lor n (bv_unsigned d)) 15) 0) as [Hal|Hnal].
-
pose proof (proj1 (land15_lor n (bv_unsigned d) Hn ltac:(lia)) Hal) as [Hn16 Hd16].
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
+ eexists. split.
* stepi (ltac:(oF' 0x8ab08%Z)) (ltac:(oD' 0x8ab08%Z)).
stepi (ltac:(oF' 0x8ab0c%Z)) (ltac:(oD' 0x8ab0c%Z)).
stepb_tk (ltac:(oF' 0x8ab10%Z)) (ltac:(oD' 0x8ab10%Z)) ltac:(cond15 Hal).
stepb_tk (ltac:(oF' 0x8ab30%Z)) (ltac:(oD' 0x8ab30%Z)) ltac:(cond).
mret.
rewrite (cfill_full mem0 d n (cbyte cv) Hn Hnw []) by (intros i Hi; lia).
apply mst_refl.
* post.
+ assert (Hq : exists q : nat, (16 * (Z.of_nat q + 1) = n)%Z).
{ exists (Z.to_nat (n / 16 - 1)). pose proof (Z.div_mod n 16 ltac:(lia)). rewrite Z2Nat.id; lia. }
destruct Hq as (q & Hq).
assert (Hc64 : v_or (v_slli (v_or (v_slli (v_or (v_slli cv 8) cv) 16) (v_or (v_slli cv 8) cv)) 32)
(v_or (v_slli (v_or (v_slli cv 8) cv) 16) (v_or (v_slli cv 8) cv)) = c64 cv).
{ rewrite (v_or_slli cv 8) by lia.
assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned cv * (2 ^ 8 + 1))) = (bv_unsigned cv * 257)%Z) by (rewrite u_Z2bv; lia).
rewrite (v_or_slli _ 16); [| lia | rewrite U1; lia | rewrite U1; lia]. rewrite U1.
assert (U2 : bv_unsigned (Z_to_bv 64 (bv_unsigned cv * 257 * (2 ^ 16 + 1))) = (bv_unsigned cv * 16843009)%Z) by (rewrite u_Z2bv; lia).
rewrite (v_or_slli _ 32); [| lia | rewrite U2; lia | rewrite U2; lia]. rewrite U2.
unfold c64, cbz. f_equal. rewrite Z.mod_small by lia. lia. }
eapply (runs_trans ASEGS _
(fun rg => mkst rg (0x8ab54 : word) (CF []) rom)
(fun rg => getr rg 10 = d /\ getr rg 11 = c64 cv /\ getr rg 12 = at_ d n /\ getr rg 13 = d
/\ getr rg 1 = ret /\ ms_agree regs rg)).
* cbv beta. eexists. split.
-- stepi (ltac:(oF' 0x8ab08%Z)) (ltac:(oD' 0x8ab08%Z)).
stepi (ltac:(oF' 0x8ab0c%Z)) (ltac:(oD' 0x8ab0c%Z)).
stepb_tk (ltac:(oF' 0x8ab10%Z)) (ltac:(oD' 0x8ab10%Z)) ltac:(cond15 Hal).
stepb_ft (ltac:(oF' 0x8ab30%Z)) (ltac:(oD' 0x8ab30%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x8ab34%Z)) (ltac:(oD' 0x8ab34%Z)) (at_ d n) ltac:(gres; rwH; apply v_add_dn).
stepi (ltac:(oF' 0x8ab38%Z)) (ltac:(oD' 0x8ab38%Z)). stepi (ltac:(oF' 0x8ab3c%Z)) (ltac:(oD' 0x8ab3c%Z)).
stepi (ltac:(oF' 0x8ab40%Z)) (ltac:(oD' 0x8ab40%Z)). stepi (ltac:(oF' 0x8ab44%Z)) (ltac:(oD' 0x8ab44%Z)).
stepi (ltac:(oF' 0x8ab48%Z)) (ltac:(oD' 0x8ab48%Z)).
stepi (ltac:(oF' 0x8ab4c%Z)) (ltac:(oD' 0x8ab4c%Z)).
stepiv (ltac:(oF' 0x8ab50%Z)) (ltac:(oD' 0x8ab50%Z)) d ltac:(gres; rwH; imm_norm; apply v_addi_0).
apply mst_refl.
-- repeat split; gres; rwH; rewrite ?Hc64; try reflexivity; solve_ms_agree.
* cbv beta. intros r1 (R10 & R11 & R12 & R13 & R1 & AG).
rewrite <- (at_0 d) in R10, R13.
destruct (wloop_run q r1 [] 0 R10 R11 R12 R13 R1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
exists r2. split; [|split; [rewrite at_0 in P10; exact P10 | eapply ms_agree_trans; eassumption]].
eapply msteps_trans; [exact RUN|].
rewrite (cfill_full mem0 d n (cbyte cv) Hn Hnw [(0, 16 * (Z.of_nat q + 1))%Z])
by (intros i Hi; rewrite ms_cov_cons; apply orb_true_iff; left; apply ms_inb_true; lia).
stepret (ltac:(oF' 0x8ab64%Z)) (ltac:(oD' 0x8ab64%Z)) ret ltac:(rewrite P1; reflexivity).
apply mst_refl.
-
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
+ eexists. split.
* stepi (ltac:(oF' 0x8ab08%Z)) (ltac:(oD' 0x8ab08%Z)).
stepi (ltac:(oF' 0x8ab0c%Z)) (ltac:(oD' 0x8ab0c%Z)).
stepb_ft (ltac:(oF' 0x8ab10%Z)) (ltac:(oD' 0x8ab10%Z)) ltac:(cond15 Hnal).
stepb_tk (ltac:(oF' 0x8ab14%Z)) (ltac:(oD' 0x8ab14%Z)) ltac:(cond).
mret.
rewrite (cfill_full mem0 d n (cbyte cv) Hn Hnw []) by (intros i Hi; lia).
apply mst_refl.
* post.
+ assert (Hq : exists q : nat, (Z.of_nat q + 1 = n)%Z) by (exists (Z.to_nat (n - 1)); rewrite Z2Nat.id; lia).
destruct Hq as (q & Hq).
eapply (runs_trans ASEGS _
(fun rg => mkst rg (0x8ab20 : word) (CF []) rom)
(fun rg => getr rg 10 = d /\ getr rg 11 = cv /\ getr rg 12 = at_ d n /\ getr rg 13 = d
/\ getr rg 1 = ret /\ ms_agree regs rg)).
* cbv beta. eexists. split.
-- stepi (ltac:(oF' 0x8ab08%Z)) (ltac:(oD' 0x8ab08%Z)).
stepi (ltac:(oF' 0x8ab0c%Z)) (ltac:(oD' 0x8ab0c%Z)).
stepb_ft (ltac:(oF' 0x8ab10%Z)) (ltac:(oD' 0x8ab10%Z)) ltac:(cond15 Hnal).
stepb_ft (ltac:(oF' 0x8ab14%Z)) (ltac:(oD' 0x8ab14%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x8ab18%Z)) (ltac:(oD' 0x8ab18%Z)) (at_ d n) ltac:(gres; rwH; apply v_add_dn).
stepiv (ltac:(oF' 0x8ab1c%Z)) (ltac:(oD' 0x8ab1c%Z)) d ltac:(gres; rwH; imm_norm; apply v_addi_0).
apply mst_refl.
-- post.
* cbv beta. intros r1 (R10 & R11 & R12 & R13 & R1 & AG).
rewrite <- (at_0 d) in R10, R13.
destruct (bloop_run q r1 [] 0 R10 R11 R12 R13 R1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
exists r2. split; [|split; [rewrite at_0 in P10; exact P10 | eapply ms_agree_trans; eassumption]].
eapply msteps_trans; [exact RUN|].
rewrite (cfill_full mem0 d n (cbyte cv) Hn Hnw [(0, Z.of_nat q + 1)%Z])
by (intros i Hi; rewrite ms_cov_cons; apply orb_true_iff; left; apply ms_inb_true; lia).
stepj (ltac:(oF' 0x8ab2c%Z)) (ltac:(oD' 0x8ab2c%Z)).
stepret (ltac:(oF' 0x8ab64%Z)) (ltac:(oD' 0x8ab64%Z)) ret ltac:(rewrite P1; reflexivity).
apply mst_refl.
Qed.
End SE.
End Walk.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
