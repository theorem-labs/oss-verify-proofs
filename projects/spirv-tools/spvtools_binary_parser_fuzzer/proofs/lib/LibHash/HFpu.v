(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool SpecFloat.
From Flocq.Core Require Import Digits Zaux.
From Flocq.IEEE754 Require Import BinarySingleNaN.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec FPSteps.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition F32 := fmt_single.
Definition zdig (n : Z) : Z := Zdigits radix2 n.
Definition fmant (n : Z) : Z := n * 2 ^ (24 - zdig n).
Definition fexpo (n : Z) : Z := zdig n - 24.

Definition ieee (n : Z) : Z := (fexpo n + 150) * 2 ^ 23 + (fmant n - 2 ^ 23).
Definition one32 : Z := 0x3f800000.

Lemma zdig_bounds : forall n, 1 <= n < 2 ^ 24 ->
  1 <= zdig n <= 24 /\ 2 ^ (zdig n - 1) <= n < 2 ^ (zdig n).
Proof.
  intros n Hn. unfold zdig.
  pose proof (Zdigits_correct radix2 n) as Hc. rewrite Z.abs_eq in Hc by lia.
  pose proof (Zdigits_gt_0 radix2 n ltac:(lia)) as Hg.
  pose proof (Zdigits_le_Zpower radix2 24 n ltac:(rewrite Z.abs_eq by lia; exact (proj2 Hn))) as Hle.
  change (Zpower radix2 (Zdigits radix2 n - 1)) with (2 ^ (Zdigits radix2 n - 1)) in Hc.
  change (Zpower radix2 (Zdigits radix2 n)) with (2 ^ (Zdigits radix2 n)) in Hc.
  lia.
Qed.

Lemma fmant_bounds : forall n, 1 <= n < 2 ^ 24 -> 2 ^ 23 <= fmant n < 2 ^ 24.
Proof.
  intros n Hn. destruct (zdig_bounds n Hn) as [Hd [Hlo Hhi]]. unfold fmant.
  set (d := zdig n) in *.
  assert (H1 : 2 ^ 23 = 2 ^ (d - 1) * 2 ^ (24 - d)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H2 : 2 ^ 24 = 2 ^ d * 2 ^ (24 - d)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (0 < 2 ^ (24 - d)) by (apply Z.pow_pos_nonneg; lia).
  rewrite H1, H2. split.
  - apply Z.mul_le_mono_nonneg_r; lia.
  - apply Z.mul_lt_mono_pos_r; lia.
Qed.

Lemma fexpo_bounds : forall n, 1 <= n < 2 ^ 24 -> -23 <= fexpo n <= 0.
Proof. intros n Hn. destruct (zdig_bounds n Hn) as [Hd _]. unfold fexpo. lia. Qed.

Lemma Psize_digits : forall p, Pos.size p = digits2_pos p.
Proof. induction p; cbn; try rewrite IHp; reflexivity. Qed.

Lemma Zdigits2_pos_val : forall p d, 2 ^ (d - 1) <= Z.pos p < 2 ^ d -> Z.pos (digits2_pos p) = d.
Proof.
  intros p d H. rewrite Zpos_digits2_pos. apply Zdigits_unique. rewrite Z.abs_eq by lia.
  assert (Hd : 1 <= d).
  { destruct (Z.le_gt_cases 1 d); [assumption|]. exfalso.
    assert (2 ^ d <= 2 ^ 0) by (destruct (Z.eq_dec d 0) as [->|]; [lia| rewrite (Z.pow_neg_r 2 d) by lia; cbn; lia]).
    cbn in *. lia. }
  change (Zpower radix2 (d - 1)) with (2 ^ (d - 1)). change (Zpower radix2 d) with (2 ^ d). exact H.
Qed.

Lemma Zdigits2_val : forall m d, 1 <= d -> 2 ^ (d - 1) <= m < 2 ^ d -> Zdigits2 m = d.
Proof.
  intros m d Hd H. assert (0 < 2 ^ (d - 1)) by (apply Z.pow_pos_nonneg; lia).
  destruct m as [|p|p]; [exfalso; lia | apply Zdigits2_pos_val; exact H | ].
  exfalso. pose proof (Pos2Z.neg_is_neg p). lia.
Qed.

Lemma digits24 : forall m, 2 ^ 23 <= Z.pos m < 2 ^ 24 -> Z.pos (digits2_pos m) = 24.
Proof. intros m Hm. apply Zdigits2_pos_val. exact Hm. Qed.
Lemma Zdigits24 : forall m, 2 ^ 23 <= m < 2 ^ 24 -> Zdigits2 m = 24.
Proof. intros m Hm. apply Zdigits2_val; [lia | exact Hm]. Qed.
Lemma Zdigits25 : forall m, 2 ^ 24 <= m < 2 ^ 25 -> Zdigits2 m = 25.
Proof. intros m Hm. apply Zdigits2_val; [lia | exact Hm]. Qed.
Lemma digits47 : forall m, 2 ^ 46 <= Z.pos m < 2 ^ 47 -> Z.pos (digits2_pos m) = 47.
Proof. intros m Hm. apply Zdigits2_pos_val. exact Hm. Qed.
Lemma Zdigits47 : forall m, 2 ^ 46 <= m < 2 ^ 47 -> Zdigits2 m = 47.
Proof. intros m Hm. apply Zdigits2_val; [lia | exact Hm]. Qed.

Lemma choice_mode_exact : forall md s m, BinarySingleNaN.choice_mode md s m loc_Exact = m.
Proof. intros md s m. destruct md; cbn; try reflexivity; destruct s; reflexivity. Qed.

Lemma round_canon : forall md m e,
  2 ^ 23 <= Z.pos m < 2 ^ 24 -> -149 <= e <= 104 ->
  round_aux F32 md false (Z.pos m) e loc_Exact = (S754_finite false m e, no_flags).
Proof.
  intros md m e Hm He. unfold round_aux, shr_fexp.
  rewrite (Zdigits24 (Z.pos m)) by lia.
  cbn [fp_prec fp_emax F32 fmt_single].
  replace (fexp 24 128 (24 + e) - e) with 0 by (unfold fexp, emin; lia).
  cbn [shr shr_record_of_loc loc_of_shr_record shr_m].
  rewrite choice_mode_exact.
  rewrite (Zdigits24 (Z.pos m)) by lia.
  replace (fexp 24 128 (24 + e) - e) with 0 by (unfold fexp, emin; lia).
  cbn [shr shr_m].
  destruct (Z.leb_spec e (128 - 24)); [|exfalso; lia].
  reflexivity.
Qed.

Lemma encode_canon : forall m e, 2 ^ 23 <= Z.pos m < 2 ^ 24 ->
  fp_encode F32 (S754_finite false m e) = (e + 150) * 2 ^ 23 + (Z.pos m - 2 ^ 23).
Proof.
  intros m e Hm. unfold fp_encode, F32, fmt_single, fp_mw, fp_ew, fp_emin. cbn [fp_prec fp_emax].
  rewrite Psize_digits, (digits24 m Hm). change (24 <? 24) with false. cbn iota.
  change (Z.log2 128 + 1) with 8.
  rewrite !Z.shiftl_mul_pow2 by lia. change (24 - 1) with 23. lia.
Qed.

Lemma testbit_high_false : forall x n, 0 <= x < 2 ^ n -> 0 <= n -> Z.testbit x n = false.
Proof.
  intros x n Hx Hn. destruct (Z.eq_dec x 0) as [->|Hnz]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma decode_canon : forall m e, 2 ^ 23 <= Z.pos m < 2 ^ 24 -> 1 <= e + 150 <= 254 ->
  fp_decode F32 ((e + 150) * 2 ^ 23 + (Z.pos m - 2 ^ 23)) = S754_finite false m e.
Proof.
  intros m e Hm He.
  set (E := (e + 150) * 2 ^ 23 + (Z.pos m - 2 ^ 23)).
  assert (HE : 0 <= E < 2 ^ 31) by (unfold E; lia).
  unfold fp_decode, fp_sign_bit, fp_exp_field, fp_man_field, F32, fmt_single, fp_mw, fp_ew, fp_emin. cbn [fp_prec fp_emax].
  change (Z.log2 128 + 1) with 8. change (24 - 1) with 23. change (23 + 8) with 31. change (3 - 128 - 24) with (-149).
  rewrite (testbit_high_false E 31) by lia.
  rewrite Z.shiftr_div_pow2, !Z.land_ones by lia.
  assert (Hx : E / 2 ^ 23 = e + 150) by (unfold E; rewrite Z.add_comm, Z.div_add by lia; rewrite Z.div_small by lia; lia).
  rewrite Hx. rewrite (Z.mod_small (e + 150)) by lia.
  assert (Hmf : E mod 2 ^ 23 = Z.pos m - 2 ^ 23).
  { unfold E. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite Hmf.
  destruct (Z.eqb_spec (e + 150) 0); [lia|].
  change (Z.ones 8) with 255. destruct (Z.eqb_spec (e + 150) 255); [lia|].
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (1 * 2 ^ 23 + (Z.pos m - 2 ^ 23)) with (Z.pos m) by lia. cbn [Z.add].
  f_equal. lia.
Qed.

Lemma of_int_val : forall md n, 1 <= n < 2 ^ 24 ->
  fp_of_int F32 md false 64 n = (ieee n, no_flags).
Proof.
  intros md n Hn.
  destruct (zdig_bounds n Hn) as [Hd [Hlo Hhi]].
  pose proof (fmant_bounds n Hn) as Hm. pose proof (fexpo_bounds n Hn) as He.
  unfold fp_of_int, int_wrap. rewrite Z.land_ones, Z.mod_small by lia. cbn [andb].
  unfold round_scaled. destruct n as [|p|p]; [lia| |lia].
  unfold round_exact. replace (fp_prec F32) with 24 by reflexivity. replace (fp_emax F32) with 128 by reflexivity.
  rewrite (Zdigits2_pos_val p (zdig (Z.pos p))) by (split; assumption).
  replace (fexp 24 128 (zdig (Z.pos p) + 0)) with (fexpo (Z.pos p)) by (unfold fexp, emin, fexpo; lia).
  unfold shl_align. rewrite Z.sub_0_r.
  destruct (fexpo (Z.pos p)) as [|q|q] eqn:Hf; [ | exfalso; lia | ].
  -
    assert (Hmp : fmant (Z.pos p) = Z.pos p).
    { unfold fmant. unfold fexpo in Hf. replace (24 - zdig (Z.pos p)) with 0 by lia. apply Z.mul_1_r. }
    rewrite (round_canon md p 0) by lia. unfold enc. cbn [fst snd].
    rewrite encode_canon by lia. unfold ieee. rewrite Hf, Hmp. reflexivity.
  - change (Pos.iter xO p q) with (shift_pos q p).
    assert (Hmp : Z.pos (shift_pos q p) = fmant (Z.pos p)).
    { rewrite shift_pos_correct, Z.pow_pos_fold. unfold fmant. unfold fexpo in Hf.
      replace (24 - zdig (Z.pos p)) with (Z.pos q) by lia. apply Z.mul_comm. }
    rewrite (round_canon md (shift_pos q p) (Z.neg q)) by lia. unfold enc. cbn [fst snd].
    rewrite encode_canon by lia. unfold ieee. rewrite Hf, Hmp. reflexivity.
Qed.

Definition mpos (n : Z) : positive := Z.to_pos (fmant n).
Lemma mpos_val : forall n, 1 <= n < 2 ^ 24 -> Z.pos (mpos n) = fmant n.
Proof. intros n Hn. unfold mpos. apply Z2Pos.id. pose proof (fmant_bounds n Hn). lia. Qed.

Lemma decode_ieee : forall n, 1 <= n < 2 ^ 24 ->
  fp_decode F32 (ieee n) = S754_finite false (mpos n) (fexpo n).
Proof.
  intros n Hn. pose proof (fmant_bounds n Hn) as Hm. pose proof (fexpo_bounds n Hn) as He.
  pose proof (mpos_val n Hn) as Hp.
  unfold ieee. rewrite <- Hp. apply decode_canon; lia.
Qed.

Lemma ieee_range : forall n, 1 <= n < 2 ^ 24 -> 0 < ieee n < 2 ^ 31.
Proof. intros n Hn. pose proof (fmant_bounds n Hn). pose proof (fexpo_bounds n Hn). unfold ieee. lia. Qed.

Lemma is_nan_ieee : forall n, 1 <= n < 2 ^ 24 -> fp_is_nan F32 (ieee n) = false.
Proof.
  intros n Hn. pose proof (fmant_bounds n Hn) as Hm. pose proof (fexpo_bounds n Hn) as He.
  unfold fp_is_nan, fp_exp_field, F32, fmt_single, fp_mw, fp_ew. cbn [fp_prec fp_emax].
  change (Z.log2 128 + 1) with 8. change (24 - 1) with 23.
  rewrite Z.shiftr_div_pow2, Z.land_ones by lia. change (Z.ones 8) with 255.
  replace (ieee n / 2 ^ 23) with (fexpo n + 150).
  2:{ unfold ieee. rewrite (Z.add_comm ((fexpo n + 150) * 2 ^ 23)), Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rewrite Z.mod_small by lia. destruct (Z.eqb_spec (fexpo n + 150) 255); [lia|]. reflexivity.
Qed.

Lemma zdig_mono : forall a b, 1 <= a < 2 ^ 24 -> 1 <= b < 2 ^ 24 -> zdig a < zdig b -> a < b.
Proof.
  intros a b Ha Hb Hlt.
  destruct (zdig_bounds a Ha) as [Hda [Hal Hah]]. destruct (zdig_bounds b Hb) as [Hdb [Hbl Hbh]].
  assert (2 ^ zdig a <= 2 ^ (zdig b - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma lt_val : forall a b, 1 <= a < 2 ^ 24 -> 1 <= b < 2 ^ 24 ->
  fp_lt F32 (ieee a) (ieee b) = ((a <? b), no_flags).
Proof.
  intros a b Ha Hb. unfold fp_lt, fp_compare.
  rewrite (is_nan_ieee a), (is_nan_ieee b), (decode_ieee a), (decode_ieee b) by assumption. cbn [orb SFcompare].
  f_equal.
  pose proof (fmant_bounds a Ha) as Hma. pose proof (fmant_bounds b Hb) as Hmb.
  pose proof (mpos_val a Ha) as Hpa. pose proof (mpos_val b Hb) as Hpb.
  destruct (zdig_bounds a Ha) as [Hda [Hal Hah]]. destruct (zdig_bounds b Hb) as [Hdb [Hbl Hbh]].
  unfold fexpo. destruct (Z.compare_spec (zdig a - 24) (zdig b - 24)) as [Heq|Hlt|Hgt].
  -
    change (Pos.compare_cont Eq (mpos a) (mpos b)) with (Z.compare (Z.pos (mpos a)) (Z.pos (mpos b))).
    rewrite Hpa, Hpb. unfold fmant. replace (zdig b) with (zdig a) by lia.
    assert (0 < 2 ^ (24 - zdig a)) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.ltb_spec a b).
    + rewrite (proj2 (Z.compare_lt_iff _ _)); [reflexivity|]. apply Z.mul_lt_mono_pos_r; lia.
    + destruct (Z.compare_spec (a * 2 ^ (24 - zdig a)) (b * 2 ^ (24 - zdig a))); try reflexivity.
      exfalso. assert (a * 2 ^ (24 - zdig a) >= b * 2 ^ (24 - zdig a)) by (apply Zmult_ge_compat_r; lia). lia.
  - pose proof (zdig_mono a b Ha Hb ltac:(lia)). destruct (Z.ltb_spec a b); [reflexivity | lia].
  - pose proof (zdig_mono b a Hb Ha ltac:(lia)). destruct (Z.ltb_spec a b); [lia | reflexivity].
Qed.

Lemma new_location_0 : forall d, new_location d 0 = loc_Exact.
Proof. intros d. unfold new_location, new_location_even, new_location_odd. destruct (Z.even d); reflexivity. Qed.

Lemma div_eucl_pair : forall a b, Z.div_eucl a b = (a / b, a mod b).
Proof. intros a b. unfold Z.div, Z.modulo. destruct (Z.div_eucl a b); reflexivity. Qed.

Lemma to_int_core : forall n, 1 <= n < 2 ^ 24 ->
  (if 0 <=? fexpo n then (Z.shiftl (Z.pos (mpos n)) (fexpo n), loc_Exact)
   else let d := Z.shiftl 1 (- fexpo n) in
        let '(q, r) := Z.div_eucl (Z.pos (mpos n)) d in (q, new_location d r)) = (n, loc_Exact).
Proof.
  intros n Hn. pose proof (mpos_val n Hn) as Hp. pose proof (fexpo_bounds n Hn) as He.
  destruct (zdig_bounds n Hn) as [Hd _].
  destruct (Z.leb_spec 0 (fexpo n)) as [H0|Hneg].
  - replace (fexpo n) with 0 by lia. rewrite Z.shiftl_0_r, Hp. unfold fmant. unfold fexpo in H0.
    replace (24 - zdig n) with 0 by lia. rewrite Z.mul_1_r. reflexivity.
  - cbv zeta. rewrite Z.shiftl_1_l, div_eucl_pair, Hp. unfold fmant, fexpo.
    replace (- (zdig n - 24)) with (24 - zdig n) by lia.
    assert (0 < 2 ^ (24 - zdig n)) by (apply Z.pow_pos_nonneg; lia).
    rewrite Z.div_mul, Z.mod_mul by lia. rewrite new_location_0. reflexivity.
Qed.

Lemma to_lu_val : forall md n, 1 <= n < 2 ^ 24 ->
  fp_to_int F32 md false 64 (ieee n) = (n, no_flags).
Proof.
  intros md n Hn. unfold fp_to_int. rewrite (is_nan_ieee n Hn), (decode_ieee n Hn).
  pose proof (to_int_core n Hn) as Hc. cbv zeta in Hc.
  lazymatch type of Hc with ?Y = _ => rewrite Hc end. rewrite choice_mode_exact. unfold int_lo, int_hi, int_wrap.
  rewrite Z.shiftl_1_l, Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616.
  destruct (Z.ltb_spec n 0); [lia|]. destruct (Z.ltb_spec (18446744073709551616 - 1) n); [lia|]. cbn [orb].
  rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.

Lemma to_w_val : forall md n, 1 <= n < 2 ^ 24 ->
  fp_to_int F32 md true 32 (ieee n) = (n, no_flags).
Proof.
  intros md n Hn. unfold fp_to_int. rewrite (is_nan_ieee n Hn), (decode_ieee n Hn).
  pose proof (to_int_core n Hn) as Hc. cbv zeta in Hc.
  rewrite Hc. rewrite choice_mode_exact. unfold int_lo, int_hi, int_wrap.
  rewrite !Z.shiftl_1_l, Z.land_ones by lia. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296.
  destruct (Z.ltb_spec n (Z.opp 2147483648)); [lia|]. destruct (Z.ltb_spec (2147483648 - 1) n); [lia|]. cbn [orb].
  rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.

Lemma decode_one : fp_decode F32 one32 = S754_finite false 8388608 (-23).
Proof. vm_compute. reflexivity. Qed.
Lemma is_nan_one : fp_is_nan F32 one32 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_one_val : forall md n, 1 <= n < 2 ^ 24 ->
  fp_mul F32 md one32 (ieee n) = (ieee n, no_flags).
Proof.
  intros md n Hn. pose proof (fmant_bounds n Hn) as Hm. pose proof (fexpo_bounds n Hn) as He.
  pose proof (mpos_val n Hn) as Hp.
  unfold fp_mul, nan_pass2. rewrite is_nan_one, (is_nan_ieee n Hn). cbn [orb].
  rewrite decode_one, (decode_ieee n Hn).
  unfold round_exact. replace (fp_prec F32) with 24 by reflexivity. replace (fp_emax F32) with 128 by reflexivity.
  rewrite (digits47 (8388608 * mpos n)) by (rewrite Pos2Z.inj_mul, Hp; lia).
  replace (fexp 24 128 (47 + (-23 + fexpo n))) with (fexpo n) by (unfold fexp, emin; lia).
  unfold shl_align. replace (fexpo n - (-23 + fexpo n)) with 23 by lia.
  unfold round_aux, shr_fexp. replace (fp_prec F32) with 24 by reflexivity. replace (fp_emax F32) with 128 by reflexivity.
  rewrite (Zdigits47 (Z.pos (8388608 * mpos n))) by (rewrite Pos2Z.inj_mul, Hp; lia).
  replace (fexp 24 128 (47 + (-23 + fexpo n)) - (-23 + fexpo n)) with 23 by (unfold fexp, emin; lia).
  change (8388608 * mpos n)%positive with ((mpos n)~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0)%positive.
  cbn [shr shr_record_of_loc SpecFloat.iter_pos shr_1 shr_m shr_r shr_s orb loc_of_shr_record xorb].
  rewrite choice_mode_exact.
  rewrite (Zdigits24 (Z.pos (mpos n))) by lia.
  replace (fexp 24 128 (24 + (-23 + fexpo n + 23)) - (-23 + fexpo n + 23)) with 0 by (unfold fexp, emin; lia).
  cbn [shr shr_m].
  replace (-23 + fexpo n + 23) with (fexpo n) by lia.
  destruct (Z.leb_spec (fexpo n) (128 - 24)); [|exfalso; lia].
  unfold enc. cbn [fst snd]. rewrite encode_canon by lia. unfold ieee. rewrite Hp. reflexivity.
Qed.

Lemma div_one_val : forall md n, 1 <= n < 2 ^ 24 ->
  fp_div F32 md (ieee n) one32 = (ieee n, no_flags).
Proof.
  intros md n Hn. pose proof (fmant_bounds n Hn) as Hm. pose proof (fexpo_bounds n Hn) as He.
  pose proof (mpos_val n Hn) as Hp.
  unfold fp_div, nan_pass2. rewrite is_nan_one, (is_nan_ieee n Hn). cbn [orb].
  rewrite decode_one, (decode_ieee n Hn).
  unfold SFdiv_core_binary. replace (fp_prec F32) with 24 by reflexivity. replace (fp_emax F32) with 128 by reflexivity.
  rewrite (Zdigits24 (Z.pos (mpos n))) by lia. change (Zdigits2 8388608) with 24.
  replace (Z.min (fexp 24 128 (24 + fexpo n - (24 + -23))) (fexpo n - -23)) with (fexpo n - 1) by (unfold fexp, emin; lia).
  replace (fexpo n - -23 - (fexpo n - 1)) with 24 by lia. cbn iota.
  rewrite div_eucl_pair, Z.shiftl_mul_pow2 by lia.
  replace (Z.pos (mpos n) * 2 ^ 24) with ((2 * Z.pos (mpos n)) * 8388608) by (change (2 ^ 24) with (2 * 8388608); lia).
  rewrite Z.div_mul, Z.mod_mul by lia. rewrite new_location_0.
  unfold round_aux, shr_fexp. replace (fp_prec F32) with 24 by reflexivity. replace (fp_emax F32) with 128 by reflexivity.
  rewrite (Zdigits25 (2 * Z.pos (mpos n))) by lia.
  replace (fexp 24 128 (25 + (fexpo n - 1)) - (fexpo n - 1)) with 1 by (unfold fexp, emin; lia).
  change (2 * Z.pos (mpos n)) with (Z.pos ((mpos n)~0)).
  cbn [shr shr_record_of_loc SpecFloat.iter_pos shr_1 shr_m shr_r shr_s orb loc_of_shr_record xorb].
  rewrite choice_mode_exact.
  rewrite (Zdigits24 (Z.pos (mpos n))) by lia.
  replace (fexp 24 128 (24 + (fexpo n - 1 + 1)) - (fexpo n - 1 + 1)) with 0 by (unfold fexp, emin; lia).
  cbn [shr shr_m].
  replace (fexpo n - 1 + 1) with (fexpo n) by lia.
  destruct (Z.leb_spec (fexpo n) (128 - 24)); [|exfalso; lia].
  unfold enc. cbn [fst snd]. rewrite encode_canon by lia. unfold ieee. rewrite Hp. reflexivity.
Qed.

Open Scope bv_scope.

Definition fholds (fx : FPState) (r : reg) (x : Z) : Prop :=
  reg_get (@fp_regs fx) r = nan_box (Z_to_bv 32 x).

Lemma land_shiftl_high_0 : forall a b n, (0 <= a)%Z -> (0 <= n)%Z -> (0 <= b < 2 ^ n)%Z ->
  Z.land (Z.shiftl a n) b = 0%Z.
Proof.
  intros a b n Ha Hn Hb. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases k n) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (testbit_high_false b k); [apply Bool.andb_false_r|  |lia].
    split; [lia|]. apply (Z.lt_le_trans _ (2 ^ n)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lor_shiftl_disjoint : forall a b n, (0 <= a)%Z -> (0 <= n)%Z -> (0 <= b < 2 ^ n)%Z ->
  Z.lor (Z.shiftl a n) b = (a * 2 ^ n + b)%Z.
Proof.
  intros a b n Ha Hn Hb. rewrite <- Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.lxor_lor by (apply land_shiftl_high_0; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shiftl_high_0; lia.
Qed.

Lemma nan_box_unsigned : forall v : bv 32,
  bv_unsigned (nan_box v) = ((2 ^ 32 - 1) * 2 ^ 32 + bv_unsigned v)%Z.
Proof.
  intros v. unfold nan_box. rewrite bv_concat_unsigned by reflexivity.
  pose proof (bv_unsigned_in_range _ v) as Hv. unfold bv_modulus in Hv.
  change (bv_unsigned (Z_to_bv 32 (-1))) with (2 ^ 32 - 1)%Z. change (Z.of_N 32) with 32%Z.
  apply lor_shiftl_disjoint; lia.
Qed.

Lemma unbox_nan_box : forall v : bv 32, unbox_s (nan_box v) = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range _ v) as Hv. unfold bv_modulus in Hv.
  unfold unbox_s.
  assert (H : bv_extract 32 32 (nan_box v) = Z_to_bv 32 (-1)).
  { apply bv_eq. rewrite bv_extract_unsigned, nan_box_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 32) with (2 ^ 32)%Z. change (Z.of_N 32) with 32%Z.
    rewrite Z.shiftr_div_pow2, Z.div_add_l, Z.div_small by lia. reflexivity. }
  rewrite H. change (bv_unsigned (Z_to_bv 32 (-1)) =? Z.ones 32)%Z with true. cbv iota.
  apply bv_eq. unfold low32. rewrite bv_extract_unsigned, nan_box_unsigned. unfold bv_wrap.
  change (bv_modulus 32) with (2 ^ 32)%Z. change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma fread_holds : forall (fx : FPState) r x, fholds fx r x -> (0 <= x < 2 ^ 32)%Z ->
  bv_unsigned (unbox_s (reg_get (@fp_regs fx) r)) = x.
Proof. intros fx r x -> Hx. rewrite unbox_nan_box. apply fp_u_Z2bv32. exact Hx. Qed.

Definition accrue_csr (cs : bv 32) (fl : fflags) : bv 32 := Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl)).
Lemma frm_zero_accrue_csr : forall cs fl, frm_zero cs -> frm_zero (accrue_csr cs fl).
Proof. intros cs fl Hz. apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]. Qed.

Lemma hp_step_fcvt_s_lu : forall (fx : FPState) segs regs pc mem rom w rd rs1 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_S FC_LU rd rs1 rm, 4%Z) ->
  frm_zero (@fp_csr fx) -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  exists md,
    let r := fp_of_int F32 md false 64 (bv_unsigned (getr regs rs1)) in
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (Z_to_bv 32 (fst r))) (@fp_regs fx)) (accrue_csr (@fp_csr fx) (snd r)))
                 regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 rm Hf He Hd Hz Hrm.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  exists md. cbv zeta.
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1) eqn:Hx0; cbv beta iota;
    match goal with |- context [let '(_, _) := fp_of_int ?f ?m ?sg ?b ?x in _] =>
      destruct (fp_of_int f m sg b x) as [v fl] eqn:Hof end;
    cbv beta iota; cbn [fp_regs fp_csr fst snd]; rewrite b_npc4; unfold F32, accrue_csr; cbn [fp_format] in Hof; rewrite Hof; reflexivity.
Qed.

Definition fari_op (op : fariop) : format -> rmode -> Z -> Z -> Z * fflags :=
  match op with F_ADD => fp_add | F_SUB => fp_sub | F_MUL => fp_mul | F_DIV => fp_div end.

Lemma hp_step_fari_s : forall (fx : FPState) segs regs pc mem rom w op rd rs1 rs2 (rm : bv 3) a b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fari op FMT_S rd rs1 rs2 rm, 4%Z) ->
  frm_zero (@fp_csr fx) -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  fholds fx rs1 a -> fholds fx rs2 b -> (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z ->
  exists md,
    let r := fari_op op F32 md a b in
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (Z_to_bv 32 (fst r))) (@fp_regs fx)) (accrue_csr (@fp_csr fx) (snd r)))
                 regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op rd rs1 rs2 rm a b Hf He Hd Hz Hrm Ha Hb Har Hbr.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
  pose proof (fread_holds fx rs1 a Ha Har) as Ra. pose proof (fread_holds fx rs2 b Hb Hbr) as Rb.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  exists md. cbv zeta.
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota. rewrite Ra, Rb.
  destruct op; cbn [fari_op];
    match goal with |- context [let '(_, _) := ?r in _] => destruct r as [v fl] eqn:Hof end;
    cbv beta iota; cbn [fp_regs fp_csr fst snd]; rewrite b_npc4; unfold F32, accrue_csr; cbn [fp_format] in Hof;
    rewrite Hof; reflexivity.
Qed.

Definition fcmp_op (op : fcmpop) : format -> Z -> Z -> bool * fflags :=
  match op with F_EQ => fp_eq | F_LT => fp_lt | F_LE => fp_le end.

Lemma hp_step_fcmp_s : forall (fx : FPState) segs regs pc mem rom w op rd rs1 rs2 a b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp op FMT_S rd rs1 rs2, 4%Z) ->
  fholds fx rs1 a -> fholds fx rs2 b -> (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z ->
  let r := fcmp_op op F32 a b in
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (@fp_regs fx) (accrue_csr (@fp_csr fx) (snd r)))
               (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (if fst r then 1 else 0)))
               (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op rd rs1 rs2 a b Hf He Hd Ha Hb Har Hbr.
  pose proof (fread_holds fx rs1 a Ha Har) as Ra. pose proof (fread_holds fx rs2 b Hb Hbr) as Rb.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *. cbv zeta.
  fp_pipeline Hf He Hd. rewrite Ra, Rb.
  destruct op; cbn [fcmp_op];
    match goal with |- context [let '(_, _) := ?r in _] => destruct r as [v fl] eqn:Hof end;
    cbv beta iota; cbn [fp_regs fp_csr fst snd]; unfold F32, accrue_csr; cbn [fp_format] in Hof; rewrite Hof;
    destruct (is_x0 rd); destruct v; cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

Lemma hp_step_fcvt_l_s : forall (fx : FPState) segs regs pc mem rom w (sgn : bool) rd rs1 (rm : bv 3) a,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt (if sgn then FC_L else FC_LU) FC_S rd rs1 rm, 4%Z) ->
  frm_zero (@fp_csr fx) -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  fholds fx rs1 a -> (0 <= a < 2 ^ 32)%Z ->
  exists md, rmode_of_field (bv_unsigned rm) 0 = Some md /\
    let r := fp_to_int F32 md sgn 64 a in
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (@fp_regs fx) (accrue_csr (@fp_csr fx) (snd r)))
                 (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (fst r)))
                 (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w sgn rd rs1 rm a Hf He Hd Hz Hrm Ha Har.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
  pose proof (fread_holds fx rs1 a Ha Har) as Ra.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  exists md. split; [unfold frm_zero in Hz; rewrite Hz in Hmd; exact Hmd|]. cbv zeta.
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota. rewrite Ra.
  destruct sgn; cbv beta iota;
    match goal with |- context [let '(_, _) := ?r in _] => destruct r as [v fl] eqn:Hof end;
    cbv beta iota; cbn [fp_regs fp_csr fst snd]; unfold F32, accrue_csr; cbn [fp_format] in Hof; rewrite Hof;
    destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

Lemma hp_step_fcvt_w_s : forall (fx : FPState) segs regs pc mem rom w (sgn : bool) rd rs1 (rm : bv 3) a,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt (if sgn then FC_W else FC_WU) FC_S rd rs1 rm, 4%Z) ->
  frm_zero (@fp_csr fx) -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  fholds fx rs1 a -> (0 <= a < 2 ^ 32)%Z ->
  exists md, rmode_of_field (bv_unsigned rm) 0 = Some md /\
    let r := fp_to_int F32 md sgn 32 a in
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (@fp_regs fx) (accrue_csr (@fp_csr fx) (snd r)))
                 (if bv_eqb rd 0 then regs else regupd regs rd (sext 64 (Z_to_bv 32 (fst r))))
                 (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w sgn rd rs1 rm a Hf He Hd Hz Hrm Ha Har.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
  pose proof (fread_holds fx rs1 a Ha Har) as Ra.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  exists md. split; [unfold frm_zero in Hz; rewrite Hz in Hmd; exact Hmd|]. cbv zeta.
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota. rewrite Ra.
  destruct sgn; cbv beta iota;
    match goal with |- context [let '(_, _) := ?r in _] => destruct r as [v fl] eqn:Hof end;
    cbv beta iota; cbn [fp_regs fp_csr fst snd]; unfold F32, accrue_csr; cbn [fp_format] in Hof; rewrite Hof;
    destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

Lemma hp_step_fcvt_s_w : forall (fx : FPState) segs regs pc mem rom w (sgn : bool) rd rs1 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_S (if sgn then FC_W else FC_WU) rd rs1 rm, 4%Z) ->
  frm_zero (@fp_csr fx) -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  exists md, rmode_of_field (bv_unsigned rm) 0 = Some md /\
    let r := fp_of_int F32 md sgn 32 (bv_unsigned (getr regs rs1)) in
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (Z_to_bv 32 (fst r))) (@fp_regs fx)) (accrue_csr (@fp_csr fx) (snd r)))
                 regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w sgn rd rs1 rm Hf He Hd Hz Hrm.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  exists md. split; [unfold frm_zero in Hz; rewrite Hz in Hmd; exact Hmd|]. cbv zeta.
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct sgn; destruct (is_x0 rs1) eqn:Hx0; cbv beta iota;
    match goal with |- context [let '(_, _) := fp_of_int ?f ?m ?sg ?b ?x in _] =>
      destruct (fp_of_int f m sg b x) as [v fl] eqn:Hof end;
    cbv beta iota; cbn [fp_regs fp_csr fst snd]; rewrite b_npc4; unfold F32, accrue_csr; cbn [fp_format] in Hof; rewrite Hof; reflexivity.
Qed.

Lemma fholds_set_same : forall fr cs r x, (0 <= x < 2 ^ 32)%Z ->
  fholds (mkFP (bvmap_set r (nan_box (Z_to_bv 32 x)) fr) cs) r x.
Proof. intros fr cs r x Hx. unfold fholds. cbn [fp_regs]. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.

Lemma fholds_set_other : forall fr cs r r' v x, r' <> r ->
  fholds (mkFP fr cs) r' x -> fholds (mkFP (bvmap_set r v fr) cs) r' x.
Proof.
  intros fr cs r r' v x Hne H. unfold fholds in *. cbn [fp_regs] in *. unfold reg_get in *.
  rewrite bvmap_get_set_other by (intros E; apply Hne; symmetry; exact E). exact H.
Qed.

Lemma flw_nan_box : forall x, (0 <= x < 2 ^ 32)%Z ->
  nan_box (bv_extract 0 32 (le_bytes_to_word (word_to_le_bytes 4 (Z_to_bv 64 x)))) = nan_box (Z_to_bv 32 x).
Proof.
  intros x Hx. f_equal. apply bv_eq. rewrite bv_extract_unsigned.
  unfold le_bytes_to_word. rewrite bytes_le_N, !Z_to_bv_unsigned, bv_wrap64_mod.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  repeat rewrite (Z.mod_small x) by lia. reflexivity.
Qed.

Lemma fsw_bytes : forall x, (0 <= x < 2 ^ 32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (low32 (nan_box (Z_to_bv 32 x)))) = word_to_le_bytes 4 (Z_to_bv 64 x).
Proof.
  intros x Hx. unfold word_to_le_bytes. f_equal.
  replace (low32 (nan_box (Z_to_bv 32 x))) with (unbox_s (nan_box (Z_to_bv 32 x))).
  2:{ unfold unbox_s.
      replace (bv_unsigned (bv_extract 32 32 (nan_box (Z_to_bv 32 x))) =? Z.ones 32)%Z with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. rewrite bv_extract_unsigned, nan_box_unsigned. unfold bv_wrap.
      change (bv_modulus 32) with (2 ^ 32)%Z. change (Z.of_N 32) with 32%Z.
      pose proof (bv_unsigned_in_range _ (Z_to_bv 32 x)) as Hr. unfold bv_modulus in Hr.
      rewrite Z.shiftr_div_pow2, Z.div_add_l, Z.div_small by lia. reflexivity. }
  rewrite unbox_nan_box, fp_u_Z2bv32, Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia. reflexivity.
Qed.
