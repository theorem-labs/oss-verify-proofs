(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Reals Psatz SpecFloat Bool.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
From LinuxProcessSemantics.Riscv Require Import Fpu.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Record format_ok (f : format) : Prop := {
fok_mw : 2 <= fp_mw f;
fok_ew : 2 <= fp_ew f;
fok_emax : fp_emax f = 2 ^ (fp_ew f - 1);
fok_prec_emax : fp_prec f < fp_emax f
}.
Lemma fmt_double_ok : format_ok fmt_double.
Proof. split; vm_compute; try reflexivity; try discriminate. Qed.
Lemma fmt_single_ok : format_ok fmt_single.
Proof. split; vm_compute; try reflexivity; try discriminate. Qed.
Definition fp_width (f : format) : Z := fp_mw f + fp_ew f + 1.


Lemma Zdiv_mul_add (a b m : Z) : 0 < m -> 0 <= b < m -> (a * m + b) / m = a.
Proof.
intros Hm Hb. rewrite Z.div_add_l, Z.div_small; lia.
Qed.
Lemma Zmod_mul_add (a b m : Z) : 0 < m -> 0 <= b < m -> (a * m + b) mod m = b.
Proof.
intros Hm Hb. rewrite Z.add_comm, Z.mod_add, Z.mod_small; lia.
Qed.
Lemma testbit_high_mul (s : bool) (r n : Z) :
0 <= n -> 0 <= r < 2 ^ n ->
Z.testbit ((if s then 1 else 0) * 2 ^ n + r) n = s.
Proof.
intros Hn Hr.
assert (H := Z.testbit_spec' ((if s then 1 else 0) * 2 ^ n + r) n Hn).
rewrite Zdiv_mul_add in H by (try apply Z.pow_pos_nonneg; lia).
destruct s, (Z.testbit _ _); simpl in H; try reflexivity; try discriminate.
Qed.
Lemma Pos_size_digits2_pos (m : positive) : Pos.size m = digits2_pos m.
Proof. induction m; simpl; try rewrite IHm; reflexivity. Qed.
Lemma Zpos_Pos_size (m : positive) : Z.pos (Pos.size m) = Zdigits radix2 (Z.pos m).
Proof. rewrite Pos_size_digits2_pos. apply Zpos_digits2_pos. Qed.
Lemma Zdigits_pos_lt_pow (m : positive) (n : Z) :
Zdigits radix2 (Z.pos m) <= n <-> Z.pos m < 2 ^ n.
Proof.
split; intro H.
- apply (Zpower_gt_Zdigits radix2) in H. simpl in H. exact H.
- apply (Zdigits_le_Zpower radix2). simpl. exact H.
Qed.
Lemma Zdigits_pos_gt_pow (m : positive) (n : Z) :
n < Zdigits radix2 (Z.pos m) <-> 2 ^ n <= Z.pos m.
Proof.
split; intro H.
- apply (Zpower_le_Zdigits radix2) in H. simpl in H. exact H.
- apply (Zdigits_gt_Zpower radix2). simpl. exact H.
Qed.
Section c.
Variable f : format.
Hypothesis Hf : format_ok f.
Let mw := fp_mw f.
Let ew := fp_ew f.
Let prec := fp_prec f.
Let emax := fp_emax f.
Let emin := fp_emin f.
Lemma prec_eq : prec = mw + 1.
Proof. unfold prec, mw, fp_mw. lia. Qed.
Lemma mw_ge_2 : 2 <= mw. Proof. exact (fok_mw f Hf). Qed.
Lemma ew_ge_2 : 2 <= ew. Proof. exact (fok_ew f Hf). Qed.
Lemma emax_eq : emax = 2 ^ (ew - 1). Proof. exact (fok_emax f Hf). Qed.
Lemma emin_eq : emin = 3 - emax - prec. Proof. reflexivity. Qed.
Lemma prec_lt_emax' : prec < emax. Proof. exact (fok_prec_emax f Hf). Qed.
Lemma pow_mw_pos : 0 < 2 ^ mw.
Proof. apply Z.pow_pos_nonneg; [lia|]. pose proof mw_ge_2; lia. Qed.
Lemma pow_ew_pos : 0 < 2 ^ ew.
Proof. apply Z.pow_pos_nonneg; [lia|]. pose proof ew_ge_2; lia. Qed.
Lemma pow_ew_ge_4 : 4 <= 2 ^ ew.
Proof.
pose proof ew_ge_2. change 4 with (2 ^ 2). apply Z.pow_le_mono_r; lia.
Qed.

Lemma emax_ge_2 : 2 <= emax.
Proof.
rewrite emax_eq. pose proof ew_ge_2.
replace (ew - 1) with (Z.succ (ew - 2)) by lia.
rewrite Z.pow_succ_r by lia.
assert (0 < 2 ^ (ew - 2)) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.
Lemma two_emax : 2 * emax = 2 ^ ew.
Proof.
rewrite emax_eq. pose proof ew_ge_2.
replace ew with (Z.succ (ew - 1)) at 2 by lia.
rewrite Z.pow_succ_r by lia. reflexivity.
Qed.
Lemma ones_ew : Z.ones ew = 2 ^ ew - 1.
Proof. rewrite Z.ones_equiv. lia. Qed.
#[export] Instance prec_gt_0_f : Prec_gt_0 (fp_prec f).
Proof. unfold Prec_gt_0. pose proof prec_eq. pose proof mw_ge_2. unfold prec in *. lia. Qed.
#[export] Instance prec_lt_emax_f : Prec_lt_emax (fp_prec f) (fp_emax f).
Proof. unfold Prec_lt_emax. exact prec_lt_emax'. Qed.
Lemma man_field_eq x : fp_man_field f x = x mod 2 ^ mw.
Proof. unfold fp_man_field. apply Z.land_ones. pose proof mw_ge_2; unfold mw in *; lia. Qed.
Lemma exp_field_eq x : fp_exp_field f x = (x / 2 ^ mw) mod 2 ^ ew.
Proof.
unfold fp_exp_field. rewrite Z.land_ones by (pose proof ew_ge_2; unfold ew in *; lia).
rewrite Z.shiftr_div_pow2 by (pose proof mw_ge_2; unfold mw in *; lia).
reflexivity.
Qed.
Lemma man_field_range x : 0 <= fp_man_field f x < 2 ^ mw.
Proof. rewrite man_field_eq. apply Z.mod_pos_bound, pow_mw_pos. Qed.
Lemma exp_field_range x : 0 <= fp_exp_field f x < 2 ^ ew.
Proof. rewrite exp_field_eq. apply Z.mod_pos_bound, pow_ew_pos. Qed.
Lemma decode_normal_mantissa_pos x :
0 < Z.shiftl 1 (fp_mw f) + fp_man_field f x.
Proof.
rewrite Z.shiftl_mul_pow2 by (pose proof mw_ge_2; unfold mw in *; lia).
pose proof (man_field_range x). pose proof pow_mw_pos. unfold mw in *. lia.
Qed.
Lemma fp_decode_cases x :
let s := fp_sign_bit f x in
let e := fp_exp_field f x in
let m := fp_man_field f x in
(e = 0 /\ m = 0 /\ fp_decode f x = S754_zero s) \/
(e = 0 /\ 0 < m /\ fp_decode f x = S754_finite s (Z.to_pos m) emin) \/
(e = 2 ^ ew - 1 /\ m = 0 /\ fp_decode f x = S754_infinity s) \/
(e = 2 ^ ew - 1 /\ 0 < m /\ fp_decode f x = S754_nan) \/
(0 < e < 2 ^ ew - 1 /\
fp_decode f x = S754_finite s (Z.to_pos (2 ^ mw + m)) (e + emin - 1)).
Proof.
cbv zeta.
pose proof (man_field_range x) as Hm. pose proof (exp_field_range x) as He.
unfold fp_decode. fold mw ew emin.
change (fp_ew f) with ew. rewrite ones_ew.
destruct (Z.eqb_spec (fp_exp_field f x) 0) as [E0|E0].
- destruct (fp_man_field f x) eqn:Em; [left; auto| right; left | lia].
repeat split; auto; lia.
- destruct (Z.eqb_spec (fp_exp_field f x) (2 ^ ew - 1)) as [E1|E1].
+ destruct (Z.eqb_spec (fp_man_field f x) 0) as [M0|M0].
* right; right; left. auto.
* right; right; right; left. repeat split; auto; lia.
+ right; right; right; right. split; [lia|].
pose proof (decode_normal_mantissa_pos x) as Hp.
rewrite Z.shiftl_mul_pow2 in Hp |- * by (pose proof mw_ge_2; unfold mw in *; lia).
rewrite Z.mul_1_l in Hp |- *. change (fp_mw f) with mw in Hp |- *.
destruct (2 ^ mw + fp_man_field f x) eqn:E; try lia. simpl. reflexivity.
Qed.
Lemma fexp_eq e : SpecFloat.fexp prec emax e = Z.max (e - prec) emin.
Proof. reflexivity. Qed.


Lemma bounded_iff (m : positive) (e : Z) :
SpecFloat.bounded prec emax m e = true <->
(Zdigits radix2 (Z.pos m) = prec /\ emin <= e <= emax - prec) \/
(Zdigits radix2 (Z.pos m) < prec /\ e = emin).
Proof.
unfold SpecFloat.bounded, canonical_mantissa.
rewrite Zpos_digits2_pos. fold prec emax. rewrite fexp_eq.
rewrite Bool.andb_true_iff, Z.eqb_eq, Z.leb_le.
pose proof prec_eq. pose proof prec_lt_emax'. pose proof emax_ge_2. pose proof mw_ge_2.
rewrite emin_eq in *. lia.
Qed.

Lemma fp_is_nan_decode x :
fp_is_nan f x = match fp_decode f x with S754_nan => true | _ => false end.
Proof.
unfold fp_is_nan. change (fp_ew f) with ew. rewrite ones_ew.
pose proof pow_ew_ge_4.
destruct (fp_decode_cases x) as [(He&Hm&E)|[(He&Hm&E)|[(He&Hm&E)|[(He&Hm&E)|(He&E)]]]];
rewrite E, ?He, ?Hm.
- replace (0 =? 2 ^ ew - 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
- replace (0 =? 2 ^ ew - 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
- rewrite Z.eqb_refl. reflexivity.
- rewrite Z.eqb_refl. destruct (Z.eqb_spec (fp_man_field f x) 0); [lia|reflexivity].
- destruct (Z.eqb_spec (fp_exp_field f x) (2 ^ ew - 1)); [lia|reflexivity].
Qed.

Lemma sb_eq (s : bool) :
(if s then Z.shiftl 1 (fp_mw f + fp_ew f) else 0) = (if s then 1 else 0) * 2 ^ ew * 2 ^ mw.
Proof.
rewrite Z.shiftl_mul_pow2 by (pose proof mw_ge_2; pose proof ew_ge_2; unfold mw, ew in *; lia).
change (fp_mw f) with mw. change (fp_ew f) with ew.
rewrite Z.pow_add_r by (pose proof mw_ge_2; pose proof ew_ge_2; lia).
destruct s; ring.
Qed.
Lemma canonical_nan_eq :
fp_canonical_nan f = (2 ^ ew - 1) * 2 ^ mw + 2 ^ (mw - 1).
Proof.
unfold fp_canonical_nan. change (fp_ew f) with ew. change (fp_mw f) with mw.
rewrite ones_ew, !Z.shiftl_mul_pow2 by (pose proof mw_ge_2; lia). lia.
Qed.
Lemma fields_of_layout (s : bool) (E M : Z) :
0 <= E < 2 ^ ew -> 0 <= M < 2 ^ mw ->
let x := (if s then 1 else 0) * 2 ^ ew * 2 ^ mw + E * 2 ^ mw + M in
fp_sign_bit f x = s /\ fp_exp_field f x = E /\ fp_man_field f x = M.
Proof.
intros HE HM x.
pose proof pow_mw_pos. pose proof pow_ew_pos. pose proof mw_ge_2. pose proof ew_ge_2.
assert (Hx : x = ((if s then 1 else 0) * 2 ^ ew + E) * 2 ^ mw + M) by (unfold x; ring).
split; [|split].
- unfold fp_sign_bit. change (fp_mw f + fp_ew f) with (mw + ew).
replace x with ((if s then 1 else 0) * 2 ^ (mw + ew) + (E * 2 ^ mw + M)).
2:{ rewrite Z.pow_add_r by lia. unfold x. ring. }
apply testbit_high_mul; [lia|].
rewrite Z.pow_add_r by lia. split; [nia|].
apply Z.lt_le_trans with ((E + 1) * 2 ^ mw); [lia|].
rewrite (Z.mul_comm (2 ^ mw)). apply Z.mul_le_mono_nonneg_r; lia.
- rewrite exp_field_eq, Hx, Zdiv_mul_add by lia.
apply Zmod_mul_add; lia.
- rewrite man_field_eq, Hx. apply Zmod_mul_add; lia.
Qed.
Lemma layout_range (s : bool) (E M : Z) :
0 <= E < 2 ^ ew -> 0 <= M < 2 ^ mw ->
0 <= (if s then 1 else 0) * 2 ^ ew * 2 ^ mw + E * 2 ^ mw + M < 2 ^ fp_width f.
Proof.
intros HE HM. unfold fp_width. change (fp_mw f + fp_ew f + 1) with (mw + ew + 1).
pose proof pow_mw_pos. pose proof pow_ew_pos. pose proof mw_ge_2. pose proof ew_ge_2.
rewrite !Z.pow_add_r by lia. change (2 ^ 1) with 2.
split; [destruct s; nia|].
assert (E * 2 ^ mw + M < 2 ^ ew * 2 ^ mw).
{ apply Z.lt_le_trans with ((E + 1) * 2 ^ mw); [lia|].
apply Z.mul_le_mono_nonneg_r; lia. }
destruct s; nia.
Qed.
Theorem fp_encode_range sf :
valid_binary prec emax sf = true ->
0 <= fp_encode f sf < 2 ^ fp_width f.
Proof.
intros Hv.
pose proof pow_mw_pos as Pm. pose proof pow_ew_pos as Pe. pose proof mw_ge_2. pose proof ew_ge_2.
assert (Hmw1 : 2 ^ (mw - 1) < 2 ^ mw) by (apply Z.pow_lt_mono_r; lia).
assert (Hmw0 : 0 < 2 ^ (mw - 1)) by (apply Z.pow_pos_nonneg; lia).
destruct sf as [s|s| |s m e]; unfold fp_encode.
- rewrite sb_eq.
replace (_ * 2 ^ ew * 2 ^ mw) with ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + 0 * 2 ^ mw + 0) by ring.
apply layout_range; lia.
- rewrite sb_eq. change (fp_ew f) with ew. change (fp_mw f) with mw.
rewrite ones_ew, Z.shiftl_mul_pow2 by lia.
replace (_ + _) with ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + (2 ^ ew - 1) * 2 ^ mw + 0) by ring.
apply layout_range; lia.
- rewrite canonical_nan_eq.
replace (_ + _) with ((if false then 1 else 0) * 2 ^ ew * 2 ^ mw + (2 ^ ew - 1) * 2 ^ mw + 2 ^ (mw - 1)) by ring.
apply (layout_range false); lia.
- simpl in Hv. apply bounded_iff in Hv.
rewrite Zpos_Pos_size. change (fp_prec f) with prec. change (fp_mw f) with mw.
change (fp_emin f) with emin. rewrite sb_eq.
pose proof prec_eq as Hp.
destruct Hv as [(Hd & He)|(Hd & He)].
+ replace (Zdigits radix2 (Z.pos m) <? prec) with false by (symmetry; apply Z.ltb_ge; lia).
assert (Hm2 : 2 ^ mw <= Z.pos m < 2 ^ (mw + 1)).
{ split. apply (proj1 (Zdigits_pos_gt_pow m mw)); lia.
apply (proj1 (Zdigits_pos_lt_pow m (mw + 1))); lia. }
rewrite Z.pow_add_r in Hm2 by lia. change (2 ^ 1) with 2 in Hm2.
rewrite !Z.shiftl_mul_pow2 by lia.
replace (_ + _ + _) with ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + (e - emin + 1) * 2 ^ mw + (Z.pos m - 2 ^ mw)) by ring.
apply layout_range; [|lia]. pose proof two_emax. pose proof emin_eq. pose proof prec_lt_emax'. lia.
+ replace (Zdigits radix2 (Z.pos m) <? prec) with true by (symmetry; apply Z.ltb_lt; lia).
assert (Z.pos m < 2 ^ mw) by (apply (proj1 (Zdigits_pos_lt_pow m mw)); lia).
replace (_ + _) with ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + 0 * 2 ^ mw + Z.pos m) by ring.
apply layout_range; lia.
Qed.
Theorem fp_decode_encode sf :
valid_binary prec emax sf = true ->
fp_decode f (fp_encode f sf) = sf.
Proof.
intros Hv.
pose proof pow_mw_pos as Pm. pose proof pow_ew_pos as Pe. pose proof mw_ge_2. pose proof ew_ge_2.
assert (Hmw1 : 2 ^ (mw - 1) < 2 ^ mw) by (apply Z.pow_lt_mono_r; lia).
assert (Hmw0 : 0 < 2 ^ (mw - 1)) by (apply Z.pow_pos_nonneg; lia).
assert (Hew3 : 3 <= 2 ^ ew - 1).
{ replace ew with (Z.succ (Z.succ (ew - 2))) by lia. rewrite !Z.pow_succ_r by lia.
assert (0 < 2 ^ (ew - 2)) by (apply Z.pow_pos_nonneg; lia). lia. }
destruct sf as [s|s| |s m e]; unfold fp_encode.
- rewrite sb_eq.
replace (_ * 2 ^ ew * 2 ^ mw) with ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + 0 * 2 ^ mw + 0) by ring.
destruct (fields_of_layout s 0 0) as (Hs & He & Hm); [lia|lia|].
cbv zeta in *.
destruct (fp_decode_cases ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + 0 * 2 ^ mw + 0))
as [(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|(E1&E)]]]]; rewrite ?Hs, ?He, ?Hm in *; try lia.
exact E.
- rewrite sb_eq. change (fp_ew f) with ew. change (fp_mw f) with mw.
rewrite ones_ew, Z.shiftl_mul_pow2 by lia.
replace (_ + _) with ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + (2 ^ ew - 1) * 2 ^ mw + 0) by ring.
destruct (fields_of_layout s (2 ^ ew - 1) 0) as (Hs & He & Hm); [lia|lia|].
cbv zeta in *.
destruct (fp_decode_cases ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + (2 ^ ew - 1) * 2 ^ mw + 0))
as [(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|(E1&E)]]]]; rewrite ?Hs, ?He, ?Hm in *; try lia.
exact E.
- rewrite canonical_nan_eq.
replace (_ + _) with ((if false then 1 else 0) * 2 ^ ew * 2 ^ mw + (2 ^ ew - 1) * 2 ^ mw + 2 ^ (mw - 1)) by ring.
destruct (fields_of_layout false (2 ^ ew - 1) (2 ^ (mw - 1))) as (Hs & He & Hm); [lia|lia|].
cbv zeta in *.
destruct (fp_decode_cases ((if false then 1 else 0) * 2 ^ ew * 2 ^ mw + (2 ^ ew - 1) * 2 ^ mw + 2 ^ (mw - 1)))
as [(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|(E1&E)]]]]; rewrite ?Hs, ?He, ?Hm in *; try lia.
exact E.
- simpl in Hv. pose proof Hv as Hb. apply bounded_iff in Hv.
rewrite Zpos_Pos_size. change (fp_prec f) with prec. change (fp_mw f) with mw.
change (fp_emin f) with emin. rewrite sb_eq.
pose proof prec_eq as Hp. pose proof two_emax as H2.
destruct Hv as [(Hd & He)|(Hd & He)].
+ replace (Zdigits radix2 (Z.pos m) <? prec) with false by (symmetry; apply Z.ltb_ge; lia).
assert (Hm2 : 2 ^ mw <= Z.pos m < 2 ^ (mw + 1)).
{ split. apply (proj1 (Zdigits_pos_gt_pow m mw)); lia.
apply (proj1 (Zdigits_pos_lt_pow m (mw + 1))); lia. }
rewrite Z.pow_add_r in Hm2 by lia. change (2 ^ 1) with 2 in Hm2.
rewrite !Z.shiftl_mul_pow2 by lia.
replace (_ + _ + _) with ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + (e - emin + 1) * 2 ^ mw + (Z.pos m - 2 ^ mw)) by ring.
pose proof emin_eq. pose proof prec_lt_emax'.
destruct (fields_of_layout s (e - emin + 1) (Z.pos m - 2 ^ mw)) as (Hs & He' & Hm'); [lia|lia|].
cbv zeta in *.
destruct (fp_decode_cases ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + (e - emin + 1) * 2 ^ mw + (Z.pos m - 2 ^ mw)))
as [(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|(E1&E)]]]]; rewrite ?Hs, ?He', ?Hm' in *; try lia.
rewrite E. f_equal; [|lia].
replace (2 ^ mw + (Z.pos m - 2 ^ mw)) with (Z.pos m) by lia. reflexivity.
+ replace (Zdigits radix2 (Z.pos m) <? prec) with true by (symmetry; apply Z.ltb_lt; lia).
assert (Z.pos m < 2 ^ mw) by (apply (proj1 (Zdigits_pos_lt_pow m mw)); lia).
replace (_ + _) with ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + 0 * 2 ^ mw + Z.pos m) by ring.
destruct (fields_of_layout s 0 (Z.pos m)) as (Hs & He' & Hm'); [lia|lia|].
cbv zeta in *.
destruct (fp_decode_cases ((if s then 1 else 0) * 2 ^ ew * 2 ^ mw + 0 * 2 ^ mw + Z.pos m))
as [(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|(E1&E)]]]]; rewrite ?Hs, ?He', ?Hm' in *; try lia.
rewrite E. subst e. reflexivity.
Qed.
Lemma man_field_neg x : fp_man_field f (fp_neg f x) = fp_man_field f x.
Proof.
rewrite !man_field_eq. unfold fp_neg. change (fp_mw f + fp_ew f) with (mw + ew).
pose proof mw_ge_2. pose proof ew_ge_2.
rewrite Z.shiftl_mul_pow2, Z.mul_1_l by lia.
apply Z.bits_inj'. intros n Hn.
rewrite !Z.testbit_mod_pow2 by lia.
destruct (Z.ltb_spec n mw); simpl; [|reflexivity].
rewrite Z.lxor_spec, Z.pow2_bits_false by lia. apply Bool.xorb_false_r.
Qed.
Lemma exp_field_neg x : fp_exp_field f (fp_neg f x) = fp_exp_field f x.
Proof.
rewrite !exp_field_eq. unfold fp_neg. change (fp_mw f + fp_ew f) with (mw + ew).
pose proof mw_ge_2. pose proof ew_ge_2.
rewrite Z.shiftl_mul_pow2, Z.mul_1_l by lia.
apply Z.bits_inj'. intros n Hn.
rewrite !Z.testbit_mod_pow2 by lia.
destruct (Z.ltb_spec n ew); simpl; [|reflexivity].
rewrite !Z.div_pow2_bits by lia.
rewrite Z.lxor_spec, Z.pow2_bits_false by lia. apply Bool.xorb_false_r.
Qed.
Lemma sign_bit_neg x : fp_sign_bit f (fp_neg f x) = negb (fp_sign_bit f x).
Proof.
unfold fp_sign_bit, fp_neg. change (fp_mw f + fp_ew f) with (mw + ew).
pose proof mw_ge_2. pose proof ew_ge_2.
rewrite Z.shiftl_mul_pow2, Z.mul_1_l by lia.
rewrite Z.lxor_spec, Z.pow2_bits_true by lia. apply Bool.xorb_true_r.
Qed.
Theorem fp_decode_neg x : fp_decode f (fp_neg f x) = SFopp (fp_decode f x).
Proof.
unfold fp_decode. rewrite man_field_neg, exp_field_neg, sign_bit_neg.
destruct (fp_exp_field f x =? 0).
- destruct (fp_man_field f x); reflexivity.
- destruct (fp_exp_field f x =? Z.ones (fp_ew f)).
+ destruct (fp_man_field f x =? 0); reflexivity.
+ pose proof (decode_normal_mantissa_pos x).
destruct (Z.shiftl 1 (fp_mw f) + fp_man_field f x); try reflexivity; lia.
Qed.



Definition fp_abs (x : Z) : Z := x mod 2 ^ (fp_width f - 1).



Definition SFabs (x : spec_float) : spec_float :=
match x with
| S754_nan => S754_nan
| S754_infinity _ => S754_infinity false
| S754_finite _ m e => S754_finite false m e
| S754_zero _ => S754_zero false
end.

Lemma fp_abs_range x : 0 <= fp_abs x < 2 ^ fp_width f.
Proof.
unfold fp_abs. pose proof mw_ge_2. pose proof ew_ge_2. unfold fp_width.
change (fp_mw f + fp_ew f) with (mw + ew).
pose proof (Z.mod_pos_bound x (2 ^ (mw + ew + 1 - 1)) ltac:(apply Z.pow_pos_nonneg; lia)).
assert (2 ^ (mw + ew + 1 - 1) < 2 ^ (mw + ew + 1)) by (apply Z.pow_lt_mono_r; lia). lia.
Qed.
Definition sf_sign' (x : spec_float) : bool :=
match x with
| S754_zero s | S754_infinity s | S754_finite s _ _ => s
| S754_nan => fp_sign_bit f (fp_canonical_nan f)
end.
Lemma fp_sign_bit_decode x :
fp_decode f x <> S754_nan -> sf_sign (fp_decode f x) = fp_sign_bit f x.
Proof.
destruct (fp_decode_cases x) as [(He&Hm&E)|[(He&Hm&E)|[(He&Hm&E)|[(He&Hm&E)|(He&E)]]]];
rewrite E; simpl; congruence.
Qed.
Lemma fp_sign_bit_false_iff x :
0 <= x < 2 ^ fp_width f ->
fp_sign_bit f x = false <-> x < 2 ^ (fp_width f - 1).
Proof.
intros Hx. unfold fp_sign_bit, fp_width in *.
change (fp_mw f + fp_ew f) with (mw + ew) in *.
pose proof mw_ge_2. pose proof ew_ge_2.
replace (mw + ew + 1 - 1) with (mw + ew) by lia.
pose proof (Z.testbit_spec' x (mw + ew)) as Ht.
assert (Hp : 0 < 2 ^ (mw + ew)) by (apply Z.pow_pos_nonneg; lia).
rewrite Z.pow_add_r, Z.pow_1_r in Hx by lia.
assert (Hq : x / 2 ^ (mw + ew) = 0 \/ x / 2 ^ (mw + ew) = 1).
{ assert (0 <= x / 2 ^ (mw + ew) < 2); [|lia].
split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
destruct (Z.testbit x (mw + ew)); simpl in Ht; specialize (Ht ltac:(lia)).
- split; [discriminate|]. intros Hl. rewrite Z.div_small in Ht by lia. rewrite Z.mod_0_l in Ht by lia. lia.
- split; [|reflexivity]. intros _.
destruct Hq as [Hq|Hq]; rewrite Hq in Ht; [|rewrite Z.mod_1_l in Ht by lia; lia].
apply Z.div_small_iff in Hq; lia.
Qed.
Lemma fp_decode_0 : fp_decode f 0 = S754_zero false.
Proof.
destruct (fields_of_layout false 0 0) as (Hs & He & Hm);
[pose proof pow_ew_pos; lia | pose proof pow_mw_pos; lia |].
cbv zeta in *. rewrite !Z.mul_0_l, !Z.add_0_r in *.
destruct (fp_decode_cases 0) as [(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|[(E1&M1&E)|(E1&E)]]]];
rewrite ?Hs, ?He, ?Hm in *; try lia; try exact E.
pose proof pow_ew_ge_4. lia.
Qed.

End c.
