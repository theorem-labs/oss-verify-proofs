(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition lo32 (a : Z) : Z := a mod 2^32.
Definition sx32 (a : Z) : Z :=
let l := a mod 2^32 in if l <? 2^31 then l else l + 2^64 - 2^32.
Definition add64 (a b : Z) : Z := (a + b) mod 2^64.
Definition sub64 (a b : Z) : Z := (a - b) mod 2^64.
Definition neg64 (a : Z) : Z := (- a) mod 2^64.
Definition not64 (a : Z) : Z := (Z.lnot a) mod 2^64.
Definition sll64 (a k : Z) : Z := (Z.shiftl a k) mod 2^64.
Definition mul64 (a b : Z) : Z := (a * b) mod 2^64.
Definition sltu (a b : Z) : Z := if a <? b then 1 else 0.
Definition addw (a b : Z) : Z := sx32 (a + b).
Definition subw (a b : Z) : Z := sx32 (a - b).
Definition negw (a : Z) : Z := sx32 (- a).
Definition sllw (a b : Z) : Z := sx32 (Z.shiftl a (b mod 32)).
Definition srlw (a b : Z) : Z := sx32 (Z.shiftr (lo32 a) (b mod 32)).
Lemma pow2_32_pos : 0 < 2^32. Proof. reflexivity. Qed.
Lemma pow2_64_pos : 0 < 2^64. Proof. reflexivity. Qed.
Lemma lo32_range a : 0 <= lo32 a < 2^32.
Proof. unfold lo32. apply Z.mod_pos_bound. reflexivity. Qed.
Lemma lo32_small a : 0 <= a < 2^32 -> lo32 a = a.
Proof. intros. unfold lo32. apply Z.mod_small. lia. Qed.
Lemma lo32_mod a : lo32 a mod 2^32 = lo32 a.
Proof. unfold lo32. apply Z.mod_mod. lia. Qed.
Lemma sx32_cases a :
(a mod 2^32 < 2^31 /\ sx32 a = a mod 2^32) \/
(2^31 <= a mod 2^32 /\ sx32 a = a mod 2^32 + 2^64 - 2^32).
Proof.
unfold sx32. destruct (a mod 2^32 <? 2^31) eqn:E.
- apply Z.ltb_lt in E. left. auto.
- apply Z.ltb_ge in E. right. auto.
Qed.
Lemma sx32_range a : 0 <= sx32 a < 2^64.
Proof.
pose proof (Z.mod_pos_bound a (2^32) pow2_32_pos).
destruct (sx32_cases a) as [[H1 H2]|[H1 H2]]; rewrite H2; lia.
Qed.
Lemma sx32_mod32 a : sx32 a mod 2^32 = a mod 2^32.
Proof.
pose proof (Z.mod_pos_bound a (2^32) pow2_32_pos).
destruct (sx32_cases a) as [[H1 H2]|[H1 H2]]; rewrite H2.
- apply Z.mod_mod. lia.
- replace (a mod 2^32 + 2^64 - 2^32) with (a mod 2^32 + (2^32 - 1) * 2^32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma lo32_sx32 a : lo32 (sx32 a) = lo32 a.
Proof. unfold lo32. apply sx32_mod32. Qed.
Lemma sx32_congr a b : a mod 2^32 = b mod 2^32 -> sx32 a = sx32 b.
Proof. intros E. unfold sx32. rewrite E. reflexivity. Qed.
Lemma sx32_lo32 a : sx32 (lo32 a) = sx32 a.
Proof. apply sx32_congr. apply lo32_mod. Qed.
Lemma sx32_idem a : sx32 (sx32 a) = sx32 a.
Proof. apply sx32_congr. apply sx32_mod32. Qed.
Lemma sx32_small a : 0 <= a < 2^31 -> sx32 a = a.
Proof.
intros H. unfold sx32. rewrite Z.mod_small by lia.
destruct (a <? 2^31) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. lia.
Qed.
Lemma sx32_big a : 2^31 <= a < 2^32 -> sx32 a = a + 2^64 - 2^32.
Proof.
intros H. unfold sx32. rewrite Z.mod_small by lia.
destruct (a <? 2^31) eqn:E; [|reflexivity]. apply Z.ltb_lt in E. lia.
Qed.
Lemma sx32_neg_small a : 0 < a <= 2^31 -> sx32 (- a) = 2^64 - a.
Proof.
intros H. unfold sx32.
replace ((- a) mod 2^32) with (2^32 - a).
2:{ symmetry. replace (- a) with ((2^32 - a) + (-1) * 2^32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
destruct (2^32 - a <? 2^31) eqn:E; [apply Z.ltb_lt in E; lia|lia].
Qed.
Lemma sx32_inj a b : sx32 a = sx32 b <-> a mod 2^32 = b mod 2^32.
Proof.
split; [|apply sx32_congr]. intros E.
rewrite <- (sx32_mod32 a), <- (sx32_mod32 b), E. reflexivity.
Qed.
Lemma sx32_inj_u32 a b : 0 <= a < 2^32 -> 0 <= b < 2^32 -> (sx32 a = sx32 b <-> a = b).
Proof.
intros Ha Hb. rewrite sx32_inj, !Z.mod_small by lia. tauto.
Qed.
Lemma sx32_zero_iff a : sx32 a = 0 <-> a mod 2^32 = 0.
Proof.
rewrite <- (sx32_small 0) by lia. rewrite sx32_inj. rewrite Z.mod_0_l by lia. tauto.
Qed.
Lemma sx32_zero_iff_u32 a : 0 <= a < 2^32 -> (sx32 a = 0 <-> a = 0).
Proof. intros. rewrite sx32_zero_iff, Z.mod_small by lia. tauto. Qed.
Lemma sx32_nonzero_u32 a : 0 < a < 2^32 -> sx32 a <> 0.
Proof. intros H E. apply (proj1 (sx32_zero_iff_u32 a ltac:(lia))) in E. lia. Qed.
Lemma addw_congr a a' b b' :
a mod 2^32 = a' mod 2^32 -> b mod 2^32 = b' mod 2^32 -> addw a b = addw a' b'.
Proof.
intros Ha Hb. unfold addw. apply sx32_congr.
rewrite Zplus_mod, Ha, Hb, <- Zplus_mod. reflexivity.
Qed.
Lemma subw_congr a a' b b' :
a mod 2^32 = a' mod 2^32 -> b mod 2^32 = b' mod 2^32 -> subw a b = subw a' b'.
Proof.
intros Ha Hb. unfold subw. apply sx32_congr.
rewrite Zminus_mod, Ha, Hb, <- Zminus_mod. reflexivity.
Qed.
Lemma negw_congr a a' : a mod 2^32 = a' mod 2^32 -> negw a = negw a'.
Proof.
intros Ha. unfold negw. apply sx32_congr.
replace (- a) with (0 - a) by lia. replace (- a') with (0 - a') by lia.
rewrite Zminus_mod, Ha, <- Zminus_mod. reflexivity.
Qed.
Lemma shiftl_mod32 a k : 0 <= k -> (Z.shiftl a k) mod 2^32 = (Z.shiftl (a mod 2^32) k) mod 2^32.
Proof.
intros Hk. rewrite !Z.shiftl_mul_pow2 by lia.
rewrite <- Zmult_mod_idemp_l. reflexivity.
Qed.
Lemma sllw_congr a a' b : a mod 2^32 = a' mod 2^32 -> sllw a b = sllw a' b.
Proof.
intros Ha. unfold sllw. apply sx32_congr.
pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
rewrite shiftl_mod32, Ha, <- shiftl_mod32 by lia. reflexivity.
Qed.
Lemma srlw_congr a a' b : a mod 2^32 = a' mod 2^32 -> srlw a b = srlw a' b.
Proof. intros Ha. unfold srlw, lo32. rewrite Ha. reflexivity. Qed.
Lemma addw_sx32_l a b : addw (sx32 a) b = addw a b.
Proof. apply addw_congr; [apply sx32_mod32|reflexivity]. Qed.
Lemma addw_sx32_r a b : addw a (sx32 b) = addw a b.
Proof. apply addw_congr; [reflexivity|apply sx32_mod32]. Qed.
Lemma subw_sx32_l a b : subw (sx32 a) b = subw a b.
Proof. apply subw_congr; [apply sx32_mod32|reflexivity]. Qed.
Lemma subw_sx32_r a b : subw a (sx32 b) = subw a b.
Proof. apply subw_congr; [reflexivity|apply sx32_mod32]. Qed.
Lemma negw_sx32 a : negw (sx32 a) = negw a.
Proof. apply negw_congr. apply sx32_mod32. Qed.
Lemma sllw_sx32 a b : sllw (sx32 a) b = sllw a b.
Proof. apply sllw_congr. apply sx32_mod32. Qed.
Lemma srlw_sx32 a b : srlw (sx32 a) b = srlw a b.
Proof. apply srlw_congr. apply sx32_mod32. Qed.
Lemma addw_lo32_l a b : addw (lo32 a) b = addw a b.
Proof. apply addw_congr; [apply lo32_mod|reflexivity]. Qed.
Lemma subw_lo32_l a b : subw (lo32 a) b = subw a b.
Proof. apply subw_congr; [apply lo32_mod|reflexivity]. Qed.
Lemma addw_0_r a : addw a 0 = sx32 a.
Proof. unfold addw. rewrite Z.add_0_r. reflexivity. Qed.
Lemma sub64_0_l b : sub64 0 b = neg64 b.
Proof. unfold sub64, neg64. f_equal. Qed.
Lemma subw_0_l b : subw 0 b = negw b.
Proof. unfold subw, negw. f_equal. Qed.
Lemma mod64_mod32 x : (x mod 2^64) mod 2^32 = x mod 2^32.
Proof. apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.
Lemma lo32_add64 a b : lo32 (add64 a b) = lo32 (a + b).
Proof. unfold lo32, add64. apply mod64_mod32. Qed.
Lemma lo32_sub64 a b : lo32 (sub64 a b) = lo32 (a - b).
Proof. unfold lo32, sub64. apply mod64_mod32. Qed.
Lemma lo32_congr_add a a' b b' :
lo32 a = lo32 a' -> lo32 b = lo32 b' -> lo32 (a + b) = lo32 (a' + b').
Proof. unfold lo32. intros Ha Hb. rewrite Zplus_mod, Ha, Hb, <- Zplus_mod. reflexivity. Qed.
Lemma lo32_congr_sub a a' b b' :
lo32 a = lo32 a' -> lo32 b = lo32 b' -> lo32 (a - b) = lo32 (a' - b').
Proof. unfold lo32. intros Ha Hb. rewrite Zminus_mod, Ha, Hb, <- Zminus_mod. reflexivity. Qed.
Lemma addw_small a b : 0 <= a + b < 2^31 -> addw a b = a + b.
Proof. intros. unfold addw. apply sx32_small. lia. Qed.
Lemma subw_small a b : 0 <= a - b < 2^31 -> subw a b = a - b.
Proof. intros. unfold subw. apply sx32_small. lia. Qed.
Lemma sextw_small a : 0 <= a < 2^31 -> sx32 a = a.
Proof. apply sx32_small. Qed.
Lemma add64_small a b : 0 <= a + b < 2^64 -> add64 a b = a + b.
Proof. intros. unfold add64. apply Z.mod_small. lia. Qed.
Lemma sub64_small a b : 0 <= a - b < 2^64 -> sub64 a b = a - b.
Proof. intros. unfold sub64. apply Z.mod_small. lia. Qed.
Lemma mul64_small a b : 0 <= a * b < 2^64 -> mul64 a b = a * b.
Proof. intros. unfold mul64. apply Z.mod_small. lia. Qed.
Lemma sll64_small a k : 0 <= k -> 0 <= a * 2^k < 2^64 -> sll64 a k = a * 2^k.
Proof. intros. unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. Qed.
Lemma add64_neg_imm a c : 0 <= c <= a -> a < 2^64 -> add64 a (2^64 - c) = a - c.
Proof.
intros. unfold add64. replace (a + (2^64 - c)) with ((a - c) + 1 * 2^64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma not64_eq a : 0 <= a < 2^64 -> not64 a = 2^64 - 1 - a.
Proof.
intros. unfold not64, Z.lnot. replace (Z.pred (- a)) with ((2^64 - 1 - a) + (-1) * 2^64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma neg64_eq a : 0 < a <= 2^64 -> neg64 a = 2^64 - a.
Proof.
intros. unfold neg64. replace (- a) with ((2^64 - a) + (-1) * 2^64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma neg64_0 : neg64 0 = 0.
Proof. reflexivity. Qed.
Lemma testbit_mod_pow2 a n i : 0 <= n -> 0 <= i ->
Z.testbit (a mod 2^n) i = if i <? n then Z.testbit a i else false.
Proof.
intros Hn Hi. destruct (i <? n) eqn:E.
- apply Z.ltb_lt in E. apply Z.mod_pow2_bits_low. lia.
- apply Z.ltb_ge in E. apply Z.mod_pow2_bits_high. lia.
Qed.
Lemma testbit_high_false a n i : 0 <= a < 2^n -> 0 <= n <= i -> Z.testbit a i = false.
Proof. intros. apply (testbit_false_of_lt a n i); lia. Qed.
Lemma testbit31_u32 l : 0 <= l < 2^32 -> Z.testbit l 31 = (2^31 <=? l).
Proof.
intros Hl. destruct (2^31 <=? l) eqn:E.
- apply Z.leb_le in E. apply Z.testbit_true; [lia|].
replace (l / 2^31) with 1; [reflexivity|].
apply Z.div_unique with (r := l - 2^31); lia.
- apply Z.leb_gt in E. apply Z.testbit_false; [lia|].
rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma testbit_sx32 a i : 0 <= i ->
Z.testbit (sx32 a) i =
if i <? 32 then Z.testbit a i else if i <? 64 then Z.testbit a 31 else false.
Proof.
intros Hi.
pose proof (Z.mod_pos_bound a (2^32) pow2_32_pos) as Hl.
set (l := a mod 2^32) in *.
assert (Hb31 : Z.testbit a 31 = (2^31 <=? l)).
{ rewrite <- testbit31_u32 by lia. subst l. symmetry. apply Z.mod_pow2_bits_low. lia. }
assert (Hlow : forall j, 0 <= j -> j < 32 -> Z.testbit l j = Z.testbit a j).
{ intros j Hj Hj'. subst l. apply Z.mod_pow2_bits_low. lia. }
destruct (sx32_cases a) as [[H1 H2]|[H1 H2]]; rewrite H2; fold l in H1, H2 |- *.
- destruct (i <? 32) eqn:E1.
+ apply Z.ltb_lt in E1. apply Hlow; lia.
+ apply Z.ltb_ge in E1. rewrite (testbit_high_false l 32 i) by lia.
destruct (i <? 64); [|reflexivity]. rewrite Hb31. symmetry. apply Z.leb_gt. lia.
-
replace (l + 2^64 - 2^32) with (l + (2^32 - 1) * 2^32) by lia.
destruct (i <? 32) eqn:E1.
+ apply Z.ltb_lt in E1.
rewrite <- (Z.mod_pow2_bits_low _ 32 i) by lia.
rewrite Z.mod_add, Z.mod_small by lia. apply Hlow; lia.
+ apply Z.ltb_ge in E1.
replace i with ((i - 32) + 32) at 1 by lia.
rewrite <- (Z.div_pow2_bits _ 32 (i - 32)) by lia.
rewrite Z.div_add, Z.div_small by lia. rewrite Z.add_0_l.
replace (2^32 - 1) with (Z.ones 32) by reflexivity.
rewrite Z.testbit_ones by lia.
destruct (i <? 64) eqn:E2.
* apply Z.ltb_lt in E2. rewrite Hb31.
transitivity true; [|symmetry; apply Z.leb_le; lia].
apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
* apply Z.ltb_ge in E2. apply andb_false_intro2. apply Z.ltb_ge. lia.
Qed.
Lemma land_sx32 a b : Z.land (sx32 a) (sx32 b) = sx32 (Z.land a b).
Proof.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, !testbit_sx32, Z.land_spec by lia.
destruct (i <? 32); [reflexivity|]. destruct (i <? 64); [|reflexivity].
rewrite Z.land_spec. reflexivity.
Qed.
Lemma lor_sx32 a b : Z.lor (sx32 a) (sx32 b) = sx32 (Z.lor a b).
Proof.
apply Z.bits_inj'. intros i Hi.
rewrite Z.lor_spec, !testbit_sx32, Z.lor_spec by lia.
destruct (i <? 32); [reflexivity|]. destruct (i <? 64); [|reflexivity].
rewrite Z.lor_spec. reflexivity.
Qed.
Lemma lxor_sx32 a b : Z.lxor (sx32 a) (sx32 b) = sx32 (Z.lxor a b).
Proof.
apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, !testbit_sx32, Z.lxor_spec by lia.
destruct (i <? 32); [reflexivity|]. destruct (i <? 64); [|reflexivity].
rewrite Z.lxor_spec. reflexivity.
Qed.
Lemma not64_sx32 a : not64 (sx32 a) = sx32 (Z.lnot a).
Proof.
unfold not64. apply Z.bits_inj'. intros i Hi.
rewrite testbit_mod_pow2, !testbit_sx32 by lia.
destruct (i <? 64) eqn:E64.
- rewrite Z.lnot_spec, testbit_sx32 by lia.
destruct (i <? 32) eqn:E32; [symmetry; apply Z.lnot_spec; lia|].
rewrite E64. symmetry. apply Z.lnot_spec. lia.
- destruct (i <? 32) eqn:E32; [|reflexivity].
apply Z.ltb_lt in E32. apply Z.ltb_ge in E64. lia.
Qed.
Lemma land_small_r a m : 0 <= m < 2^32 -> Z.land a m = Z.land (a mod 2^32) m.
Proof.
intros Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z_lt_le_dec i 32).
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite (testbit_high_false m 32 i) by lia. rewrite !andb_false_r. reflexivity.
Qed.
Lemma land_sx32_small a m : 0 <= m < 2^32 -> Z.land (sx32 a) m = Z.land a m.
Proof.
intros Hm. rewrite (land_small_r (sx32 a)), (land_small_r a) by lia.
rewrite sx32_mod32. reflexivity.
Qed.
Lemma land_lo32_small a m : 0 <= m < 2^32 -> Z.land (lo32 a) m = Z.land a m.
Proof. intros. unfold lo32. symmetry. apply land_small_r. lia. Qed.
Lemma lo32_land a b : lo32 (Z.land a b) = Z.land (lo32 a) (lo32 b).
Proof.
unfold lo32. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, !testbit_mod_pow2, Z.land_spec by lia.
destruct (i <? 32); reflexivity.
Qed.
Lemma lo32_lor a b : lo32 (Z.lor a b) = Z.lor (lo32 a) (lo32 b).
Proof.
unfold lo32. apply Z.bits_inj'. intros i Hi.
rewrite Z.lor_spec, !testbit_mod_pow2, Z.lor_spec by lia.
destruct (i <? 32); reflexivity.
Qed.
Lemma lo32_lxor a b : lo32 (Z.lxor a b) = Z.lxor (lo32 a) (lo32 b).
Proof.
unfold lo32. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, !testbit_mod_pow2, Z.lxor_spec by lia.
destruct (i <? 32); reflexivity.
Qed.
Lemma land_range a b n : 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
intros Ha Hb. assert (0 <= n) by (destruct (Z_le_gt_dec 0 n); [lia|rewrite Z.pow_neg_r in Ha; lia]).
split; [apply Z.land_nonneg; lia|].
apply lt_pow2_of_testbit; [apply Z.land_nonneg; lia|lia|].
intros i Hi. rewrite Z.land_spec, (testbit_high_false a n i) by lia. reflexivity.
Qed.
Lemma land_range_r a b n : 0 <= a -> 0 <= b < 2^n -> 0 <= Z.land a b < 2^n.
Proof. intros. rewrite Z.land_comm. apply land_range; lia. Qed.
Lemma lor_range a b n : 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
intros Ha Hb. assert (0 <= n) by (destruct (Z_le_gt_dec 0 n); [lia|rewrite Z.pow_neg_r in Ha; lia]).
split; [apply Z.lor_nonneg; lia|].
apply lt_pow2_of_testbit; [apply Z.lor_nonneg; lia|lia|].
intros i Hi. rewrite Z.lor_spec, (testbit_high_false a n i), (testbit_high_false b n i) by lia. reflexivity.
Qed.
Lemma lxor_range a b n : 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lxor a b < 2^n.
Proof.
intros Ha Hb. assert (0 <= n) by (destruct (Z_le_gt_dec 0 n); [lia|rewrite Z.pow_neg_r in Ha; lia]).
split; [apply Z.lxor_nonneg; lia|].
apply lt_pow2_of_testbit; [apply Z.lxor_nonneg; lia|lia|].
intros i Hi. rewrite Z.lxor_spec, (testbit_high_false a n i), (testbit_high_false b n i) by lia. reflexivity.
Qed.
Lemma zland_le_l a b : 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
intros Ha Hb.
pose proof (Z.lor_ldiff_and a b) as E.
assert (D : Z.land (Z.ldiff a b) (Z.land a b) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
rewrite <- Z.lxor_lor in E by exact D. rewrite <- Z.add_nocarry_lxor in E by exact D.
pose proof (proj2 (Z.ldiff_nonneg a b) (or_introl Ha)). pose proof (Z.land_nonneg a b). lia.
Qed.
Lemma zland_le_r a b : 0 <= a -> 0 <= b -> Z.land a b <= b.
Proof. intros. rewrite Z.land_comm. apply zland_le_l; lia. Qed.
Lemma shiftr_range a k n : 0 <= a < 2^n -> 0 <= k -> 0 <= Z.shiftr a k < 2^n.
Proof.
intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia.
assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma land_field a n m : 0 <= n -> 0 <= m ->
Z.land a (2^n * Z.ones m) = 2^n * ((Z.shiftr a n) mod 2^m).
Proof.
intros Hn Hm. apply Z.bits_inj'. intros i Hi.
rewrite (Z.mul_comm (2^n) (Z.ones m)), (Z.mul_comm (2^n)).
rewrite Z.land_spec, Z.mul_pow2_bits, Z.mul_pow2_bits by lia.
destruct (Z_lt_le_dec i n).
- rewrite (Z.testbit_neg_r (Z.ones m)), (Z.testbit_neg_r (Z.shiftr a n mod 2^m)) by lia. apply andb_false_r.
- rewrite Z.testbit_ones, testbit_mod_pow2 by lia.
destruct (i - n <? m) eqn:E.
+ rewrite Z.shiftr_spec by lia. replace (i - n + n) with i by lia.
replace (0 <=? i - n) with true by (symmetry; apply Z.leb_le; lia). cbn. apply andb_true_r.
+ rewrite !andb_false_r. reflexivity.
Qed.
Lemma land_neg_pow2 a n : 0 <= n -> Z.land a (- 2^n) = a - a mod 2^n.
Proof.
intros Hn. replace (- 2^n) with (Z.lnot (Z.ones n)) by (unfold Z.lnot, Z.ones; rewrite Z.shiftl_1_l; lia).
rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (Z.div_mod a (2^n)) at 2 by lia. lia.
Qed.
Lemma land_neg_pow2_u64 a n : 0 <= a < 2^64 -> 0 <= n <= 64 ->
Z.land a (2^64 - 2^n) = a - a mod 2^n.
Proof.
intros Ha Hn. rewrite <- land_neg_pow2 by lia.
apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z_lt_le_dec i 64).
- f_equal. replace (2^64 - 2^n) with ((- 2^n) mod 2^64).
+ apply Z.mod_pow2_bits_low. lia.
+ replace (- 2^n) with ((2^64 - 2^n) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia.
apply Z.mod_small. split; [|lia]. assert (2^n <= 2^64) by (apply Z.pow_le_mono_r; lia). lia.
- rewrite (testbit_high_false a 64 i) by lia. reflexivity.
Qed.
Lemma lowbit_ctz32 m : 0 < m ->
lowbit m = 2 ^ ctz32 m /\ 0 <= ctz32 m /\ Z.testbit m (ctz32 m) = true /\
(forall j, 0 <= j < ctz32 m -> Z.testbit m j = false).
Proof.
intros Hm. destruct (lowbit_spec m Hm) as (k & Hk & Hl & Hb & Hlow).
unfold ctz32. rewrite Hl. unfold bit. rewrite Z.log2_pow2 by lia. auto.
Qed.
Lemma lowbit_le m : 0 < m -> 0 < lowbit m <= m.
Proof.
intros Hm. destruct (lowbit_ctz32 m Hm) as (Hl & Hk & Hb & _). rewrite Hl.
split; [apply Z.pow_pos_nonneg; lia|].
destruct (Z_le_gt_dec (2 ^ ctz32 m) m); [lia|]. exfalso.
rewrite (testbit_high_false m (ctz32 m) (ctz32 m)) in Hb by lia. discriminate.
Qed.
Lemma lowbit_0 : lowbit 0 = 0.
Proof. reflexivity. Qed.
Lemma lowbit_nonneg m : 0 <= m -> 0 <= lowbit m <= m.
Proof.
intros Hm. destruct (Z.eq_dec m 0) as [->|]; [rewrite lowbit_0; lia|].
pose proof (lowbit_le m ltac:(lia)). lia.
Qed.
Lemma ctz32_lt m n : 0 < m < 2^n -> 0 <= n -> 0 <= ctz32 m < n.
Proof.
intros Hm Hn. destruct (lowbit_ctz32 m ltac:(lia)) as (Hl & Hk & Hb & _).
split; [lia|]. destruct (Z_lt_le_dec (ctz32 m) n); [lia|]. exfalso.
rewrite (testbit_high_false m n (ctz32 m)) in Hb by lia. discriminate.
Qed.
Lemma lowbit_pow2 k : 0 <= k -> lowbit (2^k) = 2^k.
Proof.
intros Hk. destruct (lowbit_ctz32 (2^k) ltac:(apply Z.pow_pos_nonneg; lia)) as (Hl & Hc & Hb & _).
rewrite Z.pow2_bits_eqb in Hb by lia. apply Z.eqb_eq in Hb. rewrite Hl, <- Hb. reflexivity.
Qed.
Lemma lowbit_lowbit m : 0 < m -> lowbit (lowbit m) = lowbit m.
Proof.
intros Hm. destruct (lowbit_ctz32 m Hm) as (Hl & Hk & _). rewrite Hl. apply lowbit_pow2. lia.
Qed.
Lemma sub_lowbit_ldiff m : 0 < m -> m - lowbit m = Z.ldiff m (lowbit m).
Proof.
intros Hm. destruct (lowbit_ctz32 m Hm) as (Hl & Hk & Hb & _). rewrite Hl.
change (2 ^ ctz32 m) with (bit (ctz32 m)). apply sub_bit_ldiff; [lia|]. exact Hb.
Qed.
Lemma sub_lowbit_testbit m j : 0 < m -> 0 <= j ->
Z.testbit (m - lowbit m) j = Z.testbit m j && negb (j =? ctz32 m).
Proof.
intros Hm Hj. rewrite sub_lowbit_ldiff by lia. rewrite Z.ldiff_spec.
destruct (lowbit_ctz32 m Hm) as (Hl & Hk & _). rewrite Hl, Z.pow2_bits_eqb by lia.
rewrite Z.eqb_sym. reflexivity.
Qed.
Lemma sub_lowbit_range m : 0 < m < 2^32 -> 0 <= m - lowbit m < m.
Proof. intros. pose proof (lowbit_le m ltac:(lia)). lia. Qed.
Lemma negw_and_sx32 m : Z.land (sx32 m) (negw (sx32 m)) = sx32 (lowbit m).
Proof.
rewrite negw_sx32. unfold negw. rewrite land_sx32. reflexivity.
Qed.
Lemma negw_and_u32 m : 0 <= m < 2^32 -> Z.land m (negw m) = lowbit m.
Proof.
intros Hm. unfold negw.
pose proof (lowbit_nonneg m ltac:(lia)) as Hlb.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_sx32 by lia.
destruct (i <? 32) eqn:E.
- unfold lowbit. rewrite Z.land_spec. reflexivity.
- apply Z.ltb_ge in E. rewrite (testbit_high_false m 32 i), (testbit_high_false (lowbit m) 32 i) by lia.
reflexivity.
Qed.
Lemma sx32_lowbit_nonzero m : 0 < m < 2^32 -> sx32 (lowbit m) <> 0.
Proof. intros Hm. pose proof (lowbit_le m ltac:(lia)). apply sx32_nonzero_u32. lia. Qed.
Lemma sx32_lowbit_zero_iff m : 0 <= m < 2^32 -> (sx32 (lowbit m) = 0 <-> m = 0).
Proof.
intros Hm. split.
- intros E. destruct (Z.eq_dec m 0) as [->|Hne]; [reflexivity|].
exfalso. apply (sx32_lowbit_nonzero m); lia.
- intros ->. reflexivity.
Qed.
Lemma subw_mask_first m : 0 <= m < 2^32 ->
subw (sx32 m) (sx32 (lowbit m)) = sx32 (m - lowbit m) /\
subw m (sx32 (lowbit m)) = sx32 (m - lowbit m) /\
subw (sx32 m) (lowbit m) = sx32 (m - lowbit m) /\
lo32 (sx32 (m - lowbit m)) = m - lowbit m.
Proof.
intros Hm. rewrite !subw_sx32_l, !subw_sx32_r. unfold subw.
repeat split. rewrite lo32_sx32. apply lo32_small. pose proof (lowbit_nonneg m). lia.
Qed.
Lemma sllw_1 i : 0 <= i -> sllw 1 i = sx32 (2 ^ (i mod 32)).
Proof. intros. unfold sllw. rewrite Z.shiftl_1_l. reflexivity. Qed.
Lemma sllw_2 x : 0 <= x -> sllw 2 x = sx32 (2 ^ (x mod 32 + 1)).
Proof.
intros. unfold sllw. pose proof (Z.mod_pos_bound x 32 ltac:(lia)).
rewrite Z.shiftl_mul_pow2, Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma land_31_mod x : Z.land x 31 = x mod 32.
Proof. change 31 with (Z.ones 5). apply Z.land_ones. lia. Qed.
Lemma land_sx32_bit m i : 0 <= i < 32 -> 0 <= m ->
Z.land (sx32 m) (sx32 (2^i)) = sx32 (Z.land m (2^i)) /\
(sx32 (Z.land m (2^i)) = 0 <-> Z.testbit m i = false).
Proof.
intros Hi Hm. rewrite land_sx32. split; [reflexivity|].
assert (Hr : 0 <= Z.land m (2^i) < 2^32).
{ apply land_range_r; [lia|]. split; [apply Z.pow_nonneg; lia|apply Z.pow_lt_mono_r; lia]. }
rewrite sx32_zero_iff_u32 by lia. split.
- intros E. apply (f_equal (fun z => Z.testbit z i)) in E.
rewrite Z.land_spec, Z.pow2_bits_true, Z.bits_0, andb_true_r in E by lia. exact E.
- intros Hb. apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec i j); [subst; rewrite Hb; reflexivity|apply andb_false_r].
Qed.
Lemma addiw_sllw2_m1 x : 0 <= x ->
addw (sllw 2 x) (-1) = sx32 (ones (x mod 32)) /\
addw (sllw 2 x) (2^64 - 1) = sx32 (ones (x mod 32)).
Proof.
intros Hx. rewrite sllw_2 by lia. rewrite !addw_sx32_l. unfold addw, ones.
split; [reflexivity|]. apply sx32_congr.
replace (2 ^ (x mod 32 + 1) + (2^64 - 1)) with ((2 ^ (x mod 32 + 1) - 1) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma addi_sllw2_m1 x : 0 <= x ->
lo32 (add64 (sllw 2 x) (2^64 - 1)) = ones (x mod 32) /\
(x mod 32 < 30 -> add64 (sllw 2 x) (2^64 - 1) = ones (x mod 32)).
Proof.
intros Hx. rewrite sllw_2 by lia.
pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as Hr. set (j := x mod 32) in *.
assert (Hp : 2 <= 2^(j+1) <= 2^32).
{ split. - replace 2 with (2^1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia.
- apply Z.pow_le_mono_r; lia. }
split.
- rewrite lo32_add64. rewrite (lo32_congr_add _ (2^(j+1)) _ (-1));
[|apply lo32_sx32|reflexivity].
unfold ones. apply lo32_small. lia.
- intros Hj. assert (2^(j+1) <= 2^30) by (apply Z.pow_le_mono_r; lia).
rewrite sx32_small by lia. rewrite add64_neg_imm by lia. reflexivity.
Qed.
Lemma lo32_ones_small j : 0 <= j < 32 -> lo32 (ones j) = ones j.
Proof.
intros. unfold ones. assert (2 <= 2^(j+1) <= 2^32).
{ split; [replace 2 with (2^1) at 1 by reflexivity|]; apply Z.pow_le_mono_r; lia. }
apply lo32_small. lia.
Qed.
Lemma land_mask_ones_lo32 f x : 0 <= f < 2^32 -> 0 <= x ->
lo32 (Z.land (sx32 f) (add64 (sllw 2 x) (2^64 - 1))) = Z.land f (ones (x mod 32)).
Proof.
intros Hf Hx. destruct (addi_sllw2_m1 x Hx) as (H1 & _).
pose proof (Z.mod_pos_bound x 32 ltac:(lia)).
rewrite lo32_land, H1, lo32_sx32, lo32_small by lia. reflexivity.
Qed.
Lemma land_negw_sllw2_lo32 f x : 0 <= f < 2^32 -> 0 <= x ->
lo32 (Z.land (sx32 f) (negw (sllw 2 x))) = f - Z.land f (ones (x mod 32)).
Proof.
intros Hf Hx. rewrite sllw_2, negw_sx32 by lia. unfold negw. rewrite land_sx32, lo32_sx32.
pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as Hr. set (j := x mod 32) in *.
rewrite land_neg_pow2 by lia.
unfold ones. change (2^(j+1) - 1) with (Z.pred (2^(j+1))). rewrite <- Z.ones_equiv, Z.land_ones by lia.
pose proof (Z.mod_pos_bound f (2^(j+1)) ltac:(apply Z.pow_pos_nonneg; lia)).
pose proof (Z.mod_le f (2^(j+1)) ltac:(lia) ltac:(apply Z.pow_pos_nonneg; lia)).
apply lo32_small. lia.
Qed.
Lemma install_freed_lo32 avail last : 0 <= last < 32 -> 0 <= avail <= ones last ->
lo32 (add64 (sllw 2 last) (not64 (sx32 avail))) = ones last - avail.
Proof.
intros Hl Ha. rewrite lo32_add64. rewrite sllw_2, not64_sx32 by lia.
rewrite (Z.mod_small last 32) by lia.
rewrite (lo32_congr_add _ (2^(last+1)) _ (Z.lnot avail));
[|apply lo32_sx32|apply lo32_sx32].
unfold Z.lnot, lo32, ones in *.
assert (2^(last+1) <= 2^32) by (apply Z.pow_le_mono_r; lia).
replace (2^(last+1) + Z.pred (- avail)) with (2^(last+1) - 1 - avail) by lia.
apply Z.mod_small. lia.
Qed.
Lemma install_avail_lo32 aidx : 0 <= aidx < 32 ->
lo32 (add64 (sllw 2 aidx) (2^64 - 1)) = ones aidx /\
lo32 (add64 (sx32 (ones aidx)) (2^64 - 1)) = ones aidx - 1.
Proof.
intros Ha. destruct (addi_sllw2_m1 aidx ltac:(lia)) as [H1 _].
rewrite (Z.mod_small aidx 32) in H1 by lia. split; [exact H1|].
rewrite lo32_add64. rewrite (lo32_congr_add _ (ones aidx) _ (-1));
[|apply lo32_sx32|reflexivity].
unfold ones, lo32. assert (2 <= 2^(aidx+1) <= 2^32).
{ split; [replace 2 with (2^1) at 1 by reflexivity|]; apply Z.pow_le_mono_r; lia. }
apply Z.mod_small. lia.
Qed.
Lemma lor_masks avail freed : Z.lor (sx32 avail) (sx32 freed) = sx32 (Z.lor avail freed).
Proof. apply lor_sx32. Qed.
Lemma addw_masks a b : addw (sx32 a) (sx32 b) = sx32 (a + b).
Proof. rewrite addw_sx32_l, addw_sx32_r. reflexivity. Qed.
Lemma lo32_lor_sx32 a b : 0 <= a < 2^32 -> 0 <= b < 2^32 -> lo32 (Z.lor (sx32 a) (sx32 b)) = Z.lor a b.
Proof. intros. rewrite lor_sx32, lo32_sx32. apply lo32_small. apply lor_range; lia. Qed.
Lemma lo32_addw a b : lo32 (addw a b) = (a + b) mod 2^32.
Proof. unfold addw. rewrite lo32_sx32. reflexivity. Qed.
Lemma mmap_counter_step c : 0 <= c < 2^32 ->
lo32 (add64 (sx32 c) 1) = Z.land (c + 1) (2^32 - 1).
Proof.
intros Hc. rewrite lo32_add64. rewrite (lo32_congr_add _ c _ 1); [|apply lo32_sx32|reflexivity].
change (2^32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma land_255_sx32 c : Z.land (sx32 c) 255 = Z.land c 255.
Proof. apply land_sx32_small. lia. Qed.
Definition DEBRUIJN : list Z :=
[0; 1; 28; 2; 29; 14; 24; 3; 30; 22; 20; 15; 25; 17; 4; 8;
31; 27; 13; 23; 21; 19; 16; 7; 26; 12; 18; 6; 11; 5; 10; 9].
Definition DBJ_MUL : Z := 0x077cb531.
Definition dbj_idx (x : Z) : Z := Z.shiftr ((x * DBJ_MUL) mod 2^32) 27.
Lemma dbj_idx_range x : 0 <= dbj_idx x < 32.
Proof.
unfold dbj_idx. pose proof (Z.mod_pos_bound (x * DBJ_MUL) (2^32) ltac:(lia)).
rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. change (2^27 * 32) with (2^32). lia.
Qed.
Lemma dbj_table_ok :
forallb (fun k => znth (dbj_idx (2^k)) DEBRUIJN =? k) (zseq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dbj_pow2 k : 0 <= k < 32 -> znth (dbj_idx (2^k)) DEBRUIJN = k.
Proof.
intros Hk. pose proof dbj_table_ok as T. rewrite forallb_forall in T.
specialize (T k (proj2 (In_zseq 0 32 k) ltac:(lia))). apply Z.eqb_eq in T. exact T.
Qed.
Lemma srlw_mul64_dbj a : 0 <= a -> srlw (mul64 a DBJ_MUL) 27 = dbj_idx (lo32 a).
Proof.
intros Ha. unfold srlw, mul64, dbj_idx, lo32. change (27 mod 32) with 27.
rewrite mod64_mod32, <- Zmult_mod_idemp_l.
pose proof (dbj_idx_range (a mod 2^32)) as Hr. unfold dbj_idx in Hr.
apply sx32_small. lia.
Qed.
Lemma lo32_sx32_lowbit m : 0 <= m < 2^32 -> lo32 (sx32 (lowbit m)) = lowbit m.
Proof. intros. rewrite lo32_sx32. apply lo32_small. pose proof (lowbit_nonneg m). lia. Qed.
Theorem dbj_ctz32 m : 0 < m < 2^32 ->
let idx := srlw (mul64 (sx32 (lowbit m)) DBJ_MUL) 27 in
0 <= idx < 32 /\ znth idx DEBRUIJN = ctz32 m.
Proof.
intros Hm. cbn zeta. rewrite srlw_mul64_dbj by (apply sx32_range).
rewrite lo32_sx32_lowbit by lia. split; [apply dbj_idx_range|].
destruct (lowbit_ctz32 m ltac:(lia)) as (Hl & Hk & _).
pose proof (ctz32_lt m 32 ltac:(lia) ltac:(lia)).
rewrite Hl. apply dbj_pow2. lia.
Qed.
Theorem dbj_ctz32_u32 m : 0 < m < 2^32 ->
let idx := srlw (mul64 (lowbit m) DBJ_MUL) 27 in
0 <= idx < 32 /\ znth idx DEBRUIJN = ctz32 m.
Proof.
intros Hm. cbn zeta. pose proof (lowbit_le m ltac:(lia)).
rewrite srlw_mul64_dbj, lo32_small by lia. split; [apply dbj_idx_range|].
destruct (lowbit_ctz32 m ltac:(lia)) as (Hl & Hk & _).
pose proof (ctz32_lt m 32 ltac:(lia) ltac:(lia)).
rewrite Hl. apply dbj_pow2. lia.
Qed.
Theorem take_block m : 0 < m < 2^32 ->
let a  := sx32 m in
let first := Z.land a (negw a) in
let rest  := subw a first in
let idx   := srlw (mul64 (Z.land a (negw a)) DBJ_MUL) 27 in
first = sx32 (lowbit m) /\ first <> 0 /\
lo32 rest = m - lowbit m /\ rest = sx32 (m - lowbit m) /\
0 <= idx < 32 /\ znth idx DEBRUIJN = ctz32 m /\
lowbit m = 2 ^ ctz32 m /\ 0 <= ctz32 m < 32 /\ Z.testbit m (ctz32 m) = true /\
0 <= m - lowbit m < m.
Proof.
intros Hm. cbn zeta. rewrite negw_and_sx32.
destruct (subw_mask_first m ltac:(lia)) as (S1 & _ & _ & S4).
destruct (dbj_ctz32 m Hm) as [I1 I2].
destruct (lowbit_ctz32 m ltac:(lia)) as (L1 & L2 & L3 & _).
pose proof (ctz32_lt m 32 ltac:(lia) ltac:(lia)).
pose proof (sub_lowbit_range m Hm).
repeat split; auto; try lia.
- apply sx32_lowbit_nonzero. lia.
- rewrite S1. exact S4.
Qed.
Definition stc_core (k : Z) : Z :=
let a0 := add64 k 1 in
let a2 := srlw a0 2 in
let a2 := Z.lor a2 a0 in
let a0 := srlw a0 1 in
let a2 := Z.lor a2 a0 in
let a2 := srlw a2 2 in
let a0 := Z.lor a2 a0 in
let a2 := Z.shiftr a0 4 in
let a0 := Z.lor a2 a0 in
let a2 := Z.shiftr a0 8 in
let a0 := Z.lor a2 a0 in
let a2 := sll64 a0 33 in
let a2 := Z.shiftr a2 49 in
let a0 := Z.lor a2 a0 in
let a2 := add64 a0 1 in
let a0 := not64 a0 in
let a0 := Z.land a2 a0 in
let a0 := mul64 a0 DBJ_MUL in
let a0 := srlw a0 27 in
let a0 := znth a0 DEBRUIJN in
let a0 := sll64 a0 2 in
let a0 := Z.lxor a0 124 in
let a1 := sub64 121 a0 in
let a2 := znth a1 size_classes in
let a2 := if k <? a2 then 120 else 122 in
let a2 := sub64 a2 a0 in
let t  := znth a2 size_classes in
let a0 := sltu k t in
let a0 := Z.lxor a0 1 in
Z.lor a2 a0.
Definition stc_malloc (n : Z) : Z :=
let a0 := add64 n 3 in
let s4 := Z.shiftr a0 4 in
if n <? 157 then s4
else stc_core s4.
Definition stc_group (sz : Z) : Z :=
let a1 := add64 sz 12 in
let a4 := Z.shiftr sz 4 in
if a1 <? 157 then a4
else stc_core a4.
Definition stc_trace (k : Z) : Z * Z * Z * Z :=
let a0 := add64 k 1 in let a2 := srlw a0 2 in let a2 := Z.lor a2 a0 in
let a0 := srlw a0 1 in let a2 := Z.lor a2 a0 in let a2 := srlw a2 2 in
let a0 := Z.lor a2 a0 in let a2 := Z.shiftr a0 4 in let a0 := Z.lor a2 a0 in
let a2 := Z.shiftr a0 8 in let a0 := Z.lor a2 a0 in let a2 := sll64 a0 33 in
let a2 := Z.shiftr a2 49 in let a0 := Z.lor a2 a0 in let a2 := add64 a0 1 in
let a0 := not64 a0 in let a0 := Z.land a2 a0 in let a0 := mul64 a0 DBJ_MUL in
let idx1 := srlw a0 27 in
let c4 := Z.lxor (sll64 (znth idx1 DEBRUIJN) 2) 124 in
let idx2 := sub64 121 c4 in
let idx3 := sub64 (if k <? znth idx2 size_classes then 120 else 122) c4 in
(idx1, c4, idx2, idx3).
Definition stc_idx1 (k : Z) : Z := let '(i1, _, _, _) := stc_trace k in i1.
Definition stc_c4 (k : Z) : Z := let '(_, c, _, _) := stc_trace k in c.
Definition stc_idx2 (k : Z) : Z := let '(_, _, i2, _) := stc_trace k in i2.
Definition stc_idx3 (k : Z) : Z := let '(_, _, _, i3) := stc_trace k in i3.
Definition stc_check (k : Z) : bool :=
let c := stc_core k in
let '(i1, c4, i2, i3) := stc_trace k in
(c =? class_of_units k) && (0 <=? i1) && (i1 <? 32) && (c4 =? 4 * clz32 (k + 1)) &&
(0 <=? i2) && (i2 <? 48) && (0 <=? i3) && (i3 <? 48) && (0 <=? c) && (c <? 48).
Lemma stc_check_spec k : stc_check k = true ->
stc_core k = class_of_units k /\
0 <= stc_idx1 k < 32 /\ stc_c4 k = 4 * clz32 (k + 1) /\
0 <= stc_idx2 k < 48 /\ 0 <= stc_idx3 k < 48 /\ 0 <= stc_core k < 48.
Proof.
unfold stc_check, stc_idx1, stc_c4, stc_idx2, stc_idx3.
destruct (stc_trace k) as [[[i1 c4] i2] i3]. intros T.
repeat (apply andb_prop in T as [T ?H]).
repeat match goal with
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
end.
repeat split; assumption.
Qed.
Lemma stc_core_table : forallb stc_check (zseq 10 8181) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stc_core_ok k : 10 <= k <= 8190 ->
stc_core k = class_of_units k /\
0 <= stc_idx1 k < 32 /\ stc_c4 k = 4 * clz32 (k + 1) /\
0 <= stc_idx2 k < 48 /\ 0 <= stc_idx3 k < 48 /\ 0 <= stc_core k < 48.
Proof.
intros Hk. pose proof stc_core_table as T. rewrite forallb_forall in T.
apply stc_check_spec. apply T. apply In_zseq. lia.
Qed.
Theorem stc_malloc_ok n : 0 <= n < MMAP_THRESHOLD -> stc_malloc n = size_to_class n.
Proof.
intros Hn. unfold stc_malloc, size_to_class, MMAP_THRESHOLD, IB in *.
rewrite add64_small by lia. replace (n + 4 - 1) with (n + 3) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
destruct (n <? 157) eqn:E.
- apply Z.ltb_lt in E. unfold class_of_units.
replace ((n + 3) / 16 <? 10) with true; [reflexivity|].
symmetry. apply Z.ltb_lt. apply Z.div_lt_upper_bound; lia.
- apply Z.ltb_ge in E. destruct (stc_core_ok ((n + 3) / 16)) as [H _]; [|exact H].
assert ((n + 3) / 16 < 8191) by (apply Z.div_lt_upper_bound; lia).
split; [apply Z.div_le_lower_bound; lia | lia].
Qed.
Theorem stc_malloc_range n : 0 <= n < MMAP_THRESHOLD -> 0 <= stc_malloc n < 48.
Proof.
intros Hn. rewrite stc_malloc_ok by lia. apply size_to_class_range. lia.
Qed.
Theorem stc_group_ok sz : 0 <= sz <= 131036 -> sz mod 16 = 0 ->
stc_group sz = size_to_class (sz + 12).
Proof.
intros Hs Hm. unfold stc_group, size_to_class, IB.
rewrite add64_small by lia. replace (sz + 12 + 4 - 1) with (sz + 15) by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^4) with 16.
pose proof (Z.div_mod sz 16 ltac:(lia)) as D. rewrite Hm in D.
assert (E16 : (sz + 15) / 16 = sz / 16).
{ replace (sz + 15) with ((sz / 16) * 16 + 15) by lia. rewrite Z.div_add_l by lia.
rewrite (Z.div_small 15 16) by lia. lia. }
rewrite E16.
destruct (sz + 12 <? 157) eqn:E.
- apply Z.ltb_lt in E. unfold class_of_units.
replace (sz / 16 <? 10) with true; [reflexivity|].
symmetry. apply Z.ltb_lt. apply Z.div_lt_upper_bound; lia.
- apply Z.ltb_ge in E. destruct (stc_core_ok (sz / 16)) as [H _]; [|exact H].
assert (sz / 16 < 8191) by (apply Z.div_lt_upper_bound; lia).
split; [apply Z.div_le_lower_bound; lia | lia].
Qed.
Lemma sextw_class c : 0 <= c < 48 -> sx32 c = c.
Proof. intros. apply sx32_small. lia. Qed.
