(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record venv : Type := VEnv {
  vv  : nat -> Z;
  vf1 : nat -> Z -> Z;
  vf2 : nat -> Z -> Z -> Z
}.

Definition szwrap (k a : Z) : Z := (a + 2 ^ (k - 1)) mod 2 ^ k - 2 ^ (k - 1).


Definition bounds : Type := list (nat * Z).

Fixpoint blookup (l : bounds) (n : nat) : option Z :=
  match l with
  | [] => None
  | (m, b) :: rest => if Nat.eqb m n then Some b else blookup rest n
  end.

Definition vars_ok (E : venv) (vb : bounds) : Prop :=
  forall n b, blookup vb n = Some b -> 0 <= vv E n < b.

Definition funs_ok (E : venv) (fb : bounds) : Prop :=
  forall f b x, blookup fb f = Some b -> 0 <= vf1 E f x < b.

Definition pow2_above (b : Z) : Z := 2 ^ (Z.log2_up b).

Lemma pow2_above_ge : forall b, 1 <= b -> b <= pow2_above b.
Proof.
  intros b Hb. unfold pow2_above.
  destruct (Z.eq_dec b 1) as [->|Hne]; [cbn; lia|].
  apply Z.log2_up_spec. lia.
Qed.

Definition omin (x y : option Z) : option Z :=
  match x, y with
  | Some a, Some b => Some (Z.min a b)
  | Some a, None => Some a
  | None, Some b => Some b
  | None, None => None
  end.

Lemma land_upper : forall a b, 0 <= a -> 0 <= Z.land a b <= a.
Proof.
  intros a b Ha.
  assert (H0 : 0 <= Z.land a b) by (apply Z.land_nonneg; left; exact Ha).
  split; [exact H0|].
  assert (E : a = Z.lor (Z.land a b) (Z.ldiff a b)).
  { apply Z.bits_inj'. intros i Hi.
    rewrite Z.lor_spec, Z.land_spec, Z.ldiff_spec.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  assert (Hd : 0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha).
  assert (Hdis : Z.land (Z.land a b) (Z.ldiff a b) = 0).
  { apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ Hdis) as Hx.
  rewrite Z.lxor_lor in Hx by exact Hdis.
  lia.
Qed.

Lemma lor_lxor_bound : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= n ->
  0 <= Z.lor a b < 2 ^ n /\ 0 <= Z.lxor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb Hn.
  assert (Hta : forall k, n <= k -> Z.testbit a k = false).
  { intros k Hk. destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with n; [|lia]. apply Z.log2_lt_pow2; lia. }
  assert (Htb : forall k, n <= k -> Z.testbit b k = false).
  { intros k Hk. destruct (Z.eq_dec b 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with n; [|lia]. apply Z.log2_lt_pow2; lia. }
  assert (Hor0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  assert (Hxor0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; split; try assumption.
  - destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hnz]; [lia|].
    destruct (Z_lt_le_dec (Z.lor a b) (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
    assert (Ht : Z.testbit (Z.lor a b) (Z.log2 (Z.lor a b)) = true)
      by (apply Z.bit_log2; lia).
    assert (Hl : n <= Z.log2 (Z.lor a b)).
    { apply Z.log2_le_pow2 in Hge; lia. }
    rewrite Z.lor_spec, Hta, Htb in Ht by lia. discriminate.
  - destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
    destruct (Z_lt_le_dec (Z.lxor a b) (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
    assert (Ht : Z.testbit (Z.lxor a b) (Z.log2 (Z.lxor a b)) = true)
      by (apply Z.bit_log2; lia).
    assert (Hl : n <= Z.log2 (Z.lxor a b)).
    { apply Z.log2_le_pow2 in Hge; lia. }
    rewrite Z.lxor_spec, Hta, Htb in Ht by lia. discriminate.
Qed.

Lemma szwrap_range : forall k a, 0 < k -> - 2 ^ (k - 1) <= szwrap k a < 2 ^ (k - 1).
Proof.
  intros k a Hk. unfold szwrap.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ k = 2 * 2 ^ (k - 1)).
  { replace k with (k - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
  pose proof (Z.mod_pos_bound (a + 2 ^ (k - 1)) (2 ^ k) ltac:(lia)). lia.
Qed.

Lemma szwrap_small : forall k a, 0 < k -> - 2 ^ (k - 1) <= a < 2 ^ (k - 1) -> szwrap k a = a.
Proof.
  intros k a Hk Ha. unfold szwrap.
  assert (2 ^ k = 2 * 2 ^ (k - 1)).
  { replace k with (k - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma szwrap_mod : forall k a, 0 < k -> szwrap k (a mod 2 ^ k) = szwrap k a.
Proof.
  intros k a Hk. unfold szwrap.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma szwrap_eqm : forall k a, 0 < k -> (szwrap k a) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros k a Hk. unfold szwrap.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Zminus_mod_idemp_l.
  replace (a + 2 ^ (k - 1) - 2 ^ (k - 1)) with a by lia. reflexivity.
Qed.

Lemma szwrap_idem : forall j k a, 0 < j -> j <= k -> szwrap k (szwrap j a) = szwrap j a.
Proof.
  intros j k a Hj Hjk. apply szwrap_small; [lia|].
  pose proof (szwrap_range j a Hj).
  assert (2 ^ (j - 1) <= 2 ^ (k - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma mod_mod_le : forall a j k, 0 <= j <= k -> (a mod 2 ^ k) mod 2 ^ j = a mod 2 ^ j.
Proof.
  intros a j k Hjk. apply Z.mod_mod_divide.
  exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma mod_mod_ge : forall a j k, 0 <= j <= k -> (a mod 2 ^ j) mod 2 ^ k = a mod 2 ^ j.
Proof.
  intros a j k Hjk. apply Z.mod_small.
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound a (2 ^ j) ltac:(lia)).
  assert (2 ^ j <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma testbit_mod_pow2 : forall a n i, 0 <= n -> 0 <= i ->
  Z.testbit (a mod 2 ^ n) i = if i <? n then Z.testbit a i else false.
Proof.
  intros a n i Hn Hi. destruct (Z.ltb_spec i n).
  - apply Z.mod_pow2_bits_low. lia.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma land_mod : forall a b n, 0 <= n ->
  (Z.land a b) mod 2 ^ n = Z.land (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !testbit_mod_pow2, Z.land_spec by lia.
  destruct (i <? n); reflexivity.
Qed.

Lemma lor_mod : forall a b n, 0 <= n ->
  (Z.lor a b) mod 2 ^ n = Z.lor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, !testbit_mod_pow2, Z.lor_spec by lia.
  destruct (i <? n); reflexivity.
Qed.

Lemma lxor_mod : forall a b n, 0 <= n ->
  (Z.lxor a b) mod 2 ^ n = Z.lxor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, !testbit_mod_pow2, Z.lxor_spec by lia.
  destruct (i <? n); reflexivity.
Qed.

Lemma mod64_mod64_64 : forall b, (b mod 2 ^ 64) mod 64 = b mod 64.
Proof.
  intro b. apply (Z.mod_mod_divide b (2 ^ 64) 64). exists (2 ^ 58). reflexivity.
Qed.

Lemma mod32_mod64_32 : forall b, (b mod 2 ^ 64) mod 32 = b mod 32.
Proof.
  intro b. apply (Z.mod_mod_divide b (2 ^ 64) 32). exists (2 ^ 59). reflexivity.
Qed.



Section Smart.
Variable vb : bounds.
Variable fb : bounds.

Definition mask_width (m : Z) : option Z :=
  if (0 <=? m) && (Z.eqb (2 ^ (Z.log2 (m + 1))) (m + 1)) then Some (Z.log2 (m + 1)) else None.


Context (E : venv).
Context (Hv : vars_ok E vb).
Context (Hf : funs_ok E fb).

Lemma eqmod_le : forall x y j k, 0 <= k <= j ->
  x mod 2 ^ j = y mod 2 ^ j -> x mod 2 ^ k = y mod 2 ^ k.
Proof.
  intros x y j k Hk H.
  rewrite <- (mod_mod_le x k j), <- (mod_mod_le y k j) by lia. rewrite H. reflexivity.
Qed.

Lemma szwrap_of_mod : forall k a b, 0 < k -> a mod 2 ^ k = b mod 2 ^ k -> szwrap k a = szwrap k b.
Proof.
  intros k a b Hk H. rewrite <- (szwrap_mod k a), <- (szwrap_mod k b) by lia. rewrite H. reflexivity.
Qed.

Lemma mask_width_sound : forall m k, mask_width m = Some k -> 0 <= k /\ m = 2 ^ k - 1.
Proof.
  intros m k H. unfold mask_width in H.
  destruct (Z.leb_spec 0 m); cbn [andb] in H; [|discriminate].
  destruct (Z.eqb_spec (2 ^ Z.log2 (m + 1)) (m + 1)); [|discriminate].
  injection H as <-. split; [apply Z.log2_nonneg | lia].
Qed.

Lemma land_mask : forall a k, 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof.
  intros a k Hk. replace (2 ^ k - 1) with (Z.ones k).
  - apply Z.land_ones. exact Hk.
  - unfold Z.ones. rewrite Z.shiftl_1_l. lia.
Qed.

Lemma shl_mod_shr : forall a j k, 0 <= j <= k -> k <= 64 ->
  (a * 2 ^ j) mod 2 ^ 64 / 2 ^ k = (a mod 2 ^ (64 - j)) / 2 ^ (k - j).
Proof.
  intros a j k Hjk Hk.
  replace (2 ^ 64) with (2 ^ (64 - j) * 2 ^ j)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by (try apply Z.pow_nonzero; lia).
  replace (2 ^ k) with (2 ^ j * 2 ^ (k - j))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonneg; lia).
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma shl_lit_div : forall x z j k, 0 <= j <= k -> z mod 2 ^ j = 0 ->
  (x * 2 ^ j + z) / 2 ^ k = (x + z / 2 ^ j) / 2 ^ (k - j).
Proof.
  intros x z j k Hjk Hz.
  assert (Hc : z = z / 2 ^ j * 2 ^ j).
  { pose proof (Z.div_mod z (2 ^ j) ltac:(apply Z.pow_nonzero; lia)). lia. }
  rewrite Hc at 1. rewrite <- Z.mul_add_distr_r.
  replace (2 ^ k) with (2 ^ j * 2 ^ (k - j)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonzero; lia).
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma shl_lit_mod_shr : forall x z j k, 0 <= j <= k -> k <= 64 -> z mod 2 ^ j = 0 ->
  (x * 2 ^ j + z) mod 2 ^ 64 / 2 ^ k = ((x + z / 2 ^ j) mod 2 ^ (64 - j)) / 2 ^ (k - j).
Proof.
  intros x z j k Hjk Hk Hz.
  assert (Hc : z = z / 2 ^ j * 2 ^ j).
  { pose proof (Z.div_mod z (2 ^ j) ltac:(apply Z.pow_nonzero; lia)). lia. }
  rewrite Hc at 1. rewrite <- Z.mul_add_distr_r. apply shl_mod_shr; lia.
Qed.

End Smart.


Section Sem.
Variable vb : bounds.
Variable fb : bounds.

Context (E : venv).
Context (Hv : vars_ok E vb).
Context (Hf : funs_ok E fb).

End Sem.
