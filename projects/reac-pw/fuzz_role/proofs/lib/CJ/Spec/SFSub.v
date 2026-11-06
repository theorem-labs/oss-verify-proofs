(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/Spec/FmtFpDig.v, with its numbers changed; 86 of its 232 lines of code are new or changed and 573 lines of the source are left out. *)
(* Value lemmas about the binary128 subtraction mirror f128_sub of SoftFloat.v.
   f128_sub a b is f128_add a (b with its sign bit flipped). For two negative operands of the same exponent,
   (-A) - (-B) is f128_add (-A) (+B): the signs differ, so add_main takes the subtraction path; with |A| > |B| no swap
   happens and the result carries the sign of A. The magnitude is the sign-0 computation of SoftFloatProps3
   (addsub_sub_exact), and the final rounding step is round_mirror with the sign word 2^63 (round_mirror_exact_neg
   below, the sign-1 twin of round_mirror_exact). (-A) - (-A) cancels to +0, and (-A) - (+0) returns -A unchanged.
   f128_sub_range: every branch of f128_add returns mk128 of two 64-bit words, so every result is below 2^128.
   words128: a value below 2^128 is its low word plus 2^64 times its high word. *)
From Stdlib Require Import ZArith Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.Spec Require Import SoftFloat SoftFloatProps SoftFloatProps3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

(* Flipping the sign bit of a negative packed value gives the positive value of the same fields. *)
Local Lemma neg_pack1 : forall E T, packed 1 E T ->
  mk128 (Z.lxor (hi64 (f128_pack 1 E T)) SIGN64) (lo64 (f128_pack 1 E T)) = f128_pack 0 E T.
Proof.
  intros E T PK. pose proof PK as [_ HE HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  rewrite f128_pack_hi, f128_pack_lo by assumption. rewrite sign64_eq.
  rewrite lxor_bit_set; [| lia| lia| replace ((1 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) / 2 ^ 63) with 1 by dlia; reflexivity].
  rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

(* The high word of the result: exponent field and sign bit side by side. *)
Local Lemma lor_sign_exp : forall e, 0 <= e < 2^15 -> Z.lor (e * 2^48) (2^63) = (2^15 + e) * 2^48.
Proof.
  intros e He. replace (2^63) with (1 * 2^63) by lia. rewrite (lor_low_high 1 (e * 2^48) 63) by lia. lia.
Qed.

(* The sign-1 twin of round_mirror_exact: an exact significand (three zero guard bits) packs with sign 1. *)
Local Lemma round_mirror_exact_neg : forall SHi SLo e M sg, sg = 2^63 ->
  0 <= SHi < 2^64 -> 0 <= SLo < 2^64 -> SHi * 2^64 + SLo = 8 * M -> 2^112 <= M < 2^113 -> 1 <= e <= 32766 ->
  round_mirror SHi SLo e sg = f128_pack 1 e (M - 2^112).
Proof.
  intros SHi SLo e M sg -> HSH HSL HS HM He.
  pose proof (Z.div_mod M (2^64) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound M (2^64) ltac:(lia)) as MB.
  assert (Hq : 2^48 <= M / 2^64 < 2^49) by dlia.
  set (q := M / 2^64) in *. set (r := M mod 2^64) in *. clearbody q r.
  assert (F1 : SLo mod 8 = 0) by dnia.
  assert (F2 : SLo / 8 + (SHi mod 8) * 2^61 = r) by dnia.
  assert (F3 : SHi / 8 = q) by dnia.
  unfold round_mirror.
  change 7 with (2^3 - 1). rewrite land_ones_mod by lia. change (2^3) with 8. rewrite F1.
  rewrite !shiftr_div by lia. change (2^3) with 8.
  rewrite (shl64_val SHi 61) by lia.
  replace ((SHi * 2^61) mod 2^64) with ((SHi mod 8) * 2^61) by dnia.
  rewrite (lor_low_high (SHi mod 8) (SLo / 8) 61) by dlia.
  rewrite (shl64_small e 48) by lia.
  rewrite (lor_sign_exp e) by lia.
  rewrite land_mask48, F3. replace (q mod 2^48) with (q - 2^48) by (apply Z.mod_unique with (q := 1); lia).
  rewrite (lor_high_low (2^15 + e) (q - 2^48) 48) by lia.
  change MASKLO with (2^64 - 1). rewrite land_ones_mod by lia.
  rewrite (Z.mod_small (SHi mod 8 * 2 ^ 61 + SLo / 8)) by dlia.
  change (negb (0 =? 4)) with true. change (b2z (negb (0 <? 5))) with 0. cbv iota.
  rewrite (add64_small (SHi mod 8 * 2^61 + SLo / 8) 0) by dlia. rewrite Z.add_0_r. rewrite Z.ltb_irrefl.
  change (b2z false) with 0.
  rewrite add64_small by lia.
  rewrite mk128_val by dlia. unfold f128_pack. lia.
Qed.

(* V3: the sign-1 twins of SoftFloatProps3's f128_sub_exact / f128_sub_same / f128_sub_zero_r *)
Theorem f128_sub_exact_neg : forall E T Tz L,
  packed 1 E T -> 0 <= Tz < T -> 113 <= E <= 32766 ->
  0 <= L <= 111 -> 2^L <= T - Tz < 2^(L+1) ->
  f128_sub (f128_pack 1 E T) (f128_pack 1 E Tz) = f128_pack 1 (E - (112 - L)) ((T - Tz) * 2^(112 - L) - 2^112).
Proof.
  intros E T Tz L PK HTz HE HL HD. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Htha & Htla & ETa). pose proof (T_split Tz ltac:(lia)) as (Hthz & Htlz & ETz).
  unfold f128_sub. rewrite (neg_pack1 E Tz) by (constructor; lia).
  unfold f128_add.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  rewrite !hiword_abs by lia.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change SPEC_K with (2^63 + 2^48).
  rewrite !add64_small by lia.
  replace (E * 2 ^ 48 + T / 2 ^ 64 + (2 ^ 63 + 2 ^ 48) <? 2 ^ 63 + 2 ^ 48) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (E * 2 ^ 48 + Tz / 2 ^ 64 + (2 ^ 63 + 2 ^ 48) =? 2 ^ 63 + 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (2 ^ 63 + 2 ^ 48 <? E * 2 ^ 48 + Tz / 2 ^ 64 + (2 ^ 63 + 2 ^ 48)) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb orb].
  unfold add_main.
  set (tha := T / 2^64) in *. set (tla := T mod 2^64) in *.
  set (thz := Tz / 2^64) in *. set (tlz := Tz mod 2^64) in *. clearbody tha tla thz tlz.
  (* |A| > |B|: no swap, the larger operand A (sign 1) is x *)
  replace (if E * 2 ^ 48 + thz =? E * 2 ^ 48 + tha then tla <? tlz else E * 2 ^ 48 + tha <? E * 2 ^ 48 + thz) with false.
  2:{ symmetry. destruct (Z.eqb_spec (E * 2^48 + thz) (E * 2^48 + tha)). - apply Z.ltb_ge. nia. - apply Z.ltb_ge. nia. }
  cbv iota beta.
  rewrite !hiword_exp by lia.
  replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota beta.
  rewrite !hiword_frac by lia.
  unfold align_mirror. rewrite Z.eqb_refl.
  (* the signs differ: subtraction = 1; the sign word of the result is shl64 1 63 *)
  rewrite Z.shiftr_lxor, !hiword_sign by lia. change (Z.lxor 0 1) with 1.
  rewrite !shiftr_div by lia.
  rewrite (shl64_small tha 3), (shl64_small thz 3) by lia. rewrite impl3_hi_eq.
  assert (Hd1 : 0 <= tla / 2^61 < 2^3) by dlia. assert (Hd2 : 0 <= tlz / 2^61 < 2^3) by dlia.
  rewrite (lor_high_low tha (tla / 2^61) 3) by lia.
  replace (2^51) with (1 * 2^51) by lia.
  rewrite (lor_low_high 1 (tlz / 2^61) 51) by lia.
  replace (Z.lor (thz * 2 ^ 3) (1 * 2 ^ 51 + tlz / 2 ^ 61)) with (1 * 2^51 + (thz * 2^3 + tlz / 2^61)).
  2:{ replace (1 * 2 ^ 51 + tlz / 2 ^ 61) with (Z.lor (tlz / 2^61) (1 * 2^51)) by (apply lor_low_high; lia).
      rewrite Z.lor_assoc. rewrite (lor_high_low thz (tlz / 2^61) 3) by lia. symmetry. apply lor_low_high; lia. }
  rewrite (lor_low_high 1 (tha * 2^3 + tla / 2^61) 51) by lia.
  rewrite !shl64_val by lia.
  destruct (addsub_sub_exact (1 * 2 ^ 51 + (tha * 2 ^ 3 + tla / 2 ^ 61)) ((tla * 2 ^ 3) mod 2 ^ 64)
              (1 * 2 ^ 51 + (thz * 2 ^ 3 + tlz / 2 ^ 61)) ((tlz * 2 ^ 3) mod 2 ^ 64) E (T - Tz) L)
    as [SHi [SLo (EQ & R1 & R2 & SV)]]; try lia.
  { dlia. } { dlia. } { dnia. }
  rewrite EQ.
  rewrite !lt_s64_val by lia.
  replace (2 ^ 63 <=? E - (112 - L)) with false by (symmetry; apply Z.leb_gt; lia).
  change (2^63 <=? 32767) with false. change (2^63 <=? 0) with false. cbv iota.
  replace (E - (112 - L) <? 32767) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 <? E - (112 - L)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  (* the sign word is the closed term (1 * 2^63) mod 2^64 = 2^63 *)
  apply round_mirror_exact_neg; [reflexivity | lia | lia | lia | | lia].
  assert (PS : 2^(112 - L) * 2^(L + 1) = 2^113) by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (PS' : 2^(112 - L) * 2^L = 2^112) by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (Pp : 0 < 2^(112 - L)) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Theorem f128_sub_same_neg : forall E T, packed 1 E T -> 1 <= E <= 32766 ->
  f128_sub (f128_pack 1 E T) (f128_pack 1 E T) = f128_pack 0 0 0.
Proof.
  intros E T PK HE. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Htha & Htla & ETa).
  unfold f128_sub. rewrite (neg_pack1 E T) by (constructor; lia).
  unfold f128_add.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  rewrite !hiword_abs by lia.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change SPEC_K with (2^63 + 2^48).
  rewrite !add64_small by lia.
  replace (E * 2 ^ 48 + T / 2 ^ 64 + (2 ^ 63 + 2 ^ 48) <? 2 ^ 63 + 2 ^ 48) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (E * 2 ^ 48 + T / 2 ^ 64 + (2 ^ 63 + 2 ^ 48) =? 2 ^ 63 + 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (2 ^ 63 + 2 ^ 48 <? E * 2 ^ 48 + T / 2 ^ 64 + (2 ^ 63 + 2 ^ 48)) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb orb].
  unfold add_main.
  set (tha := T / 2^64) in *. set (tla := T mod 2^64) in *. clearbody tha tla.
  rewrite Z.eqb_refl, Z.ltb_irrefl. cbv iota beta.
  rewrite !hiword_exp by lia.
  replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota beta.
  rewrite !hiword_frac by lia.
  unfold align_mirror. rewrite Z.eqb_refl.
  rewrite Z.shiftr_lxor, !hiword_sign by lia. change (Z.lxor 0 1) with 1.
  rewrite !shiftr_div by lia.
  rewrite (shl64_small tha 3) by lia. rewrite impl3_hi_eq.
  assert (Hd1 : 0 <= tla / 2^61 < 2^3) by dlia.
  rewrite (lor_high_low tha (tla / 2^61) 3) by lia.
  replace (2^51) with (1 * 2^51) by lia.
  rewrite (lor_low_high 1 (tla / 2^61) 51) by lia.
  replace (Z.lor (tha * 2 ^ 3) (1 * 2 ^ 51 + tla / 2 ^ 61)) with (1 * 2^51 + (tha * 2^3 + tla / 2^61)).
  2:{ replace (1 * 2 ^ 51 + tla / 2 ^ 61) with (Z.lor (tla / 2^61) (1 * 2^51)) by (apply lor_low_high; lia).
      rewrite Z.lor_assoc. rewrite (lor_high_low tha (tla / 2^61) 3) by lia. symmetry. apply lor_low_high; lia. }
  rewrite (lor_low_high 1 (tha * 2^3 + tla / 2^61) 51) by lia.
  (* equal magnitudes: addsub_mirror returns None and the result is +0 *)
  unfold addsub_mirror. change (negb (1 =? 0)) with true. cbv iota.
  rewrite !Z.lxor_nilpotent. change (Z.lor 0 0 =? 0) with true. reflexivity.
Qed.

Theorem f128_sub_zero_r_neg : forall E T, packed 1 E T -> E <= 32766 ->
  f128_sub (f128_pack 1 E T) (f128_pack 0 0 0) = f128_pack 1 E T.
Proof.
  intros E T PK HE. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Htha & Htla & ETa).
  unfold f128_sub. change (hi64 (f128_pack 0 0 0)) with 0. change (lo64 (f128_pack 0 0 0)) with 0.
  change (mk128 (Z.lxor 0 SIGN64) 0) with (f128_pack 1 0 0).
  unfold f128_add.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  change (0 / 2^64) with 0. change (0 mod 2^64) with 0.
  rewrite !hiword_abs by lia.
  change (0 * 2^48 + 0) with 0.
  (* b = -0 is special: the special-case chain runs *)
  change (add64 0 SPEC_K =? SPEC_K) with true. change (0 =? 0) with true. rewrite Bool.orb_true_r.
  rewrite inf_hi_eq.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (E * 2 ^ 48 + T / 2 ^ 64 <? 32767 * 2 ^ 48) with true by (symmetry; apply Z.ltb_lt; lia).
  change (0 =? 32767 * 2^48) with false. change (0 <? 32767 * 2 ^ 48) with true. cbn [negb].
  rewrite lor_eqb0 by (try apply Z.lxor_nonneg; lia). rewrite lxor_eqb0.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Bool.andb_false_r.
  change (Z.lor 0 (Z.lxor 0 (32767 * 2 ^ 48)) =? 0) with false.
  change (negb (Z.lor 0 0 =? 0)) with false. cbv iota.
  rewrite lor_eqb0 by lia.
  destruct ((T mod 2 ^ 64 =? 0) && (E * 2 ^ 48 + T / 2 ^ 64 =? 0)) eqn:C.
  - (* a = -0: the both-zero branch gives (-0) land (-0) = -0 *)
    apply andb_prop in C. destruct C as [C1 C2]. apply Z.eqb_eq in C1. apply Z.eqb_eq in C2.
    assert (E = 0) by lia. assert (T = 0) by lia. subst E T. vm_compute. reflexivity.
  - rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

(* Ranges: every piece of the mirror returns 64-bit words. *)
Local Lemma mk128_rng : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= mk128 hi lo < 2^128.
Proof. intros hi lo Hh Hl. rewrite mk128_val by lia. lia. Qed.

Local Lemma add64_rng : forall x y, 0 <= add64 x y < 2^64.
Proof. intros. unfold add64. apply wrap64_range. Qed.
Local Lemma sub64_rng : forall x y, 0 <= sub64 x y < 2^64.
Proof. intros. unfold sub64. apply wrap64_range. Qed.
Local Lemma shl64_rng : forall x n, 0 <= shl64 x n < 2^64.
Proof. intros. unfold shl64. apply wrap64_range. Qed.

Local Lemma land_rng : forall m x, 0 <= x < 2^64 -> 0 <= Z.land m x < 2^64.
Proof.
  intros m x Hx.
  assert (Ex : Z.land x (Z.ones 64) = x) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite <- Ex, Z.land_assoc, Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

(* Syntactic dispatch on the head of a 64-bit word: no failing unification against unrelated heads. *)
Local Ltac w64 :=
  lazymatch goal with
  | |- 0 <= lo64 _ < 2^64 => apply lo64_range
  | |- 0 <= hi64 _ < 2^64 => apply hi64_range
  | |- 0 <= add64 _ _ < 2^64 => apply add64_rng
  | |- 0 <= sub64 _ _ < 2^64 => apply sub64_rng
  | |- 0 <= shl64 _ _ < 2^64 => apply shl64_rng
  | |- 0 <= Z.land _ _ < 2^64 => apply land_rng; w64
  | |- 0 <= Z.lor _ _ < 2^64 => apply lor_bound; [lia | w64 | w64]
  | |- 0 <= QUIET_HI < 2^64 => unfold QUIET_HI; lia
  | |- 0 <= INF_HI < 2^64 => unfold INF_HI; lia
  | |- 0 <= QNAN_HI < 2^64 => unfold QNAN_HI; lia
  | |- _ => lia
  end.

(* Case-split every match of the goal (the mirrors' branches); each leaf is closed by leaf128. *)
Local Ltac split_matches :=
  repeat (cbv beta iota zeta; match goal with |- context [match ?x with _ => _ end] => destruct x end);
  cbv beta iota zeta.

Local Lemma round_mirror_rng : forall SHi SLo e sg, 0 <= round_mirror SHi SLo e sg < 2^128.
Proof. intros. unfold round_mirror. apply mk128_rng; apply add64_rng. Qed.

Local Ltac leaf128 :=
  lazymatch goal with
  | |- 0 <= round_mirror _ _ _ _ < 2^128 => apply round_mirror_rng
  | |- 0 <= mk128 _ _ < 2^128 => apply mk128_rng; w64
  end.

Local Lemma add_main_rng : forall aLo aHi bLo bHi aAbsHi bAbsHi,
  0 <= add_main aLo aHi bLo bHi aAbsHi bAbsHi < 2^128.
Proof.
  intros. unfold add_main.
  split_matches.
  all: leaf128.
Qed.

Local Lemma f128_add_rng : forall a b, 0 <= f128_add a b < 2^128.
Proof.
  intros a b. unfold f128_add.
  split_matches.
  all: lazymatch goal with
       | |- 0 <= add_main _ _ _ _ _ _ < 2^128 => apply add_main_rng
       | |- _ => leaf128
       end.
Qed.

(* ranges and word split *)
Lemma f128_sub_range : forall a b, 0 <= f128_sub a b < 2^128.
Proof. intros a b. unfold f128_sub. apply f128_add_rng. Qed.

Lemma words128 : forall x, 0 <= x < 2^128 -> lo64 x + 2^64 * hi64 x = x.
Proof.
  intros x Hx. unfold lo64, hi64. rewrite !wrap64_mod, shiftr_div by lia.
  rewrite (Z.mod_small (x / 2^64)).
  - pose proof (Z.div_mod x (2^64) ltac:(lia)). lia.
  - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
