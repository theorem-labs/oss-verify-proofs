(** The binary128 value facts pod_nearest (pod.h:152-171) needs: for a finite binary32 f with value N / D
    ([f32_ratio], Pod/Nearest.v), the soft-float comparisons of d = (long double)f with the constants the function
    passes, and of frac = d - (long double)t with 1/2 and -1/2, decide exactly the rational tests of
    [pod_nearest_exact]. Pure Z over the mirrors f128_of_f32, f128_of_i64, f128_sub, f128_le and f128_ge.

    Route: every finite d below 2^32 in magnitude is f128_pack s (16383 + l - k) (m 2^(112-l) - 2^112) with
    N = +-m, D = 2^k and 2^l <= m < 2^(l+1) (value m / 2^k); a comparison of packed values is the order of their
    keys (f128_le_key / f128_ge_key), and against these constants the key order is a test on l - k and m. For frac:
    t = trunc(N / D) = +-(m / 2^k), and d - t is 0 (t = 0: f128_sub_zero_r), +0 (no remainder: f128_sub_same) or the
    exact difference +-(m mod 2^k) / 2^k in the same form (f128_sub_exact), whose comparison with +-1/2 is the test
    of 2 (N - t D) against +-D. *)
From Stdlib Require Import ZArith Bool Lia SpecFloat.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.Spec Require Import SoftFloat SoftFloatProps.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.Spec Require Export SFVal SFSub.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.Spec Require Import SoftFloatProps3.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G Require Import C_extendsftf2 C_floatditf.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Nearest.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* The binary128 constants pod_nearest passes, as a2 + 2^64 * a3 *)
Definition C1_128 : Z := 2^64 * 0xc01e000000020000.                       (* -(2^31 + 1) = (long double)INT32_MIN - 1 *)
Definition C2_128 : Z := 0x0002000000000000 + 2^64 * 0xc03e000000000000.  (* -(2^63 + 1) *)
Definition HALF_128 : Z := 2^64 * 0x3ffe000000000000.                     (* 1/2 *)
Definition MHALF_128 : Z := 2^64 * 0xbffe000000000000.                    (* -1/2 *)

(** ** Tactics *)
(* The side conditions of the key lemmas: packed operands and "not a NaN". *)
Local Ltac nsf_side := first [ assumption | lia | constructor; lia ].
(* A goal [b1 = b2] of two Z tests: case on each test, then arithmetic. *)
Local Ltac nsf_bool :=
  repeat match goal with
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  end; try reflexivity; exfalso; lia.

(** ** The constants as packed fields *)
Local Lemma nsf_C1 : C1_128 = f128_pack 1 16414 (2^81). Proof. reflexivity. Qed.
Local Lemma nsf_C2 : C2_128 = f128_pack 1 16446 (2^49). Proof. reflexivity. Qed.
Local Lemma nsf_HALF : HALF_128 = f128_pack 0 16382 0. Proof. reflexivity. Qed.
Local Lemma nsf_MHALF : MHALF_128 = f128_pack 1 16382 0. Proof. reflexivity. Qed.

(** ** Keys and comparison results *)
Local Lemma nsf_cmp_lt : forall a b, (cmp_res (Z.compare a b) <? 0) = (a <? b).
Proof. intros a b. destruct (Z.compare_spec a b); destruct (Z.ltb_spec a b); try reflexivity; exfalso; lia. Qed.
Local Lemma nsf_cmp_ge : forall a b, (0 <=? cmp_res (Z.compare a b)) = (b <=? a).
Proof. intros a b. destruct (Z.compare_spec a b); destruct (Z.leb_spec b a); try reflexivity; exfalso; lia. Qed.
Local Lemma nsf_cmp_gt : forall a b, b < a -> cmp_res (Z.compare a b) = 1.
Proof. intros a b H. destruct (Z.compare_spec a b); try reflexivity; exfalso; lia. Qed.
Local Lemma nsf_okey0 : forall E T, f128_okey 0 E T = E * 2^112 + T. Proof. reflexivity. Qed.
Local Lemma nsf_okey1 : forall E T, f128_okey 1 E T = - (E * 2^112 + T). Proof. reflexivity. Qed.
Local Lemma nsf_okeyz : forall s, f128_okey s 0 0 = 0.
Proof. intros s. unfold f128_okey. destruct (s =? 0); reflexivity. Qed.

(** ** Signed magnitudes *)
(* The value of sign s and magnitude m, in the form the binary32 decoding gives it. *)
Local Definition nsf_sgn (s m : Z) : Z := if s =? 1 then - m else m.
(* With s a numeral, unfold the sign and the key. *)
Local Ltac nsf_red := cbv [nsf_sgn f128_okey Z.eqb Pos.eqb].
Local Lemma nsf_sgn_mul : forall s a b, nsf_sgn s a * b = nsf_sgn s (a * b).
Proof. intros s a b. unfold nsf_sgn. destruct (s =? 1); ring. Qed.
Local Lemma nsf_sgn_abs : forall s a, 0 <= a -> Z.abs (nsf_sgn s a) = a.
Proof. intros s a Ha. unfold nsf_sgn. destruct (s =? 1); lia. Qed.
Local Lemma nsf_sgn_neg : forall s a, 0 <= s <= 1 -> 0 < a -> (if nsf_sgn s a <? 0 then 1 else 0) = s.
Proof.
  intros s a Hs Ha. unfold nsf_sgn. destruct (Z.eqb_spec s 1) as [->|Hs1].
  - destruct (Z.ltb_spec (- a) 0); lia.
  - destruct (Z.ltb_spec a 0); lia.
Qed.

(** ** Decoding a binary32 pattern *)
Local Lemma nsf_split : forall b, 0 <= b < 2^32 -> exists s ex mf, 0 <= s <= 1 /\ 0 <= ex <= 255 /\ 0 <= mf < 2^23 /\
  b = s * 2^31 + ex * 2^23 + mf.
Proof.
  intros b Hb. exists (b / 2^31), ((b mod 2^31) / 2^23), ((b mod 2^31) mod 2^23).
  pose proof (Z.div_mod b (2^31) ltac:(lia)) as E1.
  pose proof (Z.mod_pos_bound b (2^31) ltac:(lia)) as B1.
  pose proof (Z.div_mod (b mod 2^31) (2^23) ltac:(lia)) as E2.
  pose proof (Z.mod_pos_bound (b mod 2^31) (2^23) ltac:(lia)) as B2.
  assert (H1 : 0 <= b / 2^31 <= 1).
  { split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
  assert (H2 : 0 <= (b mod 2^31) / 2^23 <= 255).
  { split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
  set (s := b / 2^31) in *. set (r := b mod 2^31) in *. set (ex := r / 2^23) in *. set (mf := r mod 2^23) in *.
  clearbody s r ex mf. lia.
Qed.

Local Lemma nsf_decode : forall s ex mf, 0 <= s <= 1 -> 0 <= ex <= 255 -> 0 <= mf < 2^23 ->
  fp_decode fmt_single (s * 2^31 + ex * 2^23 + mf) =
  if ex =? 0 then (match mf with Zpos p => S754_finite (s =? 1) p (-149) | _ => S754_zero (s =? 1) end)
  else if ex =? 255 then (if mf =? 0 then S754_infinity (s =? 1) else S754_nan)
  else (match 2^23 + mf with Zpos p => S754_finite (s =? 1) p (ex - 150) | _ => S754_nan end).
Proof.
  intros s ex mf Hs Hex Hmf.
  assert (F1 : Z.land (s * 2^31 + ex * 2^23 + mf) (Z.ones 23) = mf).
  { rewrite Z.land_ones by lia.
    replace (s * 2^31 + ex * 2^23 + mf) with (mf + (s * 2^8 + ex) * 2^23) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  assert (F2 : Z.land (Z.shiftr (s * 2^31 + ex * 2^23 + mf) 23) (Z.ones 8) = ex).
  { rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
    replace ((s * 2^31 + ex * 2^23 + mf) / 2^23) with (ex + s * 2^8).
    - rewrite Z_mod_plus_full. apply Z.mod_small. lia.
    - apply Z.div_unique with (r := mf); [left; lia | lia]. }
  assert (F3 : Z.testbit (s * 2^31 + ex * 2^23 + mf) (0 + 31) = (s =? 1)).
  { rewrite <- Z.div_pow2_bits by lia.
    replace ((s * 2^31 + ex * 2^23 + mf) / 2^31) with s.
    - destruct (Z.eqb_spec s 1) as [->|Hs1]; [reflexivity|]. replace s with 0 by lia. reflexivity.
    - apply Z.div_unique with (r := ex * 2^23 + mf); [left; lia | lia]. }
  unfold fp_decode, fp_sign_bit, fp_exp_field, fp_man_field. cbv zeta.
  change (fp_mw fmt_single) with 23. change (fp_ew fmt_single) with 8. change (fp_emin fmt_single) with (-149).
  change (23 + 8) with (0 + 31).
  rewrite F1, F2, F3. change (Z.ones 8) with 255. change (Z.shiftl 1 23) with (2^23).
  replace (ex + -149 - 1) with (ex - 150) by lia. reflexivity.
Qed.

(** [f32_ratio] by class of the pattern. *)
Local Lemma nsf_ratio_zero : forall s, 0 <= s <= 1 -> f32_ratio (s * 2^31) = Some (0, 1).
Proof.
  intros s Hs. unfold f32_ratio.
  replace (s * 2^31) with (s * 2^31 + 0 * 2^23 + 0) by ring.
  rewrite nsf_decode by lia. reflexivity.
Qed.

Local Lemma nsf_ratio_sub : forall s mf, 0 <= s <= 1 -> 0 < mf < 2^23 ->
  f32_ratio (s * 2^31 + mf) = Some (nsf_sgn s mf, 2^149).
Proof.
  intros s mf Hs Hmf. unfold f32_ratio.
  replace (s * 2^31 + mf) with (s * 2^31 + 0 * 2^23 + mf) by ring.
  rewrite nsf_decode by lia.
  destruct mf as [|p|p]; [lia| |lia]. reflexivity.
Qed.

Local Lemma nsf_ratio_big : forall s ex mf, 0 <= s <= 1 -> 150 <= ex <= 254 -> 0 <= mf < 2^23 ->
  f32_ratio (s * 2^31 + ex * 2^23 + mf) = Some (nsf_sgn s (2^23 + mf) * 2^(ex - 150), 1).
Proof.
  intros s ex mf Hs Hex Hmf. unfold f32_ratio. rewrite nsf_decode by lia.
  replace (ex =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (ex =? 255) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (HM : 0 < 2^23 + mf) by lia.
  destruct (2^23 + mf) as [|p|p] eqn:EM; [lia| |lia].
  cbv beta iota zeta.
  replace (0 <=? ex - 150) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Local Lemma nsf_ratio_small : forall s ex mf, 0 <= s <= 1 -> 1 <= ex < 150 -> 0 <= mf < 2^23 ->
  f32_ratio (s * 2^31 + ex * 2^23 + mf) = Some (nsf_sgn s (2^23 + mf), 2^(150 - ex)).
Proof.
  intros s ex mf Hs Hex Hmf. unfold f32_ratio. rewrite nsf_decode by lia.
  replace (ex =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (ex =? 255) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (HM : 0 < 2^23 + mf) by lia.
  destruct (2^23 + mf) as [|p|p] eqn:EM; [lia| |lia].
  cbv beta iota zeta.
  replace (0 <=? ex - 150) with false by (symmetry; apply Z.leb_gt; lia).
  replace (- (ex - 150)) with (150 - ex) by lia.
  reflexivity.
Qed.

Local Lemma nsf_ratio_infnan : forall s mf, 0 <= s <= 1 -> 0 <= mf < 2^23 ->
  f32_ratio (s * 2^31 + 255 * 2^23 + mf) = None.
Proof.
  intros s mf Hs Hmf. unfold f32_ratio. rewrite nsf_decode by lia.
  change (255 =? 0) with false. rewrite Z.eqb_refl.
  destruct (mf =? 0); reflexivity.
Qed.

(** ** The packed form of d *)
Local Lemma nsf_scale : forall m l, 0 <= l <= 112 -> 2^l <= m < 2^(l+1) -> 2^112 <= m * 2^(112 - l) < 2^113.
Proof.
  intros m l Hl Hm.
  assert (P : 2^l * 2^(112 - l) = 2^112) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (P' : 2^(l+1) * 2^(112 - l) = 2^113) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Q : 0 < 2^(112 - l)) by (apply Z.pow_pos_nonneg; lia).
  split.
  - rewrite <- P. apply Z.mul_le_mono_nonneg_r; lia.
  - rewrite <- P'. apply Z.mul_lt_mono_pos_r; lia.
Qed.

Local Lemma nsf_form_packed : forall s m l k, 0 <= s <= 1 -> 0 <= l <= 112 -> 0 <= 16383 + l - k <= 32767 ->
  2^l <= m < 2^(l+1) -> packed s (16383 + l - k) (m * 2^(112 - l) - 2^112).
Proof. intros s m l k Hs Hl Hk Hm. pose proof (nsf_scale m l Hl Hm). constructor; lia. Qed.

(** A finite binary32 with value N / D is +-0, or of magnitude below 2^32 in the form m / 2^k, or of magnitude at
    least 2^32 (an integer, exponent field at least 159). *)
Local Lemma nsf_d_cases : forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) ->
  0 < D /\
  ((N = 0 /\ D = 1 /\ exists s, 0 <= s <= 1 /\ f128_of_f32 b = f128_pack s 0 0) \/
   (exists s m l k, 0 <= s <= 1 /\ 0 <= k <= 149 /\ 0 <= l <= 31 /\ l <= k + 31 /\ 2^l <= m < 2^(l+1) /\
      D = 2^k /\ N = nsf_sgn s m /\ f128_of_f32 b = f128_pack s (16383 + l - k) (m * 2^(112 - l) - 2^112)) \/
   (exists s E T M, packed s E T /\ 16415 <= E <= 32766 /\ D = 1 /\ N = nsf_sgn s M /\ 2^32 <= M /\
      f128_of_f32 b = f128_pack s E T)).
Proof.
  intros b N D Hb HR.
  destruct (nsf_split b Hb) as (s & ex & mf & Hs & Hex & Hmf & ->).
  destruct (Z.eq_dec ex 255) as [->|H255].
  { rewrite nsf_ratio_infnan in HR by lia. discriminate. }
  destruct (Z.eq_dec ex 0) as [->|H0].
  - rewrite Z.mul_0_l, Z.add_0_r in HR |- *.
    destruct (Z.eq_dec mf 0) as [->|Hm0].
    + rewrite Z.add_0_r in HR |- *. rewrite nsf_ratio_zero in HR by lia. injection HR as <- <-.
      split; [lia|]. left. split; [reflexivity|]. split; [reflexivity|].
      exists s. split; [lia|]. apply f128_of_f32_zero; lia.
    + rewrite nsf_ratio_sub in HR by lia. injection HR as <- <-.
      pose proof (Z.log2_spec mf ltac:(lia)) as HL. unfold Z.succ in HL.
      assert (HL2 : Z.log2 mf < 23) by (apply Z.log2_lt_pow2; lia).
      pose proof (Z.log2_nonneg mf) as HL0.
      split; [apply Z.pow_pos_nonneg; lia|]. right; left.
      exists s, mf, (Z.log2 mf), 149.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HL|].
      split; [reflexivity|]. split; [reflexivity|].
      rewrite (f128_of_f32_subnormal s mf (Z.log2 mf)) by lia. f_equal. lia.
  - destruct (Z.le_gt_cases 150 ex) as [Hbig|Hsmall].
    + rewrite nsf_ratio_big in HR by lia. injection HR as <- <-.
      rewrite f128_of_f32_normal by lia. rewrite nsf_sgn_mul.
      assert (HP : 0 < 2^(ex - 150)) by (apply Z.pow_pos_nonneg; lia).
      split; [lia|].
      destruct (Z.le_gt_cases ex 158) as [H158|H159].
      * right; left.
        exists s, ((2^23 + mf) * 2^(ex - 150)), (ex - 127), 0.
        assert (P1 : 2^(ex - 127) = 2^23 * 2^(ex - 150)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (P2 : 2^(ex - 127 + 1) = 2^24 * 2^(ex - 150)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (P3 : 2^(ex - 150) * 2^(112 - (ex - 127)) = 2^89) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [rewrite P1, P2; nia|].
        split; [reflexivity|]. split; [reflexivity|].
        f_equal; [lia|]. rewrite <- Z.mul_assoc, P3. lia.
      * right; right.
        exists s, (ex + 16256), (mf * 2^89), ((2^23 + mf) * 2^(ex - 150)).
        assert (P9 : 2^9 <= 2^(ex - 150)) by (apply Z.pow_le_mono_r; lia).
        split; [constructor; lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [nia|]. reflexivity.
    + rewrite nsf_ratio_small in HR by lia. injection HR as <- <-.
      rewrite f128_of_f32_normal by lia.
      split; [apply Z.pow_pos_nonneg; lia|]. right; left.
      exists s, (2^23 + mf), 23, (150 - ex).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [change (23 + 1) with 24; lia|].
      split; [reflexivity|]. split; [reflexivity|].
      f_equal; [lia | change (112 - 23) with 89; lia].
Qed.

(** ** Exact subtraction, either sign *)
Local Lemma nsf_sub_zero_r : forall s E T, packed s E T -> E <= 32766 ->
  f128_sub (f128_pack s E T) (f128_pack 0 0 0) = f128_pack s E T.
Proof.
  intros s E T PK HE. assert (s = 0 \/ s = 1) as [-> | ->] by (destruct PK; lia).
  - apply f128_sub_zero_r; assumption.
  - apply f128_sub_zero_r_neg; assumption.
Qed.

Local Lemma nsf_sub_same : forall s E T, packed s E T -> 1 <= E <= 32766 ->
  f128_sub (f128_pack s E T) (f128_pack s E T) = f128_pack 0 0 0.
Proof.
  intros s E T PK HE. assert (s = 0 \/ s = 1) as [-> | ->] by (destruct PK; lia).
  - apply f128_sub_same; assumption.
  - apply f128_sub_same_neg; assumption.
Qed.

Local Lemma nsf_sub_exact : forall s E T Tz L, packed s E T -> 0 <= Tz < T -> 113 <= E <= 32766 ->
  0 <= L <= 111 -> 2^L <= T - Tz < 2^(L+1) ->
  f128_sub (f128_pack s E T) (f128_pack s E Tz) = f128_pack s (E - (112 - L)) ((T - Tz) * 2^(112 - L) - 2^112).
Proof.
  intros s E T Tz L PK H1 H2 H3 H4. assert (s = 0 \/ s = 1) as [-> | ->] by (destruct PK; lia).
  - apply f128_sub_exact; assumption.
  - apply f128_sub_exact_neg; assumption.
Qed.

(** ** frac against 1/2 and -1/2 *)
(* frac = +-0: neither test holds. *)
Local Lemma nsf_frac_zero : forall s D, 0 <= s <= 1 -> 0 < D ->
  (0 <=? f128_ge (f128_pack s 0 0) HALF_128) = (D <=? 2 * 0) /\
  (f128_le (f128_pack s 0 0) MHALF_128 <? 0) = (2 * 0 <? - D).
Proof.
  intros s D Hs HD. rewrite nsf_HALF, nsf_MHALF.
  rewrite f128_ge_key, f128_le_key by nsf_side.
  rewrite nsf_cmp_ge, nsf_cmp_lt, nsf_okeyz, nsf_okey0, nsf_okey1.
  split; nsf_bool.
Qed.

(* frac = +-m / 2^k with m < 2^k: its exponent field is 16382 exactly when 2m >= 2^k. *)
Local Lemma nsf_frac_cmp : forall s m l k, 0 <= s <= 1 -> 0 <= l < k -> k <= 149 -> l <= 112 -> 2^l <= m < 2^(l+1) ->
  (0 <=? f128_ge (f128_pack s (16383 + l - k) (m * 2^(112 - l) - 2^112)) HALF_128) = (2^k <=? 2 * nsf_sgn s m) /\
  (f128_le (f128_pack s (16383 + l - k) (m * 2^(112 - l) - 2^112)) MHALF_128 <? 0) = (2 * nsf_sgn s m <? - 2^k).
Proof.
  intros s m l k Hs Hlk Hk Hl Hm.
  assert (PK : packed s (16383 + l - k) (m * 2^(112 - l) - 2^112)) by (apply nsf_form_packed; lia).
  pose proof (nsf_scale m l ltac:(lia) Hm) as HS.
  assert (P : 2^l * 2^(112 - l) = 2^112) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Q : 0 < 2^(112 - l)) by (apply Z.pow_pos_nonneg; lia).
  assert (HX : (2^l < m /\ 2^112 < m * 2^(112 - l)) \/ (m = 2^l /\ m * 2^(112 - l) = 2^112)).
  { destruct (Z.lt_ge_cases (2^l) m) as [H|H].
    - left. split; [exact H|]. rewrite <- P. apply Z.mul_lt_mono_pos_r; lia.
    - right. assert (E : m = 2^l) by lia. split; [exact E|]. rewrite E. exact P. }
  assert (P1 : 2^(l+1) = 2 * 2^l) by (rewrite Z.pow_add_r by lia; change (2^1) with 2; ring).
  assert (Hl0 : 0 < 2^l) by (apply Z.pow_pos_nonneg; lia).
  rewrite nsf_HALF, nsf_MHALF.
  rewrite f128_ge_key, f128_le_key by nsf_side.
  rewrite nsf_cmp_ge, nsf_cmp_lt.
  set (X := m * 2^(112 - l)) in *. clearbody X.
  destruct (Z.eq_dec l (k - 1)) as [El|Nl].
  - assert (P2 : 2^k = 2 * 2^l) by (rewrite <- P1; f_equal; lia).
    assert (s = 0 \/ s = 1) as [-> | ->] by lia;
      nsf_red; split; nsf_bool.
  - assert (P2 : 2 * 2^(l+1) <= 2^k).
    { rewrite <- Z.pow_succ_r by lia. apply Z.pow_le_mono_r; lia. }
    assert (s = 0 \/ s = 1) as [-> | ->] by lia;
      nsf_red; split; nsf_bool.
Qed.

(* d = +-m / 2^k (m < 2^32 * 2^k), t = trunc(d): the frac tests are the tests of 2 (N - t D) against +-D. *)
Local Lemma nsf_frac_form : forall s m l k, 0 <= s <= 1 -> 0 <= k <= 149 -> 0 <= l <= 31 -> 2^l <= m < 2^(l+1) ->
  (0 <=? f128_ge (f128_sub (f128_pack s (16383 + l - k) (m * 2^(112 - l) - 2^112))
                            (f128_of_i64 (Z.quot (nsf_sgn s m) (2^k)))) HALF_128)
    = (2^k <=? 2 * (nsf_sgn s m - Z.quot (nsf_sgn s m) (2^k) * 2^k)) /\
  (f128_le (f128_sub (f128_pack s (16383 + l - k) (m * 2^(112 - l) - 2^112))
                      (f128_of_i64 (Z.quot (nsf_sgn s m) (2^k)))) MHALF_128 <? 0)
    = (2 * (nsf_sgn s m - Z.quot (nsf_sgn s m) (2^k) * 2^k) <? - 2^k).
Proof.
  intros s m l k Hs Hk Hl Hm.
  assert (HK : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hl0 : 0 < 2^l) by (apply Z.pow_pos_nonneg; lia).
  assert (PKd : packed s (16383 + l - k) (m * 2^(112 - l) - 2^112)) by (apply nsf_form_packed; lia).
  assert (Hquot : forall a, 0 <= a -> Z.quot (nsf_sgn s a) (2^k) = nsf_sgn s (a / 2^k)).
  { intros a Ha. unfold nsf_sgn. destruct (s =? 1).
    - rewrite Z.quot_opp_l by lia. rewrite Z.quot_div_nonneg by lia. reflexivity.
    - apply Z.quot_div_nonneg; lia. }
  rewrite (Hquot m) by lia.
  destruct (Z.lt_ge_cases l k) as [Hlk|Hlk].
  - (* |N| < D: t = 0 and frac = d *)
    assert (Hmk : m < 2^k).
    { apply Z.lt_le_trans with (2^(l+1)); [lia|]. apply Z.pow_le_mono_r; lia. }
    rewrite (Z.div_small m (2^k)) by lia.
    replace (nsf_sgn s 0) with 0 by (unfold nsf_sgn; destruct (s =? 1); reflexivity).
    rewrite f128_of_i64_zero, nsf_sub_zero_r by nsf_side.
    replace (nsf_sgn s m - 0 * 2^k) with (nsf_sgn s m) by ring.
    apply nsf_frac_cmp; lia.
  - (* |N| >= D: t = +-q with q = m / 2^k, the remainder is +-r with r = m mod 2^k *)
    pose proof (Z.div_mod m (2^k) ltac:(lia)) as Em.
    pose proof (Z.mod_pos_bound m (2^k) HK) as Hr.
    set (q := m / 2^k) in *. set (r := m mod 2^k) in *. clearbody q r.
    assert (PK1 : 2^l = 2^k * 2^(l - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (PK2 : 2^(l+1) = 2^k * 2^(l - k + 1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hlk0 : 0 < 2^(l - k)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hq : 2^(l - k) <= q < 2^(l - k + 1)).
    { split.
      - destruct (Z.lt_ge_cases q (2^(l - k))) as [H|H]; [|exact H]. exfalso.
        assert (2^k * (q + 1) <= 2^k * 2^(l - k)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
      - destruct (Z.lt_ge_cases q (2^(l - k + 1))) as [H|H]; [exact H|]. exfalso.
        assert (2^k * 2^(l - k + 1) <= 2^k * q) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
    assert (Hrem : nsf_sgn s m - nsf_sgn s q * 2^k = nsf_sgn s r) by (unfold nsf_sgn; destruct (s =? 1); lia).
    rewrite Hrem.
    assert (Hti : f128_of_i64 (nsf_sgn s q) = f128_pack s (16383 + l - k) (q * 2^(112 - (l - k)) - 2^112)).
    { rewrite (f128_of_i64_val (nsf_sgn s q) (l - k)) by (try rewrite nsf_sgn_abs by lia; lia).
      rewrite nsf_sgn_abs, nsf_sgn_neg by lia. f_equal. lia. }
    rewrite Hti.
    pose proof (nsf_scale q (l - k) ltac:(lia) Hq) as HSq.
    destruct (Z.eq_dec r 0) as [Hr0|Hr0].
    + (* no remainder: t = N / D exactly, d - t = +0 *)
      subst r.
      assert (ET : q * 2^(112 - (l - k)) = m * 2^(112 - l)).
      { rewrite Em. replace (112 - (l - k)) with (k + (112 - l)) by lia. rewrite Z.pow_add_r by lia. ring. }
      rewrite ET, nsf_sub_same by nsf_side.
      replace (nsf_sgn s 0) with 0 by (unfold nsf_sgn; destruct (s =? 1); reflexivity).
      apply nsf_frac_zero; lia.
    + (* remainder r with 2^l' <= r < 2^(l'+1), l' < k: the exact difference r / 2^k, same form *)
      pose proof (Z.log2_spec r ltac:(lia)) as HL. unfold Z.succ in HL.
      pose proof (Z.log2_nonneg r) as HL0.
      set (l' := Z.log2 r) in *. clearbody l'.
      assert (Hl'k : l' < k).
      { destruct (Z.lt_ge_cases l' k) as [H|H]; [exact H|]. exfalso.
        assert (2^k <= 2^l') by (apply Z.pow_le_mono_r; lia). lia. }
      assert (ETT : m * 2^(112 - l) - 2^112 - (q * 2^(112 - (l - k)) - 2^112) = r * 2^(112 - l)).
      { rewrite Em. replace (112 - (l - k)) with (k + (112 - l)) by lia. rewrite Z.pow_add_r by lia. ring. }
      assert (HLr : 2^(l' + (112 - l)) <= r * 2^(112 - l) < 2^(l' + (112 - l) + 1)).
      { replace (l' + (112 - l) + 1) with ((l' + 1) + (112 - l)) by lia.
        rewrite (Z.pow_add_r 2 l' (112 - l)), (Z.pow_add_r 2 (l' + 1) (112 - l)) by lia.
        assert (0 < 2^(112 - l)) by (apply Z.pow_pos_nonneg; lia). split.
        - apply Z.mul_le_mono_nonneg_r; lia.
        - apply Z.mul_lt_mono_pos_r; lia. }
      assert (HLp : 0 < 2^(l' + (112 - l))) by (apply Z.pow_pos_nonneg; lia).
      rewrite (nsf_sub_exact s (16383 + l - k) (m * 2^(112 - l) - 2^112) (q * 2^(112 - (l - k)) - 2^112)
                 (l' + (112 - l))).
      2: exact PKd.
      2: lia.
      2: lia.
      2: lia.
      2: rewrite ETT; exact HLr.
      rewrite ETT.
      replace (r * 2^(112 - l) * 2^(112 - (l' + (112 - l)))) with (r * 2^(112 - l')).
      2: { rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia. }
      replace (16383 + l - k - (112 - (l' + (112 - l)))) with (16383 + l' - k) by lia.
      apply nsf_frac_cmp; lia.
Qed.

(* d against C1 in the form case. *)
Local Lemma nsf_lo_form : forall s m l k, 0 <= s <= 1 -> 0 <= k <= 149 -> 0 <= l <= 31 -> l <= k + 31 ->
  2^l <= m < 2^(l+1) ->
  (f128_okey s (16383 + l - k) (m * 2^(112 - l) - 2^112) <? - (16414 * 2^112 + 2^81)) =
  (nsf_sgn s m <? (- 2^31 - 1) * 2^k).
Proof.
  intros s m l k Hs Hk Hl Hlk Hm.
  pose proof (nsf_scale m l ltac:(lia) Hm) as HS.
  assert (Hl0 : 0 < 2^l) by (apply Z.pow_pos_nonneg; lia).
  assert (HK : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (s = 0 \/ s = 1) as [-> | ->] by lia; nsf_red.
  - nsf_bool.
  - destruct (Z.eq_dec l (k + 31)) as [E|E].
    + assert (k = 0) by lia. subst k. assert (l = 31) by lia. subst l.
      change (112 - 31) with 81 in HS |- *. change (2^0) with 1. change (31 + 1) with 32 in Hm.
      nsf_bool.
    + assert (P : 2^(l+1) <= 2^31 * 2^k).
      { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
      nsf_bool.
Qed.

(** ** The four facts *)
Theorem near_sf_neginf : forall b, 0 <= b < 2^32 -> fp_decode fmt_single b = S754_infinity true ->
  f128_le (f128_of_f32 b) C1_128 = -1.
Proof.
  intros b Hb H.
  destruct (nsf_split b Hb) as (s & ex & mf & Hs & Hex & Hmf & ->).
  rewrite nsf_decode in H by lia. revert H.
  destruct (Z.eqb_spec ex 0) as [->|H0].
  { destruct mf; intro H; discriminate H. }
  destruct (Z.eqb_spec ex 255) as [->|H255].
  2: { destruct (2^23 + mf); intro H; discriminate H. }
  destruct (Z.eqb_spec mf 0) as [->|Hm0]; [|intro H; discriminate H].
  intro H. injection H as Hs1. apply Z.eqb_eq in Hs1. subst s.
  rewrite Z.add_0_r, (f128_of_f32_inf 1), nsf_C1 by lia.
  rewrite f128_le_key by nsf_side. reflexivity.
Qed.

Theorem near_sf_lo : forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) ->
  (f128_le (f128_of_f32 b) C1_128 <? 0) = (N <? (INT32_MIN - 1) * D).
Proof.
  intros b N D Hb HR. rewrite nsf_C1. unfold INT32_MIN.
  destruct (nsf_d_cases b N D Hb HR) as [HD [(-> & -> & s & Hs & Hd)
    | [(s & m & l & k & Hs & Hk & Hl & Hlk & Hm & -> & -> & Hd) | (s & E & T & M & PK & HE & -> & -> & HM & Hd)]]];
    rewrite Hd.
  - rewrite f128_le_key by nsf_side. rewrite nsf_cmp_lt, nsf_okeyz. reflexivity.
  - assert (PK : packed s (16383 + l - k) (m * 2^(112 - l) - 2^112)) by (apply nsf_form_packed; lia).
    rewrite f128_le_key by nsf_side. rewrite nsf_cmp_lt, nsf_okey1.
    apply nsf_lo_form; assumption.
  - rewrite f128_le_key by nsf_side. rewrite nsf_cmp_lt, nsf_okey1.
    destruct PK as [Hs HE' HT].
    assert (s = 0 \/ s = 1) as [-> | ->] by lia; nsf_red; nsf_bool.
Qed.

Theorem near_sf_c2 : forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) -> (INT32_MIN - 1) * D <= N ->
  f128_ge (f128_of_f32 b) C2_128 = 1.
Proof.
  intros b N D Hb HR HN. rewrite nsf_C2. unfold INT32_MIN in HN.
  destruct (nsf_d_cases b N D Hb HR) as [HD [(-> & -> & s & Hs & Hd)
    | [(s & m & l & k & Hs & Hk & Hl & Hlk & Hm & -> & -> & Hd) | (s & E & T & M & PK & HE & -> & -> & HM & Hd)]]];
    rewrite Hd.
  - rewrite f128_ge_key by nsf_side. apply nsf_cmp_gt. rewrite nsf_okeyz, nsf_okey1. lia.
  - assert (PK : packed s (16383 + l - k) (m * 2^(112 - l) - 2^112)) by (apply nsf_form_packed; lia).
    rewrite f128_ge_key by nsf_side. apply nsf_cmp_gt. rewrite nsf_okey1.
    pose proof (nsf_scale m l ltac:(lia) Hm) as HS.
    assert (s = 0 \/ s = 1) as [-> | ->] by lia; nsf_red; lia.
  - rewrite f128_ge_key by nsf_side. apply nsf_cmp_gt. rewrite nsf_okey1.
    destruct PK as [Hs HE' HT].
    assert (s = 0 \/ s = 1) as [-> | ->] by lia; nsf_red; cbv [nsf_sgn Z.eqb Pos.eqb] in HN; lia.
Qed.

Theorem near_sf_frac : forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) ->
  (INT32_MIN - 1) * D <= N <= (INT32_MAX + 1) * D ->
  let t := Z.quot N D in
  let fr := f128_sub (f128_of_f32 b) (f128_of_i64 t) in
  (0 <=? f128_ge fr HALF_128) = (D <=? 2 * (N - t * D)) /\
  (f128_le fr MHALF_128 <? 0) = (2 * (N - t * D) <? - D).
Proof.
  intros b N D Hb HR HND. cbv zeta.
  destruct (nsf_d_cases b N D Hb HR) as [HD [(-> & -> & s & Hs & Hd)
    | [(s & m & l & k & Hs & Hk & Hl & Hlk & Hm & -> & -> & Hd) | (s & E & T & M & PK & HE & -> & -> & HM & Hd)]]];
    rewrite Hd.
  - change (Z.quot 0 1) with 0. rewrite f128_of_i64_zero, nsf_sub_zero_r by nsf_side.
    replace (0 - 0 * 1) with 0 by ring. apply nsf_frac_zero; lia.
  - apply nsf_frac_form; lia.
  - exfalso. unfold INT32_MIN, INT32_MAX in HND.
    assert (s = 0 \/ s = 1) as [-> | ->] by (destruct PK; lia); cbv [nsf_sgn Z.eqb Pos.eqb] in HND; lia.
Qed.
