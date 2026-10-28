(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition M64 : Z := 18446744073709551615.

Lemma land64 x : Z.land x 18446744073709551615 = x mod 2^64.
Proof. change 18446744073709551615 with (2^64 - 1). rewrite <- Z.land_ones by lia. reflexivity. Qed.

Lemma mod64_small x : 0 <= x < 2^64 -> x mod 2^64 = x.
Proof. intros. apply Z.mod_small. lia. Qed.

Lemma mod64_neg x : - 2^64 <= x < 0 -> x mod 2^64 = x + 2^64.
Proof.
  intros. rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_def z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. reflexivity. Qed.

Lemma swrap32_small z : - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros. rewrite swrap32_def. rewrite Z.mod_small by lia. lia. Qed.

Lemma swrap32_range z : - 2^31 <= bv_swrap 32 z < 2^31.
Proof. rewrite swrap32_def. pose proof (Z.mod_pos_bound (z + 2^31) (2^32) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma swrap32_add_mul32 z k : bv_swrap 32 (z + k * 2^32) = bv_swrap 32 z.
Proof. rewrite !swrap32_def. replace (z + k * 2^32 + 2^31) with (z + 2^31 + k * 2^32) by lia. rewrite Z.mod_add by lia. reflexivity. Qed.

Lemma swrap32_mod64 z k : bv_swrap 32 (z mod 2^64 + k) = bv_swrap 32 (z + k).
Proof.
  rewrite (Z.mod_eq z (2^64)) by lia. replace (z - 2^64 * (z / 2^64) + k) with (z + k + (- (z / 2^64) * 2^32) * 2^32) by lia.
  apply swrap32_add_mul32.
Qed.

(* [comment removed for export] *)
Lemma swrap32_congr z : exists k, bv_swrap 32 z = z + k * 2^32.
Proof.
  rewrite swrap32_def. exists (- ((z + 2^31) / 2^32)). rewrite (Z.mod_eq (z + 2^31) (2^32)) by lia. lia.
Qed.

Lemma signed_lit z : - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 `div` 2) with (2^63). rewrite Z.mod_small by lia. lia.
Qed.

Lemma shiftr_div z k : 0 <= k -> Z.shiftr z k = z / 2^k.
Proof. intros. apply Z.shiftr_div_pow2. assumption. Qed.

Lemma sign_bit63 q : - 2^63 <= q < 2^63 -> Z.shiftr (Z.land q 18446744073709551615) 63 = (if q <? 0 then 1 else 0).
Proof.
  intros Hq. rewrite land64, shiftr_div by lia.
  destruct (Z.ltb_spec q 0).
  - rewrite mod64_neg by lia. symmetry. apply Z.div_unique_pos with (r := q + 2^64 - 2^63); lia.
  - rewrite mod64_small by lia. apply Z.div_small. lia.
Qed.

(* [comment removed for export] *)
Lemma div_ltb0 a b : 0 < b -> (a / b <? 0) = (a <? 0).
Proof.
  intros Hb. destruct (Z.ltb_spec a 0).
  - apply Z.ltb_lt. apply Z.div_lt_upper_bound; lia.
  - apply Z.ltb_ge. apply Z.div_pos; lia.
Qed.

Lemma eqm_of_sub0 e1 e2 : (e1 - e2) mod 2^64 = 0 -> e1 mod 2^64 = e2 mod 2^64.
Proof.
  intros H. apply Z.div_exact in H; [|lia]. replace e1 with (e2 + (e1 - e2) / 2^64 * 2^64) by lia. apply Z.mod_add. lia.
Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_eqm0 e1 e2 : (e1 - e2) mod 2^64 = 0 -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof. intros H. apply Z_to_bv_eqm. apply eqm_of_sub0. exact H. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_eq_mul e1 e2 k : e1 = e2 + k * 2^64 -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof. intros ->. apply Z_to_bv_eqm. apply Z.mod_add. lia. Qed.

(* [comment removed for export] *)
Lemma mod64_eq x : exists k, x mod 2^64 = x - k * 2^64 /\ 0 <= x - k * 2^64 < 2^64.
Proof. exists (x / 2^64). pose proof (Z.div_mod x (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound x (2^64) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma land16 x : Z.land x 65535 = x mod 2^16.
Proof. change 65535 with (2^16 - 1). rewrite <- Z.land_ones by lia. reflexivity. Qed.
Lemma land32 x : Z.land x 4294967295 = x mod 2^32.
Proof. change 4294967295 with (2^32 - 1). rewrite <- Z.land_ones by lia. reflexivity. Qed.
Ltac mlia := rewrite ?shiftr_div by lia; rewrite ?zb_shiftl_mul by lia; rewrite ?land64, ?land32, ?land16; Z.to_euclidean_division_equations; lia.
Ltac wmod := rewrite ?land64; apply Z_to_bv_eqm0; mlia.

Lemma sra63 r : - 2^63 <= r < 2^63 -> r / 2^63 = (if r <? 0 then -1 else 0).
Proof.
  intros Hr. destruct (Z.ltb_spec r 0).
  - symmetry. apply Z.div_unique_pos with (r := r + 2^63); lia.
  - apply Z.div_small. lia.
Qed.

Lemma swrap32_eqm V E : - 2^31 <= V < 2^31 -> (E - V) mod 2^32 = 0 -> bv_swrap 32 E = V.
Proof.
  intros HV HE. rewrite swrap32_def. apply Z.div_exact in HE; [|lia].
  replace (E + 2^31) with (V + 2^31 + (E - V) / 2^32 * 2^32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
Ltac w32 := f_equal; symmetry; rewrite ?land64; apply swrap32_eqm; [lia| mlia].

Lemma swrap32_congr_eq E v : (E - v) mod 2^32 = 0 -> bv_swrap 32 E = bv_swrap 32 v.
Proof.
  intros H. apply Z.div_exact in H; [|lia]. replace E with (v + (E - v) / 2^32 * 2^32) by lia. apply swrap32_add_mul32.
Qed.

(* [comment removed for export] *)
Lemma bit31_gen E v : - 2^31 <= v < 2^31 -> (E - v) mod 2^32 = 0 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 E) 31) = (if v <? 0 then 1 else 0).
Proof.
  intros Hv HE. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite shiftr_div by lia.
  apply Z.div_exact in HE; [|lia]. replace E with (v + (E - v) / 2^32 * 2^32) by lia. rewrite Z.mod_add by lia.
  destruct (Z.ltb_spec v 0).
  - replace (v mod 2^32) with (v + 2^32) by (symmetry; rewrite <- (Z.mod_add v 1) by lia; apply Z.mod_small; lia).
    replace ((v + 2^32) / 2^31) with 1 by (apply Z.div_unique_pos with (r := v + 2^32 - 2^31); lia). apply swrap32_small. lia.
  - rewrite Z.mod_small by lia. rewrite Z.div_small by lia. apply swrap32_small. lia.
Qed.

(* [comment removed for export] *)
Lemma sraiw_gen E v k : - 2^31 <= v < 2^31 -> 0 <= k < 32 -> (E - v) mod 2^32 = 0 -> bv_swrap 32 (Z.shiftr (bv_swrap 32 E) k) = v / 2^k.
Proof.
  intros Hv Hk HE. rewrite (swrap32_congr_eq E v HE). rewrite (swrap32_small v) by lia. rewrite shiftr_div by lia.
  apply swrap32_small. assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_le_lower_bound; nia| apply Z.div_lt_upper_bound; nia].
Qed.

(* [comment removed for export] *)
Lemma srliw_gen E v k : 0 <= v < 2^31 -> 1 <= k < 32 -> (E - v) mod 2^32 = 0 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 E) k) = v / 2^k.
Proof.
  intros Hv Hk HE. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite shiftr_div by lia.
  apply Z.div_exact in HE; [|lia]. replace E with (v + (E - v) / 2^32 * 2^32) by lia. rewrite Z.mod_add, Z.mod_small by lia.
  apply swrap32_small. assert (2 <= 2^k) by (change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia).
  split; [apply Z.div_le_lower_bound; nia| apply Z.div_lt_upper_bound; nia].
Qed.

(* [comment removed for export] *)
Lemma hi32_negc_congr x c C d : C = 2^64 - c -> d = 2^32 - c -> 0 <= x < 2^31 -> 0 < c < 2^32 ->
  ((((x * C) mod 2^64) / 2^32 + x) mod 2^64 - (x * d) / 2^32) mod 2^32 = 0.
Proof.
  intros -> -> Hx Hc.
  destruct (Z.eq_dec x 0) as [->|NZ].
  { rewrite !Z.mul_0_l. rewrite (Z.mod_0_l (2^64)) by lia. rewrite (Z.div_0_l (2^32)) by lia. reflexivity. }
  set (p := x * c). assert (Hp : 0 < p < 2^63) by (subst p; nia).
  replace (x * (2^64 - c)) with (- p + x * 2^64) by (subst p; lia). rewrite Z.mod_add by lia.
  replace ((- p) mod 2^64) with (2^32 * 2^32 + - p).
  2:{ symmetry. rewrite <- (Z.mod_add (- p) 1) by lia. rewrite Z.mod_small by lia. lia. }
  rewrite Z.div_add_l by lia.
  replace (2^32 + - p / 2^32 + x) with (2^32 + (x * 2^32 + - p) / 2^32) by (rewrite Z.div_add_l by lia; lia).
  replace (x * 2^32 + - p) with (x * (2^32 - c)) by (subst p; lia).
  set (T := x * (2^32 - c) / 2^32).
  assert (HT : 0 <= T < 2^31).
  { subst T. split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small (2^32 + T)) by lia. replace (2^32 + T - T) with (1 * 2^32) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Tactic Notation "mliak" ne_hyp_list(l) := clear - l; mlia.
Tactic Notation "wmodk" ne_hyp_list(l) := clear - l; wmod.
Tactic Notation "w32k" ne_hyp_list(l) := clear - l; w32.

(* [comment removed for export] *)
Lemma slti_lit x d : 0 <= x < 2^63 -> 9223372036854775808 <= d -> (Z.lxor x 9223372036854775808 <? d) = (x <? d - 9223372036854775808).
Proof.
  intros Hx Hd. change 9223372036854775808 with (2^63) at 1. rewrite zb_lxor_sign by lia. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec x (d - 9223372036854775808)); [apply Z.ltb_lt| apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Lemma mulhu_3600 s : 0 <= s -> Z.shiftr (s * 4294967296 * 10494147740416606208) 64 = s * 2443359173.
Proof.
  intros Hs. rewrite shiftr_div by lia. replace (s * 4294967296 * 10494147740416606208) with (s * 2443359173 * 2^64) by lia.
  apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap64_small z : - 2^63 <= z < 2^63 -> bv_swrap 64 z = z.
Proof. intros. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). change (2^64 `div` 2) with (2^63). rewrite Z.mod_small by lia. lia. Qed.
Lemma swrap64_big z : 2^63 <= z < 2^64 + 2^63 -> bv_swrap 64 z = z - 2^64.
Proof.
  intros. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). change (2^64 `div` 2) with (2^63).
  rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma lts_lit a b : bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (bv_swrap 64 a <? bv_swrap 64 b).
Proof. unfold bv_lts. rewrite !Z_to_bv_signed. reflexivity. Qed.
