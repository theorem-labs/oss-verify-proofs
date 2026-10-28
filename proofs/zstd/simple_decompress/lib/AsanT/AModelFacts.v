(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import bitvector.definitions.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma rz_log_small : forall n, 1 <= n <= 448 -> rz_log n = (if n <=? 48 then 0 else if n <=? 96 then 1 else 2).
Proof. intros n H. unfold rz_log. destruct (n <=? 48); [reflexivity|]. destruct (n <=? 96); [reflexivity|].
  replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma rz_log_range_small : forall n, 1 <= n <= 448 -> 0 <= rz_log n <= 2.
Proof. intros n H. rewrite rz_log_small by lia. destruct (n <=? 48); [lia|]. destruct (n <=? 96); lia. Qed.

Lemma rz_size_eq : forall n, rz_size n = 16 * 2 ^ rz_log n.
Proof. intros n. unfold rz_size. rewrite Z.shiftl_mul_pow2. reflexivity. unfold rz_log.
  repeat (destruct (_ <=? _)); lia. Qed.

Lemma rounded_size_eq : forall n, rounded_size n = (Z.max n 8 + 7) / 8 * 8.
Proof. intros n. unfold rounded_size, rup. f_equal. f_equal. lia. Qed.

Lemma small_facts : forall n, 1 <= n <= 448 ->
  is_primary n = true /\ needed_size n = rounded_size n + rz_size n
  /\ 16 <= rz_size n <= 64 /\ rz_size n = 16 * 2 ^ rz_log n
  /\ Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0
  /\ 24 <= needed_size n <= 512.
Proof.
  intros n H.
  pose proof (rz_log_range_small n H) as R. pose proof (rz_size_eq n) as S.
  assert (S2 : 16 <= rz_size n <= 64).
  { rewrite S. assert (2 ^ rz_log n = 1 \/ 2 ^ rz_log n = 2 \/ 2 ^ rz_log n = 4).
    { destruct (Z.eq_dec (rz_log n) 0) as [->|]; [left; reflexivity|]. destruct (Z.eq_dec (rz_log n) 1) as [->|]; [right; left; reflexivity|].
      replace (rz_log n) with 2 by lia. right; right; reflexivity. } lia. }
  pose proof (rounded_size_eq n) as RS.
  assert (RR : Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0).
  { rewrite RS. Z.div_mod_to_equations. lia. }
  assert (P : is_primary n = true).
  { unfold is_primary, needed0, K_MAX_SIZE. apply Z.leb_le. lia. }
  assert (NS : needed_size n = rounded_size n + rz_size n).
  { unfold needed_size. rewrite P. reflexivity. }
  assert (UP : rounded_size n + rz_size n <= 512).
  { rewrite S, RS. rewrite rz_log_small by lia.
    destruct (Z.leb_spec n 48); [cbn; Z.div_mod_to_equations; lia|].
    destruct (Z.leb_spec n 96); cbn; Z.div_mod_to_equations; lia. }
  rewrite NS. split; [exact P|]. split; [reflexivity|]. split; [lia|]. split; [exact S|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Lemma land_align8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
  intros x Hx.
  replace 18446744073709551608 with (Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
  replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma rounded_size_align : forall n, rounded_size n = Z.max n 8 + 7 - (Z.max n 8 + 7) mod 8.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma sllw_rz : forall n, 1 <= n <= 448 ->
  bv_swrap 32 (Z.shiftl 16 ((rz_log n mod 18446744073709551616) mod 32)) = rz_size n.
Proof.
  intros n N. pose proof (rz_log_range_small n N) as RLR. pose proof (rz_size_eq n) as RZE.
  rewrite !(Z.mod_small (rz_log n)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite RZE.
  assert (P4 : 2 ^ rz_log n <= 2 ^ 2) by (apply Z.pow_le_mono_r; lia).
  assert (P1 : 0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; lia).
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N (32 - 1)) with 2147483648 by reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma land_align8_48 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = x - x mod 8.
Proof.
  intros x Hx.
  replace 281474976710648 with (Z.ldiff (Z.ones 48) (Z.ones 3)) by reflexivity.
  replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 48) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 48; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma rz_size_small_cases : forall n, 1 <= n <= 448 -> rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64.
Proof.
  intros n N. rewrite rz_size_eq, (rz_log_small n N).
  destruct (n <=? 48); [left; reflexivity|]. destruct (n <=? 96); [right; left; reflexivity| right; right; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma amalloc_fast_eq : forall RESV st n c,
  1 <= n <= 448 -> class_id (needed_size n) = c -> 0 < c_count (get_cls st c) ->
  amalloc ATOP RESV st n =
    SRet (set_next (N.succ (a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)))
            (set_live (<[ a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) := CPrim c n ]>
                        (a_live (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)))
               (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)),
          Some (a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st))).
Proof.
  intros RESV st n c N HC POS. pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM. unfold cache_alloc. rewrite HC.
  replace (0 <? c_count (get_cls st c)) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma a_next_put_cls : forall c r st, a_next (put_cls c r st) = a_next st.
Proof. intros. reflexivity. Qed.
Lemma a_live_put_cls : forall c r st, a_live (put_cls c r st) = a_live st.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma class_id_small : forall s, s <= 512 -> class_id s = Z.shiftr (s + 31) 5.
Proof. intros s Hs. unfold class_id. replace (s <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma size_of_class_small : forall c, c <= 16 -> size_of_class c = 32 * c.
Proof. intros c Hc. unfold size_of_class. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma class_small_facts : forall n c, 1 <= n <= 448 -> class_id (needed_size n) = c ->
  1 <= c <= 16 /\ Z.shiftr (needed_size n + 31) 5 = c /\ size_of_class c = 32 * c /\ needed_size n <= size_of_class c <= 512.
Proof.
  intros n c N HC. pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  rewrite class_id_small in HC by lia.
  assert (C : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  pose proof (size_of_class_small c ltac:(lia)) as S.
  split; [exact C|]. split; [exact HC|]. split; [exact S|].
  rewrite S. rewrite <- HC. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.
Lemma max_cached_le16 : forall c, 1 <= c -> max_cached c <= 16.
Proof. intros c Hc. unfold max_cached. lia. Qed.
End CANSEC1.
