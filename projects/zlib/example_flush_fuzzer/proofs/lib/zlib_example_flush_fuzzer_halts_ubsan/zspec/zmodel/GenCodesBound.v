(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees TreeModel BuildTreeModel GenBitlenModel HuffSpec.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma lor_lt_pow2 : forall a b m, 0 <= m -> 0 <= a < 2 ^ m -> 0 <= b < 2 ^ m -> 0 <= Z.lor a b < 2 ^ m.
Proof.
  intros a b m Hm Ha Hb.
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|A0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B0]; [rewrite Z.lor_0_r; lia|].
  assert (P : 0 < Z.lor a b).
  { pose proof (Z.lor_nonneg a b). destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [apply Z.lor_eq_0_iff in E; lia | lia]. }
  apply (proj2 (Z.log2_lt_pow2 _ m P)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma bi_reverse_loop_bound : forall f code res len i,
  0 <= code -> 0 <= i -> 0 <= res < 2 ^ (i + 1) -> 1 <= len <= Z.of_nat f -> i + 1 + len <= 32 ->
  0 <= bi_reverse_loop f code res len < 2 ^ (i + len).
Proof.
  induction f as [|f IH]; intros code res len i Hc Hi Hres Hlen Hil; [cbn in Hlen; lia|].
  cbn [bi_reverse_loop].
  assert (B1 : 0 <= Z.land code 1 < 2 ^ (i + 1)).
  { split; [apply Z.land_nonneg; lia|]. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound code (2 ^ 1) ltac:(lia)). assert (2 ^ 1 <= 2 ^ (i + 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  pose proof (lor_lt_pow2 res (Z.land code 1) (i + 1) ltac:(lia) Hres B1) as L1.
  assert (S1 : wrap32 (Z.shiftl (Z.lor res (Z.land code 1)) 1) = 2 * Z.lor res (Z.land code 1)).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite wrap32_id; [lia|].
    assert (2 ^ (i + 1) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite S1.
  assert (R2 : 0 <= 2 * Z.lor res (Z.land code 1) < 2 ^ (i + 1 + 1)).
  { replace (2 ^ (i + 1 + 1)) with (2 * 2 ^ (i + 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). lia. }
  destruct (Z.ltb_spec 0 (len - 1)) as [Hl|Hl].
  - replace (i + len) with ((i + 1) + (len - 1)) by lia. apply IH; try lia. apply Z.shiftr_nonneg. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. replace (i + len) with (i + 1) by lia.
    rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Theorem bi_reverse_bound : forall code len, 0 <= code -> 1 <= len <= 15 -> 0 <= bi_reverse code len < 2 ^ len.
Proof.
  intros code len Hc Hl. unfold bi_reverse.
  pose proof (bi_reverse_loop_bound (Z.to_nat (Z.max len 1)) code 0 len 0 Hc ltac:(lia) ltac:(cbn; lia) ltac:(rewrite Z2Nat.id; lia) ltac:(lia)) as B.
  rewrite Z.add_0_l in B. exact B.
Qed.


Lemma tree_fc_set_Code : forall s t n v, tree_fc (set_Code s t n v) t = arr_set (tree_fc s t) n (wrap16 v).
Proof. intros s t n v. unfold set_Code, set_Freq. destruct t; destruct s; reflexivity. Qed.
Lemma tree_dl_set_Code : forall s t n v, tree_dl (set_Code s t n v) t = tree_dl s t.
Proof. intros s t n v. unfold set_Code, set_Freq. destruct t; destruct s; reflexivity. Qed.
Lemma Len_set_Code : forall s t n v m, Len (set_Code s t n v) t m = Len s t m.
Proof. intros. unfold Len. rewrite tree_dl_set_Code. reflexivity. Qed.

Lemma gen_codes_loop2_b15 : forall f s t nc mc n K,
  K <= arr_len (tree_fc s t) -> 0 <= n ->
  (forall i, 0 <= arr_get nc i) ->
  (forall j, 0 <= j <= mc -> Len s t j <> 0 -> 1 <= Len s t j <= 15) ->
  (forall i, 0 <= i < K -> 0 <= arr_get (tree_fc s t) i < 2 ^ 15) ->
  forall i, 0 <= i < K -> 0 <= arr_get (tree_fc (gen_codes_loop2 f s t nc mc n) t) i < 2 ^ 15.
Proof.
  induction f as [|f IH]; intros s t nc mc n K HK Hn Hnc HL HC i Hi; cbn [gen_codes_loop2]; [exact (HC i Hi)|].
  destruct (Z.leb_spec n mc) as [Hmc|Hmc]; [| exact (HC i Hi)].
  assert (HLn : Len s t n <> 0 -> 1 <= Len s t n <= 15) by (apply HL; lia).
  destruct (Z.eqb_spec (Len s t n) 0) as [E|E].
  - apply (IH s t nc mc (n + 1) K); try assumption. lia.
  - apply (IH _ t _ mc (n + 1) K).
    + rewrite tree_fc_set_Code, arr_len_set. exact HK.
    + lia.
    + intros k. destruct (Z.eq_dec (Len s t n) k) as [<-|NE].
      * destruct (Z.lt_ge_cases (Len s t n) (arr_len nc)) as [LT|GE].
        -- rewrite arr_get_set_same by (specialize (HLn E); lia). apply (proj1 (wrap16_range _)).
        -- rewrite arr_set_oob by lia. apply Hnc.
      * rewrite arr_get_set_other by exact NE. apply Hnc.
    + intros j Hj. rewrite Len_set_Code. apply HL. exact Hj.
    + intros k Hk. rewrite tree_fc_set_Code.
      destruct (Z.eq_dec n k) as [<-|NE].
      * rewrite arr_get_set_same by lia.
        pose proof (bi_reverse_bound (arr_get nc (Len s t n)) (Len s t n) (Hnc _) (HLn E)) as B.
        assert (2 ^ Len s t n <= 2 ^ 15) by (apply Z.pow_le_mono_r; specialize (HLn E); lia).
        rewrite wrap16_id; lia.
      * rewrite arr_get_set_other by exact NE. apply HC. exact Hk.
    + exact Hi.
Qed.

Lemma gen_codes_loop1_nonneg : forall f blc nc code bits,
  (forall i, 0 <= arr_get nc i) -> forall i, 0 <= arr_get (gen_codes_loop1 f blc nc code bits) i.
Proof.
  induction f as [|f IH]; intros blc nc code bits H i; cbn [gen_codes_loop1]; [apply H|].
  destruct (bits <=? MAX_BITS); [| apply H]. apply IH.
  intros k. destruct (Z.eq_dec bits k) as [<-|NE].
  - destruct (Z.lt_ge_cases bits (arr_len nc)) as [LT|GE]; [| rewrite arr_set_oob by lia; apply H].
    destruct (Z.le_gt_cases 0 bits); [rewrite arr_get_set_same by lia; apply (proj1 (wrap16_range _)) | rewrite arr_set_oob by lia; apply H].
  - rewrite arr_get_set_other by exact NE. apply H.
Qed.

Theorem gen_codes_b15 : forall s t mc K,
  K <= arr_len (tree_fc s t) ->
  (forall j, 0 <= j <= mc -> Len s t j <> 0 -> 1 <= Len s t j <= 15) ->
  (forall i, 0 <= i < K -> 0 <= arr_get (tree_fc s t) i < 2 ^ 15) ->
  forall i, 0 <= i < K -> 0 <= arr_get (tree_fc (gen_codes s t mc) t) i < 2 ^ 15.
Proof.
  intros s t mc K HK HL HC. unfold gen_codes. apply gen_codes_loop2_b15; try assumption; [lia|].
  apply gen_codes_loop1_nonneg. intros i. rewrite arr_get_make. lia.
Qed.
