(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64.
Unset Nia Cache. Unset Nra Cache.
Import W64.
Open Scope Z_scope.
Unset Lia Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma wB_two63 : wB = two63.
Proof. reflexivity. Qed.

Lemma two63_eq : two63 = 2 ^ 63.
Proof. reflexivity. Qed.

Lemma two64_eq : two64 = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma bv_modulus_64 : bv_modulus 64 = two64.
Proof. reflexivity. Qed.

Lemma bv_half_modulus_64 : bv_half_modulus 64 = two63.
Proof. reflexivity. Qed.

Lemma wl_range : forall a, 0 <= to_Z (wl a) < two63.
Proof. intros a. rewrite <- wB_two63. apply to_Z_bounded. Qed.

Lemma int_range : forall i, 0 <= to_Z i < two63.
Proof. intros i. rewrite <- wB_two63. apply to_Z_bounded. Qed.

Lemma w2Z_range : forall a, 0 <= w2Z a < two64.
Proof.
  intros a. unfold w2Z. pose proof (wl_range a).
  unfold two63, two64 in *. destruct (wt a); lia.
Qed.

Lemma wbv_unsigned : forall a, bv_unsigned (wbv a) = w2Z a.
Proof.
  intros a. unfold wbv. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  rewrite bv_modulus_64. apply w2Z_range.
Qed.

Lemma Z2w_ok : forall z, w2Z (Z2w z) = z mod two64.
Proof.
  intros z. unfold Z2w, w2Z. cbn [wt wl].
  rewrite of_Z_spec, wB_two63.
  assert (Hz : 0 <= z mod two64 < two64) by (apply Z.mod_pos_bound; reflexivity).
  set (z' := z mod two64) in *. clearbody z'.
  unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 z').
  - rewrite <- (Z.mod_unique_pos z' 9223372036854775808 1 (z' - 9223372036854775808)) by lia.
    rewrite Z.mod_small; lia.
  - rewrite (Z.mod_small z') by lia. rewrite Z.mod_small; lia.
Qed.

Lemma w2Z_wt : forall a, wt a = Z.leb two63 (w2Z a).
Proof.
  intros a. unfold w2Z. pose proof (wl_range a). unfold two63 in *.
  destruct (wt a); symmetry; [apply Z.leb_le; lia | apply Z.leb_gt; lia].
Qed.

Lemma w2Z_wl : forall a, to_Z (wl a) = w2Z a mod two63.
Proof.
  intros a. unfold w2Z. pose proof (wl_range a). unfold two63 in *.
  destruct (wt a).
  - apply (Z.mod_unique_pos _ _ 1); lia.
  - rewrite Z.mod_small; lia.
Qed.

Lemma Z2w_w2Z : forall a, Z2w (w2Z a) = a.
Proof.
  intros a. unfold Z2w. rewrite (Z.mod_small _ two64) by apply w2Z_range.
  rewrite <- w2Z_wt, <- w2Z_wl, of_to_Z. destruct a; reflexivity.
Qed.

Lemma w2Z_inj : forall a b, w2Z a = w2Z b -> a = b.
Proof. intros a b E. rewrite <- (Z2w_w2Z a), <- (Z2w_w2Z b), E. reflexivity. Qed.

Lemma bv2w_wbv : forall b : word, wbv (bv2w b) = b.
Proof.
  intros b. unfold bv2w, wbv. rewrite Z2w_ok.
  rewrite (Z.mod_small _ two64).
  - apply Z_to_bv_bv_unsigned.
  - rewrite <- bv_modulus_64. apply bv_unsigned_in_range.
Qed.

Lemma wbv_bv2w : forall a, bv2w (wbv a) = a.
Proof. intros a. unfold bv2w. rewrite wbv_unsigned. apply Z2w_w2Z. Qed.

Lemma wbv_inj : forall a b, wbv a = wbv b -> a = b.
Proof.
  intros a b E. apply w2Z_inj. rewrite <- !wbv_unsigned, E. reflexivity.
Qed.

Lemma wbv_eq_of_w2Z : forall a (b : word), w2Z a = bv_unsigned b -> wbv a = b.
Proof.
  intros a b E. apply bv_eq. rewrite wbv_unsigned. exact E.
Qed.

Lemma wbv_eq_iff : forall a (b : word), wbv a = b <-> w2Z a = bv_unsigned b.
Proof.
  intros a b; split; [intros <-; symmetry; apply wbv_unsigned | apply wbv_eq_of_w2Z].
Qed.

Lemma weqb_ok : forall a b, weqb a b = true <-> a = b.
Proof.
  intros a b. unfold weqb. rewrite andb_true_iff, Bool.eqb_true_iff, Uint63.eqb_spec.
  split.
  - intros [E1 E2]. destruct a, b; cbn in *; congruence.
  - intros ->. auto.
Qed.

Lemma weqb_w2Z : forall a b, weqb a b = true <-> w2Z a = w2Z b.
Proof.
  intros a b. rewrite weqb_ok. split; [intros ->; reflexivity | apply w2Z_inj].
Qed.

Lemma weqb_refl : forall a, weqb a a = true.
Proof. intros a. apply weqb_ok. reflexivity. Qed.

Lemma weqb_eqb : forall a b, weqb a b = Z.eqb (w2Z a) (w2Z b).
Proof.
  intros a b. destruct (weqb a b) eqn:E.
  - apply weqb_w2Z in E. rewrite E, Z.eqb_refl. reflexivity.
  - symmetry. apply Z.eqb_neq. intros E'. apply weqb_w2Z in E'. congruence.
Qed.

Lemma wltu_w2Z : forall a b, wltu a b = Z.ltb (w2Z a) (w2Z b).
Proof.
  intros a b. unfold wltu, w2Z.
  pose proof (wl_range a). pose proof (wl_range b). unfold two63 in *.
  destruct (wt a), (wt b);
  first [ destruct (ltbP (wl a) (wl b)) | idtac ]; symmetry;
  first [ apply Z.ltb_lt; lia | apply Z.ltb_ge; lia ].
Qed.

Lemma wltu_ok : forall a b, wltu a b = bv_ltu (wbv a) (wbv b).
Proof. intros a b. unfold bv_ltu. rewrite !wbv_unsigned. apply wltu_w2Z. Qed.

Lemma w2Zs_swrap : forall a, bv_swrap 64 (w2Z a) = w2Zs a.
Proof.
  intros a. unfold w2Zs, bv_swrap, bv_wrap. rewrite bv_modulus_64, bv_half_modulus_64.
  unfold w2Z. pose proof (wl_range a). unfold two63, two64 in *.
  destruct (wt a).
  - rewrite <- (Z.mod_unique_pos _ _ 1 (to_Z (wl a))); lia.
  - rewrite Z.mod_small; lia.
Qed.

Lemma wbv_signed : forall a, bv_signed (wbv a) = w2Zs a.
Proof. intros a. unfold bv_signed. rewrite wbv_unsigned. apply w2Zs_swrap. Qed.

Lemma wlts_w2Zs : forall a b, wlts a b = Z.ltb (w2Zs a) (w2Zs b).
Proof.
  intros a b. unfold wlts, w2Zs, w2Z.
  pose proof (wl_range a). pose proof (wl_range b). unfold two63, two64 in *.
  destruct (wt a), (wt b);
  first [ destruct (ltbP (wl a) (wl b)) | idtac ]; symmetry;
  first [ apply Z.ltb_lt; lia | apply Z.ltb_ge; lia ].
Qed.

Lemma wlts_ok : forall a b, wlts a b = bv_lts (wbv a) (wbv b).
Proof. intros a b. unfold bv_lts. rewrite !wbv_signed. apply wlts_w2Zs. Qed.

Lemma wbranch_ok : forall c a b, wbranch c a b = branch_taken c (wbv a) (wbv b).
Proof.
  intros c a b. destruct c; cbn [wbranch branch_taken].
  - unfold bv_eqb. rewrite !wbv_unsigned. apply weqb_eqb.
  - unfold bv_eqb. rewrite !wbv_unsigned, weqb_eqb. reflexivity.
  - apply wlts_ok.
  - rewrite wlts_ok. reflexivity.
  - apply wltu_ok.
  - rewrite wltu_ok. reflexivity.
Qed.

Lemma testbit_high : forall a n m, 0 <= a < 2 ^ n -> n <= m -> Z.testbit a m = false.
Proof.
  intros a n m Ha Hm.
  assert (Hn : 0 <= n).
  { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha; lia. }
  rewrite <- (Z.mod_small a (2 ^ n)) by lia.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma testbit_int_high : forall i m, 63 <= m -> Z.testbit (to_Z i) m = false.
Proof. intros i m Hm. apply (testbit_high _ 63); [apply int_range | exact Hm]. Qed.

Lemma tb_mul_pow2 : forall a n m, 0 <= n -> 0 <= m ->
  Z.testbit (a * 2 ^ n) m = (n <=? m) && Z.testbit a (m - n).
Proof.
  intros a n m Hn Hm. rewrite Z.mul_pow2_bits by lia.
  destruct (Z.leb_spec n m); [reflexivity|]. apply Z.testbit_neg_r. lia.
Qed.

Lemma tb_shiftl : forall a n m, 0 <= n -> 0 <= m ->
  Z.testbit (Z.shiftl a n) m = (n <=? m) && Z.testbit a (m - n).
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. apply tb_mul_pow2; lia. Qed.

Lemma tb_shiftr : forall a n m, 0 <= n -> 0 <= m ->
  Z.testbit (Z.shiftr a n) m = Z.testbit a (m + n).
Proof. intros. apply Z.shiftr_spec; lia. Qed.

Lemma w2Z_div_two63 : forall a, w2Z a / 2 ^ 63 = (if wt a then 1 else 0).
Proof.
  intros a. unfold w2Z. pose proof (wl_range a). rewrite two63_eq in *.
  destruct (wt a).
  - symmetry. apply (Z.div_unique_pos _ _ _ (to_Z (wl a))); lia.
  - apply Z.div_small. lia.
Qed.

Lemma testbit_w2Z : forall a m, 0 <= m ->
  Z.testbit (w2Z a) m =
  if m <? 63 then Z.testbit (to_Z (wl a)) m else if m =? 63 then wt a else false.
Proof.
  intros a m Hm. destruct (Z.ltb_spec m 63).
  - rewrite <- (Z.mod_pow2_bits_low (w2Z a) 63 m) by lia.
    rewrite <- two63_eq, <- w2Z_wl. reflexivity.
  - replace m with ((m - 63) + 63) at 1 by lia.
    rewrite <- Z.div_pow2_bits by lia. rewrite w2Z_div_two63.
    destruct (wt a).
    + change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec 0 (m - 63)), (Z.eqb_spec m 63); lia || reflexivity.
    + rewrite Z.bits_0. destruct (m =? 63); reflexivity.
Qed.

Lemma to_Z_ones63 : to_Z ones63 = Z.ones 63. Proof. reflexivity. Qed.
Lemma to_Z_mask32 : to_Z mask32 = Z.ones 32. Proof. reflexivity. Qed.
Lemma to_Z_mask31 : to_Z mask31 = Z.ones 31. Proof. reflexivity. Qed.
Lemma to_Z_bit31i : to_Z bit31i = 2 ^ 31. Proof. reflexivity. Qed.
Lemma to_Z_bit62i : to_Z bit62i = 2 ^ 62. Proof. reflexivity. Qed.
Lemma to_Z_hi31of63 : to_Z hi31of63 = Z.ones 31 * 2 ^ 32. Proof. reflexivity. Qed.
Lemma lit_4294967295 : 4294967295 = Z.ones 32. Proof. reflexivity. Qed.
Lemma lit_4294967296 : 4294967296 = 2 ^ 32. Proof. reflexivity. Qed.
Lemma lit_2147483648 : 2147483648 = 2 ^ 31. Proof. reflexivity. Qed.

Lemma tb_ones : forall n m, 0 <= n -> 0 <= m -> Z.testbit (Z.ones n) m = (m <? n).
Proof. intros. apply Z.testbit_ones_nonneg; lia. Qed.

Lemma tb_m1 : forall m, 0 <= m -> Z.testbit (-1) m = true.
Proof. intros. apply Z.bits_m1. lia. Qed.

Ltac w64_eval_lits :=
  change (to_Z 0%uint63) with 0 in *;
  change (to_Z 1%uint63) with 1 in *;
  change (to_Z 3%uint63) with 3 in *;
  change (to_Z 8%uint63) with 8 in *;
  change (to_Z 31%uint63) with 31 in *;
  change (to_Z 32%uint63) with 32 in *;
  change (to_Z 63%uint63) with 63 in *.

Ltac w64_zify_step :=
  first
    [ rewrite land_spec'
    | rewrite lor_spec'
    | rewrite lxor_spec'
    | rewrite lsl_spec
    | rewrite lsr_spec
    | rewrite add_spec
    | rewrite sub_spec
    | rewrite mul_spec
    | rewrite of_Z_spec
    | rewrite bitE
    | rewrite wB_two63 ].
Ltac w64_consts :=
  rewrite ?to_Z_ones63, ?to_Z_mask32, ?to_Z_mask31, ?to_Z_bit31i, ?to_Z_bit62i, ?to_Z_hi31of63,
    ?two63_eq, ?two64_eq in *;
  change 9223372036854775808 with (2 ^ 63) in *;
  change 18446744073709551616 with (2 ^ 64) in *.
Ltac w64_mod_small :=
  repeat match goal with
  | |- context [?a mod ?b] => rewrite (Z.mod_small a b) by lia
  end.
Ltac w64_zify := repeat w64_zify_step; w64_consts; w64_eval_lits; w64_mod_small.

Ltac w64_tb_step :=
  match goal with
  | |- context [Z.testbit (Z.land ?a ?b) ?m] => rewrite (Z.land_spec a b m)
  | |- context [Z.testbit (Z.lor ?a ?b) ?m] => rewrite (Z.lor_spec a b m)
  | |- context [Z.testbit (Z.lxor ?a ?b) ?m] => rewrite (Z.lxor_spec a b m)
  | |- context [Z.testbit (Z.lnot ?a) ?m] => rewrite (Z.lnot_spec a m) by lia
  | |- context [Z.testbit (?a mod 2 ^ ?n) ?m] => rewrite (Z.testbit_mod_pow2 a n m) by lia
  | |- context [Z.testbit (?a / 2 ^ ?n) ?m] => rewrite (Z.div_pow2_bits a n m) by lia
  | |- context [Z.testbit (?a * 2 ^ ?n) ?m] => rewrite (tb_mul_pow2 a n m) by lia
  | |- context [Z.testbit (Z.shiftl ?a ?n) ?m] => rewrite (tb_shiftl a n m) by lia
  | |- context [Z.testbit (Z.shiftr ?a ?n) ?m] => rewrite (tb_shiftr a n m) by lia
  | |- context [Z.testbit (Z.ones ?n) ?m] => rewrite (tb_ones n m) by lia
  | |- context [Z.testbit (2 ^ ?n) ?m] => rewrite (Z.pow2_bits_eqb n m) by lia
  | |- context [Z.testbit 0 ?m] => rewrite (Z.bits_0 m)
  | |- context [Z.testbit 1 ?m] =>
      change (Z.testbit 1 m) with (Z.testbit (2 ^ 0) m); rewrite (Z.pow2_bits_eqb 0 m) by lia
  | |- context [Z.testbit (-1) ?m] => rewrite (tb_m1 m) by lia
  | |- context [Z.testbit (w2Z ?a) ?m] => rewrite (testbit_w2Z a m) by lia; cbn [wt wl]
  end.
Ltac w64_tb := repeat w64_tb_step.

Ltac w64_bcase :=
  repeat match goal with
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec0 x y); try lia
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec0 x y); try lia
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
  end; cbn [andb orb xorb negb].

Ltac w64_tb_idx :=
  repeat match goal with
  | |- context [Z.testbit (to_Z ?x) ?i] =>
      rewrite (testbit_int_high x i) by lia
  | |- context [Z.testbit ?x ?i] =>
      rewrite (Z.testbit_neg_r x i) by lia
  | H : 0 <= ?x < 2 ^ ?n |- context [Z.testbit ?x ?i] =>
      rewrite (testbit_high x n i H) by lia
  | H : ?x < 2 ^ ?n |- context [Z.testbit ?x ?i] =>
      rewrite (testbit_high x n i) by lia
  end;
  repeat match goal with
  | |- context [Z.testbit ?x ?i] =>
      match goal with
      | |- context [Z.testbit x ?j] =>
          tryif constr_eq i j then fail
          else replace (Z.testbit x j) with (Z.testbit x i) by (f_equal; lia)
      end
  end.

Ltac w64_bfin :=
  cbn [andb orb xorb negb];
  try reflexivity;
  repeat match goal with
  | |- context [Z.testbit ?x ?i] => destruct (Z.testbit x i); cbn [andb orb xorb negb]; try reflexivity
  | |- context [if ?b then _ else _] => destruct b; cbn [andb orb xorb negb]; try reflexivity
  | |- context [wt ?x] => destruct (wt x); cbn [andb orb xorb negb]; try reflexivity
  | b : bool |- _ => destruct b; cbn [andb orb xorb negb]; try reflexivity
  end.

Ltac w64_bitblast0 :=
  apply Z.bits_inj'; intros m Hm; w64_tb; w64_zify; w64_tb; w64_bcase; w64_tb; w64_zify; w64_bcase; w64_tb_idx.
Ltac w64_bitblast := w64_bitblast0; w64_bfin.

Lemma wand_ok : forall a b, w2Z (wand a b) = Z.land (w2Z a) (w2Z b).
Proof. intros a b. unfold wand. w64_bitblast. Qed.

Lemma wor_ok : forall a b, w2Z (wor a b) = Z.lor (w2Z a) (w2Z b).
Proof. intros a b. unfold wor. w64_bitblast. Qed.

Lemma wxor_ok : forall a b, w2Z (wxor a b) = Z.lxor (w2Z a) (w2Z b).
Proof. intros a b. unfold wxor. w64_bitblast. Qed.

Lemma wnot_lnot : forall a, w2Z (wnot a) = Z.lnot (w2Z a) mod 2 ^ 64.
Proof. intros a. unfold wnot. w64_bitblast. Qed.

Lemma wnot_ok : forall a, w2Z (wnot a) = two64 - 1 - w2Z a.
Proof.
  intros a. rewrite wnot_lnot. unfold Z.lnot. pose proof (w2Z_range a).
  rewrite two64_eq in *. symmetry. apply Z.mod_unique_pos with (q := -1); lia.
Qed.

Lemma mod_cases2 : forall x m, 0 <= x < 2 * m -> x mod m = if x <? m then x else x - m.
Proof.
  intros x m H. destruct (Z.ltb_spec x m).
  - apply Z.mod_small. lia.
  - symmetry. apply Z.mod_unique_pos with (q := 1); lia.
Qed.

Lemma mod_cases_neg : forall x m, - m <= x < m -> x mod m = if x <? 0 then x + m else x.
Proof.
  intros x m H. destruct (Z.ltb_spec x 0).
  - symmetry. apply Z.mod_unique_pos with (q := -1); lia.
  - apply Z.mod_small. lia.
Qed.

Ltac w64_bcase_full :=
  repeat match goal with
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec0 x y); try lia
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec0 x y); try lia
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
  end.

Lemma wadd_ok : forall a b, w2Z (wadd a b) = (w2Z a + w2Z b) mod two64.
Proof.
  intros a b. unfold wadd, w2Z. cbn [wt wl].
  pose proof (wl_range a). pose proof (wl_range b).
  destruct (ltbP (wl a + wl b)%uint63 (wl a)) as [C|C]; revert C;
  rewrite add_spec, wB_two63; unfold two63, two64 in *;
  rewrite (mod_cases2 _ 9223372036854775808) by lia;
  rewrite (mod_cases2 _ 18446744073709551616) by (destruct (wt a), (wt b); lia);
  destruct (wt a), (wt b); cbn [xorb]; w64_bcase_full.
Qed.

Lemma wsub_ok : forall a b, w2Z (wsub a b) = (w2Z a - w2Z b) mod two64.
Proof.
  intros a b. unfold wsub, w2Z. cbn [wt wl].
  pose proof (wl_range a). pose proof (wl_range b).
  destruct (ltbP (wl a) (wl b)) as [C|C]; revert C;
  rewrite sub_spec, wB_two63; unfold two63, two64 in *;
  rewrite (mod_cases_neg _ 9223372036854775808) by lia;
  rewrite (mod_cases_neg _ 18446744073709551616) by (destruct (wt a), (wt b); lia);
  destruct (wt a), (wt b); cbn [xorb]; w64_bcase_full.
Qed.

Lemma wneg_ok : forall a, w2Z (wneg a) = (- w2Z a) mod two64.
Proof. intros a. unfold wneg. rewrite wsub_ok. reflexivity. Qed.

Lemma shamt6_ok : forall b, to_Z (shamt6 b) = Z.land (w2Z b) 63.
Proof. intros b. unfold shamt6. w64_zify. change 63 with (Z.ones 6). w64_bitblast. Qed.

Lemma shamt6_range : forall b, 0 <= to_Z (shamt6 b) <= 63.
Proof.
  intros b. rewrite shamt6_ok. change 63 with (Z.ones 6) at 1 2. rewrite Z.land_ones by lia.
  change (2 ^ 6) with 64. pose proof (Z.mod_pos_bound (w2Z b) 64). lia.
Qed.

Lemma wsll_k_ok : forall a k, to_Z k <= 63 ->
  w2Z (wsll_k a k) = (w2Z a * 2 ^ to_Z k) mod 2 ^ 64.
Proof.
  intros a k Hk. pose proof (int_range k). pose proof (w2Z_range a). rewrite two64_eq in *.
  unfold wsll_k.
  destruct (eqbP k 0) as [E|E]; change (to_Z 0) with 0 in E.
  - rewrite E, Z.pow_0_r, Z.mul_1_r, Z.mod_small by lia. reflexivity.
  - w64_bitblast.
Qed.

Lemma wsrl_k_ok : forall a k, to_Z k <= 63 ->
  w2Z (wsrl_k a k) = w2Z a / 2 ^ to_Z k.
Proof.
  intros a k Hk. pose proof (int_range k). pose proof (w2Z_range a). rewrite two64_eq in *.
  unfold wsrl_k.
  destruct (eqbP k 0) as [E|E]; change (to_Z 0) with 0 in E.
  - rewrite E, Z.pow_0_r, Z.div_1_r. reflexivity.
  - destruct a as [ta la]; cbn [wt wl] in *; destruct ta; w64_bitblast.
Qed.

Lemma testbit_sub_pow2 : forall u n j, 0 <= u < 2 ^ n -> 0 <= n -> 0 <= j ->
  Z.testbit (u - 2 ^ n) j = if j <? n then Z.testbit u j else true.
Proof.
  intros u n j Hu Hn Hj. destruct (Z.ltb_spec j n).
  - rewrite <- (Z.mod_pow2_bits_low (u - 2 ^ n) n j) by lia.
    f_equal. symmetry. apply Z.mod_unique_pos with (q := -1); lia.
  - replace j with ((j - n) + n) by lia. rewrite <- Z.div_pow2_bits by lia.
    replace ((u - 2 ^ n) / 2 ^ n) with (-1).
    + apply Z.bits_m1. lia.
    + apply Z.div_unique_pos with (r := u); lia.
Qed.

Lemma testbit_w2Zs : forall a m, 0 <= m ->
  Z.testbit (w2Zs a) m = if m <? 63 then Z.testbit (to_Z (wl a)) m else wt a.
Proof.
  intros a m Hm. unfold w2Zs. pose proof (w2Z_range a) as R. rewrite two64_eq in *.
  pose proof (w2Z_wt a) as T. rewrite two63_eq in T.
  destruct a as [ta la]; cbn [wt wl] in *; destruct ta.
  - rewrite testbit_sub_pow2 by lia. rewrite testbit_w2Z by lia. cbn [wt wl].
    symmetry in T. apply Z.leb_le in T.
    w64_bcase. destruct (Z.testbit (to_Z la) m); reflexivity.
  - rewrite testbit_w2Z by lia. cbn [wt wl]. symmetry in T. apply Z.leb_gt in T.
    w64_bcase. reflexivity.
Qed.

Ltac w64_tb_step2 :=
  match goal with
  | |- context [Z.testbit (w2Zs ?a) ?m] => rewrite (testbit_w2Zs a m) by lia; cbn [wt wl]
  end.
Ltac w64_tb ::= repeat first [w64_tb_step | w64_tb_step2].

Lemma wsra_k_ok : forall a k, to_Z k <= 63 ->
  w2Z (wsra_k a k) = (Z.shiftr (w2Zs a) (to_Z k)) mod 2 ^ 64.
Proof.
  intros a k Hk. pose proof (int_range k). pose proof (w2Z_range a). rewrite two64_eq in *.
  unfold wsra_k.
  destruct (eqbP k 0) as [E|E]; change (to_Z 0) with 0 in E.
  - rewrite E, Z.shiftr_0_r. unfold w2Zs. rewrite two64_eq. destruct (wt a).
    + apply Z.mod_unique_pos with (q := -1); lia.
    + rewrite Z.mod_small by lia. reflexivity.
  - destruct (wt a) eqn:T.
    + unfold wsrl_k. replace (PrimInt63.eqb k 0) with false by (symmetry; apply eqb_false_spec; intros ->; apply E; reflexivity).
      rewrite T. destruct a as [ta la]; cbn [wt wl] in *; subst ta. w64_bitblast.
    + rewrite wsrl_k_ok by lia. destruct a as [ta la]; cbn [wt wl] in *; subst ta. w64_bitblast.
Qed.

Lemma wofbool_ok : forall c, w2Z (wofbool c) = if c then 1 else 0.
Proof. intros [|]; reflexivity. Qed.

Lemma shamt6_bv : forall b,
  bv_unsigned (bv_and (wbv b) (Z_to_bv 64 63)) = to_Z (shamt6 b).
Proof.
  intros b. rewrite bv_and_unsigned, Z_to_bv_unsigned, wbv_unsigned, shamt6_ok. reflexivity.
Qed.

Lemma walu_ok : forall op a b, wbv (walu op a b) = alu64 op (wbv a) (wbv b).
Proof.
  intros op a b. apply wbv_eq_of_w2Z. unfold alu64, alu. destruct op; cbn [walu].
  - rewrite bv_add_unsigned, !wbv_unsigned. apply wadd_ok.
  - rewrite bv_sub_unsigned, !wbv_unsigned. apply wsub_ok.
  - rewrite bv_shiftl_unsigned, shamt6_bv, wbv_unsigned, Z.shiftl_mul_pow2 by apply int_range.
    unfold wsll. apply wsll_k_ok. apply shamt6_range.
  - rewrite <- wlts_ok, wofbool_ok. destruct (wlts a b); reflexivity.
  - rewrite <- wltu_ok, wofbool_ok. destruct (wltu a b); reflexivity.
  - rewrite bv_xor_unsigned, !wbv_unsigned. apply wxor_ok.
  - rewrite bv_shiftr_unsigned, shamt6_bv, wbv_unsigned, Z.shiftr_div_pow2 by apply int_range.
    unfold wsrl. apply wsrl_k_ok. apply shamt6_range.
  - rewrite bv_ashiftr_unsigned, shamt6_bv, wbv_signed.
    unfold wsra. apply wsra_k_ok. apply shamt6_range.
  - rewrite bv_or_unsigned, !wbv_unsigned. apply wor_ok.
  - rewrite bv_and_unsigned, !wbv_unsigned. apply wand_ok.
Qed.

Lemma lowbits_combine : forall l Q, 0 <= l < 2 ^ 63 ->
  (l + 2 ^ 63 * Q) mod 2 ^ 64 = (if Z.odd Q then 2 ^ 63 else 0) + l.
Proof.
  intros l Q Hl.
  pose proof (Z.div_mod Q 2 ltac:(lia)) as E. rewrite Zmod_odd in E.
  symmetry. apply Z.mod_unique_pos with (q := Q / 2).
  - destruct (Z.odd Q); lia.
  - rewrite E at 1. change (2 ^ 64) with (2 * 2 ^ 63). destruct (Z.odd Q); lia.
Qed.

Lemma wmul_ok : forall a b, w2Z (wmul a b) = (w2Z a * w2Z b) mod two64.
Proof.
  intros a b. unfold wmul.
  pose proof (mulc_spec (wl a) (wl b)) as HM.
  destruct (mulc (wl a) (wl b)) as [h l]. cbn [fst snd] in HM.
  pose proof (wl_range a). pose proof (wl_range b). pose proof (int_range l).
  unfold w2Z; cbn [wt wl]. rewrite wB_two63, two63_eq, two64_eq in *.
  rewrite !bitE. change (to_Z 0) with 0. rewrite !Z.bit0_odd.
  destruct (wt a), (wt b); cbn [andb].
  - transitivity ((to_Z l + 2 ^ 63 * (to_Z h + (to_Z (wl b) + to_Z (wl a)) + 2 * 2 ^ 62)) mod 2 ^ 64).
    + rewrite lowbits_combine by lia. rewrite Z.odd_add_mul_2, !Z.odd_add. reflexivity.
    + f_equal. lia.
  - transitivity ((to_Z l + 2 ^ 63 * (to_Z h + to_Z (wl b))) mod 2 ^ 64).
    + rewrite lowbits_combine by lia. rewrite !Z.odd_add, xorb_false_r. reflexivity.
    + f_equal. lia.
  - transitivity ((to_Z l + 2 ^ 63 * (to_Z h + to_Z (wl a))) mod 2 ^ 64).
    + rewrite lowbits_combine by lia. rewrite !Z.odd_add, xorb_false_l. reflexivity.
    + f_equal. lia.
  - transitivity ((to_Z l + 2 ^ 63 * (to_Z h)) mod 2 ^ 64).
    + rewrite lowbits_combine by lia. rewrite xorb_false_r. reflexivity.
    + f_equal. lia.
Qed.

Lemma w2Z_wzero : w2Z wzero = 0.
Proof. reflexivity. Qed.

Lemma weqb_wzero : forall b, weqb b wzero = Z.eqb (w2Z b) 0.
Proof. intros b. rewrite weqb_eqb, w2Z_wzero. reflexivity. Qed.

Lemma wmd_ok : forall op a b, wbv (wmd op a b) = mul_div op (wbv a) (wbv b).
Proof.
  intros op a b. apply wbv_eq_of_w2Z. unfold mul_div.
  rewrite !wbv_unsigned, <- weqb_wzero.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb.
  destruct op; cbn [wmd].
  - rewrite bv_mul_unsigned, !wbv_unsigned. apply wmul_ok.
  - unfold bv_mulhss. rewrite Z_to_bv_unsigned, !wbv_signed. apply Z2w_ok.
  - unfold bv_mulhsu. rewrite Z_to_bv_unsigned, wbv_signed, wbv_unsigned. apply Z2w_ok.
  - unfold bv_mulhuu. rewrite Z_to_bv_unsigned, !wbv_unsigned. apply Z2w_ok.
  - destruct (weqb b wzero) eqn:E.
    + rewrite Z_to_bv_unsigned. apply Z2w_ok.
    + rewrite bv_quots_unsigned, !wbv_signed. apply Z2w_ok.
  - destruct (weqb b wzero) eqn:E.
    + rewrite Z_to_bv_unsigned. apply Z2w_ok.
    + rewrite bv_divu_unsigned, !wbv_unsigned, Z2w_ok.
      rewrite weqb_wzero in E. apply Z.eqb_neq in E.
      apply Z.mod_small. split.
      * apply Z.div_pos; lia.
      * apply Z.le_lt_trans with (m := w2Z a); [|lia].
        apply Z.div_le_upper_bound; [lia|]. nia.
  - destruct (weqb b wzero) eqn:E.
    + symmetry; apply wbv_unsigned.
    + rewrite bv_rems_unsigned, !wbv_signed. apply Z2w_ok.
  - destruct (weqb b wzero) eqn:E.
    + symmetry; apply wbv_unsigned.
    + rewrite bv_modu_unsigned, !wbv_unsigned, Z2w_ok.
      rewrite weqb_wzero in E. apply Z.eqb_neq in E.
      apply Z.mod_small. pose proof (Z.mod_pos_bound (w2Z a) (w2Z b)). lia.
Qed.

Ltac w64_tb_step3 :=
  match goal with
  | |- context [Z.testbit (?u - 2 ^ ?n) ?m] => rewrite (testbit_sub_pow2 u n m) by lia
  end.
Ltac w64_tb ::= repeat first [w64_tb_step | w64_tb_step2 | w64_tb_step3].

Lemma lt_pow2_of_testbit : forall x n, 0 <= n ->
  (forall m, n <= m -> Z.testbit x m = false) -> 0 <= x < 2 ^ n.
Proof.
  intros x n Hn Hb. replace x with (x mod 2 ^ n).
  - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - apply Z.bits_inj'. intros m Hm. rewrite Z.testbit_mod_pow2 by lia.
    destruct (Z.ltb_spec m n); [reflexivity|]. symmetry. apply Hb. lia.
Qed.

Lemma lxor_range : forall x y n, 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lxor x y < 2 ^ n.
Proof.
  intros x y n Hx Hy.
  assert (Hn : 0 <= n) by (destruct (Z.le_gt_cases 0 n); [assumption|]; rewrite Z.pow_neg_r in Hx; lia).
  apply lt_pow2_of_testbit; [lia|]. intros m Hm.
  rewrite Z.lxor_spec, !(testbit_high _ n) by lia. reflexivity.
Qed.

Lemma lor_range : forall x y n, 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
  intros x y n Hx Hy.
  assert (Hn : 0 <= n) by (destruct (Z.le_gt_cases 0 n); [assumption|]; rewrite Z.pow_neg_r in Hx; lia).
  apply lt_pow2_of_testbit; [lia|]. intros m Hm.
  rewrite Z.lor_spec, !(testbit_high _ n) by lia. reflexivity.
Qed.

Lemma land_range_l : forall x y n, 0 <= x < 2 ^ n -> 0 <= Z.land x y < 2 ^ n.
Proof.
  intros x y n Hx.
  assert (Hn : 0 <= n) by (destruct (Z.le_gt_cases 0 n); [assumption|]; rewrite Z.pow_neg_r in Hx; lia).
  apply lt_pow2_of_testbit; [lia|]. intros m Hm.
  rewrite Z.land_spec, !(testbit_high _ n) by lia. reflexivity.
Qed.

Lemma land_range_r : forall x y n, 0 <= y < 2 ^ n -> 0 <= Z.land x y < 2 ^ n.
Proof. intros. rewrite Z.land_comm. apply land_range_l. assumption. Qed.

Lemma testbit_top : forall u n, 0 <= n -> 0 <= u < 2 ^ (n + 1) ->
  Z.testbit u n = (2 ^ n <=? u).
Proof.
  intros u n Hn Hu. rewrite Z.testbit_eqb by lia.
  rewrite Z.pow_add_r, Z.pow_1_r in Hu by lia.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn).
  destruct (Z.leb_spec (2 ^ n) u).
  - replace (u / 2 ^ n) with 1; [reflexivity|]. apply Z.div_unique_pos with (r := u - 2 ^ n); lia.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma lo32_range : forall a, 0 <= to_Z (lo32 a) < 2 ^ 32.
Proof.
  intros a. unfold lo32. rewrite land_spec', to_Z_mask32, Z.land_ones by lia.
  apply Z.mod_pos_bound. reflexivity.
Qed.

Lemma lo32_mod : forall a, to_Z (lo32 a) = w2Z a mod 2 ^ 32.
Proof. intros a. unfold lo32. w64_bitblast. Qed.

Lemma low32_unsigned : forall a, bv_unsigned (low32 (wbv a)) = to_Z (lo32 a).
Proof.
  intros a. unfold low32. rewrite bv_extract_unsigned, wbv_unsigned, Z.shiftr_0_r, lo32_mod.
  reflexivity.
Qed.

Lemma lo32_ok : forall a,
  to_Z (lo32 a) = w2Z a mod 2 ^ 32 /\ Z_to_bv 32 (to_Z (lo32 a)) = low32 (wbv a).
Proof.
  intros a. split; [apply lo32_mod|].
  apply bv_eq. rewrite low32_unsigned, Z_to_bv_unsigned. apply bv_wrap_small. apply lo32_range.
Qed.

Definition sx32Z (u : Z) : Z := if 2 ^ 31 <=? u then (u - 2 ^ 32) mod 2 ^ 64 else u.

Lemma swrap32 : forall u, 0 <= u < 2 ^ 32 ->
  bv_swrap 32 u = if 2 ^ 31 <=? u then u - 2 ^ 32 else u.
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.leb_spec (2 ^ 31) u).
  - rewrite <- (Z.mod_unique_pos (u + 2 ^ 31) (2 ^ 32) 1 (u + 2 ^ 31 - 2 ^ 32)); lia.
  - rewrite Z.mod_small; lia.
Qed.

Lemma sext32_unsigned : forall r : bv 32, bv_unsigned (sext 64 r) = sx32Z (bv_unsigned r).
Proof.
  intros r. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed.
  pose proof (bv_unsigned_in_range 32 r) as Hr. change (bv_modulus 32) with (2 ^ 32) in Hr.
  rewrite swrap32 by lia. unfold sx32Z, bv_wrap. rewrite bv_modulus_64, two64_eq.
  destruct (Z.leb_spec (2 ^ 31) (bv_unsigned r)); [reflexivity|].
  apply Z.mod_small. lia.
Qed.

Lemma sx32_ok' : forall i, to_Z i < 2 ^ 32 -> w2Z (sx32 i) = sx32Z (to_Z i).
Proof.
  intros i Hi. pose proof (int_range i). unfold sx32, sx32Z.
  rewrite bitE. change (to_Z 31) with 31. rewrite (testbit_top _ 31) by lia.
  destruct (Z.leb_spec (2 ^ 31) (to_Z i)).
  - w64_bitblast.
  - reflexivity.
Qed.

Lemma sx32_ok : forall i, to_Z i < 2 ^ 32 -> wbv (sx32 i) = sext 64 (Z_to_bv 32 (to_Z i)).
Proof.
  intros i Hi. pose proof (int_range i). apply wbv_eq_of_w2Z.
  rewrite sext32_unsigned, Z_to_bv_unsigned, (bv_wrap_small 32) by (change (bv_modulus 32) with (2 ^ 32); lia).
  apply sx32_ok'. exact Hi.
Qed.

Lemma zx32_ok : forall i, to_Z i < 2 ^ 32 -> wbv (zx32 i) = zext 64 (Z_to_bv 32 (to_Z i)).
Proof.
  intros i Hi. pose proof (int_range i). apply wbv_eq_of_w2Z. unfold zext.
  rewrite bv_zero_extend_unsigned', Z_to_bv_unsigned, (bv_wrap_small 32) by (change (bv_modulus 32) with (2 ^ 32); lia).
  rewrite bv_wrap_small by (rewrite bv_modulus_64; unfold two64, two63 in *; lia).
  reflexivity.
Qed.

Lemma wlit_ok : forall i, w2Z (wlit i) = to_Z i.
Proof. intros i. reflexivity. Qed.

Lemma s32Z_ok : forall i, to_Z i < 2 ^ 32 -> s32Z i = bv_swrap 32 (to_Z i).
Proof.
  intros i Hi. pose proof (int_range i). unfold s32Z.
  rewrite bitE. change (to_Z 31) with 31. rewrite (testbit_top _ 31), swrap32, lit_4294967296 by lia.
  reflexivity.
Qed.

Lemma low32_signed : forall a, bv_signed (low32 (wbv a)) = s32Z (lo32 a).
Proof. intros a. unfold bv_signed. rewrite low32_unsigned, s32Z_ok by apply lo32_range. reflexivity. Qed.

Lemma land31_range : forall z, 0 <= Z.land z 31 <= 31.
Proof.
  intros z. change 31 with (Z.ones 5) at 1 2. rewrite Z.land_ones by lia.
  change (2 ^ 5) with 32. pose proof (Z.mod_pos_bound z 32). lia.
Qed.

Lemma shamt5_bv : forall b,
  bv_unsigned (bv_and (low32 (wbv b)) (Z_to_bv 32 31)) = Z.land (to_Z (lo32 b)) 31.
Proof.
  intros b. rewrite bv_and_unsigned, Z_to_bv_unsigned, low32_unsigned. reflexivity.
Qed.

Lemma to_Z_land31 : forall y, to_Z (PrimInt63.land y 31) = Z.land (to_Z y) 31.
Proof. intros y. rewrite land_spec'. reflexivity. Qed.

Lemma lxor_bit31 : forall x, 0 <= x < 2 ^ 32 ->
  Z.lxor x (2 ^ 31) = bv_swrap 32 x + 2 ^ 31.
Proof.
  intros x Hx. rewrite swrap32 by lia.
  destruct (Z.leb_spec (2 ^ 31) x).
  - replace x with (Z.lxor (x - 2 ^ 31) (2 ^ 31)) at 1.
    + rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. lia.
    + rewrite <- Z.add_nocarry_lxor; [lia|].
      apply Z.bits_inj'; intros m Hm. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
      destruct (Z.eqb_spec 31 m); [|apply andb_false_r]. subst.
      rewrite (testbit_high _ 31); [reflexivity| lia | lia].
  - symmetry. rewrite <- Z.add_nocarry_lxor; [lia|].
    apply Z.bits_inj'; intros m Hm. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec 31 m); [|apply andb_false_r]. subst.
    rewrite (testbit_high _ 31); [reflexivity| lia | lia].
Qed.

Lemma ones32_range : 0 <= Z.ones 32 < 2 ^ 32.
Proof. rewrite <- lit_4294967295. split; [lia|reflexivity]. Qed.

Lemma land_mask32_range : forall x, 0 <= to_Z (PrimInt63.land x mask32) < 2 ^ 32.
Proof. intros x. rewrite land_spec', to_Z_mask32. apply (land_range_r _ _ 32). apply ones32_range. Qed.

Lemma lsr_lt32 : forall x k, to_Z x < 2 ^ 32 -> to_Z (PrimInt63.lsr x k) < 2 ^ 32.
Proof.
  intros x k Hx. pose proof (int_range x). pose proof (int_range k). rewrite lsr_spec.
  pose proof (Z.pow_pos_nonneg 2 (to_Z k) ltac:(lia) ltac:(lia)).
  apply Z.le_lt_trans with (m := to_Z x); [|lia].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma sx32Z_01 : forall c : bool,
  sx32Z (bv_unsigned (if c then Z_to_bv 32 1 else Z_to_bv 32 0)) = if c then 1 else 0.
Proof. intros [|]; reflexivity. Qed.

Lemma walu32_ok : forall op a b,
  wbv (walu32 op a b) = sext 64 (alu32 op (low32 (wbv a)) (low32 (wbv b))).
Proof.
  intros op a b. apply wbv_eq_of_w2Z. rewrite sext32_unsigned.
  pose proof (lo32_range a) as Ra. pose proof (lo32_range b) as Rb.
  pose proof (land31_range (to_Z (lo32 b))) as Rk.
  unfold alu32, alu, walu32. destruct op.
  -   rewrite bv_add_unsigned, !low32_unsigned.
    rewrite sx32_ok' by apply land_mask32_range.
    f_equal. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). w64_bitblast.
  -   rewrite bv_sub_unsigned, !low32_unsigned.
    rewrite sx32_ok' by apply land_mask32_range.
    f_equal. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). w64_bitblast.
  -   rewrite bv_shiftl_unsigned, shamt5_bv, low32_unsigned.
    rewrite sx32_ok' by apply land_mask32_range.
    f_equal. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
    w64_zify. rewrite ?to_Z_land31 in *. w64_bitblast.
  -   rewrite sx32Z_01, wofbool_ok. unfold bv_lts. rewrite !low32_signed, !s32Z_ok by apply lo32_range.
    match goal with |- (if ?x then _ else _) = (if ?y then _ else _) => replace x with y; [reflexivity|] end.
    destruct (ltbP (PrimInt63.lxor (lo32 a) bit31i) (PrimInt63.lxor (lo32 b) bit31i)) as [C|C];
      rewrite !lxor_spec', to_Z_bit31i, !lxor_bit31 in C by assumption.
    + apply Z.ltb_lt. lia.
    + apply Z.ltb_ge. lia.
  -   rewrite sx32Z_01, wofbool_ok. unfold bv_ltu. rewrite !low32_unsigned.
    destruct (ltbP (lo32 a) (lo32 b)) as [C|C]; symmetry.
    + rewrite (proj2 (Z.ltb_lt _ _) C). reflexivity.
    + rewrite (proj2 (Z.ltb_ge (to_Z (lo32 a)) (to_Z (lo32 b))) ltac:(lia)). reflexivity.
  -   rewrite bv_xor_unsigned, !low32_unsigned.
    rewrite sx32_ok' by (rewrite lxor_spec'; apply (lxor_range _ _ 32); assumption).
    f_equal. apply lxor_spec'.
  -   rewrite bv_shiftr_unsigned, shamt5_bv, low32_unsigned.
    rewrite sx32_ok' by (apply lsr_lt32; lia).
    f_equal. rewrite lsr_spec, to_Z_land31, Z.shiftr_div_pow2 by lia. reflexivity.
  -   rewrite bv_ashiftr_unsigned, shamt5_bv, low32_signed, s32Z_ok by apply lo32_range.
    rewrite swrap32 by lia. rewrite bitE. change (to_Z 31) with 31. rewrite (testbit_top _ 31) by lia.
    unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
    destruct (Z.leb_spec (2 ^ 31) (to_Z (lo32 a))).
    + rewrite sx32_ok' by apply land_mask32_range.
      f_equal. w64_zify. rewrite ?to_Z_land31 in *. w64_bitblast.
    + rewrite sx32_ok' by (apply lsr_lt32; lia).
      f_equal. w64_zify. rewrite ?to_Z_land31 in *. w64_bitblast.
  -   rewrite bv_or_unsigned, !low32_unsigned.
    rewrite sx32_ok' by (rewrite lor_spec'; apply (lor_range _ _ 32); assumption).
    f_equal. apply lor_spec'.
  -   rewrite bv_and_unsigned, !low32_unsigned.
    rewrite sx32_ok' by (rewrite land_spec'; apply (land_range_l _ _ 32); assumption).
    f_equal. apply land_spec'.
Qed.

Lemma Z2w32s_ok : forall z, w2Z (Z2w32s z) = sx32Z (z mod 2 ^ 32).
Proof.
  intros z. unfold Z2w32s. rewrite lit_4294967296.
  pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(reflexivity)).
  rewrite sx32_ok' by (rewrite of_Z_spec, Z.mod_small; [lia| rewrite wB_two63; unfold two63; lia]).
  rewrite of_Z_spec, Z.mod_small by (rewrite wB_two63; unfold two63; lia). reflexivity.
Qed.

Lemma eqb0_lo32 : forall b, PrimInt63.eqb (lo32 b) 0 = Z.eqb (to_Z (lo32 b)) 0.
Proof.
  intros b. destruct (eqbP (lo32 b) 0) as [E|E]; change (to_Z 0) with 0 in E; symmetry.
  - apply Z.eqb_eq. exact E.
  - apply Z.eqb_neq. exact E.
Qed.

Lemma wmd32_ok : forall op a b,
  wbv (wmd32 op a b) = sext 64 (mul_div op (low32 (wbv a)) (low32 (wbv b))).
Proof.
  intros op a b. apply wbv_eq_of_w2Z. rewrite sext32_unsigned.
  pose proof (lo32_range a) as Ra. pose proof (lo32_range b) as Rb.
  unfold mul_div, wmd32. rewrite eqb0_lo32, low32_unsigned. destruct op.
  -   rewrite bv_mul_unsigned, !low32_unsigned.
    rewrite sx32_ok' by apply land_mask32_range.
    f_equal. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). w64_bitblast.
  - unfold bv_mulhss. rewrite Z_to_bv_unsigned, !low32_signed. apply Z2w32s_ok.
  - unfold bv_mulhsu. rewrite Z_to_bv_unsigned, low32_signed, low32_unsigned. apply Z2w32s_ok.
  - unfold bv_mulhuu. rewrite Z_to_bv_unsigned, !low32_unsigned. apply Z2w32s_ok.
  - destruct (Z.eqb_spec (to_Z (lo32 b)) 0) as [E|E].
    + rewrite Z2w_ok. reflexivity.
    + rewrite bv_quots_unsigned, !low32_signed. apply Z2w32s_ok.
  - destruct (Z.eqb_spec (to_Z (lo32 b)) 0) as [E|E].
    + rewrite Z2w_ok. reflexivity.
    + rewrite bv_divu_unsigned, !low32_unsigned.
      assert (Hd : 0 <= to_Z (lo32 a) / to_Z (lo32 b) < 2 ^ 32).
      { split; [apply Z.div_pos; lia|].
        apply Z.le_lt_trans with (m := to_Z (lo32 a)); [|lia].
        apply Z.div_le_upper_bound; [lia|]. nia. }
      rewrite sx32_ok' by (rewrite div_spec; lia). f_equal. apply div_spec.
  - destruct (Z.eqb_spec (to_Z (lo32 b)) 0) as [E|E].
    + rewrite low32_unsigned. apply sx32_ok'. lia.
    + rewrite bv_rems_unsigned, !low32_signed. apply Z2w32s_ok.
  - destruct (Z.eqb_spec (to_Z (lo32 b)) 0) as [E|E].
    + rewrite low32_unsigned. apply sx32_ok'. lia.
    + rewrite bv_modu_unsigned, !low32_unsigned.
      pose proof (Z.mod_pos_bound (to_Z (lo32 a)) (to_Z (lo32 b)) ltac:(lia)).
      rewrite sx32_ok' by (rewrite mod_spec; lia). f_equal. apply mod_spec.
Qed.

Lemma pow2_m1_ones : forall n, 2 ^ n - 1 = Z.ones n.
Proof. intros n. unfold Z.ones. rewrite Z.shiftl_1_l. lia. Qed.

Ltac w64_tb_step4 :=
  match goal with
  | |- context [Z.testbit (2 ^ ?n - 1) ?m] => rewrite (pow2_m1_ones n)
  end.
Ltac w64_tb ::= repeat first [w64_tb_step | w64_tb_step2 | w64_tb_step4 | w64_tb_step3].

Lemma land_mod_ones : forall x k, 0 <= k <= 63 ->
  Z.land (x mod 2 ^ 63) (Z.ones k) = x mod 2 ^ k.
Proof. intros x k Hk. w64_bitblast. Qed.

Lemma wext_ok : forall sx lo n a, to_Z lo >= 0 ->
  1 <= to_Z n -> to_Z lo + to_Z n <= 8 ->
  w2Z (wext sx lo n a) = ext_Z sx (to_Z lo) (to_Z n) (w2Z a).
Proof.
  intros sx lo n a Hlo Hn Hle. pose proof (w2Z_range a) as Ra. rewrite two64_eq in Ra.
  unfold wext, ext_Z.
  destruct (eqbP n 8) as [E|E]; change (to_Z 8) with 8 in E.
  - rewrite E in *. assert (El : to_Z lo = 0) by lia. rewrite El.
    rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. change (8 * 8 - 1) with 63. change (8 * 8) with 64.
    rewrite (Z.mod_small (w2Z a) (2 ^ 64)) by lia.
    destruct sx; [|reflexivity]. rewrite two64_eq.
    destruct (Z.leb_spec (2 ^ 63) (w2Z a)).
    + apply Z.mod_unique_pos with (q := -1); lia.
    + symmetry. apply Z.mod_small. lia.
  - assert (HN : 1 <= to_Z n <= 7) by lia.
    assert (HP : 2 ^ 8 <= 2 ^ (8 * to_Z n) <= 2 ^ 56) by (split; apply Z.pow_le_mono_r; lia).
    assert (HP1 : 0 < 2 ^ (8 * to_Z n - 1) < 2 ^ (8 * to_Z n)) by
      (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    assert (Hnb : to_Z (PrimInt63.lsl n 3) = 8 * to_Z n) by (w64_zify; change (2 ^ 3) with 8 in *; lia).
    assert (Hlb : to_Z (PrimInt63.lsl lo 3) = 8 * to_Z lo) by (w64_zify; change (2 ^ 3) with 8 in *; lia).
    assert (Hm : to_Z (PrimInt63.sub (PrimInt63.lsl 1 (PrimInt63.lsl n 3)) 1) = Z.ones (8 * to_Z n)).
    { rewrite sub_spec, lsl_spec, Hnb, wB_two63, two63_eq. change (to_Z 1) with 1. rewrite Z.mul_1_l. w64_mod_small. apply pow2_m1_ones. }
    match goal with |- context [Uint63Axioms.bit ?x ?y] => set (u := x) in * end.
    set (U := (w2Z a / 2 ^ (8 * to_Z lo)) mod 2 ^ (8 * to_Z n)) in *.
    assert (HUr : 0 <= U < 2 ^ (8 * to_Z n)) by (apply Z.mod_pos_bound; lia).
    assert (HU : to_Z u = U).
    { subst u U. rewrite land_spec', Hm, w2Z_wl, wsrl_k_ok, two63_eq, Hlb by (rewrite Hlb; lia).
      apply land_mod_ones. lia. }
    clearbody u U.
    rewrite two64_eq.
    destruct sx; cbn [andb].
    + rewrite bitE, HU, sub_spec, Hnb. change (to_Z 1) with 1. rewrite wB_two63, two63_eq. w64_mod_small.
      rewrite (testbit_top U) by (try lia; replace (8 * to_Z n - 1 + 1) with (8 * to_Z n) by lia; lia).
      destruct (Z.leb_spec (2 ^ (8 * to_Z n - 1)) U); [|unfold w2Z; cbn [wt wl]; rewrite HU, Z.mod_small by lia; lia].
      apply Z.bits_inj'; intros m Hmm. w64_tb. rewrite lor_spec', lxor_spec', HU, Hm, to_Z_ones63. w64_tb.
      w64_bcase; w64_tb_idx; w64_bfin.
    + unfold w2Z; cbn [wt wl]; lia.
Qed.

Lemma wins_ok : forall lo n a v, to_Z lo >= 0 ->
  1 <= to_Z n -> to_Z lo + to_Z n <= 8 ->
  w2Z (wins lo n a v) = ins_Z (to_Z lo) (to_Z n) (w2Z a) (w2Z v)
  /\ 0 <= ins_Z (to_Z lo) (to_Z n) (w2Z a) (w2Z v) < two64.
Proof.
  intros lo n a v Hlo Hn Hle.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range v) as Rv. rewrite two64_eq in Ra, Rv.
  match goal with |- ?P /\ _ => assert (HE : P); [| split; [exact HE| rewrite <- HE; apply w2Z_range]] end.
  unfold wins, ins_Z.
  destruct (eqbP n 8) as [E|E]; change (to_Z 8) with 8 in E.
  - rewrite E in *. assert (El : to_Z lo = 0) by lia. rewrite El.
    rewrite Z.mul_0_r. change (8 * 8) with 64. w64_bitblast.
  - assert (HN : 1 <= to_Z n <= 7) by lia.
    assert (HP : 2 ^ 8 <= 2 ^ (8 * to_Z n) <= 2 ^ 56) by (split; apply Z.pow_le_mono_r; lia).
    assert (Hnb : to_Z (PrimInt63.lsl n 3) = 8 * to_Z n) by (w64_zify; change (2 ^ 3) with 8 in *; lia).
    assert (Hlb : to_Z (PrimInt63.lsl lo 3) = 8 * to_Z lo) by (w64_zify; change (2 ^ 3) with 8 in *; lia).
    assert (Hmi : to_Z (PrimInt63.sub (PrimInt63.lsl 1 (PrimInt63.lsl n 3)) 1) = Z.ones (8 * to_Z n)).
    { rewrite sub_spec, lsl_spec, Hnb, wB_two63, two63_eq. change (to_Z 1) with 1. rewrite Z.mul_1_l. w64_mod_small. apply pow2_m1_ones. }
    set (mi := PrimInt63.sub _ 1) in *. clearbody mi.
    rewrite wor_ok, wand_ok, wnot_lnot, !wsll_k_ok, Hlb by (rewrite Hlb; lia).
    repeat match goal with |- context [w2Z (W64 false ?x)] => change (w2Z (W64 false x)) with (0 + to_Z x) end.
    rewrite land_spec', !Hmi, w2Z_wl, two63_eq, !Z.add_0_l.
    apply (f_equal2 Z.lor); w64_bitblast.
Qed.

Lemma wins_w2Z : forall lo n a v, to_Z lo >= 0 ->
  1 <= to_Z n -> to_Z lo + to_Z n <= 8 ->
  w2Z (wins lo n a v) = ins_Z (to_Z lo) (to_Z n) (w2Z a) (w2Z v).
Proof. intros. apply wins_ok; assumption. Qed.

Lemma ins_Z_range : forall lo n a v, to_Z lo >= 0 ->
  1 <= to_Z n -> to_Z lo + to_Z n <= 8 ->
  0 <= ins_Z (to_Z lo) (to_Z n) (w2Z a) (w2Z v) < two64.
Proof. intros. apply wins_ok; assumption. Qed.

Lemma wext_range : forall sx lo n a, to_Z lo >= 0 ->
  1 <= to_Z n -> to_Z lo + to_Z n <= 8 ->
  0 <= ext_Z sx (to_Z lo) (to_Z n) (w2Z a) < two64.
Proof. intros. rewrite <- wext_ok by assumption. apply w2Z_range. Qed.

Lemma wleu_ok : forall a b, wleu a b = negb (bv_ltu (wbv b) (wbv a)).
Proof. intros a b. unfold wleu. rewrite wltu_ok. reflexivity. Qed.

Lemma wzero_ok : w2Z wzero = 0. Proof. reflexivity. Qed.
Lemma wone_ok : w2Z wone = 1. Proof. reflexivity. Qed.
Lemma wbv_wzero : wbv wzero = w0. Proof. apply wbv_eq_of_w2Z. reflexivity. Qed.
Lemma wbv_wone : wbv wone = w1. Proof. apply wbv_eq_of_w2Z. reflexivity. Qed.

Lemma bv2w_ok : forall b : word, w2Z (bv2w b) = bv_unsigned b.
Proof. intros b. rewrite <- wbv_unsigned, bv2w_wbv. reflexivity. Qed.

Section examples.
  Let top : w64 := Z2w (2 ^ 63).
  Let m1 : w64 := Z2w (-1).
  Example ex_sra63 : w2Z (walu ALU_SRA top (Z2w 63)) = 2 ^ 64 - 1.
  Proof. vm_compute. reflexivity. Qed.
  Example ex_sra0 : w2Z (walu ALU_SRA top (Z2w 64)) = 2 ^ 63.
  Proof. vm_compute. reflexivity. Qed.
  Example ex_srl63 : w2Z (walu ALU_SRL m1 (Z2w 63)) = 1.
  Proof. vm_compute. reflexivity. Qed.
  Example ex_sll63 : w2Z (walu ALU_SLL m1 (Z2w 63)) = 2 ^ 63.
  Proof. vm_compute. reflexivity. Qed.

  Example ex_sraw0 : w2Z (walu32 ALU_SRA (Z2w (2 ^ 31)) (Z2w 32)) = 2 ^ 64 - 2 ^ 31.
  Proof. vm_compute. reflexivity. Qed.
  Example ex_sraw31 : w2Z (walu32 ALU_SRA (Z2w (2 ^ 31)) (Z2w 31)) = 2 ^ 64 - 1.
  Proof. vm_compute. reflexivity. Qed.

  Example ex_Z2w_neg : w2Z (Z2w (-1)) = 2 ^ 64 - 1 /\ w2Z (Z2w (- 2 ^ 64 - 5)) = 2 ^ 64 - 5.
  Proof. vm_compute. split; reflexivity. Qed.

  Example ex_div_overflow :
    w2Z (wmd M_DIV top m1) = 2 ^ 63 /\ w2Z (wmd M_REM top m1) = 0 /\
    w2Z (wmd M_DIV wone wzero) = 2 ^ 64 - 1 /\ w2Z (wmd M_REMU top wzero) = 2 ^ 63 /\
    w2Z (wmd32 M_DIV (Z2w (2 ^ 31)) m1) = 2 ^ 64 - 2 ^ 31 /\ w2Z (wmd32 M_REM (Z2w (2 ^ 31)) m1) = 0.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Let pat : w64 := Z2w 0x8877665544332211.
  Example ex_wext :
    w2Z (wext false 0%uint63 8%uint63 pat) = 0x8877665544332211 /\
    w2Z (wext true 4%uint63 4%uint63 pat) = 2 ^ 64 - 2 ^ 32 + 0x88776655 /\
    w2Z (wext false 4%uint63 4%uint63 pat) = 0x88776655 /\
    w2Z (wext true 7%uint63 1%uint63 pat) = 2 ^ 64 - 256 + 0x88 /\
    w2Z (wext true 0%uint63 1%uint63 pat) = 0x11 /\
    w2Z (wext true 6%uint63 2%uint63 pat) = 2 ^ 64 - 2 ^ 16 + 0x8877 /\
    w2Z (wext false 6%uint63 2%uint63 pat) = ext_Z false 6 2 (w2Z pat) /\
    w2Z (wext true 3%uint63 4%uint63 pat) = ext_Z true 3 4 (w2Z pat).
  Proof. vm_compute. repeat split; reflexivity. Qed.
  Example ex_wins :
    w2Z (wins 4%uint63 4%uint63 pat m1) = 0xffffffff44332211 /\
    w2Z (wins 7%uint63 1%uint63 pat wzero) = 0x0077665544332211 /\
    w2Z (wins 0%uint63 8%uint63 pat m1) = 2 ^ 64 - 1 /\
    w2Z (wins 2%uint63 2%uint63 pat wzero) = ins_Z 2 2 (w2Z pat) 0.
  Proof. vm_compute. repeat split; reflexivity. Qed.
End examples.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
