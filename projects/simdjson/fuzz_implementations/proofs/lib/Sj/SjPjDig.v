(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition sw32 (x : Z) : Z := (x + 2147483648) mod 4294967296 - 2147483648.

Lemma sw32_small : forall x, -2147483648 <= x < 2147483648 -> sw32 x = x.
Proof. intros x H. unfold sw32. Z.div_mod_to_equations. lia. Qed.

Lemma sw32_mod64 : forall x, sw32 (x mod 18446744073709551616) = sw32 x.
Proof. intros x. unfold sw32. Z.div_mod_to_equations. lia. Qed.

Lemma sw32_add_mod32 : forall n e, -2147483648 <= n + e < 2147483648 -> sw32 (n + e mod 4294967296) = n + e.
Proof.
  intros n e H. unfold sw32.
  replace (n + e mod 4294967296 + 2147483648) with ((n + 2147483648) + e mod 4294967296) by lia.
  rewrite Z.add_mod_idemp_r by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sw32_mod64_add : forall x c, -2147483648 <= x + c < 2147483648 -> sw32 (x mod 18446744073709551616 + c) = x + c.
Proof.
  intros x c H. unfold sw32.
  replace (x mod 18446744073709551616 + c + 2147483648) with ((c + 2147483648) + x mod 18446744073709551616) by lia.
  rewrite <- Z.add_mod_idemp_r by lia.
  replace ((x mod 18446744073709551616) mod 4294967296) with (x mod 4294967296) by (Z.div_mod_to_equations; lia).
  rewrite Z.add_mod_idemp_r by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition sf_k2 (e2 : Z) : Z := Z.shiftr (e2 * 631305 - 261663) 21.

Lemma sf_k_range : forall e2, -1074 <= e2 <= 972 -> -324 <= sf_k e2 <= 292.
Proof. intros e2 H. pose proof (sf_exp_range e2 0 H ltac:(lia)). pose proof (sf_exp_range e2 16 H ltac:(lia)). lia. Qed.

Lemma sf_k2_range : forall e2, -1074 <= e2 <= 972 -> -324 <= sf_k2 e2 <= 292.
Proof.
  intros e2 H. unfold sf_k2.
  pose proof (shiftr_bounds (e2 * 631305 - 261663) 21 (-324) 292 ltac:(lia)) as HB.
  change (2 ^ 21) with 2097152 in HB. specialize (HB ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma sf_index_k : forall e2, sf_index e2 = 294 - sf_k e2.
Proof. reflexivity. Qed.
Lemma sf_index2_k2 : forall e2, sf_index2 e2 = 292 - sf_k2 e2.
Proof. reflexivity. Qed.

Lemma sf_k_machine : forall e2, -1074 <= e2 <= 972 ->
  sw32 (Z.shiftr (sw32 ((e2 mod 18446744073709551616 * 315653) mod 18446744073709551616)) 20) = sf_k e2.
Proof.
  intros e2 H. rewrite Z.mul_mod_idemp_l by lia. rewrite sw32_mod64.
  rewrite (sw32_small (e2 * 315653)) by lia.
  apply sw32_small. pose proof (sf_k_range e2 H). unfold sf_k in *. lia.
Qed.

Lemma sf_k2_machine : forall e2 c, -1074 <= e2 <= 972 ->
  c mod 18446744073709551616 = (e2 * 631305 - 261663) mod 18446744073709551616 ->
  sw32 (Z.shiftr (sw32 c) 21) = sf_k2 e2.
Proof.
  intros e2 c H HC. rewrite <- (sw32_mod64 c), HC, sw32_mod64.
  rewrite (sw32_small (e2 * 631305 - 261663)) by lia.
  apply sw32_small. pose proof (sf_k2_range e2 H). unfold sf_k2 in *. lia.
Qed.

Definition DIV100_MAGIC : Z := 2951479051793528259.

Lemma div100_magic : forall w, 0 <= w < 18446744073709551616 ->
  Z.shiftr ((Z.shiftr w 2 * DIV100_MAGIC) / 18446744073709551616) 2 = w / 100.
Proof.
  intros w H. unfold DIV100_MAGIC. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  Z.div_mod_to_equations. lia.
Qed.

Definition DIV10_MAGIC : Z := 14757395258967641293.

Lemma div10_magic : forall w, 0 <= w < 18446744073709551616 ->
  Z.shiftr ((w * DIV10_MAGIC) / 18446744073709551616) 3 = w / 10.
Proof.
  intros w H. unfold DIV10_MAGIC. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

Lemma div100_machine : forall w, 0 <= w < 18446744073709551616 ->
  Z.shiftr ((Z.shiftr (Z.shiftr w 2 * DIV100_MAGIC) 64) mod 18446744073709551616) 2 = w / 100.
Proof.
  intros w H. unfold DIV100_MAGIC. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Lemma div10_machine : forall w, 0 <= w < 18446744073709551616 ->
  Z.shiftr ((Z.shiftr (w * DIV10_MAGIC) 64) mod 18446744073709551616) 3 = w / 10.
Proof.
  intros w H. unfold DIV10_MAGIC. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rem100_machine : forall w, 0 <= w < 18446744073709551616 ->
  sw32 (w - (w / 100 * 100) mod 18446744073709551616) = w mod 100.
Proof.
  intros w H. unfold sw32. Z.div_mod_to_equations. lia.
Qed.

Lemma pow100_pos : forall j, 0 <= j -> 1 <= 100 ^ j.
Proof. intros j H. pose proof (Z.pow_pos_nonneg 100 j ltac:(lia) H). lia. Qed.

Lemma pow100_step : forall w j, 1 <= j -> 0 <= w < 100 ^ j -> 0 <= w / 100 < 100 ^ (j - 1).
Proof.
  intros w j Hj Hw. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  replace (100 * 100 ^ (j - 1)) with (100 ^ j); [lia|]. rewrite <- Z.pow_succ_r by lia. f_equal. lia.
Qed.

Lemma pow100_ge2 : forall w j, 100 <= w < 100 ^ j -> 2 <= j.
Proof.
  intros w j H. destruct (Z_lt_le_dec j 2) as [L|]; [|assumption]. exfalso.
  destruct (Z_lt_le_dec j 0); [rewrite Z.pow_neg_r in H by lia; lia|].
  assert (j = 0 \/ j = 1) as [-> | ->] by lia; cbn in H; lia.
Qed.
