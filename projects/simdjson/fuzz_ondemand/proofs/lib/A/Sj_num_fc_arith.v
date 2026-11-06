(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma mulhu_shr_gen : forall x M s K D,
  0 <= x < 18446744073709551616 -> 0 <= M < 18446744073709551616 -> M <= K -> 0 < K -> 0 < D -> 0 <= s ->
  18446744073709551616 * 2 ^ s = K * D ->
  0 <= Z.shiftr ((Z.shiftr (x * M) 64) mod 18446744073709551616) s <= x / D.
Proof.
  intros x M s K D Hx HM HK K0 D0 Hs E.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 64) with 18446744073709551616.
  assert (P0 : 0 <= x * M) by (apply Z.mul_nonneg_nonneg; lia).
  assert (PH : x * M / 18446744073709551616 < 18446744073709551616).
  { apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small (x * M / 18446744073709551616)) by (split; [apply Z.div_pos; lia | exact PH]).
  assert (S0 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; [apply Z.div_pos; lia | lia]|].
  rewrite Z.div_div by lia. rewrite E.
  assert (LE : x * M <= x * K) by (apply Z.mul_le_mono_nonneg_l; lia).
  etransitivity; [apply (Z.div_le_mono _ (x * K)); [nia | exact LE]|].
  rewrite (Z.mul_comm x K). rewrite Z.div_mul_cancel_l by lia. lia.
Qed.

Lemma sci_a : forall w, 0 <= w < 18446744073709551616 ->
  0 <= Z.shiftr ((Z.shiftr (w * 3777893186295716171) 64) mod 18446744073709551616) 11 <= w / 8192.
Proof. intros w H. apply (mulhu_shr_gen w _ 11 4611686018427387904 8192); try lia; try reflexivity. Qed.

Lemma sci_b : forall w, 0 <= w < 18446744073709551616 ->
  0 <= Z.shiftr ((Z.shiftr (Z.shiftr w 2 * 2951479051793528259) 64) mod 18446744073709551616) 2 <= w / 64.
Proof.
  intros w H.
  assert (W2 : 0 <= Z.shiftr w 2 <= w / 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 2) with 4; split; [apply Z.div_pos; lia | lia]).
  assert (W3 : Z.shiftr w 2 < 18446744073709551616).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. apply Z.div_lt_upper_bound; lia. }
  pose proof (mulhu_shr_gen (Z.shiftr w 2) 2951479051793528259 2 4611686018427387904 16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)) as B.
  split; [lia|]. etransitivity; [exact (proj2 B)|].
  etransitivity; [apply (Z.div_le_mono _ (w / 4)); lia|]. rewrite Z.div_div by lia. change (4 * 16) with 64. lia.
Qed.

Lemma sci_c : forall w, 0 <= w < 18446744073709551616 ->
  0 <= Z.shiftr ((Z.shiftr (w * 14757395258967641293) 64) mod 18446744073709551616) 3 <= w / 8.
Proof. intros w H. apply (mulhu_shr_gen w _ 3 18446744073709551616 8); try lia; try reflexivity. Qed.

Lemma sci_c8 : forall w, 0 <= w < 18446744073709551616 ->
  0 <= ((Z.shiftr (w * 14757395258967641293) 64) mod 18446744073709551616) / 8 <= w / 8.
Proof.
  intros w H. pose proof (sci_c w H) as B. rewrite (Z.shiftr_div_pow2 _ 3) in B by lia. change (2 ^ 3) with 8 in B. exact B.
Qed.
