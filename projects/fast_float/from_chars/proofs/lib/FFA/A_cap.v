(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pow5_growth (e : Z) : Z :=
  6 * (e / 135) + (e mod 135) / 27 + (if Z.eqb ((e mod 135) mod 27) 0 then 0 else 1).

Lemma pow5_growth_nonneg : forall e, 0 <= e -> 0 <= pow5_growth e.
Proof.
  intros e He. unfold pow5_growth.
  pose proof (Z.div_pos e 135 He ltac:(lia)).
  pose proof (Z.mod_pos_bound e 135 ltac:(lia)).
  pose proof (Z.div_pos (e mod 135) 27 ltac:(lia) ltac:(lia)).
  destruct (Z.eqb _ 0); lia.
Qed.

Lemma pow5_growth_135 : forall e, 135 <= e -> pow5_growth e = 6 + pow5_growth (e - 135).
Proof.
  intros e He. unfold pow5_growth.
  replace (e - 135) with (e + (-1) * 135) by lia.
  rewrite Z.div_add by lia. rewrite Z.mod_add by lia. lia.
Qed.

Lemma pow5_growth_27 : forall e, 27 <= e < 135 -> pow5_growth e = 1 + pow5_growth (e - 27).
Proof.
  intros e He. unfold pow5_growth.
  rewrite (Z.div_small e 135) by lia. rewrite (Z.mod_small e 135) by lia.
  rewrite (Z.div_small (e - 27) 135) by lia. rewrite (Z.mod_small (e - 27) 135) by lia.
  replace (e - 27) with (e + (-1) * 27) by lia.
  rewrite Z.div_add by lia. rewrite Z.mod_add by lia. lia.
Qed.

Lemma pow5_growth_small : forall e, 0 < e < 27 -> pow5_growth e = 1.
Proof.
  intros e He. unfold pow5_growth.
  rewrite (Z.div_small e 135) by lia. rewrite (Z.mod_small e 135) by lia.
  rewrite (Z.div_small e 27) by lia. rewrite (Z.mod_small e 27) by lia.
  destruct (Z.eqb_spec e 0); lia.
Qed.

Lemma pow5_growth_0 : pow5_growth 0 = 0.
Proof. reflexivity. Qed.

Lemma pow5_growth_ge5 : forall e, 135 <= e -> 5 <= pow5_growth e.
Proof. intros e He. rewrite pow5_growth_135 by lia. pose proof (pow5_growth_nonneg (e - 135) ltac:(lia)). lia. Qed.

Lemma pow5_growth_ge1 : forall e, 0 < e -> 1 <= pow5_growth e.
Proof.
  intros e He. destruct (Z_lt_le_dec e 27) as [H|H]; [rewrite pow5_growth_small by lia; lia|].
  destruct (Z_lt_le_dec e 135) as [H'|H'].
  - rewrite pow5_growth_27 by lia. pose proof (pow5_growth_nonneg (e - 27) ltac:(lia)). lia.
  - pose proof (pow5_growth_ge5 e H'). lia.
Qed.

(* [comment removed for export] *)
Lemma cap_of_len : forall ws n y, 0 <= y < 2 ^ 64 -> Z.of_nat n <= 61 -> y * bval ws n < BIG_CAP.
Proof.
  intros ws n y Hy Hn. pose proof (bval_range ws n) as (B0 & B1).
  assert (P : 2 ^ (64 * Z.of_nat n) * 2 ^ 64 <= BIG_CAP).
  { unfold BIG_CAP. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  assert (y * bval ws n <= (2 ^ 64 - 1) * bval ws n) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert ((2 ^ 64 - 1) * bval ws n < 2 ^ 64 * 2 ^ (64 * Z.of_nat n)).
  { assert ((2 ^ 64 - 1) * bval ws n <= (2 ^ 64 - 1) * (2 ^ (64 * Z.of_nat n) - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
    nia. }
  lia.
Qed.

Lemma cap_of_len_pow2 : forall ws n e, 0 <= e -> 64 * Z.of_nat n + e <= 3968 -> bval ws n * 2 ^ e < BIG_CAP.
Proof.
  intros ws n e He Hn. pose proof (bval_range ws n) as (B0 & B1).
  assert (P : 2 ^ (64 * Z.of_nat n) * 2 ^ e <= BIG_CAP).
  { unfold BIG_CAP. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He).
  assert (bval ws n * 2 ^ e < 2 ^ (64 * Z.of_nat n) * 2 ^ e) by (apply Z.mul_lt_mono_pos_r; lia).
  lia.
Qed.

(* [comment removed for export] *)
Lemma pow5_growth_bound : forall e, 0 <= e -> pow5_growth e <= e / 27 + e / 135 + 1.
Proof.
  intros e He. unfold pow5_growth.
  pose proof (Z.div_mod e 135 ltac:(lia)). pose proof (Z.mod_pos_bound e 135 ltac:(lia)).
  pose proof (Z.div_mod (e mod 135) 27 ltac:(lia)). pose proof (Z.mod_pos_bound (e mod 135) 27 ltac:(lia)).
  pose proof (Z.div_mod e 27 ltac:(lia)). pose proof (Z.mod_pos_bound e 27 ltac:(lia)).
  destruct (Z.eqb _ 0); lia.
Qed.

Lemma pos_dc_cap_of_bounds : forall len e, 0 <= len <= 8 -> 0 <= e <= 330 ->
  len + pow5_growth e <= 61 /\ 64 * (len + pow5_growth e) + e <= 3968.
Proof.
  intros len e Hl He. pose proof (pow5_growth_bound e ltac:(lia)).
  assert (e / 27 < 13) by (apply Z.div_lt_upper_bound; lia). assert (e / 135 < 3) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma neg_cap : forall k, 0 <= k <= 1300 -> 1 + pow5_growth k <= 61.
Proof.
  intros k Hk. pose proof (pow5_growth_bound k ltac:(lia)).
  assert (k / 27 < 49) by (apply Z.div_lt_upper_bound; lia). assert (k / 135 < 10) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
