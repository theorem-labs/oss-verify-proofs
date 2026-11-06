(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition hexval (c : Z) : option Z :=
  if (48 <=? c) && (c <=? 57) then Some (c - 48)
  else if (65 <=? c) && (c <=? 70) then Some (c - 55)
  else if (97 <=? c) && (c <=? 102) then Some (c - 87)
  else None.

(* [comment removed for export] *)
Definition d2v (i : Z) : Z :=
  let j := i / 210 in let b := i mod 210 in
  if (i <? 630) then (match hexval b with Some v => Z.shiftl v (4 * j) | None => 4294967295 end)
  else (match hexval (i - 630) with Some v => Z.shiftl v 12 | None => 4294967295 end).

Definition d2v_table : list Z := map (fun i => d2v (Z.of_nat i)) (seq 0 886).

(* [comment removed for export] *)
Definition d2v_blk (blk b : Z) : Z := match hexval b with Some v => Z.shiftl v (4 * blk) | None => 4294967295 end.

Lemma d2v_at : forall blk b, 0 <= blk <= 3 -> 0 <= b < 256 -> (blk < 3 -> b < 210) -> d2v (210 * blk + b) = d2v_blk blk b.
Proof.
  intros blk b Hblk Hb Hlt. unfold d2v, d2v_blk.
  destruct (Z.eq_dec blk 3) as [->|N].
  - replace (210 * 3 + b <? 630) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (210 * 3 + b - 630) with b by lia. reflexivity.
  - specialize (Hlt ltac:(lia)).
    replace (210 * blk + b <? 630) with true by (symmetry; apply Z.ltb_lt; lia).
    replace ((210 * blk + b) / 210) with blk by (apply (Z.div_unique (210 * blk + b) 210 blk b); lia).
    replace ((210 * blk + b) mod 210) with b by (apply (Z.mod_unique (210 * blk + b) 210 blk b); lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma d2v_overlap : forall blk b, 0 <= blk < 3 -> 210 <= b < 256 -> d2v (210 * blk + b) = 4294967295.
Proof.
  intros blk b Hblk Hb. replace (210 * blk + b) with (210 * (blk + 1) + (b - 210)) by lia.
  rewrite d2v_at by lia. unfold d2v_blk, hexval.
  replace ((48 <=? b - 210) && (b - 210 <=? 57)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
  replace ((65 <=? b - 210) && (b - 210 <=? 70)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
  replace ((97 <=? b - 210) && (b - 210 <=? 102)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma hexval_none_ge : forall b, 210 <= b -> hexval b = None.
Proof.
  intros b Hb. unfold hexval.
  replace ((48 <=? b) && (b <=? 57)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((65 <=? b) && (b <=? 70)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((97 <=? b) && (b <=? 102)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma d2v_read : forall blk b, 0 <= blk <= 3 -> 0 <= b < 256 -> d2v (210 * blk + b) = d2v_blk blk b.
Proof.
  intros blk b Hblk Hb. destruct (Z_lt_ge_dec blk 3) as [L|G].
  - destruct (Z_lt_ge_dec b 210) as [L2|G2]; [apply d2v_at; lia|].
    rewrite d2v_overlap by lia. unfold d2v_blk. rewrite hexval_none_ge by lia. reflexivity.
  - apply d2v_at; lia.
Qed.

Lemma hexval_range : forall c v, hexval c = Some v -> 0 <= v < 16.
Proof.
  intros c v H. unfold hexval in H.
  destruct ((48 <=? c) && (c <=? 57)) eqn:E1; [apply andb_true_iff in E1; destruct E1 as [A B]; apply Z.leb_le in A; apply Z.leb_le in B; inversion H; lia|].
  destruct ((65 <=? c) && (c <=? 70)) eqn:E2; [apply andb_true_iff in E2; destruct E2 as [A B]; apply Z.leb_le in A; apply Z.leb_le in B; inversion H; lia|].
  destruct ((97 <=? c) && (c <=? 102)) eqn:E3; [apply andb_true_iff in E3; destruct E3 as [A B]; apply Z.leb_le in A; apply Z.leb_le in B; inversion H; lia|].
  discriminate.
Qed.

Lemma hexval_some_hex : forall c v, hexval c = Some v -> (48 <= c <= 57) \/ (65 <= c <= 70) \/ (97 <= c <= 102).
Proof.
  intros c v H. unfold hexval in H.
  destruct ((48 <=? c) && (c <=? 57)) eqn:E1; [apply andb_true_iff in E1; destruct E1 as [A B]; apply Z.leb_le in A; apply Z.leb_le in B; lia|].
  destruct ((65 <=? c) && (c <=? 70)) eqn:E2; [apply andb_true_iff in E2; destruct E2 as [A B]; apply Z.leb_le in A; apply Z.leb_le in B; lia|].
  destruct ((97 <=? c) && (c <=? 102)) eqn:E3; [apply andb_true_iff in E3; destruct E3 as [A B]; apply Z.leb_le in A; apply Z.leb_le in B; lia|].
  discriminate.
Qed.

Lemma d2v_blk_range : forall blk b, 0 <= blk <= 3 -> 0 <= d2v_blk blk b < 2 ^ 32.
Proof.
  intros blk b Hb. unfold d2v_blk. destruct (hexval b) as [v|] eqn:E; [|lia].
  pose proof (hexval_range b v E). rewrite Z.shiftl_mul_pow2 by lia.
  assert (P : 0 < 2 ^ (4 * blk) <= 2 ^ 12) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  change (2 ^ 12) with 4096 in P. change (2 ^ 32) with 4294967296. nia.
Qed.

(* [comment removed for export] *)
Definition sx32z (v : Z) : Z := if v <? 2147483648 then v else v - 4294967296.

(* [comment removed for export] *)
Definition hex4 (b0 b1 b2 b3 : Z) : Z :=
  Z.lor (Z.lor (Z.lor (sx32z (d2v_blk 3 b0)) (sx32z (d2v_blk 2 b1))) (sx32z (d2v_blk 1 b2))) (sx32z (d2v_blk 0 b3)).

Definition all_hex4 (b0 b1 b2 b3 : Z) : Prop :=
  hexval b0 <> None /\ hexval b1 <> None /\ hexval b2 <> None /\ hexval b3 <> None.

Lemma sx32z_blk_valid : forall blk c v, 0 <= blk <= 3 -> hexval c = Some v -> sx32z (d2v_blk blk c) = Z.shiftl v (4 * blk) /\ 0 <= Z.shiftl v (4 * blk) < 2 ^ (4 * blk + 4).
Proof.
  intros blk c v Hb H. unfold d2v_blk. rewrite H. pose proof (hexval_range c v H).
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (P : 0 < 2 ^ (4 * blk)) by (apply Z.pow_pos_nonneg; lia).
  assert (P4 : 2 ^ (4 * blk + 4) = 2 ^ (4 * blk) * 16) by (rewrite Z.pow_add_r by lia; reflexivity).
  assert (Pm : 2 ^ (4 * blk) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  split; [|nia]. unfold sx32z. replace (v * 2 ^ (4 * blk) <? 2147483648) with true; [reflexivity|].
  symmetry. apply Z.ltb_lt. change (2 ^ 12) with 4096 in Pm. nia.
Qed.

Lemma sx32z_blk_invalid : forall blk c, hexval c = None -> sx32z (d2v_blk blk c) = -1.
Proof. intros blk c H. unfold d2v_blk. rewrite H. reflexivity. Qed.

Lemma lor_m1_l : forall x, Z.lor (-1) x = -1.
Proof. intros x. apply Z.lor_m1_l. Qed.
Lemma lor_m1_r : forall x, Z.lor x (-1) = -1.
Proof. intros x. apply Z.lor_m1_r. Qed.

Lemma hex4_invalid : forall b0 b1 b2 b3, ~ all_hex4 b0 b1 b2 b3 -> hex4 b0 b1 b2 b3 = -1.
Proof.
  intros b0 b1 b2 b3 N. unfold hex4, all_hex4 in *.
  destruct (hexval b0) eqn:E0; [|rewrite (sx32z_blk_invalid 3 b0 E0), !lor_m1_l; reflexivity].
  destruct (hexval b1) eqn:E1; [|rewrite (sx32z_blk_invalid 2 b1 E1), lor_m1_r, !lor_m1_l; reflexivity].
  destruct (hexval b2) eqn:E2; [|rewrite (sx32z_blk_invalid 1 b2 E2), lor_m1_r, lor_m1_l; reflexivity].
  destruct (hexval b3) eqn:E3; [|rewrite (sx32z_blk_invalid 0 b3 E3), lor_m1_r; reflexivity].
  exfalso. apply N. repeat split; discriminate.
Qed.

Lemma hex4_valid : forall b0 b1 b2 b3, all_hex4 b0 b1 b2 b3 -> 0 <= hex4 b0 b1 b2 b3 < 65536.
Proof.
  intros b0 b1 b2 b3 (H0 & H1 & H2 & H3). unfold hex4.
  destruct (hexval b0) as [v0|] eqn:E0; [|congruence]. destruct (hexval b1) as [v1|] eqn:E1; [|congruence].
  destruct (hexval b2) as [v2|] eqn:E2; [|congruence]. destruct (hexval b3) as [v3|] eqn:E3; [|congruence].
  destruct (sx32z_blk_valid 3 b0 v0 ltac:(lia) E0) as [-> _]. destruct (sx32z_blk_valid 2 b1 v1 ltac:(lia) E1) as [-> _].
  destruct (sx32z_blk_valid 1 b2 v2 ltac:(lia) E2) as [-> _]. destruct (sx32z_blk_valid 0 b3 v3 ltac:(lia) E3) as [-> _].
  pose proof (hexval_range _ _ E0). pose proof (hexval_range _ _ E1). pose proof (hexval_range _ _ E2). pose proof (hexval_range _ _ E3).
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ (4 * 3)) with 4096. change (2 ^ (4 * 2)) with 256. change (2 ^ (4 * 1)) with 16. change (2 ^ (4 * 0)) with 1.
  assert (L2 : forall x n, 0 < n -> 0 <= x < 2 ^ n -> Z.log2 x < n).
  { intros x n Hn Hx. destruct (Z.eq_dec x 0) as [->|Ex]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (B : forall x y n, 0 < n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n).
  { intros x y n Hn Hx Hy. split; [apply Z.lor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [rewrite E; lia|].
    apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg x y); lia|]. rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; apply L2; lia. }
  assert (B16 : forall x y, 0 <= x < 65536 -> 0 <= y < 65536 -> 0 <= Z.lor x y < 65536).
  { intros x y Hx Hy. pose proof (B x y 16 ltac:(lia)) as HB. change (2 ^ 16) with 65536 in HB. apply HB; assumption. }
  apply B16; [apply B16; [apply B16|]|]; lia.
Qed.

(* [comment removed for export] *)
Definition esc_map (c : Z) : Z :=
  if c =? 34 then 34 else if c =? 47 then 47 else if c =? 92 then 92 else if c =? 98 then 8 else if c =? 102 then 12
  else if c =? 110 then 10 else if c =? 114 then 13 else if c =? 116 then 9 else 0.
Definition esc_table : list Z := map (fun i => esc_map (Z.of_nat i)) (seq 0 256).

(* [comment removed for export] *)
Definition sow_neg (c : Z) : Z :=
  if (c =? 9) || (c =? 10) || (c =? 13) || (c =? 32) || (c =? 44) || (c =? 58) || (c =? 91) || (c =? 93) || (c =? 123) || (c =? 125)
  then 0 else 1.
Definition sow_table : list Z := map (fun i => sow_neg (Z.of_nat i)) (seq 0 256).
