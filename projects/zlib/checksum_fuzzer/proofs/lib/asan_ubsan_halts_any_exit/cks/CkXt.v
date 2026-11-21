(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.



Definition xt (c : Z) : Z := Z.lxor (Z.shiftr c 1) (if Z.odd c then POLY else 0).

Lemma bstep_xt : forall b, bstep b = xt b.
Proof. intros b. unfold bstep, xt. destruct (Z.odd b); [reflexivity | now rewrite Z.lxor_0_r]. Qed.

Fixpoint xtn (n : nat) (c : Z) : Z :=
  match n with O => c | S k => xtn k (xt c) end.

Lemma xtn_O : forall c, xtn 0 c = c. Proof. reflexivity. Qed.
Lemma xtn_S : forall n c, xtn (S n) c = xtn n (xt c). Proof. reflexivity. Qed.

Lemma xtn_add : forall m n c, xtn (m + n) c = xtn n (xtn m c).
Proof.
  induction m as [|m IH]; intros n c; cbn; [reflexivity | apply IH].
Qed.

Lemma xtn_S_out : forall n c, xtn (S n) c = xt (xtn n c).
Proof.
  intros n c. replace (S n) with (n + 1)%nat by lia.
  rewrite xtn_add. reflexivity.
Qed.


Lemma odd_lxor : forall a b, Z.odd (Z.lxor a b) = xorb (Z.odd a) (Z.odd b).
Proof.
  intros a b. rewrite <- !Z.bit0_odd. rewrite Z.lxor_spec. reflexivity.
Qed.

Lemma shiftr_lxor : forall a b n,
  Z.shiftr (Z.lxor a b) n = Z.lxor (Z.shiftr a n) (Z.shiftr b n).
Proof.
  intros a b n. apply Z.bits_inj'. intros m Hm.
  rewrite Z.lxor_spec, !Z.shiftr_spec, Z.lxor_spec by lia. reflexivity.
Qed.

Lemma xt_xor : forall a b, xt (Z.lxor a b) = Z.lxor (xt a) (xt b).
Proof.
  intros a b. unfold xt. rewrite shiftr_lxor, odd_lxor.
  destruct (Z.odd a), (Z.odd b); cbn [xorb];
    apply Z.bits_inj'; intros m Hm;
    rewrite ?Z.lxor_spec, ?Z.bits_0; btauto.
Qed.

Lemma xtn_xor : forall n a b, xtn n (Z.lxor a b) = Z.lxor (xtn n a) (xtn n b).
Proof.
  induction n as [|n IH]; intros a b; cbn; [reflexivity|].
  rewrite xt_xor. apply IH.
Qed.

Lemma xt_0 : xt 0 = 0. Proof. reflexivity. Qed.

Lemma xtn_0 : forall n, xtn n 0 = 0.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [xtn]. rewrite xt_0. exact IH. Qed.


Lemma lxor_bound32 : forall a b,
  0 <= a < 4294967296 -> 0 <= b < 4294967296 -> 0 <= Z.lxor a b < 4294967296.
Proof.
  intros a b Ha Hb.
  assert (Hn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [exact Hn|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|Hz]; [rewrite E; lia|].
  replace 4294967296 with (2 ^ 32) by reflexivity.
  apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 32 ltac:(lia))).
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [E|Ha0]; [rewrite E; cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 a 32 ltac:(lia))). cbn. lia.
  - destruct (Z.eq_dec b 0) as [E|Hb0]; [rewrite E; cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 b 32 ltac:(lia))). cbn. lia.
Qed.

Lemma xt_range : forall c, 0 <= c < 4294967296 -> 0 <= xt c < 4294967296.
Proof.
  intros c Hc. unfold xt.
  assert (H1 : 0 <= Z.shiftr c 1 < 4294967296).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with c; [apply Z.div_le_upper_bound; lia | lia]. }
  destruct (Z.odd c).
  - apply lxor_bound32; [exact H1 | unfold POLY; lia].
  - rewrite Z.lxor_0_r. exact H1.
Qed.

Lemma xtn_range : forall n c, 0 <= c < 4294967296 -> 0 <= xtn n c < 4294967296.
Proof.
  induction n as [|n IH]; intros c Hc; cbn; [exact Hc | apply IH, xt_range, Hc].
Qed.


Lemma xt_even : forall v, 0 <= v -> Z.odd v = false -> xt v = Z.shiftr v 1.
Proof. intros v _ Hv. unfold xt. rewrite Hv. apply Z.lxor_0_r. Qed.

Lemma odd_shiftl_S : forall b k, 0 <= b -> Z.odd (Z.shiftl b (Z.of_nat (S k))) = false.
Proof.
  intros b k Hb. rewrite <- Z.bit0_odd, Z.shiftl_spec_low by lia. reflexivity.
Qed.

Lemma shiftr_shiftl_S : forall b k, 0 <= b ->
  Z.shiftr (Z.shiftl b (Z.of_nat (S k))) 1 = Z.shiftl b (Z.of_nat k).
Proof.
  intros b k Hb. rewrite Z.shiftr_shiftl_l by lia.
  f_equal. lia.
Qed.

Lemma xtn_shiftl : forall k m b, 0 <= b ->
  xtn k (Z.shiftl b (Z.of_nat (k + m))) = Z.shiftl b (Z.of_nat m).
Proof.
  induction k as [|k IH]; intros m b Hb; cbn [xtn].
  - f_equal.
  - replace (S k + m)%nat with (S (k + m)) by lia.
    rewrite xt_even by
      (first [ apply Z.shiftl_nonneg; exact Hb | apply odd_shiftl_S; exact Hb ]).
    rewrite shiftr_shiftl_S by exact Hb. apply IH. exact Hb.
Qed.

Corollary xtn_shiftl_exact : forall k b, 0 <= b ->
  xtn k (Z.shiftl b (Z.of_nat k)) = b.
Proof.
  intros k b Hb.
  replace (Z.of_nat k) with (Z.of_nat (k + 0)) by (f_equal; lia).
  rewrite (xtn_shiftl k 0 b Hb). cbn [Z.of_nat]. apply Z.shiftl_0_r.
Qed.

Lemma xtn_shifted_byte : forall n k b, 0 <= b -> (k <= n)%nat ->
  xtn n (Z.shiftl b (Z.of_nat k)) = xtn (n - k) b.
Proof.
  intros n k b Hb Hk.
  replace n with (k + (n - k))%nat at 1 by lia.
  rewrite xtn_add, xtn_shiftl_exact by exact Hb. reflexivity.
Qed.


Definition byteZ (c : Z) (k : nat) : Z :=
  Z.land (Z.shiftr c (8 * Z.of_nat k)) 255.

Lemma byteZ_range : forall c k, 0 <= byteZ c k < 256.
Proof.
  intros c k. unfold byteZ.
  replace 255 with (Z.ones 8) by reflexivity.
  rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256. apply Z.mod_pos_bound. lia.
Qed.

Definition crc_tab (n : Z) : Z := xtn 8 n.

Definition crc_step (c b : Z) : Z := xtn 8 (Z.lxor c b).

Definition crc_fold (c : Z) (bs : list Z) : Z := fold_left crc_step bs c.

Definition crc32_math (init : Z) (bs : list Z) : Z :=
  Z.lxor (crc_fold (Z.lxor init M32) bs) M32.

Lemma crc_fold_nil : forall c, crc_fold c [] = c. Proof. reflexivity. Qed.
Lemma crc_fold_cons : forall c b bs, crc_fold c (b :: bs) = crc_fold (crc_step c b) bs.
Proof. reflexivity. Qed.
Lemma crc_fold_app : forall bs cs c, crc_fold c (bs ++ cs) = crc_fold (crc_fold c bs) cs.
Proof. intros bs cs c. unfold crc_fold. apply fold_left_app. Qed.

Lemma crc_fold_range : forall bs c, 0 <= c < 4294967296 ->
  (forall b, In b bs -> 0 <= b < 256) -> 0 <= crc_fold c bs < 4294967296.
Proof.
  induction bs as [|b bs IH]; intros c Hc Hb; [exact Hc|].
  rewrite crc_fold_cons. apply IH.
  - unfold crc_step. apply xtn_range. apply lxor_bound32; [exact Hc|].
    assert (Hb0 : 0 <= b < 256) by (apply Hb; left; reflexivity). lia.
  - intros x Hx. apply Hb. right. exact Hx.
Qed.


Definition wordLE (b0 b1 b2 b3 : Z) : Z :=
  Z.lxor b0 (Z.lxor (Z.shiftl b1 8) (Z.lxor (Z.shiftl b2 16) (Z.shiftl b3 24))).

Lemma xtn_wordLE : forall n b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 -> (24 <= n)%nat ->
  xtn n (wordLE b0 b1 b2 b3)
  = Z.lxor (xtn n b0)
      (Z.lxor (xtn (n - 8) b1) (Z.lxor (xtn (n - 16) b2) (xtn (n - 24) b3))).
Proof.
  intros n b0 b1 b2 b3 H0 H1 H2 H3 Hn. unfold wordLE.
  rewrite !xtn_xor.
  replace 8 with (Z.of_nat 8) by reflexivity.
  replace 16 with (Z.of_nat 16) by reflexivity.
  replace 24 with (Z.of_nat 24) by reflexivity.
  rewrite (xtn_shifted_byte n 8 b1) by (assumption || lia).
  rewrite (xtn_shifted_byte n 16 b2) by (assumption || lia).
  rewrite (xtn_shifted_byte n 24 b3) by (assumption || lia).
  reflexivity.
Qed.

Theorem crc_step4 : forall c b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  crc_step (crc_step (crc_step (crc_step c b0) b1) b2) b3
  = xtn 32 (Z.lxor c (wordLE b0 b1 b2 b3)).
Proof.
  intros c b0 b1 b2 b3 H0 H1 H2 H3. unfold crc_step.
  rewrite (xtn_xor 32 c (wordLE b0 b1 b2 b3)).
  rewrite (xtn_wordLE 32 b0 b1 b2 b3) by (assumption || lia).
  cbn [Nat.sub].
  rewrite !xtn_xor, <- !xtn_add.
  cbn [Nat.add].
  rewrite !Z.lxor_assoc. reflexivity.
Qed.

Definition braid_tab (k : nat) (i : Z) : Z := xtn ((23 - k) * 8) (Z.shiftl i 24).

Lemma braid_tab_alt : forall k i, 0 <= i -> (k <= 3)%nat ->
  braid_tab k i = xtn ((23 - k) * 8 - 24) i.
Proof.
  intros k i Hi Hk. unfold braid_tab.
  replace 24 with (Z.of_nat 24) by reflexivity.
  rewrite (xtn_shifted_byte ((23 - k) * 8) 24 i) by (assumption || lia).
  reflexivity.
Qed.

Definition braid_round4 (b0 b1 b2 b3 : Z) : Z :=
  Z.lxor (braid_tab 0 b0)
    (Z.lxor (braid_tab 1 b1) (Z.lxor (braid_tab 2 b2) (braid_tab 3 b3))).

Theorem braid_round4_xtn : forall b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  braid_round4 b0 b1 b2 b3 = xtn 160 (wordLE b0 b1 b2 b3).
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold braid_round4.
  rewrite !braid_tab_alt by (assumption || lia).
  rewrite (xtn_wordLE 160 b0 b1 b2 b3) by (assumption || lia).
  cbn [Nat.sub Nat.mul]. reflexivity.
Qed.

Definition absorb4 (c w : Z) : Z := xtn 32 (Z.lxor c w).

Lemma braid_round4_absorb : forall c b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  xtn 128 (absorb4 c (wordLE b0 b1 b2 b3))
  = xtn 160 (Z.lxor c (wordLE b0 b1 b2 b3)).
Proof.
  intros. unfold absorb4. rewrite <- xtn_add. reflexivity.
Qed.


Lemma testbit_high : forall v n m, 0 <= v < 2 ^ n -> 0 <= n <= m ->
  Z.testbit v m = false.
Proof.
  intros v n m Hv Hm.
  destruct (Z.eq_dec v 0) as [E|Hv0]; [rewrite E; apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 v < n) by (apply (proj1 (Z.log2_lt_pow2 v n ltac:(lia))); lia).
  lia.
Qed.

Lemma land_shiftl_disj : forall x y k, 0 <= x < 2 ^ k -> 0 <= k -> 0 <= y ->
  Z.land x (Z.shiftl y k) = 0.
Proof.
  intros x y k Hx Hk Hy. apply Z.bits_inj'. intros m Hm.
  rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec m k) as [Hlt|Hge].
  - rewrite (Z.testbit_neg_r y (m - k)) by lia. apply Bool.andb_false_r.
  - rewrite (testbit_high x k m Hx) by lia. reflexivity.
Qed.

Lemma lxor_shiftl_add : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b ->
  Z.lxor a (Z.shiftl b k) = a + 2 ^ k * b.
Proof.
  intros a b k Hk Ha Hb. rewrite <- Z.add_nocarry_lxor.
  - rewrite Z.shiftl_mul_pow2 by lia. lia.
  - apply land_shiftl_disj; [exact Ha | exact Hk | exact Hb].
Qed.

Lemma wordLE_sum : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  wordLE b0 b1 b2 b3 = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold wordLE.
  replace (Z.shiftl b3 24) with (Z.shiftl (Z.shiftl b3 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- (Z.shiftl_lxor b2 (Z.shiftl b3 8) 16).
  rewrite (lxor_shiftl_add b2 b3 8) by (change (2 ^ 8) with 256; lia).
  replace (Z.shiftl (b2 + 2 ^ 8 * b3) 16) with (Z.shiftl (Z.shiftl (b2 + 2 ^ 8 * b3) 8) 8)
    by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- (Z.shiftl_lxor b1 _ 8).
  rewrite (lxor_shiftl_add b1 (b2 + 2 ^ 8 * b3) 8) by (change (2 ^ 8) with 256; lia).
  rewrite (lxor_shiftl_add b0 _ 8) by (change (2 ^ 8) with 256; lia).
  change (2 ^ 8) with 256. lia.
Qed.

Lemma byteZ_divmod : forall v k, byteZ v k = (v / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
  intros v k. unfold byteZ. change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma wordLE_bytes : forall v, 0 <= v < 4294967296 ->
  wordLE (byteZ v 0) (byteZ v 1) (byteZ v 2) (byteZ v 3) = v.
Proof.
  intros v Hv.
  assert (B0 : byteZ v 0 = v mod 256).
  { rewrite byteZ_divmod. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity. }
  assert (B1 : byteZ v 1 = (v / 256) mod 256).
  { rewrite byteZ_divmod. change (2 ^ (8 * Z.of_nat 1)) with 256. reflexivity. }
  assert (B2 : byteZ v 2 = (v / 65536) mod 256).
  { rewrite byteZ_divmod. change (2 ^ (8 * Z.of_nat 2)) with 65536. reflexivity. }
  assert (B3 : byteZ v 3 = (v / 16777216) mod 256).
  { rewrite byteZ_divmod. change (2 ^ (8 * Z.of_nat 3)) with 16777216. reflexivity. }
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (v / 256) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (v / 65536) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (v / 16777216) 256 ltac:(lia)).
  rewrite wordLE_sum by (rewrite ?B0, ?B1, ?B2, ?B3; lia).
  rewrite B0, B1, B2, B3.
  assert (E1 : v = 256 * (v / 256) + v mod 256) by (apply Z.div_mod; lia).
  assert (E2 : v / 256 = 256 * (v / 65536) + (v / 256) mod 256).
  { replace (v / 65536) with (v / 256 / 256) by (rewrite Z.div_div by lia; reflexivity).
    apply Z.div_mod. lia. }
  assert (E3 : v / 65536 = 256 * (v / 16777216) + (v / 65536) mod 256).
  { replace (v / 16777216) with (v / 65536 / 256) by (rewrite Z.div_div by lia; reflexivity).
    apply Z.div_mod. lia. }
  assert (E4 : (v / 16777216) mod 256 = v / 16777216).
  { apply Z.mod_small. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; lia. }
  lia.
Qed.

