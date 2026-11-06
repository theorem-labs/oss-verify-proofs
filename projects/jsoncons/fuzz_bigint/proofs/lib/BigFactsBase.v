(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BigModel.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.

Ltac bdall := repeat match goal with
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wordZ (w : Z) : Prop := 0 <= w < W.M.
Definition words_ok (ws : words) : Prop := Forall wordZ ws.

Lemma M_pos : 0 < W.M. Proof. reflexivity. Qed.
Lemma M_val : W.M = 18446744073709551616. Proof. reflexivity. Qed.
Lemma half_val : W.half = 4294967296. Proof. reflexivity. Qed.
Lemma M_half : W.M = W.half * W.half. Proof. reflexivity. Qed.
Lemma max_word_val : W.max_word = 18446744073709551615. Proof. reflexivity. Qed.
Lemma r_mask_val : W.r_mask = 4294967295. Proof. reflexivity. Qed.
Lemma l_mask_val : W.l_mask = 18446744069414584320. Proof. reflexivity. Qed.
Lemma l_bit_val : W.l_bit = 9223372036854775808. Proof. reflexivity. Qed.
Lemma r_mask_ones : W.r_mask = Z.ones 32. Proof. reflexivity. Qed.
Global Opaque W.M W.half W.max_word W.r_mask W.l_mask W.l_bit.
Arguments W.M : simpl never.
Arguments W.half : simpl never.

Lemma wrap_range z : wordZ (W.wrap z).
Proof. unfold wordZ, W.wrap. pose proof M_pos. split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; lia. Qed.
Lemma wrap_id z : wordZ z -> W.wrap z = z.
Proof. unfold wordZ, W.wrap. intros. apply Z.mod_small. lia. Qed.
Lemma add_range a b : wordZ (W.add a b). Proof. apply wrap_range. Qed.
Lemma sub_range a b : wordZ (W.sub a b). Proof. apply wrap_range. Qed.
Lemma mul_range a b : wordZ (W.mul a b). Proof. apply wrap_range. Qed.
Lemma shl_range a k : wordZ (W.shl a k). Proof. apply wrap_range. Qed.
Lemma b2z_range b : 0 <= W.b2z b <= 1. Proof. destruct b; simpl; lia. Qed.
Lemma shr_range a k : wordZ a -> 0 <= k -> wordZ (W.shr a k).
Proof. unfold wordZ, W.shr. intros. pose proof (Z.pow_pos_nonneg 2 k).
  split. apply Z.div_pos; lia. apply Z.le_lt_trans with a. 2: lia.
  apply Z.div_le_upper_bound. lia. nia. Qed.
Lemma land_range a b : wordZ a -> wordZ b -> wordZ (W.land a b).
Proof. unfold wordZ, W.land. rewrite M_val. intros. change 18446744073709551616 with (2^64) in *. split. apply Z.land_nonneg; lia.
  destruct (Z.eq_dec (Z.land a b) 0). lia.
  assert (Hp: 0 < Z.land a b) by (pose proof (Z.land_nonneg a b); lia).
  destruct (Z.eq_dec a 0). subst. rewrite Z.land_0_l in n. lia.
  assert (Z.log2 (Z.land a b) <= Z.log2 a). { pose proof (Z.log2_land a b). lia. }
  assert (Z.log2 a < 64). { apply Z.log2_lt_pow2; lia. }
  assert (H3: Z.log2 (Z.land a b) < 64) by lia.
  apply Z.log2_lt_pow2 in H3. lia. lia. Qed.
Lemma lor_range a b : wordZ a -> wordZ b -> wordZ (W.lor a b).
Proof. unfold wordZ, W.lor. rewrite M_val. intros. change 18446744073709551616 with (2^64) in *. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec a 0). subst. rewrite Z.lor_0_l. lia.
  destruct (Z.eq_dec b 0). subst. rewrite Z.lor_0_r. lia.
  assert (Hp: 0 < Z.lor a b). { pose proof (Z.lor_nonneg a b). assert (Z.lor a b <> 0). { intro E. apply Z.lor_eq_0_iff in E. lia. } lia. }
  apply Z.log2_lt_pow2. lia. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia. Qed.
Lemma divu_range a b : wordZ a -> wordZ b -> wordZ (W.divu a b).
Proof. unfold wordZ, W.divu. rewrite max_word_val, M_val. intros. bdall. lia. split. apply Z.div_pos; lia.
  apply Z.le_lt_trans with a. apply Z.div_le_upper_bound; nia. lia. Qed.
Lemma remu_range a b : wordZ a -> wordZ b -> wordZ (W.remu a b).
Proof. unfold wordZ, W.remu. intros. bdall. lia. pose proof (Z.mod_pos_bound a b). lia. Qed.

Lemma words_ok_nil : words_ok []. Proof. constructor. Qed.
Lemma words_ok_cons w ws : wordZ w -> words_ok ws -> words_ok (w :: ws). Proof. intros; constructor; auto. Qed.
Lemma words_ok_app a b : words_ok a -> words_ok b -> words_ok (a ++ b).
Proof. unfold words_ok. intros. apply Forall_app; auto. Qed.
Lemma words_ok_app_inv a b : words_ok (a ++ b) -> words_ok a /\ words_ok b.
Proof. unfold words_ok. intros H. apply Forall_app in H. exact H. Qed.
Lemma words_ok_zeros n : words_ok (zeros n).
Proof. unfold zeros, words_ok. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. unfold wordZ. pose proof M_pos. lia. Qed.
Lemma words_ok_firstn n ws : words_ok ws -> words_ok (firstn n ws).
Proof. intros. rewrite <- (firstn_skipn n ws) in H. apply words_ok_app_inv in H. tauto. Qed.
Lemma words_ok_skipn n ws : words_ok ws -> words_ok (skipn n ws).
Proof. intros. rewrite <- (firstn_skipn n ws) in H. apply words_ok_app_inv in H. tauto. Qed.
Lemma words_ok_nth ws i : words_ok ws -> wordZ (nth_w ws i).
Proof. unfold nth_w, words_ok. intros. destruct (Nat.lt_ge_cases i (length ws)).
  apply Forall_nth; auto. rewrite nth_overflow by lia. unfold wordZ; pose proof M_pos; lia. Qed.

Lemma upd_length ws i v : length (upd ws i v) = length ws.
Proof. revert i; induction ws; destruct i; simpl; auto. Qed.
Lemma upd_nth ws i v j : nth_w (upd ws i v) j = if (Nat.eqb i j && (j <? length ws))%nat then v else nth_w ws j.
Proof. unfold nth_w. revert i j; induction ws as [|w ws IH]; intros [|i] [|j]; simpl; auto.
  all: try (destruct (Nat.eqb i j); reflexivity).
  all: try (rewrite IH; destruct (Nat.eqb i j) eqn:E; simpl; auto). Qed.
Lemma upd_nth_same ws i v : (i < length ws)%nat -> nth_w (upd ws i v) i = v.
Proof. intros. rewrite upd_nth. rewrite Nat.eqb_refl. destruct (Nat.ltb_spec i (length ws)); simpl; auto; lia. Qed.
Lemma upd_nth_other ws i v j : i <> j -> nth_w (upd ws i v) j = nth_w ws j.
Proof. intros. rewrite upd_nth. destruct (Nat.eqb_spec i j); simpl; auto; lia. Qed.
Lemma upd_words_ok ws i v : words_ok ws -> wordZ v -> words_ok (upd ws i v).
Proof. revert i; induction ws; destruct i; simpl; intros; auto; inversion H; subst; constructor; auto. apply IHws; auto. Qed.
Lemma upd_app_l a b i v : (i < length a)%nat -> upd (a ++ b) i v = upd a i v ++ b.
Proof. revert i; induction a; intros [|i]; simpl; intros; try lia; auto. rewrite IHa; auto; lia. Qed.
Lemma upd_app_r a b i v : (length a <= i)%nat -> upd (a ++ b) i v = a ++ upd b (i - length a) v.
Proof. revert i; induction a; intros [|i]; simpl; intros; try lia; auto. rewrite IHa; auto; lia. Qed.
Lemma upd_overflow ws i v : (length ws <= i)%nat -> upd ws i v = ws.
Proof. revert i; induction ws; destruct i; simpl; intros; auto; try lia. rewrite IHws; auto; lia. Qed.
Lemma nth_w_app_l a b i : (i < length a)%nat -> nth_w (a ++ b) i = nth_w a i.
Proof. intros; unfold nth_w; apply app_nth1; auto. Qed.
Lemma nth_w_app_r a b i : (length a <= i)%nat -> nth_w (a ++ b) i = nth_w b (i - length a).
Proof. intros; unfold nth_w; apply app_nth2; auto. Qed.
Lemma nth_w_overflow ws i : (length ws <= i)%nat -> nth_w ws i = 0.
Proof. intros; unfold nth_w; apply nth_overflow; auto. Qed.
Lemma nth_w_zeros n i : nth_w (zeros n) i = 0.
Proof. unfold nth_w, zeros. destruct (Nat.lt_ge_cases i n). apply nth_repeat. rewrite nth_overflow; auto. rewrite repeat_length; auto. Qed.
Lemma zeros_length n : length (zeros n) = n. Proof. apply repeat_length. Qed.

(* [comment removed for export] *)
Fixpoint val (ws : words) : Z := match ws with [] => 0 | w :: t => w + W.M * val t end.

Lemma val_nil : val [] = 0. Proof. reflexivity. Qed.
Lemma val_cons w t : val (w :: t) = w + W.M * val t. Proof. reflexivity. Qed.
Lemma val_app a b : val (a ++ b) = val a + W.M ^ (Z.of_nat (length a)) * val b.
Proof. induction a as [|w a IH]. simpl app; simpl length; simpl Z.of_nat. rewrite Z.pow_0_r, val_nil. lia.
  simpl app; simpl length. rewrite !val_cons, IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma val_zeros n : val (zeros n) = 0.
Proof. unfold zeros; induction n. reflexivity. simpl repeat. rewrite val_cons, IHn. lia. Qed.
Lemma val_bound ws : words_ok ws -> 0 <= val ws < W.M ^ (Z.of_nat (length ws)).
Proof. induction ws as [|w ws IH]; intros. rewrite val_nil. simpl. lia. inversion H; subst. specialize (IH H3). unfold wordZ in H2.
  rewrite val_cons. simpl length. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. pose proof M_pos. nia. Qed.
Lemma val_nonneg ws : words_ok ws -> 0 <= val ws. Proof. intros H; apply val_bound in H; lia. Qed.
Lemma val_upd ws i v : (i < length ws)%nat ->
  val (upd ws i v) = val ws + (v - nth_w ws i) * W.M ^ (Z.of_nat i).
Proof. revert i; induction ws as [|w ws IH]; intros [|i]; simpl length; simpl upd; intros; try lia. rewrite !val_cons. unfold nth_w; simpl nth. rewrite Z.pow_0_r. lia.
  rewrite !val_cons. rewrite IH by lia. unfold nth_w; simpl nth. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma val_firstn_skipn n ws : val ws = val (firstn n ws) + W.M ^ (Z.of_nat (length (firstn n ws))) * val (skipn n ws).
Proof. rewrite <- (firstn_skipn n ws) at 1. apply val_app. Qed.
Lemma val_cons_nth ws : ws <> [] -> val ws = nth_w ws 0 + W.M * val (skipn 1 ws).
Proof. destruct ws; intros. congruence. reflexivity. Qed.
Lemma val_single_nth ws i : (i < length ws)%nat ->
  val ws = val (firstn i ws) + W.M ^ Z.of_nat i * (nth_w ws i + W.M * val (skipn (S i) ws)).
Proof. intros. rewrite (val_firstn_skipn i ws) at 1. rewrite length_firstn, Nat.min_l by lia.
  f_equal. f_equal. rewrite (val_cons_nth (skipn i ws)). 2:{ intro E. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. simpl in E. lia. }
  unfold nth_w. rewrite nth_skipn, Nat.add_0_r. rewrite skipn_skipn. f_equal. Qed.

(* [comment removed for export] *)
Lemma val_removelast ws : ws <> [] -> val ws = val (removelast ws) + last ws 0 * W.M ^ (Z.of_nat (length ws) - 1).
Proof. intros H. assert (E := app_removelast_last 0 H).
  assert (L: length ws = S (length (removelast ws))). { rewrite E at 1. rewrite length_app. simpl. lia. }
  rewrite E at 1. rewrite val_app, val_cons, val_nil, L. rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat (length (removelast ws))) - 1) with (Z.of_nat (length (removelast ws))) by lia. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma add_carry a b : wordZ a -> wordZ b ->
  W.add a b + W.M * W.b2z (W.ltu (W.add a b) a) = a + b.
Proof. unfold wordZ, W.add, W.wrap, W.ltu, W.b2z. intros.
  destruct (Z_lt_le_dec (a + b) W.M).
  - rewrite Z.mod_small by lia. bdall; lia.
  - replace ((a + b) mod W.M) with (a + b - W.M). bdall; lia.
    apply Z.mod_unique with 1; lia. Qed.
(* [comment removed for export] *)
Lemma add_carry' a b : wordZ a -> wordZ b ->
  W.add a b + W.M * W.b2z (W.ltu (W.add a b) b) = a + b.
Proof. intros. replace (W.add a b) with (W.add b a). rewrite add_carry; auto; lia. unfold W.add; f_equal; lia. Qed.
Lemma sub_borrow a b : wordZ a -> wordZ b ->
  W.sub a b = a - b + W.M * W.b2z (W.ltu a b).
Proof. unfold wordZ, W.sub, W.wrap, W.ltu, W.b2z. intros. bdall.
  - symmetry. apply Z.mod_unique with (-1); lia.
  - rewrite Z.mod_small; lia. Qed.
(* [comment removed for export] *)
Lemma sub_borrow_test a b : wordZ a -> wordZ b -> W.ltu a (W.sub a b) = W.ltu a b.
Proof. intros. pose proof (sub_borrow a b H H0). unfold W.ltu, W.b2z in *. unfold wordZ in *.
  destruct (Z.ltb_spec a b); bdall; auto; lia. Qed.
Lemma add_small a b : wordZ a -> wordZ b -> a + b < W.M -> W.add a b = a + b.
Proof. intros. unfold W.add. apply wrap_id. unfold wordZ in *. lia. Qed.
Lemma sub_small a b : wordZ a -> wordZ b -> b <= a -> W.sub a b = a - b.
Proof. intros. rewrite sub_borrow by auto. unfold W.ltu, W.b2z. bdall; lia. Qed.
Lemma mul_small a b : 0 <= a -> 0 <= b -> a * b < W.M -> W.mul a b = a * b.
Proof. intros. unfold W.mul. apply wrap_id. unfold wordZ. nia. Qed.

(* [comment removed for export] *)
Lemma halves a : wordZ a -> a = W.shr a 32 * W.half + W.land a W.r_mask /\ 0 <= W.shr a 32 < W.half /\ 0 <= W.land a W.r_mask < W.half.
Proof. unfold wordZ, W.shr, W.land. rewrite r_mask_ones. intros. rewrite Z.land_ones by lia.
  change (2^32) with 4294967296.
  rewrite half_val in *. rewrite M_val in *. split. rewrite Z.mul_comm. apply Z_div_mod_eq_full.
  split. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. apply Z.mod_pos_bound; lia. Qed.
Lemma shl32 a : wordZ a -> W.shl a 32 = (a mod W.half) * W.half.
Proof. unfold wordZ, W.shl, W.wrap. intros. change (2^32) with 4294967296. rewrite M_half, half_val.
  rewrite Z.mul_mod_distr_r. reflexivity. lia. lia. Qed.
Lemma shr32 a : W.shr a 32 = a / W.half. Proof. rewrite half_val. reflexivity. Qed.

(* [comment removed for export] *)
Theorem DDproduct_correct A B : wordZ A -> wordZ B ->
  let (hi, lo) := DDproduct A B in wordZ hi /\ wordZ lo /\ hi * W.M + lo = A * B.
Proof.
  intros HA HB. unfold DDproduct.
  destruct (halves A HA) as (EA & RA1 & RA2). destruct (halves B HB) as (EB & RB1 & RB2).
  set (ah := W.shr A 32) in *. set (al := W.land A W.r_mask) in *.
  set (bh := W.shr B 32) in *. set (bl := W.land B W.r_mask) in *.
  rewrite half_val in *. rewrite M_val.
  assert (Hll: W.mul al bl = al * bl) by (apply mul_small; rewrite ?M_val; nia).
  assert (Hhh: W.mul ah bh = ah * bh) by (apply mul_small; rewrite ?M_val; nia).
  assert (Hlh: W.mul al bh = al * bh) by (apply mul_small; rewrite ?M_val; nia).
  assert (Hhl: W.mul ah bl = ah * bl) by (apply mul_small; rewrite ?M_val; nia).
  rewrite Hll, Hhh, Hlh, Hhl.
  set (m1 := al * bh). set (m2 := ah * bl). set (lo0 := al * bl). set (hi0 := ah * bh).
  assert (W1: wordZ m1) by (unfold wordZ, m1; rewrite M_val; nia).
  assert (W2: wordZ m2) by (unfold wordZ, m2; rewrite M_val; nia).
  assert (W0: wordZ lo0) by (unfold wordZ, lo0; rewrite M_val; nia).
  assert (Wh: wordZ hi0) by (unfold wordZ, hi0; rewrite M_val; nia).
  rewrite (shl32 m1 W1), (shl32 m2 W2). rewrite !shr32. rewrite half_val.
  pose proof (Z_div_mod_eq_full m1 4294967296) as Dm1. pose proof (Z.mod_pos_bound m1 4294967296) as Bm1.
  pose proof (Z_div_mod_eq_full m2 4294967296) as Dm2. pose proof (Z.mod_pos_bound m2 4294967296) as Bm2.
  assert (D1: 0 <= m1 / 4294967296 < 4294967296). { split. apply Z.div_pos; unfold wordZ in W1; lia. apply Z.div_lt_upper_bound. lia. unfold m1; nia. }
  assert (D2: 0 <= m2 / 4294967296 < 4294967296). { split. apply Z.div_pos; unfold wordZ in W2; lia. apply Z.div_lt_upper_bound. lia. unfold m2; nia. }
  set (s1 := m1 mod 4294967296 * 4294967296). assert (Ws1: wordZ s1) by (unfold wordZ, s1; rewrite M_val; nia).
  set (s2 := m2 mod 4294967296 * 4294967296). assert (Ws2: wordZ s2) by (unfold wordZ, s2; rewrite M_val; nia).
  pose proof (add_carry lo0 s1 W0 Ws1) as C1.
  set (lo1 := W.add lo0 s1) in *. set (c1 := W.b2z (W.ltu lo1 lo0)) in *.
  assert (Wlo1: wordZ lo1) by apply add_range.
  pose proof (add_carry lo1 s2 Wlo1 Ws2) as C2.
  set (lo2 := W.add lo1 s2) in *. set (c2 := W.b2z (W.ltu lo2 lo1)) in *.
  assert (Wlo2: wordZ lo2) by apply add_range.
  pose proof (b2z_range (W.ltu lo1 lo0)). pose proof (b2z_range (W.ltu lo2 lo1)). fold c1 in H. fold c2 in H0.
  (* [comment removed for export] *)
  assert (KEY: (hi0 + (c1 + m1 / 4294967296) + (c2 + m2 / 4294967296)) * 18446744073709551616 + lo2 = A * B).
  { rewrite EA, EB. rewrite M_val in C1, C2. unfold hi0. unfold lo0 in C1. nia. }
  assert (Bhi: 0 <= hi0 + (c1 + m1 / 4294967296) + (c2 + m2 / 4294967296) < 18446744073709551616).
  { unfold wordZ in HA, HB, Wlo2. rewrite M_val in *. split. unfold hi0. nia.
    assert (A * B <= 18446744073709551615 * 18446744073709551615) by nia. nia. }
  assert (E1: W.add c1 (m1 / 4294967296) = c1 + m1 / 4294967296). { apply add_small; unfold wordZ; rewrite ?M_val; lia. }
  rewrite E1.
  (* [comment removed for export] *)
  assert (E2: W.add hi0 (c1 + m1 / 4294967296) = hi0 + (c1 + m1 / 4294967296)). { apply add_small; unfold wordZ in *; rewrite ?M_val in *; clear - Bhi D1 D2 H H0 Wh; lia. }
  rewrite E2.
  assert (E3: W.add c2 (m2 / 4294967296) = c2 + m2 / 4294967296). { apply add_small; unfold wordZ; rewrite ?M_val; lia. }
  rewrite E3.
  assert (E4: W.add (hi0 + (c1 + m1 / 4294967296)) (c2 + m2 / 4294967296) = hi0 + (c1 + m1 / 4294967296) + (c2 + m2 / 4294967296)).
  { apply add_small; unfold wordZ in *; rewrite ?M_val in *; clear - Bhi D1 D2 H H0 Wh; lia. }
  rewrite E4. split. unfold wordZ; rewrite M_val; lia. split. exact Wlo2. exact KEY.
Qed.

Lemma DDproduct_hi_bound A B : wordZ A -> wordZ B -> fst (DDproduct A B) <= W.M - 2.
Proof. intros. pose proof (DDproduct_correct A B H H0). destruct (DDproduct A B) as [hi lo]. simpl.
  destruct H1 as (Wh & Wl & E). unfold wordZ in *. rewrite M_val in *.
  assert (A * B <= 18446744073709551615 * 18446744073709551615) by nia. nia. Qed.
