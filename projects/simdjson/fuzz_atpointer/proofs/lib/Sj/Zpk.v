(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi SjTape Zpj.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition Tf (l : list Z) : Z -> Z := fun i => nth (Z.to_nat i) l 0.

Fixpoint zupd (l : list Z) (i : nat) (v : Z) : list Z :=
  match l, i with
  | [], _ => []
  | _ :: l', O => v :: l'
  | y :: l', S i' => y :: zupd l' i' v
  end.

Lemma zupd_length : forall l i v, length (zupd l i v) = length l.
Proof. induction l as [|y l IH]; intros [|i] v; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma nth_zupd_same : forall l i v, (i < length l)%nat -> nth i (zupd l i v) 0 = v.
Proof. induction l as [|y l IH]; intros [|i] v H; cbn in *; try lia. apply IH. lia. Qed.

Lemma nth_zupd_other : forall l i j v, i <> j -> nth j (zupd l i v) 0 = nth j l 0.
Proof.
  induction l as [|y l IH]; intros [|i] [|j] v H; cbn; try reflexivity; try congruence. apply IH. congruence.
Qed.

Lemma Tf_app_l : forall l r i, 0 <= i < Z.of_nat (length l) -> Tf (l ++ r) i = Tf l i.
Proof. intros l r i H. unfold Tf. apply app_nth1. lia. Qed.

Lemma Tf_app_r : forall l r Wv j, Z.of_nat (length l) = Wv -> 0 <= j -> Tf (l ++ r) (Wv + j) = Tf r j.
Proof.
  intros l r Wv j HL Hj. unfold Tf. rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma Tf_app_r0 : forall l r Wv, Z.of_nat (length l) = Wv -> Tf (l ++ r) Wv = Tf r 0.
Proof. intros l r Wv HL. rewrite <- (Tf_app_r l r Wv 0 HL) by lia. f_equal. lia. Qed.

Lemma Tf_zupd_same : forall l i v, 0 <= i < Z.of_nat (length l) -> Tf (zupd l (Z.to_nat i) v) i = v.
Proof. intros l i v H. unfold Tf. apply nth_zupd_same. lia. Qed.

Lemma Tf_zupd_other : forall l i j v, 0 <= i -> 0 <= j -> i <> j -> Tf (zupd l (Z.to_nat i) v) j = Tf l j.
Proof. intros l i j v Hi Hj H. unfold Tf. apply nth_zupd_other. lia. Qed.

Lemma frameT_app : forall l r Wv, Z.of_nat (length l) = Wv -> frameT Wv (Tf l) (Tf (l ++ r)).
Proof. intros l r Wv HL x Hx. apply Tf_app_l. lia. Qed.

Lemma frameS_app : forall l r sn, Z.of_nat (length l) = sn -> frameS sn (Tf l) (Tf (l ++ r)).
Proof. intros l r sn HL x Hx. apply Tf_app_l. lia. Qed.

Lemma frameTx_zupd_app : forall l r Wv ti v, Z.of_nat (length l) = Wv -> 0 <= ti ->
  frameTx Wv ti (Tf l) (Tf (zupd l (Z.to_nat ti) v ++ r)).
Proof.
  intros l r Wv ti v HL Hti x Hx Hne. rewrite Tf_app_l by (rewrite zupd_length; lia).
  apply Tf_zupd_other; lia.
Qed.

Lemma Tf_zupd_app_same : forall l r ti v, 0 <= ti < Z.of_nat (length l) -> Tf (zupd l (Z.to_nat ti) v ++ r) ti = v.
Proof. intros l r ti v H. rewrite Tf_app_l by (rewrite zupd_length; lia). apply Tf_zupd_same. exact H. Qed.

Lemma Tf_zupd_app_r0 : forall l r Wv ti v, Z.of_nat (length l) = Wv -> Tf (zupd l (Z.to_nat ti) v ++ r) Wv = Tf r 0.
Proof. intros l r Wv ti v HL. apply Tf_app_r0. rewrite zupd_length. exact HL. Qed.

Definition le4z (d : Z) : list Z := [d mod 256; (d / 256) mod 256; (d / 65536) mod 256; (d / 16777216) mod 256].
Definition srec (d : Z) (cb : list Z) : list Z := le4z d ++ cb ++ [0].

Lemma srec_length : forall d cb, Z.of_nat (length cb) = d -> Z.of_nat (length (srec d cb)) = d + 5.
Proof. intros d cb H. unfold srec, le4z. rewrite !length_app. cbn [length]. lia. Qed.

Lemma wrote_str_app : forall sbs sbv d cb, Z.of_nat (length sbs) = sbv -> Z.of_nat (length cb) = d -> 0 <= d < 2^32 ->
  wrote_str (Tf (sbs ++ srec d cb)) sbv d.
Proof.
  intros sbs sbv d cb HL HC Hd. unfold wrote_str, le32. split.
  - rewrite (Tf_app_r0 _ _ sbv HL), (Tf_app_r _ _ sbv 1 HL), (Tf_app_r _ _ sbv 2 HL), (Tf_app_r _ _ sbv 3 HL) by lia.
    unfold Tf, srec, le4z. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add app nth].
    change (Pos.to_nat 1) with 1%nat. change (Pos.to_nat 2) with 2%nat. change (Pos.to_nat 3) with 3%nat. cbn [nth].
    pose proof (Z.div_mod d 256 ltac:(lia)). pose proof (Z.div_mod (d / 256) 256 ltac:(lia)).
    pose proof (Z.div_mod (d / 256 / 256) 256 ltac:(lia)).
    rewrite !Z.div_div in * by lia. change (256 * 256) with 65536 in *. change (65536 * 256) with 16777216 in *.
    assert (d / 16777216 < 256) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= d / 16777216) by (apply Z.div_pos; lia).
    rewrite (Z.mod_small (d / 16777216)) by lia. lia.
  - replace (sbv + 4 + d) with (sbv + (4 + d)) by lia. rewrite (Tf_app_r _ _ sbv (4 + d) HL) by lia.
    unfold Tf, srec. rewrite app_nth2 by (unfold le4z; cbn [length]; lia).
    rewrite app_nth2 by (unfold le4z; cbn [length]; lia).
    replace (Z.to_nat (4 + d) - length (le4z d) - length cb)%nat with 0%nat by (unfold le4z; cbn [length]; lia). reflexivity.
Qed.

Lemma tinv_counts_cons : forall bs idxs CK l s g, Inv bs idxs l s -> TInv CK l s g -> (l = ObjCont \/ l = ArrCont) ->
  exists c cs, gC g = c :: cs.
Proof.
  intros bs idxs CK l s g HI (d & _ & HT) Hl. pose proof (inv_kind _ _ _ _ HI) as Hk.
  destruct Hl as [-> | ->]; cbn [kind_ok TInv] in *; destruct Hk as (ti & rest & E); rewrite E in HT; cbn [vafter vdone] in HT;
    destruct (gC g) as [|c cs]; try contradiction; eauto.
Qed.

Lemma land_hi_lo : forall n hi lo, 0 <= n -> 0 <= lo < 2^n -> Z.land (hi * 2^n) lo = 0.
Proof.
  intros n hi lo Hn Hlo. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec0 i n) as [L|L].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec lo 0) as [->|Hz]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 lo i); [apply andb_false_r|lia|].
    apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma lor_hi_lo : forall n hi lo, 0 <= n -> 0 <= lo < 2^n -> Z.lor (hi * 2^n) lo = hi * 2^n + lo.
Proof.
  intros n hi lo Hn Hlo. pose proof (land_hi_lo n hi lo Hn Hlo) as HL.
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma tword_lor : forall t v, 0 <= v < 2^56 -> Z.lor (Z.shiftl t 56) v = tword t v.
Proof. intros t v Hv. rewrite Z.shiftl_mul_pow2 by lia. unfold tword. apply lor_hi_lo; lia. Qed.

Lemma tword_lor' : forall t v, 0 <= v < 2^56 -> Z.lor v (Z.shiftl t 56) = tword t v.
Proof. intros t v Hv. rewrite Z.lor_comm. apply tword_lor. exact Hv. Qed.

Lemma cword_lor : forall t nxt cv, 0 <= nxt < 2^32 -> 0 <= cv < 2^24 ->
  Z.lor nxt (Z.lor (Z.shiftl cv 32) (Z.shiftl t 56)) = cword t nxt cv.
Proof.
  intros t nxt cv Hn Hc. unfold cword.
  rewrite (Z.lor_comm (Z.shiftl cv 32)), Z.lor_assoc, (Z.lor_comm nxt), <- Z.lor_assoc.
  rewrite (Z.shiftl_mul_pow2 cv) by lia. rewrite (Z.lor_comm nxt), (lor_hi_lo 32 cv nxt) by lia.
  rewrite tword_lor by lia. f_equal. lia.
Qed.

Lemma tword_range : forall t v, 0 <= t < 256 -> 0 <= v < 2^56 -> 0 <= tword t v < 2^64.
Proof. intros t v Ht Hv. unfold tword. lia. Qed.
Lemma cword_range : forall t nxt cv, 0 <= t < 256 -> 0 <= nxt < 2^32 -> 0 <= cv < 2^24 -> 0 <= cword t nxt cv < 2^64.
Proof. intros t nxt cv Ht Hn Hc. unfold cword. apply tword_range; lia. Qed.
