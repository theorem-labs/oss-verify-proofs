(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.



Definition xt (c : Z) : Z := Z.lxor (Z.shiftr c 1) (if Z.odd c then POLY else 0).


Fixpoint xtn (n : nat) (c : Z) : Z :=
  match n with O => c | S k => xtn k (xt c) end.












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










Definition crc_step (c b : Z) : Z := xtn 8 (Z.lxor c b).

Definition crc_fold (c : Z) (bs : list Z) : Z := fold_left crc_step bs c.

Lemma crc_fold_cons : forall c b bs, crc_fold c (b :: bs) = crc_fold (crc_step c b) bs.
Proof. reflexivity. Qed.

Lemma crc_fold_range : forall bs c, 0 <= c < 4294967296 ->
  (forall b, In b bs -> 0 <= b < 256) -> 0 <= crc_fold c bs < 4294967296.
Proof.
  induction bs as [|b bs IH]; intros c Hc Hb; [exact Hc|].
  rewrite crc_fold_cons. apply IH.
  - unfold crc_step. apply xtn_range. apply lxor_bound32; [exact Hc|].
    assert (Hb0 : 0 <= b < 256) by (apply Hb; left; reflexivity). lia.
  - intros x Hx. apply Hb. right. exact Hx.
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





