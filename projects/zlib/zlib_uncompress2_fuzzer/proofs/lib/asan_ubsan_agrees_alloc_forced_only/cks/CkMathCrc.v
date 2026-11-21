(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Btauto.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkXt CkMultmodp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Definition bytes (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Lemma bytes_firstn : forall n bs, bytes bs -> bytes (firstn n bs).
Proof.
  unfold bytes. intros n bs H. revert n. induction H; intros [|n]; cbn; try constructor; auto.
Qed.

Lemma bytes_skipn : forall n bs, bytes bs -> bytes (skipn n bs).
Proof.
  unfold bytes. intros n bs H. revert n. induction H; intros [|n]; cbn; try constructor; auto.
Qed.

Lemma bytes_app : forall xs ys, bytes xs -> bytes ys -> bytes (xs ++ ys).
Proof. intros. apply Forall_app. split; assumption. Qed.

Lemma bytes_In : forall bs, bytes bs -> forall b, In b bs -> 0 <= b < 256.
Proof. intros bs H. apply Forall_forall. exact H. Qed.

Lemma firstn_add_skipn : forall {A} (a b : nat) (l : list A),
  firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof.
  intros A a. induction a as [|a IH]; intros b l; [reflexivity|].
  destruct l as [|x l]; cbn; [now rewrite firstn_nil | now rewrite IH].
Qed.

Lemma skipn_skipn' : forall {A} (a b : nat) (l : list A), skipn a (skipn b l) = skipn (b + a) l.
Proof. intros. rewrite skipn_skipn. f_equal. lia. Qed.


Lemma ctab_xtn : forall i, 0 <= i < 256 -> ctab i = xtn 8 i.
Proof.
  intros i Hi. unfold ctab.
  replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia.
  apply Z.eqb_eq.
  apply (forallb_seq_nth (fun j => nth j crc_table 0 =? xtn 8 (Z.of_nat j)) 0 256 (Z.to_nat i)); [|lia].
  vm_compute. reflexivity.
Qed.

Lemma ctab_crc_tab : forall i, 0 <= i < 256 -> ctab i = crc_tab i.
Proof. exact ctab_xtn. Qed.

Lemma btab_braid_tab : forall (k : nat) i, (k < 4)%nat -> 0 <= i < 256 ->
  btab (Z.of_nat k) i = braid_tab k i.
Proof.
  intros k i Hk Hi. unfold btab. rewrite Nat2Z.id.
  replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia.
  apply Z.eqb_eq.
  apply (forallb_seq_nth (fun j => nth j (nth k crc_braid_table []) 0 =? braid_tab k (Z.of_nat j)) 0 256 (Z.to_nat i)); [|lia].
  destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity .. | lia].
Qed.

Lemma ctab_range : forall i, 0 <= ctab i < 2 ^ 32.
Proof.
  intros i. unfold ctab.
  pose proof (forallb_nth (fun v => (0 <=? v) && (v <? 2 ^ 32)) crc_table 0 (Z.to_nat i)
                ltac:(vm_compute; reflexivity) eq_refl) as H.
  cbn beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma btab_range : forall k i, 0 <= btab k i < 2 ^ 32.
Proof.
  intros k i. unfold btab.
  set (P := fun v => (0 <=? v) && (v <? 2 ^ 32)).
  assert (HP : forall v, P v = true -> 0 <= v < 2 ^ 32).
  { intros v Hv. unfold P in Hv. apply andb_prop in Hv as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  apply HP.
  assert (Hrow : forall r, In r crc_braid_table -> forallb P r = true).
  { intros r Hr. cbn in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity. }
  destruct (nth_in_or_default (Z.to_nat k) crc_braid_table []) as [Hin|Hdef].
  - apply forallb_nth; [apply Hrow; exact Hin | reflexivity].
  - rewrite Hdef. destruct (Z.to_nat i); reflexivity.
Qed.


Lemma land_255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_M32 : forall x, Z.land x M32 = x mod 2 ^ 32.
Proof. intros x. change M32 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_M32_small : forall x, 0 <= x < 2 ^ 32 -> Z.land x M32 = x.
Proof. intros x Hx. rewrite land_M32. apply Z.mod_small. exact Hx. Qed.

Lemma xtn8_shiftl8 : forall y, 0 <= y -> xtn 8 (Z.shiftl y 8) = y.
Proof. intros y Hy. change (Z.shiftl y 8) with (Z.shiftl y (Z.of_nat 8)). apply xtn_shiftl_exact. exact Hy. Qed.

Lemma split8 : forall x, 0 <= x -> x = Z.lxor (Z.shiftl (Z.shiftr x 8) 8) (x mod 256).
Proof.
  intros x Hx. rewrite Z.lxor_comm.
  assert (Hs : Z.shiftr x 8 = x / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite (lxor_shiftl_add (x mod 256) (Z.shiftr x 8) 8); rewrite ?Hs; change (2 ^ 8) with 256; lia.
Qed.

Lemma xtn8_split : forall x, 0 <= x -> xtn 8 x = Z.lxor (Z.shiftr x 8) (xtn 8 (x mod 256)).
Proof.
  intros x Hx. rewrite (split8 x Hx) at 1. rewrite xtn_xor, xtn8_shiftl8; [reflexivity|].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma crc_word1_xtn : forall x, 0 <= x -> crc_word1 x = xtn 8 x.
Proof.
  intros x Hx. unfold crc_word1. rewrite land_255, (xtn8_split x Hx).
  rewrite ctab_xtn by lia. reflexivity.
Qed.

Lemma crc_word_xtn : forall x, 0 <= x -> crc_word x = xtn 32 x.
Proof.
  intros x Hx. unfold crc_word.
  rewrite (crc_word1_xtn x Hx).
  rewrite (crc_word1_xtn (xtn 8 x)) by (apply xtn_nonneg; exact Hx).
  rewrite (crc_word1_xtn (xtn 8 (xtn 8 x))) by (apply xtn_nonneg, xtn_nonneg; exact Hx).
  rewrite (crc_word1_xtn (xtn 8 (xtn 8 (xtn 8 x)))) by (apply xtn_nonneg, xtn_nonneg, xtn_nonneg; exact Hx).
  rewrite <- !xtn_add. reflexivity.
Qed.

Lemma crc_byte_step : forall c b, 0 <= c -> 0 <= b < 256 -> crc_byte c b = crc_step c b.
Proof.
  intros c b Hc Hb. unfold crc_byte, crc_step.
  assert (Hx : 0 <= Z.lxor c b) by (apply Z.lxor_nonneg; lia).
  rewrite (xtn8_split _ Hx).
  rewrite shiftr_lxor.
  replace (Z.shiftr b 8) with 0
    by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256; symmetry; apply Z.div_small; lia).
  rewrite Z.lxor_0_r. rewrite land_255, (Z.lxor_comm b c).
  rewrite ctab_xtn by lia. reflexivity.
Qed.

Lemma crc_bytes_fold : forall bs c, bytes bs -> 0 <= c < 2 ^ 32 -> crc_bytes c bs = crc_fold c bs.
Proof.
  induction bs as [|b bs IH]; intros c Hbs Hc; [reflexivity|].
  inversion Hbs as [|b' bs' Hb Hbs']; subst.
  rewrite crc_bytes_cons, crc_fold_cons. rewrite crc_byte_step by lia.
  apply IH; [exact Hbs'|]. unfold crc_step. apply xtn_range. apply lxor_bound32; lia.
Qed.

Lemma braid1_lane : forall c w, 0 <= c < 2 ^ 32 -> 0 <= w < 2 ^ 32 ->
  braid1 c w = xtn 160 (Z.lxor c w).
Proof.
  intros c w Hc Hw. unfold braid1.
  pose proof (lxor_bound32 c w Hc Hw) as Hx.
  set (x := Z.lxor c w) in *.
  change (Z.land x 255) with (byteZ x 0).
  change (Z.land (Z.shiftr x 8) 255) with (byteZ x 1).
  change (Z.land (Z.shiftr x 16) 255) with (byteZ x 2).
  change (Z.land (Z.shiftr x 24) 255) with (byteZ x 3).
  change 0 with (Z.of_nat 0) at 1. change 1 with (Z.of_nat 1) at 1.
  change 2 with (Z.of_nat 2) at 1. change 3 with (Z.of_nat 3) at 1.
  rewrite !btab_braid_tab by (lia || apply byteZ_range).
  rewrite <- (wordLE_bytes x Hx) at 5.
  rewrite <- braid_round4_xtn by (apply (proj1 (byteZ_range _ _))).
  unfold braid_round4. rewrite !Z.lxor_assoc. reflexivity.
Qed.

Lemma wle_wordLE : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  wle b0 b1 b2 b3 = wordLE b0 b1 b2 b3.
Proof.
  intros. unfold wle. rewrite wordLE_sum by assumption.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216. lia.
Qed.

Lemma wle_range : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= wle b0 b1 b2 b3 < 2 ^ 32.
Proof.
  intros. unfold wle.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216. lia.
Qed.


Lemma xtnl_locked : { f : nat -> Z -> Z | f = xtn }. Proof. exists xtn. reflexivity. Qed.
Definition xtnl : nat -> Z -> Z := proj1_sig xtnl_locked.
Lemma xtnl_eq : xtnl = xtn. Proof. exact (proj2_sig xtnl_locked). Qed.
Lemma xtnl_at : forall n c, xtnl n c = xtn n c. Proof. intros. rewrite xtnl_eq. reflexivity. Qed.
Lemma xtnl_xor : forall n a b, xtnl n (Z.lxor a b) = Z.lxor (xtnl n a) (xtnl n b).
Proof. intros. rewrite !xtnl_at. apply xtn_xor. Qed.
Lemma xtnl_0 : forall n, xtnl n 0 = 0.
Proof. intros. rewrite xtnl_at. apply xtn_0. Qed.
Lemma xtnl_range : forall n c, 0 <= c < 2 ^ 32 -> 0 <= xtnl n c < 2 ^ 32.
Proof. intros. rewrite xtnl_at. apply (xtn_range n c). assumption. Qed.

Definition comb5 (x0 x1 x2 x3 x4 : Z) : Z :=
  Z.lxor (xtnl 160 x0) (Z.lxor (xtnl 128 x1) (Z.lxor (xtnl 96 x2) (Z.lxor (xtnl 64 x3) (xtnl 32 x4)))).

Lemma comb5_xor : forall a0 a1 a2 a3 a4 b0 b1 b2 b3 b4,
  comb5 (Z.lxor a0 b0) (Z.lxor a1 b1) (Z.lxor a2 b2) (Z.lxor a3 b3) (Z.lxor a4 b4)
  = Z.lxor (comb5 a0 a1 a2 a3 a4) (comb5 b0 b1 b2 b3 b4).
Proof. intros. unfold comb5. rewrite !xtnl_xor. xor_ac. Qed.

Lemma comb5_shift : forall x0 x1 x2 x3 x4,
  comb5 (xtnl 160 x0) (xtnl 160 x1) (xtnl 160 x2) (xtnl 160 x3) (xtnl 160 x4)
  = xtnl 160 (comb5 x0 x1 x2 x3 x4).
Proof.
  intros. unfold comb5. rewrite !xtnl_xor. rewrite !xtnl_at.
  rewrite <- !xtn_add. cbn [Nat.add]. reflexivity.
Qed.

Lemma fold_word : forall q b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  crc_fold q [b0; b1; b2; b3] = xtnl 32 (Z.lxor q (wordLE b0 b1 b2 b3)).
Proof. intros. cbn [crc_fold fold_left]. rewrite xtnl_at. apply crc_step4; assumption. Qed.

Lemma fold_block : forall q b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19,
  Forall (fun b => 0 <= b) [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19] ->
  crc_fold q [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19]
  = Z.lxor (xtnl 160 q) (comb5 (wordLE b0 b1 b2 b3) (wordLE b4 b5 b6 b7) (wordLE b8 b9 b10 b11)
                            (wordLE b12 b13 b14 b15) (wordLE b16 b17 b18 b19)).
Proof.
  intros. repeat match goal with H : Forall _ (_ :: _) |- _ => inversion_clear H end.
  change [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19]
    with ([b0;b1;b2;b3] ++ ([b4;b5;b6;b7] ++ ([b8;b9;b10;b11] ++ ([b12;b13;b14;b15] ++ [b16;b17;b18;b19])))).
  rewrite !crc_fold_app. rewrite !fold_word by assumption.
  unfold comb5. rewrite !xtnl_at. rewrite !xtn_xor. rewrite <- !xtn_add. cbn [Nat.add].
  xor_ac.
Qed.

Definition lane_step (l w : Z) : Z := xtnl 160 (Z.lxor l w).

Lemma lane_step_range : forall l w, 0 <= l < 2 ^ 32 -> 0 <= w < 2 ^ 32 ->
  0 <= lane_step l w < 2 ^ 32.
Proof. intros. unfold lane_step. apply xtnl_range. apply lxor_bound32; assumption. Qed.

Definition combine5 (l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 : Z) : Z :=
  xtnl 32 (Z.lxor (Z.lxor l4 w4) (xtnl 32 (Z.lxor (Z.lxor l3 w3) (xtnl 32 (Z.lxor (Z.lxor l2 w2)
    (xtnl 32 (Z.lxor (Z.lxor l1 w1) (xtnl 32 (Z.lxor l0 w0))))))))).

Lemma combine_split : forall l0 l1 l2 l3 l4 w0 w1 w2 w3 w4,
  combine5 l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 = Z.lxor (comb5 l0 l1 l2 l3 l4) (comb5 w0 w1 w2 w3 w4).
Proof.
  intros. unfold combine5, comb5. rewrite !xtnl_at.
  rewrite !xtn_xor. rewrite <- !xtn_add. cbn [Nat.add].
  xor_ac.
Qed.

Definition binv (l0 l1 l2 l3 l4 q : Z) : Prop := comb5 l0 l1 l2 l3 l4 = xtnl 160 q.

Lemma binv_init : forall c, binv c 0 0 0 0 c.
Proof. intros c. unfold binv, comb5. rewrite !xtnl_0, !Z.lxor_0_r. reflexivity. Qed.

Lemma binv_step : forall l0 l1 l2 l3 l4 q w0 w1 w2 w3 w4 q',
  binv l0 l1 l2 l3 l4 q ->
  q' = Z.lxor (xtnl 160 q) (comb5 w0 w1 w2 w3 w4) ->
  binv (lane_step l0 w0) (lane_step l1 w1) (lane_step l2 w2) (lane_step l3 w3) (lane_step l4 w4) q'.
Proof.
  intros l0 l1 l2 l3 l4 q w0 w1 w2 w3 w4 q' HI Hq. unfold binv in *. unfold lane_step.
  rewrite comb5_shift, comb5_xor, HI, Hq. reflexivity.
Qed.

Lemma binv_combine : forall l0 l1 l2 l3 l4 q w0 w1 w2 w3 w4,
  binv l0 l1 l2 l3 l4 q ->
  combine5 l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 = Z.lxor (xtnl 160 q) (comb5 w0 w1 w2 w3 w4).
Proof. intros * HI. rewrite combine_split. unfold binv in HI. rewrite HI. reflexivity. Qed.


Lemma block20 : forall blk : list Z, length blk = 20%nat ->
  exists b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19,
    blk = [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19].
Proof.
  intros blk H.
  destruct blk as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|b16 [|b17 [|b18 [|b19 [|x l]]]]]]]]]]]]]]]]]]]]];
    cbn in H; try lia.
  now exists b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19.
Qed.

Definition lanes_ok (cs : list Z) (q : Z) : Prop :=
  exists l0 l1 l2 l3 l4, cs = [l0; l1; l2; l3; l4] /\
    0 <= l0 < 2 ^ 32 /\ 0 <= l1 < 2 ^ 32 /\ 0 <= l2 < 2 ^ 32 /\ 0 <= l3 < 2 ^ 32 /\ 0 <= l4 < 2 ^ 32 /\
    binv l0 l1 l2 l3 l4 q.

Lemma lanes_ok_init : forall c, 0 <= c < 2 ^ 32 -> lanes_ok [c; 0; 0; 0; 0] c.
Proof.
  intros c Hc. exists c, 0, 0, 0, 0. repeat split; try lia. apply binv_init.
Qed.

Lemma braid_step_ok : forall cs q blk, lanes_ok cs q -> bytes blk -> length blk = 20%nat ->
  lanes_ok (braid_step cs blk) (crc_fold q blk).
Proof.
  intros cs q blk (l0 & l1 & l2 & l3 & l4 & -> & H0 & H1 & H2 & H3 & H4 & HI) Hb Hlen.
  destruct (block20 blk Hlen) as (b0&b1&b2&b3&b4&b5&b6&b7&b8&b9&b10&b11&b12&b13&b14&b15&b16&b17&b18&b19&->).
  unfold bytes in Hb.
  repeat match goal with H : Forall _ (_ :: _) |- _ => inversion_clear H end.
  cbn [braid_step words_le List.combine map fst snd].
  pose proof (wle_range b0 b1 b2 b3) as W0. pose proof (wle_range b4 b5 b6 b7) as W1.
  pose proof (wle_range b8 b9 b10 b11) as W2. pose proof (wle_range b12 b13 b14 b15) as W3.
  pose proof (wle_range b16 b17 b18 b19) as W4.
  rewrite !braid1_lane by (assumption || (apply W0 || apply W1 || apply W2 || apply W3 || apply W4; assumption)).
  rewrite <- !xtnl_at. fold (lane_step l0 (wle b0 b1 b2 b3)). 
  exists (lane_step l0 (wle b0 b1 b2 b3)), (lane_step l1 (wle b4 b5 b6 b7)), (lane_step l2 (wle b8 b9 b10 b11)),
         (lane_step l3 (wle b12 b13 b14 b15)), (lane_step l4 (wle b16 b17 b18 b19)).
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end;
    try (apply lane_step_range; [assumption | (apply W0 || apply W1 || apply W2 || apply W3 || apply W4); assumption]).
  eapply binv_step; [exact HI|].
  rewrite !wle_wordLE by assumption.
  apply fold_block. repeat constructor; lia.
Qed.

Lemma braid_state_0 : forall cs bs, braid_state cs 0 bs = cs.
Proof. reflexivity. Qed.

Lemma braid_state_S_front : forall cs i bs,
  braid_state cs (S i) bs = braid_state (braid_step cs (firstn 20 bs)) i (skipn 20 bs).
Proof. reflexivity. Qed.

Lemma blocks_of_S : forall n bs, blocks_of (S n) bs = firstn 20 bs :: blocks_of n (skipn 20 bs).
Proof. reflexivity. Qed.

Lemma block_S : forall i bs, block i (skipn 20 bs) = block (S i) bs.
Proof. intros. unfold block. rewrite skipn_skipn'. f_equal. f_equal. lia. Qed.

Lemma blocks_of_S_snoc : forall i bs, blocks_of (S i) bs = blocks_of i bs ++ [block i bs].
Proof.
  induction i as [|i IH]; intros bs.
  - cbn. unfold block. cbn [Nat.mul skipn]. reflexivity.
  - rewrite blocks_of_S, (IH (skipn 20 bs)), blocks_of_S, block_S. reflexivity.
Qed.

Lemma braid_run_app : forall cs bl1 bl2, braid_run cs (bl1 ++ bl2) = braid_run (braid_run cs bl1) bl2.
Proof. intros cs bl1; revert cs; induction bl1 as [|b bl1 IH]; intros; cbn; [reflexivity | apply IH]. Qed.

Lemma braid_state_S : forall cs i bs,
  braid_state cs (S i) bs = braid_step (braid_state cs i bs) (block i bs).
Proof. intros. unfold braid_state. rewrite blocks_of_S_snoc, braid_run_app. reflexivity. Qed.

Lemma block_length : forall i bs, (20 * S i <= length bs)%nat -> length (block i bs) = 20%nat.
Proof. intros i bs H. unfold block. rewrite length_firstn, length_skipn. lia. Qed.

Lemma braid_state_ok : forall i cs q bs, lanes_ok cs q -> bytes bs -> (20 * i <= length bs)%nat ->
  lanes_ok (braid_state cs i bs) (crc_fold q (firstn (20 * i) bs)).
Proof.
  induction i as [|i IH]; intros cs q bs Hcs Hbs Hlen.
  - cbn [Nat.mul firstn]. rewrite crc_fold_nil. exact Hcs.
  - rewrite braid_state_S.
    replace (20 * S i)%nat with (20 * i + 20)%nat by lia.
    rewrite <- (firstn_add_skipn (20 * i) 20 bs), crc_fold_app.
    apply braid_step_ok.
    + apply IH; [exact Hcs | exact Hbs | lia].
    + apply bytes_firstn, bytes_skipn, Hbs.
    + apply block_length. exact Hlen.
Qed.

Lemma crc_word_range : forall x, 0 <= x < 2 ^ 32 -> 0 <= crc_word x < 2 ^ 32.
Proof. intros x Hx. rewrite crc_word_xtn by lia. apply (xtn_range 32 x Hx). Qed.

Lemma crc_word_xtnl : forall x, 0 <= x < 2 ^ 32 -> crc_word x = xtnl 32 x.
Proof. intros x Hx. rewrite xtnl_at. apply crc_word_xtn. lia. Qed.

Lemma braid_last_combine5 : forall l0 l1 l2 l3 l4 w0 w1 w2 w3 w4,
  0 <= l0 < 2 ^ 32 -> 0 <= l1 < 2 ^ 32 -> 0 <= l2 < 2 ^ 32 -> 0 <= l3 < 2 ^ 32 -> 0 <= l4 < 2 ^ 32 ->
  0 <= w0 < 2 ^ 32 -> 0 <= w1 < 2 ^ 32 -> 0 <= w2 < 2 ^ 32 -> 0 <= w3 < 2 ^ 32 -> 0 <= w4 < 2 ^ 32 ->
  crc_word (Z.lxor (Z.lxor l4 w4) (crc_word (Z.lxor (Z.lxor l3 w3) (crc_word (Z.lxor (Z.lxor l2 w2)
    (crc_word (Z.lxor (Z.lxor l1 w1) (crc_word (Z.lxor l0 w0)))))))))
  = combine5 l0 l1 l2 l3 l4 w0 w1 w2 w3 w4.
Proof.
  intros l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 L0 L1 L2 L3 L4 W0 W1 W2 W3 W4. unfold combine5.
  assert (R0 : 0 <= Z.lxor l0 w0 < 2 ^ 32) by (apply lxor_bound32; assumption).
  rewrite (crc_word_xtnl _ R0).
  assert (R1 : 0 <= Z.lxor (Z.lxor l1 w1) (xtnl 32 (Z.lxor l0 w0)) < 2 ^ 32).
  { apply lxor_bound32; [apply lxor_bound32; assumption | apply xtnl_range; exact R0]. }
  rewrite (crc_word_xtnl _ R1).
  assert (R2 : 0 <= Z.lxor (Z.lxor l2 w2) (xtnl 32 (Z.lxor (Z.lxor l1 w1) (xtnl 32 (Z.lxor l0 w0)))) < 2 ^ 32).
  { apply lxor_bound32; [apply lxor_bound32; assumption | apply xtnl_range; exact R1]. }
  rewrite (crc_word_xtnl _ R2).
  assert (R3 : 0 <= Z.lxor (Z.lxor l3 w3) (xtnl 32 (Z.lxor (Z.lxor l2 w2)
                 (xtnl 32 (Z.lxor (Z.lxor l1 w1) (xtnl 32 (Z.lxor l0 w0)))))) < 2 ^ 32).
  { apply lxor_bound32; [apply lxor_bound32; assumption | apply xtnl_range; exact R2]. }
  rewrite (crc_word_xtnl _ R3).
  assert (R4 : 0 <= Z.lxor (Z.lxor l4 w4) (xtnl 32 (Z.lxor (Z.lxor l3 w3) (xtnl 32 (Z.lxor (Z.lxor l2 w2)
                 (xtnl 32 (Z.lxor (Z.lxor l1 w1) (xtnl 32 (Z.lxor l0 w0)))))))) < 2 ^ 32).
  { apply lxor_bound32; [apply lxor_bound32; assumption | apply xtnl_range; exact R3]. }
  rewrite (crc_word_xtnl _ R4).
  reflexivity.
Qed.

Lemma braid_last_ok : forall cs q blk, lanes_ok cs q -> bytes blk -> length blk = 20%nat ->
  braid_last cs blk = crc_fold q blk.
Proof.
  intros cs q blk (l0 & l1 & l2 & l3 & l4 & -> & H0 & H1 & H2 & H3 & H4 & HI) Hb Hlen.
  destruct (block20 blk Hlen) as (b0&b1&b2&b3&b4&b5&b6&b7&b8&b9&b10&b11&b12&b13&b14&b15&b16&b17&b18&b19&->).
  unfold bytes in Hb.
  repeat match goal with H : Forall _ (_ :: _) |- _ => inversion_clear H end.
  cbn [braid_last words_le].
  assert (V0 : 0 <= wle b0 b1 b2 b3 < 2 ^ 32) by (apply wle_range; assumption).
  assert (V1 : 0 <= wle b4 b5 b6 b7 < 2 ^ 32) by (apply wle_range; assumption).
  assert (V2 : 0 <= wle b8 b9 b10 b11 < 2 ^ 32) by (apply wle_range; assumption).
  assert (V3 : 0 <= wle b12 b13 b14 b15 < 2 ^ 32) by (apply wle_range; assumption).
  assert (V4 : 0 <= wle b16 b17 b18 b19 < 2 ^ 32) by (apply wle_range; assumption).
  rewrite (braid_last_combine5 l0 l1 l2 l3 l4) by assumption.
  rewrite (binv_combine l0 l1 l2 l3 l4 q) by exact HI.
  rewrite !wle_wordLE by assumption.
  symmetry. apply fold_block. repeat constructor; lia.
Qed.

Lemma align4_range : forall adr, 0 <= align4 adr <= 3.
Proof. intros adr. unfold align4. lia. Qed.

Theorem crc_braid_phase_fold : forall adr c bs,
  bytes bs -> 0 <= c < 2 ^ 32 -> 23 <= Zlen bs ->
  let na := Z.to_nat (align4 adr) in
  let blks := Z.to_nat ((Zlen bs - align4 adr) / 20) in
  crc_braid_phase adr c bs
  = (crc_fold c (firstn (na + 20 * blks) bs), skipn (na + 20 * blks) bs).
Proof.
  intros adr c bs Hbs Hc Hlen na blks. unfold crc_braid_phase.
  pose proof (align4_range adr) as Hna.
  unfold Zlen in *.
  set (bs1 := skipn (Z.to_nat (align4 adr)) bs).
  assert (L1 : Z.of_nat (length bs1) = Z.of_nat (length bs) - align4 adr).
  { subst bs1. rewrite length_skipn. lia. }
  rewrite L1. fold na.
  set (B := (Z.of_nat (length bs) - align4 adr) / 20) in *.
  assert (HB : 1 <= B) by (subst B; apply Z.div_le_lower_bound; lia).
  assert (HB20 : 20 * B <= Z.of_nat (length bs) - align4 adr) by (subst B; lia).
  rewrite crc_bytes_fold by (try apply bytes_firstn; assumption).
  assert (Hq : lanes_ok [crc_fold c (firstn na bs); 0; 0; 0; 0] (crc_fold c (firstn na bs))).
  { apply lanes_ok_init. apply crc_fold_range; [exact Hc|]. apply bytes_In. apply bytes_firstn. exact Hbs. }
  assert (Hbs1 : bytes bs1) by (apply bytes_skipn; exact Hbs).
  assert (Hlen1 : (20 * S (Z.to_nat (B - 1)) <= length bs1)%nat) by lia.
  pose proof (braid_state_ok (Z.to_nat (B - 1)) _ _ bs1 Hq Hbs1 ltac:(lia)) as Hst.
  rewrite (braid_last_ok _ _ _ Hst) by (try apply block_length; try (apply bytes_firstn, bytes_skipn); assumption).
  rewrite <- crc_fold_app. unfold block. rewrite firstn_add_skipn.
  rewrite <- crc_fold_app. subst bs1. rewrite firstn_add_skipn, skipn_skipn'.
  replace (Z.to_nat (align4 adr) + (20 * Z.to_nat (B - 1) + 20))%nat with (na + 20 * blks)%nat by lia.
  replace (na + (20 * Z.to_nat (B - 1) + 20))%nat with (na + 20 * blks)%nat by lia.
  replace (Z.to_nat (align4 adr) + Z.to_nat (20 * B))%nat with (na + 20 * blks)%nat by lia.
  reflexivity.
Qed.


Definition crc32_spec (c : Z) (bs : list Z) : Z := Z.lxor (crc_fold (crc_pre c) bs) M32.

Lemma crc_pre_range : forall c, 0 <= crc_pre c < 2 ^ 32.
Proof. intros c. unfold crc_pre. rewrite land_M32. apply Z.mod_pos_bound. lia. Qed.

Lemma testbit_M32 : forall m, 0 <= m -> Z.testbit M32 m = (m <? 32).
Proof.
  intros m Hm. change M32 with (Z.ones 32). rewrite Z.testbit_ones by lia.
  destruct (Z.leb_spec 0 m); [reflexivity | lia].
Qed.

Lemma crc_pre_xor : forall c, 0 <= c < 2 ^ 32 -> crc_pre c = Z.lxor c M32.
Proof.
  intros c Hc. unfold crc_pre. apply Z.bits_inj'. intros m Hm.
  rewrite Z.land_spec, Z.lnot_spec, Z.lxor_spec, testbit_M32 by lia.
  destruct (Z.ltb_spec m 32).
  - destruct (Z.testbit c m); reflexivity.
  - rewrite (testbit_high c 32 m) by lia. reflexivity.
Qed.

Lemma crc_pre_0 : crc_pre 0 = M32.
Proof. reflexivity. Qed.

Lemma lxor_M32_range : forall x, 0 <= x < 2 ^ 32 -> 0 <= Z.lxor x M32 < 2 ^ 32.
Proof. intros. apply lxor_bound32; [assumption | unfold M32; lia]. Qed.

Lemma crc32_spec_range : forall c bs, bytes bs -> 0 <= crc32_spec c bs < 2 ^ 32.
Proof.
  intros c bs Hbs. unfold crc32_spec. apply lxor_M32_range.
  apply crc_fold_range; [apply crc_pre_range | apply bytes_In; exact Hbs].
Qed.

Theorem crc32_z_model_spec : forall adr c bs, bytes bs ->
  crc32_z_model adr c bs = crc32_spec c bs.
Proof.
  intros adr c bs Hbs. unfold crc32_z_model, crc32_spec.
  pose proof (crc_pre_range c) as Hc0.
  destruct (Z.ltb_spec (Zlen bs) 23) as [Hlt|Hge].
  - cbn [fst snd]. rewrite crc_bytes_fold by assumption. reflexivity.
  - rewrite (crc_braid_phase_fold adr (crc_pre c) bs Hbs Hc0) by lia. cbn [fst snd].
    rewrite crc_bytes_fold.
    + rewrite <- crc_fold_app, firstn_skipn. reflexivity.
    + apply bytes_skipn. exact Hbs.
    + apply crc_fold_range; [exact Hc0|]. apply bytes_In, bytes_firstn. exact Hbs.
Qed.

Corollary crc32_z_model_adr : forall adr adr' c bs, bytes bs ->
  crc32_z_model adr c bs = crc32_z_model adr' c bs.
Proof. intros. rewrite !crc32_z_model_spec by assumption. reflexivity. Qed.

Corollary crc32_z_model_range : forall adr c bs, bytes bs -> 0 <= crc32_z_model adr c bs < 2 ^ 32.
Proof. intros. rewrite crc32_z_model_spec by assumption. apply crc32_spec_range. assumption. Qed.


Theorem crc32_spec_app : forall c xs ys, bytes xs ->
  crc32_spec (crc32_spec c xs) ys = crc32_spec c (xs ++ ys).
Proof.
  intros c xs ys Hxs. unfold crc32_spec at 1 3.
  rewrite (crc_pre_xor (crc32_spec c xs)) by (apply crc32_spec_range; exact Hxs).
  unfold crc32_spec. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
  rewrite crc_fold_app. reflexivity.
Qed.

Corollary crc32_spec_nil : forall c, 0 <= c < 2 ^ 32 -> crc32_spec c [] = c.
Proof.
  intros c Hc. unfold crc32_spec. rewrite crc_fold_nil, (crc_pre_xor c Hc).
  rewrite Z.lxor_assoc, Z.lxor_nilpotent. apply Z.lxor_0_r.
Qed.

Theorem crc_fold_affine : forall bs c,
  crc_fold c bs = Z.lxor (xtn (8 * length bs) c) (crc_fold 0 bs).
Proof.
  induction bs as [|b bs IH]; intros c.
  - cbn [length Nat.mul crc_fold fold_left xtn]. symmetry. apply Z.lxor_0_r.
  - rewrite !crc_fold_cons. rewrite (IH (crc_step c b)), (IH (crc_step 0 b)).
    unfold crc_step. rewrite Z.lxor_0_l, xtn_xor.
    cbn [length]. replace (8 * S (length bs))%nat with (8 + 8 * length bs)%nat by lia.
    rewrite (xtn_add 8 (8 * length bs) c). rewrite !xtn_xor. xor_ac.
Qed.

Theorem crc32_spec_affine : forall c bs, 0 <= c < 2 ^ 32 ->
  crc32_spec c bs = Z.lxor (xtn (8 * length bs) c) (crc32_spec 0 bs).
Proof.
  intros c bs Hc. unfold crc32_spec. rewrite (crc_pre_xor c Hc), crc_pre_0.
  rewrite (crc_fold_affine bs (Z.lxor c M32)), (crc_fold_affine bs M32).
  rewrite xtn_xor. xor_ac.
Qed.

Theorem crc32_combine_op_spec : forall c bs,
  bytes bs -> 0 <= c < 2 ^ 32 -> Zlen bs < 2 ^ 29 ->
  crc32_combine_op c (crc32_spec 0 bs) (crc32_combine_gen (Zlen bs)) = crc32_spec c bs.
Proof.
  intros c bs Hbs Hc Hlen. unfold crc32_combine_op, crc32_combine_gen, crc32_combine_gen64.
  unfold Zlen in *.
  rewrite multmodp_x2nmodp_3 by lia.
  rewrite land_M32_small by (apply crc32_spec_range; exact Hbs).
  rewrite (crc32_spec_affine c bs Hc).
  replace (Z.to_nat (8 * Z.of_nat (length bs))) with (8 * length bs)%nat by lia.
  reflexivity.
Qed.

Lemma crc32_combine_gen_op : forall c1 c2 len,
  crc32_combine c1 c2 len = crc32_combine_op c1 c2 (crc32_combine_gen len).
Proof.
  intros. unfold crc32_combine, crc32_combine64, crc32_combine_op, crc32_combine_gen, crc32_combine_gen64.
  reflexivity.
Qed.
