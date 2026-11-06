(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnInv BnSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Specs2.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma left_align_value : forall (l : list Z), limbs l -> (1 <= length l)%nat -> nth (length l - 1) l 0 <> 0 ->
  let sh := 64 - num_bits_word (nth (length l - 1) l 0) in
  let r := fst (lshift_limbs l sh 0) in
  0 <= sh < 64 /\ limbs r /\ length r = length l /\ lval r = lval l * 2 ^ sh /\ 2 ^ 63 <= nth (length l - 1) r 0.
Proof.
  intros l Hl Hlen Htop. cbv zeta. set (n := (length l - 1)%nat) in *. set (x := nth n l 0) in *.
  pose proof (limbs_nth l n Hl) as Hx. fold x in Hx. destruct Hx as [Hx0 Hx1].
  destruct (num_bits_word_spec x ltac:(lia)) as (Hb1 & Hb2 & Hb3).
  pose proof (num_bits_word_le x 64 ltac:(lia) ltac:(unfold BW in *; lia)) as Hb4.
  set (bits := num_bits_word x) in *. set (sh := 64 - bits).
  assert (Hsh : 0 <= sh < 64) by (subst sh; lia).
  pose proof (lshift_limbs_spec l sh 0 Hl Hsh ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as Hs.
  destruct (lshift_limbs l sh 0) as [r mo]. cbn [fst]. destruct Hs as (Hr & Hrl & Hmo & Hv).

  pose proof (nth_limb_val l n Hl ltac:(lia)) as El. fold x in El.
  rewrite (skipn_all2 l) in El by lia. cbn [lval] in El. rewrite Z.mul_0_r, Z.add_0_r in El.
  pose proof (lval_bound (firstn n l) (limbs_firstn n l Hl)) as Hlo. rewrite firstn_length_le in Hlo by lia.
  pose proof (Bp_pos n) as Hbn.
  assert (E2 : 2 ^ bits * 2 ^ sh = BW).
  { rewrite <- Z.pow_add_r by lia. subst sh. replace (bits + (64 - bits)) with 64 by lia. reflexivity. }
  assert (E3 : 2 ^ (bits - 1) * 2 ^ sh = 2 ^ 63).
  { rewrite <- Z.pow_add_r by lia. subst sh. f_equal. lia. }
  assert (Hp : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  assert (EBl : Bp (length l) = BW * Bp n) by (rewrite <- Bp_S; f_equal; subst n; lia).

  assert (Hfit : lval l * 2 ^ sh < Bp (length l)).
  { rewrite EBl, <- E2. assert (lval l < Bp n * 2 ^ bits) by nia. nia. }
  assert (Emo : mo = 0).
  { pose proof (lval_nonneg r Hr). pose proof (Bp_pos (length l)). nia. }
  rewrite Emo, Z.mul_0_r, Z.add_0_r, Z.add_0_r in Hv.
  split; [exact Hsh|]. split; [exact Hr|]. split; [exact Hrl|]. split; [exact Hv|].

  pose proof (nth_limb_val r n Hr ltac:(lia)) as Er.
  rewrite (skipn_all2 r) in Er by lia. cbn [lval] in Er. rewrite Z.mul_0_r, Z.add_0_r in Er.
  pose proof (lval_bound (firstn n r) (limbs_firstn n r Hr)) as Hrlo. rewrite firstn_length_le in Hrlo by lia.
  assert (Hge : Bp n * 2 ^ 63 <= lval r).
  { rewrite Hv, <- E3. assert (Bp n * 2 ^ (bits - 1) <= lval l) by nia. nia. }
  destruct (Z.lt_ge_cases (nth n r 0) (2 ^ 63)) as [Hlt|]; [exfalso|assumption].
  assert (Bp n * nth n r 0 <= Bp n * (2 ^ 63 - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma le_bytes_val_bound : forall bs, 0 <= le_bytes_val bs < 256 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; cbn [le_bytes_val length].
  - cbn. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. pose proof (Z.mod_pos_bound b 256 ltac:(lia)). lia.
Qed.

Lemma bytes_to_limbs_spec : forall n bs, limbs (bytes_to_limbs n bs) /\ length (bytes_to_limbs n bs) = n.
Proof.
  induction n as [|n IH]; intros bs; cbn [bytes_to_limbs length]; [split; [constructor|reflexivity]|].
  destruct (IH (skipn 8 bs)) as [H1 H2]. split; [|rewrite H2; reflexivity].
  constructor; [|exact H1]. pose proof (le_bytes_val_bound (firstn 8 bs)) as [Hb0 Hb1].
  assert (Hl : (length (firstn 8 bs) <= 8)%nat) by (rewrite length_firstn; lia).
  assert (256 ^ Z.of_nat (length (firstn 8 bs)) <= 256 ^ 8) by (apply Z.pow_le_mono_r; lia).
  unfold limb. change BW with (256 ^ 8). lia.
Qed.

Lemma skip_zero_bytes_length : forall bs, (length (skip_zero_bytes bs) <= length bs)%nat.
Proof.
  induction bs as [|b bs IH]; cbn [skip_zero_bytes length]; [lia|].
  destruct b; cbn [length]; lia.
Qed.

Definition MAX_BYTES : Z := 256000.

End Specs2.
