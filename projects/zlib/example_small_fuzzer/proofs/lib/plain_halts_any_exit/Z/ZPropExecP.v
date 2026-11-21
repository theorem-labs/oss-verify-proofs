(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma Z_shiftr_range : forall a k : Z, (0 <= a < 2^64)%Z -> (0 <= k)%Z ->
  (0 <= Z.shiftr a k < 2^64)%Z.
Proof.
  intros a k Ha Hk. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with a; [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.


Lemma two64_pos : (0 < 2^64)%Z.
Proof. lia. Qed.


Ltac split_value_ifs :=
  repeat match goal with
  | |- context [if ?b then _ else _] =>
      lazymatch type of b with
      | bool =>
          lazymatch b with
          | true => fail
          | false => fail
          | _ => destruct b
          end
      end
  end.


Lemma nth_error_skipn_cons : forall {A} (bs : list A) d, (d < length bs)%nat ->
  exists b, nth_error bs d = Some b /\ skipn d bs = b :: skipn (S d) bs.
Proof.
  intros A bs. induction bs as [|x bs IH]; intros d Hd; [cbn in Hd; lia|].
  destruct d as [|d'].
  - exists x. split; reflexivity.
  - cbn [length] in Hd. destruct (IH d' ltac:(lia)) as [b [H1 H2]].
    exists b. split; [exact H1|]. cbn [skipn]. exact H2.
Qed.
