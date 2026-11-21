(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

