(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition is_upper (c : Z) : bool := (65 <=? c) && (c <? 91).
Definition is_lower (c : Z) : bool := (97 <=? c) && (c <? 123).
Definition is_digit (c : Z) : bool := (48 <=? c) && (c <? 58).
Definition is_alpha (c : Z) : bool := is_upper c || is_lower c.
Definition is_alnum (c : Z) : bool := is_upper c || is_lower c || is_digit c.
Definition is_xdigit (c : Z) : bool := is_digit c || ((65 <=? c) && (c <? 71)) || ((97 <=? c) && (c <? 103)).
Definition to_lower (c : Z) : Z := if is_upper c then c + 32 else c.

Lemma to_lower_range : forall c, 0 <= c < 256 -> 0 <= to_lower c < 256.
Proof.
  intros c Hc. unfold to_lower, is_upper.
  destruct (_ && _) eqn:E; [apply andb_true_iff in E; destruct E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2|]; lia.
Qed.

Lemma to_lower_0 : to_lower 0 = 0.
Proof. reflexivity. Qed.

Definition htons_z (x : Z) : Z := (x mod 256) * 256 + x / 256.

Fixpoint strncasecmp_walk (l r : list (bv 8)) (k : nat) {struct l} : option Z :=
  match l, r with
  | a :: l', b :: r' =>
      if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0
          || negb ((bv_unsigned a =? bv_unsigned b) || (to_lower (bv_unsigned a) =? to_lower (bv_unsigned b))))%bool
      then Some (to_lower (bv_unsigned a) - to_lower (bv_unsigned b))
      else match k with O => None | S k' => strncasecmp_walk l' r' k' end
  | _, _ => None
  end.

Definition strncasecmp_model (l r : list (bv 8)) (n : Z) : option Z :=
  if n =? 0 then Some 0 else strncasecmp_walk l r (Z.to_nat (n - 1)).
