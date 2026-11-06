(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition itv := (option Z * option Z)%type.

Definition itv_top : itv := (None, None).
Definition itv_const (c : Z) : itv := (Some c, Some c).
Definition itv_lo (i : itv) : option Z := fst i.
Definition itv_hi (i : itv) : option Z := snd i.

Definition lo_le (lo : option Z) (z : Z) : Prop :=
  match lo with Some l => l <= z | None => True end.
Definition hi_ge (hi : option Z) (z : Z) : Prop :=
  match hi with Some h => z <= h | None => True end.

Definition in_itv (z : Z) (i : itv) : Prop := lo_le (fst i) z /\ hi_ge (snd i) z.

Definition itv_mem (z : Z) (i : itv) : bool :=
  (match fst i with Some l => Z.leb l z | None => true end)
  && (match snd i with Some h => Z.leb z h | None => true end).

Lemma itv_mem_spec z i : itv_mem z i = true <-> in_itv z i.
Proof.
  unfold itv_mem, in_itv. destruct i as [[l|] [h|]]; simpl;
  rewrite ?andb_true_iff, ?Z.leb_le; tauto.
Qed.

Lemma in_itv_top z : in_itv z itv_top.
Proof. split; exact I. Qed.

Lemma in_itv_const c : in_itv c (itv_const c).
Proof. split; simpl; lia. Qed.

Lemma in_itv_const_inv z c : in_itv z (itv_const c) -> z = c.
Proof. intros [H1 H2]; simpl in *; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ob_add (a b : option Z) : option Z :=
  match a, b with Some x, Some y => Some (x + y) | _, _ => None end.

Definition itv_add (a b : itv) : itv := (ob_add (fst a) (fst b), ob_add (snd a) (snd b)).

Definition itv_addc (a : itv) (c : Z) : itv :=
  (match fst a with Some x => Some (x + c) | None => None end,
   match snd a with Some x => Some (x + c) | None => None end).

Definition ob_scale (k : Z) (a : option Z) : option Z :=
  match a with Some x => Some (k * x) | None => None end.

(* [comment removed for export] *)
Definition itv_scale (k : Z) (a : itv) : itv :=
  if Z.leb 0 k then (ob_scale k (fst a), ob_scale k (snd a))
  else (ob_scale k (snd a), ob_scale k (fst a)).

Definition itv_neg (a : itv) : itv := itv_scale (-1) a.

Definition ob_min (a b : option Z) : option Z :=
  match a, b with Some x, Some y => Some (Z.min x y) | _, _ => None end.
Definition ob_max (a b : option Z) : option Z :=
  match a, b with Some x, Some y => Some (Z.max x y) | _, _ => None end.

(* [comment removed for export] *)
Definition itv_hull (a b : itv) : itv := (ob_min (fst a) (fst b), ob_max (snd a) (snd b)).

(* [comment removed for export] *)
Definition meet_lo (a b : option Z) : option Z :=
  match a, b with
  | None, _ => b
  | _, None => a
  | Some x, Some y => Some (Z.max x y)
  end.
Definition meet_hi (a b : option Z) : option Z :=
  match a, b with
  | None, _ => b
  | _, None => a
  | Some x, Some y => Some (Z.min x y)
  end.
Definition itv_meet (a b : itv) : itv := (meet_lo (fst a) (fst b), meet_hi (snd a) (snd b)).

(* [comment removed for export] *)
Definition itv_le (a b : itv) : bool :=
  (match fst b with
   | None => true
   | Some lb => match fst a with Some la => Z.leb lb la | None => false end
   end)
  && (match snd b with
      | None => true
      | Some hb => match snd a with Some ha => Z.leb ha hb | None => false end
      end).

Definition itv_empty (a : itv) : bool :=
  match fst a, snd a with Some l, Some h => Z.ltb h l | _, _ => false end.

(* [comment removed for export] *)
Definition itv_hi_le (a : itv) (b : Z) : bool :=
  match snd a with Some h => Z.leb h b | None => false end.
Definition itv_hi_lt (a : itv) (b : Z) : bool :=
  match snd a with Some h => Z.ltb h b | None => false end.
Definition itv_lo_ge (a : itv) (b : Z) : bool :=
  match fst a with Some l => Z.leb b l | None => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac itv_crush :=
  unfold in_itv, itv_add, itv_addc, itv_scale, itv_neg, itv_hull, itv_meet, itv_le, itv_empty,
    itv_hi_le, itv_hi_lt, itv_lo_ge, ob_add, ob_scale, ob_min, ob_max, meet_lo, meet_hi,
    lo_le, hi_ge in *;
  repeat match goal with
         | i : itv |- _ => destruct i as [[?|] [?|]]
         | o : option Z |- _ => destruct o
         end; simpl in *;
  rewrite ?andb_true_iff, ?andb_false_iff, ?Z.leb_le, ?Z.ltb_lt in *;
  try (intuition (try lia; try nia)).

Lemma in_itv_add x y a b : in_itv x a -> in_itv y b -> in_itv (x + y) (itv_add a b).
Proof. itv_crush. Qed.

Lemma in_itv_addc x a c : in_itv x a -> in_itv (x + c) (itv_addc a c).
Proof. itv_crush. Qed.

Lemma in_itv_scale k x a : in_itv x a -> in_itv (k * x) (itv_scale k a).
Proof.
  unfold itv_scale. destruct (Z.leb_spec 0 k); itv_crush.
Qed.

Lemma in_itv_neg x a : in_itv x a -> in_itv (- x) (itv_neg a).
Proof.
  intros H. unfold itv_neg. replace (- x) with ((-1) * x) by lia. now apply in_itv_scale.
Qed.

Lemma in_itv_hull_l x a b : in_itv x a -> in_itv x (itv_hull a b).
Proof. itv_crush. Qed.

Lemma in_itv_hull_r x a b : in_itv x b -> in_itv x (itv_hull a b).
Proof. itv_crush. Qed.

Lemma in_itv_meet x a b : in_itv x a -> in_itv x b -> in_itv x (itv_meet a b).
Proof. itv_crush. Qed.

Lemma in_itv_meet_inv x a b : in_itv x (itv_meet a b) -> in_itv x a /\ in_itv x b.
Proof. itv_crush. Qed.

Lemma in_itv_meet_iff x a b : in_itv x (itv_meet a b) <-> in_itv x a /\ in_itv x b.
Proof.
  split; [apply in_itv_meet_inv|]. intros [H1 H2]; now apply in_itv_meet.
Qed.

Lemma itv_le_sound a b x : itv_le a b = true -> in_itv x a -> in_itv x b.
Proof. itv_crush. Qed.

Lemma itv_empty_sound a x : itv_empty a = true -> ~ in_itv x a.
Proof. itv_crush. Qed.

Lemma itv_hi_le_sound a b x : itv_hi_le a b = true -> in_itv x a -> x <= b.
Proof. itv_crush. Qed.

Lemma itv_hi_lt_sound a b x : itv_hi_lt a b = true -> in_itv x a -> x < b.
Proof. itv_crush. Qed.

Lemma itv_lo_ge_sound a b x : itv_lo_ge a b = true -> in_itv x a -> b <= x.
Proof. itv_crush. Qed.

Lemma in_itv_lo x a l : in_itv x a -> fst a = Some l -> l <= x.
Proof. itv_crush; congruence. Qed.

Lemma in_itv_hi x a h : in_itv x a -> snd a = Some h -> x <= h.
Proof. itv_crush; congruence. Qed.

Lemma in_itv_intro x (lo hi : option Z) :
  lo_le lo x -> hi_ge hi x -> in_itv x (lo, hi).
Proof. intros; split; assumption. Qed.

(* [comment removed for export] *)
Lemma in_itv_weaken x l1 h1 l2 h2 :
  in_itv x (l1, h1) ->
  (match l2 with None => True | Some b => match l1 with Some a => b <= a | None => False end end) ->
  (match h2 with None => True | Some b => match h1 with Some a => a <= b | None => False end end) ->
  in_itv x (l2, h2).
Proof. itv_crush. Qed.
