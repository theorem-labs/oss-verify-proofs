(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PArith.
From Stdlib Require Import NArith.
From Stdlib Require Import Pnat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition pos_of (k : nat) : positive := Pos.of_succ_nat k.

Inductive cmp := Le | Ge | Eq.
Record row := mkrow { r_lhs : list (positive * Z); r_cmp : cmp; r_rhs : Z }.
Definition lin := list (positive * Z).

Fixpoint leval (x : positive -> Z) (l : lin) : Z :=
  match l with [] => 0 | (v, a) :: r => a * x v + leval x r end.

Definition holds (x : positive -> Z) (r : row) : Prop :=
  match r_cmp r with
  | Le => leval x (r_lhs r) <= r_rhs r
  | Ge => leval x (r_lhs r) >= r_rhs r
  | Eq => leval x (r_lhs r) = r_rhs r
  end.

Fixpoint coef (l : lin) (v : positive) : Z :=
  match l with [] => 0 | (w, a) :: r => (if Pos.eqb w v then a else 0) + coef r v end.

Fixpoint vars_in (l : lin) (nv : N) : bool :=
  match l with [] => true | (w, _) :: r => N.leb (N.pos w) nv && vars_in r nv end.

Fixpoint nsum (f : positive -> Z) (n : nat) : Z :=
  match n with O => 0 | S k => nsum f k + f (pos_of k) end.

Record lp := mklp { lp_nv : nat; lp_rows : list row; lp_obj : lin; lp_bound : Z }.

Fixpoint zipsum (ys : list Z) (rs : list row) (f : Z -> row -> Z) : Z :=
  match ys, rs with
  | y :: ys', r :: rs' => f y r + zipsum ys' rs' f
  | _, _ => 0
  end.

Fixpoint signs_ok (ys : list Z) (rs : list row) : bool :=
  match ys, rs with
  | y :: ys', r :: rs' => (match r_cmp r with Le => 0 <=? y | Ge => y <=? 0 | Eq => true end) && signs_ok ys' rs'
  | [], [] => true
  | _, _ => false
  end.

Fixpoint rows_vars_in (rs : list row) (nv : N) : bool :=
  match rs with [] => true | r :: rs' => vars_in (r_lhs r) nv && rows_vars_in rs' nv end.

Definition colsum (ys : list Z) (rs : list row) (v : positive) : Z := zipsum ys rs (fun y r => y * coef (r_lhs r) v).

Fixpoint cols_ok (ys : list Z) (rs : list row) (obj : lin) (D : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S k => (D * coef obj (pos_of k) <=? colsum ys rs (pos_of k)) && cols_ok ys rs obj D k
  end.

Definition lp_check (P : lp) (ys : list Z) (D : Z) : bool :=
  let nvN := N.of_nat (lp_nv P) in
  (0 <? D) && rows_vars_in (lp_rows P) nvN && vars_in (lp_obj P) nvN
  && signs_ok ys (lp_rows P)
  && cols_ok ys (lp_rows P) (lp_obj P) D (lp_nv P)
  && (zipsum ys (lp_rows P) (fun y r => y * r_rhs r) <=? D * lp_bound P).

