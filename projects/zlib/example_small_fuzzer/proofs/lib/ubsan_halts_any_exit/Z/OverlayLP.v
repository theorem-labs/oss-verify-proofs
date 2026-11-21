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

Lemma pos_of_inj k k' : pos_of k = pos_of k' -> k = k'.
Proof. unfold pos_of. intros H. apply SuccNat2Pos.inj. exact H. Qed.

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

Lemma nsum_ext f g n : (forall k, (k < n)%nat -> f (pos_of k) = g (pos_of k)) -> nsum f n = nsum g n.
Proof. induction n; cbn [nsum]; intros; [reflexivity|]. rewrite IHn, H; auto. Qed.
Lemma nsum_zero' (f : positive -> Z) n : (forall v, f v = 0) -> nsum f n = 0.
Proof. intros H. induction n; cbn [nsum]; [reflexivity|]. rewrite IHn, H. reflexivity. Qed.
Lemma nsum_add f g n : nsum (fun v => f v + g v) n = nsum f n + nsum g n.
Proof. induction n; cbn [nsum]; lia. Qed.
Lemma nsum_scale c f n : nsum (fun v => c * f v) n = c * nsum f n.
Proof. induction n; cbn [nsum]; lia. Qed.
Lemma nsum_le f g n : (forall k, (k < n)%nat -> f (pos_of k) <= g (pos_of k)) -> nsum f n <= nsum g n.
Proof. induction n; cbn [nsum]; intros; [lia|]. pose proof (H n ltac:(lia)). specialize (IHn ltac:(intros; apply H; lia)). lia. Qed.
Lemma nsum_single n k a : (k < n)%nat -> nsum (fun v => if Pos.eqb (pos_of k) v then a else 0) n = a.
Proof.
  induction n; cbn [nsum]; intros; [lia|].
  destruct (Nat.eq_dec k n) as [->|NE].
  - rewrite Pos.eqb_refl. rewrite (nsum_ext _ (fun _ => 0)); [rewrite nsum_zero' by reflexivity; lia|].
    intros k' Hk'. destruct (Pos.eqb_spec (pos_of n) (pos_of k')); [|reflexivity]. apply pos_of_inj in e. lia.
  - rewrite IHn by lia. destruct (Pos.eqb_spec (pos_of k) (pos_of n)); [|lia]. apply pos_of_inj in e. lia.
Qed.

Lemma in_universe w nv : N.leb (N.pos w) (N.of_nat nv) = true -> exists k, (k < nv)%nat /\ pos_of k = w.
Proof.
  intros H. apply N.leb_le in H. exists (Nat.pred (Pos.to_nat w)). split.
  - pose proof (Pos2Nat.is_pos w). lia.
  - unfold pos_of. apply SuccNat2Pos.inv. pose proof (Pos2Nat.is_pos w). lia.
Qed.

Lemma leval_coef x l nv : vars_in l (N.of_nat nv) = true -> leval x l = nsum (fun v => coef l v * x v) nv.
Proof.
  induction l as [|[w a] r IH]; cbn [leval coef vars_in]; intros V.
  - rewrite nsum_zero' by (intros; lia). reflexivity.
  - apply andb_prop in V. destruct V as [V1 V2].
    destruct (in_universe w nv V1) as (k & Hk & <-).
    rewrite (IH V2).
    rewrite (nsum_ext (fun v => ((if Pos.eqb (pos_of k) v then a else 0) + coef r v) * x v)
                      (fun v => (if Pos.eqb (pos_of k) v then a * x (pos_of k) else 0) + coef r v * x v)).
    2:{ intros k' _. destruct (Pos.eqb_spec (pos_of k) (pos_of k')); [rewrite e; lia|lia]. }
    rewrite nsum_add. rewrite (nsum_single nv k (a * x (pos_of k)) Hk). lia.
Qed.

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

Lemma cols_ok_all ys rs obj D n : cols_ok ys rs obj D n = true ->
  forall k, (k < n)%nat -> D * coef obj (pos_of k) <= colsum ys rs (pos_of k).
Proof.
  induction n; cbn; intros H k Hk; [lia|]. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Nat.eq_dec k n); [subst; apply Z.leb_le; exact H1|]. apply IHn; [exact H2|lia].
Qed.

Lemma zipsum_rows_le x : forall ys rs nv,
  signs_ok ys rs = true -> rows_vars_in rs (N.of_nat nv) = true -> Forall (holds x) rs ->
  nsum (fun v => colsum ys rs v * x v) nv <= zipsum ys rs (fun y r => y * r_rhs r).
Proof.
  induction ys as [|y ys IH]; intros [|r rs] nv S V F; cbn in *; try discriminate.
  - unfold colsum. cbn [zipsum]. rewrite nsum_zero' by (intros; lia). lia.
  - apply andb_prop in S. destruct S as [S1 S2]. apply andb_prop in V. destruct V as [V1 V2].
    inversion F; subst.
    unfold colsum. cbn [zipsum].
    rewrite (nsum_ext (fun v => (y * coef (r_lhs r) v + zipsum ys rs (fun y0 r0 => y0 * coef (r_lhs r0) v)) * x v)
                      (fun v => y * (coef (r_lhs r) v * x v) + colsum ys rs v * x v)) by (intros; unfold colsum; lia).
    rewrite nsum_add, nsum_scale. rewrite <- (leval_coef x (r_lhs r) nv V1).
    specialize (IH rs nv S2 V2 H2).
    unfold holds in H1. destruct (r_cmp r); [apply Z.leb_le in S1|apply Z.leb_le in S1|]; nia.
Qed.

Theorem lp_check_sound P ys D x :
  lp_check P ys D = true ->
  (forall k, (k < lp_nv P)%nat -> 0 <= x (pos_of k)) ->
  Forall (holds x) (lp_rows P) ->
  leval x (lp_obj P) <= lp_bound P.
Proof.
  intros C NN F. unfold lp_check in C.
  repeat (apply andb_prop in C; destruct C as [C ?]).
  apply Z.ltb_lt in C. apply Z.leb_le in H.
  pose proof (cols_ok_all _ _ _ _ _ H0) as COL.
  pose proof (zipsum_rows_le x ys (lp_rows P) (lp_nv P) H1 H3 F) as ZR.
  rewrite (leval_coef x (lp_obj P) (lp_nv P) H2).
  assert (D * nsum (fun v => coef (lp_obj P) v * x v) (lp_nv P) <= nsum (fun v => colsum ys (lp_rows P) v * x v) (lp_nv P)).
  { rewrite <- nsum_scale. apply nsum_le. intros k Hk. pose proof (COL k Hk). pose proof (NN k Hk). nia. }
  nia.
Qed.
