(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition yptr := nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive yprog (A : Type) : Type :=
| YRet (a : A)
| YAbort
| YMalloc (n : Z) (k : option yptr -> yprog A)
| YRealloc (p : option yptr) (n : Z) (k : option yptr -> yprog A)
| YFree (p : option yptr) (k : yprog A)
| YEmit (bytes : list Z) (k : yprog A).

Arguments YRet {A} a.
Arguments YAbort {A}.
Arguments YMalloc {A} n k.
Arguments YRealloc {A} p n k.
Arguments YFree {A} p k.
Arguments YEmit {A} bytes k.

Fixpoint ybind {A B : Type} (m : yprog A) (f : A -> yprog B) : yprog B :=
  match m with
  | YRet a => f a
  | YAbort => YAbort
  | YMalloc n k => YMalloc n (fun r => ybind (k r) f)
  | YRealloc p n k => YRealloc p n (fun r => ybind (k r) f)
  | YFree p k => YFree p (ybind k f)
  | YEmit bs k => YEmit bs (ybind k f)
  end.

(* [comment removed for export] *)
Definition ymalloc (n : Z) : yprog (option yptr) := YMalloc n (fun r => YRet r).
Definition yrealloc (p : option yptr) (n : Z) : yprog (option yptr) := YRealloc p n (fun r => YRet r).
Definition yfree (p : option yptr) : yprog unit := YFree p (YRet tt).
Definition yemit (bs : list Z) : yprog unit := YEmit bs (YRet tt).
(* [comment removed for export] *)
Definition yassert (b : bool) : yprog unit := if b then YRet tt else YAbort.

Declare Scope yprog_scope.
Notation "x <- m ;; k" := (ybind m (fun x => k))
  (at level 100, m at next level, right associativity) : yprog_scope.
Notation "m ;;; k" := (ybind m (fun _ => k))
  (at level 100, right associativity) : yprog_scope.
Notation "' p <- m ;; k" := (ybind m (fun x => let 'p := x in k))
  (at level 100, p pattern, m at next level, right associativity) : yprog_scope.
Open Scope yprog_scope.

(* [comment removed for export] *)
Lemma ybind_ret_l : forall {A B} (a : A) (f : A -> yprog B), ybind (YRet a) f = f a.
Proof. reflexivity. Qed.
Lemma ybind_abort_l : forall {A B} (f : A -> yprog B), ybind YAbort f = YAbort.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint ysafe {A : Type} (m : yprog A) : Prop :=
  match m with
  | YRet _ => True
  | YAbort => False
  | YMalloc _ k => forall r, ysafe (k r)
  | YRealloc _ _ k => forall r, ysafe (k r)
  | YFree _ k => ysafe k
  | YEmit _ k => ysafe k
  end.

(* [comment removed for export] *)
Fixpoint ypost {A : Type} (m : yprog A) (Q : A -> Prop) : Prop :=
  match m with
  | YRet a => Q a
  | YAbort => False
  | YMalloc _ k => forall r, ypost (k r) Q
  | YRealloc _ _ k => forall r, ypost (k r) Q
  | YFree _ k => ypost k Q
  | YEmit _ k => ypost k Q
  end.

Lemma ypost_safe : forall {A} (m : yprog A) Q, ypost m Q -> ysafe m.
Proof. induction m; cbn; intros; auto; try (intros; eauto). Qed.

Lemma ypost_true : forall {A} (m : yprog A), ysafe m -> ypost m (fun _ => True).
Proof. induction m; cbn; intros; auto. Qed.

Lemma ypost_mono : forall {A} (m : yprog A) (Q Q' : A -> Prop),
  ypost m Q -> (forall a, Q a -> Q' a) -> ypost m Q'.
Proof. induction m; cbn; intros; eauto. Qed.

Lemma ypost_bind : forall {A B} (m : yprog A) (f : A -> yprog B) (Q : A -> Prop) (R : B -> Prop),
  ypost m Q -> (forall a, Q a -> ypost (f a) R) -> ypost (ybind m f) R.
Proof. induction m; cbn; intros; eauto. Qed.

Lemma ypost_ret : forall {A} (a : A) (Q : A -> Prop), Q a -> ypost (YRet a) Q.
Proof. intros; exact H. Qed.

Lemma ypost_conj : forall {A} (m : yprog A) (Q Q' : A -> Prop),
  ypost m Q -> ypost m Q' -> ypost m (fun a => Q a /\ Q' a).
Proof. induction m; cbn; intros; eauto; try contradiction. Qed.

(* [comment removed for export] *)
Lemma ypost_bind_inv : forall {A B} (m : yprog A) (f : A -> yprog B) (R : B -> Prop),
  ypost (ybind m f) R -> ypost m (fun a => ypost (f a) R).
Proof. induction m; cbn; intros; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zslice (l : list Z) (i n : Z) : list Z := firstn (Z.to_nat n) (skipn (Z.to_nat i) l).

Lemma zslice_length : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l ->
  zlength (zslice l i n) = n.
Proof.
  intros l i n Hi Hn H. unfold zslice, zlength in *.
  rewrite length_firstn, length_skipn. lia.
Qed.

(* [comment removed for export] *)
Definition c_tab : Z := 9.     Definition c_lf : Z := 10.   Definition c_vt : Z := 11.
Definition c_ff : Z := 12.     Definition c_cr : Z := 13.   Definition c_sp : Z := 32.
Definition c_quote : Z := 34.  (* [comment removed for export] *)
Definition c_star : Z := 42.   (* [comment removed for export] *)
Definition c_plus : Z := 43.   Definition c_comma : Z := 44. Definition c_minus : Z := 45.
Definition c_dot : Z := 46.    Definition c_slash : Z := 47.
Definition c_0 : Z := 48.      Definition c_1 : Z := 49.    Definition c_9 : Z := 57.
Definition c_colon : Z := 58.
Definition c_A : Z := 65.      Definition c_E : Z := 69.    Definition c_F : Z := 70.
Definition c_lbracket : Z := 91.  (* [comment removed for export] *)
Definition c_bslash : Z := 92.    (* [comment removed for export] *)
Definition c_rbracket : Z := 93.  (* [comment removed for export] *)
Definition c_a : Z := 97.  Definition c_b : Z := 98.  Definition c_e : Z := 101. Definition c_f : Z := 102.
Definition c_n : Z := 110. Definition c_r : Z := 114. Definition c_t : Z := 116. Definition c_u : Z := 117.
Definition c_lbrace : Z := 123.   (* [comment removed for export] *)
Definition c_rbrace : Z := 125.   (* [comment removed for export] *)

Definition is_digit (c : Z) : bool := (c_0 <=? c) && (c <=? c_9).
