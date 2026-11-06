(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import List Permutation.
Import ListNotations.

Section P.
  Context {T : Type}.

  Lemma perm_pull_here : forall (X R0 : list T), Permutation (X ++ R0) (X ++ R0).
  Proof. intros. apply Permutation_refl. Qed.

  Lemma perm_pull_last : forall (X : list T), Permutation X (X ++ []).
  Proof. intros. rewrite app_nil_r. apply Permutation_refl. Qed.

  Lemma perm_pull_step : forall (Y X R0 R0' : list T), Permutation R0 (X ++ R0') -> Permutation (Y ++ R0) (X ++ (Y ++ R0')).
  Proof.
    intros Y X R0 R0' P. eapply Permutation_trans; [apply Permutation_app_head; exact P|].
    rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  Qed.

  Lemma perm_cancel : forall (X L R R' : list T), Permutation R (X ++ R') -> Permutation L R' -> Permutation (X ++ L) R.
  Proof.
    intros X L R R' P Q. eapply Permutation_trans; [|apply Permutation_sym; exact P]. apply Permutation_app_head. exact Q.
  Qed.

  Lemma perm_cancel_last : forall (X R R' : list T), Permutation R (X ++ R') -> Permutation [] R' -> Permutation X R.
  Proof.
    intros X R R' P Q. eapply Permutation_trans; [|apply Permutation_sym; exact P].
    rewrite <- (app_nil_r X) at 1. apply Permutation_app_head. exact Q.
  Qed.

  Lemma perm_cons_app : forall (a : T) (l : list T), a :: l = [a] ++ l.
  Proof. reflexivity. Qed.
End P.

Ltac perm_pull X R :=
  lazymatch R with
  | X ++ ?R0 => constr:(perm_pull_here X R0)
  | ?Y ++ ?R0 => let p0 := perm_pull X R0 in constr:(perm_pull_step Y X R0 _ p0)
  | X => constr:(perm_pull_last X)
  end.

Ltac perm_norm :=
  repeat (rewrite <- ?app_assoc, ?app_nil_r, ?app_nil_l);
  repeat match goal with
         | |- context [?a :: ?l] => lazymatch l with [] => fail | _ => rewrite (perm_cons_app a l) end
         end;
  repeat (rewrite <- ?app_assoc, ?app_nil_r, ?app_nil_l).

Ltac perm_solve_core :=
  lazymatch goal with
  | |- Permutation ?L ?L => apply Permutation_refl
  | |- Permutation [] [] => apply Permutation_refl
  | |- Permutation (?X ++ ?L) ?R =>
      let p := perm_pull X R in
      eapply (perm_cancel X L R _ p); cbv beta; perm_solve_core
  | |- Permutation ?X ?R =>
      let p := perm_pull X R in
      eapply (perm_cancel_last X R _ p); cbv beta; perm_solve_core
  end.

Ltac perm_solve := perm_norm; perm_solve_core.

Goal forall (T : Type) (A B C D E : list T) (x : T),
  Permutation (A ++ (B ++ x :: C) ++ D ++ E) (E ++ C ++ ((D ++ [x]) ++ B) ++ A).
Proof. intros. perm_solve. Qed.
Goal forall (T : Type) (A B C : list T), Permutation (A ++ B ++ C) (C ++ [] ++ B ++ A).
Proof. intros. perm_solve. Qed.
