(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pf_elem_seg {A} (S R : list A) (e : A) : Permutation (S ++ e :: R) (e :: S ++ R).
Proof. apply Permutation_sym. apply Permutation_middle. Qed.
Lemma pf_seg_elem {A} (Sg R : list A) (x : A) : Permutation (x :: Sg ++ R) (Sg ++ x :: R).
Proof. apply Permutation_middle. Qed.
Lemma pf_seg_nil {A} (Sg : list A) : Permutation Sg (Sg ++ []).
Proof. rewrite app_nil_r. apply Permutation_refl. Qed.
Lemma pf_elem_nil {A} (e : A) : Permutation [e] (e :: []).
Proof. apply Permutation_refl. Qed.

(* [comment removed for export] *)
Ltac pfront e :=
  lazymatch goal with
  | |- Permutation (e :: _) _ => apply Permutation_refl
  | |- Permutation (?x :: _) _ => eapply Permutation_trans; [apply perm_skip; pfront e|apply perm_swap]
  | |- Permutation (?S ++ _) _ => eapply Permutation_trans; [apply Permutation_app_head; pfront e|apply pf_elem_seg]
  end.
(* [comment removed for export] *)
Ltac psfront Sg :=
  lazymatch goal with
  | |- Permutation (Sg ++ _) _ => apply Permutation_refl
  | |- Permutation Sg _ => apply pf_seg_nil
  | |- Permutation (?x :: _) _ => eapply Permutation_trans; [apply perm_skip; psfront Sg|apply pf_seg_elem]
  | |- Permutation (?S ++ _) _ => eapply Permutation_trans; [apply Permutation_app_head; psfront Sg|apply Permutation_app_swap_app]
  end.
Ltac perm_norm := cbn [app]; repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); cbn [app].
Ltac perm_solve :=
  perm_norm;
  lazymatch goal with
  | |- Permutation ?L ?L => apply Permutation_refl
  | |- Permutation _ [] => apply Permutation_refl
  | |- Permutation _ (?e :: _) => eapply Permutation_trans; [pfront e|]; apply perm_skip; perm_solve
  | |- Permutation _ (?S ++ _) => eapply Permutation_trans; [psfront S|]; apply Permutation_app_head; perm_solve
  | |- Permutation _ ?S => eapply Permutation_trans; [psfront S|]; rewrite app_nil_r; apply Permutation_refl
  end.
(* [comment removed for export] *)
Ltac perm_via H := eapply Permutation_trans; [exact H|]; perm_solve.
