(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import List Permutation.
Import ListNotations.

Lemma perm_chunk_middle {A} (c l l1 l2 : list A) :
Permutation l (l1 ++ l2) -> Permutation (c ++ l) (l1 ++ c ++ l2).
Proof.
intros H. eapply Permutation_trans; [apply Permutation_app_head; exact H|].
apply Permutation_app_swap_app.
Qed.

Lemma perm_chunk_last {A} (c l l1 : list A) :
Permutation l l1 -> Permutation (c ++ l) (l1 ++ c).
Proof.
intros H. eapply Permutation_trans; [apply Permutation_app_head; exact H|]. apply Permutation_app_comm.
Qed.

Lemma perm_tail_last {A} (c l1 : list A) :
Permutation (@nil A) l1 -> Permutation c (l1 ++ c).
Proof. intros H. apply Permutation_nil in H. subst l1. apply Permutation_refl. Qed.

Ltac perm_norm := repeat rewrite <- app_assoc; repeat rewrite app_nil_r; cbn [app].

Ltac find_cons x r :=
lazymatch r with
| x :: ?r2 => let T := type of x in constr:((@nil T , r2))
| ?y :: ?r' => lazymatch find_cons x r' with (?r1, ?r2) => constr:((y :: r1, r2)) end
| ?c ++ ?r' => lazymatch find_cons x r' with (?r1, ?r2) => constr:((c ++ r1, r2)) end
end.

Ltac find_chunk c r :=
lazymatch r with
| c ++ ?r2 => lazymatch type of c with list ?T => constr:((@nil T, r2)) end
| c => lazymatch type of c with list ?T => constr:((@nil T, tt)) end
| ?y :: ?r' => lazymatch find_chunk c r' with (?r1, ?r2) => constr:((y :: r1, r2)) end
| ?d ++ ?r' => lazymatch find_chunk c r' with (?r1, ?r2) => constr:((d ++ r1, r2)) end
end.

Ltac perm_solve :=
perm_norm;
lazymatch goal with
| |- Permutation ?l ?l => apply Permutation_refl
| |- Permutation nil ?r => apply Permutation_refl
| |- Permutation (?x :: ?l) ?r =>
lazymatch find_cons x r with
| (?r1, ?r2) =>
apply (@Permutation_trans _ _ (r1 ++ x :: r2));
[ apply Permutation_cons_app; perm_solve
| perm_norm; apply Permutation_refl ]
end
| |- Permutation (?c ++ ?l) ?r =>
lazymatch find_chunk c r with
| (?r1, tt) =>
apply (@Permutation_trans _ _ (r1 ++ c));
[ apply perm_chunk_last; perm_solve
| perm_norm; apply Permutation_refl ]
| (?r1, ?r2) =>
apply (@Permutation_trans _ _ (r1 ++ c ++ r2));
[ apply perm_chunk_middle; perm_solve
| perm_norm; apply Permutation_refl ]
end
| |- Permutation ?c ?r =>
lazymatch find_chunk c r with
| (?r1, tt) => apply perm_tail_last; perm_solve
end
end.

Goal forall (a b c : nat) (X Y Z : list nat),
Permutation (a :: X ++ b :: Y ++ c :: Z) ((Y ++ [c; a]) ++ X ++ b :: Z).
Proof. intros. perm_solve. Qed.
Goal forall (X Y Z W : list nat) (p q : nat),
Permutation (X ++ Y ++ Z ++ W) (Z ++ (X ++ Y) ++ W).
Proof. intros. perm_solve. Qed.
Goal forall (X Y : list nat) (p q r : nat),
Permutation (p :: q :: r :: X ++ Y) ((X ++ [r; q; p]) ++ Y).
Proof. intros. perm_solve. Qed.
Goal forall (X L : list nat) (g0 g1 g2 blk : nat),
Permutation (g2 :: g1 :: g0 :: L ++ blk :: X) ((L ++ [g0; g1; g2; blk]) ++ X).
Proof. intros. perm_solve. Qed.
Goal forall (X L : list nat) (o1 o2 : list nat) (blk : nat),
Permutation (o2 ++ o1 ++ L ++ blk :: X) (L ++ o1 ++ o2 ++ blk :: X).
Proof. intros. perm_solve. Qed.
Goal forall (X : list nat) (o1 : list nat), Permutation (o1 ++ X) (o1 ++ X).
Proof. intros. perm_solve. Qed.
Goal forall (X Y : list nat), Permutation (X ++ Y) (Y ++ X).
Proof. intros. perm_solve. Qed.
