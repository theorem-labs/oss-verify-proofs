(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require Import List Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma perm_nil_end {A} (l r : list A) : Permutation (l ++ []) (r ++ []) -> Permutation l r.
Proof. rewrite !app_nil_r. exact (fun H => H). Qed.

Ltac perm_split_elem T x r k :=
lazymatch r with
| x :: ?r2 => k (@nil T) r2
| ?y :: ?r' => perm_split_elem T x r' ltac:(fun r1 r2 => k (y :: r1) r2)
| ?B ++ ?r' => perm_split_elem T x r' ltac:(fun r1 r2 => k (B ++ r1) r2)
end.

Ltac perm_split_chunk T A r k :=
lazymatch r with
| A ++ ?r2 => k (@nil T) r2
| ?y :: ?r' => perm_split_chunk T A r' ltac:(fun r1 r2 => k (y :: r1) r2)
| ?B ++ ?r' => perm_split_chunk T A r' ltac:(fun r1 r2 => k (B ++ r1) r2)
end.

Ltac perm_norm := cbn [app]; repeat (first [ progress (rewrite <- ?app_assoc) | progress (cbn [app]) ]).

Ltac perm_step :=
lazymatch goal with
| |- @Permutation ?T ?l ?r =>
first
[ apply Permutation_refl
| lazymatch l with
| ?x :: ?l' =>
perm_split_elem T x r ltac:(fun r1 r2 =>
apply (@Permutation_trans T (x :: l') (x :: (r1 ++ r2)) r);
[ apply perm_skip
| replace r with (r1 ++ x :: r2) by (perm_norm; reflexivity); apply Permutation_middle ])
| ?A ++ ?l' =>
perm_split_chunk T A r ltac:(fun r1 r2 =>
apply (@Permutation_trans T (A ++ l') (A ++ (r1 ++ r2)) r);
[ apply Permutation_app_head
| replace r with (r1 ++ A ++ r2) by (perm_norm; reflexivity); apply Permutation_app_swap_app ])
end ]
end.

Ltac perm :=
apply perm_nil_end; perm_norm;
repeat (perm_step; perm_norm).

