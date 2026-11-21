(* SPDX-License-Identifier: LGPL-2.1-or-later *)
(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU Lesser General Public License for more details.                *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)
(* Modified by Theorem Labs, 2026-11: 3 lines added (Unset Lia Cache, Unset Nia Cache, Unset Nra Cache). *)

(** * Auxiliary functions and theorems

- Key definitions: [map2], [find_min], [find_max]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Export List Arith.
From Coq Require Import Inverse_Image Wf_nat Sorting.Permutation.
Export ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Set Default Proof Using "Type".

(** Properties of the fold operator *)
Section Fold.

Variables (A : Type) (B : Type).
Variable f : A -> B -> A.
Variable g : B -> A -> A.
Variable h : A -> A.
 
Theorem fold_left_eta :
 forall l a f1,
 (forall a b, In b l -> f a b = f1 a b) -> fold_left f l a = fold_left f1 l a.
Proof.
intros l; elim l; simpl in |- *; auto.
intros a l0 H a0 f1 H0.
rewrite H0; auto.
Qed.
 
Theorem fold_left_map :
 forall (C : Type) a l (k : C -> B),
 fold_left f (map k l) a = fold_left (fun a b => f a (k b)) l a.
Proof.
intros C a l k; generalize a; elim l; simpl in |- *; auto.
Qed.
 
Theorem fold_left_init :
 (forall (a : A) (b : B), h (f a b) = f (h a) b) ->
 forall (a : A) (l : list B), fold_left f l (h a) = h (fold_left f l a).
Proof.
intros H a l; generalize a; elim l; clear l a; simpl in |- *; auto.
intros a l H0 a0.
rewrite <- H; auto.
Qed.
 
End Fold.

(** Some properties of list operators: app, map, ... *)
Section List.

Variables (A : Type) (B : Type) (C : Type).
Variable f : A -> B.

(** An induction theorem for list based on length *)
Theorem list_length_ind :
 forall P : list A -> Prop,
 (forall l1 : list A,
  (forall l2 : list A, length l2 < length l1 -> P l2) -> P l1) ->
 forall l : list A, P l.
Proof.
intros P H l;
 apply well_founded_ind with (R := fun x y : list A => length x < length y);
 auto.
apply wf_inverse_image with (R := lt); auto.
apply lt_wf.
Qed.

Program Definition list_length_induction (P : list A -> Type)
 (rec : forall l1 : list A, (forall l2 : list A, length l2 < length l1 -> P l2) -> P l1)
 (l : list A) : P l :=
@well_founded_induction_type _
 (fun x y : list A => length x < length y)
  ((fun _ _ _ => @wf_inverse_image _ _ lt _ _) P rec l) P rec l.

Theorem app_inv_app :
 forall l1 l2 l3 l4 a,
 l1 ++ l2 = l3 ++ a :: l4 ->
 (exists l5 : list A, l1 = l3 ++ a :: l5) \/
 (exists l5, l2 = l5 ++ a :: l4).
Proof.
intros l1; elim l1; simpl in |- *; auto.
intros l2 l3 l4 a H; right; exists l3; auto.
intros a l H l2 l3 l4 a0; case l3; simpl in |- *.
intros H0; left; exists l; apply f_equal2 with (f := cons (A:=A));
 injection H0; auto.
intros b l0 H0; case (H l2 l0 l4 a0); auto.
injection H0; auto.
intros (l5, H1).
left; exists l5; apply f_equal2 with (f := cons (A:=A)); injection H0; auto.
Qed.
 
Theorem app_inv_app2 :
 forall l1 l2 l3 l4 a b,
 l1 ++ l2 = l3 ++ a :: b :: l4 ->
 (exists l5 : list A, l1 = l3 ++ a :: b :: l5) \/
 (exists l5, l2 = l5 ++ a :: b :: l4) \/
 l1 = l3 ++ a :: [] /\ l2 = b :: l4.
Proof.
intros l1; elim l1; simpl in |- *; auto.
intros l2 l3 l4 a b H; right; left; exists l3; auto.
intros a l H l2 l3 l4 a0 b; case l3; simpl in |- *.
case l; simpl in |- *.
intros H0; right; right; injection H0; split; auto.
apply f_equal2 with (f := cons (A:=A)); auto.
intros b0 l0 H0; left; exists l0; injection H0; intros;
 repeat apply f_equal2 with (f := cons (A:=A)); auto.
intros b0 l0 H0; case (H l2 l0 l4 a0 b); auto.
injection H0; auto.
intros (l5, HH1); left; exists l5; apply f_equal2 with (f := cons (A:=A));
 auto; injection H0; auto.
intros [H1| (H1, H2)]; auto.
right; right; split; auto; apply f_equal2 with (f := cons (A:=A)); auto;
 injection H0; auto.
Qed.
 
Theorem same_length_ex :
 forall (a : A) l1 l2 l3,
 length (l1 ++ a :: l2) = length l3 ->
 exists l4,
   (exists l5,
      (exists b : B,
         length l1 = length l4 /\ length l2 = length l5 /\ l3 = l4 ++ b :: l5)).
Proof.
intros a l1; elim l1; simpl in |- *; auto.
intros l2 l3; case l3; simpl in |- *; try (intros; discriminate).
intros b l H; exists []; exists l; exists b; repeat (split; auto).
intros a0 l H l2 l3; case l3; simpl in |- *; try (intros; discriminate).
intros b l0 H0.
case (H l2 l0); auto.
intros l4 (l5, (b1, (HH1, (HH2, HH3)))).
exists (b :: l4); exists l5; exists b1; repeat (simpl in |- *; split; auto).
apply f_equal2 with (f := cons (A:=B)); auto.
Qed.
 
Theorem in_map_fst_inv :
 forall a (l : list (B * C)),
 In a (map (fst (B:=_)) l) -> exists c, In (a, c) l.
Proof.
intros a l; elim l; simpl in |- *; auto.
intros H; case H.
intros a0 l0 H [H0| H0]; auto.
exists (snd a0); left; rewrite <- H0; case a0; simpl in |- *; auto.
case H; auto; intros l1 Hl1; exists l1; auto.
Qed.

(** Properties of flat_map *)
Theorem in_flat_map_in :
 forall (l : list B) (f : B -> list C) a b,
 In a (f b) -> In b l -> In a (flat_map f l).
Proof.
intros; apply in_flat_map; exists b; split; auto.
Qed.
 
Theorem in_flat_map_ex :
 forall (l : list B) (f : B -> list C) a,
 In a (flat_map f l) -> exists b, In b l /\ In a (f b).
Proof.
intros; apply in_flat_map; auto.
Qed.

Theorem NoDup_app :
 forall l1 l2,
 NoDup l1 ->
 NoDup l2 -> (forall a : A, In a l1 -> In a l2 -> False) -> NoDup (l1 ++ l2).
Proof.
intros L1; elim L1; simpl in |- *; auto.
intros a l H l2 H0 H1 H2; apply NoDup_cons; simpl in |- *; auto.
red in |- *; intros H3; case in_app_or with (1 := H3); auto; intros H4.
inversion H0; auto.
apply H2 with a; auto.
apply H; auto.
apply NoDup_cons_iff with (1 := H0); auto.
intros a0 H3 H4; apply (H2 a0); auto.
Qed.

Theorem NoDup_app_inv :
 forall l1 l2 (a : A), NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 a0 H0 [H1| H1] H2.
inversion H0; auto.
case H5; rewrite H1; auto with datatypes.
apply (H l2 a0); auto.
apply NoDup_cons_iff with (1 := H0); auto.
Qed.

Theorem NoDup_app_inv_l :
 forall (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
intros l1; elim l1; simpl in |- *; auto using NoDup_nil.
intros a l H l2 H0; inversion H0; apply NoDup_cons; auto.
contradict H3; auto with datatypes.
apply H with l2; auto.
Qed.

Theorem NoDup_app_inv_r : forall l1 l2 : list A, NoDup (l1 ++ l2) -> NoDup l2.
Proof.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 H0; inversion H0; auto.
Qed.
 
End List.

(** Definition of map2 *)
Section map2.
Variables (A : Type) (B : Type) (C : Type).
Variable f : A -> B -> C.
 
Fixpoint map2 (l1 : list A) : list B -> list C :=
  fun l2 =>
  match l1 with
  | [] => []
  | a :: l3 =>
      match l2 with
      | [] => []
      | b :: l4 => f a b :: map2 l3 l4
      end
  end.
 
Theorem map2_app :
 forall l1 l2 l3 l4,
 length l1 = length l2 ->
 map2 (l1 ++ l3) (l2 ++ l4) = map2 l1 l2 ++ map2 l3 l4.
Proof.
intros l1; elim l1; auto.
intros l2; case l2; simpl in |- *; auto; intros; discriminate.
intros a l H l2 l3 l4; case l2.
simpl in |- *; intros; discriminate.
intros b l0 H0.
apply trans_equal with (f a b :: map2 (l ++ l3) (l0 ++ l4)).
simpl in |- *; auto.
rewrite H; auto.
Qed.
 
End map2.

Arguments map2 [A B C].

(** Properties of the firstn and skipn functions *)
Section First.
Variable A : Type.

(** Properties of firstn *)
Theorem firstn_le_app1 :
 forall (n : nat) (l1 l2 : list A),
 length l1 <= n -> firstn n (l1 ++ l2) = l1 ++ firstn (n - length l1) l2.
Proof.
intros n; elim n; simpl in |- *; auto.
intros l1; case l1; simpl in |- *; auto.
intros b l l2 H; contradict H; auto with arith.
intros n0 H l1; case l1; simpl in |- *; auto with arith.
intros b l l2 H0; rewrite H; auto with arith.
Qed.
 
Theorem firstn_le_app2 :
 forall (n : nat) (l1 l2 : list A),
 n <= length l1 -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
intros n; elim n; simpl in |- *; auto.
intros n0 H l1 l2; case l1; simpl in |- *.
intros H1; contradict H1; auto with arith.
intros a l H0; (apply f_equal2 with (f := cons (A:=A)); auto).
apply H; apply le_S_n; auto.
Qed.

Theorem firstn_le_length_eq :
 forall (n : nat) (l1 : list A), n <= length l1 -> length (firstn n l1) = n.
Proof.
intros n l1; generalize n; elim l1; clear n l1; simpl in |- *; auto.
intros n; case n; simpl in |- *; auto.
intros n1 H1; contradict H1; auto with arith.
intros a l H n; case n; simpl in |- *; auto with arith.
Qed.

Theorem skipn_le_app1 :
 forall (n : nat) (l1 l2 : list A),
 length l1 <= n -> skipn n (l1 ++ l2) = skipn (n - length l1) l2.
Proof.
intros n; elim n; simpl in |- *; auto.
intros l1; case l1; simpl in |- *; auto.
intros b l l2 H; contradict H; auto with arith.
intros n0 H l1; case l1; simpl in |- *; auto with arith.
Qed.
 
Theorem skipn_le_app2 :
 forall (n : nat) (l1 l2 : list A),
 n <= length l1 -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
intros n; elim n; simpl in |- *; auto.
intros n0 H l1; case l1; simpl in |- *; auto with arith.
intros l2 H1; contradict H1; auto with arith.
Qed.

End First.

(** Existence of a first max *)
Section FirstMax.
 
Theorem exist_first_max :
 forall l : list nat,
 l <> [] ->
 exists a : nat,
   (exists l1 : list nat,
      (exists l2 : list nat,
         l = l1 ++ a :: l2 /\
         (forall n1, In n1 l1 -> n1 < a) /\ (forall n1, In n1 l2 -> n1 <= a))).
Proof.
intros l; elim l; simpl in |- *; auto.
intros H; case H; auto.
intros a l0; case l0.
intros H H0; exists a; exists []; exists [];
 repeat (split; simpl in |- *; auto with datatypes).
intros n1 H1; case H1.
intros n1 H1; case H1.
intros n l1 H H0; case H; clear H; auto.
red in |- *; intros H1; discriminate; auto.
intros a1 (l2, (l3, (HH1, (HH2, HH3)))).
case (Nat.le_gt_cases a1 a); intros HH4; auto.
exists a; exists []; exists (n :: l1);
 repeat (split; auto with datatypes).
intros n1 H1; case H1.
rewrite HH1.
intros n1 H1; apply Nat.le_trans with (2 := HH4); case in_app_or with (1 := H1);
 auto with arith.
intros H2; apply Nat.lt_le_incl; auto.
simpl in |- *; intros [H2| H2]; [ rewrite H2 | idtac ]; auto.
exists a1; exists (a :: l2); exists l3;
 repeat (split; simpl in |- *; auto with datatypes).
apply f_equal2 with (f := cons (A:=nat)); auto.
intros n1 [H2| H2]; [ rewrite <- H2 | idtac ]; auto.
Qed.
 
End FirstMax.

(** Find the minimum and the maximun in a list *)
Section FindMin.
Variable A : Type.
Variable f : A -> nat.

(** Search in the list for the min with respect to a valuation function f *)
Fixpoint find_min (l : list A) : option (nat * A) :=
  match l with
  | [] => None
  | a :: l1 =>
      match find_min l1 with
      | None => Some (f a, a)
      | Some (n1, b) =>
          let n2 := f a in
          match le_lt_dec n1 n2 with
          | left _ => Some (n1, b)
          | right _ => Some (n2, a)
          end
      end
  end.

Theorem find_min_correct :
 forall l : list A,
 match find_min l with
 | None => l = []
 | Some (a, b) => (In b l /\ a = f b) /\ (forall c : A, In c l -> f b <= f c)
 end.
Proof.
intros l; elim l; simpl in |- *; auto.
intros a l0; case (find_min l0); simpl in |- *.
intros p; case p; simpl in |- *.
intros n b ((H1, H2), H3); case (le_lt_dec n (f a)); simpl in |- *.
intros H4; split; auto.
intros c [H5| H5]; auto.
rewrite <- H2; rewrite <- H5; auto.
intros H4; split; auto.
intros c [H5| H5]; auto.
rewrite <- H5; auto.
apply Nat.le_trans with (f b); auto.
rewrite <- H2; auto with arith.
intros H; rewrite H; split; simpl in |- *; auto.
intros c [H1| H1]; rewrite H1 || case H1; auto.
Qed.

(** Search in the list for the max with respect to a valuation function f *)
Fixpoint find_max (l : list A) : option (nat * A) :=
  match l with
  | [] => None
  | a :: l1 =>
      match find_max l1 with
      | None => Some (f a, a)
      | Some (n1, b) =>
          let n2 := f a in
          match le_lt_dec n1 n2 with
          | right _ => Some (n1, b)
          | left _ => Some (n2, a)
          end
      end
  end.
 
Theorem find_max_correct :
 forall l : list A,
 match find_max l with
 | None => l = []
 | Some (a, b) => (In b l /\ a = f b) /\ (forall c : A, In c l -> f c <= f b)
 end.
Proof.
intros l; elim l; simpl in |- *; auto.
intros a l0; case (find_max l0); simpl in |- *.
intros p; case p; simpl in |- *.
intros n b ((H1, H2), H3); case (le_lt_dec n (f a)); simpl in |- *.
intros H4; split; auto.
intros c [H5| H5]; auto.
rewrite <- H5; auto.
apply Nat.le_trans with (f b); auto.
rewrite <- H2; auto with arith.
intros H4; split; auto.
intros c [H5| H5]; auto.
rewrite <- H5; auto.
apply Nat.le_trans with (f b); auto.
rewrite <- H2; auto with arith.
intros H; rewrite H; split; simpl in |- *; auto.
intros c [H1| H1]; rewrite H1 || case H1; auto.
Qed.
 
End FindMin.

Arguments find_min [A].
Arguments find_max [A].

(** Permutation is compatible with fold_left *)
Theorem fold_left_permutation :
 forall (A B : Type) (f : A -> B -> A),
 (forall (a : A) (b1 b2 : B), f (f a b1) b2 = f (f a b2) b1) ->
 forall (a : A) (l1 l2 : list B),
 Permutation l1 l2 -> fold_left f l1 a = fold_left f l2 a.
Proof.
intros A B f Hf a l1 l2 H; generalize a; elim H; clear H a l1 l2;
 simpl in |- *; auto.
intros a b l a0; rewrite Hf; auto.
intros l1 l2 l3 H H0 H1 H2 a; apply trans_equal with (1 := H0 a); auto.
Qed.

Section Permutation.
Variable A : Type.

#[local] Hint Constructors Permutation : core.
#[local] Hint Resolve Permutation_refl : core.
#[local] Hint Resolve Permutation_app : core.
#[local] Hint Resolve Permutation_app_swap : core.

(**
 Take a list and return the list of all pairs of an element of the
 list and the remaining list 
*)
Fixpoint split_one (l : list A) : list (A * list A) :=
  match l with
  | [] => []
  | a :: l1 =>
     (a, l1) :: map (fun p : A * list A => (fst p, a :: snd p)) (split_one l1)
  end.

(** The pairs of the list are a permutation *)
Theorem split_one_permutation :
 forall (a : A) (l1 l2 : list A),
 In (a, l1) (split_one l2) -> Permutation (a :: l1) l2.
Proof.
intros a l1 l2; generalize a l1; elim l2; clear a l1 l2; simpl in |- *; auto.
intros a l1 H1; case H1.
intros a l H a0 l1 [H0| H0].
injection H0; intros H1 H2; rewrite H2; rewrite H1; auto.
generalize H H0; elim (split_one l); simpl in |- *; auto.
intros H1 H2; case H2.
intros a1 l0 H1 H2 [H3| H3]; auto.
injection H3; intros H4 H5; (rewrite <- H4; rewrite <- H5).
apply Permutation_trans with (a :: fst a1 :: snd a1); auto.
apply perm_skip.
apply H2; auto.
case a1; simpl in |- *; auto.
Qed.

(** All elements of the list are there *)
Theorem split_one_in_ex :
 forall (a : A) (l1 : list A),
 In a l1 -> exists l2 : list A, In (a, l2) (split_one l1).
Proof.
intros a l1; elim l1; simpl in |- *; auto.
intros H; case H.
intros a0 l H [H0| H0]; auto.
exists l; left; apply f_equal2 with (f := pair (A:=A) (B:=list A)); auto.
case H; auto.
intros x H1; exists (a0 :: x); right; auto.
apply
 (in_map (fun p : A * list A => (fst p, a0 :: snd p)) (split_one l) (a, x));
 auto.
Qed.

(** An auxillary function to generate all permutations *) 
Fixpoint all_permutations_aux (l : list A) (n : nat) {struct n} :
 list (list A) :=
  match n with
  | O => [] :: []
  | S n1 =>
      flat_map
        (fun p : A * list A =>
         map (cons (fst p)) (all_permutations_aux (snd p) n1)) 
        (split_one l)
  end.

(** Generate all the permutations *)
Definition all_permutations (l : list A) :=
 all_permutations_aux l (length l).
 
Lemma all_permutations_aux_permutation :
  forall (n : nat) (l1 l2 : list A),
  n = length l2 -> In l1 (all_permutations_aux l2 n) -> Permutation l1 l2.
Proof.
intros n; elim n; simpl in |- *; auto.
intros l1 l2; case l2.
simpl in |- *; intros H0 [H1| H1].
rewrite <- H1; auto.
case H1.
simpl in |- *; intros; discriminate.
intros n0 H l1 l2 H0 H1.
case in_flat_map_ex with (1 := H1).
clear H1; intros x; case x; clear x; intros a1 l3 (H1, H2).
case (proj1 (in_map_iff _ _ _)) with (1 := H2).
simpl in |- *; intros y (H4, H3).
rewrite <- H4; auto.
apply Permutation_trans with (a1 :: l3); auto.
apply perm_skip; auto.
apply H with (2 := H3).
apply eq_add_S.
apply trans_equal with (1 := H0).
change (length l2 = length (a1 :: l3)) in |- *.
apply Permutation_length; auto.
apply Permutation_sym; apply split_one_permutation; auto.
apply split_one_permutation; auto.
Qed.

(** All the elements of the list are permutations *) 
Theorem all_permutations_permutation :
 forall l1 l2 : list A, In l1 (all_permutations l2) -> Permutation l1 l2.
Proof.
intros l1 l2 H; apply all_permutations_aux_permutation with (n := length l2);
 auto.
Qed.
 
Lemma permutation_all_permutations_aux :
  forall (n : nat) (l1 l2 : list A),
  n = length l2 -> Permutation l1 l2 -> In l1 (all_permutations_aux l2 n).
Proof.
intros n; elim n; simpl in |- *; auto.
intros l1 l2; case l2.
intros H H0; apply Permutation_sym in H0; rewrite Permutation_nil with (1 := H0); auto with datatypes.
simpl in |- *; intros; discriminate.
intros n0 H l1; case l1.
intros l2 H0 H1;
 rewrite Permutation_nil with (1 := H1) in H0;
 discriminate.
clear l1; intros a1 l1 l2 H1 H2.
case (split_one_in_ex a1 l2); auto.
apply Permutation_in with (1 := H2); auto with datatypes.
intros x H0.
apply in_flat_map_in with (b := (a1, x)); auto.
apply in_map; simpl in |- *.
apply H; auto.
apply eq_add_S.
apply trans_equal with (1 := H1).
change (length l2 = length (a1 :: x)) in |- *.
apply Permutation_length; auto.
apply Permutation_sym; apply split_one_permutation; auto.
apply Permutation_cons_inv with (a := a1).
apply Permutation_trans with (1 := H2).
apply Permutation_sym; apply split_one_permutation; auto.
Qed.

(** A permutation is in the list *) 
Theorem permutation_all_permutations :
 forall l1 l2 : list A, Permutation l1 l2 -> In l1 (all_permutations l2).
Proof.
intros l1 l2 H; unfold all_permutations in |- *;
 apply permutation_all_permutations_aux; auto.
Qed.

(** Permutation is decidable *) 
Definition Permutation_dec :
  (forall a b : A, {a = b} + {a <> b}) ->
  forall l1 l2 : list A, {Permutation l1 l2} + {~ Permutation l1 l2}.
Proof.
intros H l1 l2.
case (In_dec (list_eq_dec H) l1 (all_permutations l2)).
intros i; left; apply all_permutations_permutation; auto.
intros i; right; contradict i; apply permutation_all_permutations; auto.
Defined.

Theorem Permutation_transposition :
 forall (a b : A) l1 l2,
 Permutation (a :: l1 ++ b :: l2) (b :: l1 ++ a :: l2).
Proof.
intros a b l1 l2.
assert (H_eq: b :: l1 ++ a :: l2 = (b :: l1) ++ a :: l2) by reflexivity.
rewrite H_eq.
apply Permutation_cons_app.
apply Permutation_sym.
apply Permutation_cons_app; auto.
Qed.

End Permutation.

Arguments split_one [A].
Arguments all_permutations [A].
Arguments Permutation_dec [A].
