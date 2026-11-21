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
(* Modified by Theorem Labs, 2026-11: the logical path of one Require line changed (From Huffman to the logical path of the folder that holds this file), and 3 lines added (Unset Lia Cache, Unset Nia Cache, Unset Nra Cache). *)

(** * Weights of encodings

- Key definitions: [weight]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Import Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Huffman Require Export Code Frequency ISort UniqueKey.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Set Default Proof Using "Type".

Section Weight.
Variable A : Type.
Variable A_eq_dec : forall a b : A, {a = b} + {a <> b}.

Theorem fold_plus_split :
 forall (B : Type) (l : list B) (c : nat) (f : B -> nat),
 c + fold_left (fun (a : nat) (b : B) => a + f b) l 0 =
 fold_left (fun (a : nat) (b : B) => a + f b) l c.
Proof.
intros B l; elim l; simpl in |- *; auto.
intros a l0 H c f.
rewrite <- (H (f a)).
rewrite <- (H (c + f a)).
rewrite Nat.add_assoc; auto.
Qed.

Theorem fold_plus_permutation :
 forall (B : Type) (l1 l2 : list B) (c : nat) (f : B -> nat),
 Permutation l1 l2 ->
 fold_left (fun (a : nat) (b : B) => a + f b) l1 c =
 fold_left (fun (a : nat) (b : B) => a + f b) l2 c.
Proof.
intros B l1 l2 c f H; generalize c f; elim H; clear H l1 l2 c f;
 simpl in |- *; auto.
intros a b L c f; repeat rewrite <- Nat.add_assoc; rewrite (Nat.add_comm (f a));
 auto.
intros L1 L2 L3 H H0 H1 H2 c f; apply trans_equal with (1 := H0 c f); auto.
Qed.

Theorem length_encode_nId :
 forall a l1 l n,
 length (encode A_eq_dec ((a, l1) :: l) (id_list a n)) = n * length l1.
Proof.
intros a l1 l n; elim n; simpl in |- *; auto.
intros n0 H; case (A_eq_dec a a); auto.
intros e; rewrite app_length; rewrite H; auto.
intros H1; case H1; auto.
Qed.

Theorem frequency_length :
 forall (m : list A) (c : code A),
 unique_key c ->
 length (encode A_eq_dec c m) =
 fold_left
   (fun a b => a + number_of_occurrences A_eq_dec (fst b) m * length (snd b))
   c 0.
Proof.
intros m c; generalize m; elim c; clear c m; simpl in |- *; auto.
intros m; elim m; simpl in |- *; auto.
intros (a, l1) l Rec m H; simpl in |- *.
case (number_of_occurrences_permutation_ex A A_eq_dec m a);
 intros m1 (Hm1, Hm2).
rewrite
 Permutation_length
                    with
                    (1 := 
                      encode_permutation_val _ A_eq_dec _ _ ((a, l1) :: l) Hm1).
rewrite encode_app; auto.
rewrite app_length; auto.
rewrite length_encode_nId.
rewrite encode_cons_inv; auto.
rewrite Rec; simpl in |- *; auto.
rewrite <-
 fold_plus_split
                 with
                 (f := 
                   fun b : A * list bool =>
                   number_of_occurrences A_eq_dec (fst b) m * length (snd b))
                (c := number_of_occurrences A_eq_dec a m * length l1).
apply f_equal2 with (f := plus); auto.
cut (forall l2, ~ In (a, l2) l).
elim l; simpl in |- *; auto.
intros (a2, l2) l3; simpl in |- *; intros Rec1 H4.
rewrite <-
 fold_plus_split
                 with
                 (c := number_of_occurrences A_eq_dec a2 m1 * length l2)
                (f := 
                  fun b : A * list bool =>
                  number_of_occurrences A_eq_dec (fst b) m1 * length (snd b)).
rewrite <-
 fold_plus_split
                 with
                 (c := number_of_occurrences A_eq_dec a2 m * length l2)
                (f := 
                  fun b : A * list bool =>
                  number_of_occurrences A_eq_dec (fst b) m * length (snd b)).
apply f_equal2 with (f := plus); auto.
2: apply Rec1; auto.
2: intros l0; red in |- *; intros H0; case (H4 l0); auto.
2: intros l2; red in |- *; intros H0;
    case unique_key_in with (1 := H) (a := a) (b2 := l2); 
    auto.
2: apply unique_key_inv with (1 := H); auto.
apply f_equal2 with (f := mult); auto.
apply
 trans_equal
  with
    (2 := number_of_occurrences_permutation _ A_eq_dec _ _ a2
            (Permutation_sym Hm1)).
rewrite number_of_occurrences_app.
replace
 (number_of_occurrences A_eq_dec a2
    (id_list a (number_of_occurrences A_eq_dec a m))) with 0; 
 auto.
cut (a2 <> a).
elim (number_of_occurrences A_eq_dec a m); simpl in |- *; auto.
intros n H0 H1; case (A_eq_dec a2 a); simpl in |- *; auto.
intros e; case H1; auto.
red in |- *; intros H0; case (H4 l2); left;
 apply f_equal2 with (f := pair (A:=A) (B:=list bool)); 
 auto.
Qed.

Definition weight m c := length (encode A_eq_dec c m).

Theorem weight_permutation :
 forall m c1 c2,
 unique_prefix c1 -> Permutation c1 c2 -> weight m c1 = weight m c2.
Proof.
intros m c1 c2 H H0; unfold weight in |- *.
apply f_equal with (f := length (A:=bool)).
apply encode_permutation; auto.
Qed.

Definition restrict_code (m : list A) (c : code A) : 
  code A :=
  map (fun x => (fst x, find_code A_eq_dec (fst x) c))
    (frequency_list A_eq_dec m).

Theorem NoDup_unique_key :
 forall (A B : Type) (l : list (A * B)),
 NoDup (map (fst (B:=_)) l) -> unique_key l.
Proof.
intros AA BB l; elim l; simpl in |- *; auto.
intros a; case a.
intros a0 b l0 H H0; apply unique_key_cons; auto.
intros b0; red in |- *; intros H1; absurd (In a0 (map (fst (B:=_)) l0)); auto.
inversion H0; auto.
change (In (fst (a0, b0)) (map (fst (B:=_)) l0)) in |- *; auto with datatypes.
apply in_map; auto.
apply H; apply NoDup_cons_iff with (1 := H0); auto.
Qed.
 
Theorem restrict_code_unique_key :
 forall (m : list A) (c : code A), unique_key (restrict_code m c).
Proof.
intros m c; apply NoDup_unique_key.
unfold restrict_code in |- *.
replace
 (map (fst (B:=_))
    (map (fun x : A * nat => (fst x, find_code A_eq_dec (fst x) c))
       (frequency_list A_eq_dec m))) with
 (map (fst (B:=_)) (frequency_list A_eq_dec m)).
apply unique_key_NoDup; auto.
elim (frequency_list A_eq_dec m); simpl in |- *; auto with datatypes.
intros a l H; apply f_equal2 with (f := cons (A:=A)); auto.
Qed.

Theorem restrict_code_in :
 forall (m : list A) (a : A) (c : code A),
 In a m -> find_code A_eq_dec a c = find_code A_eq_dec a (restrict_code m c).
Proof.
intros m a c H.
apply sym_equal; apply find_code_correct2; auto.
apply restrict_code_unique_key.
generalize (in_frequency_map _ A_eq_dec m a H).
unfold restrict_code in |- *; elim (frequency_list A_eq_dec m); simpl in |- *;
 auto with datatypes.
intros a0; case a0; simpl in |- *; auto with datatypes.
intros a1 n l H0 [H1| H1]; try rewrite H1; auto.
Qed.

Theorem restrict_code_encode_length_inc :
 forall (m m1 : list A) (c : code A),
 incl m1 m -> encode A_eq_dec c m1 = encode A_eq_dec (restrict_code m c) m1.
Proof.
intros m m1 c; elim m1; simpl in |- *; auto.
intros a l H H0.
apply f_equal2 with (f := app (A:=bool)); auto with datatypes.
apply restrict_code_in; auto with datatypes.
apply H; apply incl_tran with (2 := H0); auto with datatypes.
Qed.

Theorem restrict_code_encode_length :
 forall (m : list A) (c : code A),
 encode A_eq_dec c m = encode A_eq_dec (restrict_code m c) m.
Proof.
intros m c; apply restrict_code_encode_length_inc; auto with datatypes.
Qed.

End Weight.
Arguments weight [A].
Arguments restrict_code [A].
