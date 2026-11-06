(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.

Set Implicit Arguments.

Section PMap.
  Variable A : Type.

  Inductive pmap : Type :=
  | PLeaf : pmap
  | PNode : pmap -> option A -> pmap -> pmap.

  Definition pm_empty : pmap := PLeaf.

  Fixpoint pm_get (k : positive) (m : pmap) {struct m} : option A :=
    match m with
    | PLeaf => None
    | PNode l o r =>
        match k with
        | xH => o
        | xO k' => pm_get k' l
        | xI k' => pm_get k' r
        end
    end.

  Fixpoint pm_single (k : positive) (v : A) : pmap :=
    match k with
    | xH => PNode PLeaf (Some v) PLeaf
    | xO k' => PNode (pm_single k' v) None PLeaf
    | xI k' => PNode PLeaf None (pm_single k' v)
    end.

  Fixpoint pm_set (k : positive) (v : A) (m : pmap) {struct m} : pmap :=
    match m with
    | PLeaf => pm_single k v
    | PNode l o r =>
        match k with
        | xH => PNode l (Some v) r
        | xO k' => PNode (pm_set k' v l) o r
        | xI k' => PNode l o (pm_set k' v r)
        end
    end.

  Fixpoint pm_remove (k : positive) (m : pmap) {struct m} : pmap :=
    match m with
    | PLeaf => PLeaf
    | PNode l o r =>
        match k with
        | xH => PNode l None r
        | xO k' => PNode (pm_remove k' l) o r
        | xI k' => PNode l o (pm_remove k' r)
        end
    end.

  (* [comment removed for export] *)
  Fixpoint pm_xelements (m : pmap) (f : positive -> positive) (acc : list (positive * A))
    : list (positive * A) :=
    match m with
    | PLeaf => acc
    | PNode l o r =>
        let acc1 := pm_xelements r (fun p => f (xI p)) acc in
        let acc2 := match o with Some v => (f xH, v) :: acc1 | None => acc1 end in
        pm_xelements l (fun p => f (xO p)) acc2
    end.

  Definition pm_elements (m : pmap) : list (positive * A) := pm_xelements m (fun p => p) [].

  Definition pm_fold (B : Type) (g : B -> positive -> A -> B) (m : pmap) (b : B) : B :=
    fold_left (fun acc kv => g acc (fst kv) (snd kv)) (pm_elements m) b.

  (* [comment removed for export] *)
  Fixpoint pm_size (m : pmap) : nat :=
    match m with
    | PLeaf => O
    | PNode l o r => (match o with Some _ => S O | None => O end) + pm_size l + pm_size r
    end.

  (* [comment removed for export] *)
  Lemma pm_get_empty k : pm_get k pm_empty = None.
  Proof. reflexivity. Qed.

  Lemma pm_get_single_same k v : pm_get k (pm_single k v) = Some v.
  Proof. induction k; simpl; auto. Qed.

  Lemma pm_get_single_other k k' v : k <> k' -> pm_get k' (pm_single k v) = None.
  Proof.
    revert k'. induction k; intros k' Hne; destruct k'; simpl; auto; try congruence.
    - apply IHk. congruence.
    - apply IHk. congruence.
  Qed.

  Lemma pm_get_set_same k v m : pm_get k (pm_set k v m) = Some v.
  Proof.
    revert k. induction m; intros k.
    - simpl. apply pm_get_single_same.
    - destruct k; simpl; auto.
  Qed.

  Lemma pm_get_set_other k k' v m : k <> k' -> pm_get k' (pm_set k v m) = pm_get k' m.
  Proof.
    revert k k'. induction m; intros k k' Hne.
    - simpl. rewrite pm_get_single_other; auto.
    - destruct k, k'; simpl; auto; try congruence.
      + apply IHm2. congruence.
      + apply IHm1. congruence.
  Qed.

  Lemma pm_get_set k k' v m :
    pm_get k' (pm_set k v m) = if Pos.eqb k' k then Some v else pm_get k' m.
  Proof.
    destruct (Pos.eqb_spec k' k).
    - subst. apply pm_get_set_same.
    - apply pm_get_set_other. congruence.
  Qed.

  Lemma pm_get_remove_same k m : pm_get k (pm_remove k m) = None.
  Proof.
    revert k. induction m; intros k; simpl; auto. destruct k; simpl; auto.
  Qed.

  Lemma pm_get_remove_other k k' m : k <> k' -> pm_get k' (pm_remove k m) = pm_get k' m.
  Proof.
    revert k k'. induction m; intros k k' Hne; simpl; auto.
    destruct k, k'; simpl; auto; try congruence.
    - apply IHm2. congruence.
    - apply IHm1. congruence.
  Qed.

  Lemma pm_get_remove k k' m :
    pm_get k' (pm_remove k m) = if Pos.eqb k' k then None else pm_get k' m.
  Proof.
    destruct (Pos.eqb_spec k' k).
    - subst. apply pm_get_remove_same.
    - apply pm_get_remove_other. congruence.
  Qed.

  Lemma pm_xelements_spec m : forall f acc kv,
    In kv (pm_xelements m f acc) <->
    (exists p, fst kv = f p /\ pm_get p m = Some (snd kv)) \/ In kv acc.
  Proof.
    induction m as [|l IHl o r IHr]; intros f acc kv; simpl.
    - split.
      + intros H. right; exact H.
      + intros [[p [_ H]]|H]; [discriminate|exact H].
    - rewrite IHl. split.
      + intros [[p [H1 H2]]|H].
        * left. exists (xO p). simpl. auto.
        * assert (H' : (o = Some (snd kv) /\ fst kv = f xH) \/ In kv (pm_xelements r (fun p => f (xI p)) acc)).
          { destruct o as [v|].
            - destruct H as [H|H].
              + left. destruct kv as [k1 v1]. simpl in *. inversion H; subst. auto.
              + right; exact H.
            - right; exact H. }
          destruct H' as [[Ho Hk]|Hin].
          -- left. exists xH. simpl. auto.
          -- rewrite IHr in Hin. destruct Hin as [[p [H1 H2]]|Hacc].
             ++ left. exists (xI p). simpl; auto.
             ++ right; exact Hacc.
      + intros [[p [H1 H2]]|H].
        * destruct p as [p|p|]; simpl in H2.
          -- right.
             assert (Hin : In kv (pm_xelements r (fun p0 : positive => f (xI p0)) acc)).
             { rewrite IHr. left. exists p. auto. }
             destruct o; [right|]; exact Hin.
          -- left. exists p. auto.
          -- right. subst o. left. destruct kv as [k1 v1]; simpl in *. congruence.
        * right.
          assert (Hin : In kv (pm_xelements r (fun p0 : positive => f (xI p0)) acc)).
          { rewrite IHr. right. exact H. }
          destruct o; [right|]; exact Hin.
  Qed.

  Lemma pm_elements_correct m k v :
    In (k, v) (pm_elements m) <-> pm_get k m = Some v.
  Proof.
    unfold pm_elements. rewrite pm_xelements_spec. simpl. split.
    - intros [[p [H1 H2]]|H]; [subst; exact H2 | destruct H].
    - intros H. left. exists k. auto.
  Qed.

  Lemma pm_elements_complete m k v :
    pm_get k m = Some v -> In (k, v) (pm_elements m).
  Proof. intros; now apply pm_elements_correct. Qed.

  Lemma pm_elements_sound m k v :
    In (k, v) (pm_elements m) -> pm_get k m = Some v.
  Proof. intros; now apply pm_elements_correct. Qed.

  (* [comment removed for export] *)
  Definition pm_forallb (f : positive -> A -> bool) (m : pmap) : bool :=
    forallb (fun kv => f (fst kv) (snd kv)) (pm_elements m).

  Lemma pm_forallb_sound f m :
    pm_forallb f m = true -> forall k v, pm_get k m = Some v -> f k v = true.
  Proof.
    unfold pm_forallb. intros H k v Hg.
    rewrite forallb_forall in H.
    apply pm_elements_complete in Hg. exact (H _ Hg).
  Qed.

End PMap.

Arguments pm_empty {A}.
Arguments PLeaf {A}.

(* [comment removed for export] *)
Fixpoint pm_map {A B : Type} (f : A -> B) (m : pmap A) : pmap B :=
  match m with
  | PLeaf => PLeaf
  | PNode l o r => PNode (pm_map f l) (match o with Some v => Some (f v) | None => None end) (pm_map f r)
  end.

Lemma pm_get_map {A B} (f : A -> B) m k :
  pm_get k (pm_map f m) = match pm_get k m with Some v => Some (f v) | None => None end.
Proof.
  revert k; induction m; intros k; simpl; auto. destruct k; simpl; auto.
Qed.

(* [comment removed for export] *)
Definition pm_mem {A} (k : positive) (m : pmap A) : bool :=
  match pm_get k m with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition pm_of_list {A} (l : list (positive * A)) : pmap A :=
  fold_left (fun m kv => pm_set (fst kv) (snd kv) m) l pm_empty.

Fixpoint forallb_l {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with [] => true | x :: t => if f x then forallb_l f t else false end.
Fixpoint existsb_l {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | x :: t => if f x then true else existsb_l f t end.
Lemma forallb_l_eq {A : Type} (f : A -> bool) (l : list A) : forallb_l f l = forallb f l.
Proof. induction l as [|x t IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma existsb_l_eq {A : Type} (f : A -> bool) (l : list A) : existsb_l f l = existsb f l.
Proof. induction l as [|x t IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.
Definition pm_forallb_l {A : Type} (f : positive -> A -> bool) (m : pmap A) : bool :=
  forallb_l (fun kv => f (fst kv) (snd kv)) (pm_elements m).
Lemma pm_forallb_l_eq {A : Type} (f : positive -> A -> bool) (m : pmap A) : pm_forallb_l f m = pm_forallb f m.
Proof. unfold pm_forallb_l, pm_forallb. apply forallb_l_eq. Qed.

(* [comment removed for export] *)
Lemma if_andb (a b : bool) : (if a then b else false) = (a && b). Proof. reflexivity. Qed.
Lemma if_orb (a b : bool) : (if a then true else b) = (a || b). Proof. reflexivity. Qed.
