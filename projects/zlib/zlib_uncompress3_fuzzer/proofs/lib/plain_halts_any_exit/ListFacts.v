(** * Common.ListFacts — designated home for generic list facts.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT and domain-free: pure [firstn]/[skipn]/[nth]/[In]
    facts with no byte/word/RISC-V content.

    This file is the single canonical home for the generic list lemmas
    ([firstn_S_nth] for the snoc-peel fact; [In_firstn] for
    firstn-membership; plus [skipn_cons_nth] and [firstn_all_len]).  Each
    fact is stated ONCE here, in the development's stdlib vocabulary
    ([firstn]/[skipn]/[nth]/[In]) — which is what every use site speaks —
    and proved by DEFERRING to stdpp's list library ([take_S_r],
    [drop_S], [firstn_all], [elem_of_take], ...) rather than by fresh
    induction wherever stdpp already has the fact.  In current stdpp
    [take]/[drop] are notations for [firstn]/[skipn], so the bridge to the
    stdlib statements below is definitional.

    A broader, development-wide switch to stdpp idioms (take/drop/lookup
    everywhere) is deliberately DEFERRED; this file only introduces the
    stdpp dependency locally, for the facts it hosts.

    To keep this module at the bottom of the Common dependency DAG it
    imports NO other Common file — only Stdlib and stdpp's list library. *)

From Stdlib Require Import List Lia.
From stdpp Require Import list.
Import ListNotations.

(** Peel the last element off a [firstn (S i)]: canonical form of the
    per-example [firstn_S_nth] / [firstn_snoc] / [firstn_snoc_nth].
    Polymorphic with an explicit default [d]; the byte-specialised sites
    (default [Z_to_bv 8 0]) are instances.  Argument order [(A l i d)]
    matches the existing [firstn_S_nth] call sites. *)
Lemma firstn_S_nth (A : Type) (l : list A) (i : nat) (d : A) :
  (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros Hi.
  pose proof (lookup_lt_is_Some_2 l i Hi) as [x Hx].
  rewrite (nth_lookup l i d), Hx. cbn.
  exact (take_S_r _ _ _ Hx).
Qed.

(** Membership in a prefix implies membership in the whole list: canonical
    form of the per-example [In_firstn] / [In_firstn_incl]. *)
Lemma In_firstn {A} (x : A) (n : nat) (l : list A) :
  In x (firstn n l) -> In x l.
Proof.
  intros H. apply list_elem_of_In. apply list_elem_of_In in H.
  apply elem_of_take in H as (i & Hl & _).
  eapply list_elem_of_lookup_2. exact Hl.
Qed.

(** Expose the head of a [skipn i]: canonical form of the per-example
    [skipn_cons_nth].  Polymorphic with an explicit default [d]; argument
    order [(l i d)] matches Common's neighbouring [CatExec.skipn_nth].
    The byte-specialised sites (default [Z_to_bv 8 0]) supply that default
    explicitly. *)
Lemma skipn_cons_nth {A} (l : list A) (i : nat) (d : A) :
  (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros Hi.
  pose proof (lookup_lt_is_Some_2 l i Hi) as [x Hx].
  rewrite (nth_lookup l i d), Hx. cbn.
  exact (drop_S l x i Hx).
Qed.

(** [firstn] of a list's full length is the list: canonical form of the
    per-example [firstn_all_len].  This is exactly stdlib/stdpp
    [firstn_all]; kept under its own name for the existing call sites. *)
Lemma firstn_all_len {A} (l : list A) : firstn (length l) l = l.
Proof. apply firstn_all. Qed.
