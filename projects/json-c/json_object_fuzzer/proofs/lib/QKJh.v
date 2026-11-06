(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)


From Stdlib Require Import ZArith List Bool.
From stdpp Require Import gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive nref : Type := NNull | NRun (i : N) | NSent.
Inductive pref : Type := PNull | PNode (i : N).

Definition nref_eqb (a b : nref) : bool :=
match a, b with
| NNull, NNull => true
| NSent, NSent => true
| NRun i, NRun j => N.eqb i j
| _, _ => false
end.
Definition pref_eqb (a b : pref) : bool :=
match a, b with
| PNull, PNull => true
| PNode i, PNode j => N.eqb i j
| _, _ => false
end.

Lemma nref_eqb_eq : forall a b, nref_eqb a b = true <-> a = b.
Proof.
intros [|i|] [|j|]; cbn; split; intro H; try discriminate; try reflexivity.
- apply N.eqb_eq in H. subst. reflexivity.
- inversion H. subst. apply N.eqb_refl.
Qed.
Lemma pref_eqb_eq : forall a b, pref_eqb a b = true <-> a = b.
Proof.
intros [|i] [|j]; cbn; split; intro H; try discriminate; try reflexivity.
- apply N.eqb_eq in H. subst. reflexivity.
- inversion H. subst. apply N.eqb_refl.
Qed.

#[global] Instance nref_eq_dec : EqDecision nref.
Proof. intros a b. destruct (nref_eqb a b) eqn:E.
- left. apply nref_eqb_eq. exact E.
- right. intro H. apply nref_eqb_eq in H. congruence.
Defined.
#[global] Instance pref_eq_dec : EqDecision pref.
Proof. intros a b. destruct (pref_eqb a b) eqn:E.
- left. apply pref_eqb_eq. exact E.
- right. intro H. apply pref_eqb_eq in H. congruence.
Defined.

Section FribidiState.
Context {ptr : Type}.

Record run_rec : Type := mkRun {
r_blk   : ptr;
r_prev  : nref;
r_next  : nref;
r_pos   : Z;
r_len   : Z;
r_type  : option Z;
r_level : Z;
r_iso   : Z;
r_btype : option Z;
r_previ : nref;
r_nexti : nref
}.

Record pnode_rec : Type := mkPN {
pn_blk   : ptr;
pn_open  : nref;
pn_close : nref;
pn_next  : pref
}.

Record brow : Type := mkRow {
row_blk   : ptr;
row_cells : list (option nref)
}.

Record FSt : Type := mkF {
f_runs   : gmap N run_rec;
f_pnodes : gmap N pnode_rec;
f_rows   : gmap N brow;
f_next   : N;
f_types  : list Z;
f_btypes : list Z;
f_levels : list Z
}.

Definition fst_init : FSt := mkF ∅ ∅ ∅ 0%N [] [] [].

End FribidiState.

Arguments run_rec ptr : clear implicits.
Arguments pnode_rec ptr : clear implicits.
Arguments brow ptr : clear implicits.
Arguments FSt ptr : clear implicits.
