(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths and module names changed; 39 of its 62 lines of code are new or changed and 549 lines of the source are left out. *)
(* Theorem Labs, 2026-10: index-free membership in the start-up constant tables (Tfib_const_abs and Tfib_const_sym of
   either image, or any closed list of acell). A positional proof `nth_error_In T k` breaks each time the table is
   regenerated, so a reader names the row only: `in_const_tbl` proves `In row T` from
   `existsb (row_eqb row) T = true`, which vm_compute decides on a closed goal (the tactic clears the context and
   refuses a goal that still names a hypothesis, a section variable or an evar), and existsb_row_In turns the boolean
   into `In`. Image-generic: it depends on YG0f's acell only, and the table is the goal's own argument. *)
(* Alternative measured: a Theorem Labs lane's index-search tactic in_const_abs (a working branch 8d49db69171,
   proofs/libreac/fuzz_disco/lib/Reusable/YD2l.v:48). On ctrl's 2135-row tables it takes 0.522 s (A) / 0.373 s (B) per
   use at row 625 and 4.093 s at row 2134; in_const_tbl takes 0.001 s at each row. Timing file:
   TimeCI.out. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0f.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint ci_aexp_eqb (a b : aexp) : bool :=
match a, b with
| ANum x, ANum y => x =? y
| ASp x, ASp y => x =? y | AQ x, AQ y => x =? y | AT x, AT y => x =? y | AC x, AC y => x =? y
| AF x, AF y => x =? y | ANB x, ANB y => x =? y | ASB x, ASB y => x =? y
| ASec r x, ASec s y => Nat.eqb r s && (x =? y)
| ATop x, ATop y => x =? y | ATsd x, ATsd y => x =? y | AStk x, AStk y => x =? y
| AInst x, AInst y => x =? y | ADepot x, ADepot y => x =? y | AStore x, AStore y => x =? y
| ATp x, ATp y => x =? y | AIal x, AIal y => x =? y | AD x, AD y => x =? y
| ASh a', ASh b' => ci_aexp_eqb a' b'
| _, _ => false
end.
Lemma ci_aexp_eqb_eq : forall a b, ci_aexp_eqb a b = true -> a = b.
Proof.
induction a; destruct b; cbn; intros H; try discriminate H;
repeat match goal with
| E : (_ && _)%bool = true |- _ => apply andb_prop in E as [? ?]
| E : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in E
| E : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in E
end; subst; try reflexivity.
f_equal. exact (IHa _ H).
Qed.
Definition ci_aval_eqb (x y : aval) : bool :=
match x, y with
| AV a, AV b => ci_aexp_eqb a b
| AVmask m v, AVmask m' v' => (m =? m') && (v =? v')
| _, _ => false
end.
Lemma ci_aval_eqb_eq : forall x y, ci_aval_eqb x y = true -> x = y.
Proof.
intros [a|m v] [b|m' v'] H; cbn in H; try discriminate H.
- f_equal. exact (ci_aexp_eqb_eq a b H).
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Definition row_eqb (x y : acell) : bool :=
ci_aexp_eqb (c_at x) (c_at y) && Nat.eqb (c_w x) (c_w y) && ci_aval_eqb (c_val x) (c_val y).
Lemma row_eqb_eq : forall x y, row_eqb x y = true -> x = y.
Proof.
intros [a w v] [b w' v'] H. unfold row_eqb in H. cbn [c_at c_w c_val] in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply ci_aexp_eqb_eq in H1. apply Nat.eqb_eq in H2. apply ci_aval_eqb_eq in H3. subst. reflexivity.
Qed.
Lemma existsb_row_In : forall row t, existsb (row_eqb row) t = true -> In row t.
Proof.
intros row t H. apply existsb_exists in H as (x & Hx & E). apply row_eqb_eq in E. subst x. exact Hx.
Qed.
Ltac in_const_tbl :=
lazymatch goal with
| |- In ?row ?t =>
  tryif has_evar row then fail 0 "in_const_tbl: the row has an evar; give the row in full" else
  tryif has_evar t then fail 0 "in_const_tbl: the table has an evar" else
  apply (existsb_row_In row t); clear;
  lazymatch goal with
  | H : _ |- _ => fail 0 "in_const_tbl: the goal is not closed, it names" H
  | |- _ => vm_compute; reflexivity
  end
| |- _ => fail 0 "in_const_tbl: the goal is not of the form In row table"
end.
