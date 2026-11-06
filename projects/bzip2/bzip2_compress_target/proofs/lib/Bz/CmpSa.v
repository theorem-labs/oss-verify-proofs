(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require LiaTuning.
From Ltac2 Require Ltac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac sa_nlit n := lazymatch n with O => constr:(tt) | S _ => constr:(tt) | Z.to_nat ?z => sa_closed z end
with sa_closed z :=
  lazymatch z with
  | Z0 => constr:(tt) | Zpos _ => constr:(tt) | Zneg _ => constr:(tt)
  | Z.add ?a ?b => let _ := sa_closed a in sa_closed b | Z.sub ?a ?b => let _ := sa_closed a in sa_closed b
  | Z.mul ?a ?b => let _ := sa_closed a in sa_closed b | Z.opp ?a => sa_closed a | Z.pow ?a ?b => let _ := sa_closed a in sa_closed b
  | Z.of_nat ?n => sa_nlit n
  end.
(* [comment removed for export] *)
Ltac sa_memb x L := lazymatch L with (?y, ?r) => lazymatch y with x => constr:(true) | _ => sa_memb x r end | _ => constr:(false) end.
Ltac sa_add x L := let b := sa_memb x L in lazymatch b with true => L | false => constr:((x, L)) end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sa_atoms_e acc e :=
  lazymatch e with
  | Z.add ?a ?b => let acc := sa_atoms_e acc a in sa_atoms_e acc b
  | Z.sub ?a ?b => let acc := sa_atoms_e acc a in sa_atoms_e acc b
  | Z.mul ?a ?b => let acc := sa_atoms_e acc a in sa_atoms_e acc b
  | Z.opp ?a => sa_atoms_e acc a
  | Z0 => acc | Zpos _ => acc | Zneg _ => acc
  | Z.pow _ _ => let _ := sa_closed e in acc
  | Z.of_nat _ => let _ := sa_closed e in acc
  | Z.div _ _ => fail | Z.modulo _ _ => fail | Z.quot _ _ => fail | Z.rem _ _ => fail | Z.to_nat _ => fail
  | Z.of_N _ => fail | Z.to_N _ => fail | Z.max _ _ => fail | Z.min _ _ => fail | Z.abs _ => fail | Z.sgn _ => fail | Z.succ _ => fail | Z.pred _ => fail
  | _ => sa_add e acc
  end.
Ltac sa_atoms_p acc P :=
  lazymatch P with
  | ?A /\ ?B => let acc := sa_atoms_p acc A in sa_atoms_p acc B
  | Z.le ?a ?b => let acc := sa_atoms_e acc a in sa_atoms_e acc b | Z.lt ?a ?b => let acc := sa_atoms_e acc a in sa_atoms_e acc b
  | Z.ge ?a ?b => let acc := sa_atoms_e acc a in sa_atoms_e acc b | Z.gt ?a ?b => let acc := sa_atoms_e acc a in sa_atoms_e acc b
  | @eq Z ?a ?b => let acc := sa_atoms_e acc a in sa_atoms_e acc b
  end.
(* [comment removed for export] *)
Ltac sa_lin_e L e :=
  lazymatch e with
  | Z.add ?a ?b => sa_lin_e L a; sa_lin_e L b | Z.sub ?a ?b => sa_lin_e L a; sa_lin_e L b
  | Z.mul ?a ?b => sa_lin_e L a; sa_lin_e L b | Z.opp ?a => sa_lin_e L a
  | _ => let b := sa_memb e L in lazymatch b with true => idtac | false => let _ := sa_closed e in idtac end
  end.
Ltac sa_lin L P :=
  lazymatch P with
  | ?A /\ ?B => sa_lin L A; sa_lin L B
  | Z.le ?a ?b => sa_lin_e L a; sa_lin_e L b | Z.lt ?a ?b => sa_lin_e L a; sa_lin_e L b
  | Z.ge ?a ?b => sa_lin_e L a; sa_lin_e L b | Z.gt ?a ?b => sa_lin_e L a; sa_lin_e L b
  | @eq Z ?a ?b => sa_lin_e L a; sa_lin_e L b
  end.
(* [comment removed for export] *)
Ltac sa_noleaf_e L e :=
  lazymatch e with
  | Z.add ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b | Z.sub ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b
  | Z.mul ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b | Z.opp ?a => sa_noleaf_e L a
  | Z.div ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b | Z.modulo ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b
  | Z.quot ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b | Z.rem ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b
  | Z.max ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b | Z.min ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b
  | Z.abs ?a => sa_noleaf_e L a | Z.sgn ?a => sa_noleaf_e L a | Z.succ ?a => sa_noleaf_e L a | Z.pred ?a => sa_noleaf_e L a
  | Z.pow ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b
  | Z.of_nat ?n => sa_nomention L n | Z.of_N ?n => sa_nomention L n | Z.to_nat ?n => fail | Z.to_N ?n => fail
  | _ => let b := sa_memb e L in lazymatch b with true => fail | false => idtac end
  end
with sa_nomention L n := lazymatch L with (?y, ?r) => lazymatch n with context [y] => fail | _ => sa_nomention r n end | _ => idtac end.
Ltac sa_noleaf L P :=
  lazymatch P with
  | ?A /\ ?B => sa_noleaf L A; sa_noleaf L B | ?A \/ ?B => sa_noleaf L A; sa_noleaf L B
  | ~ ?A => sa_noleaf L A | ?A <-> ?B => sa_noleaf L A; sa_noleaf L B
  | Z.le ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b | Z.lt ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b
  | Z.ge ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b | Z.gt ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b
  | @eq Z ?a ?b => sa_noleaf_e L a; sa_noleaf_e L b
  | @eq nat ?a ?b => sa_nomention L a; sa_nomention L b | @eq N ?a ?b => sa_nomention L a; sa_nomention L b
  | @eq bool ?a ?b => sa_nomention L a; sa_nomention L b | @eq positive ?a ?b => sa_nomention L a; sa_nomention L b
  | Peano.le ?a ?b => sa_nomention L a; sa_nomention L b | Peano.lt ?a ?b => sa_nomention L a; sa_nomention L b
  | Z.divide ?a ?b => sa_nomention L a; sa_nomention L b
  | forall _ : ?A, ?B => lazymatch type of A with Prop => sa_noleaf L A; sa_noleaf L B | _ => sa_nomention L P end
  | _ => idtac                                       (* [comment removed for export] *)
  end.

Module SA.
  Import Ltac2.
  Ltac2 clear_local_props () : unit :=
    let ids := List.map_filter (fun (id, body, ty) =>
                 match body with
                 | Some _ => None
                 | None => if LiaTuning.zt_is_local id then (if LiaTuning.zt_is_prop ty then Some id else None) else None
                 end) (Control.hyps ()) in
    match ids with [] => () | _ :: _ => Std.clear ids end.
End SA.
Ltac sa_clear_local := ltac2:(Control.enter SA.clear_local_props).

(* [comment removed for export] *)
Ltac sa_premises L :=
  lazymatch goal with
  | |- ?P -> _ =>
      lazymatch type of P with Prop => idtac end;
      first [ sa_lin L P; let H := fresh "SAk" in intro H; sa_premises L; revert H
            | sa_noleaf L P; let H := fresh "SAd" in intro H; clear H; sa_premises L ]
  | |- forall _, _ => fail                          (* [comment removed for export] *)
  | |- let _ := _ in _ => fail
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac sa_app A B := lazymatch A with (?x, ?r) => let t := sa_app r B in constr:((x, t)) | _ => B end.
Ltac sa_gen todo Zs :=
  lazymatch todo with
  | (?a, ?r) =>
      tryif (is_var a; match goal with x := _ |- _ => constr_eq x a end) then fail else idtac;      (* [comment removed for export] *)
      generalize dependent a;
      let z := fresh "sa_z" in intro z;
      let Zs' := constr:((z, Zs)) in
      let L := sa_app Zs' r in
      sa_premises L; sa_gen r Zs'; revert z
  | _ => sa_clear_local
  end.
Ltac sa_no_nesting L := lazymatch L with
  | (?a, ?r) => lazymatch r with context [a] => fail | _ => idtac end;
                let rec chk s := lazymatch s with (?b, ?t) => lazymatch a with context [b] => fail | _ => chk t end | _ => idtac end in chk r;
                sa_no_nesting r
  | _ => idtac end.
Ltac sa_prepare :=
  lazymatch goal with |- ?G =>
    tryif has_evar G then fail else idtac;
    let L := sa_atoms_p tt G in
    lazymatch L with tt => fail | (_, tt) => idtac | (_, (_, tt)) => idtac | (_, (_, (_, tt))) => idtac | _ => fail end;
    sa_no_nesting L;
    sa_gen L tt
  end.

Section SelfTest.
Variable f : Z -> Z. Variable u : Z. Hypothesis Hu : 0 <= u < 4294967296. Hypothesis Hv : 0 <= f 3 < 100.
Goal forall (x y r1 r2 : Z) (P : Z -> Prop), 0 <= f x < 10 -> P (f x) -> (y <= 5 \/ 0 <= f (f x)) -> r1 + 0 <= r2 -> r2 <= r1 -> True.
Proof.
  intros x y r1 r2 P H1 H2 H3 H4 H5.
  assert (0 <= f x < 2^32) by (sa_prepare; lia).
  assert (0 <= u * 256 < 2^40) by (sa_prepare; lia).
  assert (r1 = r2) by (sa_prepare; lia).
  assert (f x + Z.of_nat (Z.to_nat 1548) <= f x + 2000) by (sa_prepare; lia).
  assert_fails (assert (0 <= u < 2^31) by (sa_prepare; lia)).
  assert_succeeds (assert (0 <= u < 2^31) by (sa_prepare; shelve)).          (* [comment removed for export] *)
  assert_succeeds (assert (- 2^31 <= f y < 2^31) by (sa_prepare; shelve)).   (* [comment removed for export] *)
  assert_fails (assert (r1 = y) by (sa_prepare; shelve)).                  (* [comment removed for export] *)
  assert_succeeds (assert (x = u) by (sa_prepare; shelve)).
  assert_fails (assert (0 <= x + y + r1 + r2 < 7) by (sa_prepare; shelve)).  (* [comment removed for export] *)
  exact I.
Qed.
Goal forall (x y : Z), 0 <= x + y < 10 -> 0 <= y -> True.
Proof. intros x y H1 H2. assert_fails (assert (0 <= x < 2^32) by (sa_prepare; shelve)). exact I. Qed.   (* [comment removed for export] *)
Goal forall a : Z, 0 <= a < 5 -> True.
Proof. intros a H. set (idx := a + 1). assert (0 <= idx < 7) by (first [ tryif sa_prepare then fail 2 else lia ]). exact I. Qed.
Goal forall a b : Z, a < b -> b < a -> False.
Proof. intros a b H1 H2. Fail sa_prepare. lia. Qed.
End SelfTest.
