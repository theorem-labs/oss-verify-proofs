(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia Zify.
From Stdlib Require List.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control List Std.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 rec has_arith (t : constr) : bool :=
  lazy_match! t with
  | @eq ?ty _ _ => lazy_match! ty with Z => true | nat => true | positive => true | N => true | _ => false end
  | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
  | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
  | N.le _ _ => true | N.lt _ _ => true | Pos.le _ _ => true | Pos.lt _ _ => true | Z.divide _ _ => true
  | False => true
  | ?a /\ ?b => if has_arith a then true else has_arith b
  | ?a \/ ?b => if has_arith a then true else has_arith b
  | ?a <-> ?b => if has_arith a then true else has_arith b
  | ~ ?a => has_arith a
  | ?a -> ?b => if has_arith a then true else has_arith b
  | _ => false
  end.

Ltac2 prune_arith () : unit :=
  let hs := List.fold_right (fun (id, _, ty) acc => if has_arith ty then id :: acc else acc) (Control.hyps ()) [] in
  Std.keep hs.

Ltac2 rec atomic_arith (t : constr) : bool :=
  lazy_match! t with
  | ?a /\ ?b => if atomic_arith a then atomic_arith b else false
  | @eq ?ty _ _ => lazy_match! ty with Z => true | nat => true | positive => true | N => true | _ => false end
  | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
  | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
  | False => true
  | _ => false
  end.
Ltac2 has_hard (t : constr) : bool :=
  match! t with
  | context [Z.modulo _ _] => true
  | context [Z.div _ _] => true
  | context [Z.pow _ ?e] => lazy_match! e with Zpos _ => Control.zero Match_failure | Z0 => Control.zero Match_failure | _ => true end
  | _ => false
  end.
Ltac2 prune_atomic () : unit :=
  let hs := List.fold_right (fun (id, _, ty) acc => if atomic_arith ty then (if has_hard ty then acc else id :: acc) else acc) (Control.hyps ()) [] in
  Std.keep hs.
Ltac prune_atomic := ltac2:(prune_atomic ()).

Ltac prune_arith := ltac2:(prune_arith ()).

Ltac zchecker_k :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff ;
  exact_no_check (Stdlib.micromega.ZMicromega.ZTautoChecker_sound __ff __wit
                    (@eq_refl bool true)
                    (@Stdlib.micromega.VarMap.find BinNums.Z BinNums.Z0 __varmap)).

Ltac plia_cert_lazy := constr:(false).
Ltac zchecker_sel := lazymatch plia_cert_lazy with true => zchecker_k | _ => Stdlib.micromega.Lia.zchecker end.

Ltac zify_ne := intros; zify_elim_let; zify_op; (zify_iter_specs); zify_saturate.
Ltac lia_ne := zify_ne; xlia zchecker_sel.

Ltac lia_st := Zify.zify; xlia zchecker_sel.

Ltac plia_full_fallback := constr:(true).
Ltac plia_last := lazymatch plia_full_fallback with false => fail | _ => lia_st end.
Ltac plia := first [ solve [ prune_atomic; lia_ne ] | solve [ prune_arith; lia_ne ] | solve [ prune_arith; lia_st ] | plia_last ].

Ltac plia_dbg := first [ solve [ prune_atomic; lia_ne ] | idtac "PLIA-FALLBACK0"; solve [ prune_arith; lia_ne ]
                       | idtac "PLIA-FALLBACK1"; solve [ prune_arith; lia_st ]
                       | idtac "PLIA-FALLBACK2"; tryif assert_succeeds lia_st then (idtac "PLIA-T3-OK"; lia_st) else fail ].

Ltac pnia := first [ solve [ prune_arith; Zify.zify; xnia zchecker_sel ] | Zify.zify; xnia zchecker_sel ].

Ltac plia_v := first [ solve [ prune_atomic; zify_ne; xlia Stdlib.micromega.Lia.zchecker ] | solve [ prune_arith; zify_ne; xlia Stdlib.micromega.Lia.zchecker ] | solve [ prune_arith; Stdlib.micromega.Lia.lia ] | Stdlib.micromega.Lia.lia ].
Ltac plia_k := first [ solve [ prune_atomic; zify_ne; xlia zchecker_k ] | solve [ prune_arith; zify_ne; xlia zchecker_k ] | solve [ prune_arith; Zify.zify; xlia zchecker_k ] | Zify.zify; xlia zchecker_k ].

Goal forall (x y : Z) (P : Z -> Prop) (f : Z -> Z), P x -> (forall z, P z -> z < 3)%Z -> (0 <= x)%Z -> (x < y)%Z \/ P y -> f x = 3%Z -> (x <= y)%Z -> (x < f x + y + 1)%Z.
Proof. intros. prune_arith. Fail match goal with H : P x |- _ => idtac end. plia. Qed.
Section Smoke.
  Import Stdlib.Lists.List.
  Goal forall (x y : Z) (n : nat) (l : list Z), (0 <= x < 16)%Z -> (y = 2 * x + 1)%Z -> (n <= length l)%nat -> In x l -> (y <= 31 /\ 0 <= Z.of_nat n)%Z.
  Proof. intros. plia_k. Qed.
  Goal forall (x y : Z) (n : nat) (l : list Z), (0 <= x < 16)%Z -> (y = 2 * x + 1)%Z -> (n <= length l)%nat -> In x l -> (y <= 31 /\ 0 <= Z.of_nat n)%Z.
  Proof. intros. plia_v. Qed.
  Goal forall (x : Z) (P : Prop), (P /\ (x < 3)%Z) -> (P -> x < 3)%Z -> (x < 4)%Z.
  Proof. intros. plia_dbg. Qed.
  Goal forall x y : Z, (0 <= x)%Z -> (0 <= y)%Z -> (0 <= x * y)%Z.
  Proof. intros. pnia. Qed.
End Smoke.
