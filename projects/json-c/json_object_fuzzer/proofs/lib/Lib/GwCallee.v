(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition gw_hyp (P : Prop) : Prop := P.

Ltac gw_subst T X Y :=
let P := eval pattern X in T in
lazymatch P with ?F _ => let r := eval cbv beta in (F Y) in r end.

Ltac gw_strip n T :=
lazymatch n with
| O => T
| S ?n' => lazymatch T with forall _ : _, ?T' => gw_strip n' T' end
end.

Ltac gw_fold_pcs T b K offs :=
lazymatch offs with
| nil => T
| ?o :: ?rest =>
let s := eval vm_compute in (K + o) in
let T' := gw_subst T (b + K + o) (b + s) in
gw_fold_pcs T' b K rest
end.

Ltac gw_callee_type0 t n :=
let T0 := type of t in
let T1 := eval cbv beta in T0 in
let T2 := gw_strip n T1 in
T2.
Ltac gw_callee_type t n b K offs :=
let T0 := type of t in
let T1 := eval cbv beta in T0 in
let T2 := gw_strip n T1 in
let T3 := gw_fold_pcs T2 b K offs in
T3.
Ltac gw_callee_hyp t n b K offs := let T := gw_callee_type t n b K offs in exact T.
