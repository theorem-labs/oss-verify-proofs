(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2 Constr Std Control Ltac1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Ltac2 cert_refl_native (rhs : constr) :=
  let g := Control.goal () in
  let ty := Constr.type rhs in
  let r := constr:(@eq_refl $ty $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.native g)).
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let ty := Constr.type rhs in
  let r := constr:(@eq_refl $ty $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
#[export] Set Default Proof Mode "Classic".
Tactic Notation "cert_native" constr(c) := (let f := ltac2:(c |- cert_refl_native (Option.get (Ltac1.to_constr c))) in f c).
Tactic Notation "cert_vm" constr(c) := (let f := ltac2:(c |- cert_refl_vm (Option.get (Ltac1.to_constr c))) in f c).
