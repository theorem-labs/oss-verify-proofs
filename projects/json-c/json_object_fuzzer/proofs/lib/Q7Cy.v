(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)


From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 cert_refl (rhs : constr) :=
let g := Control.goal () in
let r := constr:(@eq_refl _ $rhs) in
Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.native g)).

Ltac2 cert_refl_vm (rhs : constr) :=
let g := Control.goal () in
let r := constr:(@eq_refl _ $rhs) in
Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
