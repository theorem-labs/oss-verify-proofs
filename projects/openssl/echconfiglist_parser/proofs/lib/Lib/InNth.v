(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac in_nth_go A l x n fuel :=
  lazymatch fuel with
  | O => fail "in_nth: not found within the fuel"
  | S ?fuel' => first [ exact (@nth_error_In A l n x (@eq_refl (option A) (Some x))) | in_nth_go A l x constr:(S n) fuel' ]
  end.

Ltac in_nth :=
  lazymatch goal with
  | |- @In ?A ?x ?l => in_nth_go A l x constr:(O) constr:(400%nat)
  end.
