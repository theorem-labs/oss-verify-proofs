(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition ub_kind2 (pc : Z) : Z :=
  match pc with
  | _ => 0
  end.
