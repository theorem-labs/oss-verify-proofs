(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require Import ZArith List Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Inductive parg : Type := PA_s (s : list Z) | PA_i (i : Z) | PA_u (u : Z) | PA_g (d : Z)
| PA_li (i : Z) | PA_lu (u : Z).

Record dir : Type := mkDir { d_fl : Z; d_w : Z; d_p : Z; d_xp : bool; d_t : Z; d_ty : Z }.
