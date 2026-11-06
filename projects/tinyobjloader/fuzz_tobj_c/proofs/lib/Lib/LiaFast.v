(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require Import ZArith PreOmega ZifyClasses ZifyInst Zify Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zify_core :=
  intros;
  Zify.zify_pre_hook;
  zify_elim_let;
  zify_op;
  (Zify.zify_iter_specs);
  Zify.zify_saturate.

Ltac zify_noeuclid := zify_core; Zify.zify_post_hook.
Ltac zify_euclid := zify_core; Zify.zify_internal_to_euclidean_division_equations; Zify.zify_post_hook.

Ltac lia_noeuclid := zify_noeuclid; xlia zchecker.
Ltac lia_euclid := zify_euclid; xlia zchecker.
Ltac nia_noeuclid := zify_noeuclid; xnia zchecker.
Ltac nia_euclid := zify_euclid; xnia zchecker.

Ltac Stdlib.micromega.Lia.lia ::= first [ lia_noeuclid | lia_euclid ].

