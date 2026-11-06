(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Zify.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac wd_zs :=
  intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (zify_iter_specs);
  first [ solve [ Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook; xlia zchecker ]
        | zify_saturate; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook ].

Ltac wd_zs_stock :=
  intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (zify_iter_specs); zify_saturate;
  Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.

Ltac Zify.zify ::= wd_zs.
