(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Zify.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac zify_nodiv := intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (zify_iter_specs);
  first [ solve [ Zify.zify_post_hook; xlia zchecker ] | zify_saturate; Zify.zify_post_hook ].

Ltac lia_nd :=
  lazymatch Zify.zify_convert_to_euclidean_division_equations_flag with
  | true => first [ solve [ zify_nodiv; xlia zchecker ] | Zify.zify; xlia zchecker ]
  | _ => Zify.zify; xlia zchecker
  end.
Ltac zlia_nd := lia_nd.
Ltac znia_nd :=
  lazymatch Zify.zify_convert_to_euclidean_division_equations_flag with
  | true => first [ solve [ zify_nodiv; xnia zchecker ] | Zify.zify; xnia zchecker ]
  | _ => Zify.zify; xnia zchecker
  end.
