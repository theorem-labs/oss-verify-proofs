(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import LiaTuning StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 rv_prune0_nog () : unit :=     (* [comment removed for export] *)
  match rv4_ids false (Control.hyps ()) with [] => () | ids => Std.clear ids end.
Ltac zify_prune_relevant_nog := ltac2:(Control.enter rv_prune0_nog).

(* [comment removed for export] *)
Ltac lia_tier0u :=
  first [ zify_prune_relevant_nog; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac tlia_u := first [ zify_prune_relevant_nog; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
                     | Zify.zify; xlia zchecker
                     | sf_unhide;
                       first [ zify_prune_neg; Zify.zify; xlia zchecker
                             | zify_prune_plain; Zify.zify; xlia zchecker
                             | Zify.zify; xlia zchecker ] ].
Ltac lia3_u := first [ zify_prune_relevant_nog; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
                     | zify_prune_plain; Zify.zify; xlia zchecker
                     | zify_prune_neg; Zify.zify; xlia zchecker
                     | Zify.zify; xlia zchecker ].
