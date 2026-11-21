(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import LiaTuning StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 rv_prune0_nog () : unit :=
  match rv4_ids false (Control.hyps ()) with [] => () | ids => Std.clear ids end.
Ltac zify_prune_relevant_nog := ltac2:(Control.enter rv_prune0_nog).

Ltac lia_tier0u :=
  first [ zify_prune_relevant_nog; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

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
