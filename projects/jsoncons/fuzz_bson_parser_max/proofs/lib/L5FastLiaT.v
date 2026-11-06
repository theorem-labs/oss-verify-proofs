(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac plia2 := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_st ] ].
Ltac plia1 := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_ne ] ].
(* [comment removed for export] *)
Ltac plia_log := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_ne ]
                       | idtac "PLIA-T2-TRY"; solve [ L5FastLia.prune_arith; L5FastLia.lia_st ]
                       | idtac "PLIA-T3-TRY"; tryif assert_succeeds L5FastLia.plia_last then (idtac "PLIA-T3-OK"; L5FastLia.plia_last) else fail ].
Goal forall x y : Z, (0 <= x)%Z -> (x <= 2 * x)%Z /\ (y = y)%Z.
Proof. intros. split. plia2. plia1. Qed.
