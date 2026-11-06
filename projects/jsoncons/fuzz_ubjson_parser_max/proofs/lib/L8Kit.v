(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
Ltac l8_concl T := lazymatch T with ?A -> ?B => l8_concl B | _ => T end.
Ltac cfeed0 N X tac :=
let T := type of X in
let T' := eval cbn beta iota in T in
let C := l8_concl T' in
assert (N : C) by (apply X; cbn beta iota; first [ tac | lazymatch goal with |- ?A => fail 1 "cfeed: cannot prove premise" A end ]).
Tactic Notation "cfeed" ident(N) constr(X) tactic(tac) := cfeed0 N X tac.
