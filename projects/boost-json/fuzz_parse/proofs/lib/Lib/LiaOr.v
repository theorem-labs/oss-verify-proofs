(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "" s.

Definition orbox : ltac2:(zQ "00>1PPP") := ltac2:(zQ "00\1PP^1").

Ltac box_ors := repeat match goal with H : ?P \/ ?Q |- _ => change (orbox (P \/ Q)) in H end.

Ltac olia :=
  box_ors;
  first [ lia
        | match goal with H : orbox _ |- _ => unfold orbox in H; lia end
        | match goal with H1 : orbox _ |- _ => match goal with H2 : orbox _ |- _ => unfold orbox in H1, H2; lia end end
        | unfold orbox in *; lia ].
