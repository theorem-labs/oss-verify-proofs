(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
Open Scope Z_scope.

Ltac rng_tac :=
  lazymatch goal with |- icpt_rng ?A ?n =>
    apply icpt_rng_intro;
    [ first [ match goal with H : shw _ ?A0 ?n0 |- _ => apply (win_ok_sub A0 n0 A n (proj2 (proj2 H))); lia end
            | match goal with H : win_ok ?A0 ?n0 |- _ => apply (win_ok_sub A0 n0 A n H); lia end ]
    | lia | lia ] end.
