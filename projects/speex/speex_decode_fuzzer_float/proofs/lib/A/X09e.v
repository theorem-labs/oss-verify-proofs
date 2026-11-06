(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ck.
Import ListNotations.
Definition hidp (P : Prop) : Prop := P.

Ltac f32_fold_snoc H :=
match type of H with rw_cells ?S ?M ?P (f32 ?d ++ [C4 ?v]) => change (rw_cells S M P (f32 d ++ f32 [v])) in H; rewrite <- f32_app in H end.
Ltac f32_norm H :=
repeat match type of H with context [?a ++ [C4 ?v]] => change (a ++ [C4 v]) with (a ++ f32 [v]) in H end;
rewrite <- ?f32_app in H.
