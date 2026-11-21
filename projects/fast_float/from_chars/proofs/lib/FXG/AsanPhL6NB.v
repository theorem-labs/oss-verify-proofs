(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the loop constants are renamed onto the new start-up by AsanRelaunch). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Import AsanRelaunch.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition PHL6_N0 : positive := rl_vmap 8652%positive.
Definition PHL6_MEAS : lin := rl_lin {| l_c := 0; l_t := [(8665%positive, 1)] |}.
