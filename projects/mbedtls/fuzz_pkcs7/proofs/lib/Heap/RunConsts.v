(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

Record rconsts := mkRC {
  rc_secret : Z; rc_canary : Z;
  rc_secret_range : 0 <= rc_secret < 2^64; rc_canary_range : 0 <= rc_canary < 2^64 }.

(* [comment removed for export] *)
Lemma z0_range : 0 <= 0 < 2^64. Proof. lia. Qed.
Definition rc0 : rconsts := mkRC 0 0 z0_range z0_range.
