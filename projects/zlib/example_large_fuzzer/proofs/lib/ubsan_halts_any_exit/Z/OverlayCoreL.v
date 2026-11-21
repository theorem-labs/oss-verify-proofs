(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateOverlay OverlayBlock OverlayFacts OverlayLarge OverlayGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Theorem overlay_core_proof : OVERLAY_CORE.
Proof.
  apply OVERLAY_CORE_from_bound. intros s b OP OK.
  pose proof (op_lbs _ OP) as R.
  exact (overlay_bound_large b (ds_lit_bufsize s) OK ltac:(lia)).
Qed.
