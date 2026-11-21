(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateOverlay OverlayBlock OverlayFacts OverlayLarge. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import OverlayGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Theorem overlay_core_proof : OVERLAY_CORE.
Proof.
  apply OVERLAY_CORE_from_bound. intros s b OP OK.
  pose proof (op_lbs _ OP) as R.
  exact (overlay_bound_large b (ds_lit_bufsize s) OK ltac:(lia)).
Qed.
