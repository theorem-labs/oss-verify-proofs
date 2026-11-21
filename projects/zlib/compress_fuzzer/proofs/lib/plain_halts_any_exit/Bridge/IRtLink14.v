
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiC ZHarnessC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZApiInstC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require
  RtL0ZRt14 RtL1ZRt14 RtL2ZRt14 RtL3ZRt14 RtL4ZRt14 RtL5ZRt14 RtL6ZRt14 RtL7ZRt14 RtL8ZRt14 RtL9ZRt14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IBoundary IBoundary14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Theorem rt_compress_path_all14 : forall L, 0 <= L <= 9 -> RtCompressPath14 L.
Proof.
  intros L HL.
  assert (H : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
  - exact RtL0ZRt14.zr_l0z_compress_path14.
  - exact RtL1ZRt14.zr_l1z_compress_path14.
  - exact RtL2ZRt14.zr_l2z_compress_path14.
  - exact RtL3ZRt14.zr_l3z_compress_path14.
  - exact RtL4ZRt14.zr_l4z_compress_path14.
  - exact RtL5ZRt14.zr_l5z_compress_path14.
  - exact RtL6ZRt14.zr_l6z_compress_path14.
  - exact RtL7ZRt14.zr_l7z_compress_path14.
  - exact RtL8ZRt14.zr_l8z_compress_path14.
  - exact RtL9ZRt14.zr_l9z_compress_path14.
Qed.

(** compress_fuzzer's two asserts never fail, on every input, given the two part C deliverables at 1.4. *)
Theorem harness_no_ckfail_all14 :
  BrCompressCall -> BrUncompressCall14 ->
  forall d k, harness_outC ZApiInstC.zinstC d <> HC_exit k.
Proof.
  intros HC HU d k.
  pose proof (sel_level_range (norm8 d)) as HL.
  exact (harness_no_ckfail14 (sel_level (norm8 d)) HL HC HU
           (rt_compress_path_all14 _ HL) d k eq_refl).
Qed.
