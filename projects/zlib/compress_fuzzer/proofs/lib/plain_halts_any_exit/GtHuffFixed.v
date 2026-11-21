(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtHuffFixed — THE FIXED LEG,
      DISCHARGED (amendment #10 window; q7-decode as TL-confirmed
      carrier, 2026-08-20).

    [ZrHuffFixedLeg] (Q6HuffResidue's premise-carrying residue, v4)
    holds outright: the canonical composition (ZReproQ6S) applied to the
    mountain theorem (GtLenFastLeg.zr_len_fast_leg_holds).  With the
    amended walk (ZReproQ6W) and q6-fixedtbl's assemblies, the raw
    face's residue reduces to the DYNAMIC leg alone.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  Q6HuffResidue ZReproQ6S GtLenFastLeg.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Theorem zr_huff_fixed_holds : ZrHuffFixedLeg.
Proof.
  exact (zr_fixed_canonical zr_len_fast_leg_holds).
Qed.

Print Assumptions zr_huff_fixed_holds.
