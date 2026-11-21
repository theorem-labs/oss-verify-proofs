(* the zlib 1.4 twin of GtHuffFixed, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from GtHuffFixed), 1.3.1-only declarations no 1.4 consumer needs. *)
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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtHuffFixed.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtLenFastLeg14 Q6HuffResidue14 ZReproQ6S14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Theorem zr_huff_fixed_holds14 : ZrHuffFixedLeg14.
Proof.
  exact (zr_fixed_canonical14 zr_len_fast_leg_holds14).
Qed.

