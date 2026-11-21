(* the zlib 1.4 twin of Q6FaceFinal, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from Q6FaceFinal), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * Q6FaceFinal — the inflater endgame, legible in-tree.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; TL
    order via flow-lead, train #3).  Three one-line compositions, no
    new content: each face's reduction theorem (Q6*Face) applied to its
    assembly's core theorem (Zr*Asm footer) with the fixed leg
    discharged by [GtHuffFixed.zr_huff_fixed_holds] (landed q7-p10).

    Net in-tree state these three lines make legible: ALL THREE
    [ZR_InflaterConsumes] faces — raw (wb -15), gzip (wb 31), zlib
    (wb 15) — are conditional on [ZrHuffDynLeg] ALONE, the inflater
    family's last residue (the dynamic-table round).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro Q6HuffResidue Q6RawFace Q6GzipFace Q6ZlibFace
  ZrRawAsm ZrGzipAsm ZrZlibAsm GtHuffFixed.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6FaceFinal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtHuffFixed14 Q6HuffResidue14 Q6ZlibFace14 ZRepro14T ZrZlibAsm14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.



Theorem zr_zlib_face_final14 : ZrHuffDynLeg14 -> ZRepro_Inflater_zlib14.
Proof.
  intro HDyn.
  apply zr_zlib_face_from_core14.
  exact (zr_zlib_core_final14 zr_huff_fixed_holds14 HDyn).
Qed.

