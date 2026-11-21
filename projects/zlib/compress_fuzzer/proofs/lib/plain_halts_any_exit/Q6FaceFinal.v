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
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Theorem zr_raw_face_final : ZrHuffDynLeg -> ZRepro_Inflater_raw.
Proof.
  intro HDyn.
  apply zr_raw_face_from_core.
  exact (zr_raw_core_final zr_huff_fixed_holds HDyn).
Qed.

Theorem zr_gzip_face_final : ZrHuffDynLeg -> ZRepro_Inflater_gzip.
Proof.
  intro HDyn.
  apply zr_gzip_face_from_core.
  exact (zr_gzip_core_final zr_huff_fixed_holds HDyn).
Qed.

Theorem zr_zlib_face_final : ZrHuffDynLeg -> ZRepro_Inflater_zlib.
Proof.
  intro HDyn.
  apply zr_zlib_face_from_core.
  exact (zr_zlib_core_final zr_huff_fixed_holds HDyn).
Qed.

Print Assumptions zr_raw_face_final.
Print Assumptions zr_gzip_face_final.
Print Assumptions zr_zlib_face_final.
