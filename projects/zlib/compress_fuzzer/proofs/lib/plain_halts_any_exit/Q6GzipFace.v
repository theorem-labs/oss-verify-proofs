(** * Q6GzipFace — ZRepro_Inflater_gzip reduced to one named soundness core.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; TL
    assignment: gzip-face groundwork).  Mirror of Q6RawFace at the gzip
    config (windowBits 31, frame ZR_FramedGzip 9): the face reduces to
    [ZrGzipCore] — Z_FINISH soundness of the pump on a FRAME-SHAPED
    stream (fixed 10-byte header, arbitrary trailer words) against the
    declarative [dec_stream] of the body.  The trailer words are
    QUANTIFIED (tc, tn): on a successful run the model itself checked
    them against its computed crc32/ISIZE, so the core never needs them
    pinned — mismatches die in M_BAD and are excluded by the success
    premise.

    Discharges here: the flush leg ([ZReproL0F.zr_inflate_flushblind]),
    the frame unfold (existential body decomposition), Some-injectivity.
    Cap ceilings + the Forall-byte premise ride along exactly as in
    Q6RawFace (the 2026-08-20 byte repair; the falsifier guard leaf is
    ZReproFalsifyGuard.v).

    CORE v2: the core gains `0 <= cap` — found by
    attempting the assembly (the walk's 0 <= o_left premise at the init
    state IS o_left = cap; at negative cap the machine does junk trips
    with negative o_left and the core is falsifiable).  The face supplies
    it via zlen x <= cap + zlen nonneg; threaded in the reduction.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits BwStream ZBitsIn ZBitsOut DeflateSpec
  InflateFast Inflate Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro ZReproL0F.
Import SymbolIdDeclIface.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** THE named residue: Z_FINISH soundness of the gzip pump on a
    frame-shaped stream.  Whoever proves this (gzip entry leg + the
    shared body walk + gzip trailer tail) closes the face below. *)
Definition ZrGzipCore : Prop :=
  forall cap body tc tn y,
    0 <= cap ->
    cap <= 4294967295 ->
    zlen (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn)
      <= 4294967290 ->
    Forall (fun b => 0 <= b < 256)
      (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn) ->
    zr_inflate Z_FINISH 31 cap
      (zr_gzip_header 9 ++ body ++ zr_le32 tc ++ zr_le32 tn) = Some y ->
    dec_stream (bytes_bits body) = Some y.

Theorem zr_gzip_face_from_core :
  ZrGzipCore -> ZRepro_Inflater_gzip.
Proof.
  intros CORE.
  unfold ZRepro_Inflater_gzip, ZR_InflaterConsumes.
  intros x enc flush cap HX HF HFl Hxcap Hcap Henc HBy [y Hy].
  destruct HF as [body [Heq HB]].
  subst enc.
  assert (HyF : zr_inflate Z_FINISH 31 cap
                  (zr_gzip_header 9 ++ body
                   ++ zr_le32 (crc32_z zr_crc_init false 0 x)
                   ++ zr_le32 (zlen x)) = Some y).
  { apply (zr_inflate_to_finish flush); [| | exact Hy];
      destruct HFl as [-> | ->];
      unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES; lia. }
  assert (Hcap0 : 0 <= cap) by (unfold zlen in Hxcap; lia).
  pose proof (CORE cap body (crc32_z zr_crc_init false 0 x) (zlen x) y
                Hcap0 Hcap Henc HBy HyF) as HD.
  unfold BodyDecodesTo in HB.
  rewrite HB in HD. injection HD as <-.
  exact Hy.
Qed.

Print Assumptions zr_gzip_face_from_core.
