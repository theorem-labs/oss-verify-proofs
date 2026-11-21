(** * Q6ZlibFace — ZRepro_Inflater_zlib reduced to one named soundness core.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; TL
    trilogy assignment).  Third sibling of Q6RawFace/Q6GzipFace, at the
    zlib config (windowBits 15, frame ZR_FramedZlib).  The core takes
    the FRAME-SHAPED stream ([b0;b1] ++ body ++ be32 ad) with ALL FOUR
    words quantified and NO header-validity premise: the model checks
    the header itself (bad CM/CINFO/FCHECK die in M_BAD; an FDICT-set
    header — which [ZlibHeaderOk]'s fourth clause (FDICT clear; the
    GAP7-F2 amendment) now ALSO excludes — dies at
    [InfRet Z_NEED_DICT]), and every rejection is excluded by the
    success premise.  [ZlibHeaderOk] and [TrailerMatchesPayload] are
    emitter-side obligations; soundness discards them here, exactly as
    Q6GzipFace discards the gzip trailer values.

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

(** THE named residue: Z_FINISH soundness of the zlib pump on a
    frame-shaped stream — model-rt's zr_sound goal at the decomposed
    spelling (the skipn-2 body split done by the frame). *)
Definition ZrZlibCore : Prop :=
  forall cap b0 b1 body ad y,
    0 <= cap ->
    cap <= 4294967295 ->
    zlen ([b0; b1] ++ body ++ be32 ad) <= 4294967290 ->
    Forall (fun b => 0 <= b < 256) ([b0; b1] ++ body ++ be32 ad) ->
    zr_inflate Z_FINISH 15 cap ([b0; b1] ++ body ++ be32 ad) = Some y ->
    dec_stream (bytes_bits body) = Some y.

Theorem zr_zlib_face_from_core :
  ZrZlibCore -> ZRepro_Inflater_zlib.
Proof.
  intros CORE.
  unfold ZRepro_Inflater_zlib, ZR_InflaterConsumes.
  intros x enc flush cap HX HF HFl Hxcap Hcap Henc HBy [y Hy].
  destruct HF as (b0 & b1 & body & ad & Heq & Hhdr & HB & Htr).
  unfold ZlibFramed in Heq. subst enc.
  assert (HyF : zr_inflate Z_FINISH 15 cap
                  ([b0; b1] ++ body ++ be32 ad) = Some y).
  { apply (zr_inflate_to_finish flush); [| | exact Hy];
      destruct HFl as [-> | ->];
      unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES; lia. }
  assert (Hcap0 : 0 <= cap) by (unfold zlen in Hxcap; lia).
  pose proof (CORE cap b0 b1 body ad y Hcap0 Hcap Henc HBy HyF) as HD.
  unfold BodyDecodesTo in HB.
  rewrite HB in HD. injection HD as <-.
  exact Hy.
Qed.

Print Assumptions zr_zlib_face_from_core.
