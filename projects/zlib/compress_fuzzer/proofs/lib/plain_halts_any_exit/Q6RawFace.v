(** * Q6RawFace — ZRepro_Inflater_raw reduced to one named soundness core.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; TL
    assignment).  The raw inflater face (windowBits -15, frame =
    [BodyDecodesTo] alone) is here reduced to [ZrRawCore]: the
    Z_FINISH-soundness of [zr_inflate] at wrap 0 against the declarative
    [dec_stream].  The reduction discharges: the [ZR_Flush1] leg (via
    [ZReproL0F.zr_inflate_to_finish] — Z_NO_FLUSH runs are flush-blind),
    the frame unfold (raw frame IS the [dec_stream] equation), and
    Some-injectivity.

    [ZrRawCore]'s premise set is the face's (enc, cap) projection: the
    cap ceilings ride along because the u32 unwrap makes UNBOUNDED
    soundness falsifiable (ZRepro.v's cap-ceiling note; at raw there is
    no checksum to mask a wrapped mis-copy, so the bound is load-bearing
    for the core, not just the face), and the BYTE premise rides along
    because without it the face itself is FALSE (the 2026-08-20 byte
    repair; machine-checked falsifier in ZReproFalsifyGuard.v — the
    model copies [br_in] raw where the spec reads through [bytes_bits]'
    low-8 masking; [br_wf]'s in-range clause is the walk-side guard this
    premise establishes at init via [zlist]).  Statement shape ACKed by
    model-rt; this reduction proves the interface SUFFICIENT for the
    face — inhabitation is the stage-3/4 walk.

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

(** THE named residue: Z_FINISH soundness of the raw pump.  Whoever
    proves this (the stage-3/4 walk, or its stored+static fragment plus
    the LEN-chain stage-4 deliverable) closes the face below. *)
Definition ZrRawCore : Prop :=
  forall cap enc y,
    0 <= cap ->
    cap <= 4294967295 ->
    zlen enc <= 4294967290 ->
    Forall (fun b => 0 <= b < 256) enc ->
    zr_inflate Z_FINISH (-15) cap enc = Some y ->
    dec_stream (bytes_bits enc) = Some y.

Theorem zr_raw_face_from_core :
  ZrRawCore -> ZRepro_Inflater_raw.
Proof.
  intros CORE.
  unfold ZRepro_Inflater_raw, ZR_InflaterConsumes.
  intros x enc flush cap HX HF HFl Hxcap Hcap Henc HBy [y Hy].
  assert (HyF : zr_inflate Z_FINISH (-15) cap enc = Some y).
  { apply (zr_inflate_to_finish flush); [| | exact Hy];
      destruct HFl as [-> | ->];
      unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES; lia. }
  assert (Hcap0 : 0 <= cap)
    by (pose proof HX as [_ _]; unfold zlen in Hxcap; lia).
  pose proof (CORE cap enc y Hcap0 Hcap Henc HBy HyF) as HD.
  unfold ZR_FramedRaw, BodyDecodesTo in HF.
  rewrite HF in HD. injection HD as <-.
  exact Hy.
Qed.

Print Assumptions zr_raw_face_from_core.
