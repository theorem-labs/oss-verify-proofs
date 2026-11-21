(** * ZREmitDecode — per-config decodability corollaries (GAP7, half 2).

    OWNER: q5-emitter (2026-08-20; q7-decode's GAP7 delegation, item 2).

    The landed zero-premise faces bundle header/body/trailer inside each
    config's Frame; q7-decode's body-success lemma consumes the BODY
    SLICE alone.  These corollaries do the split once, in the frozen
    consumer shape: [zr_deflate = Some enc], the frame equation naming
    the slice, byte-bounds on the SLICE (q7 parity note: the uniform
    shape across all three configs, matching the l1 head where
    body = enc), and [BodyDecodesTo body x]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro ZREmitClose Gap7Strict ZRRawShell Gap7Bridge EnoughFitsB14.
Import SymbolIdDeclIface.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** default-zlib (6,15): the body between the 2-byte header and the
    4-byte adler trailer decodes to the input. *)
Theorem zlib_body_decodes : forall x,
  ZR_Input x ->
  exists enc b0 b1 body ad,
    zr_deflate ZR_DEFAULT_LEVEL 15 x = Some enc
    /\ ZlibFramed enc b0 b1 body ad
    /\ Forall (fun b => 0 <= b < 256) body
    /\ BodyDecodesTo body x.
Proof.
  intros x Hx.
  destruct (ZRepro_Emitter_default_zlib_holds x Hx)
    as (enc & Henc & _ & Hby & HF).
  destruct HF as (b0 & b1 & body & ad & Hfr & _ & Hdec & _).
  exists enc, b0, b1, body, ad.
  split; [exact Henc|].
  split; [exact Hfr|].
  split; [|exact Hdec].
  unfold ZlibFramed in Hfr. rewrite Hfr in Hby.
  apply Forall_app in Hby. destruct Hby as [_ Hby].
  apply Forall_app in Hby. destruct Hby as [Hbody _].
  exact Hbody.
Qed.

(** l9-gzip (9,31): the body between the 10-byte header and the 8-byte
    CRC/ISIZE trailer decodes to the input. *)
Theorem gzip_body_decodes : forall x,
  ZR_Input x ->
  exists enc body,
    zr_deflate 9 31 x = Some enc
    /\ enc = zr_gzip_header 9 ++ body
             ++ zr_le32 (crc32_z zr_crc_init false 0 x)
             ++ zr_le32 (zlen x)
    /\ Forall (fun b => 0 <= b < 256) body
    /\ BodyDecodesTo body x.
Proof.
  intros x Hx.
  destruct (ZRepro_Emitter_l9_gzip_holds x Hx)
    as (enc & Henc & _ & Hby & HF).
  destruct HF as (body & Heq & Hdec).
  exists enc, body.
  split; [exact Henc|].
  split; [exact Heq|].
  split; [|exact Hdec].
  rewrite Heq in Hby.
  apply Forall_app in Hby. destruct Hby as [_ Hby].
  apply Forall_app in Hby. destruct Hby as [Hbody _].
  exact Hbody.
Qed.

(* ==========================================================================
   q7 F4 (sub-byte padding): the EXACTNESS twins.  The body slice is
   consumed to within one byte; the decode leftover is the Z_FINISH
   windup pad, so [length rem < 8].  [IsValidStreamFor] is the spec's
   own predicate (DeflateSpec §11); [IsValidStreamFor_DecodesTo] weakens
   back to the loose form if a consumer wants both from one supply.
   ========================================================================== *)

Theorem zlib_body_valid : forall x,
  ZR_Input x ->
  exists enc b0 b1 body ad,
    zr_deflate ZR_DEFAULT_LEVEL 15 x = Some enc
    /\ ZlibFramed enc b0 b1 body ad
    /\ Forall (fun b => 0 <= b < 256) body
    /\ IsValidStreamFor body x.
Proof. exact ZR_BodyValidZlib_holds. Qed.

Theorem gzip_body_valid : forall x,
  ZR_Input x ->
  exists enc body,
    zr_deflate 9 31 x = Some enc
    /\ enc = zr_gzip_header 9 ++ body
             ++ zr_le32 (crc32_z zr_crc_init false 0 x)
             ++ zr_le32 (zlen x)
    /\ Forall (fun b => 0 <= b < 256) body
    /\ IsValidStreamFor body x.
Proof. exact ZR_BodyValidGzip_holds. Qed.

(* ==========================================================================
   GAP7 STRICT twins: the machine-accept decode succeeds on the emitted
   body, modulo the freeze's two named statements — g1's
   [build_accepts_of_kraft_STMT] (proof in flight, their declaration)
   and the ENOUGH residue [EnoughFits_STMT] (g6's commission).  Both
   premises drop by name when the proofs land; everything else is
   zero-premise.
   ========================================================================== *)

Theorem zlib_body_strict :
  build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
  forall x, ZR_Input x ->
  exists enc b0 b1 body ad,
    zr_deflate ZR_DEFAULT_LEVEL 15 x = Some enc
    /\ ZlibFramed enc b0 b1 body ad
    /\ Forall (fun b => 0 <= b < 256) body
    /\ (exists rem, dec_stream_from_strict (bytes_bits body) []
                    = Some (x, rem)
                 /\ (length rem < 8)%nat).
Proof.
  intros HBK EFR.
  exact (ZR_BodyStrictZlib_of HBK EFR).
Qed.

Theorem gzip_body_strict :
  build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
  forall x, ZR_Input x ->
  exists enc body,
    zr_deflate 9 31 x = Some enc
    /\ enc = zr_gzip_header 9 ++ body
             ++ zr_le32 (crc32_z zr_crc_init false 0 x)
             ++ zr_le32 (zlen x)
    /\ Forall (fun b => 0 <= b < 256) body
    /\ (exists rem, dec_stream_from_strict (bytes_bits body) []
                    = Some (x, rem)
                 /\ (length rem < 8)%nat).
Proof.
  intros HBK EFR.
  exact (ZR_BodyStrictGzip_of HBK EFR).
Qed.

Print Assumptions zlib_body_decodes.
Print Assumptions gzip_body_decodes.
Print Assumptions zlib_body_valid.
Print Assumptions gzip_body_valid.
Theorem raw_body_strict :
  build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
  forall x enc,
    ZR_Input x ->
    zr_deflate 1 (-15) x = Some enc ->
    exists rem, dec_stream_from_strict (bytes_bits enc) [] = Some (x, rem).
Proof.
  intros HBK EFR x enc HI HS.
  exact (proj2 (proj2 (zr_emitter_l1_raw_frame x enc HI HS)) HBK EFR).
Qed.

(* ==========================================================================
   ZERO-PREMISE FINAL FORMS (2026-08-22): both frozen statements are now
   THEOREMS — g1's [Gap7Bridge.build_accepts_of_kraft_holds] (r4 window)
   and g6's [EnoughFitsB14.enough_fits_capped_final] — so the strict rows
   hold unconditionally, per the campaign's zero-premise [_holds] naming.
   ========================================================================== *)

Theorem zlib_body_strict_holds : forall x,
  ZR_Input x ->
  exists enc b0 b1 body ad,
    zr_deflate ZR_DEFAULT_LEVEL 15 x = Some enc
    /\ ZlibFramed enc b0 b1 body ad
    /\ Forall (fun b => 0 <= b < 256) body
    /\ (exists rem, dec_stream_from_strict (bytes_bits body) []
                    = Some (x, rem)
                 /\ (length rem < 8)%nat).
Proof.
  exact (zlib_body_strict build_accepts_of_kraft_holds
           enough_fits_capped_final).
Qed.

Theorem gzip_body_strict_holds : forall x,
  ZR_Input x ->
  exists enc body,
    zr_deflate 9 31 x = Some enc
    /\ enc = zr_gzip_header 9 ++ body
             ++ zr_le32 (crc32_z zr_crc_init false 0 x)
             ++ zr_le32 (zlen x)
    /\ Forall (fun b => 0 <= b < 256) body
    /\ (exists rem, dec_stream_from_strict (bytes_bits body) []
                    = Some (x, rem)
                 /\ (length rem < 8)%nat).
Proof.
  exact (gzip_body_strict build_accepts_of_kraft_holds
           enough_fits_capped_final).
Qed.

Theorem raw_body_strict_holds : forall x enc,
  ZR_Input x ->
  zr_deflate 1 (-15) x = Some enc ->
  exists rem, dec_stream_from_strict (bytes_bits enc) [] = Some (x, rem).
Proof.
  exact (raw_body_strict build_accepts_of_kraft_holds
           enough_fits_capped_final).
Qed.

Print Assumptions zlib_body_strict.
Print Assumptions gzip_body_strict.
Print Assumptions raw_body_strict.
Print Assumptions zlib_body_strict_holds.
Print Assumptions gzip_body_strict_holds.
Print Assumptions raw_body_strict_holds.
