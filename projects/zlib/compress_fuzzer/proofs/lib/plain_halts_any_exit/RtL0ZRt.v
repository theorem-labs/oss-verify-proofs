(** * RtL0ZRt — the (0, 15) zlib-format round trip at compress_fuzzer's
      uncompress call shape.

    The zlib-rt campaign closed level 0 at the Z_FINISH reads only
    (ZReproL0C.ZRepro_RoundTrip_l0_zlib_holds at avail_out = n + 1 and
    ZReproL0C.zr_l0_roundtrip_tight_cap at avail_out = n).  compress_fuzzer's
    [uncompress] reads with Z_NO_FLUSH at avail_out = n, so its fact was a
    gap.  It closes by citation: ZReproL0E.zr_inflate_transfer moves a
    Z_FINISH success to any flush other than Z_BLOCK / Z_TREES, and the
    compressBound fit is ZReproL0D.ZRepro_Emitter_l0_zlib_holds's bound
    conjunct (deflateBound(15) = compressBound by
    ZRepro.zr_compress_bound_agrees).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk ZBitsIn Inflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZReproL0C ZReproL0D ZReproL0E.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** compress_fuzzer's compress2 + uncompress pair at level 0. *)
Theorem zr_l0z_compress_path : forall x : list Z,
  ZR_Input x ->
  exists enc,
    zr_deflate 0 15 x = Some enc
    /\ zlen enc <= zlen x + Z.shiftr (zlen x) 12 + Z.shiftr (zlen x) 14
                   + Z.shiftr (zlen x) 25 + 13
    /\ zr_inflate Z_NO_FLUSH 15 (zlen x) enc = Some x.
Proof.
  intros x Hx.
  destruct (ZRepro_Emitter_l0_zlib_holds x Hx) as [enc [Henc [Hlen _]]].
  destruct (zr_l0_roundtrip_tight_cap x Hx) as [enc' [Henc' Hi]].
  rewrite Henc in Henc'. injection Henc' as <-.
  exists enc. split; [exact Henc|]. split.
  { rewrite <- zr_compress_bound_agrees. exact Hlen. }
  apply zr_inflate_transfer;
    [ unfold Z_NO_FLUSH, Z_BLOCK; lia
    | unfold Z_NO_FLUSH, Z_TREES; lia
    | exact Hi ].
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions zr_l0z_compress_path.
Unset Printing All.
