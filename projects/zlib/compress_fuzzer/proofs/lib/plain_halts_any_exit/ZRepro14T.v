(** * ZRepro14T — zlib 1.4 twins of the three ZRepro statements the RtL<L>ZRt14 chain needs.  [ZRepro.ZR_PumpSucceeds], [ZRepro.ZR_InflaterConsumes] and
    [ZRepro.ZRepro_Inflater_zlib] word for word, with [ZRepro14.zr_inflate14] for [ZRepro.zr_inflate]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel
  Require Import Base Checksum Chunk ZBitsIn ZBitsOut InflateFast Inflate
                 Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import DeclIface ZRepro ZRepro14.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** [ZRepro.ZR_PumpSucceeds] at 1.4. *)
Definition ZR_PumpSucceeds14 (level windowBits : Z) : Prop :=
  forall x enc flush cap,
    ZR_Input x -> zr_deflate level windowBits x = Some enc ->
    ZR_Flush1 flush -> zlen x <= cap -> cap <= 4294967295 ->
    exists y, zr_inflate14 flush windowBits cap enc = Some y.

(** [ZRepro.ZR_InflaterConsumes] at 1.4. *)
Definition ZR_InflaterConsumes14 (windowBits : Z)
           (Frame : list Z -> list Z -> Prop) : Prop :=
  forall x enc flush cap,
    ZR_Input x -> Frame enc x -> ZR_Flush1 flush -> zlen x <= cap ->
    cap <= 4294967295 -> zlen enc <= 4294967290 ->
    Forall (fun b => 0 <= b < 256) enc ->
    (exists y, zr_inflate14 flush windowBits cap enc = Some y) ->
    zr_inflate14 flush windowBits cap enc = Some x.

(** [ZRepro.ZRepro_Inflater_zlib] at 1.4. *)
Definition ZRepro_Inflater_zlib14 : Prop := ZR_InflaterConsumes14 15 ZR_FramedZlib.
