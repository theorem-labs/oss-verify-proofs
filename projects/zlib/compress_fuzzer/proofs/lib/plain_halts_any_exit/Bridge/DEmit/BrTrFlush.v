(** * Bridge.DEmit.BrTrFlush — pair D22 of PAIRS.md: [_tr_flush_block], S5 vs RT.

    The statement [BrFlushBlock] (pair D23) builds on.  RT's side
    ([rt_fb], [rt_fb_state]) is in [BrTrFlushDefs], re-exported here; the
    proof is assembled in [BrFbFin] from the tree phase ([BrFbPre]), the
    block's bits ([BrFbEmit]) and the pieces in [BrFbKit].

    The block the two [FLUSH_BLOCK_ONLY]s hand to [_tr_flush_block]: S5
    passes a window OFFSET ([DeflateOverlay.fb_buf], [None] when
    [block_start < 0]) and [stored_len] mod 2^64 ([fb_len]); RT passes the
    window BYTES ([win_take]) and the plain [Z] length, and returns the
    data type separately ([rt_fb]).  Under [em_core] and [fb_lz] the
    length is in [[0, 2^32)], so the two lengths agree. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Export BrTrFlushDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require BrFbFin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Theorem br_tr_flush_block : forall s t pre_out pre_in last,
  dst_rel s t pre_out pre_in -> em_core s -> fb_lz t -> 0 <= last <= 1 ->
  dst_rel (DT.tr_flush_block s (DO.fb_buf s) (DO.fb_len s) last) (rt_fb_state t last) pre_out pre_in.
Proof. exact BrFbFin.br_tr_flush_block'. Qed.

Print Assumptions br_tr_flush_block.
