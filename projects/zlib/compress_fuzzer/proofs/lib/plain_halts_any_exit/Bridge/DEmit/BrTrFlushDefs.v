(** * Bridge.DEmit.BrTrFlushDefs — RT's side of pair D22 ([_tr_flush_block]).

    The block the two [FLUSH_BLOCK_ONLY]s hand to [_tr_flush_block]: S5
    passes a window OFFSET ([DeflateOverlay.fb_buf], [None] when
    [block_start < 0]) and [stored_len] mod 2^64 ([fb_len]); RT passes the
    window BYTES ([win_take]) and the plain [Z] length, and returns the
    data type separately ([rt_fb]).  Under [em_core] and [fb_lz] the
    length is in [[0, 2^32)], so the two lengths agree.  [BrTrFlush]
    re-exports this file. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** RT's [_tr_flush_block] call inside [flush_block_only]. *)
Definition rt_fb (t : RD.DSt) (last : Z) : Z * RT.TSt :=
  let l := RD.d_ls t in
  let bs := RD.ls_blockstart l in
  let stored_len := RD.ls_strstart l - bs in
  let buf := if Z.leb 0 bs then Some (RD.win_take (RD.ls_window l) bs stored_len) else None in
  RT.tr_flush_block buf stored_len last (RC.dg_level (RD.d_cfg t)) (RC.dg_strategy (RD.d_cfg t))
                    (RD.zs_datatype (RD.d_strm t)) (RD.d_ts t).

(** The RT state right after it (data type and trees installed). *)
Definition rt_fb_state (t : RD.DSt) (last : Z) : RD.DSt :=
  RD.setD_ts (snd (rt_fb t last)) (RD.setD_strm (RD.setZ_datatype (fst (rt_fb t last)) (RD.d_strm t)) t).
