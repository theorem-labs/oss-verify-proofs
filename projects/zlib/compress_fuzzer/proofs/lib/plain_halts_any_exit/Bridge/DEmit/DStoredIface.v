(** * Bridge.DEmit.DStoredIface — pair D13 of PAIRS.md: [deflate_stored], S5 vs RT


    Level 0's block function as compress_fuzzer's one [deflate(Z_FINISH)]
    call reaches it: straight after the zlib header, with no input in the
    window yet ([lookahead = 0], no symbols).  The block states agree and
    the states stay related, as in group M's [dm_deflate_fast]; afterwards
    only the trailer runs, so the last three conclusions are exactly what
    [DZHeader.pair_deflate_trailer] asks for (no [mt_inv] conclusion).

    The S5 premise is [st_inv], not group D's [em_inv]: [em_inv] contains
    [em_core]'s [1 <= ds_level s], which [dst_rel] contradicts at level 0
    (the first version of this statement, ,
    was vacuous for that reason).  [st_inv] is the queue / bit buffer /
    stream-count part, which holds at the dispatch after the header's flush.

    Where the two models differ:
    - S5's loop runs [avail_out + 1] trips (group R's
      [IFuelDefl.fuel_deflate_stored]: more fuel changes nothing), RT's
      [avail_out / 5 + 3];
    - the window refill reads the call's input array (S5) against [lastn]
      of the consumed input (RT);
    - M's [dm_read_buf_window] / [dm_read_buf_next_out] relate the two
      [read_buf]s, and [DTrStored] / [BrStored] the stored blocks.

    Ownership: group D (a worker); the proof is a worker's. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DStored.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** S5's queue, bit buffer and stream counts at level 0's entry. *)
Definition st_inv (s : DS.deflate_state) : Prop :=
  DS.ds_pending s = 0 /\ DS.ds_pending_out s = 0 /\ DS.ds_bi_valid s = 0
  /\ 0 <= DS.cs_avail_out (DS.ds_strm s) < 2 ^ 32 /\ 0 <= DS.cs_total_out (DS.ds_strm s)
  /\ DS.cs_total_out (DS.ds_strm s) + DS.cs_avail_out (DS.ds_strm s) + arr_len (DS.ds_pending_buf s) < 2 ^ 64.

Theorem br_deflate_stored : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> mt_inv t -> st_inv s ->
  RC.dg_level (RD.d_cfg t) = 0 -> DS.ds_lookahead s = 0 -> DS.ds_sym_next s = 0 ->
  DS.ds_strstart s = 0 -> DS.ds_block_start s = 0 ->
  bs_of (snd (DB.deflate_stored s Z_FINISH)) = fst (RD.deflate_stored Z_FINISH t)
  /\ dst_rel (fst (DB.deflate_stored s Z_FINISH)) (snd (RD.deflate_stored Z_FINISH t)) pre_out pre_in
  /\ DS.ds_sym_next (fst (DB.deflate_stored s Z_FINISH)) = 0
  /\ fp_ok (fst (DB.deflate_stored s Z_FINISH))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (DB.deflate_stored s Z_FINISH))) <> 0 ->
      room (fst (DB.deflate_stored s Z_FINISH)) 10).
Proof. exact DStored.br_deflate_stored_iface. Qed.
