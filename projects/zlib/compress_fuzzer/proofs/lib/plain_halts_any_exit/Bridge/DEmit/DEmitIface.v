(** * Bridge.DEmit.DEmitIface — group D's day-1 statement file (part C of the tracker 2.2).

    The four pair statements group M's [deflate_fast] / [deflate_slow] call:
    the two symbol tallies and the two block flushes.  Group D proves them
    in its own files under [Bridge/DEmit/]; this file re-exports each proof
    under the frozen statement (the tallies: [BrTally]; the flushes:
    [BrFlushBlock] on pair D22, [BrTrFlush.br_tr_flush_block]; all four are
    closed under the global context).  Frozen once published: a change goes
    through the part C lead (PAIR-GROUPS.md).

    Every statement has the shape of the proved pairs ([BrBits], [BrFlush]):
    the deflate relation [dst_rel] on entry plus named side conditions, then
    [dst_rel] again between the two models' results, equality of the returned
    value, and the side condition back for the next call.

    The side conditions (defined in [DEmitDefs], re-exported here) are
    S5-only predicates ([dst_rel] already carries the RT side), all over the
    EMISSION fields of S5's state, so M's matching and window code leaves
    them alone ([em_inv_frame]):

    - [em_core s]: S5's own flush-entry record [RefDeflSafeFB.fb_entry]
      (S5's safety proof establishes it at every flush point:
      [RefDeflSafeLF.DC_fb_entry]) minus its window and [strstart] fields,
      plus an empty pending queue and room in [total_out].  From it and
      [fb_lz], S5's closed [FB_CALL] gives that a block's emission stays
      inside [pending_buf] and never overwrites a symbol before it is read,
      which is what lets S5's aliased [sym_buf] agree with RT's separate one.
    - [em_inv s]: [em_core s] with room for one more symbol (the state
      between two trips of the deflate loops).
    - [fb_lz t]: the window/[strstart] facts a flush needs, stated on RT's
      side over [d_cfg] and [d_ls] only (group M's matching invariant
      implies it).

    Ownership: group D (a worker).  Reviewer: the part C lead. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateBlk TreeModel DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Export DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require BrTally BrFlushBlock.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* 3.  The pair statements group M calls                                     *)
(* ------------------------------------------------------------------------- *)

(** [_tr_tally_lit] (pair D21).  No condition on [c] (both models store
    [c mod 256]).  Proved: [BrTally.br_tr_tally_lit]. *)
Theorem pair_tr_tally_lit : forall s t pre_out pre_in c,
  dst_rel s t pre_out pre_in -> em_inv s ->
  dst_rel (fst (DT.tr_tally_lit s c))
          (RD.setD_ts (snd (RT.tr_tally_lit c (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))) t)
          pre_out pre_in
  /\ snd (DT.tr_tally_lit s c) = fst (RT.tr_tally_lit c (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))
  /\ em_core (fst (DT.tr_tally_lit s c))
  /\ (snd (DT.tr_tally_lit s c) = false -> em_inv (fst (DT.tr_tally_lit s c))).
Proof. exact BrTally.br_tr_tally_lit. Qed.

(** [_tr_tally_dist] (pair D21).  The [dst_rel] half needs nothing of
    [distance]/[length]; [1 <= distance <= 32768] is for [em_core] (a stored
    distance of 0 would read back as a literal and break [freq_hist]).
    Proved: [BrTally.br_tr_tally_dist]. *)
Theorem pair_tr_tally_dist : forall s t pre_out pre_in distance length,
  dst_rel s t pre_out pre_in -> em_inv s -> 1 <= distance <= 32768 ->
  dst_rel (fst (DT.tr_tally_dist s distance length))
          (RD.setD_ts (snd (RT.tr_tally_dist distance length (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))) t)
          pre_out pre_in
  /\ snd (DT.tr_tally_dist s distance length)
     = fst (RT.tr_tally_dist distance length (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))
  /\ em_core (fst (DT.tr_tally_dist s distance length))
  /\ (snd (DT.tr_tally_dist s distance length) = false -> em_inv (fst (DT.tr_tally_dist s distance length))).
Proof. exact BrTally.br_tr_tally_dist. Qed.

(** [FLUSH_BLOCK_ONLY] (pair D23).  When [avail_out] is left non-zero the
    queue has drained and the next block starts empty, so [em_inv] holds
    again. *)
Theorem pair_flush_block_only : forall s t pre_out pre_in last,
  dst_rel s t pre_out pre_in -> em_core s -> fb_lz t -> 0 <= last <= 1 ->
  dst_rel (DL.flush_block_only s last) (RD.flush_block_only last t) pre_out pre_in
  /\ (DS.cs_avail_out (DS.ds_strm (DL.flush_block_only s last)) <> 0 -> em_inv (DL.flush_block_only s last)).
Proof. exact BrFlushBlock.br_flush_block_only. Qed.

(** [FLUSH_BLOCK] (pair D23): the same, plus the early-return block state. *)
Theorem pair_flush_block : forall s t pre_out pre_in last,
  dst_rel s t pre_out pre_in -> em_core s -> fb_lz t -> 0 <= last <= 1 ->
  dst_rel (fst (DB.flush_block s last)) (snd (RD.flush_block last t)) pre_out pre_in
  /\ option_map bs_of (snd (DB.flush_block s last)) = fst (RD.flush_block last t)
  /\ (DS.cs_avail_out (DS.ds_strm (fst (DB.flush_block s last))) <> 0 -> em_inv (fst (DB.flush_block s last))).
Proof. exact BrFlushBlock.br_flush_block. Qed.
