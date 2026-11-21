(** * Bridge.DMatch.DMatchIface — group M (deflate matching and window): the pair
    statements other groups use.

    PAIR-GROUPS.md, group M.

    Consumers: group D's dispatch, block
    driver and [deflate_stored] (D12, D8, D7, D13).

    | statement              | pair | S5                       | RT                                 |
    |------------------------|------|--------------------------|------------------------------------|
    | [dm_compress_bound]    | D5   | [compressBound_m]        | [ZRepro.zr_deflate_bound 15]       |
    | [dm_entry]             | D1   | [IProbe.s5_entry]        | [IProbe.rt_entry]                  |
    | [dm_read_buf_window]   | D17  | [read_buf (RB_window o)] | [read_buf] + [win_blit]            |
    | [dm_read_buf_next_out] | D17  | [read_buf RB_next_out]   | [read_buf] + [setZ_out]            |
    | [dm_fill_window]       | D17  | [fill_window]            | [fill_window] (as [fill_if true])  |
    | [dm_deflate_fast]      | D14  | [deflate_fast]           | [deflate_fast]                     |
    | [dm_deflate_slow]      | D15  | [deflate_slow]           | [deflate_slow]                     |

    The block-state map [bs_of] is [IRelDefl]'s.  Group D's emission
    invariant [em_inv] (S5 side: pending queue empty, room for one more
    symbol), its field view [em_view] and [fb_lz] (RT side: what a flush needs
    of the window) come from [DEmit/DEmitIface.v].  The matching invariant
    [mt_inv] is in [DMatchDefs.v]; it contains group R's [ms_inv] /
    [ms_fast_inv] / [ms_slow_inv] ([Risk/RiskIface.v]).

    Ownership: group M (a worker).  A change goes through the part C lead. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZRepro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require IProbe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Export DMatchDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MBasic MReadBuf MEntry MLz MFill4 MFast7 MLazy6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.
Module SDfl := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Deflate.

(* ------------------------------------------------------------------------- *)
(* D5: compressBound                                                         *)
(* ------------------------------------------------------------------------- *)

(** S5's [compressBound] is RT's [deflateBound] at windowBits 15 (S5 only adds
    a [wrap64] cast, the identity below 2^60). *)
Theorem dm_compress_bound : forall len, 0 <= len < 2 ^ 60 ->
  SDfl.compressBound_m len = ZRepro.zr_deflate_bound 15 len.
Proof. exact MBasic.m_compress_bound. Qed.

(* ------------------------------------------------------------------------- *)
(* D1: the state at the deflate entry, every level and every input           *)
(* ------------------------------------------------------------------------- *)

(** Generalises [IProbe.deflate_entry_related] from one input to all inputs
    compress_fuzzer can pass: S5's state just after [deflate_m] installs the
    call's stream, against RT's [defl_new level 8 15 8 0] with the same call
    installed ([zr_deflate]'s [s1]). *)
Theorem dm_entry : forall level data,
  0 <= level <= 9 -> Forall (fun b => 0 <= b < 256) data -> zlength data <= 1048573 ->
  exists t, IProbe.rt_entry level data = Some t
         /\ dst_rel (IProbe.s5_entry level data) t [] []
         /\ RD.defl_wf t /\ mt_inv t.
Proof. exact MEntry.m_entry. Qed.

(** What group D's flush pairs need of the window holds at every point where
    [mt_inv] does. *)
Theorem mt_inv_fb_lz : forall t, mt_inv t -> fb_lz t.
Proof. exact MLz.m_fb_lz. Qed.

(* ------------------------------------------------------------------------- *)
(* D17: read_buf and fill_window                                             *)
(* ------------------------------------------------------------------------- *)

(** [read_buf] into the window at [off] (fill_window, deflate_stored's tail).
    RT's [read_buf] returns the bytes; its callers blit them at [off].  The
    write must fit S5's window (S5 drops a write past its end). *)
Theorem dm_read_buf_window : forall s t pre_out pre_in off size,
  dst_rel s t pre_out pre_in -> rb_ok t -> 0 <= size -> 0 <= off ->
  off + Z.min size (Chunk.zlen (RD.zs_in (RD.d_strm t))) <= RD.ls_windowsize (RD.d_ls t) ->
  snd (SLz.read_buf s (SLz.RB_window off) size)
    = Chunk.zlen (fst (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
  /\ dst_rel (fst (SLz.read_buf s (SLz.RB_window off) size))
       (RD.setD_strm (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
          (RD.setD_ls (RD.setL_window
                         (RD.win_blit (fst (RD.read_buf (RD.d_wrap t) size (RD.d_strm t))) off
                                      (RD.ls_window (RD.d_ls t)))
                         (RD.d_ls t)) t))
       pre_out pre_in
  /\ rb_ok (RD.setD_strm (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t))) t)
  /\ em_view (fst (SLz.read_buf s (SLz.RB_window off) size)) = em_view s.
Proof.
  intros s t pre_out pre_in off size H1 H2 H3 H4 H5.
  destruct (MReadBuf.m_read_buf_window s t pre_out pre_in off size H1 H2 H3 H4 H5) as (A & B & C).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. apply MReadBuf.m_rb_em_view_window.
Qed.

(** [read_buf] straight to the output (deflate_stored's direct copy).  RT's
    caller appends the bytes to [zs_out]; S5's [read_buf] emits them. *)
Theorem dm_read_buf_next_out : forall s t pre_out pre_in size,
  dst_rel s t pre_out pre_in -> rb_ok t -> 0 <= size ->
  snd (SLz.read_buf s SLz.RB_next_out size)
    = Chunk.zlen (fst (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
  /\ dst_rel (fst (SLz.read_buf s SLz.RB_next_out size))
       (RD.setD_strm (RD.setZ_out (RD.zs_out (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
                                   ++ fst (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))
                                  (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t)))) t)
       pre_out pre_in
  /\ rb_ok (RD.setD_strm (snd (RD.read_buf (RD.d_wrap t) size (RD.d_strm t))) t)
  /\ em_view (fst (SLz.read_buf s SLz.RB_next_out size)) = em_view s.
Proof.
  intros s t pre_out pre_in size H1 H2 H3.
  destruct (MReadBuf.m_read_buf_next_out s t pre_out pre_in size H1 H2 H3) as (A & B & C).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. apply MReadBuf.m_rb_em_view_next_out.
Qed.

(** [fill_window], as both block loops call it (lookahead below
    MIN_LOOKAHEAD).  S5 runs 263 trips at most, RT [avail_in + 2]; neither
    bound is reached.  Afterwards the window has room for a full match at
    [strstart]. *)
Theorem dm_fill_window : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> mt_inv t ->
  RD.ls_lookahead (RD.d_ls t) < 262 ->
  dst_rel (SLz.fill_window s) (RD.fill_if true t) pre_out pre_in
  /\ mt_inv (RD.fill_if true t)
  /\ RD.ls_strstart (RD.d_ls (RD.fill_if true t)) + 262 <= 65536
  /\ em_view (SLz.fill_window s) = em_view s.
Proof. exact MFill4.m_fill_window. Qed.

(* ------------------------------------------------------------------------- *)
(* D14, D15: deflate_fast and deflate_slow                                   *)
(* ------------------------------------------------------------------------- *)

(** One [deflate_fast] call (levels 1-3), from any related state with the
    matching invariant and group D's emission invariant.  The block states
    agree, the states stay related, and the emission invariant is back
    whenever output room is left (every exit that is not a full output
    buffer). *)
Theorem dm_deflate_fast : forall s t pre_out pre_in flush,
  dst_rel s t pre_out pre_in -> mt_inv t -> em_inv s ->
  1 <= RC.dg_level (RD.d_cfg t) <= 3 ->
  bs_of (snd (SBlk.deflate_fast s flush)) = fst (RD.deflate_fast flush t)
  /\ dst_rel (fst (SBlk.deflate_fast s flush)) (snd (RD.deflate_fast flush t)) pre_out pre_in
  /\ mt_inv (snd (RD.deflate_fast flush t))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (SBlk.deflate_fast s flush))) <> 0 ->
      em_inv (fst (SBlk.deflate_fast s flush))).
Proof. exact MFast7.m_deflate_fast. Qed.

(** One [deflate_slow] call (levels 4-9), same shape.  NOTE: the [dst_rel]
    conclusion needs [lz_rel]'s prev_match conjunct read mod 2^32, like
    match_start (done by the lead in ): deflate_slow copies
    match_start into prev_match on every trip, and RT's match_start is
    negative after a window slide when the last hit is older than w_size. *)
Theorem dm_deflate_slow : forall s t pre_out pre_in flush,
  dst_rel s t pre_out pre_in -> mt_inv t -> em_inv s ->
  4 <= RC.dg_level (RD.d_cfg t) <= 9 ->
  bs_of (snd (SBlk.deflate_slow s flush)) = fst (RD.deflate_slow flush t)
  /\ dst_rel (fst (SBlk.deflate_slow s flush)) (snd (RD.deflate_slow flush t)) pre_out pre_in
  /\ mt_inv (snd (RD.deflate_slow flush t))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (SBlk.deflate_slow s flush))) <> 0 ->
      em_inv (fst (SBlk.deflate_slow s flush))).
Proof. exact MLazy6.m_deflate_slow. Qed.
