(** * Bridge.DMatch.DMatchDefs — group M (deflate matching and window): the definitions
    [DMatchIface] states its pairs with.

    Kept apart from [DMatchIface] so that the proof files can import these
    definitions and [DMatchIface] can, once they are proved, re-export the
    proofs without a cycle.

    - [cf_geom level]: compress_fuzzer's geometry (zlib wrapper, windowBits 15,
      memLevel 8, default strategy), the one [defl_new level 8 15 8 0] builds.
    - [rb_ok t]: what [read_buf] needs of the stream (no checksum other than
      Adler-32, [total_in] does not wrap).
    - [mt_inv t]: the matching-side invariant, over RT's state only (the S5
      side of every fact follows through [IRelDefl.dst_rel]).  It contains
      group R's hash-chain and match invariants ([Risk/RiskIface.v]:
      [ms_inv], [ms_fast_inv], [ms_slow_inv]) and adds what the S5/RT
      lockstep needs besides: window bytes, the slide offset [slid] that
      bounds every position by the consumed input, and the stream bounds.
      It reads only [d_cfg], [d_wrap], [d_ls] and the input side of [d_strm]
      ([zs_in], [zs_done], [zs_totalin]), so any code that leaves those alone
      keeps it ([mt_inv_frame]); group D carries it from
      [DMatchIface.dm_entry] to the dispatch that way.

    Ownership: group M (a worker).  Group D uses [mt_inv] only through
    [dm_entry], [mt_inv_frame], [mt_inv_fb_lz] and as a precondition, so its
    fields may grow (over the same components) without touching D. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require RiskIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module RK := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk.RiskIface.

(** compress_fuzzer's geometry at [level]: w_size 32768 (window_size 65536),
    hash_size 32768, MAX_DIST = 32768 - 262 = 32506. *)
Definition cf_geom (level : Z) : RC.DeflGeom := RC.defl_geom_wrap 1 level 15 8 0.

Definition rb_ok (t : RD.DSt) : Prop :=
  (RD.d_wrap t = 0 \/ RD.d_wrap t = 1)
  /\ 0 <= RD.zs_totalin (RD.d_strm t)
  /\ RD.zs_totalin (RD.d_strm t) + Chunk.zlen (RD.zs_in (RD.d_strm t)) < 2 ^ 64.

(** The matching-side invariant.  Positions are window indices; [slid] (in
    [mt_slid]) is how far the window has slid over the consumed input, so
    [slid + p] is the input position of window index [p]. *)
Record mt_inv (t : RD.DSt) : Prop := mkMtInv {
  mt_level : 0 <= RC.dg_level (RD.d_cfg t) <= 9;
  mt_cfg   : RD.d_cfg t = cf_geom (RC.dg_level (RD.d_cfg t));
  mt_wrap  : RD.d_wrap t = 1;
  mt_rb    : rb_ok t;
  (** group R's invariants: hash chains point below [strstart], window
      room, and the pending match of each loop *)
  mt_ms    : RK.ms_inv t;
  mt_fast  : RC.dg_level (RD.d_cfg t) <= 3 -> RK.ms_fast_inv t;
  mt_slow  : 4 <= RC.dg_level (RD.d_cfg t) -> RK.ms_slow_inv t;
  (** every window byte is a byte *)
  mt_win   : forall i, 0 <= i < 65536 -> 0 <= RD.ls_window (RD.d_ls t) i < 256;
  mt_ma    : RD.ls_matchavail (RD.d_ls t) = 0
             \/ (RD.ls_matchavail (RD.d_ls t) = 1 /\ 1 <= RD.ls_strstart (RD.d_ls t));
  mt_ml    : 0 <= RD.ls_matchlen (RD.d_ls t) <= 258 /\ 0 <= RD.ls_prevlen (RD.d_ls t) <= 258;
  mt_bs    : RD.ls_blockstart (RD.d_ls t) <= RD.ls_strstart (RD.d_ls t);
  mt_hw    : 0 <= RD.ls_highwater (RD.d_ls t) <= 65536;
  (** block start and match start are real input positions at or before
      [strstart]: what makes S5's [wrap32]/[wrap64] readings of
      [strstart - match_start] and [strstart - block_start] exact *)
  mt_slid  : exists slid, 0 <= slid
             /\ Chunk.zlen (RD.zs_done (RD.d_strm t))
                = slid + RD.ls_strstart (RD.d_ls t) + RD.ls_lookahead (RD.d_ls t)
             /\ 0 <= slid + RD.ls_blockstart (RD.d_ls t)
             /\ 0 <= slid + RD.ls_matchstart (RD.d_ls t)
             /\ RD.ls_matchstart (RD.d_ls t) <= RD.ls_strstart (RD.d_ls t);
  mt_inlen : Chunk.zlen (RD.zs_done (RD.d_strm t)) + Chunk.zlen (RD.zs_in (RD.d_strm t)) < 2 ^ 32;
  (** a pending match (deflate_slow) was found at [strstart - 1], so
      [strstart >= 1]: what makes S5's [wrap32 (strstart + lookahead - 3)]
      (deflate_slow's [max_insert]) exact *)
  mt_pend  : RC.MIN_MATCH <= RD.ls_matchlen (RD.d_ls t) -> 1 <= RD.ls_strstart (RD.d_ls t)
}.

Lemma rb_ok_frame : forall t t',
  RD.d_wrap t' = RD.d_wrap t ->
  RD.zs_in (RD.d_strm t') = RD.zs_in (RD.d_strm t) ->
  RD.zs_totalin (RD.d_strm t') = RD.zs_totalin (RD.d_strm t) ->
  rb_ok t -> rb_ok t'.
Proof. intros t t' Hw Hi Ht (H1 & H2 & H3). unfold rb_ok. rewrite Hw, Hi, Ht. auto. Qed.

Lemma ms_inv_frame : forall t t',
  RD.d_cfg t' = RD.d_cfg t -> RD.d_ls t' = RD.d_ls t -> RK.ms_inv t -> RK.ms_inv t'.
Proof.
  intros t t' Hc Hl H. destruct H. constructor; rewrite ?Hc, ?Hl; assumption.
Qed.

Lemma mt_inv_frame : forall t t',
  RD.d_cfg t' = RD.d_cfg t -> RD.d_wrap t' = RD.d_wrap t -> RD.d_ls t' = RD.d_ls t ->
  RD.zs_in (RD.d_strm t') = RD.zs_in (RD.d_strm t) ->
  RD.zs_done (RD.d_strm t') = RD.zs_done (RD.d_strm t) ->
  RD.zs_totalin (RD.d_strm t') = RD.zs_totalin (RD.d_strm t) ->
  mt_inv t -> mt_inv t'.
Proof.
  intros t t' Hc Hw Hl Hi Hd Ht H. destruct H.
  pose proof (rb_ok_frame t t' Hw Hi Ht mt_rb0) as Hrb.
  pose proof (ms_inv_frame t t' Hc Hl mt_ms0) as Hms.
  constructor; unfold RK.ms_fast_inv, RK.ms_slow_inv in *; rewrite ?Hc, ?Hw, ?Hl, ?Hi, ?Hd; assumption.
Qed.
