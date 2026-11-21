(** * Bridge.Risk.RiskIface — group R's day-1 statement file (part C of the tracker 2.2).

    The two risk items other groups prove against.
    all are now proved in [Bridge/Risk/] ((a) in
    [OvKit], (b) in [MsKit] / [MsFill] / [MsTrip] / [MsTripS] / [MsFinal])
    and closed here by [exact].  Frozen: a change goes through the part C
    lead (PAIR-GROUPS.md).  Changes since day 1 (2026-10-20): [ms_slow_inv]
    gained the slow match-length clause (the lead's request); [ms_inv]
    gained [mi_wmask] / [mi_hmask]; [ms_lm_live] needs only the [prev] half
    of the chains ([ms_prev_ok]) and the window mask.

    (a) The sym_buf overlay, FUNCTIONAL half (for group D: D22 tr_flush_block,
        D31 compress_block).  S5 keeps its symbols inside [pending_buf]
        (from [lit_bufsize] on) while the block's bits are written into the
        same array from 0; RT keeps the symbols in a separate [ts_symbuf].
        S5's closed [FB_CALL] (from [overlay_core_proof]) gives the SAFETY
        half: under [fb_entry] the emission stays inside [pending_buf].  It
        does not state that the symbols S5 reads are the ones that were
        tallied.  The statements below do: under the running invariant of
        S5's own proof ([RefDeflSafeE4.CBI]: the bit write position never
        passes the read position of the next symbol), S5's [compress_block]
        equals [sbs_run] over the send_bits calls computed from the PRISTINE
        symbols (the symbol bytes as they were when the block started), and
        at a flush ([fb_entry]) both the dynamic and the static branch meet
        that invariant.  Under [sym_rel] the pristine symbol bytes are RT's
        [ts_symbuf], so D compares [cb_calls] with RT's emission.

    (b) match_start live range (for group M: D14 deflate_fast, D15
        deflate_slow).  [lz_rel] relates [match_start] and [prev_match] mod
        2^32 only (RT lets them go negative after a window slide, S5 wraps).
        S5 tallies [wrap32 (strstart - match_start)] (fast) and
        [wrap32 (strstart - 1 - prev_match)] (slow); these equal RT's
        unwrapped distances exactly when the live distance is in
        [[0, 2^32)].  The statements: the arithmetic ([ms_wrap_dist]); RT's
        [longest_match] result is live when it improves on [prev_length],
        provided every hash-chain entry lies below [strstart]
        ([ms_chain_ok]); the chain invariant and the per-strategy match
        invariants survive a loop trip; so at every match emission the RT
        distance is in [[1, max_dist]].

    Ownership: group R (a worker).  Reviewer: the part C lead. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState Trees TreesTab DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel CompressModel TreeModel FlushBlockModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay RefDeflSafeFB RefDeflSafeE4 RefDeflSafeE5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require OvKit MsDefs MsFinal.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module RB := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Base.

(* ========================================================================= *)
(* (a)  The sym_buf overlay, functional half                                 *)
(* ========================================================================= *)

(** The send_bits calls for symbols [j, j+1, ..., j+n-1] of [s0], read from
    [s0]'s symbol bytes ([sym_calls] reads [pending_buf] at
    [lit_bufsize + 3j .. lit_bufsize + 3j + 2]); [cb_calls] for all [N]
    symbols; [cb_all] adds END_BLOCK.  Defined (and the lemmas below proved)
    in [Risk.OvKit]; these names are aliases. *)
Notation cb_calls_from := OvKit.cb_calls_from (only parsing).
Notation cb_calls := OvKit.cb_calls (only parsing).
Notation cb_all := OvKit.cb_all (only parsing).

(** [compress_block] on the overlaid array emits the pristine symbols.  The
    hypotheses are those of S5's [RefDeflSafeE4.compress_block_facts]:
    [PREFIX] is the overlay invariant itself (before symbol [k] is read, the
    bit write position [W0 + cost of symbols 0..k-1] is at most the read
    position [8 * (lit_bufsize + 3k)]); [CBI s0 .. 0 y] says [y] is [s0]'s
    array with only bits written below [pending]. *)
Lemma ov_compress_block : forall s0 lfc ldl dfc ddl N W0,
  0 <= N ->
  arr_len (ds_pending_buf s0) = ds_lit_bufsize s0 * 4 ->
  ds_lit_bufsize s0 + 3 * N + 3 <= arr_len (ds_pending_buf s0) ->
  (forall j, 0 <= j < N -> sym_okb s0 j) ->
  (forall j, 0 <= j < N -> 0 <= arr_get ldl (sym_lcode s0 j) <= 15) ->
  (forall j, 0 <= j < N -> sym_isdist s0 j = true -> 0 <= arr_get ddl (sym_dcode s0 j) <= 15) ->
  (forall k, 0 <= k < N -> W0 + zsum (dcost ldl ddl s0) 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s0 + 3 * k)) ->
  W0 + zsum (dcost ldl ddl s0) 0 (Z.to_nat N) <= 8 * arr_len (ds_pending_buf s0) ->
  forall y, CBI s0 ldl ddl N W0 0 y ->
  compress_block y lfc ldl dfc ddl = sbs_run y (cb_all s0 lfc ldl dfc ddl N).
Proof. exact OvKit.ov_compress_block. Qed.

(** At a flush, dynamic branch: S5's [compress_block] call after the tree
    header ([hX13]) emits the pristine symbols of the flushed state [s]
    with the block's dynamic codes.  [overlay_core_proof] is what makes
    [PREFIX] hold here. *)
Lemma ov_emit_dyn : forall s last,
  fb_entry s last ->
  tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 1 ->
  let X6 := ov_X6 s in
  let y := hX13 X6 last (ov_mb s) in
  compress_block y (ds_dyn_ltree_fc X6) (ds_dyn_ltree_dl X6) (ds_dyn_dtree_fc X6) (ds_dyn_dtree_dl X6)
  = sbs_run y (cb_all s (ds_dyn_ltree_fc X6) (ds_dyn_ltree_dl X6) (ds_dyn_dtree_fc X6) (ds_dyn_dtree_dl X6) (nsym s)).
Proof. exact OvKit.ov_emit_dyn. Qed.

(** At a flush, static branch (no branch hypothesis: a static code is at
    most 31 bits per 3-byte symbol, so the invariant holds whatever the
    branch). *)
Lemma ov_emit_stat : forall s last,
  fb_entry s last ->
  let y := send_bits (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3 in
  compress_block y static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
  = sbs_run y (cb_all s static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl (nsym s)).
Proof. exact OvKit.ov_emit_stat. Qed.

(** The pristine calls depend only on the symbol bytes [[0, 3N)] of the
    symbol area, so under [sym_rel] they are computed from RT's
    [ts_symbuf]: two states with the same symbol bytes have the same calls. *)
Lemma cb_calls_ext : forall a b lfc ldl dfc ddl N,
  (forall i, 0 <= i < 3 * N -> sym_buf_get b i = sym_buf_get a i) ->
  cb_calls b lfc ldl dfc ddl N = cb_calls a lfc ldl dfc ddl N.
Proof. exact OvKit.cb_calls_ext. Qed.

(* ========================================================================= *)
(* (b)  match_start live range                                              *)
(* ========================================================================= *)

(** The arithmetic: S5's tallied distance is RT's when RT's is in range.
    ([lz_rel] gives [ds_match_start = wrap32 ms] and
    [ds_prev_match = wrap32 pm]; [ds_strstart = ls_strstart].) *)
Lemma ms_wrap_dist : forall a m, 0 <= a - m < 2 ^ 32 -> wrap32 (a - wrap32 m) = a - m.
Proof.
  intros a m H. rewrite !wrap32_mod. rewrite Zminus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.

(** The definitions (b) is stated with live in [Risk.MsDefs] (so the proof
    files need not import this file); these names are aliases for the same
    constants.

    - [ms_chain_ok g l]: RT's hash chains point strictly below [strstart]
      (or are NIL), every [head] slot of the hash table and every [prev]
      slot of the window; [ms_prev_ok]: the [prev] half.
    - [ms_inv s]: the chain invariant plus the state facts it needs to
      survive a trip (window slide, the inserts of fill_window and of the
      match loops), and the geometry's masks; all hold from [deflateInit2] on.
    - [ms_fast_inv s]: deflate_fast, at the top of a trip no match is pending.
    - [ms_slow_inv s]: deflate_slow, at the top of a trip a pending match
      (found one trip earlier, at [strstart - 1]) is no longer than
      [lookahead + 1] (the slow clause of [IFuelDefl.fuel_deflate_slow]) and
      is live.
    - [df_l1 p0] / [ds_l2 p0]: the trip's states as [df_body] / [ds_body]
      name them, from the post-fill state [p0] (verbatim lets).
    - [step_state r]: the state a trip leaves, whatever it returns. *)
Notation ms_chain_ok := MsDefs.ms_chain_ok (only parsing).
Notation ms_prev_ok := MsDefs.ms_prev_ok (only parsing).
Notation ms_inv := MsDefs.ms_inv (only parsing).
Notation mi_chain := MsDefs.mi_chain (only parsing).
Notation mi_wsize := MsDefs.mi_wsize (only parsing).
Notation mi_maxdist := MsDefs.mi_maxdist (only parsing).
Notation mi_winsize := MsDefs.mi_winsize (only parsing).
Notation mi_str := MsDefs.mi_str (only parsing).
Notation mi_look := MsDefs.mi_look (only parsing).
Notation mi_room := MsDefs.mi_room (only parsing).
Notation mi_ins := MsDefs.mi_ins (only parsing).
Notation mi_wmask := MsDefs.mi_wmask (only parsing).
Notation mi_hmask := MsDefs.mi_hmask (only parsing).
Notation ms_fast_inv := MsDefs.ms_fast_inv (only parsing).
Notation ms_slow_inv := MsDefs.ms_slow_inv (only parsing).
Notation df_l1 := MsDefs.df_l1 (only parsing).
Notation ds_l2 := MsDefs.ds_l2 (only parsing).
Notation step_state := MsDefs.step_state (only parsing).

(** [longest_match] reports a live match whenever it improves on
    [prev_length]: the reported start is one of the chain positions it
    visited, all of which lie in [[strstart - max_dist, strstart - 1]].
    Only the [prev] half of the chains is needed (after the trip's own hash
    insert, [head] holds [strstart] itself). *)
Lemma ms_lm_live : forall g l cur,
  ms_prev_ok g l -> RC.dg_w_mask g = RC.dg_w_size g - 1 -> 1 <= RC.dg_w_size g ->
  RD.NIL < cur < RD.ls_strstart l -> RD.ls_strstart l - cur <= RC.dg_max_dist g ->
  let r := RD.longest_match g l cur in
  RD.ls_prevlen l < fst r -> 1 <= RD.ls_strstart l - snd r <= RC.dg_max_dist g.
Proof. exact MsFinal.ms_lm_live_r. Qed.

(** The top-of-loop fill keeps the invariants (a slide moves [strstart],
    [match_start] and every chain entry down by [w_size] together). *)
Lemma ms_fill : forall s,
  ms_inv s -> ms_inv (RD.ds_fill s)
  /\ (ms_fast_inv s -> ms_fast_inv (RD.ds_fill s))
  /\ (ms_slow_inv s -> ms_slow_inv (RD.ds_fill s)).
Proof. exact MsFinal.ms_fill_r. Qed.

(** Emission in deflate_fast (post-fill state [p0], [lookahead >= 1]): the
    match branch's distance is live. *)
Lemma ms_fast_emit : forall p0,
  ms_inv p0 -> ms_fast_inv p0 -> 1 <= RD.ls_lookahead (RD.d_ls p0) ->
  RC.MIN_MATCH <= RD.ls_matchlen (df_l1 p0) ->
  1 <= RD.ls_strstart (df_l1 p0) - RD.ls_matchstart (df_l1 p0) <= RC.dg_max_dist (RD.d_cfg p0).
Proof. exact MsFinal.ms_fast_emit_r. Qed.

(** Emission in deflate_slow (post-fill state [p0]): the previous match's
    distance is live. *)
Lemma ms_slow_emit : forall p0,
  ms_inv p0 -> ms_slow_inv p0 -> 1 <= RD.ls_lookahead (RD.d_ls p0) ->
  RC.MIN_MATCH <= RD.ls_prevlen (ds_l2 p0) -> RD.ls_matchlen (ds_l2 p0) <= RD.ls_prevlen (ds_l2 p0) ->
  1 <= RD.ls_strstart (ds_l2 p0) - 1 - RD.ls_prevmatch (ds_l2 p0) <= RC.dg_max_dist (RD.d_cfg p0).
Proof. exact MsFinal.ms_slow_emit_r. Qed.

(** One whole trip keeps the invariants, whatever the trip returns. *)
Lemma ms_df_step : forall flush s,
  ms_inv s -> ms_fast_inv s ->
  ms_inv (step_state (RD.df_step flush s)) /\ ms_fast_inv (step_state (RD.df_step flush s)).
Proof. exact MsFinal.ms_df_step_r. Qed.

Lemma ms_ds_step : forall flush s,
  ms_inv s -> ms_slow_inv s ->
  ms_inv (step_state (RD.ds_step flush s)) /\ ms_slow_inv (step_state (RD.ds_step flush s)).
Proof. exact MsFinal.ms_ds_step_r. Qed.

(** At deflate's first call (a fresh [defl_new] state with the call's
    stream installed) all three hold. *)
Lemma ms_init : forall level t0 z,
  RD.defl_new level 8 15 8 0 = Some t0 ->
  let t := RD.setD_strm z t0 in
  ms_inv t /\ ms_fast_inv t /\ ms_slow_inv t.
Proof. exact MsFinal.ms_init_r. Qed.
