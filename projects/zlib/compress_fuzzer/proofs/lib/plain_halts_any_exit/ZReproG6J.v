(** * ZReproG6J — G6 bound-fit, part J: one flush EVENT fits, in tot_bits.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    The seam q5-emitter's [EvChain] fold consumes.  [flush_block_only] is
    [tr_flush_block] (the writer growth, part H) wrapped in
    [flush_pending] (the drain, part A, tot_bits-conserving).  Because
    [flush_pending] conserves [tot_bits] and the drained-output prefix is
    a whole number of bytes, [ceil8] factors through the
    [8*|zs_out|] summand, so the per-event potential step is EXACTLY the
    per-block writer step of part H:

        ceil8 (tot_bits after) <= ceil8 (tot_bits before)
                                  + 8*(fe_end - fe_start) + 40.

    Stated over an [EvOk] snapshot with a PRESENT stored buffer
    ([0 <= blockstart], which is where [EvOk]'s window clause already
    lives).  The walk-supplied per-snapshot facts (zeroed counters, fresh
    BL freqs, blcount support, tree-length nonnegativity, memLevel-8
    [sym_end]) are explicit hypotheses — the contract q5's walk discharges
    at each flush site.  The [buf = None] (post-slide) case is deferred to
    the walk's symbol/byte bound (see the lane report).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  SwWin SwEv G3Event ZReproG6A ZReproG6H.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** [tot_bits]'s [ceil8] splits off the drained-byte multiple. *)
Lemma tot_bits_ceil8 : forall s, 0 <= bw_valid (zbw s) ->
  ceil8 (tot_bits s) = 8 * zlen (zs_out (d_strm s)) + ceil8 (zbits (zbw s)).
Proof.
  intros s Hv. unfold tot_bits.
  pose proof (zlen_nonneg (zs_out (d_strm s))) as Hq.
  rewrite Z.add_comm.
  rewrite (ceil8_add_mul (zbits (zbw s)) (zlen (zs_out (d_strm s)))).
  ring.
Qed.

(** The stored buffer's length at a present block start. *)
Lemma flush_buf_len : forall l,
  0 <= ls_blockstart l -> ls_blockstart l <= ls_strstart l ->
  zlen (win_take (ls_window l) (ls_blockstart l)
          (ls_strstart l - ls_blockstart l))
  = ls_strstart l - ls_blockstart l.
Proof.
  intros l Hbs Hle. apply win_take_zlen. lia.
Qed.

Theorem flush_block_only_acct : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g ->
  dg_strategy g = 0 ->
  dg_sym_end g <= 49149 ->
  bwv (ts_bw (d_ts (fe_s ev))) ->
  0 <= zs_availout (d_strm (fe_s ev)) ->
  0 <= ls_blockstart (d_ls (fe_s ev)) ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
  let s' := flush_block_only (fe_last ev) (fe_s ev) in
  tot_bits (fe_s ev) <= tot_bits s'
  /\ ceil8 (tot_bits s')
     <= ceil8 (tot_bits (fe_s ev)) + 8 * (fe_end ev - fe_start ev) + 40
  /\ bwv (zbw s')
  /\ zs_availout (d_strm s')
     = zs_availout (d_strm (fe_s ev))
       - (zlen (zs_out (d_strm s')) - zlen (zs_out (d_strm (fe_s ev))))
  /\ zlen (zs_out (d_strm (fe_s ev))) <= zlen (zs_out (d_strm s'))
  /\ 0 <= zs_availout (d_strm s').
Proof.
  intros g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo Hbs
         Hol0 Hsl0 Hbl0 HblZ HnnL HnnD s'.
  destruct HE as (Ecfg & Ewrap & Hbuf & Hfreq & Henc & Hsn & Hspan & Hend
                  & Hres & Hspan_eq & Hwin & Hlast01).
  set (s := fe_s ev) in *.
  (* token count from the memLevel-8 sym_end and the buffer extent *)
  assert (Hlen : Z.of_nat (length (fe_toks ev)) <= 16383).
  { pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext. lia. }
  (* the level>=1 dispatch fires; stored buffer present *)
  set (l := d_ls s) in *.
  set (bs := ls_blockstart l) in *.
  set (slen := ls_strstart l - bs) in *.
  assert (Hbble : bs <= ls_strstart l) by lia.
  assert (Hlevg : 0 < dg_level (d_cfg s)) by (rewrite Ecfg; exact Hlev).
  assert (Hstratg : dg_strategy (d_cfg s) = 0) by (rewrite Ecfg; exact Hstrat).
  set (buf := if Z.leb 0 bs
              then Some (win_take (ls_window l) bs slen) else None) in *.
  set (dat := win_take (ls_window l) bs slen) in *.
  assert (Ebuf : buf = Some dat)
    by (unfold buf; replace (Z.leb 0 bs) with true
          by (symmetry; apply Z.leb_le; lia); reflexivity).
  set (r := tr_flush_block (Some dat) slen (fe_last ev) (dg_level (d_cfg s))
              0 (zs_datatype (d_strm s)) (d_ts s)) in *.
  (* the tr_flush_block writer step (part H) *)
  destruct (tr_flush_block_len (d_ts s) (fe_toks ev) dat slen (fe_last ev)
              (dg_level (d_cfg s)) (zs_datatype (d_strm s))
              Hbwv ltac:(lia) Hlevg Hbuf Henc Hlen Hol0 Hsl0 Hbl0 Hfreq HblZ
              HnnL HnnD
              ltac:(apply flush_buf_len; lia) ltac:(lia))
    as (Hmono & Hstep & Hwf & _).
  fold r in Hmono, Hstep, Hwf.
  (* the flush_block_only state, opened to flush_pending of s2 *)
  unfold s', flush_block_only. cbv zeta.
  fold l. fold bs. fold slen. fold dat. fold buf.
  rewrite Ebuf. rewrite Hstratg.
  change (tr_flush_block (Some dat) slen (fe_last ev) (dg_level (d_cfg s))
            0 (zs_datatype (d_strm s)) (d_ts s))
    with r.
  set (s2 := setD_ls (setL_blockstart (ls_strstart l) l)
               (setD_ts (snd r)
                  (setD_strm (setZ_datatype (fst r) (d_strm s)) s))) in *.
  (* projections of s2 *)
  assert (E2ts : ts_bw (d_ts s2) = ts_bw (snd r))
    by (unfold s2, setD_ls, setD_ts, setD_strm; reflexivity).
  assert (E2out : zs_out (d_strm s2) = zs_out (d_strm s))
    by (unfold s2, setD_ls, setD_ts, setD_strm, setZ_datatype; reflexivity).
  assert (E2avo : zs_availout (d_strm s2) = zs_availout (d_strm s))
    by (unfold s2, setD_ls, setD_ts, setD_strm, setZ_datatype; reflexivity).
  assert (E2zbw : zbw s2 = ts_bw (snd r)) by (unfold zbw; exact E2ts).
  (* flush_pending accounting (part A) *)
  destruct (flush_pending_acct s2
              ltac:(rewrite E2zbw; unfold bwv in *; exact Hwf)
              ltac:(rewrite E2avo; exact Havo))
    as (Fcons & Fbwv & Favo & Fmono & Favo0 & _ & _ & _ & _ & _ & _).
  (* tot_bits of s2, and of s *)
  assert (Hts2 : tot_bits s2 = 8 * zlen (zs_out (d_strm s)) + zbits (ts_bw (snd r))).
  { unfold tot_bits. rewrite E2out, E2zbw. reflexivity. }
  assert (Hts : tot_bits s = 8 * zlen (zs_out (d_strm s)) + zbits (ts_bw (d_ts s)))
    by (unfold tot_bits, zbw; reflexivity).
  pose proof (zlen_nonneg (zs_out (d_strm s))) as HQnn.
  (* the four conclusions *)
  assert (Hspan' : fe_end ev - fe_start ev = slen)
    by (unfold slen, bs, l; exact Hspan_eq).
  split; [|split; [|split; [|split; [|split]]]].
  - (* monotone *)
    rewrite Fcons, Hts2, Hts. lia.
  - (* ceil8 step *)
    rewrite Fcons, Hts2, Hts.
    rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s))) (zbits (ts_bw (snd r)))).
    rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s))) (zbits (ts_bw (d_ts s)))).
    rewrite !(ceil8_add_mul _ (zlen (zs_out (d_strm s)))).
    rewrite Hspan'. lia.
  - (* bwv of the final writer *)
    exact Fbwv.
  - (* availout relation *)
    rewrite Favo, E2avo, E2out. reflexivity.
  - (* output grows *)
    rewrite <- E2out at 1. exact Fmono.
  - (* availout nonneg *)
    exact Favo0.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions flush_block_only_acct.
Unset Printing All.
