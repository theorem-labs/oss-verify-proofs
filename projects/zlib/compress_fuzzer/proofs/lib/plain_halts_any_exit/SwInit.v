(** * SwInit — [DsInv] holds at the one-call dispatch state.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G5, part 2.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The state [deflate_run] hands [deflate_slow] differs from
    [deflate_reset] only in fields [DsInv] never reads (status,
    lastflush, the bit writer after the wrapper header, zs_out /
    avail_out / total_out) plus the two the CALL sets ([zs_in],
    [avail_out]) and the header's adler reset.  So the lemma pins only
    the fields the invariant reads, as equations to the reset state's,
    and the one-call chain discharges them by conversion. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees CresChain
  CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac lsimp' :=
  cbn [ls_window ls_prev ls_head ls_insh ls_blockstart ls_matchlen
       ls_prevmatch ls_matchavail ls_strstart ls_matchstart ls_lookahead
       ls_prevlen ls_insert ls_highwater ls_windowsize
       setL_window setL_prev setL_head setL_insh setL_blockstart
       setL_matchlen setL_prevmatch setL_matchavail setL_strstart
       setL_matchstart setL_lookahead setL_prevlen setL_insert
       setL_highwater setL_windowsize].

Theorem dsinv_init : forall g wbits hbits wrap x s,
  GeomOk2 g wbits hbits ->
  d_cfg s = g ->
  d_wrap s = wrap ->
  d_ls s = d_ls (deflate_reset g wrap) ->
  ts_symbuf (d_ts s) = ts_symbuf (tr_init ts_new) ->
  ts_symnext (d_ts s) = ts_symnext (tr_init ts_new) ->
  ts_trees (d_ts s) TK_L = ts_trees (tr_init ts_new) TK_L ->
  ts_trees (d_ts s) TK_D = ts_trees (tr_init ts_new) TK_D ->
  zs_in (d_strm s) = x ->
  zs_done (d_strm s) = [] ->
  zs_totalin (d_strm s) = 0 ->
  CkInv wrap (d_strm s) ->
  Forall (fun b => 0 <= b < 256) x ->
  DsInv g wrap 0 (fun _ => False) [] s.
Proof.
  intros g wbits hbits wrap x s Hg Ecfg Ewrap Els Esb Esn EtL EtD
         Ein Edn Eti HK Hx.
  assert (Hls : forall (f : LSt -> Z),
            f (d_ls s) = f (d_ls (deflate_reset g wrap)))
    by (intro f; rewrite Els; reflexivity).
  constructor.
  - exact Ecfg.
  - exact Ewrap.
  - (* WinInv at the empty window *)
    constructor.
    + rewrite (Hls ls_strstart).
      unfold deflate_reset; cbn [d_ls]; unfold lm_init, clear_hash; lsimp'.
      lia.
    + rewrite (Hls ls_lookahead).
      unfold deflate_reset; cbn [d_ls]; unfold lm_init, clear_hash; lsimp'.
      lia.
    + rewrite (Hls ls_strstart), (Hls ls_lookahead), (Hls ls_windowsize).
      unfold deflate_reset; cbn [d_ls]; unfold lm_init, clear_hash; lsimp'.
      pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)). lia.
    + rewrite (Hls ls_windowsize).
      unfold deflate_reset; cbn [d_ls]; unfold lm_init, clear_hash; lsimp'.
      reflexivity.
    + lia.
    + rewrite Edn, (Hls ls_strstart), (Hls ls_lookahead).
      unfold deflate_reset; cbn [d_ls]; unfold lm_init, clear_hash; lsimp'.
      change (zlen []) with 0. lia.
    + rewrite Eti, Edn. reflexivity.
    + rewrite Edn. apply Forall_nil.
    + rewrite Ein. exact Hx.
    + rewrite (Hls ls_strstart), (Hls ls_lookahead).
      unfold deflate_reset; cbn [d_ls]; unfold lm_init, clear_hash; lsimp'.
      intros i Hi. lia.
  - exact HK.
  - (* the chain, empty *)
    rewrite Els.
    exact (chaincl_reset g wbits hbits wrap Hg).
  - (* no buffered tokens *)
    rewrite Esb, Esn.
    cbn [tr_init ts_symnext init_block].
    apply bt_nil; try reflexivity.
  - (* frequencies: END_BLOCK at 1, everything else 0 *)
    split.
    + intros i Hi. rewrite EtL.
      cbn [count_L].
      change (ts_trees (tr_init ts_new) TK_L)
        with (t_setfreq (tree_zero_freq (Z.to_nat L_CODES) 0 tzero)
                END_BLOCK 1).
      unfold t_setfreq, t_freq. cbn [tr_fc].
      destruct (Z.eqb_spec i END_BLOCK) as [->|Hne].
      * rewrite zset_same. reflexivity.
      * rewrite zset_other by exact Hne.
        change (tr_fc (tree_zero_freq (Z.to_nat L_CODES) 0 tzero) i)
          with (t_freq (tree_zero_freq (Z.to_nat L_CODES) 0 tzero) i).
        rewrite tree_zero_freq_spec.
        destruct ((0 <=? i) && (i <? 0 + Z.of_nat (Z.to_nat L_CODES)));
          reflexivity.
    + intros i Hi. rewrite EtD.
      cbn [count_D].
      change (ts_trees (tr_init ts_new) TK_D)
        with (tree_zero_freq (Z.to_nat D_CODES) 0 tzero).
      rewrite tree_zero_freq_spec.
      destruct ((0 <=? i) && (i <? 0 + Z.of_nat (Z.to_nat D_CODES)));
        reflexivity.
  - apply Forall_nil.
  - (* empty resolution *)
    rewrite Els, Edn.
    unfold deflate_reset. cbn [d_ls].
    unfold lm_init, clear_hash. lsimp'.
    cbn [resolve]. reflexivity.
  - rewrite Els. unfold deflate_reset. cbn [d_ls].
    unfold lm_init, clear_hash. lsimp'. lia.
  - rewrite Els. unfold deflate_reset. cbn [d_ls].
    unfold lm_init, clear_hash. lsimp'. lia.
  - rewrite Els. unfold deflate_reset. cbn [d_ls].
    unfold lm_init, clear_hash. lsimp'. left. reflexivity.
  - rewrite Els. unfold deflate_reset. cbn [d_ls].
    unfold lm_init, clear_hash. lsimp'. intro H. lia.
  - (* no deferred candidate *)
    unfold MatchCand.
    rewrite Els. unfold deflate_reset. cbn [d_ls].
    unfold lm_init, clear_hash. lsimp'.
    intro H. unfold MIN_MATCH in H. exfalso. lia.
  - rewrite Els. unfold deflate_reset. cbn [d_ls].
    unfold lm_init, clear_hash. lsimp'.
    unfold MIN_MATCH, MAX_MATCH. lia.
  - rewrite Els. unfold deflate_reset. cbn [d_ls].
    unfold lm_init, clear_hash. lsimp'.
    unfold MIN_MATCH, MAX_MATCH. lia.
  - rewrite Esn.
    cbn [tr_init init_block ts_symnext set_matches set_symnext
         set_statlen set_optlen set_tree set_bw].
    pose proof (g2_se_lo _ _ _ Hg). lia.
Qed.

Print Assumptions dsinv_init.
