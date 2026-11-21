(** * SwArm3 — the slow-path walk, part W3e: the DEFER arm of [ds_body]
      (deflate.c:2007-2014 — no tally, remember the candidate, advance one).

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The arm fires when the PREVIOUS candidate is not worth emitting
    ([prev_length < MIN_MATCH] or beaten by the new one) and there is no
    pending literal.  It sets [match_avail = 1] (the byte at the OLD
    [strstart] becomes the pending literal) and advances.  [DsInv] is
    restored with the same token list: the tally point
    [strstart - matchavail] is unchanged ([+1 -1]), and the new candidate's
    [MatchCand] comes from the dispatch facts — the arm's own guard kills
    the routed-to-arm-1 disjunct.

    The lemma takes the DISPATCH-POINT facts (SwArmPre's [dsb_top_facts]
    conclusions) as premises over an abstract [l2], so SwLoop can glue
    prelude and arm without this file recomputing [dsb_l2]. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac lsimp :=
  cbn [ls_window ls_prev ls_head ls_insh ls_blockstart ls_matchlen
       ls_prevmatch ls_matchavail ls_strstart ls_matchstart ls_lookahead
       ls_prevlen ls_insert ls_highwater ls_windowsize
       setL_window setL_prev setL_head setL_insh setL_blockstart
       setL_matchlen setL_prevmatch setL_matchavail setL_strstart
       setL_matchstart setL_lookahead setL_prevlen setL_insert
       setL_highwater setL_windowsize
       d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm
       fst snd].

Theorem dsb_arm3_inv : forall g wbits hbits wrap slid Ins Ins2 toks s l2,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  1 <= ls_lookahead (d_ls s) ->
  ChainInv g (ls_window l2) (ls_prev l2) (ls_head l2)
           (ls_strstart l2) (ls_lookahead l2) Ins2 ->
  (forall p, Ins2 p -> p <= ls_strstart (d_ls s)) ->
  ls_window l2 = ls_window (d_ls s) ->
  ls_strstart l2 = ls_strstart (d_ls s) ->
  ls_lookahead l2 = ls_lookahead (d_ls s) ->
  ls_blockstart l2 = ls_blockstart (d_ls s) ->
  ls_matchavail l2 = ls_matchavail (d_ls s) ->
  ls_windowsize l2 = ls_windowsize (d_ls s) ->
  ls_insert l2 = 0 ->
  (MIN_MATCH <= ls_lookahead (d_ls s) ->
   ls_insh l2 = h3 g (ls_window (d_ls s)) (ls_strstart (d_ls s))) ->
  0 <= ls_matchlen l2 <= MAX_MATCH ->
  ls_prevlen l2 = ls_matchlen (d_ls s) ->
  (MIN_MATCH <= ls_matchlen l2 ->
   ls_matchlen l2 <= ls_lookahead (d_ls s)
   /\ (ls_matchlen l2 <= ls_prevlen l2
       \/ (0 <= slid + ls_matchstart l2
           /\ 1 <= ls_strstart (d_ls s) - ls_matchstart l2 <= dg_max_dist g
           /\ forall k, 0 <= k < ls_matchlen l2 ->
                nth (Z.to_nat (slid + ls_matchstart l2 + k))
                    (zs_done (d_strm s)) 0
                = nth (Z.to_nat (slid + ls_strstart (d_ls s) + k))
                      (zs_done (d_strm s)) 0))) ->
  ((Z.leb MIN_MATCH (ls_prevlen l2))
   && (Z.leb (ls_matchlen l2) (ls_prevlen l2))) = false ->
  ls_matchavail l2 = 0 ->
  DsInv g wrap slid Ins2 toks
    (setD_ls (setL_lookahead (ls_lookahead l2 - 1)
               (setL_strstart (ls_strstart l2 + 1)
                 (setL_matchavail 1 l2))) (setD_ls l2 s)).
Proof.
  intros g wbits hbits wrap slid Ins Ins2 toks s l2
         Hg HI Hla1 Hcinv2 Hhi2 Ew Ess Ela Ebs Ema Ews Eins Einsh Hmlb Epl
         Hdisp Hguard Hma0.
  pose proof (di_win _ _ _ _ _ _ HI) as HW.
  pose proof (wi_ss _ _ _ _ HW) as Hss.
  pose proof (wi_la _ _ _ _ HW) as Hla.
  pose proof (wi_room _ _ _ _ HW) as Hroom.
  pose proof (wi_wsize _ _ _ _ HW) as Hwsz.
  pose proof (wi_slid _ _ _ _ HW) as Hslid.
  pose proof (wi_done _ _ _ _ HW) as Hdone.
  pose proof (di_ma _ _ _ _ _ _ HI) as Hma01.
  (* the pre-state matchavail is 0 through the l2 equation *)
  assert (Hma0s : ls_matchavail (d_ls s) = 0) by congruence.
  constructor; lsimp.
  - exact (di_cfg _ _ _ _ _ _ HI).
  - exact (di_wrap _ _ _ _ _ _ HI).
  - (* WinInv at (ss+1, la-1) *)
    destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    constructor; lsimp; try lia; try congruence;
      try assumption.
    intros i Hi. rewrite Ew. apply W10.
    rewrite Ess, Ela in Hi. lia.
  - exact (di_ck _ _ _ _ _ _ HI).
  - (* ChainCl at the advanced state *)
    constructor; lsimp.
    + (* flr_advance to (ss+1, la-1) *)
      eapply (flr_advance g wbits hbits);
        first [ exact Hcinv2
              | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
              | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
              | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
              | exact (go_maxd _ (g2_geom _ _ _ Hg))
              | lia ].
    + intros p Hp. pose proof (Hhi2 _ Hp). rewrite Ess. lia.
    + exact Eins.
    + (* sync rolls forward *)
      unfold SyncOK. lsimp.
      intros _ Hla3'.
      rewrite Ela in Hla3'.
      rewrite Ess, Ew.
      rewrite (Einsh ltac:(unfold MIN_MATCH in *; lia)).
      replace (ls_strstart (d_ls s) + 1 + 2)
        with (ls_strstart (d_ls s) + 3) by lia.
      apply (h3_roll g wbits hbits _ _ Hg).
  - exact (di_buf _ _ _ _ _ _ HI).
  - exact (di_freq _ _ _ _ _ _ HI).
  - exact (di_enc _ _ _ _ _ _ HI).
  - (* the value spine: tally point unchanged *)
    pose proof (di_res _ _ _ _ _ _ HI) as Hres.
    rewrite Ebs, Ess.
    replace (slid + (ls_strstart (d_ls s) + 1) - 1)
      with (slid + ls_strstart (d_ls s) - ls_matchavail (d_ls s))
      by lia.
    exact Hres.
  - rewrite Ebs. exact (di_bb0 _ _ _ _ _ _ HI).
  - pose proof (di_bble _ _ _ _ _ _ HI). rewrite Ebs, Ess. lia.
  - right. reflexivity.
  - intros _. rewrite Ess. lia.
  - (* the deferred candidate *)
    unfold MatchCand. lsimp.
    intros Hml3.
    destruct (Hdisp Hml3) as [Hmlla Hout].
    destruct Hout as [Hle|Hval].
    + (* impossible: the guard says the previous candidate lost *)
      exfalso.
      apply andb_false_iff in Hguard.
      destruct Hguard as [Hb|Hb]; apply Z.leb_gt in Hb;
        unfold MIN_MATCH in *; lia.
    + destruct Hval as (Hms0 & Hd & Hag).
      repeat split; try (rewrite Ess; lia); try lia.
      intros k Hk.
      rewrite Ess.
      replace (ls_strstart (d_ls s) + 1 - 1)
        with (ls_strstart (d_ls s)) by lia.
      apply Hag. exact Hk.
  - pose proof (di_ml _ _ _ _ _ _ HI) as Hmls. rewrite Epl. exact Hmls.
  - exact Hmlb.
  - exact (di_sn _ _ _ _ _ _ HI).
Qed.

Print Assumptions dsb_arm3_inv.
