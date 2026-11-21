(** * SwArm1b — the slow-path walk, part W3g(ii): the MATCH-TALLY arm of
      [ds_body] (deflate.c:1967-1993 — tally the PREVIOUS trip's match,
      insert every covered position, advance past it, maybe flush).

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    THE VALUE-SPINE FACT this arm turns on: at entry the previous trip
    DEFERRED, so [match_avail = 1] and the tally point sits at
    [strstart - 1] — exactly where the emitted match's cover begins.  The
    match token extends the resolution by [prev_length] bytes
    ([copy_n_slice] + the invariant's [MatchCand] byte agreement), and the
    arm's exit bookkeeping ([strstart += prev_length - 1],
    [match_avail = 0]) lands the tally point at the new resolution end.

    The chain rides SwArm1a's [ds_insert_walk] (anchor [(ss_cur, S - ss_cur)],
    [S] the dispatch [strstart + lookahead]), plus one un-inserted
    [flr_advance] step for the final [strstart++]; that last step's hash
    sync is the walk's [InsSync] disjunct — stale is only possible past
    [max_insert], where the post-arm lookahead is under [MIN_MATCH]. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwArm2 SwArm1a.
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

Theorem dsb_arm1_inv : forall g wbits hbits wrap slid Ins Ins2 toks s l2,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
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
  ls_prevlen l2 = ls_matchlen (d_ls s) ->
  ls_prevmatch l2 = ls_matchstart (d_ls s) ->
  ((Z.leb MIN_MATCH (ls_prevlen l2))
   && (Z.leb (ls_matchlen l2) (ls_prevlen l2))) = true ->
  let s2 := setD_ls l2 s in
  let tt := tr_tally_dist (ls_strstart l2 - 1 - ls_prevmatch l2)
                          (ls_prevlen l2 - MIN_MATCH)
                          (dg_sym_end g) (d_ts s2) in
  let l3 := setL_prevlen (ls_prevlen l2 - 2)
              (setL_lookahead (ls_lookahead l2 - (ls_prevlen l2 - 1)) l2) in
  let l4 := ds_insert (Z.to_nat (ls_prevlen l3) + 1) g
              (ls_strstart l2 + ls_lookahead l2 - MIN_MATCH) l3 in
  let l5 := setL_strstart (ls_strstart l4 + 1)
              (setL_matchlen (MIN_MATCH - 1) (setL_matchavail 0 l4)) in
  let s3 := setD_ls l5 (setD_ts (snd tt) s2) in
  exists Ins' toks' evs,
    Forall (EvOk g wrap (zs_done (d_strm s))) evs
    /\ ( (fst tt = false /\ evs = []
          /\ DsInv g wrap slid Ins' toks' s3
          /\ zs_done (d_strm s3) = zs_done (d_strm s)
          /\ zs_in (d_strm s3) = zs_in (d_strm s)
          /\ ls_lookahead (d_ls s3)
             = ls_lookahead (d_ls s) - (ls_prevlen l2 - 1)
          /\ ls_strstart (d_ls s3)
             = ls_strstart (d_ls s) + ls_prevlen l2 - 1
          /\ ls_blockstart (d_ls s3) = ls_blockstart (d_ls s)
          /\ ts_bw (d_ts s3) = ts_bw (d_ts s)
          /\ zs_out (d_strm s3) = zs_out (d_strm s)
          /\ zs_availout (d_strm s3) = zs_availout (d_strm s)
          /\ toks' = toks ++ [TMatch (ls_prevlen l2)
                                (ls_strstart l2 - 1 - ls_prevmatch l2)])
       \/ (exists ev, fst tt = true /\ evs = [ev] /\ fe_last ev = 0
          /\ fe_s ev = s3
          /\ fe_start ev = slid + ls_blockstart (d_ls s)
          /\ fe_end ev = slid + (ls_strstart (d_ls s) + ls_prevlen l2 - 1)
          /\ ls_blockstart (d_ls (flush_block_only 0 s3))
             = ls_strstart (d_ls s) + ls_prevlen l2 - 1
          /\ ts_bw (d_ts (fe_s ev)) = ts_bw (d_ts s)
          /\ zs_out (d_strm (fe_s ev)) = zs_out (d_strm s)
          /\ zs_availout (d_strm (fe_s ev)) = zs_availout (d_strm s)
          /\ DsInv g wrap slid Ins' toks' (flush_block_only 0 s3)
          /\ zs_done (d_strm (flush_block_only 0 s3)) = zs_done (d_strm s)
          /\ zs_in (d_strm (flush_block_only 0 s3)) = zs_in (d_strm s)
          /\ ls_lookahead (d_ls (flush_block_only 0 s3))
             = ls_lookahead (d_ls s) - (ls_prevlen l2 - 1)
          /\ ls_strstart (d_ls (flush_block_only 0 s3))
             = ls_strstart (d_ls s) + ls_prevlen l2 - 1
          /\ fe_toks ev = toks ++ [TMatch (ls_prevlen l2)
                                     (ls_strstart l2 - 1 - ls_prevmatch l2)]
          /\ toks' = []) ).
Proof.
  intros g wbits hbits wrap slid Ins Ins2 toks s l2
         Hg HI Hcinv2 Hhi2 Ew Ess Ela Ebs Ema Ews Eins Einsh Epl Epm Hguard.
  (* ---- the ambient facts ---- *)
  pose proof (di_win _ _ _ _ _ _ HI) as HW.
  pose proof (wi_ss _ _ _ _ HW) as Hss.
  pose proof (wi_la _ _ _ _ HW) as Hla.
  pose proof (wi_room _ _ _ _ HW) as Hroom.
  pose proof (wi_wsize _ _ _ _ HW) as Hwsz.
  pose proof (wi_slid _ _ _ _ HW) as Hslid.
  pose proof (wi_done _ _ _ _ HW) as Hdone.
  pose proof (buftoks_extent _ _ _ _ (di_buf _ _ _ _ _ _ HI)) as Hext.
  pose proof (di_sn _ _ _ _ _ _ HI) as Hsn.
  pose proof (g2_se_hi _ _ _ Hg) as Hsehi.
  pose proof (g2_se_lo _ _ _ Hg) as Hselo.
  pose proof (g2_se_mod _ _ _ Hg) as Hsemod.
  pose proof (g2_u16 _ _ _ Hg) as Hu16ws.
  pose proof (go_maxd _ (g2_geom _ _ _ Hg)) as Emaxd.
  pose proof (Z_div_mod_eq_full (dg_sym_end g) 3) as Hse3.
  (* the guard, split *)
  apply andb_true_iff in Hguard. destruct Hguard as [Hg1 _].
  apply Z.leb_le in Hg1. rename Hg1 into HplMM.
  pose proof HplMM as Hpl3'. unfold MIN_MATCH in Hpl3'.
  pose proof (di_ml _ _ _ _ _ _ HI) as Hmls.  (* matchlen (d_ls s) range *)
  pose proof Hmls as Hmls'. unfold MAX_MATCH in Hmls'.
  (* the previous candidate, from the invariant *)
  destruct (di_cand _ _ _ _ _ _ HI ltac:(rewrite <- Epl; exact HplMM))
    as (Hma1s & Hms0 & Hdist & HmlMM & HmlLa & Hag).
  pose proof (di_ma1 _ _ _ _ _ _ HI Hma1s) as Hss1.
  assert (Hdist2 : 1 <= ls_strstart l2 - 1 - ls_prevmatch l2
                   <= dg_max_dist g)
    by (rewrite Ess, Epm; exact Hdist).
  (* ---- the tally step ---- *)
  assert (Ets2 : d_ts (setD_ls l2 s) = d_ts s) by reflexivity.
  cbv zeta. rewrite Ets2.
  destruct (tr_tally_dist_step (ls_strstart l2 - 1 - ls_prevmatch l2)
              (ls_prevlen l2 - MIN_MATCH) (dg_sym_end g) (d_ts s) toks
              ltac:(lia) ltac:(lia)
              (di_buf _ _ _ _ _ _ HI) (di_freq _ _ _ _ _ _ HI)
              ltac:(rewrite u16_id by lia; lia))
    as (Hbuf' & Hsn' & Hfreq' & Hflag & Hframe).
  destruct Hframe as (FtrBL & Fmax & Fblc & Fheap & Fhl & Fhm & Fdep
                      & Fopt & Fstat & Fmat & Fbw).
  set (tt := tr_tally_dist (ls_strstart l2 - 1 - ls_prevmatch l2)
               (ls_prevlen l2 - MIN_MATCH) (dg_sym_end g) (d_ts s)) in *.
  (* the clean token *)
  assert (Etok : toks ++ [TMatch (u8 (ls_prevlen l2 - MIN_MATCH) + 3)
                                 (u16 (ls_strstart l2 - 1 - ls_prevmatch l2))]
               = toks ++ [TMatch (ls_prevlen l2)
                                 (ls_strstart l2 - 1 - ls_prevmatch l2)]).
  { rewrite u8_id by (unfold MIN_MATCH in *; lia).
    rewrite u16_id by lia.
    repeat f_equal. unfold MIN_MATCH. lia. }
  assert (Henc' : cEnc (toks ++ [TMatch (ls_prevlen l2)
                                   (ls_strstart l2 - 1 - ls_prevmatch l2)])).
  { apply Forall_app. split; [exact (di_enc _ _ _ _ _ _ HI)|].
    constructor; [|apply Forall_nil].
    cbn [tok_enc]. rewrite <- Epl in Hmls'.
    split; [split|split]; unfold MIN_MATCH, MAX_MATCH; lia. }
  (* ---- the resolution extension ---- *)
  assert (Hres' : resolve (firstn (Z.to_nat (slid + ls_blockstart (d_ls s)))
                    (zs_done (d_strm s)))
                    (toks ++ [TMatch (ls_prevlen l2)
                                (ls_strstart l2 - 1 - ls_prevmatch l2)])
                = Some (firstn (Z.to_nat (slid + ls_strstart (d_ls s) - 1
                                          + ls_prevlen l2))
                          (zs_done (d_strm s)))).
  { rewrite resolve_app.
    pose proof (di_res _ _ _ _ _ _ HI) as Hres.
    rewrite Hma1s in Hres.
    rewrite Hres.
    cbn [resolve resolve_tok].
    assert (Hzl : zlen (firstn (Z.to_nat (slid + ls_strstart (d_ls s) - 1))
                          (zs_done (d_strm s)))
                = slid + ls_strstart (d_ls s) - 1).
    { unfold zlen. rewrite length_firstn. unfold zlen in Hdone. lia. }
    rewrite Hzl.
    replace ((1 <=? ls_strstart l2 - 1 - ls_prevmatch l2)
             && (ls_strstart l2 - 1 - ls_prevmatch l2
                 <=? slid + ls_strstart (d_ls s) - 1))
      with true
      by (symmetry; apply andb_true_iff;
          split; apply Z.leb_le; lia).
    cbn [resolve].
    f_equal.
    apply copy_n_slice.
    - lia.
    - lia.
    - lia.
    - rewrite <- Epl in HmlLa. lia.
    - intros k Hk.
      replace (slid + ls_strstart (d_ls s) - 1
               - (ls_strstart l2 - 1 - ls_prevmatch l2) + k)
        with (slid + ls_matchstart (d_ls s) + k) by lia.
      replace (slid + ls_strstart (d_ls s) - 1 + k)
        with (slid + (ls_strstart (d_ls s) - 1) + k) by lia.
      apply Hag. rewrite Epl in Hk. lia. }
  (* ---- the insert walk ---- *)
  set (l3 := setL_prevlen (ls_prevlen l2 - 2)
               (setL_lookahead (ls_lookahead l2 - (ls_prevlen l2 - 1)) l2)).
  rewrite <- Epl in HmlLa.  (* now: prevlen l2 <= lookahead (d_ls s) + 1 *)
  assert (HC3 : ChainInv g (ls_window l3) (ls_prev l3) (ls_head l3)
                  (ls_strstart l3)
                  (ls_strstart l2 + ls_lookahead l2 - ls_strstart l3) Ins2).
  { unfold l3; lsimp.
    replace (ls_strstart l2 + ls_lookahead l2 - ls_strstart l2)
      with (ls_lookahead l2) by lia.
    exact Hcinv2. }
  destruct (ds_insert_walk (Z.to_nat (ls_prevlen l3) + 1) g wbits hbits
              (ls_strstart l2 + ls_lookahead l2) Ins2 l3 Hg HC3
              ltac:(unfold l3; lsimp; intros p Hp;
                    rewrite Ess; exact (Hhi2 p Hp))
              ltac:(destruct (Z.le_gt_cases MIN_MATCH (ls_lookahead (d_ls s)))
                      as [Hla3|Hla3];
                    [ left; unfold l3; lsimp;
                      rewrite (Einsh Hla3), <- Ew, <- Ess; reflexivity
                    | right; unfold l3; lsimp;
                      unfold MIN_MATCH in *; lia ])
              ltac:(unfold l3; lsimp; lia)
              ltac:(unfold l3; lsimp; lia)
              ltac:(unfold l3; lsimp;
                    rewrite Nat2Z.inj_add, Z2Nat.id by lia;
                    cbn [Z.of_nat]; lia)
              ltac:(unfold l3; lsimp; lia)
              ltac:(lia))
    as (Ins4 & HC4 & Hhi4 & Hsync4 & Ew4 & Ebs4 & Ema4 & Eml4 & Ems4
        & Ela4 & Ews4 & Eins4 & Epl4 & Ess4).
  cbv zeta in HC4, Hhi4, Hsync4, Ew4, Ebs4, Ema4, Eml4, Ems4, Ela4,
    Ews4, Eins4, Epl4, Ess4.
  set (l4 := ds_insert (Z.to_nat (ls_prevlen l3) + 1) g
               (ls_strstart l2 + ls_lookahead l2 - MIN_MATCH) l3) in *.
  (* plain-Z forms of the walk equations *)
  assert (Ess4' : ls_strstart l4 = ls_strstart l2 + ls_prevlen l2 - 2)
    by (rewrite Ess4; unfold l3; lsimp; lia).
  assert (Ela4' : ls_lookahead l4
                  = ls_lookahead l2 - (ls_prevlen l2 - 1))
    by (rewrite Ela4; unfold l3; lsimp; reflexivity).
  set (l5 := setL_strstart (ls_strstart l4 + 1)
               (setL_matchlen (MIN_MATCH - 1) (setL_matchavail 0 l4))).
  (* ---- the l5 field dictionary ---- *)
  assert (E5w : ls_window l5 = ls_window (d_ls s))
    by (unfold l5; lsimp; rewrite Ew4; unfold l3; lsimp; exact Ew).
  assert (E5ss : ls_strstart l5 = ls_strstart (d_ls s) + ls_prevlen l2 - 1)
    by (unfold l5; lsimp; rewrite Ess4'; lia).
  assert (E5la : ls_lookahead l5
                 = ls_lookahead (d_ls s) - (ls_prevlen l2 - 1))
    by (unfold l5; lsimp; rewrite Ela4'; lia).
  assert (E5bs : ls_blockstart l5 = ls_blockstart (d_ls s))
    by (unfold l5; lsimp; rewrite Ebs4; unfold l3; lsimp; exact Ebs).
  assert (E5ws : ls_windowsize l5 = ls_windowsize (d_ls s))
    by (unfold l5; lsimp; rewrite Ews4; unfold l3; lsimp; exact Ews).
  assert (E5ins : ls_insert l5 = 0)
    by (unfold l5; lsimp; rewrite Eins4; unfold l3; lsimp; exact Eins).
  assert (E5ma : ls_matchavail l5 = 0)
    by (unfold l5; lsimp; reflexivity).
  assert (E5ml : ls_matchlen l5 = MIN_MATCH - 1)
    by (unfold l5; lsimp; reflexivity).
  assert (E5pl : ls_prevlen l5 = 0)
    by (unfold l5; lsimp; exact Epl4).
  (* ---- WinInv at l5 ---- *)
  assert (HW5 : WinInv g slid l5 (d_strm s)).
  { destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    constructor;
      rewrite ?E5w, ?E5ss, ?E5la, ?E5ws;
      try lia; try assumption.
    intros i Hi. apply W10. lia. }
  (* ---- ChainCl at l5 ---- *)
  assert (HCI5 : ChainInv g (ls_window l4) (ls_prev l4) (ls_head l4)
                   (ls_strstart l4 + 1) (ls_lookahead l4) Ins4).
  { eapply (flr_advance g wbits hbits);
      first [ exact HC4
            | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
            | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
            | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
            | exact (go_maxd _ (g2_geom _ _ _ Hg))
            | lia ]. }
  assert (HCC5 : ChainCl g Ins4 l5).
  { constructor.
    - unfold l5; lsimp. exact HCI5.
    - intros p Hp. pose proof (Hhi4 _ Hp).
      unfold l5; lsimp. lia.
    - exact E5ins.
    - unfold SyncOK. unfold l5; lsimp.
      intros _ Hla3'.
      destruct Hsync4 as [Hs4|Hp4].
      + rewrite Hs4.
        replace (ls_strstart l4 + 1 + 2)
          with (ls_strstart l4 + 3) by lia.
        apply (h3_roll g wbits hbits _ _ Hg).
      + exfalso. unfold MIN_MATCH in *. lia. }
  (* ---- assemble, by flush flag ---- *)
  set (s3 := setD_ls l5 (setD_ts (snd tt) (setD_ls l2 s))).
  assert (E3ls : d_ls s3 = l5) by reflexivity.
  assert (E3ts : d_ts s3 = snd tt) by reflexivity.
  assert (E3strm : d_strm s3 = d_strm s) by reflexivity.
  destruct (fst tt) eqn:Eflag.
  - (* FLUSH *)
    destruct (flush_block_only_step g wbits hbits wrap slid
                (toks ++ [TMatch (ls_prevlen l2)
                            (ls_strstart l2 - 1 - ls_prevmatch l2)]) s3 0 Hg
                ltac:(unfold s3; lsimp; exact (di_cfg _ _ _ _ _ _ HI))
                ltac:(unfold s3; lsimp; exact (di_wrap _ _ _ _ _ _ HI))
                ltac:(rewrite E3ls, E3strm; exact HW5)
                ltac:(rewrite E3strm; exact (di_ck _ _ _ _ _ _ HI))
                ltac:(rewrite E3ts; rewrite <- Etok; exact Hbuf')
                ltac:(rewrite E3ts; rewrite <- Etok; exact Hfreq')
                Henc'
                ltac:(rewrite E3ts, Hsn'; lia)
                ltac:(lia)
                ltac:(rewrite E3ls, E5bs; exact (di_bb0 _ _ _ _ _ _ HI))
                ltac:(rewrite E3ls, E5bs, E5ss;
                      pose proof (di_bble _ _ _ _ _ _ HI);
                      rewrite Hma1s in *; lia)
                ltac:(rewrite E3ls, E3strm, E5bs, E5ss;
                      replace (slid + (ls_strstart (d_ls s)
                                       + ls_prevlen l2 - 1))
                        with (slid + ls_strstart (d_ls s) - 1
                              + ls_prevlen l2) by lia;
                      exact Hres'))
      as (HEv & Fcfg & Fwrap & FW & FK & FBuf & FFreq & FSn & Fbs & Fss
          & Fla & Fma & Fml & Fpl & Fpm & Fms & Fwin & Fprev & Fhead
          & Finsh & Fins & Fws & Fdn & Fin & Fti & Favo).
    cbv zeta in HEv.
    exists Ins4, [],
      [{| fe_s := s3; fe_last := 0;
          fe_start := slid + ls_blockstart (d_ls s3);
          fe_end := slid + ls_strstart (d_ls s3);
          fe_toks := toks ++ [TMatch (ls_prevlen l2)
                                (ls_strstart l2 - 1 - ls_prevmatch l2)] |}].
    split.
    { constructor; [|apply Forall_nil].
      rewrite Fdn, E3strm in HEv. exact HEv. }
    right.
    exists {| fe_s := s3; fe_last := 0;
              fe_start := slid + ls_blockstart (d_ls s3);
              fe_end := slid + ls_strstart (d_ls s3);
              fe_toks := toks ++ [TMatch (ls_prevlen l2)
                                    (ls_strstart l2 - 1 - ls_prevmatch l2)] |}.
    repeat apply conj.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn [fe_start]. rewrite E3ls, E5bs. reflexivity.
    + cbn [fe_end]. rewrite E3ls, E5ss. reflexivity.
    + rewrite Fbs, E3ls, E5ss. reflexivity.
    + cbn [fe_s]. rewrite E3ts. exact Fbw.
    + cbn [fe_s]. rewrite E3strm. reflexivity.
    + cbn [fe_s]. rewrite E3strm. reflexivity.
    + (* DsInv at the flushed state *)
      constructor.
      * exact Fcfg.
      * exact Fwrap.
      * exact FW.
      * exact FK.
      * constructor.
        -- rewrite Fwin, Fprev, Fhead, Fss, Fla, E3ls.
           exact (cc_inv _ _ _ HCC5).
        -- rewrite Fss, E3ls.
           exact (cc_hi _ _ _ HCC5).
        -- rewrite Fins, E3ls. exact E5ins.
        -- unfold SyncOK.
           rewrite Finsh, Fwin, Fss, Fla, Fins, E3ls.
           exact (cc_sync _ _ _ HCC5).
      * exact FBuf.
      * exact FFreq.
      * apply Forall_nil.
      * cbn [resolve].
        rewrite Fbs, Fss, Fma, Fdn, E3ls, E3strm, E5ma.
        do 2 f_equal. lia.
      * rewrite Fbs, E3ls, E5ss. lia.
      * rewrite Fbs, Fss, Fma, E3ls, E5ss, E5ma. lia.
      * rewrite Fma, E3ls, E5ma. left. reflexivity.
      * rewrite Fma, E3ls, E5ma. intros E. lia.
      * unfold MatchCand. intros Hml3.
        rewrite Fml, E3ls, E5ml in Hml3.
        unfold MIN_MATCH in Hml3. exfalso. lia.
      * rewrite Fpl, E3ls, E5pl. unfold MAX_MATCH. lia.
      * rewrite Fml, E3ls, E5ml. unfold MIN_MATCH, MAX_MATCH. lia.
      * rewrite FSn. lia.
    + rewrite Fdn, E3strm. reflexivity.
    + rewrite Fin, E3strm. reflexivity.
    + rewrite Fla, E3ls, E5la. reflexivity.
    + rewrite Fss, E3ls, E5ss. reflexivity.
    + reflexivity.
    + reflexivity.
  - (* NO FLUSH *)
    exists Ins4,
      (toks ++ [TMatch (ls_prevlen l2)
                  (ls_strstart l2 - 1 - ls_prevmatch l2)]), [].
    split; [apply Forall_nil|].
    left.
    repeat apply conj.
    + reflexivity.
    + reflexivity.
    + (* DsInv at s3 *)
      constructor.
      * unfold s3; lsimp. exact (di_cfg _ _ _ _ _ _ HI).
      * unfold s3; lsimp. exact (di_wrap _ _ _ _ _ _ HI).
      * rewrite E3ls, E3strm. exact HW5.
      * rewrite E3strm. exact (di_ck _ _ _ _ _ _ HI).
      * rewrite E3ls. exact HCC5.
      * rewrite E3ts. rewrite <- Etok. exact Hbuf'.
      * rewrite E3ts. rewrite <- Etok. exact Hfreq'.
      * exact Henc'.
      * rewrite E3ls, E3strm, E5bs, E5ss, E5ma.
        replace (slid + (ls_strstart (d_ls s) + ls_prevlen l2 - 1) - 0)
          with (slid + ls_strstart (d_ls s) - 1 + ls_prevlen l2) by lia.
        exact Hres'.
      * rewrite E3ls, E5bs. exact (di_bb0 _ _ _ _ _ _ HI).
      * rewrite E3ls, E5bs, E5ss, E5ma.
        pose proof (di_bble _ _ _ _ _ _ HI).
        rewrite Hma1s in *. lia.
      * rewrite E3ls, E5ma. left. reflexivity.
      * rewrite E3ls, E5ma. intros E. lia.
      * unfold MatchCand. intros Hml3.
        rewrite E3ls, E5ml in Hml3.
        unfold MIN_MATCH in Hml3. exfalso. lia.
      * rewrite E3ls, E5pl. unfold MAX_MATCH. lia.
      * rewrite E3ls, E5ml. unfold MIN_MATCH, MAX_MATCH. lia.
      * rewrite E3ts, Hsn'.
        symmetry in Hflag.
        apply Z.eqb_neq in Hflag. lia.
    + rewrite E3strm. reflexivity.
    + rewrite E3strm. reflexivity.
    + rewrite E3ls, E5la. reflexivity.
    + rewrite E3ls, E5ss. reflexivity.
    + rewrite E3ls, E5bs. reflexivity.
    + rewrite E3ts. exact Fbw.
    + rewrite E3strm. reflexivity.
    + rewrite E3strm. reflexivity.
    + reflexivity.
Qed.

Print Assumptions dsb_arm1_inv.
