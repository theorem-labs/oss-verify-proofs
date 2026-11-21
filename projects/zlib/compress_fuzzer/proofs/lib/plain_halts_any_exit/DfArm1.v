(** * DfArm1 — the fast-path walk, part F4: the MATCH arm of [df_body]
      ([deflate.c:1840-1887] — tally the fresh match at [strstart],
      advance by its length (inserting hash entries when short enough),
      possibly flush AFTER the advance).

    OWNER: q5-emitter (GAP7 D1).  TRUST BOUNDARY: pure Gallina.

    STRUCTURE: the two advance sub-arms (insert-covered vs skip-with-
    reseed) produce the SAME field dictionary — [strstart + len],
    [lookahead - len], matchlen 0, matchavail 0 — and differ only in
    how [ChainCl] is re-established (the insert walk vs [flr_advance]
    plus the two-byte reseed, whose [SyncOK] is [h3]'s own definition).
    A shared TAIL over an abstract [l4] does the tally/flush assembly
    once. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwArm1a SwArm2
  ZRTreeState DfArm DfIns.
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

Theorem dfb_arm1_inv : forall g wbits hbits wrap slid Ins Ins2 toks s l1,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  BsFloor g s ->
  DfSide (d_ls s) ->
  0 <= zs_availout (d_strm s) ->
  ChainInv g (ls_window l1) (ls_prev l1) (ls_head l1)
           (ls_strstart l1) (ls_lookahead l1) Ins2 ->
  (forall p, Ins2 p -> p <= ls_strstart (d_ls s)) ->
  ls_window l1 = ls_window (d_ls s) ->
  ls_strstart l1 = ls_strstart (d_ls s) ->
  ls_lookahead l1 = ls_lookahead (d_ls s) ->
  ls_blockstart l1 = ls_blockstart (d_ls s) ->
  ls_matchavail l1 = 0 ->
  ls_windowsize l1 = ls_windowsize (d_ls s) ->
  ls_insert l1 = ls_insert (d_ls s) ->
  ls_prevlen l1 = 2 ->
  (ls_matchlen l1 = ls_matchlen (d_ls s) \/ ls_matchlen l1 = 2
   \/ MIN_MATCH <= ls_matchlen l1) ->
  (MIN_MATCH <= ls_lookahead (d_ls s) ->
   ls_insh l1 = h3 g (ls_window (d_ls s)) (ls_strstart (d_ls s))) ->
  0 <= ls_matchlen l1 <= MAX_MATCH ->
  (MIN_MATCH <= ls_matchlen l1 ->
   ls_matchlen l1 <= ls_lookahead (d_ls s)
   /\ 0 <= slid + ls_matchstart l1
   /\ 1 <= ls_strstart (d_ls s) - ls_matchstart l1 <= dg_max_dist g
   /\ forall k, 0 <= k < ls_matchlen l1 ->
        nth (Z.to_nat (slid + ls_matchstart l1 + k))
            (zs_done (d_strm s)) 0
        = nth (Z.to_nat (slid + ls_strstart (d_ls s) + k))
              (zs_done (d_strm s)) 0) ->
  Z.leb MIN_MATCH (ls_matchlen l1) = true ->
  let s2 := setD_ls l1 s in
  let tt := tr_tally_dist (ls_strstart l1 - ls_matchstart l1)
                          (ls_matchlen l1 - MIN_MATCH)
                          (dg_sym_end g) (d_ts s2) in
  let l2 := setL_lookahead (ls_lookahead l1 - ls_matchlen l1) l1 in
  let l4 :=
    if (Z.leb (ls_matchlen l2) (dg_max_lazy_match g))
       && (Z.leb MIN_MATCH (ls_lookahead l2)) then
      let l3 := setL_matchlen (ls_matchlen l2 - 1) l2 in
      let l3b := df_insert (Z.to_nat (ls_matchlen l3) + 1) g
                   (ls_matchlen l3) l3 in
      setL_strstart (ls_strstart l3b + 1) (setL_matchlen 0 l3b)
    else
      let l3 := setL_matchlen 0
                  (setL_strstart (ls_strstart l2 + ls_matchlen l2) l2) in
      let h0 := ls_window l3 (ls_strstart l3) in
      setL_insh (update_hash g h0 (ls_window l3 (ls_strstart l3 + 1))) l3 in
  let s3 := setD_ls l4 (setD_ts (snd tt) s2) in
  exists Ins' toks' evs,
    Forall (EvOk g wrap (zs_done (d_strm s))) evs
    /\ ( (fst tt = false /\ evs = []
          /\ DsInv g wrap slid Ins' toks' s3
          /\ zs_done (d_strm s3) = zs_done (d_strm s)
          /\ zs_in (d_strm s3) = zs_in (d_strm s)
          /\ ls_lookahead (d_ls s3)
             = ls_lookahead (d_ls s) - ls_matchlen l1
          /\ ls_strstart (d_ls s3)
             = ls_strstart (d_ls s) + ls_matchlen l1
          /\ ls_blockstart (d_ls s3) = ls_blockstart (d_ls s)
          /\ ts_bw (d_ts s3) = ts_bw (d_ts s)
          /\ zs_out (d_strm s3) = zs_out (d_strm s)
          /\ zs_availout (d_strm s3) = zs_availout (d_strm s)
          /\ DfSide (d_ls s3)
          /\ toks' = toks ++ [TMatch (ls_matchlen l1)
                                (ls_strstart (d_ls s) - ls_matchstart l1)])
       \/ (exists ev, fst tt = true /\ evs = [ev] /\ fe_last ev = 0
          /\ fe_s ev = s3
          /\ fe_start ev = slid + ls_blockstart (d_ls s)
          /\ fe_end ev = slid + (ls_strstart (d_ls s) + ls_matchlen l1)
          /\ ls_blockstart (d_ls (flush_block_only 0 s3))
             = ls_strstart (d_ls s) + ls_matchlen l1
          /\ ts_bw (d_ts (fe_s ev)) = ts_bw (d_ts s)
          /\ zs_out (d_strm (fe_s ev)) = zs_out (d_strm s)
          /\ zs_availout (d_strm (fe_s ev)) = zs_availout (d_strm s)
          /\ DsInv g wrap slid Ins' toks' (flush_block_only 0 s3)
          /\ zs_done (d_strm (flush_block_only 0 s3)) = zs_done (d_strm s)
          /\ zs_in (d_strm (flush_block_only 0 s3)) = zs_in (d_strm s)
          /\ ls_lookahead (d_ls (flush_block_only 0 s3))
             = ls_lookahead (d_ls s) - ls_matchlen l1
          /\ ls_strstart (d_ls (flush_block_only 0 s3))
             = ls_strstart (d_ls s) + ls_matchlen l1
          /\ DfSide (d_ls (flush_block_only 0 s3))
          /\ fe_toks ev = toks ++ [TMatch (ls_matchlen l1)
                                     (ls_strstart (d_ls s) - ls_matchstart l1)]
          /\ toks' = []
          /\ ts_symnext (d_ts (fe_s ev)) = dg_sym_end g
          /\ (ls_blockstart (d_ls (fe_s ev)) < 0 ->
              dg_max_dist g < fe_end ev - fe_start ev)) )
    /\ (0 < dg_level g -> DfSnap (d_ts s) ->
        DfSnap (d_ts (if fst tt then flush_block_only 0 s3 else s3))
        /\ Forall (fun ev => DfSnap (d_ts (fe_s ev))) evs)
    /\ BsFloor g (if fst tt then flush_block_only 0 s3 else s3).
Proof.
  intros g wbits hbits wrap slid Ins Ins2 toks s l1
         Hg HI HBsf (Hma0 & Hpl2s & Hml02s) Havo Hcinv2 Hhi2 Ew Ess Ela Ebs
         Ema Ews Eins Hpl2 Hml3c Einsh Hmlb Hqual Hguard.
  apply Z.leb_le in Hguard.
  destruct (Hqual Hguard) as (Hmlla & Hms0 & Hdist & Hag).
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
  pose proof (go_maxd _ (g2_geom _ _ _ Hg)) as Emaxd.
  pose proof (g2_u16 _ _ _ Hg) as Hu16ws.
  pose proof (Z_div_mod_eq_full (dg_sym_end g) 3) as Hse3.
  pose proof Hmlb as Hmlb'. unfold MAX_MATCH in Hmlb'.
  pose proof Hguard as Hml3'. unfold MIN_MATCH in Hml3'.
  assert (Ets2 : d_ts (setD_ls l1 s) = d_ts s) by reflexivity.
  cbv zeta. rewrite Ets2, Ess.
  (* ---- the tally step ---- *)
  destruct (tr_tally_dist_step (ls_strstart (d_ls s) - ls_matchstart l1)
              (ls_matchlen l1 - MIN_MATCH) (dg_sym_end g) (d_ts s) toks
              ltac:(lia) ltac:(lia)
              (di_buf _ _ _ _ _ _ HI) (di_freq _ _ _ _ _ _ HI)
              ltac:(rewrite u16_id by lia; lia))
    as (Hbuf' & Hsn' & Hfreq' & Hflag & Hframe).
  destruct Hframe as (FtrBL & Fmax & Fblc & Fheap & Fhl & Fhm & Fdep
                      & Fopt & Fstat & Fmat & Fbw).
  set (tt := tr_tally_dist (ls_strstart (d_ls s) - ls_matchstart l1)
               (ls_matchlen l1 - MIN_MATCH) (dg_sym_end g) (d_ts s)) in *.
  (* the clean token *)
  assert (Etok : toks ++ [TMatch (u8 (ls_matchlen l1 - MIN_MATCH) + 3)
                                 (u16 (ls_strstart (d_ls s)
                                       - ls_matchstart l1))]
               = toks ++ [TMatch (ls_matchlen l1)
                                 (ls_strstart (d_ls s) - ls_matchstart l1)]).
  { rewrite u8_id by (unfold MIN_MATCH in *; lia).
    rewrite u16_id by lia.
    repeat f_equal. unfold MIN_MATCH. lia. }
  assert (Henc' : cEnc (toks ++ [TMatch (ls_matchlen l1)
                                   (ls_strstart (d_ls s)
                                    - ls_matchstart l1)])).
  { apply Forall_app. split; [exact (di_enc _ _ _ _ _ _ HI)|].
    constructor; [|apply Forall_nil].
    cbn [tok_enc].
    split; [split|split]; unfold MIN_MATCH, MAX_MATCH; lia. }
  (* ---- the resolution extension ---- *)
  assert (Hres' : resolve (firstn (Z.to_nat (slid + ls_blockstart (d_ls s)))
                    (zs_done (d_strm s)))
                    (toks ++ [TMatch (ls_matchlen l1)
                                (ls_strstart (d_ls s) - ls_matchstart l1)])
                = Some (firstn (Z.to_nat (slid + ls_strstart (d_ls s)
                                          + ls_matchlen l1))
                          (zs_done (d_strm s)))).
  { rewrite resolve_app.
    pose proof (di_res _ _ _ _ _ _ HI) as Hres.
    rewrite Hma0 in Hres.
    replace (slid + ls_strstart (d_ls s) - 0)
      with (slid + ls_strstart (d_ls s)) in Hres by lia.
    rewrite Hres.
    cbn [resolve resolve_tok].
    assert (Hzl : zlen (firstn (Z.to_nat (slid + ls_strstart (d_ls s)))
                          (zs_done (d_strm s)))
                = slid + ls_strstart (d_ls s)).
    { unfold zlen. rewrite length_firstn. unfold zlen in Hdone. lia. }
    rewrite Hzl.
    replace ((1 <=? ls_strstart (d_ls s) - ls_matchstart l1)
             && (ls_strstart (d_ls s) - ls_matchstart l1
                 <=? slid + ls_strstart (d_ls s)))
      with true
      by (symmetry; apply andb_true_iff;
          split; apply Z.leb_le; lia).
    cbn [resolve].
    f_equal.
    apply copy_n_slice.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros k Hk.
      replace (slid + ls_strstart (d_ls s)
               - (ls_strstart (d_ls s) - ls_matchstart l1) + k)
        with (slid + ls_matchstart l1 + k) by lia.
      apply Hag. lia. }
  (* ---- the SHARED TAIL over an abstract advanced state ---- *)
  set (goalOf := fun (l4v : LSt) =>
    exists Ins' toks' evs,
      Forall (EvOk g wrap (zs_done (d_strm s))) evs
      /\ ( (fst tt = false /\ evs = []
            /\ DsInv g wrap slid Ins' toks'
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))
            /\ zs_done (d_strm (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s)))) = zs_done (d_strm s)
            /\ zs_in (d_strm (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s)))) = zs_in (d_strm s)
            /\ ls_lookahead (d_ls (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s))))
               = ls_lookahead (d_ls s) - ls_matchlen l1
            /\ ls_strstart (d_ls (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s))))
               = ls_strstart (d_ls s) + ls_matchlen l1
            /\ ls_blockstart (d_ls (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s)))) = ls_blockstart (d_ls s)
            /\ ts_bw (d_ts (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s)))) = ts_bw (d_ts s)
            /\ zs_out (d_strm (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s)))) = zs_out (d_strm s)
            /\ zs_availout (d_strm (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s)))) = zs_availout (d_strm s)
            /\ DfSide (d_ls (setD_ls l4v (setD_ts (snd tt)
                 (setD_ls l1 s))))
            /\ toks' = toks ++ [TMatch (ls_matchlen l1)
                                  (ls_strstart (d_ls s) - ls_matchstart l1)])
         \/ (exists ev, fst tt = true /\ evs = [ev] /\ fe_last ev = 0
            /\ fe_s ev = setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s))
            /\ fe_start ev = slid + ls_blockstart (d_ls s)
            /\ fe_end ev = slid + (ls_strstart (d_ls s) + ls_matchlen l1)
            /\ ls_blockstart (d_ls (flush_block_only 0
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))))
               = ls_strstart (d_ls s) + ls_matchlen l1
            /\ ts_bw (d_ts (fe_s ev)) = ts_bw (d_ts s)
            /\ zs_out (d_strm (fe_s ev)) = zs_out (d_strm s)
            /\ zs_availout (d_strm (fe_s ev)) = zs_availout (d_strm s)
            /\ DsInv g wrap slid Ins' toks' (flush_block_only 0
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s))))
            /\ zs_done (d_strm (flush_block_only 0
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))))
               = zs_done (d_strm s)
            /\ zs_in (d_strm (flush_block_only 0
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))))
               = zs_in (d_strm s)
            /\ ls_lookahead (d_ls (flush_block_only 0
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))))
               = ls_lookahead (d_ls s) - ls_matchlen l1
            /\ ls_strstart (d_ls (flush_block_only 0
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))))
               = ls_strstart (d_ls s) + ls_matchlen l1
            /\ DfSide (d_ls (flush_block_only 0
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))))
            /\ fe_toks ev = toks ++ [TMatch (ls_matchlen l1)
                                       (ls_strstart (d_ls s)
                                        - ls_matchstart l1)]
            /\ toks' = []
            /\ ts_symnext (d_ts (fe_s ev)) = dg_sym_end g
            /\ (ls_blockstart (d_ls (fe_s ev)) < 0 ->
                dg_max_dist g < fe_end ev - fe_start ev)) )
      /\ (0 < dg_level g -> DfSnap (d_ts s) ->
          DfSnap (d_ts (if fst tt then flush_block_only 0
                 (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))
               else setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s))))
          /\ Forall (fun ev => DfSnap (d_ts (fe_s ev))) evs)
      /\ BsFloor g (if fst tt then flush_block_only 0
             (setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))
           else setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s)))).
  assert (TAIL : forall (l4v : LSt) (Ins4 : Z -> Prop),
    ls_window l4v = ls_window (d_ls s) ->
    ls_strstart l4v = ls_strstart (d_ls s) + ls_matchlen l1 ->
    ls_lookahead l4v = ls_lookahead (d_ls s) - ls_matchlen l1 ->
    ls_blockstart l4v = ls_blockstart (d_ls s) ->
    ls_matchavail l4v = 0 ->
    ls_matchlen l4v = 0 ->
    ls_prevlen l4v = 2 ->
    ls_windowsize l4v = ls_windowsize (d_ls s) ->
    ChainCl g Ins4 l4v ->
    WinInv g slid l4v (d_strm s) ->
    goalOf l4v).
  { intros l4v Ins4 E4w E4ss E4la E4bs E4ma E4ml E4pl2 E4ws HCC4 HW4.
    unfold goalOf.
    set (s3 := setD_ls l4v (setD_ts (snd tt) (setD_ls l1 s))) in *.
    assert (E3ls : d_ls s3 = l4v) by reflexivity.
    assert (E3ts : d_ts s3 = snd tt) by reflexivity.
    assert (E3strm : d_strm s3 = d_strm s) by reflexivity.
    assert (HW3 : WinInv g slid (d_ls s3) (d_strm s3))
      by (rewrite E3ls, E3strm; exact HW4).
    assert (Hsnap3 : DfSnap (d_ts s) -> DfSnap (d_ts s3)).
    { intros (HT & Ho & Hst).
      rewrite E3ts.
      refine (conj _ (conj _ _)).
      - apply treeinv_tally_dist. exact HT.
      - exact (proj1 (statzero_tally_dist _ _ _ _ (conj Ho Hst))).
      - exact (proj2 (statzero_tally_dist _ _ _ _ (conj Ho Hst))). }
    destruct (fst tt) eqn:Eflag.
    - (* FLUSH after the advance *)
      destruct (flush_block_only_step g wbits hbits wrap slid
                  (toks ++ [TMatch (ls_matchlen l1)
                              (ls_strstart (d_ls s) - ls_matchstart l1)])
                  s3 0 Hg
                  ltac:(unfold s3; lsimp; exact (di_cfg _ _ _ _ _ _ HI))
                  ltac:(unfold s3; lsimp; exact (di_wrap _ _ _ _ _ _ HI))
                  HW3
                  ltac:(rewrite E3strm; exact (di_ck _ _ _ _ _ _ HI))
                  ltac:(rewrite E3ts; rewrite <- Etok; exact Hbuf')
                  ltac:(rewrite E3ts; rewrite <- Etok; exact Hfreq')
                  ltac:(exact Henc')
                  ltac:(rewrite E3ts, Hsn'; lia)
                  ltac:(lia)
                  ltac:(rewrite E3ls, E4bs; exact (di_bb0 _ _ _ _ _ _ HI))
                  ltac:(rewrite E3ls, E4bs, E4ss;
                        pose proof (di_bble _ _ _ _ _ _ HI);
                        rewrite Hma0 in *; lia)
                  ltac:(rewrite E3ls, E3strm, E4bs, E4ss;
                        replace (slid + (ls_strstart (d_ls s)
                                         + ls_matchlen l1))
                          with (slid + ls_strstart (d_ls s)
                                + ls_matchlen l1) by lia;
                        exact Hres'))
        as (HEv & Fcfg & Fwrap & FW & FK & FBuf & FFreq & FSn & Fbs & Fss
            & Fla & Fma & Fml & Fpl & Fpm & Fms & Fwin & Fprev & Fhead
            & Finsh & Fins & Fws & Fdn & Fin & Fti & Favo).
      cbv zeta in HEv.
      exists Ins4, [],
        [{| fe_s := s3; fe_last := 0;
            fe_start := slid + ls_blockstart (d_ls s3);
            fe_end := slid + ls_strstart (d_ls s3);
            fe_toks := toks ++ [TMatch (ls_matchlen l1)
                                  (ls_strstart (d_ls s)
                                   - ls_matchstart l1)] |}].
      split.
      { constructor; [|apply Forall_nil].
        rewrite Fdn, E3strm in HEv. exact HEv. }
      split.
      { right.
        exists {| fe_s := s3; fe_last := 0;
                  fe_start := slid + ls_blockstart (d_ls s3);
                  fe_end := slid + ls_strstart (d_ls s3);
                  fe_toks := toks ++ [TMatch (ls_matchlen l1)
                                        (ls_strstart (d_ls s)
                                         - ls_matchstart l1)] |}.
        repeat apply conj.
        + reflexivity.
        + reflexivity.
        + reflexivity.
        + reflexivity.
        + cbn [fe_start]. rewrite E3ls, E4bs. reflexivity.
        + cbn [fe_end]. rewrite E3ls, E4ss. reflexivity.
        + rewrite Fbs, E3ls, E4ss. reflexivity.
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
            -- rewrite Fwin, Fprev, Fhead, Fss, Fla.
               exact (cc_inv _ _ _ HCC4).
            -- rewrite Fss.
               exact (cc_hi _ _ _ HCC4).
            -- rewrite Fins.
               exact (cc_ins0 _ _ _ HCC4).
            -- unfold SyncOK.
               rewrite Finsh, Fwin, Fss, Fla, Fins.
               exact (cc_sync _ _ _ HCC4).
          * exact FBuf.
          * exact FFreq.
          * apply Forall_nil.
          * cbn [resolve].
            rewrite Fbs, Fss, Fma, Fdn, E3ls, E4ma.
            do 2 f_equal. lia.
          * rewrite Fbs, E3ls, E4ss. lia.
          * rewrite Fbs, Fss, Fma, E3ls, E4ss, E4ma. lia.
          * rewrite Fma, E3ls, E4ma. left. reflexivity.
          * rewrite Fma, E3ls, E4ma. intros E. lia.
          * unfold MatchCand. intros Hml3.
            rewrite Fml, E3ls, E4ml in Hml3.
            unfold MIN_MATCH in Hml3. exfalso. lia.
          * rewrite Fpl, E3ls, E4pl2. unfold MAX_MATCH. lia.
          * rewrite Fml, E3ls, E4ml. unfold MIN_MATCH, MAX_MATCH in *. lia.
          * rewrite FSn. lia.
        + rewrite Fdn, E3strm. reflexivity.
        + rewrite Fin, E3strm. reflexivity.
        + rewrite Fla, E3ls, E4la. reflexivity.
        + rewrite Fss, E3ls, E4ss. reflexivity.
        + (* DfSide, three atoms *)
          rewrite Fma, E3ls, E4ma. reflexivity.
        + rewrite Fpl, E3ls. exact E4pl2.
        + rewrite Fml, E3ls, E4ml. left. reflexivity.
        + reflexivity.
        + reflexivity.
        + cbn [fe_s]. rewrite E3ts, Hsn'.
          apply Z.eqb_eq. congruence.
        + cbn [fe_s fe_start fe_end]. rewrite E3ls, E4bs, E4ss.
          intros Hneg. pose proof (HBsf Hneg). lia. }
      split.
      { intros Hlv HSn.
        pose proof (Hsnap3 HSn) as (HT3 & Ho3 & Hst3).
        split.
        - refine (conj _ (conj _ _)).
          + apply treeinv_flush;
              [ unfold s3; lsimp;
                rewrite (di_cfg _ _ _ _ _ _ HI); exact Hlv
              | exact HT3 ].
          + exact (proj1 (statzero_flush _ _)).
          + exact (proj2 (statzero_flush _ _)).
        - constructor; [|apply Forall_nil].
          cbn [fe_s]. exact (conj HT3 (conj Ho3 Hst3)). }
      { unfold BsFloor. rewrite Fbs, E3ls, E4ss.
        intros Hneg. exfalso. lia. }
    - (* NO FLUSH *)
      exists Ins4,
        (toks ++ [TMatch (ls_matchlen l1)
                    (ls_strstart (d_ls s) - ls_matchstart l1)]), [].
      split; [apply Forall_nil|].
      split.
      { left.
        repeat apply conj.
        + reflexivity.
        + reflexivity.
        + (* DsInv at s3 *)
          constructor.
          * unfold s3; lsimp. exact (di_cfg _ _ _ _ _ _ HI).
          * unfold s3; lsimp. exact (di_wrap _ _ _ _ _ _ HI).
          * exact HW3.
          * rewrite E3strm. exact (di_ck _ _ _ _ _ _ HI).
          * rewrite E3ls. exact HCC4.
          * rewrite E3ts. rewrite <- Etok. exact Hbuf'.
          * rewrite E3ts. rewrite <- Etok. exact Hfreq'.
          * exact Henc'.
          * rewrite E3ls, E3strm, E4bs, E4ss, E4ma.
            replace (slid + (ls_strstart (d_ls s) + ls_matchlen l1) - 0)
              with (slid + ls_strstart (d_ls s) + ls_matchlen l1) by lia.
            exact Hres'.
          * rewrite E3ls, E4bs. exact (di_bb0 _ _ _ _ _ _ HI).
          * rewrite E3ls, E4bs, E4ss, E4ma.
            pose proof (di_bble _ _ _ _ _ _ HI).
            rewrite Hma0 in *. lia.
          * rewrite E3ls, E4ma. left. reflexivity.
          * rewrite E3ls, E4ma. intros Habs. discriminate Habs.
          * unfold MatchCand.
            rewrite E3ls, E4ml.
            intros Hml3. exfalso.
            unfold MIN_MATCH in Hml3. lia.
          * rewrite E3ls, E4pl2. unfold MAX_MATCH. lia.
          * rewrite E3ls, E4ml. unfold MIN_MATCH, MAX_MATCH in *. lia.
          * rewrite E3ts, Hsn'.
            symmetry in Hflag. apply Z.eqb_neq in Hflag. lia.
        + rewrite E3strm. reflexivity.
        + rewrite E3strm. reflexivity.
        + rewrite E3ls. exact E4la.
        + rewrite E3ls. exact E4ss.
        + rewrite E3ls. exact E4bs.
        + rewrite E3ts. exact Fbw.
        + rewrite E3strm. reflexivity.
        + rewrite E3strm. reflexivity.
        + rewrite E3ls. exact E4ma.
        + rewrite E3ls. exact E4pl2.
        + rewrite E3ls, E4ml. left. reflexivity.
        + reflexivity. }
      split.
      { intros Hlv HSn.
        split; [exact (Hsnap3 HSn) | apply Forall_nil]. }
      { unfold BsFloor. rewrite E3ls, E4bs, E4ss. intros Hneg.
        pose proof (HBsf Hneg). lia. }
  }
  (* ---- dispatch on the advance sub-arm ---- *)
  lsimp.
  destruct ((Z.leb (ls_matchlen l1) (dg_max_lazy_match g))
            && (Z.leb MIN_MATCH (ls_lookahead l1 - ls_matchlen l1)))
    eqn:Esub.
  - (* INSERT-covered advance *)
    apply andb_true_iff in Esub as [Esub1 Esub2].
    apply Z.leb_le in Esub2.
    rewrite Ela in Esub2.
    set (l3 := setL_matchlen (ls_matchlen l1 - 1)
                 (setL_lookahead (ls_lookahead l1 - ls_matchlen l1) l1)).
    assert (HC3 : ChainInv g (ls_window l3) (ls_prev l3) (ls_head l3)
                    (ls_strstart l3)
                    (ls_strstart (d_ls s) + ls_lookahead (d_ls s)
                     - ls_strstart l3) Ins2).
    { unfold l3; lsimp.
      rewrite Ess.
      replace (ls_strstart (d_ls s) + ls_lookahead (d_ls s)
               - ls_strstart (d_ls s))
        with (ls_lookahead (d_ls s)) by lia.
      rewrite <- Ess, <- Ela.
      exact Hcinv2. }
    destruct (df_insert_walk (Z.to_nat (ls_matchlen l3) + 1) g wbits hbits
                (ls_strstart (d_ls s) + ls_lookahead (d_ls s)) Ins2 l3
                (ls_matchlen l3) Hg HC3
                ltac:(unfold l3; lsimp; intros p Hp;
                      rewrite Ess; exact (Hhi2 p Hp))
                ltac:(left; unfold l3; lsimp;
                      rewrite (Einsh ltac:(unfold MIN_MATCH in *; lia)),
                        <- Ew, <- Ess; reflexivity)
                ltac:(unfold l3; lsimp; rewrite Ess; lia)
                ltac:(unfold l3; lsimp; lia)
                ltac:(unfold l3; lsimp;
                      rewrite Nat2Z.inj_add, Z2Nat.id by lia;
                      cbn [Z.of_nat]; lia)
                ltac:(unfold l3; lsimp; rewrite Ess;
                      unfold MIN_MATCH in *; lia)
                ltac:(lia))
      as (Ins4 & HC4 & Hhi4 & Hsync4 & Ew4 & Ebs4 & Ema4 & Eml4 & Ems4
          & Ela4 & Ews4 & Eins4 & Epl4 & Epm4 & Ess4).
    cbv zeta in HC4, Hhi4, Hsync4, Ew4, Ebs4, Ema4, Eml4, Ems4, Ela4,
      Ews4, Eins4, Epl4, Epm4, Ess4.
    set (l3b := df_insert (Z.to_nat (ls_matchlen l3) + 1) g
                  (ls_matchlen l3) l3) in *.
    (* plain forms *)
    assert (Ess3b : ls_strstart l3b = ls_strstart (d_ls s)
                    + ls_matchlen l1 - 1)
      by (rewrite Ess4; unfold l3; lsimp; rewrite Ess; lia).
    assert (Ela3b : ls_lookahead l3b = ls_lookahead (d_ls s)
                    - ls_matchlen l1)
      by (rewrite Ela4; unfold l3; lsimp; rewrite Ela; reflexivity).
    apply (TAIL (setL_strstart (ls_strstart l3b + 1)
                   (setL_matchlen 0 l3b)) Ins4);
      lsimp.
    + rewrite Ew4. unfold l3; lsimp. exact Ew.
    + rewrite Ess3b. lia.
    + exact Ela3b.
    + rewrite Ebs4. unfold l3; lsimp. exact Ebs.
    + rewrite Ema4. unfold l3; lsimp. exact Ema.
    + reflexivity.
    + rewrite Epl4. unfold l3; lsimp. exact Hpl2.
    + rewrite Ews4. unfold l3; lsimp. exact Ews.
    + (* ChainCl at the final state *)
      constructor.
      * lsimp.
        eapply (flr_advance g wbits hbits);
          first [ exact HC4
                | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
                | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
                | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
                | exact (go_maxd _ (g2_geom _ _ _ Hg))
                | (rewrite ?Ess3b, ?Ela3b; lia) ].
      * intros p Hp. lsimp.
        pose proof (Hhi4 _ Hp). lia.
      * lsimp. rewrite Eins4. unfold l3; lsimp.
        rewrite Eins.
        exact (cc_ins0 _ _ _ (di_chain _ _ _ _ _ _ HI)).
      * unfold SyncOK. lsimp.
        intros _ Hla3'.
        destruct Hsync4 as [Hs4|Hp4].
        -- rewrite Hs4.
           replace (ls_strstart l3b + 1 + 2)
             with (ls_strstart l3b + 3) by lia.
           apply (h3_roll g wbits hbits _ _ Hg).
        -- exfalso. rewrite Ess3b, Ela3b in *.
           unfold MIN_MATCH in *. lia.
    + (* WinInv at the final state *)
      destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
      constructor; lsimp;
        rewrite ?Ew4, ?Ess3b, ?Ela3b, ?Ews4;
        unfold l3; lsimp;
        rewrite ?Ew, ?Ews;
        try lia; try congruence; try assumption.
      intros i Hi. apply W10. lia.
  - (* SKIP-with-reseed advance *)
    apply (TAIL (setL_insh
                   (update_hash g
                      (ls_window (setL_matchlen 0
                         (setL_strstart (ls_strstart l1 + ls_matchlen l1)
                            (setL_lookahead (ls_lookahead l1
                                             - ls_matchlen l1) l1)))
                         (ls_strstart (setL_matchlen 0
                            (setL_strstart (ls_strstart l1 + ls_matchlen l1)
                               (setL_lookahead (ls_lookahead l1
                                                - ls_matchlen l1) l1)))))
                      (ls_window (setL_matchlen 0
                         (setL_strstart (ls_strstart l1 + ls_matchlen l1)
                            (setL_lookahead (ls_lookahead l1
                                             - ls_matchlen l1) l1)))
                         (ls_strstart (setL_matchlen 0
                            (setL_strstart (ls_strstart l1 + ls_matchlen l1)
                               (setL_lookahead (ls_lookahead l1
                                                - ls_matchlen l1) l1)))
                          + 1)))
                   (setL_matchlen 0
                      (setL_strstart (ls_strstart l1 + ls_matchlen l1)
                         (setL_lookahead (ls_lookahead l1 - ls_matchlen l1)
                            l1)))) Ins2);
      lsimp.
    + exact Ew.
    + rewrite Ess. reflexivity.
    + rewrite Ela. reflexivity.
    + exact Ebs.
    + exact Ema.
    + reflexivity.
    + exact Hpl2.
    + exact Ews.
    + (* ChainCl: advance without inserts, then the reseed sync *)
      constructor.
      * lsimp.
        eapply (flr_advance g wbits hbits);
          first [ exact Hcinv2
                | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
                | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
                | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
                | exact (go_maxd _ (g2_geom _ _ _ Hg))
                | (rewrite ?Ess, ?Ela; lia) ].
      * intros p Hp. lsimp.
        pose proof (Hhi2 _ Hp). rewrite Ess. lia.
      * lsimp. rewrite Eins.
        exact (cc_ins0 _ _ _ (di_chain _ _ _ _ _ _ HI)).
      * (* the two-byte reseed IS one update behind h3 — definitional *)
        unfold SyncOK. lsimp.
        intros _ _.
        unfold h3. reflexivity.
    + (* WinInv *)
      destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
      constructor; lsimp;
        rewrite ?Ew, ?Ess, ?Ela, ?Ews;
        try lia; try congruence; try assumption.
      intros i Hi. apply W10. lia.
Qed.

Print Assumptions dfb_arm1_inv.
