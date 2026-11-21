(** * SwArm2 — the slow-path walk, part W3f: the PENDING-LITERAL arm of
      [ds_body] (deflate.c:1994-2006 — emit the byte at [strstart-1],
      possibly flush, advance one; [match_avail] STAYS 1).

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    THE BOOKKEEPING FACT the arm turns on: emitting the pending literal at
    [strstart - 1] and advancing keeps the tally point
    [strstart - matchavail] one PAST the emitted byte — the byte at the NEW
    [strstart - 1] becomes the next pending literal, so [match_avail] stays
    1 and the value spine extends by exactly one input byte.

    The optional mid-arm flush is SwEv's [flush_block_only_step]; the event
    snapshots the post-tally state, and the conclusion's disjunction hands
    SwLoop the output-side chaining equations for both cases. *)

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

(** [firstn] one past: the next element lands at the end. *)
Lemma firstn_snoc_nth : forall (l : list Z) n,
  (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  induction l as [|x l IH]; intros n Hn; cbn [length] in Hn; [lia|].
  destruct n as [|n]; cbn [firstn nth app]; [reflexivity|].
  rewrite (IH n) by lia. reflexivity.
Qed.

Theorem dsb_arm2_inv : forall g wbits hbits wrap slid Ins Ins2 toks s l2,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  1 <= ls_lookahead (d_ls s) ->
  0 <= zs_availout (d_strm s) ->
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
  ls_matchavail l2 = 1 ->
  let c := ls_window l2 (ls_strstart l2 - 1) in
  let s2 := setD_ls l2 s in
  let tt := tr_tally_lit c (dg_sym_end g) (d_ts s2) in
  let s3 := setD_ts (snd tt) s2 in
  let s4 := if fst tt then flush_block_only 0 s3 else s3 in
  let s5 := setD_ls (setL_lookahead (ls_lookahead (d_ls s4) - 1)
                      (setL_strstart (ls_strstart (d_ls s4) + 1) (d_ls s4)))
                    s4 in
  exists toks' evs,
    DsInv g wrap slid Ins2 toks' s5
    /\ Forall (EvOk g wrap (zs_done (d_strm s5))) evs
    /\ zs_done (d_strm s5) = zs_done (d_strm s)
    /\ zs_in (d_strm s5) = zs_in (d_strm s)
    /\ ls_lookahead (d_ls s5) = ls_lookahead (d_ls s) - 1
    /\ ls_strstart (d_ls s5) = ls_strstart (d_ls s) + 1
    /\ ( (fst tt = false /\ evs = []
          /\ ls_blockstart (d_ls s5) = ls_blockstart (d_ls s)
          /\ ts_bw (d_ts s5) = ts_bw (d_ts s)
          /\ zs_out (d_strm s5) = zs_out (d_strm s)
          /\ zs_availout (d_strm s5) = zs_availout (d_strm s)
          /\ toks' = toks ++ [TLit c])
       \/ (exists ev, fst tt = true /\ evs = [ev] /\ fe_last ev = 0
          /\ fe_start ev = slid + ls_blockstart (d_ls s)
          /\ fe_end ev = slid + ls_strstart (d_ls s)
          /\ ls_blockstart (d_ls s5) = ls_strstart (d_ls s)
          /\ ts_bw (d_ts (fe_s ev)) = ts_bw (d_ts s)
          /\ zs_out (d_strm (fe_s ev)) = zs_out (d_strm s)
          /\ zs_availout (d_strm (fe_s ev)) = zs_availout (d_strm s)
          /\ d_ts s5 = d_ts (flush_block_only (fe_last ev) (fe_s ev))
          /\ zs_out (d_strm s5)
             = zs_out (d_strm (flush_block_only (fe_last ev) (fe_s ev)))
          /\ zs_availout (d_strm s5)
             = zs_availout (d_strm (flush_block_only (fe_last ev) (fe_s ev)))
          /\ fe_s ev = s3
          /\ fe_toks ev = toks ++ [TLit c]
          /\ toks' = []) ).
Proof.
  intros g wbits hbits wrap slid Ins Ins2 toks s l2
         Hg HI Hla1 Havo Hcinv2 Hhi2 Ew Ess Ela Ebs Ema Ews Eins Einsh
         Hmlb Epl Hdisp Hguard Hma1.
  pose proof (di_win _ _ _ _ _ _ HI) as HW.
  pose proof (wi_ss _ _ _ _ HW) as Hss.
  pose proof (wi_la _ _ _ _ HW) as Hla.
  pose proof (wi_room _ _ _ _ HW) as Hroom.
  pose proof (wi_wsize _ _ _ _ HW) as Hwsz.
  pose proof (wi_slid _ _ _ _ HW) as Hslid.
  pose proof (wi_done _ _ _ _ HW) as Hdone.
  pose proof (di_ma1 _ _ _ _ _ _ HI) as Hma1s'.
  assert (Hma1s : ls_matchavail (d_ls s) = 1) by congruence.
  assert (Hss1 : 1 <= ls_strstart (d_ls s)) by (apply Hma1s'; exact Hma1s).
  pose proof (buftoks_extent _ _ _ _ (di_buf _ _ _ _ _ _ HI)) as Hext.
  pose proof (di_sn _ _ _ _ _ _ HI) as Hsn.
  pose proof (g2_se_hi _ _ _ Hg) as Hsehi.
  pose proof (g2_se_lo _ _ _ Hg) as Hselo.
  pose proof (g2_se_mod _ _ _ Hg) as Hsemod.
  (* the emitted byte *)
  assert (Hc : 0 <= ls_window (d_ls s) (ls_strstart (d_ls s) - 1) < 256).
  { apply (wininv_bytes g slid (d_ls s) (d_strm s) HW). lia. }
  assert (Hcval : ls_window (d_ls s) (ls_strstart (d_ls s) - 1)
                  = nth (Z.to_nat (slid + (ls_strstart (d_ls s) - 1)))
                        (zs_done (d_strm s)) 0).
  { apply (wi_win _ _ _ _ HW). lia. }
  assert (Ets2 : d_ts (setD_ls l2 s) = d_ts s) by (lsimp; reflexivity).
  cbv zeta.
  rewrite Ew, Ess, Ets2.
  set (c := ls_window (d_ls s) (ls_strstart (d_ls s) - 1)) in *.
  (* the tally step *)
  destruct (tr_tally_lit_step c (dg_sym_end g) (d_ts s) toks
              ltac:(lia) ltac:(lia)
              (di_buf _ _ _ _ _ _ HI) (di_freq _ _ _ _ _ _ HI))
    as (Hbuf' & Hsn' & Hfreq' & Hflag & Hframe).
  destruct Hframe as (FtrBL & Fmax & Fblc & Fheap & Fhl & Fhm & Fdep
                      & Fopt & Fstat & Fmat & Fbw).
  set (tt := tr_tally_lit c (dg_sym_end g) (d_ts s)) in *.
  (* the new token list, with the mask dropped *)
  assert (Etok : toks ++ [TLit (u8 c)] = toks ++ [TLit c])
    by (rewrite u8_id by exact Hc; reflexivity).
  assert (Henc' : cEnc (toks ++ [TLit c])).
  { apply Forall_app. split; [exact (di_enc _ _ _ _ _ _ HI)|].
    constructor; [cbn; exact Hc | constructor]. }
  (* the extended resolution, ending at the CURRENT strstart *)
  assert (Hres' : resolve (firstn (Z.to_nat (slid + ls_blockstart (d_ls s)))
                    (zs_done (d_strm s))) (toks ++ [TLit c])
                  = Some (firstn (Z.to_nat (slid + ls_strstart (d_ls s)))
                      (zs_done (d_strm s)))).
  { rewrite resolve_app.
    pose proof (di_res _ _ _ _ _ _ HI) as Hres.
    rewrite Hma1s in Hres.
    rewrite Hres.
    cbn [resolve resolve_tok].
    rewrite u8_id by exact Hc.
    f_equal.
    assert (Hn : (Z.to_nat (slid + ls_strstart (d_ls s) - 1)
                  < length (zs_done (d_strm s)))%nat)
      by (unfold zlen in Hdone; lia).
    replace (Z.to_nat (slid + ls_strstart (d_ls s)))
      with (S (Z.to_nat (slid + ls_strstart (d_ls s) - 1))) by lia.
    rewrite (firstn_snoc_nth _ _ Hn).
    f_equal. f_equal.
    rewrite Hcval.
    f_equal. f_equal. lia. }
  (* symnext arithmetic for the two flag cases *)
  assert (Hsn3 : ts_symnext (d_ts s) + 3 <= dg_sym_end g).
  { pose proof (Z_div_mod_eq_full (dg_sym_end g) 3). lia. }
  (* case on the flush flag *)
  destruct (fst tt) eqn:Eflag.
  - (* FLUSH *)
    (* the state handed to the flush *)
    set (s3 := setD_ts (snd tt) (setD_ls l2 s)) in *.
    assert (E3ls : d_ls s3 = l2) by (unfold s3; lsimp; reflexivity).
    assert (E3strm : d_strm s3 = d_strm s) by (unfold s3; lsimp; reflexivity).
    assert (E3ts : d_ts s3 = snd tt) by (unfold s3; lsimp; reflexivity).
    assert (HW2 : WinInv g slid (d_ls s3) (d_strm s3)).
    { rewrite E3ls, E3strm.
      destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
      constructor; try congruence.
      intros i Hi. rewrite Ew. apply W10. congruence. }
    destruct (flush_block_only_step g wbits hbits wrap slid
                (toks ++ [TLit c]) s3 0 Hg
                ltac:(unfold s3; lsimp; exact (di_cfg _ _ _ _ _ _ HI))
                ltac:(unfold s3; lsimp; exact (di_wrap _ _ _ _ _ _ HI))
                HW2
                ltac:(rewrite E3strm; exact (di_ck _ _ _ _ _ _ HI))
                ltac:(rewrite E3ts; rewrite <- Etok; exact Hbuf')
                ltac:(rewrite E3ts; rewrite <- Etok; exact Hfreq')
                ltac:(exact Henc')
                ltac:(rewrite E3ts; lia)
                ltac:(lia)
                ltac:(rewrite E3ls, Ebs; exact (di_bb0 _ _ _ _ _ _ HI))
                ltac:(rewrite E3ls, Ebs, Ess;
                      pose proof (di_bble _ _ _ _ _ _ HI); lia)
                ltac:(rewrite E3ls, E3strm, Ebs, Ess; exact Hres'))
      as (HEv & Fcfg & Fwrap & FW & FK & FBuf & FFreq & FSn & Fbs & Fss
          & Fla & Fma & Fml & Fpl & Fpm & Fms & Fwin & Fprev & Fhead
          & Finsh & Fins & Fws & Fdn & Fin & Fti & Favo).
    cbv zeta in HEv.
    exists [],
      [{| fe_s := s3; fe_last := 0;
          fe_start := slid + ls_blockstart (d_ls s3);
          fe_end := slid + ls_strstart (d_ls s3);
          fe_toks := toks ++ [TLit c] |}].
    (* everything is now about s5 over s4 := flush_block_only 0 s3 *)
    repeat apply conj.
    + (* DsInv at s5 *)
      constructor; lsimp.
      * exact Fcfg.
      * exact Fwrap.
      * (* WinInv advanced: normalize every field to (d_ls s) vocabulary *)
        destruct HW as [V1 V2 V3 V4 V5 V6 V7 V8 V9 V10].
        constructor; lsimp;
          rewrite ?Fss, ?Fla, ?Fwin, ?Fws, ?Fdn, ?Fin, ?Fti, ?E3ls, ?E3strm,
            ?Ess, ?Ela, ?Ew, ?Ews;
          try lia; try congruence; try assumption.
        intros i Hi.
        rewrite ?Fss, ?Fla, ?E3ls, ?Ess, ?Ela in Hi.
        apply V10. lia.
      * exact FK.
      * (* chain: transported across the flush, then advanced *)
        constructor; lsimp.
        -- eapply (flr_advance g wbits hbits);
             first [ (rewrite Fwin, Fprev, Fhead, E3ls; exact Hcinv2)
                   | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
                   | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
                   | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
                   | exact (go_maxd _ (g2_geom _ _ _ Hg))
                   | (rewrite ?Fss, ?Fla, ?E3ls, ?Ess, ?Ela; lia) ].
        -- intros p Hp. pose proof (Hhi2 _ Hp).
           rewrite Fss, E3ls, Ess. lia.
        -- rewrite Fins, E3ls. exact Eins.
        -- unfold SyncOK. lsimp.
           intros _ Hla3'.
           rewrite Fla, E3ls, Ela in Hla3'.
           rewrite Fss, Fwin, Finsh, E3ls, Ess, Ew.
           rewrite (Einsh ltac:(unfold MIN_MATCH in *; lia)).
           replace (ls_strstart (d_ls s) + 1 + 2)
             with (ls_strstart (d_ls s) + 3) by lia.
           apply (h3_roll g wbits hbits _ _ Hg).
      * exact FBuf.
      * exact FFreq.
      * constructor.
      * (* empty resolution at the new block base *)
        rewrite Fbs, Fss, Fdn, E3ls, E3strm, Ess.
        cbn [resolve].
        f_equal. f_equal.
        rewrite Fma, E3ls, Ema, Hma1s. lia.
      * rewrite Fbs, E3ls, Ess. lia.
      * rewrite Fbs, Fss, Fma, E3ls, Ess, Ema, Hma1s. lia.
      * rewrite Fma, E3ls, Ema. right. exact Hma1s.
      * intros _. rewrite Fss, E3ls, Ess. lia.
      * (* the candidate survives flush + advance *)
        unfold MatchCand. lsimp.
        rewrite Fml, Fms, Fss, Fla, Fma, E3ls, Ess, Ela, Ema.
        intros Hml3.
        destruct (Hdisp Hml3) as [Hmlla Hout].
        destruct Hout as [Hle|Hval].
        -- exfalso.
           apply andb_false_iff in Hguard.
           destruct Hguard as [Hb|Hb]; apply Z.leb_gt in Hb;
             unfold MIN_MATCH in *; lia.
        -- destruct Hval as (Hms0 & Hd & Hag).
           repeat split; try lia.
           intros k Hk.
           rewrite Fdn, E3strm.
           replace (ls_strstart (d_ls s) + 1 - 1)
             with (ls_strstart (d_ls s)) by lia.
           apply Hag. exact Hk.
      * rewrite Fpl, E3ls. lsimp.
        pose proof (di_ml _ _ _ _ _ _ HI). rewrite Epl. assumption.
      * rewrite Fml, E3ls. lsimp. exact Hmlb.
      * rewrite FSn. lia.
    + (* the one event, over the FINAL done *)
      constructor; [|constructor].
      lsimp. exact HEv.
    + lsimp. rewrite Fdn, E3strm. reflexivity.
    + lsimp. rewrite Fin, E3strm. reflexivity.
    + lsimp. rewrite Fla, E3ls, Ela. lia.
    + lsimp. rewrite Fss, E3ls, Ess. lia.
    + right.
      exists {| fe_s := s3; fe_last := 0;
                fe_start := slid + ls_blockstart (d_ls s3);
                fe_end := slid + ls_strstart (d_ls s3);
                fe_toks := toks ++ [TLit c] |}.
      repeat apply conj; try reflexivity.
      all: cbn [fe_s fe_last fe_start fe_end];
           first [ (rewrite E3ts; exact Fbw)
                 | (rewrite E3ls, Ebs; reflexivity)
                 | (rewrite E3ls, Ess; reflexivity)
                 | (lsimp; rewrite Fbs, E3ls, Ess; reflexivity)
                 | (unfold s3; lsimp; reflexivity)
                 | reflexivity ].
  - (* NO FLUSH *)
    exists (toks ++ [TLit c]), [].
    repeat apply conj; try (apply Forall_nil).
    + (* DsInv at s5 *)
      constructor; lsimp.
      * exact (di_cfg _ _ _ _ _ _ HI).
      * exact (di_wrap _ _ _ _ _ _ HI).
      * destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
        constructor; lsimp; try lia; try congruence.
        intros i Hi. rewrite Ew. apply W10.
        rewrite Ess, Ela in Hi. lia.
      * exact (di_ck _ _ _ _ _ _ HI).
      * constructor; lsimp.
        -- eapply (flr_advance g wbits hbits);
             first [ exact Hcinv2
                   | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
                   | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
                   | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
                   | exact (go_maxd _ (g2_geom _ _ _ Hg))
                   | (rewrite ?Ess, ?Ela; lia) ].
        -- intros p Hp. pose proof (Hhi2 _ Hp). rewrite Ess. lia.
        -- exact Eins.
        -- unfold SyncOK. lsimp.
           intros _ Hla3'.
           rewrite Ela in Hla3'.
           rewrite Ess, Ew.
           rewrite (Einsh ltac:(unfold MIN_MATCH in *; lia)).
           replace (ls_strstart (d_ls s) + 1 + 2)
             with (ls_strstart (d_ls s) + 3) by lia.
           apply (h3_roll g wbits hbits _ _ Hg).
      * rewrite <- Etok. exact Hbuf'.
      * rewrite <- Etok. exact Hfreq'.
      * exact Henc'.
      * rewrite Ebs, Ess, Hma1.
        replace (slid + (ls_strstart (d_ls s) + 1) - 1)
          with (slid + ls_strstart (d_ls s)) by lia.
        exact Hres'.
      * rewrite Ebs. exact (di_bb0 _ _ _ _ _ _ HI).
      * rewrite Ebs, Ess. pose proof (di_bble _ _ _ _ _ _ HI). lia.
      * rewrite Ema. right. exact Hma1s.
      * intros _. rewrite Ess. lia.
      * unfold MatchCand. lsimp.
        intros Hml3.
        destruct (Hdisp Hml3) as [Hmlla Hout].
        destruct Hout as [Hle|Hval].
        -- exfalso.
           apply andb_false_iff in Hguard.
           destruct Hguard as [Hb|Hb]; apply Z.leb_gt in Hb;
             unfold MIN_MATCH in *; lia.
        -- destruct Hval as (Hms0 & Hd & Hag).
           repeat split; try (rewrite Ess; lia); try lia.
           intros k Hk.
           rewrite Ess.
           replace (ls_strstart (d_ls s) + 1 - 1)
             with (ls_strstart (d_ls s)) by lia.
           apply Hag. exact Hk.
      * pose proof (di_ml _ _ _ _ _ _ HI). rewrite Epl. assumption.
      * exact Hmlb.
      * rewrite Hsn'.
        symmetry in Hflag. apply Z.eqb_neq in Hflag.
        pose proof (Z_div_mod_eq_full (dg_sym_end g) 3). lia.
    + lsimp. reflexivity.
    + lsimp. reflexivity.
    + lsimp. rewrite Ela. lia.
    + lsimp. rewrite Ess. lia.
    + left.
      repeat apply conj; try reflexivity.
      all: lsimp; first [ exact Ebs | reflexivity ].
Qed.

Print Assumptions dsb_arm2_inv.
