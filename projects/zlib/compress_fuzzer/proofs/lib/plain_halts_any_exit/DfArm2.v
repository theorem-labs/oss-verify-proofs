(** * DfArm2 — the fast-path walk, part F3: the LITERAL arm of [df_body]
      ([deflate.c:1889-1898] — emit the byte at [strstart], advance one,
      possibly flush AFTER the advance).

    OWNER: q5-emitter (GAP7 D1).  TRUST BOUNDARY: pure Gallina.

    Differences from the slow arm (SwArm2): the tally point is the
    CURRENT [strstart] (no lazy pending byte), [match_avail] stays 0,
    and the optional flush snapshots the ADVANCED state — [fe_end] is
    [strstart + 1] directly.  The [DfSnap] thread rides in the
    conclusion (the raw shell's decode engine consumes it per event). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwArm2
  ZRTreeState DfArm.
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

Theorem dfb_arm2_inv : forall g wbits hbits wrap slid Ins Ins2 toks s l1,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  BsFloor g s ->
  DfSide (d_ls s) ->
  1 <= ls_lookahead (d_ls s) ->
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
  Z.leb MIN_MATCH (ls_matchlen l1) = false ->
  let c := ls_window l1 (ls_strstart l1) in
  let s2 := setD_ls l1 s in
  let tt := tr_tally_lit c (dg_sym_end g) (d_ts s2) in
  let s3 := setD_ls (setL_strstart (ls_strstart l1 + 1)
                      (setL_lookahead (ls_lookahead l1 - 1) l1))
                    (setD_ts (snd tt) s2) in
  exists Ins' toks' evs,
    Forall (EvOk g wrap (zs_done (d_strm s))) evs
    /\ ( (fst tt = false /\ evs = []
          /\ DsInv g wrap slid Ins' toks' s3
          /\ zs_done (d_strm s3) = zs_done (d_strm s)
          /\ zs_in (d_strm s3) = zs_in (d_strm s)
          /\ ls_lookahead (d_ls s3) = ls_lookahead (d_ls s) - 1
          /\ ls_strstart (d_ls s3) = ls_strstart (d_ls s) + 1
          /\ ls_blockstart (d_ls s3) = ls_blockstart (d_ls s)
          /\ ts_bw (d_ts s3) = ts_bw (d_ts s)
          /\ zs_out (d_strm s3) = zs_out (d_strm s)
          /\ zs_availout (d_strm s3) = zs_availout (d_strm s)
          /\ DfSide (d_ls s3)
          /\ toks' = toks ++ [TLit c])
       \/ (exists ev, fst tt = true /\ evs = [ev] /\ fe_last ev = 0
          /\ fe_s ev = s3
          /\ fe_start ev = slid + ls_blockstart (d_ls s)
          /\ fe_end ev = slid + (ls_strstart (d_ls s) + 1)
          /\ ls_blockstart (d_ls (flush_block_only 0 s3))
             = ls_strstart (d_ls s) + 1
          /\ ts_bw (d_ts (fe_s ev)) = ts_bw (d_ts s)
          /\ zs_out (d_strm (fe_s ev)) = zs_out (d_strm s)
          /\ zs_availout (d_strm (fe_s ev)) = zs_availout (d_strm s)
          /\ DsInv g wrap slid Ins' toks' (flush_block_only 0 s3)
          /\ zs_done (d_strm (flush_block_only 0 s3)) = zs_done (d_strm s)
          /\ zs_in (d_strm (flush_block_only 0 s3)) = zs_in (d_strm s)
          /\ ls_lookahead (d_ls (flush_block_only 0 s3))
             = ls_lookahead (d_ls s) - 1
          /\ ls_strstart (d_ls (flush_block_only 0 s3))
             = ls_strstart (d_ls s) + 1
          /\ DfSide (d_ls (flush_block_only 0 s3))
          /\ fe_toks ev = toks ++ [TLit c]
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
         Hg HI HBsf (Hma0 & Hpl2s & Hml02s) Hla1 Havo Hcinv2 Hhi2 Ew Ess Ela
         Ebs Ema Ews Eins Hpl2 Hml3c Einsh Hmlb Hguard.
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
  (* the emitted byte *)
  assert (Hc : 0 <= ls_window (d_ls s) (ls_strstart (d_ls s)) < 256).
  { apply (wininv_bytes g slid (d_ls s) (d_strm s) HW). lia. }
  assert (Hcval : ls_window (d_ls s) (ls_strstart (d_ls s))
                  = nth (Z.to_nat (slid + ls_strstart (d_ls s)))
                        (zs_done (d_strm s)) 0).
  { apply (wi_win _ _ _ _ HW). lia. }
  assert (Ets2 : d_ts (setD_ls l1 s) = d_ts s) by (lsimp; reflexivity).
  cbv zeta.
  rewrite Ew, Ess, Ets2.
  set (c := ls_window (d_ls s) (ls_strstart (d_ls s))) in *.
  (* the tally step *)
  destruct (tr_tally_lit_step c (dg_sym_end g) (d_ts s) toks
              ltac:(lia) ltac:(lia)
              (di_buf _ _ _ _ _ _ HI) (di_freq _ _ _ _ _ _ HI))
    as (Hbuf' & Hsn' & Hfreq' & Hflag & Hframe).
  destruct Hframe as (FtrBL & Fmax & Fblc & Fheap & Fhl & Fhm & Fdep
                      & Fopt & Fstat & Fmat & Fbw).
  set (tt := tr_tally_lit c (dg_sym_end g) (d_ts s)) in *.
  assert (Etok : toks ++ [TLit (u8 c)] = toks ++ [TLit c])
    by (rewrite u8_id by exact Hc; reflexivity).
  assert (Henc' : cEnc (toks ++ [TLit c])).
  { apply Forall_app. split; [exact (di_enc _ _ _ _ _ _ HI)|].
    constructor; [cbn; exact Hc | constructor]. }
  (* the extended resolution: ma = 0, so [di_res] already ends at the
     CURRENT strstart; the new byte lands at exactly that index *)
  assert (Hres' : resolve (firstn (Z.to_nat (slid + ls_blockstart (d_ls s)))
                    (zs_done (d_strm s))) (toks ++ [TLit c])
                  = Some (firstn (Z.to_nat (slid + ls_strstart (d_ls s) + 1))
                      (zs_done (d_strm s)))).
  { rewrite resolve_app.
    pose proof (di_res _ _ _ _ _ _ HI) as Hres.
    rewrite Hma0 in Hres.
    replace (slid + ls_strstart (d_ls s) - 0)
      with (slid + ls_strstart (d_ls s)) in Hres by lia.
    rewrite Hres.
    cbn [resolve resolve_tok].
    rewrite u8_id by exact Hc.
    f_equal.
    assert (Hn : (Z.to_nat (slid + ls_strstart (d_ls s))
                  < length (zs_done (d_strm s)))%nat)
      by (unfold zlen in Hdone; lia).
    replace (Z.to_nat (slid + ls_strstart (d_ls s) + 1))
      with (S (Z.to_nat (slid + ls_strstart (d_ls s)))) by lia.
    rewrite (firstn_snoc_nth _ _ Hn).
    f_equal. f_equal.
    exact Hcval. }
  assert (Hsn3 : ts_symnext (d_ts s) + 3 <= dg_sym_end g).
  { pose proof (Z_div_mod_eq_full (dg_sym_end g) 3). lia. }
  (* the advanced+tallied state *)
  match goal with
  | |- context [setD_ls ?L (setD_ts (snd tt) (setD_ls l1 s))] =>
      set (l3 := L);
      set (s3 := setD_ls l3 (setD_ts (snd tt) (setD_ls l1 s))) in *
  end.
  assert (E3ls : d_ls s3 = l3) by reflexivity.
  assert (E3ts : d_ts s3 = snd tt) by reflexivity.
  assert (E3strm : d_strm s3 = d_strm s) by reflexivity.
  assert (E3ss : ls_strstart l3 = ls_strstart (d_ls s) + 1)
    by (unfold l3; lsimp; congruence).
  assert (E3la : ls_lookahead l3 = ls_lookahead (d_ls s) - 1)
    by (unfold l3; lsimp; congruence).
  assert (E3bs : ls_blockstart l3 = ls_blockstart (d_ls s))
    by (unfold l3; lsimp; congruence).
  assert (E3ma : ls_matchavail l3 = 0)
    by (unfold l3; lsimp; congruence).
  assert (E3pl : ls_prevlen l3 = ls_prevlen l1)
    by (unfold l3; lsimp; reflexivity).
  assert (E3ml : ls_matchlen l3 = ls_matchlen l1)
    by (unfold l3; lsimp; reflexivity).
  assert (E3ins : ls_insert l3 = ls_insert (d_ls s))
    by (unfold l3; lsimp; congruence).
  assert (E3w : ls_window l3 = ls_window (d_ls s))
    by (unfold l3; lsimp; congruence).
  (* the window invariant at s3 *)
  assert (HW3 : WinInv g slid (d_ls s3) (d_strm s3)).
  { rewrite E3ls, E3strm.
    destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    constructor; unfold l3; lsimp; try lia; try congruence.
    intros i Hi. rewrite Ew. apply W10.
    rewrite ?Ess, ?Ela in Hi. lia. }
  (* the chain closure at s3 *)
  assert (HCC3 : ChainCl g Ins2 (d_ls s3)).
  { rewrite E3ls.
    constructor.
    - unfold l3; lsimp.
      eapply (flr_advance g wbits hbits);
        first [ exact Hcinv2
              | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
              | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
              | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
              | exact (go_maxd _ (g2_geom _ _ _ Hg))
              | (rewrite ?Ess, ?Ela; lia) ].
    - intros p Hp; unfold l3; lsimp.
      pose proof (Hhi2 _ Hp). lia.
    - unfold l3; lsimp.
      rewrite Eins.
      exact (cc_ins0 _ _ _ (di_chain _ _ _ _ _ _ HI)).
    - unfold SyncOK. unfold l3; lsimp.
      intros _ Hla3'.
      rewrite Ela in Hla3'.
      rewrite Ew.
      rewrite (Einsh ltac:(unfold MIN_MATCH in *; lia)).
      replace (ls_strstart (d_ls s) + 1 + 2)
        with (ls_strstart (d_ls s) + 3) by lia.
      apply (h3_roll g wbits hbits _ _ Hg). }
  (* the exit matchlen pin: the kept value is 0 or 2 *)
  assert (Hml02x : ls_matchlen l1 = 0 \/ ls_matchlen l1 = 2).
  { apply Z.leb_gt in Hguard.
    destruct Hml3c as [E|[E|E]];
      [ rewrite E; exact Hml02s
      | right; exact E
      | exfalso; unfold MIN_MATCH in *; lia ]. }
  (* the snap thread, shared *)
  assert (Hsnap3 : DfSnap (d_ts s) -> DfSnap (d_ts s3)).
  { intros (HT & Ho & Hst).
    rewrite E3ts.
    refine (conj _ (conj _ _)).
    - apply treeinv_tally_lit. exact HT.
    - exact (proj1 (statzero_tally_lit _ _ _ (conj Ho Hst))).
    - exact (proj2 (statzero_tally_lit _ _ _ (conj Ho Hst))). }
  destruct (fst tt) eqn:Eflag.
  - (* FLUSH after the advance *)
    destruct (flush_block_only_step g wbits hbits wrap slid
                (toks ++ [TLit c]) s3 0 Hg
                ltac:(unfold s3; lsimp; exact (di_cfg _ _ _ _ _ _ HI))
                ltac:(unfold s3; lsimp; exact (di_wrap _ _ _ _ _ _ HI))
                HW3
                ltac:(rewrite E3strm; exact (di_ck _ _ _ _ _ _ HI))
                ltac:(rewrite E3ts; rewrite <- Etok; exact Hbuf')
                ltac:(rewrite E3ts; rewrite <- Etok; exact Hfreq')
                ltac:(exact Henc')
                ltac:(rewrite E3ts, Hsn'; lia)
                ltac:(lia)
                ltac:(rewrite E3ls, E3bs; exact (di_bb0 _ _ _ _ _ _ HI))
                ltac:(rewrite E3ls, E3bs, E3ss;
                      pose proof (di_bble _ _ _ _ _ _ HI);
                      rewrite Hma0 in *; lia)
                ltac:(rewrite E3ls, E3strm, E3bs, E3ss;
                      replace (slid + (ls_strstart (d_ls s) + 1))
                        with (slid + ls_strstart (d_ls s) + 1) by lia;
                      exact Hres'))
      as (HEv & Fcfg & Fwrap & FW & FK & FBuf & FFreq & FSn & Fbs & Fss
          & Fla & Fma & Fml & Fpl & Fpm & Fms & Fwin & Fprev & Fhead
          & Finsh & Fins & Fws & Fdn & Fin & Fti & Favo).
    cbv zeta in HEv.
    exists Ins2, [],
      [{| fe_s := s3; fe_last := 0;
          fe_start := slid + ls_blockstart (d_ls s3);
          fe_end := slid + ls_strstart (d_ls s3);
          fe_toks := toks ++ [TLit c] |}].
    split.
    { constructor; [|apply Forall_nil].
      rewrite Fdn, E3strm in HEv. exact HEv. }
    split.
    { right.
      exists {| fe_s := s3; fe_last := 0;
                fe_start := slid + ls_blockstart (d_ls s3);
                fe_end := slid + ls_strstart (d_ls s3);
                fe_toks := toks ++ [TLit c] |}.
      repeat apply conj.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + cbn [fe_start]. rewrite E3ls, E3bs. reflexivity.
      + cbn [fe_end]. rewrite E3ls, E3ss. reflexivity.
      + rewrite Fbs, E3ls, E3ss. reflexivity.
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
             exact (cc_inv _ _ _ HCC3).
          -- rewrite Fss.
             exact (cc_hi _ _ _ HCC3).
          -- rewrite Fins.
             exact (cc_ins0 _ _ _ HCC3).
          -- unfold SyncOK.
             rewrite Finsh, Fwin, Fss, Fla, Fins.
             exact (cc_sync _ _ _ HCC3).
        * exact FBuf.
        * exact FFreq.
        * apply Forall_nil.
        * cbn [resolve].
          rewrite Fbs, Fss, Fma, Fdn, E3ls, E3ma.
          do 2 f_equal. lia.
        * rewrite Fbs, E3ls, E3ss. lia.
        * rewrite Fbs, Fss, Fma, E3ls, E3ss, E3ma. lia.
        * rewrite Fma, E3ls, E3ma. left. reflexivity.
        * rewrite Fma, E3ls, E3ma. intros E. lia.
        * unfold MatchCand. intros Hml3.
          rewrite Fml, E3ls, E3ml in Hml3.
          apply Z.leb_gt in Hguard. exfalso. lia.
        * rewrite Fpl, E3ls, E3pl. unfold MIN_MATCH, MAX_MATCH in *. lia.
        * rewrite Fml, E3ls, E3ml. unfold MIN_MATCH, MAX_MATCH in *. lia.
        * rewrite FSn. lia.
      + rewrite Fdn, E3strm. reflexivity.
      + rewrite Fin, E3strm. reflexivity.
      + rewrite Fla, E3ls, E3la. reflexivity.
      + rewrite Fss, E3ls, E3ss. reflexivity.
      + (* DfSide at the flush output, three atoms *)
        rewrite Fma, E3ls, E3ma. reflexivity.
      + rewrite Fpl, E3ls, E3pl. exact Hpl2.
      + rewrite Fml, E3ls, E3ml. exact Hml02x.
      + reflexivity.
      + reflexivity.
      + cbn [fe_s]. rewrite E3ts, Hsn'.
        apply Z.eqb_eq. congruence.
      + cbn [fe_s fe_start fe_end]. rewrite E3ls, E3bs, E3ss.
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
    { unfold BsFloor. rewrite Fbs, E3ls, E3ss.
      intros Hneg. exfalso. lia. }
  - (* NO FLUSH *)
    exists Ins2, (toks ++ [TLit c]), [].
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
        * exact HCC3.
        * rewrite E3ts. rewrite <- Etok. exact Hbuf'.
        * rewrite E3ts. rewrite <- Etok. exact Hfreq'.
        * exact Henc'.
        * rewrite E3ls, E3strm, E3bs, E3ss, E3ma.
          replace (slid + (ls_strstart (d_ls s) + 1) - 0)
            with (slid + ls_strstart (d_ls s) + 1) by lia.
          exact Hres'.
        * rewrite E3ls, E3bs. exact (di_bb0 _ _ _ _ _ _ HI).
        * rewrite E3ls, E3bs, E3ss, E3ma.
          pose proof (di_bble _ _ _ _ _ _ HI).
          rewrite Hma0 in *. lia.
        * rewrite E3ls, E3ma. left. reflexivity.
        * rewrite E3ls, E3ma. intros Habs. discriminate Habs.
        * unfold MatchCand.
          rewrite E3ls, E3ml.
          intros Hml3. exfalso.
          apply Z.leb_gt in Hguard. lia.
        * rewrite E3ls, E3pl. unfold MIN_MATCH, MAX_MATCH in *. lia.
        * rewrite E3ls, E3ml. exact Hmlb.
        * rewrite E3ts, Hsn'.
          symmetry in Hflag. apply Z.eqb_neq in Hflag. lia.
      + rewrite E3strm. reflexivity.
      + rewrite E3strm. reflexivity.
      + rewrite E3ls. exact E3la.
      + rewrite E3ls. exact E3ss.
      + rewrite E3ls. exact E3bs.
      + rewrite E3ts. exact Fbw.
      + rewrite E3strm. reflexivity.
      + rewrite E3strm. reflexivity.
      + rewrite E3ls. exact E3ma.
      + rewrite E3ls, E3pl. exact Hpl2.
      + rewrite E3ls, E3ml. exact Hml02x.
      + reflexivity. }
    split.
    { intros Hlv HSn.
      split; [exact (Hsnap3 HSn) | apply Forall_nil]. }
    { unfold BsFloor. rewrite E3ls, E3bs, E3ss. intros Hneg.
      pose proof (HBsf Hneg). lia. }
Qed.

Print Assumptions dfb_arm2_inv.
