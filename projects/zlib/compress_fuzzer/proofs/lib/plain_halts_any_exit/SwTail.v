(** * SwTail — the slow-path walk, part W4d: [ds_tail] at [Z_FINISH].

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W4.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The loop broke with zero lookahead and drained input, so the tail
    (deflate.c:2016-2029 with [emit_pending_lit = set_insert = true])
    tallies the possibly-pending literal at [strstart - 1] (its flush
    flag is DISCARDED — the C code relies on the sym_buf bound), parks
    [insert] for a hypothetical next call, and emits the FINAL block:
    [flush_block 1].  The event closes both ledgers:

      * output: chained from the loop's final accumulator into the
        flushed state ([EvChain [ev]]);
      * input: [fe_start] is the running block base and [fe_end] is
        [slid + strstart] = [zlen zs_done] — the WHOLE consumed input
        (that equality is [wi_done] at [lookahead = 0]).

    [avail_out] decides [FinishStarted] (buffer full at return) vs
    [FinishDone]. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwArm2 SwDrain
  SwStep ZRTreeState ZREvSnap.
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

(** The state [ds_tail Z_FINISH true true] hands to [flush_block 1] — the tail
    flush event's [fe_s].  EXPORT WIDENING (an earlier development run M4-MODEL, 2026-09-07;
    q7-decode-2 RULING F1b): [ds_tail_finish] names the event's state so
    the deflate_slow discharger can identify it with DslowTail's [dtl_s2 s]
    (convertible: the same let-chain with [emit_pending_lit = set_insert = true]). *)
Definition sw_tail_s2 (s : DSt) : DSt :=
  let g := d_cfg s in
  let s1 :=
    if true && negb (Z.eqb (ls_matchavail (d_ls s)) 0) then
      let tt := tr_tally_lit (ls_window (d_ls s) (ls_strstart (d_ls s) - 1))
                             (dg_sym_end g) (d_ts s) in
      setD_ls (setL_matchavail 0 (d_ls s)) (setD_ts (snd tt) s)
    else s in
  let l  := d_ls s1 in
  setD_ls (setL_insert (if true
                        then (if Z.ltb (ls_strstart l) (MIN_MATCH - 1)
                              then ls_strstart l else MIN_MATCH - 1)
                        else 0) l) s1.

Ltac sw_tail_s2_closer :=
  unfold sw_tail_s2; cbv zeta;
  repeat match goal with
         | H : d_cfg _ = _ |- _ => rewrite H
         | H : ls_matchavail (d_ls _) = 0 |- _ => rewrite H
         | H : Z.eqb (ls_matchavail (d_ls _)) 0 = false |- _ => rewrite H
         end;
  cbn [Z.eqb andb negb]; cbv iota; reflexivity.

Theorem ds_tail_finish : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  ls_lookahead (d_ls s) = 0 ->
  0 <= zs_availout (d_strm s) ->
  exists ev bs s',
    ds_tail Z_FINISH true true s = (bs, s')
    /\ ( (bs = FinishStarted /\ zs_availout (d_strm s') = 0)
       \/ (bs = FinishDone /\ 1 <= zs_availout (d_strm s')) )
    /\ EvOk g wrap (zs_done (d_strm s')) ev
    /\ fe_last ev = 1
    /\ EvChain [ev] (ts_bw (d_ts s)) (zs_out (d_strm s))
                    (zs_availout (d_strm s))
                    (ts_bw (d_ts s')) (zs_out (d_strm s'))
                    (zs_availout (d_strm s'))
    /\ EvTile [ev] (slid + ls_blockstart (d_ls s))
                   (slid + ls_strstart (d_ls s))
    /\ slid + ls_strstart (d_ls s) = zlen (zs_done (d_strm s))
    /\ zs_done (d_strm s') = zs_done (d_strm s)
    /\ zs_in (d_strm s') = zs_in (d_strm s)
    /\ zs_totalin (d_strm s') = zs_totalin (d_strm s)
    /\ 0 <= zs_availout (d_strm s')
    /\ CkInv wrap (d_strm s')
    /\ d_wrap s' = d_wrap s
    /\ d_cfg s' = d_cfg s
    /\ (0 < dg_level g -> ZRSideInv g toks s ->
        ZRTreeInv (d_ts s') /\ EvSnapOk g ev)
    /\ (0 < dg_level g ->
        ZRTreeInv (d_ts s) /\ ts_optlen (d_ts s) = 0
        /\ ts_statlen (d_ts s) = 0 ->
        (ZRTreeInv (d_ts s') /\ ts_optlen (d_ts s') = 0
         /\ ts_statlen (d_ts s') = 0)
        /\ (ZRTreeInv (d_ts (fe_s ev)) /\ ts_optlen (d_ts (fe_s ev)) = 0
            /\ ts_statlen (d_ts (fe_s ev)) = 0))
    /\ (ls_blockstart (d_ls (fe_s ev)) = ls_blockstart (d_ls s)
        /\ 0 <= ls_blockstart (d_ls s'))
    /\ fe_s ev = sw_tail_s2 s.
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg HI Hla0 Havo.
  pose proof (di_win _ _ _ _ _ _ HI) as HW.
  pose proof (wi_ss _ _ _ _ HW) as Hss.
  pose proof (wi_la _ _ _ _ HW) as Hla.
  pose proof (wi_room _ _ _ _ HW) as Hroom.
  pose proof (wi_wsize _ _ _ _ HW) as Hwsz.
  pose proof (wi_slid _ _ _ _ HW) as Hslid.
  pose proof (wi_done _ _ _ _ HW) as Hdone.
  pose proof (di_cfg _ _ _ _ _ _ HI) as Ecfg.
  pose proof (di_wrap _ _ _ _ _ _ HI) as Ewrap.
  pose proof (buftoks_extent _ _ _ _ (di_buf _ _ _ _ _ _ HI)) as Hext.
  pose proof (di_sn _ _ _ _ _ _ HI) as Hsn.
  pose proof (g2_se_hi _ _ _ Hg) as Hsehi.
  pose proof (g2_se_lo _ _ _ Hg) as Hselo.
  pose proof (g2_se_mod _ _ _ Hg) as Hsemod.
  pose proof (Z_div_mod_eq_full (dg_sym_end g) 3) as Hse3.
  assert (Hcomp : slid + ls_strstart (d_ls s) = zlen (zs_done (d_strm s)))
    by lia.
  unfold ds_tail. cbv zeta.
  rewrite Ecfg.
  cbn [andb].
  destruct (Z.eqb (ls_matchavail (d_ls s)) 0) eqn:Ema0; cbn [negb]; cbv iota.
  - (* ---- no pending literal ---- *)
    apply Z.eqb_eq in Ema0.
    replace (Z.eqb Z_FINISH Z_FINISH) with true by reflexivity.
    cbv iota.
    match goal with
    | |- context [flush_block 1 ?X] => set (s2 := X)
    end.
    assert (E2ls : d_ls s2
                   = setL_insert
                       (if Z.ltb (ls_strstart (d_ls s)) (MIN_MATCH - 1)
                        then ls_strstart (d_ls s) else MIN_MATCH - 1)
                       (d_ls s)) by reflexivity.
    assert (E2ts : d_ts s2 = d_ts s) by reflexivity.
    assert (E2strm : d_strm s2 = d_strm s) by reflexivity.
    assert (HW2 : WinInv g slid (d_ls s2) (d_strm s2)).
    { rewrite E2ls, E2strm.
      destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
      constructor; lsimp; assumption. }
    destruct (flush_block_only_step g wbits hbits wrap slid toks s2 1 Hg
                ltac:(unfold s2; lsimp; exact Ecfg)
                ltac:(unfold s2; lsimp; exact Ewrap)
                HW2
                ltac:(rewrite E2strm; exact (di_ck _ _ _ _ _ _ HI))
                ltac:(rewrite E2ts; exact (di_buf _ _ _ _ _ _ HI))
                ltac:(rewrite E2ts; exact (di_freq _ _ _ _ _ _ HI))
                (di_enc _ _ _ _ _ _ HI)
                ltac:(rewrite E2ts; lia)
                ltac:(lia)
                ltac:(rewrite E2ls; lsimp; exact (di_bb0 _ _ _ _ _ _ HI))
                ltac:(rewrite E2ls; lsimp;
                      pose proof (di_bble _ _ _ _ _ _ HI);
                      destruct (di_ma _ _ _ _ _ _ HI); lia)
                ltac:(rewrite E2ls, E2strm; lsimp;
                      pose proof (di_res _ _ _ _ _ _ HI) as Hres;
                      rewrite Ema0 in Hres;
                      replace (slid + ls_strstart (d_ls s))
                        with (slid + ls_strstart (d_ls s) - 0) by lia;
                      exact Hres))
      as (HEv & Fcfg & Fwrap & FW & FK & FBuf & FFreq & FSn & Fbs & Fss
          & Fla & Fma & Fml & Fpl & Fpm & Fms & Fwin & Fprev & Fhead
          & Finsh & Fins & Fws & Fdn & Fin & Fti & Favo).
    cbv zeta in HEv.
    unfold flush_block. cbv zeta.
    exists {| fe_s := s2; fe_last := 1;
              fe_start := slid + ls_blockstart (d_ls s2);
              fe_end := slid + ls_strstart (d_ls s2);
              fe_toks := toks |}.
    destruct (Z.eqb (zs_availout (d_strm (flush_block_only 1 s2))) 0)
      eqn:Eavo0; cbv iota.
    + (* FinishStarted *)
      apply Z.eqb_eq in Eavo0.
      cbn [Z.eqb]. cbv iota.
      exists FinishStarted, (flush_block_only 1 s2).
      split; [reflexivity|].
      split; [left; split; [reflexivity | exact Eavo0]|].
      split; [exact HEv|].
      split; [reflexivity|].
      split; [cbn [EvChain fe_s fe_last];
              rewrite E2ts, E2strm; repeat split; reflexivity|].
      split; [cbn [EvTile fe_start fe_end];
              rewrite E2ls; lsimp; split; reflexivity|].
      split; [exact Hcomp|].
      split; [rewrite Fdn, E2strm; reflexivity|].
      split; [rewrite Fin, E2strm; reflexivity|].
      split; [rewrite Fti, E2strm; reflexivity|].
      split; [lia|].
      split; [exact FK|].
      split; [rewrite Fwrap, ?Ewrap; reflexivity|].
      split; [rewrite Fcfg, ?Ecfg; reflexivity|].
      split.
      { intros Hlv HS.
        destruct HS as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
        unfold SldInv in Hsldf.
        assert (HT2 : ZRTreeInv (d_ts s2))
          by (rewrite E2ts;
              first [exact HTIf | apply treeinv_tally_lit; exact HTIf]).
        assert (Hc2 : d_cfg s2 = d_cfg s) by reflexivity.
        split.
        { apply treeinv_flush; [rewrite Hc2, Ecfg; exact Hlv | exact HT2]. }
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        * cbn [fe_s]. exact HT2.
        * cbn [fe_s]. rewrite E2ts.
          first [ exact Holf
                | exact (proj1 (statzero_tally_lit _ _ _ (conj Holf Hslf))) ].
        * cbn [fe_s]. rewrite E2ts.
          first [ exact Hslf
                | exact (proj2 (statzero_tally_lit _ _ _ (conj Holf Hslf))) ].
        * cbn [fe_last]. intros Habs. discriminate Habs.
        * cbn [fe_toks].
          first [ exact Hfarf
                | (apply Forall_app; split; [exact Hfarf|];
                   constructor; [exact I | apply Forall_nil]) ].
        * cbn [fe_s fe_start fe_end].
          assert (E2bs2 : ls_blockstart (d_ls s2) = ls_blockstart (d_ls s))
            by reflexivity.
          assert (E2ss2 : ls_strstart (d_ls s2) = ls_strstart (d_ls s))
            by reflexivity.
          rewrite E2bs2, E2ss2.
          intros Hb. specialize (Hsldf Hb). lia. }
      (* the counter-bundle thread (fast-path consumer) *)
      split.
      { intros Hlv (HT & Ho & Hst).
      assert (HT2 : ZRTreeInv (d_ts s2))
        by (rewrite E2ts;
            first [exact HT | apply treeinv_tally_lit; exact HT]).
      assert (Ho2 : ts_optlen (d_ts s2) = 0)
        by (rewrite E2ts;
            first [ exact Ho
                  | exact (proj1 (statzero_tally_lit _ _ _ (conj Ho Hst))) ]).
      assert (Hst2 : ts_statlen (d_ts s2) = 0)
        by (rewrite E2ts;
            first [ exact Hst
                  | exact (proj2 (statzero_tally_lit _ _ _ (conj Ho Hst))) ]).
      assert (Hc2 : d_cfg s2 = d_cfg s) by reflexivity.
      split.
      { refine (conj _ (conj _ _)).
        - apply treeinv_flush; [rewrite Hc2, Ecfg; exact Hlv | exact HT2].
        - exact (proj1 (statzero_flush _ _)).
        - exact (proj2 (statzero_flush _ _)). }
      cbn [fe_s].
      exact (conj HT2 (conj Ho2 Hst2)). }
      split; [| cbn [fe_s]; unfold s2; sw_tail_s2_closer].
      { split.
        - cbn [fe_s]. reflexivity.
        - rewrite Fbs.
          replace (ls_strstart (d_ls s2)) with (ls_strstart (d_ls s))
            by reflexivity.
          exact Hss. }
    + (* FinishDone *)
      exists FinishDone, (flush_block_only 1 s2).
      split; [reflexivity|].
      split.
      { right. split; [reflexivity|].
        apply Z.eqb_neq in Eavo0.
        pose proof (flush_block_only_avo_nonneg 1 s2
                      ltac:(rewrite E2strm; exact Havo)).
        lia. }
      split; [exact HEv|].
      split; [reflexivity|].
      split; [cbn [EvChain fe_s fe_last];
              rewrite E2ts, E2strm; repeat split; reflexivity|].
      split; [cbn [EvTile fe_start fe_end];
              rewrite E2ls; lsimp; split; reflexivity|].
      split; [exact Hcomp|].
      split; [rewrite Fdn, E2strm; reflexivity|].
      split; [rewrite Fin, E2strm; reflexivity|].
      split; [rewrite Fti, E2strm; reflexivity|].
      split; [apply flush_block_only_avo_nonneg;
              rewrite E2strm; exact Havo|].
      split; [exact FK|].
      split; [rewrite Fwrap, ?Ewrap; reflexivity|].
      split; [rewrite Fcfg, ?Ecfg; reflexivity|].
      split.
      { intros Hlv HS.
        destruct HS as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
        unfold SldInv in Hsldf.
        assert (HT2 : ZRTreeInv (d_ts s2))
          by (rewrite E2ts;
              first [exact HTIf | apply treeinv_tally_lit; exact HTIf]).
        assert (Hc2 : d_cfg s2 = d_cfg s) by reflexivity.
        split.
        { apply treeinv_flush; [rewrite Hc2, Ecfg; exact Hlv | exact HT2]. }
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        * cbn [fe_s]. exact HT2.
        * cbn [fe_s]. rewrite E2ts.
          first [ exact Holf
                | exact (proj1 (statzero_tally_lit _ _ _ (conj Holf Hslf))) ].
        * cbn [fe_s]. rewrite E2ts.
          first [ exact Hslf
                | exact (proj2 (statzero_tally_lit _ _ _ (conj Holf Hslf))) ].
        * cbn [fe_last]. intros Habs. discriminate Habs.
        * cbn [fe_toks].
          first [ exact Hfarf
                | (apply Forall_app; split; [exact Hfarf|];
                   constructor; [exact I | apply Forall_nil]) ].
        * cbn [fe_s fe_start fe_end].
          assert (E2bs2 : ls_blockstart (d_ls s2) = ls_blockstart (d_ls s))
            by reflexivity.
          assert (E2ss2 : ls_strstart (d_ls s2) = ls_strstart (d_ls s))
            by reflexivity.
          rewrite E2bs2, E2ss2.
          intros Hb. specialize (Hsldf Hb). lia. }
      (* the counter-bundle thread (fast-path consumer) *)
      split.
      { intros Hlv (HT & Ho & Hst).
      assert (HT2 : ZRTreeInv (d_ts s2))
        by (rewrite E2ts;
            first [exact HT | apply treeinv_tally_lit; exact HT]).
      assert (Ho2 : ts_optlen (d_ts s2) = 0)
        by (rewrite E2ts;
            first [ exact Ho
                  | exact (proj1 (statzero_tally_lit _ _ _ (conj Ho Hst))) ]).
      assert (Hst2 : ts_statlen (d_ts s2) = 0)
        by (rewrite E2ts;
            first [ exact Hst
                  | exact (proj2 (statzero_tally_lit _ _ _ (conj Ho Hst))) ]).
      assert (Hc2 : d_cfg s2 = d_cfg s) by reflexivity.
      split.
      { refine (conj _ (conj _ _)).
        - apply treeinv_flush; [rewrite Hc2, Ecfg; exact Hlv | exact HT2].
        - exact (proj1 (statzero_flush _ _)).
        - exact (proj2 (statzero_flush _ _)). }
      cbn [fe_s].
      exact (conj HT2 (conj Ho2 Hst2)). }
      split; [| cbn [fe_s]; unfold s2; sw_tail_s2_closer].
      { split.
        - cbn [fe_s]. reflexivity.
        - rewrite Fbs.
          replace (ls_strstart (d_ls s2)) with (ls_strstart (d_ls s))
            by reflexivity.
          exact Hss. }
  - (* ---- a pending literal to tally ---- *)
    assert (Hma1 : ls_matchavail (d_ls s) = 1).
    { apply Z.eqb_neq in Ema0.
      destruct (di_ma _ _ _ _ _ _ HI); congruence. }
    pose proof (di_ma1 _ _ _ _ _ _ HI Hma1) as Hss1.
    (* the byte *)
    assert (Hc : 0 <= ls_window (d_ls s) (ls_strstart (d_ls s) - 1) < 256).
    { apply (wininv_bytes g slid (d_ls s) (d_strm s) HW). lia. }
    assert (Hcval : ls_window (d_ls s) (ls_strstart (d_ls s) - 1)
                    = nth (Z.to_nat (slid + (ls_strstart (d_ls s) - 1)))
                          (zs_done (d_strm s)) 0).
    { apply (wi_win _ _ _ _ HW). lia. }
    set (c := ls_window (d_ls s) (ls_strstart (d_ls s) - 1)) in *.
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
    assert (Hres' : resolve (firstn (Z.to_nat (slid + ls_blockstart (d_ls s)))
                      (zs_done (d_strm s))) (toks ++ [TLit c])
                    = Some (firstn (Z.to_nat (slid + ls_strstart (d_ls s)))
                        (zs_done (d_strm s)))).
    { rewrite resolve_app.
      pose proof (di_res _ _ _ _ _ _ HI) as Hres.
      rewrite Hma1 in Hres.
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
    replace (Z.eqb Z_FINISH Z_FINISH) with true by reflexivity.
    cbv iota.
    match goal with
    | |- context [flush_block 1 ?X] => set (s2 := X)
    end.
    assert (E2ts : d_ts s2 = snd tt) by reflexivity.
    assert (E2strm : d_strm s2 = d_strm s) by reflexivity.
    assert (E2ss : ls_strstart (d_ls s2) = ls_strstart (d_ls s))
      by reflexivity.
    assert (E2bs : ls_blockstart (d_ls s2) = ls_blockstart (d_ls s))
      by reflexivity.
    assert (HW2 : WinInv g slid (d_ls s2) (d_strm s2)).
    { destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
      constructor; unfold s2; lsimp; assumption. }
    assert (Hsn3 : ts_symnext (d_ts s) + 3 <= dg_sym_end g) by lia.
    destruct (flush_block_only_step g wbits hbits wrap slid
                (toks ++ [TLit c]) s2 1 Hg
                ltac:(unfold s2; lsimp; exact Ecfg)
                ltac:(unfold s2; lsimp; exact Ewrap)
                HW2
                ltac:(rewrite E2strm; exact (di_ck _ _ _ _ _ _ HI))
                ltac:(rewrite E2ts; rewrite <- Etok; exact Hbuf')
                ltac:(rewrite E2ts; rewrite <- Etok; exact Hfreq')
                Henc'
                ltac:(rewrite E2ts, Hsn'; lia)
                ltac:(lia)
                ltac:(unfold s2; lsimp; exact (di_bb0 _ _ _ _ _ _ HI))
                ltac:(unfold s2; lsimp;
                      pose proof (di_bble _ _ _ _ _ _ HI); lia)
                ltac:(unfold s2; lsimp; exact Hres'))
      as (HEv & Fcfg & Fwrap & FW & FK & FBuf & FFreq & FSn & Fbs & Fss
          & Fla & Fma & Fml & Fpl & Fpm & Fms & Fwin & Fprev & Fhead
          & Finsh & Fins & Fws & Fdn & Fin & Fti & Favo).
    cbv zeta in HEv.
    unfold flush_block. cbv zeta.
    exists {| fe_s := s2; fe_last := 1;
              fe_start := slid + ls_blockstart (d_ls s2);
              fe_end := slid + ls_strstart (d_ls s2);
              fe_toks := toks ++ [TLit c] |}.
    destruct (Z.eqb (zs_availout (d_strm (flush_block_only 1 s2))) 0)
      eqn:Eavo0; cbv iota.
    + (* FinishStarted *)
      apply Z.eqb_eq in Eavo0.
      cbn [Z.eqb]. cbv iota.
      exists FinishStarted, (flush_block_only 1 s2).
      split; [reflexivity|].
      split; [left; split; [reflexivity | exact Eavo0]|].
      split; [exact HEv|].
      split; [reflexivity|].
      split; [cbn [EvChain fe_s fe_last];
              rewrite E2ts, E2strm, Fbw; repeat split; reflexivity|].
      split; [cbn [EvTile fe_start fe_end];
              rewrite E2bs, E2ss; split; reflexivity|].
      split; [exact Hcomp|].
      split; [rewrite Fdn, E2strm; reflexivity|].
      split; [rewrite Fin, E2strm; reflexivity|].
      split; [rewrite Fti, E2strm; reflexivity|].
      split; [lia|].
      split; [exact FK|].
      split; [rewrite Fwrap, ?Ewrap; reflexivity|].
      split; [rewrite Fcfg, ?Ecfg; reflexivity|].
      split.
      { intros Hlv HS.
        destruct HS as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
        unfold SldInv in Hsldf.
        assert (HT2 : ZRTreeInv (d_ts s2))
          by (rewrite E2ts;
              first [exact HTIf | apply treeinv_tally_lit; exact HTIf]).
        assert (Hc2 : d_cfg s2 = d_cfg s) by reflexivity.
        split.
        { apply treeinv_flush; [rewrite Hc2, Ecfg; exact Hlv | exact HT2]. }
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        * cbn [fe_s]. exact HT2.
        * cbn [fe_s]. rewrite E2ts.
          first [ exact Holf
                | exact (proj1 (statzero_tally_lit _ _ _ (conj Holf Hslf))) ].
        * cbn [fe_s]. rewrite E2ts.
          first [ exact Hslf
                | exact (proj2 (statzero_tally_lit _ _ _ (conj Holf Hslf))) ].
        * cbn [fe_last]. intros Habs. discriminate Habs.
        * cbn [fe_toks].
          first [ exact Hfarf
                | (apply Forall_app; split; [exact Hfarf|];
                   constructor; [exact I | apply Forall_nil]) ].
        * cbn [fe_s fe_start fe_end].
          assert (E2bs2 : ls_blockstart (d_ls s2) = ls_blockstart (d_ls s))
            by reflexivity.
          assert (E2ss2 : ls_strstart (d_ls s2) = ls_strstart (d_ls s))
            by reflexivity.
          rewrite E2bs2, E2ss2.
          intros Hb. specialize (Hsldf Hb). lia. }
      (* the counter-bundle thread (fast-path consumer) *)
      split.
      { intros Hlv (HT & Ho & Hst).
      assert (HT2 : ZRTreeInv (d_ts s2))
        by (rewrite E2ts;
            first [exact HT | apply treeinv_tally_lit; exact HT]).
      assert (Ho2 : ts_optlen (d_ts s2) = 0)
        by (rewrite E2ts;
            first [ exact Ho
                  | exact (proj1 (statzero_tally_lit _ _ _ (conj Ho Hst))) ]).
      assert (Hst2 : ts_statlen (d_ts s2) = 0)
        by (rewrite E2ts;
            first [ exact Hst
                  | exact (proj2 (statzero_tally_lit _ _ _ (conj Ho Hst))) ]).
      assert (Hc2 : d_cfg s2 = d_cfg s) by reflexivity.
      split.
      { refine (conj _ (conj _ _)).
        - apply treeinv_flush; [rewrite Hc2, Ecfg; exact Hlv | exact HT2].
        - exact (proj1 (statzero_flush _ _)).
        - exact (proj2 (statzero_flush _ _)). }
      cbn [fe_s].
      exact (conj HT2 (conj Ho2 Hst2)). }
      split; [| cbn [fe_s]; unfold s2; sw_tail_s2_closer].
      { split.
        - cbn [fe_s]. reflexivity.
        - rewrite Fbs.
          replace (ls_strstart (d_ls s2)) with (ls_strstart (d_ls s))
            by reflexivity.
          exact Hss. }
    + (* FinishDone *)
      exists FinishDone, (flush_block_only 1 s2).
      split; [reflexivity|].
      split.
      { right. split; [reflexivity|].
        apply Z.eqb_neq in Eavo0.
        pose proof (flush_block_only_avo_nonneg 1 s2
                      ltac:(rewrite E2strm; exact Havo)).
        lia. }
      split; [exact HEv|].
      split; [reflexivity|].
      split; [cbn [EvChain fe_s fe_last];
              rewrite E2ts, E2strm, Fbw; repeat split; reflexivity|].
      split; [cbn [EvTile fe_start fe_end];
              rewrite E2bs, E2ss; split; reflexivity|].
      split; [exact Hcomp|].
      split; [rewrite Fdn, E2strm; reflexivity|].
      split; [rewrite Fin, E2strm; reflexivity|].
      split; [rewrite Fti, E2strm; reflexivity|].
      split; [apply flush_block_only_avo_nonneg;
              rewrite E2strm; exact Havo|].
      split; [exact FK|].
      split; [rewrite Fwrap, ?Ewrap; reflexivity|].
      split; [rewrite Fcfg, ?Ecfg; reflexivity|].
      split.
      { intros Hlv HS.
        destruct HS as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
        unfold SldInv in Hsldf.
        assert (HT2 : ZRTreeInv (d_ts s2))
          by (rewrite E2ts;
              first [exact HTIf | apply treeinv_tally_lit; exact HTIf]).
        assert (Hc2 : d_cfg s2 = d_cfg s) by reflexivity.
        split.
        { apply treeinv_flush; [rewrite Hc2, Ecfg; exact Hlv | exact HT2]. }
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        * cbn [fe_s]. exact HT2.
        * cbn [fe_s]. rewrite E2ts.
          first [ exact Holf
                | exact (proj1 (statzero_tally_lit _ _ _ (conj Holf Hslf))) ].
        * cbn [fe_s]. rewrite E2ts.
          first [ exact Hslf
                | exact (proj2 (statzero_tally_lit _ _ _ (conj Holf Hslf))) ].
        * cbn [fe_last]. intros Habs. discriminate Habs.
        * cbn [fe_toks].
          first [ exact Hfarf
                | (apply Forall_app; split; [exact Hfarf|];
                   constructor; [exact I | apply Forall_nil]) ].
        * cbn [fe_s fe_start fe_end].
          assert (E2bs2 : ls_blockstart (d_ls s2) = ls_blockstart (d_ls s))
            by reflexivity.
          assert (E2ss2 : ls_strstart (d_ls s2) = ls_strstart (d_ls s))
            by reflexivity.
          rewrite E2bs2, E2ss2.
          intros Hb. specialize (Hsldf Hb). lia. }
      (* the counter-bundle thread (fast-path consumer) *)
      split.
      { intros Hlv (HT & Ho & Hst).
      assert (HT2 : ZRTreeInv (d_ts s2))
        by (rewrite E2ts;
            first [exact HT | apply treeinv_tally_lit; exact HT]).
      assert (Ho2 : ts_optlen (d_ts s2) = 0)
        by (rewrite E2ts;
            first [ exact Ho
                  | exact (proj1 (statzero_tally_lit _ _ _ (conj Ho Hst))) ]).
      assert (Hst2 : ts_statlen (d_ts s2) = 0)
        by (rewrite E2ts;
            first [ exact Hst
                  | exact (proj2 (statzero_tally_lit _ _ _ (conj Ho Hst))) ]).
      assert (Hc2 : d_cfg s2 = d_cfg s) by reflexivity.
      split.
      { refine (conj _ (conj _ _)).
        - apply treeinv_flush; [rewrite Hc2, Ecfg; exact Hlv | exact HT2].
        - exact (proj1 (statzero_flush _ _)).
        - exact (proj2 (statzero_flush _ _)). }
      cbn [fe_s].
      exact (conj HT2 (conj Ho2 Hst2)). }
      split; [| cbn [fe_s]; unfold s2; sw_tail_s2_closer].
      { split.
        - cbn [fe_s]. reflexivity.
        - rewrite Fbs.
          replace (ls_strstart (d_ls s2)) with (ls_strstart (d_ls s))
            by reflexivity.
          exact Hss. }
Qed.

Print Assumptions ds_tail_finish.
