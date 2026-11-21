(** * SwStep — the slow-path walk, part W4b: ONE [ds_step] at [Z_FINISH].

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W4.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    THE TRICHOTOMY.  At [Z_FINISH] the NeedMore top-exit is dead
    ([flush <> Z_NO_FLUSH]), so one trip either
      * BREAKs — the fill came back with zero lookahead, which by SwDrain
        means the input is fully consumed;
      * CONTinues — [DsInv] is re-established, any flush is exported as an
        [EvOk] event with the output chained ([EvChain]), and the measure
        [|zs_in| + lookahead] strictly drops (the fill conserves it, every
        arm debits lookahead);
      * RETurns [NeedMore] — an output-buffer exhaustion ([avail_out = 0])
        at a mid-loop flush; exported with the same invariant + events so
        the caller can refute it from a size bound.

    [EvChain] is the output-side ledger: each event's snapshot carries the
    accumulated bit-writer/output/avail_out, and the flush of that
    snapshot produces the next accumulator.  G3 folds the actual bitstream
    out of exactly this structure. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwArm2 SwArm3
  SwArm1a SwArm1b SwDrain ZRTreeState ZREvSnap.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac dsimp :=
  cbn [d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm
       zs_in zs_done zs_out zs_availout zs_totalin zs_totalout zs_adler
       zs_datatype
       setZ_in setZ_done setZ_out setZ_availout setZ_totalin setZ_totalout
       setZ_adler setZ_datatype
       ls_lookahead ls_strstart ls_matchavail ls_matchlen ls_prevlen
       ls_blockstart ls_matchstart ls_prevmatch
       setL_lookahead setL_strstart setL_matchavail setL_matchlen
       setL_prevlen setL_matchstart setL_blockstart ls_window
       fst snd].

(** ** 1. The output ledger *)

Fixpoint EvChain (evs : list FlushEv) (bw : BW) (out : list Z) (avo : Z)
                 (bw' : BW) (out' : list Z) (avo' : Z) : Prop :=
  match evs with
  | [] => bw' = bw /\ out' = out /\ avo' = avo
  | ev :: r =>
      ts_bw (d_ts (fe_s ev)) = bw
      /\ zs_out (d_strm (fe_s ev)) = out
      /\ zs_availout (d_strm (fe_s ev)) = avo
      /\ EvChain r
           (ts_bw (d_ts (flush_block_only (fe_last ev) (fe_s ev))))
           (zs_out (d_strm (flush_block_only (fe_last ev) (fe_s ev))))
           (zs_availout (d_strm (flush_block_only (fe_last ev) (fe_s ev))))
           bw' out' avo'
  end.

Lemma evchain_app : forall e1 e2 bw out avo bw1 out1 avo1 bw2 out2 avo2,
  EvChain e1 bw out avo bw1 out1 avo1 ->
  EvChain e2 bw1 out1 avo1 bw2 out2 avo2 ->
  EvChain (e1 ++ e2) bw out avo bw2 out2 avo2.
Proof.
  induction e1 as [|ev e1 IH];
    intros e2 bw out avo bw1 out1 avo1 bw2 out2 avo2 H1 H2.
  - cbn [EvChain] in H1. destruct H1 as (->&->&->). exact H2.
  - cbn [EvChain] in H1 |- *.
    destruct H1 as (Hb & Ho & Ha & Hr).
    repeat split; try assumption.
    exact (IH e2 _ _ _ _ _ _ _ _ _ Hr H2).
Qed.

(** The input-side ledger: consecutive flush events TILE the consumed
    input — each block starts where the previous one ended (in input
    coordinates, [slid + blockstart], conserved across window slides). *)
Fixpoint EvTile (evs : list FlushEv) (bst bst' : Z) : Prop :=
  match evs with
  | [] => bst' = bst
  | ev :: r => fe_start ev = bst /\ EvTile r (fe_end ev) bst'
  end.

Lemma evtile_app : forall e1 e2 a b c,
  EvTile e1 a b -> EvTile e2 b c -> EvTile (e1 ++ e2) a c.
Proof.
  induction e1 as [|ev e1 IH]; intros e2 a b c H1 H2.
  - cbn [EvTile] in H1. subst b. exact H2.
  - cbn [EvTile] in H1 |- *.
    destruct H1 as (He & Hr).
    split; [exact He | exact (IH e2 _ _ _ Hr H2)].
Qed.

(** ** 2. The flush keeps [avail_out] nonnegative *)

Lemma flush_pending_avo_nonneg : forall s,
  0 <= zs_availout (d_strm s) ->
  0 <= zs_availout (d_strm (flush_pending s)).
Proof.
  intros s Havo. unfold flush_pending. cbv zeta.
  pose proof (zlen_nonneg (bw_out (ts_bw (tr_flush_bits (d_ts s))))) as Hpd.
  destruct (Z.ltb_spec (zs_availout (d_strm s))
              (zlen (bw_out (ts_bw (tr_flush_bits (d_ts s)))))) as [H|H];
    cbv iota.
  - destruct (Z.eqb_spec (zs_availout (d_strm s)) 0) as [E|E]; dsimp; lia.
  - destruct (Z.eqb_spec (zlen (bw_out (ts_bw (tr_flush_bits (d_ts s))))) 0)
      as [E|E]; dsimp; lia.
Qed.

Lemma flush_block_only_avo_nonneg : forall last s,
  0 <= zs_availout (d_strm s) ->
  0 <= zs_availout (d_strm (flush_block_only last s)).
Proof.
  intros last s Havo.
  unfold flush_block_only. cbv zeta.
  apply flush_pending_avo_nonneg. dsimp. exact Havo.
Qed.

(** The hash-insert loop never touches the block base. *)
Lemma insert_string_bs : forall g str l,
  ls_blockstart (snd (insert_string g str l)) = ls_blockstart l.
Proof. reflexivity. Qed.

Lemma ds_insert_bs : forall f g mi l,
  ls_blockstart (ds_insert f g mi l) = ls_blockstart l.
Proof.
  induction f as [|f IH]; intros g mi l; [reflexivity|].
  cbn [ds_insert]. cbv zeta.
  destruct (Z.leb _ _); destruct (Z.eqb _ _); rewrite ?IH; reflexivity.
Qed.

(** ** 3. One trip *)

Theorem ds_step_finish : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  dg_strategy g = 0 ->
  DsInv g wrap slid Ins toks s ->
  0 <= zs_availout (d_strm s) ->
  (* BREAK: input drained *)
  (exists s' slid' Ins',
      ds_step Z_FINISH s = DsBreak s'
      /\ DsInv g wrap slid' Ins' toks s'
      /\ ls_lookahead (d_ls s') = 0
      /\ zs_in (d_strm s') = []
      /\ (exists nd, zs_done (d_strm s') = zs_done (d_strm s) ++ nd)
      /\ zs_done (d_strm s') ++ zs_in (d_strm s')
         = zs_done (d_strm s) ++ zs_in (d_strm s)
      /\ slid' + ls_blockstart (d_ls s') = slid + ls_blockstart (d_ls s)
      /\ d_ts s' = d_ts s
      /\ zs_out (d_strm s') = zs_out (d_strm s)
      /\ zs_availout (d_strm s') = zs_availout (d_strm s)
      /\ (ZRSideInv g toks s -> ZRSideInv g toks s'))
  \/ (* CONT *)
  (exists s' evs slid' Ins' toks',
      ds_step Z_FINISH s = DsCont s'
      /\ DsInv g wrap slid' Ins' toks' s'
      /\ Forall (EvOk g wrap (zs_done (d_strm s'))) evs
      /\ Forall (fun ev => fe_last ev = 0) evs
      /\ EvChain evs (ts_bw (d_ts s)) (zs_out (d_strm s))
                     (zs_availout (d_strm s))
                     (ts_bw (d_ts s')) (zs_out (d_strm s'))
                     (zs_availout (d_strm s'))
      /\ (exists nd, zs_done (d_strm s') = zs_done (d_strm s) ++ nd)
      /\ zs_done (d_strm s') ++ zs_in (d_strm s')
         = zs_done (d_strm s) ++ zs_in (d_strm s)
      /\ EvTile evs (slid + ls_blockstart (d_ls s))
                    (slid' + ls_blockstart (d_ls s'))
      /\ 0 <= zs_availout (d_strm s')
      /\ zlen (zs_in (d_strm s')) + ls_lookahead (d_ls s')
         < zlen (zs_in (d_strm s)) + ls_lookahead (d_ls s)
      /\ (0 < dg_level g -> ZRSideInv g toks s ->
          ZRSideInv g toks' s'
          /\ Forall (EvSnapOk g) evs)
      /\ sw_step_sites (ds_fill s) evs)
  \/ (* RET: avail_out exhausted at a flush *)
  (exists s' evs slid' Ins' toks',
      ds_step Z_FINISH s = DsRet NeedMore s'
      /\ DsInv g wrap slid' Ins' toks' s'
      /\ Forall (EvOk g wrap (zs_done (d_strm s'))) evs
      /\ Forall (fun ev => fe_last ev = 0) evs
      /\ EvChain evs (ts_bw (d_ts s)) (zs_out (d_strm s))
                     (zs_availout (d_strm s))
                     (ts_bw (d_ts s')) (zs_out (d_strm s'))
                     (zs_availout (d_strm s'))
      /\ (exists nd, zs_done (d_strm s') = zs_done (d_strm s) ++ nd)
      /\ zs_done (d_strm s') ++ zs_in (d_strm s')
         = zs_done (d_strm s) ++ zs_in (d_strm s)
      /\ EvTile evs (slid + ls_blockstart (d_ls s))
                    (slid' + ls_blockstart (d_ls s'))
      /\ zs_availout (d_strm s') = 0
      /\ (0 < dg_level g -> ZRSideInv g toks s ->
          ZRSideInv g toks' s'
          /\ Forall (EvSnapOk g) evs)
      /\ sw_step_sites (ds_fill s) evs).
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg Hstrat HI Havo.
  (* ---- the fill ---- *)
  destruct (dsinv_fill g wbits hbits wrap slid Ins toks s Hg HI)
    as (slid1 & Ins1 & HI1 & HP1 & Ets1 & Estat1 & Ecfg1 & Ewrap1).
  set (sf := ds_fill s) in *.
  pose proof (sp_out _ _ _ _ _ _ _ HP1) as Eout1.
  pose proof (sp_avout _ _ _ _ _ _ _ HP1) as Eavo1.
  pose proof (sp_cons _ _ _ _ _ _ _ HP1) as Econs1.
  destruct (sp_donex _ _ _ _ _ _ _ HP1) as (nd1 & Ednx1).
  pose proof (sp_ss _ _ _ _ _ _ _ HP1) as Ess1.
  pose proof (sp_bs _ _ _ _ _ _ _ HP1) as Ebs1.
  pose proof (wi_done _ _ _ _ (di_win _ _ _ _ _ _ HI)) as Hd0.
  pose proof (wi_done _ _ _ _ (di_win _ _ _ _ _ _ HI1)) as Hd1.
  pose proof (wi_la _ _ _ _ (di_win _ _ _ _ _ _ HI1)) as Hla1'.
  assert (Ebw1 : ts_bw (d_ts sf) = ts_bw (d_ts s))
    by (rewrite Ets1; reflexivity).
  assert (Havof : 0 <= zs_availout (d_strm sf)) by lia.
  pose proof (sp_ms _ _ _ _ _ _ _ HP1) as Ems1.
  pose proof (sp_ml _ _ _ _ _ _ _ HP1) as Eml1.
  pose proof (sp_sslb _ _ _ _ _ _ _ HP1) as Esslb1.
  pose proof (wi_ss _ _ _ _ (di_win _ _ _ _ _ _ HI1)) as Hssf0.
  assert (Hside1 : forall toks0, ZRSideInv g toks0 s -> ZRSideInv g toks0 sf).
  { intros toks0 (HTI0 & Hol0 & Hsl0 & Hfar0 & Hpend0 & Hsld0).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    - rewrite Ets1. exact HTI0.
    - rewrite Ets1. exact Hol0.
    - rewrite Ets1. exact Hsl0.
    - exact Hfar0.
    - unfold FarPend in *. rewrite Eml1. intros H3.
      specialize (Hpend0 H3). lia.
    - unfold SldInv in *. intros Hbs.
      destruct Esslb1 as [Ess'|Hmd].
      + assert (Hb0 : ls_blockstart (d_ls s) < 0) by lia.
        specialize (Hsld0 Hb0). lia.
      + lia. }
  assert (Hm1 : zlen (zs_in (d_strm sf)) + ls_lookahead (d_ls sf)
              = zlen (zs_in (d_strm s)) + ls_lookahead (d_ls s)).
  { assert (Ezl : zlen (zs_done (d_strm sf)) + zlen (zs_in (d_strm sf))
                = zlen (zs_done (d_strm s)) + zlen (zs_in (d_strm s)))
      by (unfold zlen; rewrite <- !Nat2Z.inj_add, <- !length_app, Econs1;
          reflexivity).
    lia. }
  (* ---- the top of the trip ---- *)
  destruct (ds_need s && (Z.eqb (ls_lookahead (d_ls sf)) 0)) eqn:Ebrk.
  - (* BREAK *)
    left.
    pose proof Ebrk as Ebrk'.
    apply andb_true_iff in Ebrk'. destruct Ebrk' as [Eneed Ela0].
    apply Z.eqb_eq in Ela0.
    exists sf, slid1, Ins1.
    split.
    { unfold ds_step.
      replace (Z.eqb Z_FINISH Z_NO_FLUSH) with false by reflexivity.
      rewrite andb_false_r.
      fold sf. rewrite Ebrk. reflexivity. }
    repeat apply conj; try assumption.
    + apply (ds_fill_drain g wbits hbits wrap slid Ins toks s Hg HI).
      fold sf. rewrite Ela0. unfold MIN_LOOKAHEAD. lia.
    + exists nd1. exact Ednx1.
    + intro HS. exact (Hside1 _ HS).
  - (* the body runs *)
    assert (Estep : ds_step Z_FINISH s = ds_body Z_FINISH sf).
    { unfold ds_step.
      replace (Z.eqb Z_FINISH Z_NO_FLUSH) with false by reflexivity.
      rewrite andb_false_r.
      fold sf. rewrite Ebrk. reflexivity. }
    assert (Hla1 : 1 <= ls_lookahead (d_ls sf)).
    { apply andb_false_iff in Ebrk.
      destruct Ebrk as [Eneed|Ela0].
      - unfold ds_need in Eneed. apply Z.ltb_ge in Eneed.
        pose proof (sp_lagrow _ _ _ _ _ _ _ HP1).
        unfold MIN_LOOKAHEAD in Eneed. lia.
      - apply Z.eqb_neq in Ela0. lia. }
    rewrite ds_body_shape, (di_cfg _ _ _ _ _ _ HI1) in Estep.
    cbv zeta in Estep.
    destruct (dsb_top_facts g wbits hbits wrap slid1 Ins1 toks sf
                Hg Hstrat HI1) as (Ins2 & Htop).
    cbv zeta in Htop.
    set (l2 := dsb_l2 g (fst (dsb_ph g (d_ls sf)))
                 (dsb_l1 (snd (dsb_ph g (d_ls sf))))) in *.
    destruct Htop as (Hcinv2 & Hhi2 & Ew & Ess & Ela & Ebs & Ema & Ews
                      & Eins & Epl & Epm & Einsh & Hmlb & Hdisp & Hfar2).
    destruct ((Z.leb MIN_MATCH (ls_prevlen l2))
              && (Z.leb (ls_matchlen l2) (ls_prevlen l2))) eqn:Eg1.
    + (* ---- ARM 1: match tally ---- *)
      pose proof Eg1 as Hpl3.
      apply andb_true_iff in Hpl3. destruct Hpl3 as [Hpl3 _].
      apply Z.leb_le in Hpl3. unfold MIN_MATCH in Hpl3.
      destruct (dsb_arm1_inv g wbits hbits wrap slid1 Ins1 Ins2 toks sf l2
                  Hg HI1 Hcinv2 Hhi2 Ew Ess Ela Ebs Ema Ews Eins Einsh
                  Epl Epm Eg1)
        as (Ins' & toks' & evs & HFor & Hdisj).
      cbv zeta in HFor, Hdisj.
      destruct Hdisj as [HNo|HYes].
      * (* no flush: DsCont s3 *)
        destruct HNo as (Eflag & Eevs & HInv & Edn & Ein & Ela5 & Ess5
                         & Ebs5 & Ebw5 & Eout5 & Eavo5 & Etoks5).
        rewrite Eflag in Estep.
        match type of Estep with
        | _ = DsCont ?X => set (s3 := X) in *
        end.
        subst evs.
        right. left.
        exists s3, [], slid1, Ins', toks'.
        split; [exact Estep|].
        split; [exact HInv|].
        split; [apply Forall_nil|].
        split; [apply Forall_nil|].
        split; [cbn [EvChain]; repeat split; congruence|].
        split; [exists nd1; rewrite Edn; exact Ednx1|].
        split; [rewrite Edn, Ein; exact Econs1|].
        split; [cbn [EvTile]; rewrite Ebs5; lia|].
        split; [rewrite Eavo5; lia|].
        split; [rewrite Ein, Ela5; lia|].
        split; [| sw_sites_close l2 Ecfg1 HI Hma1 Eg2 Hdisj].
        intros Hlv HS.
        pose proof (Hside1 _ HS) as HSf.
        destruct HSf as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
        unfold FarPend in Hpendf. unfold SldInv in Hsldf.
        split; [|apply Forall_nil].
        assert (E3ml : ls_matchlen (d_ls s3) = MIN_MATCH - 1)
          by (unfold s3; dsimp; reflexivity).
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        -- unfold s3. dsimp. apply treeinv_tally_dist. exact HTIf.
        -- unfold s3. dsimp.
           exact (proj1 (statzero_tally_dist _ _ _ _ (conj Holf Hslf))).
        -- unfold s3. dsimp.
           exact (proj2 (statzero_tally_dist _ _ _ _ (conj Holf Hslf))).
        -- rewrite Etoks5. apply Forall_app. split; [exact Hfarf|].
           constructor; [|apply Forall_nil].
           cbn [FarOkTok]. intros Hl3.
           rewrite Epl in Hl3.
           assert (Hd : ls_strstart (d_ls sf) - ls_matchstart (d_ls sf)
                        <= TOO_FAR + 1)
             by (apply Hpendf; unfold MIN_MATCH; exact Hl3).
           rewrite Ess, Epm. lia.
        -- unfold FarPend. rewrite E3ml.
           intros Habs. exfalso. unfold MIN_MATCH in Habs. lia.
        -- unfold SldInv. rewrite Ebs5, Ess5.
           intros Hb. specialize (Hsldf Hb). lia.
      * (* flush: DsRet or DsCont on avail_out *)
        destruct HYes as (ev & Eflag & Eevs & Elast & Efes & Efst & Efen
                          & Ebs5 & Ebwe & Eoute & Eavoe & HInv & Edn & Ein
                          & Ela5 & Ess5 & Etokse & Etoks0).
        rewrite Eflag in Estep.
        unfold flush_block in Estep. cbv zeta in Estep.
        match type of HInv with
        | DsInv _ _ _ _ _ (flush_block_only 0 ?X) => set (s3 := X) in *
        end.
        subst evs.
        destruct (Z.eqb (zs_availout (d_strm (flush_block_only 0 s3))) 0)
          eqn:Eavo0.
        -- (* avail_out exhausted: DsRet NeedMore *)
           cbn [Z.eqb] in Estep. cbv iota in Estep.
           apply Z.eqb_eq in Eavo0.
           right. right.
           exists (flush_block_only 0 s3), [ev], slid1, Ins', toks'.
           split; [exact Estep|].
           split; [exact HInv|].
           split; [rewrite Edn; exact HFor|].
           split; [constructor; [exact Elast | apply Forall_nil]|].
           split; [cbn [EvChain]; rewrite Elast, Efes;
                   repeat split; congruence|].
           split; [exists nd1; rewrite Edn; exact Ednx1|].
           split; [rewrite Edn, Ein; exact Econs1|].
           split; [cbn [EvTile]; rewrite Efst, Efen, Ebs5;
                   split; lia|].
           split; [exact Eavo0|].
           split; [| sw_sites_close l2 Ecfg1 HI Hma1 Eg2 Hdisj].
           intros Hlv HS.
           pose proof (Hside1 _ HS) as HSf.
           destruct HSf as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
           unfold FarPend in Hpendf. unfold SldInv in Hsldf.
           assert (HT3 : ZRTreeInv (d_ts s3))
             by (unfold s3; dsimp; apply treeinv_tally_dist; exact HTIf).
           assert (Hcfg3 : d_cfg s3 = g)
             by (unfold s3; dsimp; rewrite Ecfg1;
                 exact (di_cfg _ _ _ _ _ _ HI)).
           assert (Hstat3 : ts_optlen (d_ts s3) = 0
                            /\ ts_statlen (d_ts s3) = 0)
             by (unfold s3; dsimp;
                 exact (statzero_tally_dist _ _ _ _ (conj Holf Hslf))).
           assert (E3ml : ls_matchlen (d_ls s3) = MIN_MATCH - 1)
             by (unfold s3; dsimp; reflexivity).
           assert (E3bs : ls_blockstart (d_ls s3) = ls_blockstart (d_ls sf))
             by (unfold s3; dsimp; rewrite ds_insert_bs; dsimp; exact Ebs).
           assert (E3sn : ts_symnext (d_ts s3) = dg_sym_end g)
             by (unfold s3; dsimp; apply tally_dist_full; exact Eflag).
           assert (E3ss : ls_strstart (d_ls s3)
                          = ls_strstart (d_ls sf) + ls_prevlen l2 - 1).
           { rewrite <- Ess5. rewrite flush_block_only_ls. dsimp.
             reflexivity. }
           assert (Htokfar : Forall FarOkTok
                     (toks ++ [TMatch (ls_prevlen l2)
                                 (ls_strstart l2 - 1 - ls_prevmatch l2)])).
           { apply Forall_app. split; [exact Hfarf|].
             constructor; [|apply Forall_nil].
             cbn [FarOkTok]. intros Hl3.
             rewrite Epl in Hl3.
             assert (Hd : ls_strstart (d_ls sf) - ls_matchstart (d_ls sf)
                          <= TOO_FAR + 1)
               by (apply Hpendf; unfold MIN_MATCH; exact Hl3).
             rewrite Ess, Epm. lia. }
           split.
           { refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
             - apply treeinv_flush; [rewrite Hcfg3; exact Hlv | exact HT3].
             - exact (proj1 (statzero_flush _ _)).
             - exact (proj2 (statzero_flush _ _)).
             - rewrite Etoks0. apply Forall_nil.
             - unfold FarPend. rewrite flush_block_only_ls. dsimp.
               rewrite E3ml. intros Habs. exfalso.
               unfold MIN_MATCH in Habs. lia.
             - unfold SldInv. rewrite flush_block_only_ls. dsimp.
               intros Habs. exfalso. lia. }
           constructor; [|apply Forall_nil].
           refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
           ++ rewrite Efes. exact HT3.
           ++ rewrite Efes. exact (proj1 Hstat3).
           ++ rewrite Efes. exact (proj2 Hstat3).
           ++ intros _. rewrite Efes. exact E3sn.
           ++ rewrite Etokse. exact Htokfar.
           ++ rewrite Efes, E3bs, Efst, Efen.
              intros Hb. specialize (Hsldf Hb). lia.
        -- (* room left: DsCont *)
           cbv iota in Estep.
           right. left.
           exists (flush_block_only 0 s3), [ev], slid1, Ins', toks'.
           split; [exact Estep|].
           split; [exact HInv|].
           split; [rewrite Edn; exact HFor|].
           split; [constructor; [exact Elast | apply Forall_nil]|].
           split; [cbn [EvChain]; rewrite Elast, Efes;
                   repeat split; congruence|].
           split; [exists nd1; rewrite Edn; exact Ednx1|].
           split; [rewrite Edn, Ein; exact Econs1|].
           split; [cbn [EvTile]; rewrite Efst, Efen, Ebs5;
                   split; lia|].
           split; [apply flush_block_only_avo_nonneg;
                   unfold s3; dsimp; lia|].
           split; [rewrite Ein, Ela5; lia|].
           split; [| sw_sites_close l2 Ecfg1 HI Hma1 Eg2 Hdisj].
           intros Hlv HS.
           pose proof (Hside1 _ HS) as HSf.
           destruct HSf as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
           unfold FarPend in Hpendf. unfold SldInv in Hsldf.
           assert (HT3 : ZRTreeInv (d_ts s3))
             by (unfold s3; dsimp; apply treeinv_tally_dist; exact HTIf).
           assert (Hcfg3 : d_cfg s3 = g)
             by (unfold s3; dsimp; rewrite Ecfg1;
                 exact (di_cfg _ _ _ _ _ _ HI)).
           assert (Hstat3 : ts_optlen (d_ts s3) = 0
                            /\ ts_statlen (d_ts s3) = 0)
             by (unfold s3; dsimp;
                 exact (statzero_tally_dist _ _ _ _ (conj Holf Hslf))).
           assert (E3ml : ls_matchlen (d_ls s3) = MIN_MATCH - 1)
             by (unfold s3; dsimp; reflexivity).
           assert (E3bs : ls_blockstart (d_ls s3) = ls_blockstart (d_ls sf))
             by (unfold s3; dsimp; rewrite ds_insert_bs; dsimp; exact Ebs).
           assert (E3sn : ts_symnext (d_ts s3) = dg_sym_end g)
             by (unfold s3; dsimp; apply tally_dist_full; exact Eflag).
           assert (E3ss : ls_strstart (d_ls s3)
                          = ls_strstart (d_ls sf) + ls_prevlen l2 - 1).
           { rewrite <- Ess5. rewrite flush_block_only_ls. dsimp.
             reflexivity. }
           assert (Htokfar : Forall FarOkTok
                     (toks ++ [TMatch (ls_prevlen l2)
                                 (ls_strstart l2 - 1 - ls_prevmatch l2)])).
           { apply Forall_app. split; [exact Hfarf|].
             constructor; [|apply Forall_nil].
             cbn [FarOkTok]. intros Hl3.
             rewrite Epl in Hl3.
             assert (Hd : ls_strstart (d_ls sf) - ls_matchstart (d_ls sf)
                          <= TOO_FAR + 1)
               by (apply Hpendf; unfold MIN_MATCH; exact Hl3).
             rewrite Ess, Epm. lia. }
           split.
           { refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
             - apply treeinv_flush; [rewrite Hcfg3; exact Hlv | exact HT3].
             - exact (proj1 (statzero_flush _ _)).
             - exact (proj2 (statzero_flush _ _)).
             - rewrite Etoks0. apply Forall_nil.
             - unfold FarPend. rewrite flush_block_only_ls. dsimp.
               rewrite E3ml. intros Habs. exfalso.
               unfold MIN_MATCH in Habs. lia.
             - unfold SldInv. rewrite flush_block_only_ls. dsimp.
               intros Habs. exfalso. lia. }
           constructor; [|apply Forall_nil].
           refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
           ++ rewrite Efes. exact HT3.
           ++ rewrite Efes. exact (proj1 Hstat3).
           ++ rewrite Efes. exact (proj2 Hstat3).
           ++ intros _. rewrite Efes. exact E3sn.
           ++ rewrite Etokse. exact Htokfar.
           ++ rewrite Efes, E3bs, Efst, Efen.
              intros Hb. specialize (Hsldf Hb). lia.
    + (* ---- not arm 1 ---- *)
      destruct (negb (Z.eqb (ls_matchavail l2) 0)) eqn:Eg2.
      * (* ---- ARM 2: pending literal ---- *)
        apply negb_true_iff in Eg2. apply Z.eqb_neq in Eg2.
        assert (Hma1 : ls_matchavail l2 = 1).
        { destruct (di_ma _ _ _ _ _ _ HI1) as [E|E]; congruence. }
        destruct (dsb_arm2_inv g wbits hbits wrap slid1 Ins1 Ins2 toks sf l2
                    Hg HI1 Hla1 Havof Hcinv2 Hhi2 Ew Ess Ela Ebs Ema Ews
                    Eins Einsh Hmlb Epl Hdisp Eg1 Hma1)
          as (toks' & evs & HInv & HFor & Edn & Ein & Ela5 & Ess5 & Hdisj).
        match type of HInv with
        | DsInv _ _ _ _ _ ?X => set (s5 := X) in *
        end.
        destruct (Z.eqb (zs_availout (d_strm s5)) 0) eqn:Eavo0.
        -- (* DsRet NeedMore s5 *)
           cbv iota in Estep.
           apply Z.eqb_eq in Eavo0.
           right. right.
           exists s5, evs, slid1, Ins2, toks'.
           split; [exact Estep|].
           split; [exact HInv|].
           split; [exact HFor|].
           split.
           { destruct Hdisj as [(E1 & E2 & _)|(ev & E1 & E2 & E3 & _)];
               subst evs; [apply Forall_nil|].
             constructor; [exact E3 | apply Forall_nil]. }
           split.
           { destruct Hdisj as [(E1 & E2 & Ebs5 & Eb & Eo & Ea & _)
                               |(ev & E1 & E2 & E3 & Efst & Efen & Ebs5
                                 & Eb & Eo & Ea & Ets5 & Eout5 & Eavo5
                                 & Efes2 & _)];
               subst evs; cbn [EvChain]; repeat split; congruence. }
           split; [exists nd1; rewrite Edn; exact Ednx1|].
           split; [rewrite Edn, Ein; exact Econs1|].
           split.
           { destruct Hdisj as [(E1 & E2 & Ebs5 & Eb & Eo & Ea & _)
                               |(ev & E1 & E2 & E3 & Efst & Efen & Ebs5
                                 & Eb & Eo & Ea & Ets5 & Eout5 & Eavo5
                                 & Efes2 & _)];
               subst evs; cbn [EvTile];
               [ rewrite Ebs5; lia
               | rewrite Efst, Efen, Ebs5; split; lia ]. }
           split; [exact Eavo0|].
           split; [| sw_sites_close l2 Ecfg1 HI Hma1 Eg2 Hdisj].
           intros Hlv HS.
           pose proof (Hside1 _ HS) as HSf.
           destruct HSf as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
           unfold FarPend in Hpendf. unfold SldInv in Hsldf.
           assert (HT3 : ZRTreeInv (snd (tr_tally_lit
                     (ls_window l2 (ls_strstart l2 - 1)) (dg_sym_end g)
                     (d_ts sf))))
             by (apply treeinv_tally_lit; exact HTIf).
           assert (Hstat3 : ts_optlen (snd (tr_tally_lit
                       (ls_window l2 (ls_strstart l2 - 1)) (dg_sym_end g)
                       (d_ts sf))) = 0
                   /\ ts_statlen (snd (tr_tally_lit
                       (ls_window l2 (ls_strstart l2 - 1)) (dg_sym_end g)
                       (d_ts sf))) = 0)
             by (exact (statzero_tally_lit _ _ _ (conj Holf Hslf))).
           assert (Htokfar : Forall FarOkTok
                     (toks ++ [TLit (ls_window l2 (ls_strstart l2 - 1))])).
           { apply Forall_app. split; [exact Hfarf|].
             constructor; [exact I | apply Forall_nil]. }
           destruct Hdisj as [(E1 & E2 & Ebs5 & Eb & Eo & Ea & Etoks5)
                             |(ev & E1 & E2 & E3 & Efst & Efen & Ebs5
                               & Eb & Eo & Ea & Ets5 & Eout5 & Eavo5
                               & Efes2 & Etokse & Etoks0)]; subst evs.
           ++ split; [|apply Forall_nil].
              refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
              ** unfold s5. rewrite E1. cbv iota. dsimp. exact HT3.
              ** unfold s5. rewrite E1. cbv iota. dsimp.
                 exact (proj1 Hstat3).
              ** unfold s5. rewrite E1. cbv iota. dsimp.
                 exact (proj2 Hstat3).
              ** rewrite Etoks5. exact Htokfar.
              ** unfold FarPend. unfold s5. rewrite E1. cbv iota. dsimp.
                 intros H3. pose proof (Hfar2 H3) as Hd2. lia.
              ** unfold SldInv. unfold s5. rewrite E1. cbv iota. dsimp.
                 rewrite Ess, Ebs.
                 intros Hb. specialize (Hsldf Hb). lia.
           ++ split.
              { refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
                - unfold s5. rewrite E1. cbv iota. dsimp.
                  apply treeinv_flush;
                    [ dsimp; rewrite Ecfg1, (di_cfg _ _ _ _ _ _ HI);
                      exact Hlv
                    | dsimp; exact HT3 ].
                - unfold s5. rewrite E1. cbv iota. dsimp.
                  exact (proj1 (statzero_flush _ _)).
                - unfold s5. rewrite E1. cbv iota. dsimp.
                  exact (proj2 (statzero_flush _ _)).
                - rewrite Etoks0. apply Forall_nil.
                - unfold FarPend. unfold s5. rewrite E1. cbv iota.
                  rewrite flush_block_only_ls. dsimp.
                  intros H3. pose proof (Hfar2 H3) as Hd2. lia.
                - unfold SldInv. unfold s5. rewrite E1. cbv iota.
                  rewrite flush_block_only_ls. dsimp.
                  rewrite Ess.
                  intros Habs. exfalso. lia. }
              constructor; [|apply Forall_nil].
              refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
              ** rewrite Efes2. dsimp. exact HT3.
              ** rewrite Efes2. dsimp. exact (proj1 Hstat3).
              ** rewrite Efes2. dsimp. exact (proj2 Hstat3).
              ** intros _. rewrite Efes2. dsimp.
                 apply tally_lit_full. exact E1.
              ** rewrite Etokse. exact Htokfar.
              ** rewrite Efes2, Efst, Efen. dsimp. rewrite Ebs.
                 intros Hb. specialize (Hsldf Hb). lia.
        -- (* DsCont s5 *)
           cbv iota in Estep.
           right. left.
           exists s5, evs, slid1, Ins2, toks'.
           split; [exact Estep|].
           split; [exact HInv|].
           split; [exact HFor|].
           split.
           { destruct Hdisj as [(E1 & E2 & _)|(ev & E1 & E2 & E3 & _)];
               subst evs; [apply Forall_nil|].
             constructor; [exact E3 | apply Forall_nil]. }
           split.
           { destruct Hdisj as [(E1 & E2 & Ebs5 & Eb & Eo & Ea & _)
                               |(ev & E1 & E2 & E3 & Efst & Efen & Ebs5
                                 & Eb & Eo & Ea & Ets5 & Eout5 & Eavo5
                                 & Efes2 & _)];
               subst evs; cbn [EvChain]; repeat split; congruence. }
           split; [exists nd1; rewrite Edn; exact Ednx1|].
           split; [rewrite Edn, Ein; exact Econs1|].
           split.
           { destruct Hdisj as [(E1 & E2 & Ebs5 & Eb & Eo & Ea & _)
                               |(ev & E1 & E2 & E3 & Efst & Efen & Ebs5
                                 & Eb & Eo & Ea & Ets5 & Eout5 & Eavo5
                                 & Efes2 & _)];
               subst evs; cbn [EvTile];
               [ rewrite Ebs5; lia
               | rewrite Efst, Efen, Ebs5; split; lia ]. }
           split.
           { destruct Hdisj as [(E1 & E2 & Ebs5 & Eb & Eo & Ea & _)
                               |(ev & E1 & E2 & E3 & Efst & Efen & Ebs5
                                 & Eb & Eo & Ea & Ets5 & Eout5 & Eavo5
                                 & Efes2 & _)].
             - lia.
             - rewrite Eavo5, E3.
               apply flush_block_only_avo_nonneg. lia. }
           split; [rewrite Ein, Ela5; lia|].
           split; [| sw_sites_close l2 Ecfg1 HI Hma1 Eg2 Hdisj].
           intros Hlv HS.
           pose proof (Hside1 _ HS) as HSf.
           destruct HSf as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
           unfold FarPend in Hpendf. unfold SldInv in Hsldf.
           assert (HT3 : ZRTreeInv (snd (tr_tally_lit
                     (ls_window l2 (ls_strstart l2 - 1)) (dg_sym_end g)
                     (d_ts sf))))
             by (apply treeinv_tally_lit; exact HTIf).
           assert (Hstat3 : ts_optlen (snd (tr_tally_lit
                       (ls_window l2 (ls_strstart l2 - 1)) (dg_sym_end g)
                       (d_ts sf))) = 0
                   /\ ts_statlen (snd (tr_tally_lit
                       (ls_window l2 (ls_strstart l2 - 1)) (dg_sym_end g)
                       (d_ts sf))) = 0)
             by (exact (statzero_tally_lit _ _ _ (conj Holf Hslf))).
           assert (Htokfar : Forall FarOkTok
                     (toks ++ [TLit (ls_window l2 (ls_strstart l2 - 1))])).
           { apply Forall_app. split; [exact Hfarf|].
             constructor; [exact I | apply Forall_nil]. }
           destruct Hdisj as [(E1 & E2 & Ebs5 & Eb & Eo & Ea & Etoks5)
                             |(ev & E1 & E2 & E3 & Efst & Efen & Ebs5
                               & Eb & Eo & Ea & Ets5 & Eout5 & Eavo5
                               & Efes2 & Etokse & Etoks0)]; subst evs.
           ++ split; [|apply Forall_nil].
              refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
              ** unfold s5. rewrite E1. cbv iota. dsimp. exact HT3.
              ** unfold s5. rewrite E1. cbv iota. dsimp.
                 exact (proj1 Hstat3).
              ** unfold s5. rewrite E1. cbv iota. dsimp.
                 exact (proj2 Hstat3).
              ** rewrite Etoks5. exact Htokfar.
              ** unfold FarPend. unfold s5. rewrite E1. cbv iota. dsimp.
                 intros H3. pose proof (Hfar2 H3) as Hd2. lia.
              ** unfold SldInv. unfold s5. rewrite E1. cbv iota. dsimp.
                 rewrite Ess, Ebs.
                 intros Hb. specialize (Hsldf Hb). lia.
           ++ split.
              { refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
                - unfold s5. rewrite E1. cbv iota. dsimp.
                  apply treeinv_flush;
                    [ dsimp; rewrite Ecfg1, (di_cfg _ _ _ _ _ _ HI);
                      exact Hlv
                    | dsimp; exact HT3 ].
                - unfold s5. rewrite E1. cbv iota. dsimp.
                  exact (proj1 (statzero_flush _ _)).
                - unfold s5. rewrite E1. cbv iota. dsimp.
                  exact (proj2 (statzero_flush _ _)).
                - rewrite Etoks0. apply Forall_nil.
                - unfold FarPend. unfold s5. rewrite E1. cbv iota.
                  rewrite flush_block_only_ls. dsimp.
                  intros H3. pose proof (Hfar2 H3) as Hd2. lia.
                - unfold SldInv. unfold s5. rewrite E1. cbv iota.
                  rewrite flush_block_only_ls. dsimp.
                  rewrite Ess.
                  intros Habs. exfalso. lia. }
              constructor; [|apply Forall_nil].
              refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
              ** rewrite Efes2. dsimp. exact HT3.
              ** rewrite Efes2. dsimp. exact (proj1 Hstat3).
              ** rewrite Efes2. dsimp. exact (proj2 Hstat3).
              ** intros _. rewrite Efes2. dsimp.
                 apply tally_lit_full. exact E1.
              ** rewrite Etokse. exact Htokfar.
              ** rewrite Efes2, Efst, Efen. dsimp. rewrite Ebs.
                 intros Hb. specialize (Hsldf Hb). lia.
      * (* ---- ARM 3: defer ---- *)
        apply negb_false_iff in Eg2. apply Z.eqb_eq in Eg2.
        pose proof (dsb_arm3_inv g wbits hbits wrap slid1 Ins1 Ins2 toks sf l2
                      Hg HI1 Hla1 Hcinv2 Hhi2 Ew Ess Ela Ebs Ema Ews
                      Eins Einsh Hmlb Epl Hdisp Eg1 Eg2) as HInv.
        match type of HInv with
        | DsInv _ _ _ _ _ ?X => set (s6 := X) in *
        end.
        right. left.
        exists s6, [], slid1, Ins2, toks.
        split; [exact Estep|].
        assert (E6ts : d_ts s6 = d_ts sf) by reflexivity.
        assert (E6strm : d_strm s6 = d_strm sf) by reflexivity.
        assert (E6la : ls_lookahead (d_ls s6) = ls_lookahead l2 - 1)
          by reflexivity.
        assert (E6bs : ls_blockstart (d_ls s6) = ls_blockstart l2)
          by reflexivity.
        split; [exact HInv|].
        split; [apply Forall_nil|].
        split; [apply Forall_nil|].
        split; [cbn [EvChain]; rewrite E6ts, E6strm;
                repeat split; congruence|].
        split; [exists nd1; rewrite E6strm; exact Ednx1|].
        split; [rewrite E6strm; exact Econs1|].
        split; [cbn [EvTile]; rewrite E6bs, Ebs; lia|].
        split; [rewrite E6strm; lia|].
        split; [rewrite E6strm, E6la, Ela; lia|].
        split; [| sw_sites_close l2 Ecfg1 HI Hma1 Eg2 Hdisj].
        intros Hlv HS.
        pose proof (Hside1 _ HS) as HSf.
        destruct HSf as (HTIf & Holf & Hslf & Hfarf & Hpendf & Hsldf).
        unfold FarPend in Hpendf. unfold SldInv in Hsldf.
        split; [|apply Forall_nil].
        assert (E6ml : ls_matchlen (d_ls s6) = ls_matchlen l2)
          by reflexivity.
        assert (E6ms : ls_matchstart (d_ls s6) = ls_matchstart l2)
          by reflexivity.
        assert (E6ss : ls_strstart (d_ls s6) = ls_strstart l2 + 1)
          by reflexivity.
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        -- rewrite E6ts. exact HTIf.
        -- rewrite E6ts. exact Holf.
        -- rewrite E6ts. exact Hslf.
        -- exact Hfarf.
        -- unfold FarPend. rewrite E6ml, E6ms, E6ss.
           intros H3. pose proof (Hfar2 H3) as Hd2. lia.
        -- unfold SldInv. rewrite E6bs, E6ss, Ess, Ebs.
           intros Hb. specialize (Hsldf Hb). lia.
(* fast-shadow (batch JG7): the kernel re-derives the proof's cbn/dsimp
   conversions at Qed, unfolding the [ds_fill] fill tower with no
   sharing; marking the walk functions opaque for the CHECK only (the term
   never needs them unfolded) cuts Qed from the census head to seconds.
   Proof commands above are byte-identical to base; the line below is
   inside the proof, so elaboration state is untouched by construction. *)
Local Strategy opaque [ds_fill flush_block_only ds_insert insert_string].
Qed.
(* fast-shadow restore (importers see default levels; Local + explicit). *)
Local Strategy transparent [ds_fill flush_block_only ds_insert insert_string].

Print Assumptions ds_step_finish.
