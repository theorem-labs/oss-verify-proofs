(** * DfStep — the fast-path walk, part F5: one [df_step] trip.

    OWNER: q5-emitter (GAP7 D1).  TRUST BOUNDARY: pure Gallina.

    Mirror of [SwStep.ds_step_finish] with two body arms instead of
    three; the fill is the SHARED [dsinv_fill], and [DfSide] rides
    through it on [StepPres]'s [sp_ma]/[sp_pl] frames.  The [DfSnap]
    per-event thread comes packaged from the arms. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwDrain SwStep
  ZRTreeState DfArm DfIns DfArm1 DfArm2.
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

Theorem df_step_finish : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  BsFloor g s ->
  DfSide (d_ls s) ->
  0 <= zs_availout (d_strm s) ->
  (* BREAK: input drained *)
  (exists s' slid' Ins',
      df_step Z_FINISH s = DsBreak s'
      /\ DsInv g wrap slid' Ins' toks s'
      /\ DfSide (d_ls s')
      /\ ls_lookahead (d_ls s') = 0
      /\ zs_in (d_strm s') = []
      /\ (exists nd, zs_done (d_strm s') = zs_done (d_strm s) ++ nd)
      /\ zs_done (d_strm s') ++ zs_in (d_strm s')
         = zs_done (d_strm s) ++ zs_in (d_strm s)
      /\ slid' + ls_blockstart (d_ls s') = slid + ls_blockstart (d_ls s)
      /\ d_ts s' = d_ts s
      /\ zs_out (d_strm s') = zs_out (d_strm s)
      /\ zs_availout (d_strm s') = zs_availout (d_strm s)
      /\ BsFloor g s')
  \/ (* CONT *)
  (exists s' evs slid' Ins' toks',
      df_step Z_FINISH s = DsCont s'
      /\ DsInv g wrap slid' Ins' toks' s'
      /\ DfSide (d_ls s')
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
      /\ (0 < dg_level g -> DfSnap (d_ts s) ->
          DfSnap (d_ts s')
          /\ Forall (fun ev => DfSnap (d_ts (fe_s ev))) evs)
      /\ (0 < dg_level g -> Forall (fun ev =>
           (fe_last ev = 0 -> ts_symnext (d_ts (fe_s ev)) = dg_sym_end g)
           /\ (ls_blockstart (d_ls (fe_s ev)) < 0 ->
               dg_max_dist g < fe_end ev - fe_start ev)) evs)
      /\ BsFloor g s')
  \/ (* RET: avail_out exhausted at a flush *)
  (exists s' evs slid' Ins' toks',
      df_step Z_FINISH s = DsRet NeedMore s'
      /\ DsInv g wrap slid' Ins' toks' s'
      /\ DfSide (d_ls s')
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
      /\ (0 < dg_level g -> DfSnap (d_ts s) ->
          DfSnap (d_ts s')
          /\ Forall (fun ev => DfSnap (d_ts (fe_s ev))) evs)
      /\ (0 < dg_level g -> Forall (fun ev =>
           (fe_last ev = 0 -> ts_symnext (d_ts (fe_s ev)) = dg_sym_end g)
           /\ (ls_blockstart (d_ls (fe_s ev)) < 0 ->
               dg_max_dist g < fe_end ev - fe_start ev)) evs)
      /\ BsFloor g s').
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg HI HBsf HSide Havo.
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
  pose proof (sp_ma _ _ _ _ _ _ _ HP1) as Ema1.
  pose proof (sp_pl _ _ _ _ _ _ _ HP1) as Epl1.
  pose proof (sp_ml _ _ _ _ _ _ _ HP1) as Emlf1.
  pose proof (wi_done _ _ _ _ (di_win _ _ _ _ _ _ HI)) as Hd0.
  pose proof (wi_done _ _ _ _ (di_win _ _ _ _ _ _ HI1)) as Hd1.
  pose proof (wi_la _ _ _ _ (di_win _ _ _ _ _ _ HI1)) as Hla1'.
  assert (Ebw1 : ts_bw (d_ts sf) = ts_bw (d_ts s))
    by (rewrite Ets1; reflexivity).
  assert (Havof : 0 <= zs_availout (d_strm sf)) by lia.
  assert (HBsf1 : BsFloor g sf)
    by (exact (bsfloor_steppres _ _ _ _ _ _ _ HP1 HBsf)).
  assert (HSidef : DfSide (d_ls sf)).
  { destruct HSide as (Hma0 & Hpl2 & Hml02).
    refine (conj _ (conj _ _)).
    - congruence.
    - congruence.
    - destruct Hml02 as [E|E]; [left|right]; congruence. }

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
    { unfold df_step.
      replace (Z.eqb Z_FINISH Z_NO_FLUSH) with false by reflexivity.
      rewrite andb_false_r.
      fold sf. rewrite Ebrk. reflexivity. }
    repeat apply conj; try assumption.
    all: first
      [ exact (proj1 HSidef)
      | (destruct HSidef as (_ & Hp); lia)
      | (apply (ds_fill_drain g wbits hbits wrap slid Ins toks s Hg HI);
         fold sf; rewrite Ela0; unfold MIN_LOOKAHEAD; lia)
      | (exists nd1; exact Ednx1) ].
  - (* the body runs *)
    assert (Estep : df_step Z_FINISH s = df_body Z_FINISH sf).
    { unfold df_step.
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
    rewrite df_body_shape, (di_cfg _ _ _ _ _ _ HI1) in Estep.
    cbv zeta in Estep.
    destruct (df_top_facts g wbits hbits wrap slid1 Ins1 toks sf
                Hg HI1 HSidef) as (Ins2 & Htop).
    cbv zeta in Htop.
    set (l1 := if negb (Z.eqb (fst (dsb_ph g (d_ls sf))) NIL)
                  && (Z.leb (ls_strstart (snd (dsb_ph g (d_ls sf)))
                             - fst (dsb_ph g (d_ls sf)))
                            (dg_max_dist g))
               then let r := longest_match g (snd (dsb_ph g (d_ls sf)))
                               (fst (dsb_ph g (d_ls sf))) in
                    setL_matchstart (snd r)
                      (setL_matchlen (fst r) (snd (dsb_ph g (d_ls sf))))
               else snd (dsb_ph g (d_ls sf))) in *.
    destruct Htop as (Hcinv2 & Hhi2 & Ew & Ess & Ela & Ebs & Ema & Ews
                      & Eins & Hpl2 & Hml3c & Einsh & Hmlb & Hqual).
    destruct (Z.leb MIN_MATCH (ls_matchlen l1)) eqn:Eg1.
    + (* ---- MATCH arm ---- *)
      destruct (dfb_arm1_inv g wbits hbits wrap slid1 Ins1 Ins2 toks sf l1
                  Hg HI1 HBsf1 HSidef Havof Hcinv2 Hhi2 Ew Ess Ela Ebs Ema
                  Ews Eins Hpl2 Hml3c Einsh Hmlb Hqual Eg1)
        as (Ins' & toks' & evs & HFor & Hdisj & HSnap & HBsF).
      cbv zeta in HFor, Hdisj, HSnap, HBsF.
      destruct Hdisj as [HNo|HYes].
      * (* no flush: DsCont s3 *)
        destruct HNo as (Eflag & Eevs & HInv & Edn & Ein & Ela5 & Ess5
                         & Ebs5 & Ebw5 & Eout5 & Eavo5 & HSide5 & Etoks5).
        rewrite Eflag in Estep.
        match type of Estep with
        | _ = DsCont ?X => set (s3 := X) in *
        end.
        subst evs.
        right. left.
        exists s3, [], slid1, Ins', toks'.
        split; [exact Estep|].
        split; [exact HInv|].
        split; [exact HSide5|].
        split; [apply Forall_nil|].
        split; [apply Forall_nil|].
        split; [cbn [EvChain]; repeat split; congruence|].
        split; [exists nd1; rewrite Edn; exact Ednx1|].
        split; [rewrite Edn, Ein; exact Econs1|].
        split; [cbn [EvTile]; rewrite Ebs5; lia|].
        split; [rewrite Eavo5; lia|].
        split; [rewrite Ein, Ela5;
                assert (Hml1c := Eg1); apply Z.leb_le in Hml1c;
                unfold MIN_MATCH in Hml1c; lia|].
        split.
        { intros Hlv HSn.
          destruct (HSnap Hlv ltac:(rewrite <- Ets1 in HSn; exact HSn))
            as (HS' & _).
          rewrite Eflag in HS'.
          split; [exact HS' | apply Forall_nil]. }
        split; [intros _; apply Forall_nil|].
        rewrite Eflag in HBsF. exact HBsF.
      * (* flush *)
        destruct HYes as (ev & Eflag & Eevs & Elast & Efes & Efst & Efen
                          & Ebs5 & Ebwe & Eoute & Eavoe & HInv & Edn & Ein
                          & Ela5 & Ess5 & HSide5 & Etokse & Etoks0
                          & Htally & Hfloor).
        rewrite Eflag in Estep.
        unfold flush_block in Estep. cbv zeta in Estep.
        match type of HInv with
        | DsInv _ _ _ _ _ (flush_block_only 0 ?X) => set (s3 := X) in *
        end.
        subst evs.
        destruct (Z.eqb (zs_availout (d_strm (flush_block_only 0 s3))) 0)
          eqn:Eavo0.
        -- (* DsRet NeedMore *)
           cbn [Z.eqb] in Estep. cbv iota in Estep.
           apply Z.eqb_eq in Eavo0.
           right. right.
           exists (flush_block_only 0 s3), [ev], slid1, Ins', toks'.
           split; [exact Estep|].
           split; [exact HInv|].
           split; [exact HSide5|].
           split; [rewrite Edn; exact HFor|].
           split; [constructor; [exact Elast | apply Forall_nil]|].
           split; [cbn [EvChain]; rewrite Elast, Efes;
                   repeat split; congruence|].
           split; [exists nd1; rewrite Edn; exact Ednx1|].
           split; [rewrite Edn, Ein; exact Econs1|].
           split; [cbn [EvTile]; rewrite Efst, Efen, Ebs5;
                   split; lia|].
           split; [exact Eavo0|].
           split.
           { intros Hlv HSn.
             destruct (HSnap Hlv ltac:(rewrite <- Ets1 in HSn; exact HSn))
               as (HS' & HFe).
             rewrite Eflag in HS'.
             split; [exact HS'|].
             constructor; [|apply Forall_nil].
             apply Forall_inv in HFe. exact HFe. }
           split.
           { intros _.
             constructor; [|apply Forall_nil].
             split; [intros _; exact Htally | exact Hfloor]. }
           rewrite Eflag in HBsF. exact HBsF.
        -- (* DsCont *)
           cbv iota in Estep.
           right. left.
           exists (flush_block_only 0 s3), [ev], slid1, Ins', toks'.
           split; [exact Estep|].
           split; [exact HInv|].
           split; [exact HSide5|].
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
           split; [rewrite Ein, Ela5;
                   assert (Hml1c := Eg1); apply Z.leb_le in Hml1c;
                   unfold MIN_MATCH in Hml1c; lia|].
           split.
           { intros Hlv HSn.
             destruct (HSnap Hlv ltac:(rewrite <- Ets1 in HSn; exact HSn))
               as (HS' & HFe).
             rewrite Eflag in HS'.
             split; [exact HS'|].
             constructor; [|apply Forall_nil].
             apply Forall_inv in HFe. exact HFe. }
           split.
           { intros _.
             constructor; [|apply Forall_nil].
             split; [intros _; exact Htally | exact Hfloor]. }
           rewrite Eflag in HBsF. exact HBsF.
    + (* ---- LITERAL arm ---- *)
      destruct (dfb_arm2_inv g wbits hbits wrap slid1 Ins1 Ins2 toks sf l1
                  Hg HI1 HBsf1 HSidef Hla1 Havof Hcinv2 Hhi2 Ew Ess Ela Ebs
                  Ema Ews Eins Hpl2 Hml3c Einsh Hmlb Eg1)
        as (Ins' & toks' & evs & HFor & Hdisj & HSnap & HBsF).
      cbv zeta in HFor, Hdisj, HSnap, HBsF.
      destruct Hdisj as [HNo|HYes].
      * (* no flush: DsCont s3 *)
        destruct HNo as (Eflag & Eevs & HInv & Edn & Ein & Ela5 & Ess5
                         & Ebs5 & Ebw5 & Eout5 & Eavo5 & HSide5 & Etoks5).
        rewrite Eflag in Estep.
        match type of Estep with
        | _ = DsCont ?X => set (s3 := X) in *
        end.
        subst evs.
        right. left.
        exists s3, [], slid1, Ins', toks'.
        split; [exact Estep|].
        split; [exact HInv|].
        split; [exact HSide5|].
        split; [apply Forall_nil|].
        split; [apply Forall_nil|].
        split; [cbn [EvChain]; repeat split; congruence|].
        split; [exists nd1; rewrite Edn; exact Ednx1|].
        split; [rewrite Edn, Ein; exact Econs1|].
        split; [cbn [EvTile]; rewrite Ebs5; lia|].
        split; [rewrite Eavo5; lia|].
        split; [rewrite Ein, Ela5; lia|].
        split.
        { intros Hlv HSn.
          destruct (HSnap Hlv ltac:(rewrite <- Ets1 in HSn; exact HSn))
            as (HS' & _).
          rewrite Eflag in HS'.
          split; [exact HS' | apply Forall_nil]. }
        split; [intros _; apply Forall_nil|].
        rewrite Eflag in HBsF. exact HBsF.
      * (* flush *)
        destruct HYes as (ev & Eflag & Eevs & Elast & Efes & Efst & Efen
                          & Ebs5 & Ebwe & Eoute & Eavoe & HInv & Edn & Ein
                          & Ela5 & Ess5 & HSide5 & Etokse & Etoks0
                          & Htally & Hfloor).
        rewrite Eflag in Estep.
        unfold flush_block in Estep. cbv zeta in Estep.
        match type of HInv with
        | DsInv _ _ _ _ _ (flush_block_only 0 ?X) => set (s3 := X) in *
        end.
        subst evs.
        destruct (Z.eqb (zs_availout (d_strm (flush_block_only 0 s3))) 0)
          eqn:Eavo0.
        -- (* DsRet NeedMore *)
           cbn [Z.eqb] in Estep. cbv iota in Estep.
           apply Z.eqb_eq in Eavo0.
           right. right.
           exists (flush_block_only 0 s3), [ev], slid1, Ins', toks'.
           split; [exact Estep|].
           split; [exact HInv|].
           split; [exact HSide5|].
           split; [rewrite Edn; exact HFor|].
           split; [constructor; [exact Elast | apply Forall_nil]|].
           split; [cbn [EvChain]; rewrite Elast, Efes;
                   repeat split; congruence|].
           split; [exists nd1; rewrite Edn; exact Ednx1|].
           split; [rewrite Edn, Ein; exact Econs1|].
           split; [cbn [EvTile]; rewrite Efst, Efen, Ebs5;
                   split; lia|].
           split; [exact Eavo0|].
           split.
           { intros Hlv HSn.
             destruct (HSnap Hlv ltac:(rewrite <- Ets1 in HSn; exact HSn))
               as (HS' & HFe).
             rewrite Eflag in HS'.
             split; [exact HS'|].
             constructor; [|apply Forall_nil].
             apply Forall_inv in HFe. exact HFe. }
           split.
           { intros _.
             constructor; [|apply Forall_nil].
             split; [intros _; exact Htally | exact Hfloor]. }
           rewrite Eflag in HBsF. exact HBsF.
        -- (* DsCont *)
           cbv iota in Estep.
           right. left.
           exists (flush_block_only 0 s3), [ev], slid1, Ins', toks'.
           split; [exact Estep|].
           split; [exact HInv|].
           split; [exact HSide5|].
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
           split.
           { intros Hlv HSn.
             destruct (HSnap Hlv ltac:(rewrite <- Ets1 in HSn; exact HSn))
               as (HS' & HFe).
             rewrite Eflag in HS'.
             split; [exact HS'|].
             constructor; [|apply Forall_nil].
             apply Forall_inv in HFe. exact HFe. }
           split.
           { intros _.
             constructor; [|apply Forall_nil].
             split; [intros _; exact Htally | exact Hfloor]. }
           rewrite Eflag in HBsF. exact HBsF.
Qed.

Print Assumptions df_step_finish.
