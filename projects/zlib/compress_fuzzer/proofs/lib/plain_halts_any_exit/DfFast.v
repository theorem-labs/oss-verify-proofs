(** * DfFast — the fast-path walk, part F7: [deflate_fast] at [Z_FINISH],
      whole-call.

    OWNER: q5-emitter (GAP7 D1).  TRUST BOUNDARY: pure Gallina.
    Mirror of [SwSlow.deflate_slow_finish]: [df_loop] under its static
    fuel, then the SHARED [ds_tail].  The [DfSnap] thread rides via
    [SwTail]'s counter-bundle conjunct. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwDrain SwStep
  SwLoop SwTail ZRTreeState DfArm DfIns DfArm1 DfArm2 DfStep DfLoop.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** With no pending literal, the tail's emit flag is irrelevant. *)
Lemma ds_tail_epl_irrelevant : forall flush si s,
  ls_matchavail (d_ls s) = 0 ->
  ds_tail flush false si s = ds_tail flush true si s.
Proof.
  intros flush si s Hma.
  unfold ds_tail. cbv zeta.
  rewrite Hma.
  replace (Z.eqb 0 0) with true by reflexivity.
  cbn [negb andb].
  reflexivity.
Qed.

Theorem deflate_fast_finish : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  BsFloor g s ->
  DfSide (d_ls s) ->
  0 <= zs_availout (d_strm s) ->
  exists bs s' evs,
    deflate_fast Z_FINISH s = (bs, s')
    /\ Forall (EvOk g wrap (zs_done (d_strm s'))) evs
    /\ EvChain evs (ts_bw (d_ts s)) (zs_out (d_strm s))
                   (zs_availout (d_strm s))
                   (ts_bw (d_ts s')) (zs_out (d_strm s'))
                   (zs_availout (d_strm s'))
    /\ zs_done (d_strm s') ++ zs_in (d_strm s')
       = zs_done (d_strm s) ++ zs_in (d_strm s)
    /\ (exists nd, zs_done (d_strm s') = zs_done (d_strm s) ++ nd)
    /\ ( (exists evs0 evf,
            evs = evs0 ++ [evf]
            /\ Forall (fun e => fe_last e = 0) evs0
            /\ fe_last evf = 1
            /\ EvTile evs (slid + ls_blockstart (d_ls s))
                          (zlen (zs_done (d_strm s')))
            /\ zs_in (d_strm s') = []
            /\ zs_done (d_strm s')
               = zs_done (d_strm s) ++ zs_in (d_strm s)
            /\ CkInv wrap (d_strm s')
            /\ zs_totalin (d_strm s') = zlen (zs_done (d_strm s'))
            /\ ( (bs = FinishStarted /\ zs_availout (d_strm s') = 0)
               \/ (bs = FinishDone /\ 1 <= zs_availout (d_strm s')) ))
       \/ (bs = NeedMore /\ zs_availout (d_strm s') = 0
           /\ Forall (fun e => fe_last e = 0) evs) )
    /\ d_wrap s' = d_wrap s
    /\ d_cfg s' = d_cfg s
    /\ (exists te, EvTile evs (slid + ls_blockstart (d_ls s)) te
                   /\ te <= zlen (zs_done (d_strm s')))
    /\ (0 < dg_level g -> DfSnap (d_ts s) ->
        DfSnap (d_ts s')
        /\ Forall (fun ev => DfSnap (d_ts (fe_s ev))) evs)
    /\ (0 < dg_level g -> Forall (fun ev =>
         (fe_last ev = 0 -> ts_symnext (d_ts (fe_s ev)) = dg_sym_end g)
         /\ (ls_blockstart (d_ls (fe_s ev)) < 0 ->
             dg_max_dist g < fe_end ev - fe_start ev)) evs)
    /\ BsFloor g s'.
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg HI HBsf HSide Havo.
  pose proof (wi_la _ _ _ _ (di_win _ _ _ _ _ _ HI)) as Hla0.
  pose proof (zlen_nonneg (zs_in (d_strm s))) as Hin0.
  destruct (df_loop_finish (ds_fuel s) g wbits hbits wrap slid Ins toks s
              Hg HI HBsf HSide Havo
              ltac:(unfold ds_fuel;
                    rewrite Nat2Z.inj_add, Z2Nat.id by lia;
                    cbn [Z.of_nat]; lia))
    as (s1 & evs1 & slid1 & Ins1 & toks1 & ob & Erun & HI1 & HSide1
        & HFor1 & HLast1 & HCh1 & Hdnx1 & Hcons1 & HTl1 & Hout & HSnapl
        & HEvX1 & HBsf1).
  unfold deflate_fast.
  rewrite Erun.
  destruct Hout as [(Eob & Ela0' & Ein0 & Havo1) | (Eob & Eavo0)].
  - (* the loop BROKE: run the tail *)
    subst ob. cbv iota.
    rewrite (ds_tail_epl_irrelevant Z_FINISH true s1 (proj1 HSide1)).
    destruct (ds_tail_finish g wbits hbits wrap slid1 Ins1 toks1 s1
                Hg HI1 Ela0' Havo1)
      as (ev & bs & s' & Etail & Hbs & HEvf & Hlastf & HChf & HTlf
          & Hcompf & Ednf & Einf & Etif & Havof & FKf & FWf & FCf & _
          & HSnapt & HTailF).
    exists bs, s', (evs1 ++ [ev]).
    split; [exact Etail|].
    split.
    { apply Forall_app. split.
      - rewrite Ednf. exact HFor1.
      - constructor; [exact HEvf | apply Forall_nil]. }
    split; [exact (evchain_app _ _ _ _ _ _ _ _ _ _ _ HCh1 HChf)|].
    assert (Hcons : zs_done (d_strm s') ++ zs_in (d_strm s')
                    = zs_done (d_strm s) ++ zs_in (d_strm s))
      by (rewrite Ednf, Einf; exact Hcons1).
    split; [exact Hcons|].
    split.
    { destruct Hdnx1 as (nd1 & E1).
      exists nd1. rewrite Ednf. exact E1. }
    split.
    { left.
      exists evs1, ev.
      split; [reflexivity|].
      split; [exact HLast1|].
      split; [exact Hlastf|].
      assert (Ein' : zs_in (d_strm s') = []) by (rewrite Einf; exact Ein0).
      assert (Edone' : zs_done (d_strm s')
                       = zs_done (d_strm s) ++ zs_in (d_strm s))
        by (rewrite <- Hcons, Ein', app_nil_r; reflexivity).
      split.
      { apply (evtile_app _ _ _ _ _ HTl1).
        rewrite Ednf.
        replace (zlen (zs_done (d_strm s1))) with
          (slid1 + ls_strstart (d_ls s1)) by exact Hcompf.
        exact HTlf. }
      split; [exact Ein'|].
      split; [exact Edone'|].
      split; [exact FKf|].
      split.
      { rewrite Etif, Ednf.
        pose proof (wi_totin _ _ _ _ (di_win _ _ _ _ _ _ HI1)) as Hti1.
        exact Hti1. }
      destruct Hbs as [(Ebs & Eav0)|(Ebs & Hav1)].
      + left. split; [exact Ebs | exact Eav0].
      + right. split; [exact Ebs | exact Hav1]. }
    split.
    { rewrite FWf.
      pose proof (di_wrap _ _ _ _ _ _ HI1).
      pose proof (di_wrap _ _ _ _ _ _ HI).
      congruence. }
    split.
    { rewrite FCf.
      pose proof (di_cfg _ _ _ _ _ _ HI1).
      pose proof (di_cfg _ _ _ _ _ _ HI).
      congruence. }
    split.
    { exists (zlen (zs_done (d_strm s'))).
      split; [|lia].
      apply (evtile_app _ _ _ _ _ HTl1).
      rewrite Ednf.
      replace (zlen (zs_done (d_strm s1))) with
        (slid1 + ls_strstart (d_ls s1)) by exact Hcompf.
      exact HTlf. }
    split.
    { intros Hlv HSn.
      destruct (HSnapl Hlv HSn) as (HS1 & HF1).
      destruct (HSnapt Hlv HS1) as (HS2 & HFe).
      split; [exact HS2|].
      apply Forall_app.
      split; [exact HF1|].
      constructor; [exact HFe | apply Forall_nil]. }
    split.
    { intros Hlv.
      apply Forall_app.
      split; [exact (HEvX1 Hlv)|].
      constructor; [|apply Forall_nil].
      split.
      - intros E. rewrite E in Hlastf. discriminate Hlastf.
      - destruct HTailF as ((Ebsev & _) & _).
        cbn [EvTile] in HTlf.
        destruct HTlf as (Etfs & Etfe).
        intros Hneg.
        rewrite Ebsev in Hneg.
        pose proof (HBsf1 Hneg).
        rewrite Etfs, <- Etfe. lia. }
    { destruct HTailF as ((_ & Hbs') & _).
      intros Hneg. lia. }
  - (* avail_out exhausted mid-loop *)
    subst ob. cbv iota.
    exists NeedMore, s1, evs1.
    split; [reflexivity|].
    split; [exact HFor1|].
    split; [exact HCh1|].
    split; [exact Hcons1|].
    split; [exact Hdnx1|].
    split.
    { right.
      split; [reflexivity|].
      split; [exact Eavo0 | exact HLast1]. }
    split.
    { pose proof (di_wrap _ _ _ _ _ _ HI1).
      pose proof (di_wrap _ _ _ _ _ _ HI).
      congruence. }
    split.
    { pose proof (di_cfg _ _ _ _ _ _ HI1).
      pose proof (di_cfg _ _ _ _ _ _ HI).
      congruence. }
    split.
    { exists (slid1 + ls_blockstart (d_ls s1)).
      split; [exact HTl1|].
      pose proof (wi_done _ _ _ _ (di_win _ _ _ _ _ _ HI1)).
      pose proof (wi_la _ _ _ _ (di_win _ _ _ _ _ _ HI1)).
      pose proof (di_bble _ _ _ _ _ _ HI1).
      destruct (di_ma _ _ _ _ _ _ HI1) as [E|E]; lia. }
    split.
    { intros Hlv HSn.
      exact (HSnapl Hlv HSn). }
    split; [exact HEvX1 | exact HBsf1].
Qed.

Print Assumptions deflate_fast_finish.
