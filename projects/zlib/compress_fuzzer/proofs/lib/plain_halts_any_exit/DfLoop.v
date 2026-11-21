(** * DfLoop — the fast-path walk, part F6: the [df_loop] fuel induction.

    OWNER: q5-emitter (GAP7 D1).  TRUST BOUNDARY: pure Gallina.
    Near-verbatim mirror of [SwLoop.ds_loop_finish] over
    [DfStep.df_step_finish], with the [DfSide]/[DfSnap] threads. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwDrain SwStep SwLoop
  ZRTreeState DfArm DfIns DfArm1 DfArm2 DfStep.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Theorem df_loop_finish : forall fuel g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  BsFloor g s ->
  DfSide (d_ls s) ->
  0 <= zs_availout (d_strm s) ->
  zlen (zs_in (d_strm s)) + ls_lookahead (d_ls s) < Z.of_nat fuel ->
  exists s' evs slid' Ins' toks' ob,
    df_loop fuel Z_FINISH s = (ob, s')
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
    /\ ( (ob = None
          /\ ls_lookahead (d_ls s') = 0
          /\ zs_in (d_strm s') = []
          /\ 0 <= zs_availout (d_strm s'))
       \/ (ob = Some NeedMore /\ zs_availout (d_strm s') = 0) )
    /\ (0 < dg_level g -> DfSnap (d_ts s) ->
        DfSnap (d_ts s')
        /\ Forall (fun ev => DfSnap (d_ts (fe_s ev))) evs)
    /\ (0 < dg_level g -> Forall (fun ev =>
         (fe_last ev = 0 -> ts_symnext (d_ts (fe_s ev)) = dg_sym_end g)
         /\ (ls_blockstart (d_ls (fe_s ev)) < 0 ->
             dg_max_dist g < fe_end ev - fe_start ev)) evs)
    /\ BsFloor g s'.
Proof.
  induction fuel as [|f IH];
    intros g wbits hbits wrap slid Ins toks s Hg HI HBsf HSide Havo Hfuel.
  - pose proof (zlen_nonneg (zs_in (d_strm s))).
    pose proof (wi_la _ _ _ _ (di_win _ _ _ _ _ _ HI)).
    cbn [Z.of_nat] in Hfuel. lia.
  - cbn [df_loop].
    destruct (df_step_finish g wbits hbits wrap slid Ins toks s
                Hg HI HBsf HSide Havo)
      as [HB | [HC | HR]].
    + (* BREAK *)
      destruct HB as (s' & slid' & Ins' & Estep & HI' & HSide' & Ela0
                      & Ein0 & Hdnx & Hcons & Ebs & Ets & Eout & Eavo
                      & HBsfB).
      rewrite Estep.
      exists s', [], slid', Ins', toks, None.
      split; [reflexivity|].
      split; [exact HI'|].
      split; [exact HSide'|].
      split; [apply Forall_nil|].
      split; [apply Forall_nil|].
      split; [cbn [EvChain]; rewrite Ets, Eout, Eavo;
              repeat split; reflexivity|].
      split; [exact Hdnx|].
      split; [exact Hcons|].
      split; [cbn [EvTile]; exact Ebs|].
      split.
      { left. repeat split; try assumption. lia. }
      split.
      { intros _ HSn.
        split; [rewrite Ets; exact HSn | apply Forall_nil]. }
      split; [intros _; apply Forall_nil | exact HBsfB].
    + (* CONT: recurse *)
      destruct HC as (s1 & evs1 & slid1 & Ins1 & toks1 & Estep & HI1
                      & HSide1 & HFor1 & HLast1 & HCh1 & Hdnx1 & Hcons1
                      & HTl1 & Havo1 & Hmeas & HSnap1 & HEvX1 & HBsf1).
      rewrite Estep.
      destruct (IH g wbits hbits wrap slid1 Ins1 toks1 s1
                  Hg HI1 HBsf1 HSide1 Havo1 ltac:(lia))
        as (s' & evs2 & slid' & Ins' & toks' & ob & Erun & HI' & HSide'
            & HFor2 & HLast2 & HCh2 & Hdnx2 & Hcons2 & HTl2 & Hout
            & HSnap2 & HEvX2 & HBsf2).
      exists s', (evs1 ++ evs2), slid', Ins', toks', ob.
      split; [exact Erun|].
      split; [exact HI'|].
      split; [exact HSide'|].
      split.
      { apply Forall_app. split; [|exact HFor2].
        destruct Hdnx2 as (nd2 & Ednx2).
        rewrite Ednx2.
        eapply Forall_impl; [|exact HFor1].
        intros ev HE. apply evok_append. exact HE. }
      split; [apply Forall_app; split; assumption|].
      split; [exact (evchain_app _ _ _ _ _ _ _ _ _ _ _ HCh1 HCh2)|].
      split.
      { destruct Hdnx1 as (nd1 & E1). destruct Hdnx2 as (nd2 & E2).
        exists (nd1 ++ nd2). rewrite E2, E1, app_assoc. reflexivity. }
      split; [rewrite Hcons2; exact Hcons1|].
      split; [exact (evtile_app _ _ _ _ _ HTl1 HTl2)|].
      split; [exact Hout|].
      split.
      { intros Hlv HSn.
        destruct (HSnap1 Hlv HSn) as (HS1 & HF1).
        destruct (HSnap2 Hlv HS1) as (HS2 & HF2).
        split; [exact HS2|].
        apply Forall_app. split; [exact HF1 | exact HF2]. }
      split.
      { intros Hlv.
        apply Forall_app.
        split; [exact (HEvX1 Hlv) | exact (HEvX2 Hlv)]. }
      exact HBsf2.
    + (* RET *)
      destruct HR as (s' & evs & slid' & Ins' & toks' & Estep & HI'
                      & HSide' & HFor & HLast & HCh & Hdnx & Hcons & HTl
                      & Eavo0 & HSnap & HEvX & HBsfR).
      rewrite Estep.
      exists s', evs, slid', Ins', toks', (Some NeedMore).
      split; [reflexivity|].
      split; [exact HI'|].
      split; [exact HSide'|].
      split; [exact HFor|].
      split; [exact HLast|].
      split; [exact HCh|].
      split; [exact Hdnx|].
      split; [exact Hcons|].
      split; [exact HTl|].
      split.
      { right. split; [reflexivity | exact Eavo0]. }
      split; [exact HSnap|].
      split; [exact HEvX | exact HBsfR].
Qed.

Print Assumptions df_loop_finish.
