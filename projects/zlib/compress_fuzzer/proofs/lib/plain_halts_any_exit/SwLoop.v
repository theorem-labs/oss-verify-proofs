(** * SwLoop — the slow-path walk, part W4c: the whole [ds_loop] at
      [Z_FINISH].

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W4.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    Fuel induction over SwStep's trichotomy.  The measure
    [|zs_in| + lookahead] strictly drops on every [DsCont], so any fuel
    strictly above the initial measure outlasts the loop ([ds_fuel] is
    measure + 2).  The outcome is binary: [None] — the input is drained
    (the [ds_tail] path), or [Some NeedMore] — [avail_out] hit zero at a
    mid-loop flush.  Both come with [DsInv], the accumulated event list
    (all [fe_last = 0]) and the output ledger chained end to end. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwArm2 SwArm3
  SwArm1a SwArm1b SwDrain SwStep ZRTreeState ZREvSnap.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Theorem ds_loop_finish : forall fuel g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  dg_strategy g = 0 ->
  DsInv g wrap slid Ins toks s ->
  0 <= zs_availout (d_strm s) ->
  zlen (zs_in (d_strm s)) + ls_lookahead (d_ls s) < Z.of_nat fuel ->
  exists s' evs slid' Ins' toks' ob,
    ds_loop fuel Z_FINISH s = (ob, s')
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
    /\ ( (ob = None
          /\ ls_lookahead (d_ls s') = 0
          /\ zs_in (d_strm s') = []
          /\ 0 <= zs_availout (d_strm s'))
       \/ (ob = Some NeedMore /\ zs_availout (d_strm s') = 0) )
    /\ (0 < dg_level g -> ZRSideInv g toks s ->
        ZRSideInv g toks' s'
        /\ Forall (EvSnapOk g) evs).
Proof.
  induction fuel as [|f IH];
    intros g wbits hbits wrap slid Ins toks s Hg Hstrat HI Havo Hfuel.
  - pose proof (zlen_nonneg (zs_in (d_strm s))).
    pose proof (wi_la _ _ _ _ (di_win _ _ _ _ _ _ HI)).
    cbn [Z.of_nat] in Hfuel. lia.
  - cbn [ds_loop].
    destruct (ds_step_finish g wbits hbits wrap slid Ins toks s
                Hg Hstrat HI Havo)
      as [HB | [HC | HR]].
    + (* BREAK *)
      destruct HB as (s' & slid' & Ins' & Estep & HI' & Ela0 & Ein0
                      & Hdnx & Hcons & Ebs & Ets & Eout & Eavo & HTIb).
      rewrite Estep.
      exists s', [], slid', Ins', toks, None.
      split; [reflexivity|].
      split; [exact HI'|].
      split; [apply Forall_nil|].
      split; [apply Forall_nil|].
      split; [cbn [EvChain]; rewrite Ets, Eout, Eavo;
              repeat split; reflexivity|].
      split; [exact Hdnx|].
      split; [exact Hcons|].
      split; [cbn [EvTile]; exact Ebs|].
      split.
      { left. repeat split; try assumption. lia. }
      intros _ HTI.
      split; [apply HTIb; exact HTI | apply Forall_nil].
    + (* CONT: recurse *)
      destruct HC as (s1 & evs1 & slid1 & Ins1 & toks1 & Estep & HI1
                      & HFor1 & HLast1 & HCh1 & Hdnx1 & Hcons1 & HTl1
                      & Havo1 & Hmeas & HTI1 & _).
      rewrite Estep.
      destruct (IH g wbits hbits wrap slid1 Ins1 toks1 s1
                  Hg Hstrat HI1 Havo1 ltac:(lia))
        as (s' & evs2 & slid' & Ins' & toks' & ob & Erun & HI' & HFor2
            & HLast2 & HCh2 & Hdnx2 & Hcons2 & HTl2 & Hout & HTI2).
      exists s', (evs1 ++ evs2), slid', Ins', toks', ob.
      split; [exact Erun|].
      split; [exact HI'|].
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
      intros Hlv HTI.
      destruct (HTI1 Hlv HTI) as (HT1 & HF1).
      destruct (HTI2 Hlv HT1) as (HT2 & HF2).
      split; [exact HT2|].
      apply Forall_app. split; [exact HF1 | exact HF2].
    + (* RET *)
      destruct HR as (s' & evs & slid' & Ins' & toks' & Estep & HI'
                      & HFor & HLast & HCh & Hdnx & Hcons & HTl & Eavo0
                      & HTIr & _).
      rewrite Estep.
      exists s', evs, slid', Ins', toks', (Some NeedMore).
      split; [reflexivity|].
      split; [exact HI'|].
      split; [exact HFor|].
      split; [exact HLast|].
      split; [exact HCh|].
      split; [exact Hdnx|].
      split; [exact Hcons|].
      split; [exact HTl|].
      split.
      { right. split; [reflexivity | exact Eavo0]. }
      exact HTIr.
Qed.

Print Assumptions ds_loop_finish.
