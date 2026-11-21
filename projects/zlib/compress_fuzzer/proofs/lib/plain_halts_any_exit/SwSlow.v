(** * SwSlow — the slow-path walk, part W4e: [deflate_slow] at [Z_FINISH],
      whole-call.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4 capstone.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    [ds_loop] (with its static fuel [ds_fuel], which strictly dominates
    the measure) followed by [ds_tail].  The success outcome hands G3/G5
    everything the stream assembly needs:

      * the event list splits as [evs0 ++ [evf]] — stored/normal blocks
        with [fe_last = 0], then the final block with [fe_last = 1];
      * the output ledger [EvChain] runs from the caller's accumulators
        to the returned state's;
      * the input ledger [EvTile] runs from the caller's block base to
        [zlen zs_done] — and the final [zs_done] is exactly the initial
        [zs_done ++ zs_in]: the whole input, consumed and covered;
      * the checksum invariant [CkInv] holds at the final stream (the
        adler/crc of everything consumed — the trailer's value).

    The alternative outcome is [NeedMore] with [avail_out = 0], which the
    one-call assembly refutes against the [deflateBound]-sized buffer. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwArm2 SwArm3
  SwArm1a SwArm1b SwDrain SwStep SwLoop SwTail ZRTreeState ZREvSnap.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Theorem deflate_slow_finish : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  dg_strategy g = 0 ->
  DsInv g wrap slid Ins toks s ->
  0 <= zs_availout (d_strm s) ->
  exists bs s' evs,
    deflate_slow Z_FINISH s = (bs, s')
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
               \/ (bs = FinishDone /\ 0 <= zs_availout (d_strm s')) ))
       \/ (bs = NeedMore /\ zs_availout (d_strm s') = 0
           /\ Forall (fun e => fe_last e = 0) evs) )
    /\ d_wrap s' = d_wrap s
    /\ d_cfg s' = d_cfg s
    /\ (exists te, EvTile evs (slid + ls_blockstart (d_ls s)) te
                   /\ te <= zlen (zs_done (d_strm s')))
    /\ (0 < dg_level g -> ZRSideInv g toks s ->
        ZRTreeInv (d_ts s')
        /\ Forall (EvSnapOk g) evs).
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg Hstrat HI Havo.
  pose proof (wi_la _ _ _ _ (di_win _ _ _ _ _ _ HI)) as Hla0.
  pose proof (zlen_nonneg (zs_in (d_strm s))) as Hin0.
  destruct (ds_loop_finish (ds_fuel s) g wbits hbits wrap slid Ins toks s
              Hg Hstrat HI Havo
              ltac:(unfold ds_fuel;
                    rewrite Nat2Z.inj_add, Z2Nat.id by lia;
                    cbn [Z.of_nat]; lia))
    as (s1 & evs1 & slid1 & Ins1 & toks1 & ob & Erun & HI1 & HFor1
        & HLast1 & HCh1 & Hdnx1 & Hcons1 & HTl1 & Hout & HTIl).
  unfold deflate_slow.
  rewrite Erun.
  destruct Hout as [(Eob & Ela0 & Ein0 & Havo1) | (Eob & Eavo0)].
  - (* the loop BROKE: run the tail *)
    subst ob. cbv iota.
    destruct (ds_tail_finish g wbits hbits wrap slid1 Ins1 toks1 s1
                Hg HI1 Ela0 Havo1)
      as (ev & bs & s' & Etail & Hbs & HEvf & Hlastf & HChf & HTlf
          & Hcompf & Ednf & Einf & Etif & Havof & FKf & FWf & FCf & HTIt
          & _ & _).
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
      destruct Hbs as [(Ebs & Eav0)|(Ebs & _)].
      + left. split; [exact Ebs | exact Eav0].
      + right. split; [exact Ebs | exact Havof]. }
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
    intros Hlv HTI.
    destruct (HTIl Hlv HTI) as (HT1 & HF1).
    destruct (HTIt Hlv HT1) as (HT2 & HFe).
    split; [exact HT2|].
    apply Forall_app.
    split; [exact HF1|].
    constructor; [exact HFe | apply Forall_nil].
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
    intros Hlv HTI.
    destruct (HTIl Hlv HTI) as (HS1 & HF1).
    destruct HS1 as (HT1 & _).
    split; [exact HT1 | exact HF1].
Qed.

Print Assumptions deflate_slow_finish.
