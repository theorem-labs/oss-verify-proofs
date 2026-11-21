(** * G5Body — the emitted blocks decode as ONE deflate body.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G5, part 1.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The fold over the walk's event list: each event's per-block delta
    (G3Event) is one [dec_blk] step, the tiling ([EvTile]) hands each
    block the accumulator the previous block produced, and STORED
    blocks' byte-parity obligations discharge against ONE global fact —
    the whole body is whole bytes (the final windup) — by subtracting
    the block's own "aligned after me" export.  The final event's BFINAL
    stops [dec_stream_fuel] with the tiled range fully decoded. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees StreamPos.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwEv SwStep Gap7Strict.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** One 0-final block's wire facts, as the fold consumes them —
    G3Event's conclusion shape at [fe_last = 0]. *)
Definition EvBits (done : list Z) (ev : FlushEv) (delta : list bool)
  : Prop :=
  dst_stream (flush_block_only (fe_last ev) (fe_s ev))
    = dst_stream (fe_s ev) ++ delta
  /\ ( (fe_last ev = 0
        /\ (forall suffix,
             dec_blk (delta ++ suffix)
               (firstn (Z.to_nat (fe_start ev)) done)
             = Some (false, firstn (Z.to_nat (fe_end ev)) done, suffix))
        /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
            forall suffix,
             dec_blk_strict (delta ++ suffix)
               (firstn (Z.to_nat (fe_start ev)) done)
             = Some (false, firstn (Z.to_nat (fe_end ev)) done, suffix)))
     \/ (fe_last ev = 0
        /\ (length (dst_stream (flush_block_only (fe_last ev) (fe_s ev)))
            mod 8 = 0)%nat
        /\ (forall suffix, (length suffix mod 8 = 0)%nat ->
             dec_blk (delta ++ suffix)
               (firstn (Z.to_nat (fe_start ev)) done)
             = Some (false, firstn (Z.to_nat (fe_end ev)) done, suffix))
        /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
            forall suffix, (length suffix mod 8 = 0)%nat ->
             dec_blk_strict (delta ++ suffix)
               (firstn (Z.to_nat (fe_start ev)) done)
             = Some (false, firstn (Z.to_nat (fe_end ev)) done, suffix))) ).

(** The final block's, BFINAL set. *)
Definition EvBitsFin (done : list Z) (ev : FlushEv) (delta : list bool)
  : Prop :=
  dst_stream (flush_block_only (fe_last ev) (fe_s ev))
    = dst_stream (fe_s ev) ++ delta
  /\ fe_last ev = 1
  /\ exists pad, (length pad < 8)%nat
     /\ (forall suffix, (length suffix mod 8 = 0)%nat ->
          dec_blk (delta ++ suffix)
            (firstn (Z.to_nat (fe_start ev)) done)
          = Some (true, firstn (Z.to_nat (fe_end ev)) done, pad ++ suffix))
     /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
         forall suffix, (length suffix mod 8 = 0)%nat ->
          dec_blk_strict (delta ++ suffix)
            (firstn (Z.to_nat (fe_start ev)) done)
          = Some (true, firstn (Z.to_nat (fe_end ev)) done, pad ++ suffix)).

(** dst-continuity between consecutive events. *)
Fixpoint DstChain (evs : list FlushEv) (d0 d1 : list bool) : Prop :=
  match evs with
  | [] => d1 = d0
  | ev :: r =>
      dst_stream (fe_s ev) = d0
      /\ DstChain r
           (dst_stream (flush_block_only (fe_last ev) (fe_s ev))) d1
  end.

Lemma evchain_dst : forall evs bw out avo bw' out' avo',
  EvChain evs bw out avo bw' out' avo' ->
  DstChain evs (bytes_bits out ++ bw_stream bw)
               (bytes_bits out' ++ bw_stream bw').
Proof.
  induction evs as [|ev r IH];
    intros bw out avo bw' out' avo' H; cbn [EvChain DstChain] in *.
  - destruct H as (->&->&_). reflexivity.
  - destruct H as (Hb & Ho & Ha & Hr).
    split.
    + unfold dst_stream. rewrite Hb, Ho. reflexivity.
    + pose proof (IH _ _ _ _ _ _ Hr) as H.
      unfold dst_stream. exact H.
Qed.

Lemma mod8_split : forall a b,
  ((a + b) mod 8 = 0)%nat -> (a mod 8 = 0)%nat -> (b mod 8 = 0)%nat.
Proof.
  intros a b Hab Ha.
  rewrite Nat.Div0.add_mod, Ha in Hab.
  cbn [Nat.add] in Hab.
  now rewrite Nat.Div0.mod_mod in Hab.
Qed.

(** Every block occupies at least one bit on the wire (its own header),
    so the event count bounds no more fuel than the bit count. *)
Lemma evbits_delta_pos : forall done ev delta,
  EvBits done ev delta -> (1 <= length delta)%nat.
Proof.
  intros done ev delta (Hdst & Harm).
  destruct Harm as [(E0 & Hdec & _)|(E0 & Hmod & Hdec & _)].
  - pose proof (Hdec []) as H.
    pose proof (dec_blk_shorter _ _ _ _ _ H) as Hs.
    rewrite length_app in Hs. cbn [length] in Hs. lia.
  - pose proof (Hdec [] ltac:(reflexivity)) as H.
    pose proof (dec_blk_shorter _ _ _ _ _ H) as Hs.
    rewrite length_app in Hs. cbn [length] in Hs. lia.
Qed.

(** ** The prefix fold *)

Lemma dec_blocks_prefix :
  forall evs0 deltas0 done p0 p1 sufT d0,
  Forall2 (EvBits done) evs0 deltas0 ->
  DstChain evs0 d0 (d0 ++ concat deltas0) ->
  EvTile evs0 p0 p1 ->
  ((length d0 + (length (concat deltas0) + length sufT)) mod 8 = 0)%nat ->
  forall fuel,
    (length (concat deltas0 ++ sufT) + length evs0 < fuel)%nat ->
    dec_stream_fuel fuel (concat deltas0 ++ sufT)
      (firstn (Z.to_nat p0) done)
    = dec_stream_fuel (fuel - length evs0) sufT
        (firstn (Z.to_nat p1) done).
Proof.
  induction evs0 as [|ev r IH];
    intros deltas0 done p0 p1 sufT d0 HF HD HT Hpar fuel Hfuel.
  - inversion HF; subst deltas0.
    cbn [EvTile] in HT. subst p1.
    cbn [concat app length].
    rewrite Nat.sub_0_r. reflexivity.
  - inversion HF as [|ev' delta r' deltas' HB HF' Ee Ed]; subst.
    cbn [DstChain] in HD. destruct HD as (Hd0 & HD').
    cbn [EvTile] in HT. destruct HT as (Hstart & HT').
    pose proof HB as (Hdst & Harm).
    cbn [concat]. rewrite <- app_assoc.
    destruct fuel as [|fuel']; [cbn [length] in Hfuel; lia|].
    cbn [dec_stream_fuel].
    assert (Hstep : dec_blk (delta ++ concat deltas' ++ sufT)
                      (firstn (Z.to_nat p0) done)
                    = Some (false, firstn (Z.to_nat (fe_end ev)) done,
                            concat deltas' ++ sufT)).
    { destruct Harm as [(E0 & Hdec & _)|(E0 & Hmod & Hdec & _)].
      - rewrite <- Hstart. apply Hdec.
      - rewrite <- Hstart. apply Hdec.
        (* the whole remainder is whole bytes: total minus the aligned
           consumed prefix *)
        rewrite Hdst, Hd0, length_app in Hmod.
        cbn [concat] in Hpar. rewrite length_app in Hpar.
        apply (mod8_split (length d0 + length delta)).
        + rewrite length_app. lia.
        + exact Hmod. }
    rewrite Hstep.
    cbv beta iota.
    replace (S fuel' - length (ev :: r))%nat
      with (fuel' - length r)%nat by (cbn [length]; lia).
    apply (IH deltas' done (fe_end ev) p1 sufT
             (d0 ++ delta)).
    + exact HF'.
    + rewrite Hdst, Hd0 in HD'.
      rewrite <- app_assoc. exact HD'.
    + exact HT'.
    + cbn [concat] in Hpar. rewrite length_app in Hpar |- *. lia.
    + rewrite length_app in Hfuel |- *.
      cbn [concat length] in Hfuel.
      rewrite length_app in Hfuel. lia.
Qed.

(** ** The strict twins of the fuel-independence and prefix folds
    (GAP7 freeze r3).  [dec_blk_strict_weaken] hands the length
    accounting back to the lax [dec_blk_shorter]. *)

Lemma dec_stream_strict_fuel_indep : forall f1 f2 bits acc,
  (length bits < f1)%nat -> (length bits < f2)%nat ->
  dec_stream_strict_fuel f1 bits acc = dec_stream_strict_fuel f2 bits acc.
Proof.
  induction f1 as [|f1 IH]; intros f2 bits acc H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|].
  cbn [dec_stream_strict_fuel].
  destruct (dec_blk_strict bits acc) as [[[fin acc'] r]|] eqn:E;
    [|reflexivity].
  pose proof (dec_blk_shorter _ _ _ _ _ (dec_blk_strict_weaken _ _ _ _ _ E))
    as Hs.
  destruct fin; [reflexivity|].
  apply IH; lia.
Qed.

Lemma dec_blocks_prefix_strict :
  forall evs0 deltas0 done p0 p1 sufT d0,
  build_accepts_of_kraft_STMT ->
  EnoughFits_STMT ->
  Forall2 (EvBits done) evs0 deltas0 ->
  DstChain evs0 d0 (d0 ++ concat deltas0) ->
  EvTile evs0 p0 p1 ->
  ((length d0 + (length (concat deltas0) + length sufT)) mod 8 = 0)%nat ->
  forall fuel,
    (length (concat deltas0 ++ sufT) + length evs0 < fuel)%nat ->
    dec_stream_strict_fuel fuel (concat deltas0 ++ sufT)
      (firstn (Z.to_nat p0) done)
    = dec_stream_strict_fuel (fuel - length evs0) sufT
        (firstn (Z.to_nat p1) done).
Proof.
  induction evs0 as [|ev r IH];
    intros deltas0 done p0 p1 sufT d0 HBK EFR HF HD HT Hpar fuel Hfuel.
  - inversion HF; subst deltas0.
    cbn [EvTile] in HT. subst p1.
    cbn [concat app length].
    rewrite Nat.sub_0_r. reflexivity.
  - inversion HF as [|ev' delta r' deltas' HB HF' Ee Ed]; subst.
    cbn [DstChain] in HD. destruct HD as (Hd0 & HD').
    cbn [EvTile] in HT. destruct HT as (Hstart & HT').
    pose proof HB as (Hdst & Harm).
    cbn [concat]. rewrite <- app_assoc.
    destruct fuel as [|fuel']; [cbn [length] in Hfuel; lia|].
    cbn [dec_stream_strict_fuel].
    assert (Hstep : dec_blk_strict (delta ++ concat deltas' ++ sufT)
                      (firstn (Z.to_nat p0) done)
                    = Some (false, firstn (Z.to_nat (fe_end ev)) done,
                            concat deltas' ++ sufT)).
    { destruct Harm as [(E0 & _ & Hdecs)|(E0 & Hmod & _ & Hdecs)].
      - rewrite <- Hstart. apply (Hdecs HBK EFR).
      - rewrite <- Hstart. apply (Hdecs HBK EFR).
        rewrite Hdst, Hd0, length_app in Hmod.
        cbn [concat] in Hpar. rewrite length_app in Hpar.
        apply (mod8_split (length d0 + length delta)).
        + rewrite length_app. lia.
        + exact Hmod. }
    rewrite Hstep.
    cbv beta iota.
    replace (S fuel' - length (ev :: r))%nat
      with (fuel' - length r)%nat by (cbn [length]; lia).
    apply (IH deltas' done (fe_end ev) p1 sufT
             (d0 ++ delta) HBK EFR).
    + exact HF'.
    + rewrite Hdst, Hd0 in HD'.
      rewrite <- app_assoc. exact HD'.
    + exact HT'.
    + cbn [concat] in Hpar. rewrite length_app in Hpar |- *. lia.
    + rewrite length_app in Hfuel |- *.
      cbn [concat length] in Hfuel.
      rewrite length_app in Hfuel. lia.
Qed.

(** ** The whole body *)

Theorem dec_blocks :
  forall evs0 evf deltas0 deltaf done p0 pend d0,
  Forall2 (EvBits done) evs0 deltas0 ->
  EvBitsFin done evf deltaf ->
  DstChain (evs0 ++ [evf]) d0 ((d0 ++ concat deltas0) ++ deltaf) ->
  EvTile (evs0 ++ [evf]) p0 pend ->
  ((length d0 + (length (concat deltas0) + length deltaf)) mod 8 = 0)%nat ->
  exists rem,
    dec_stream_from (concat deltas0 ++ deltaf)
      (firstn (Z.to_nat p0) done)
    = Some (firstn (Z.to_nat pend) done, rem)
    /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
        dec_stream_from_strict (concat deltas0 ++ deltaf)
          (firstn (Z.to_nat p0) done)
        = Some (firstn (Z.to_nat pend) done, rem))
    /\ (length rem < 8)%nat.
Proof.
  intros evs0 evf deltas0 deltaf done p0 pend d0 HF HFin HD HT Hpar.
  (* split the chains at the final event *)
  assert (Hsplit : forall (l : list FlushEv) d p dd,
      DstChain (l ++ [evf]) d dd ->
      EvTile (l ++ [evf]) p pend ->
      exists dmid pmid,
        DstChain l d dmid
        /\ dst_stream (fe_s evf) = dmid
        /\ EvTile l p pmid
        /\ fe_start evf = pmid
        /\ fe_end evf = pend).
  { clear HF HFin HD HT Hpar.
    induction l as [|ev r IH]; intros d p dd HD HT.
    - cbn [DstChain app EvTile] in HD, HT.
      destruct HD as (Hfe & Hend).
      destruct HT as (Hst & Hpe).
      exists d, p.
      cbn [DstChain EvTile].
      repeat split; try assumption; try reflexivity.
      symmetry; assumption.
    - cbn [DstChain app EvTile] in HD, HT.
      destruct HD as (Hfe & HD').
      destruct HT as (Hst & HT').
      destruct (IH _ _ _ HD' HT') as (dmid & pmid & H1 & H2 & H3 & H4 & H5).
      exists dmid, pmid.
      cbn [DstChain EvTile].
      repeat split; assumption. }
  destruct (Hsplit evs0 d0 p0 _ HD HT)
    as (dmid & pmid & HD0 & Hdmid & HT0 & Hpmid & Hpendf).

  (* pin dmid: the prefix chain ends where the concatenation says *)
  assert (Edmid : dmid = d0 ++ concat deltas0).
  { clear -HD0 HF.
    revert deltas0 d0 HF HD0.
    induction evs0 as [|ev r IH]; intros deltas0 d0 HF HD0.
    - inversion HF; subst. cbn [DstChain] in HD0. subst dmid.
      cbn [concat]. now rewrite app_nil_r.
    - inversion HF as [|? ? ? ? HB HF']; subst.
      cbn [DstChain] in HD0. destruct HD0 as (Hfe & HD').
      destruct HB as (Hdst & _).
      rewrite Hdst, Hfe in HD'.
      pose proof (IH _ _ HF' HD') as H.
      cbn [concat]. rewrite app_assoc. exact H. }
  destruct HFin as (Hdstf & Elast & pad & Hpadlen & Hdecf & HdecfsG).
  (* the final step's parity: its suffix is empty *)
  pose proof (Hdecf [] ltac:(reflexivity)) as Hf.
  rewrite !app_nil_r in Hf.

  (* fuel bookkeeping *)
  assert (Hdposs : (length evs0 <= length (concat deltas0))%nat).
  { clear -HF.
    induction HF as [|ev delta evs deltas HB HF IH];
      cbn [length concat]; [lia|].
    pose proof (evbits_delta_pos _ _ _ HB).
    rewrite length_app. lia. }
  exists pad.
  split; [|split].
  - unfold dec_stream_from.
    rewrite (dec_stream_fuel_indep
               (S (length (concat deltas0 ++ deltaf)))
               (S (length (concat deltas0 ++ deltaf) + length evs0))
               (concat deltas0 ++ deltaf)
               (firstn (Z.to_nat p0) done)) by lia.
    rewrite (dec_blocks_prefix evs0 deltas0 done p0 pmid deltaf d0 HF
               ltac:(rewrite <- Edmid; exact HD0) HT0
               ltac:(exact Hpar)
               (S (length (concat deltas0 ++ deltaf) + length evs0))
               ltac:(lia)).
    destruct (S (length (concat deltas0 ++ deltaf) + length evs0)
              - length evs0)%nat as [|fuel'] eqn:Ef.
    { lia. }
    cbn [dec_stream_fuel].
    rewrite <- Hpmid, Hf.
    cbv beta iota.
    rewrite Hpendf. reflexivity.
  - intros HBK EFR.
    pose proof (HdecfsG HBK EFR [] ltac:(reflexivity)) as Hfs.
    rewrite !app_nil_r in Hfs.
    unfold dec_stream_from_strict.
    rewrite (dec_stream_strict_fuel_indep
               (S (length (concat deltas0 ++ deltaf)))
               (S (length (concat deltas0 ++ deltaf) + length evs0))
               (concat deltas0 ++ deltaf)
               (firstn (Z.to_nat p0) done)) by lia.
    rewrite (dec_blocks_prefix_strict evs0 deltas0 done p0 pmid deltaf d0
               HBK EFR HF
               ltac:(rewrite <- Edmid; exact HD0) HT0
               ltac:(exact Hpar)
               (S (length (concat deltas0 ++ deltaf) + length evs0))
               ltac:(lia)).
    destruct (S (length (concat deltas0 ++ deltaf) + length evs0)
              - length evs0)%nat as [|fuel2'] eqn:Ef2.
    { lia. }
    cbn [dec_stream_strict_fuel].
    rewrite <- Hpmid, Hfs.
    cbv beta iota.
    rewrite Hpendf. reflexivity.
  - exact Hpadlen.
Qed.

Print Assumptions dec_blocks.
