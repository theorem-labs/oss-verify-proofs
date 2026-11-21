(** * ZReproG6Q — the seams, CLOSED: BoundSeam + SpanSeam, zlib and gzip.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    q5-emitter's q5-evsnap landing put everything the discharges need INTO
    the packs (hoisted tile, ZRTreeInv at every snapshot, Forall EvSnapOk,
    dg_max_dist = 32506).  This file assembles the landed pieces into the
    four seam propositions themselves:

      zr_boundseam_holds   : ZR_BoundSeam      (zlib,  4 <= availout)
      zr_gzboundseam_holds : ZR_GzBoundSeam    (gzip,  8 <= availout)
      zr_spanseam_holds    : ZR_SpanSeam       (zlib)
      zr_gzspanseam_holds  : ZR_GzSpanSeam     (gzip)

    With q5's emitter_face_modulo3 / emitter_face_gz_modulo3, the emitter
    faces are now conditional on StaleSeam ONLY (g1's queued ScanR landing).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  SwWin SwEv SwStep G3Event ZRepro ZReproG6A ZReproG6I ZReproG6J ZReproG6K
  ZReproG6L ZReproG6N ZReproG6O ZReproG6P ZREmitBody ZREmitFace ZRGzFace ZREvSnap
  ZRSnapGlue ZRTreeState.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Small folds: extent >= token count; tile splitting and counting.
   ========================================================================== *)

Lemma toks_ext_ge_len : forall toks,
  cEnc toks -> Z.of_nat (length toks) <= toks_ext toks.
Proof.
  induction toks as [|t r IH]; intro He; cbn [toks_ext length].
  - lia.
  - inversion He as [|? ? Ht Hr]; subst.
    pose proof (tok_ext_pos t Ht). pose proof (IH Hr).
    rewrite Nat2Z.inj_succ. lia.
Qed.

(** A full (non-last) block spans at least 16383 bytes: the tally is at
    its memLevel-8 cap and every token covers at least one byte. *)
Lemma evsnap_min_span : forall g wrap done ev,
  EvOk g wrap done ev ->
  dg_sym_end g = 49149 ->
  (fe_last ev = 0 -> ts_symnext (d_ts (fe_s ev)) = dg_sym_end g) ->
  fe_last ev = 0 ->
  16383 <= fe_end ev - fe_start ev.
Proof.
  intros g wrap done ev HE Esym Hsn Hl0.
  destruct HE as (_ & _ & Hbuf & _ & Henc & _ & Hspan & Hend
                  & Hres & _ & _ & _).
  pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext.
  rewrite (Hsn Hl0), Esym in Hext.
  pose proof (resolve_length (fe_toks ev)
                (firstn (Z.to_nat (fe_start ev)) done)
                (firstn (Z.to_nat (fe_end ev)) done) Henc Hres) as RL.
  rewrite !g6_zlen_firstn in RL by lia.
  pose proof (toks_ext_ge_len (fe_toks ev) Henc).
  lia.
Qed.

Lemma evtile_split : forall l1 l2 a c,
  EvTile (l1 ++ l2) a c -> exists b, EvTile l1 a b /\ EvTile l2 b c.
Proof.
  induction l1 as [|ev r IH]; intros l2 a c HT.
  - exists a. split; [reflexivity | exact HT].
  - cbn [app EvTile] in HT. destruct HT as [Ha HT'].
    destruct (IH l2 (fe_end ev) c HT') as (b & H1 & H2).
    exists b. split; [split; [exact Ha | exact H1] | exact H2].
Qed.

Lemma evtile_full_count : forall evs a b,
  EvTile evs a b ->
  Forall (fun ev => 16383 <= fe_end ev - fe_start ev) evs ->
  a + 16383 * Z.of_nat (length evs) <= b.
Proof.
  induction evs as [|ev r IH]; intros a b HT HF; cbn [EvTile length] in *.
  - lia.
  - destruct HT as [Ha HT'].
    inversion HF as [|? ? Hh Hr]; subst.
    pose proof (IH (fe_end ev) b HT' Hr).
    rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma evtile_nonneg : forall evs a b,
  EvTile evs a b ->
  Forall (fun ev => 0 <= fe_end ev - fe_start ev) evs ->
  a <= b.
Proof.
  induction evs as [|ev r IH]; intros a b HT HF; cbn [EvTile] in *.
  - lia.
  - destruct HT as [Ha HT'].
    inversion HF as [|? ? Hh Hr]; subst.
    pose proof (IH (fe_end ev) b HT' Hr). lia.
Qed.

(* ==========================================================================
   2.  The chain induction: per-event budgets with bwv/avail threading.
   ========================================================================== *)

(** [flush_from_acct_full] plus the two clauses the CHAIN threads. *)
Lemma flush_from_acct_thread : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g -> dg_strategy g = 0 -> dg_sym_end g <= 49149 ->
  bwv (ts_bw (d_ts (fe_s ev))) ->
  0 <= zs_availout (d_strm (fe_s ev)) ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
  Forall tok_far_ok (fe_toks ev) ->
  (ls_blockstart (d_ls (fe_s ev)) < 0 -> 32506 < fe_end ev - fe_start ev) ->
  EvStepBudget ev
  /\ bwv (ts_bw (d_ts (flush_block_only (fe_last ev) (fe_s ev))))
  /\ 0 <= zs_availout (d_strm (flush_block_only (fe_last ev) (fe_s ev))).
Proof.
  intros g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo Hol Hsl Hbl
         HblZ HnnL HnnD Hfar Hsld.
  assert (HB : EvStepBudget ev)
    by (exact (flush_from_acct_full g wrap done ev HE Hlev Hstrat Hsend Hbwv
                 Havo Hol Hsl Hbl HblZ HnnL HnnD Hfar Hsld)).
  destruct (Z.le_gt_cases 0 (ls_blockstart (d_ls (fe_s ev)))) as [Hge|Hlt].
  - destruct (flush_block_only_acct g wrap done ev HE Hlev Hstrat Hsend
                Hbwv Havo Hge Hol Hsl Hbl HblZ HnnL HnnD)
      as (_ & _ & Hbwv' & _ & _ & Havo').
    exact (conj HB (conj Hbwv' Havo')).
  - destruct (flush_block_only_acct_none g wrap done ev HE Hlev Hstrat Hsend
                Hbwv Havo Hlt Hfar (Hsld Hlt) Hol Hsl Hbl HblZ HnnL HnnD)
      as (_ & _ & Hbwv' & _ & _ & Havo').
    exact (conj HB (conj Hbwv' Havo')).
Qed.

(** The whole chain's budgets, from the start-state writer facts. *)
Lemma evchain_budget : forall g wrap done evs bw out avo bw' out' avo',
  EvChain evs bw out avo bw' out' avo' ->
  Forall (EvOk g wrap done) evs ->
  Forall (EvSnapOk g) evs ->
  0 < dg_level g -> dg_strategy g = 0 -> dg_sym_end g <= 49149 ->
  dg_max_dist g = 32506 ->
  bwv bw -> 0 <= avo ->
  Forall EvStepBudget evs.
Proof.
  intros g wrap done evs.
  induction evs as [|ev r IH];
    intros bw out avo bw' out' avo' HCh HOk HSn Hlev Hstrat Hsend Hmaxd
           Hbwv Havo.
  - constructor.
  - cbn [EvChain] in HCh.
    destruct HCh as (Hbw & Hout & Havoe & HCh').
    pose proof (Forall_inv HOk) as HOk1.
    pose proof (Forall_inv_tail HOk) as HOkr.
    pose proof (Forall_inv HSn) as HSn1.
    pose proof (Forall_inv_tail HSn) as HSnr.
    destruct HSn1 as (HTI & Hol & Hsl & _ & Hfar & Hsld).
    destruct HTI as (Hbl & HblZ & HnnL & HnnD & _).
    assert (HblZ' : forall v, 0 <= v < 19 ->
              t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0)
      by (intros v Hv; apply HblZ;
          change BL_CODES with 19; lia).
    destruct (flush_from_acct_thread g wrap done ev HOk1 Hlev Hstrat Hsend
                ltac:(rewrite Hbw; exact Hbwv)
                ltac:(rewrite Havoe; exact Havo)
                Hol Hsl Hbl HblZ' HnnL HnnD
                (farok_forall_to _ Hfar)
                ltac:(intro Hb; rewrite <- Hmaxd; exact (Hsld Hb)))
      as (HB & Hbwv' & Havo').
    constructor; [exact HB|].
    exact (IH _ _ _ bw' out' avo' HCh' HOkr HSnr Hlev Hstrat Hsend Hmaxd
             Hbwv' Havo').
Qed.

(* ==========================================================================
   3.  The seam theorems, zlib.
   ========================================================================== *)

Theorem zr_boundseam_holds : ZR_BoundSeam.
Proof.
  intros x g sd bs s' evs Hx Hcap P.
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HFOk & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile' & HTIsd & HTIs' & HFSn & Hmaxd).
  assert (Elev : 0 < dg_level g) by (rewrite Hlvl; lia).
  assert (Esym : dg_sym_end g = 49149).
  { vm_compute in Eg. injection Eg as Eg. rewrite <- Eg. reflexivity. }
  assert (Hbwv0 : bwv (ts_bw (d_ts sd)))
    by (unfold bwv; rewrite Hbvsd; unfold Buf_size; lia).
  assert (Havo0 : 0 <= zs_availout (d_strm sd)).
  { rewrite Havosd.
    pose proof (zr_bound_lo (zlen x) (zlen_nonneg x)). lia. }
  pose proof (evchain_budget g 1 (zs_done (d_strm s')) evs _ _ _ _ _ _
                HC HFOk HFSn Elev Hstrat ltac:(lia) Hmaxd Hbwv0 Havo0)
    as HBud.
  destruct Htile' as (te & Htile & Hte).
  assert (Hsp0 : Forall (fun ev => 0 <= fe_end ev - fe_start ev) evs).
  { eapply Forall_impl; [|exact HFOk].
    intros ev HE.
    destruct HE as (_ & _ & _ & _ & _ & _ & Hspan & _). lia. }
  assert (Hte0 : 0 <= te)
    by (pose proof (evtile_nonneg evs 0 te Htile Hsp0); lia).
  assert (Hdone_le : zlen (zs_done (d_strm s')) <= zlen x).
  { rewrite <- Hcons, g6_zlen_app.
    pose proof (zlen_nonneg (zs_in (d_strm s'))). lia. }
  assert (HT : 0 <= te <= zlen x) by lia.
  assert (Hblocks : Z.of_nat (length evs) <= zr_hnblocks (zlen x)).
  { unfold zr_hnblocks.
    destruct Hout as [HL | HR].
    - destruct HL as (evs0 & evf & Ee & H0s & Hl1 & _ & _ & _ & _ & _ & _).
      subst evs.
      destruct (evtile_split evs0 [evf] 0 te Htile) as (m & Ht0 & Ht1).
      assert (HFull : Forall (fun ev => 16383 <= fe_end ev - fe_start ev)
                        evs0).
      { rewrite Forall_forall. intros ev Hin.
        rewrite Forall_forall in HFOk, HFSn, H0s.
        assert (Hin' : In ev (evs0 ++ [evf]))
          by (apply in_or_app; left; exact Hin).
        destruct (HFSn ev Hin') as (_ & _ & _ & Hsn & _ & _).
        exact (evsnap_min_span g 1 (zs_done (d_strm s')) ev (HFOk ev Hin')
                 Esym Hsn (H0s ev Hin)). }
      pose proof (evtile_full_count evs0 0 m Ht0 HFull) as Hcnt.
      cbn [EvTile] in Ht1. destruct Ht1 as [Hm Hte'].
      assert (Hmf : 0 <= fe_end evf - fe_start evf).
      { rewrite Forall_forall in Hsp0.
        apply Hsp0. apply in_or_app. right. left. reflexivity. }
      rewrite length_app. cbn [length].
      rewrite Nat2Z.inj_add.
      assert (Hq : Z.of_nat (length evs0) <= zlen x / 16383).
      { apply Z.div_le_lower_bound; lia. }
      cbn [Z.of_nat]. lia.
    - destruct HR as (_ & _ & H0all).
      assert (HFull : Forall (fun ev => 16383 <= fe_end ev - fe_start ev)
                        evs).
      { rewrite Forall_forall. intros ev Hin.
        rewrite Forall_forall in HFOk, HFSn, H0all.
        destruct (HFSn ev Hin) as (_ & _ & _ & Hsn & _ & _).
        exact (evsnap_min_span g 1 (zs_done (d_strm s')) ev (HFOk ev Hin)
                 Esym Hsn (H0all ev Hin)). }
      pose proof (evtile_full_count evs 0 te Htile HFull) as Hcnt.
      assert (Hq : Z.of_nat (length evs) <= zlen x / 16383).
      { apply Z.div_le_lower_bound; lia. }
      lia. }
  assert (H4 : 4 <= zs_availout (d_strm s')).
  { refine (zr_bound_fits_p x evs (ts_bw (d_ts sd)) (ts_bw (d_ts s'))
             (zs_out (d_strm sd)) (zs_out (d_strm s'))
             (zs_availout (d_strm sd)) (zs_availout (d_strm s'))
             (zr_deflate_bound 15 (zlen x)) 2 4
             (conj (zlen_nonneg x) Hcap) HC te HT Htile HBud Hblocks
             _ _ _ _).
    - rewrite Houtsd. reflexivity.
    - rewrite (zbits_eqn _ ltac:(rewrite Hbvsd; lia)).
      rewrite Hbwsd, Hbvsd. reflexivity.
    - exact Havosd.
    - pose proof (zr_room_bound (zlen x) (conj (zlen_nonneg x) Hcap)).
      lia. }
  destruct Hout as [HL | HR].
  - destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfin).
    destruct Hfin as [(E1 & E2) | (E1 & _)].
    + exfalso. lia.
    + exact (conj E1 H4).
  - destruct HR as (_ & E2 & _). exfalso. lia.
Qed.

Theorem zr_spanseam_holds : ZR_SpanSeam.
Proof.
  intros x g sd bs s' evs Hx P.
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HFOk & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile' & HTIsd & HTIs' & HFSn & Hmaxd).
  assert (Elev : 0 < dg_level g) by (rewrite Hlvl; lia).
  assert (Esym : dg_sym_end g = 49149).
  { vm_compute in Eg. injection Eg as Eg. rewrite <- Eg. reflexivity. }
  rewrite Forall_forall. intros ev Hin.
  rewrite Forall_forall in HFOk, HFSn.
  destruct (HFSn ev Hin) as (HTI & Hol & Hsl & _ & _ & _).
  destruct HTI as (Hbl & HblZ & HnnL & HnnD & _).
  apply (span_guard_holds g 1 (zs_done (d_strm s')) ev (HFOk ev Hin) Elev
           ltac:(lia) Hol Hsl Hbl).
  - intros v Hv. apply HblZ. change BL_CODES with 19. lia.
  - exact HnnL.
  - exact HnnD.
Qed.

(* ==========================================================================
   4.  The seam theorems, gzip.
   ========================================================================== *)

Theorem zr_gzboundseam_holds : ZR_GzBoundSeam.
Proof.
  intros x g sd bs s' evs Hx Hcap P.
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HFOk & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile' & HTIsd & HTIs' & HFSn & Hmaxd).
  assert (Elev : 0 < dg_level g) by (rewrite Hlvl; lia).
  assert (Esym : dg_sym_end g = 49149).
  { vm_compute in Eg. injection Eg as Eg. rewrite <- Eg. reflexivity. }
  assert (Hbwv0 : bwv (ts_bw (d_ts sd)))
    by (unfold bwv; rewrite Hbvsd; unfold Buf_size; lia).
  assert (Hblo : 25 <= zr_deflate_bound 31 (zlen x)).
  { pose proof (zlen_nonneg x) as Hn.
    unfold zr_deflate_bound, zr_wraplen.
    replace (31 <? 0) with false by reflexivity.
    replace (15 <? 31) with true by reflexivity.
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 12) Hn).
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 14) Hn).
    pose proof (proj2 (Z.shiftr_nonneg (zlen x) 25) Hn).
    lia. }
  assert (Havo0 : 0 <= zs_availout (d_strm sd)) by (rewrite Havosd; lia).
  pose proof (evchain_budget g 2 (zs_done (d_strm s')) evs _ _ _ _ _ _
                HC HFOk HFSn Elev Hstrat ltac:(lia) Hmaxd Hbwv0 Havo0)
    as HBud.
  destruct Htile' as (te & Htile & Hte).
  assert (Hsp0 : Forall (fun ev => 0 <= fe_end ev - fe_start ev) evs).
  { eapply Forall_impl; [|exact HFOk].
    intros ev HE.
    destruct HE as (_ & _ & _ & _ & _ & _ & Hspan & _). lia. }
  assert (Hte0 : 0 <= te)
    by (pose proof (evtile_nonneg evs 0 te Htile Hsp0); lia).
  assert (Hdone_le : zlen (zs_done (d_strm s')) <= zlen x).
  { rewrite <- Hcons, g6_zlen_app.
    pose proof (zlen_nonneg (zs_in (d_strm s'))). lia. }
  assert (HT : 0 <= te <= zlen x) by lia.
  assert (Hblocks : Z.of_nat (length evs) <= zr_hnblocks (zlen x)).
  { unfold zr_hnblocks.
    destruct Hout as [HL | HR].
    - destruct HL as (evs0 & evf & Ee & H0s & Hl1 & _ & _ & _ & _ & _ & _).
      subst evs.
      destruct (evtile_split evs0 [evf] 0 te Htile) as (m & Ht0 & Ht1).
      assert (HFull : Forall (fun ev => 16383 <= fe_end ev - fe_start ev)
                        evs0).
      { rewrite Forall_forall. intros ev Hin.
        rewrite Forall_forall in HFOk, HFSn, H0s.
        assert (Hin' : In ev (evs0 ++ [evf]))
          by (apply in_or_app; left; exact Hin).
        destruct (HFSn ev Hin') as (_ & _ & _ & Hsn & _ & _).
        exact (evsnap_min_span g 2 (zs_done (d_strm s')) ev (HFOk ev Hin')
                 Esym Hsn (H0s ev Hin)). }
      pose proof (evtile_full_count evs0 0 m Ht0 HFull) as Hcnt.
      cbn [EvTile] in Ht1. destruct Ht1 as [Hm Hte'].
      assert (Hmf : 0 <= fe_end evf - fe_start evf).
      { rewrite Forall_forall in Hsp0.
        apply Hsp0. apply in_or_app. right. left. reflexivity. }
      rewrite length_app. cbn [length].
      rewrite Nat2Z.inj_add.
      assert (Hq : Z.of_nat (length evs0) <= zlen x / 16383).
      { apply Z.div_le_lower_bound; lia. }
      cbn [Z.of_nat]. lia.
    - destruct HR as (_ & _ & H0all).
      assert (HFull : Forall (fun ev => 16383 <= fe_end ev - fe_start ev)
                        evs).
      { rewrite Forall_forall. intros ev Hin.
        rewrite Forall_forall in HFOk, HFSn, H0all.
        destruct (HFSn ev Hin) as (_ & _ & _ & Hsn & _ & _).
        exact (evsnap_min_span g 2 (zs_done (d_strm s')) ev (HFOk ev Hin)
                 Esym Hsn (H0all ev Hin)). }
      pose proof (evtile_full_count evs 0 te Htile HFull) as Hcnt.
      assert (Hq : Z.of_nat (length evs) <= zlen x / 16383).
      { apply Z.div_le_lower_bound; lia. }
      lia. }
  assert (H8 : 8 <= zs_availout (d_strm s')).
  { refine (zr_bound_fits_p x evs (ts_bw (d_ts sd)) (ts_bw (d_ts s'))
             (zs_out (d_strm sd)) (zs_out (d_strm s'))
             (zs_availout (d_strm sd)) (zs_availout (d_strm s'))
             (zr_deflate_bound 31 (zlen x)) 10 8
             (conj (zlen_nonneg x) Hcap) HC te HT Htile HBud Hblocks
             _ _ _ _).
    - rewrite Houtsd. reflexivity.
    - rewrite (zbits_eqn _ ltac:(rewrite Hbvsd; lia)).
      rewrite Hbwsd, Hbvsd. reflexivity.
    - exact Havosd.
    - pose proof (zr_room_bound31 (zlen x) (conj (zlen_nonneg x) Hcap)).
      lia. }
  destruct Hout as [HL | HR].
  - destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfin).
    destruct Hfin as [(E1 & E2) | (E1 & _)].
    + exfalso. lia.
    + exact (conj E1 H8).
  - destruct HR as (_ & E2 & _). exfalso. lia.
Qed.

Theorem zr_gzspanseam_holds : ZR_GzSpanSeam.
Proof.
  intros x g sd bs s' evs Hx P.
  destruct P as (Eg & Hlvl & Hstrat & Hwb & Hgeom & Eslow & Hcfgsd & Hwrapsd
                 & Houtsd & Havosd & Hinsd & Hdnsd & Hbwsd & Hbvsd & Hbufsd
                 & HI & HFOk & HC & Hcons & Hw' & Hc' & Hout & Hcond
                 & Htile' & HTIsd & HTIs' & HFSn & Hmaxd).
  assert (Elev : 0 < dg_level g) by (rewrite Hlvl; lia).
  assert (Esym : dg_sym_end g = 49149).
  { vm_compute in Eg. injection Eg as Eg. rewrite <- Eg. reflexivity. }
  rewrite Forall_forall. intros ev Hin.
  rewrite Forall_forall in HFOk, HFSn.
  destruct (HFSn ev Hin) as (HTI & Hol & Hsl & _ & _ & _).
  destruct HTI as (Hbl & HblZ & HnnL & HnnD & _).
  apply (span_guard_holds g 2 (zs_done (d_strm s')) ev (HFOk ev Hin) Elev
           ltac:(lia) Hol Hsl Hbl).
  - intros v Hv. apply HblZ. change BL_CODES with 19. lia.
  - exact HnnL.
  - exact HnnD.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions zr_boundseam_holds.
Print Assumptions zr_spanseam_holds.
Print Assumptions zr_gzboundseam_holds.
Print Assumptions zr_gzspanseam_holds.
Unset Printing All.
