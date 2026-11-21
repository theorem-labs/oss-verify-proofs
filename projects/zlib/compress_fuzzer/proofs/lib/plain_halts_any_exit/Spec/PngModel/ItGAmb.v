(** * ItGAmb — [amb_ok] survives a build's write-back (the [dyn_amb_wb]
      residual, ALL exits: accepted, rejected, overflow).

    OWNER: an earlier development run (inhabitation lap).  [amb_ok] (InflateThy, chain
    repair 2026-08-19) is the pointwise ambient contract of the codes
    array; inflate installs [codes_wb cs k (o_tbl o)] BEFORE testing the
    build's return, so preservation may not assume acceptance.  The walk:
    every fill writes an [it_here] leaf (whose [LeafShape] covers amb's
    op/val clauses and whose width is [len - drop], in [1,15] by the
    landed [CovInv] — which holds on EVERY [PreGo] path, acceptance only
    separates Break from Overflow); every pointer write is capped by the
    [it_enough] test it just passed (LENS/DISTS), or cannot happen at all
    (CT_CODES with lens bounded by [root0] — the guard premise; the
    uncapped exotic-CODES corner is REAL, see the counterexample note in
    the lane log, and the guard is free at the one real CODES call). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees Inflate InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGTblRepl ItGTblLeafPos
  GtUsedBits GtLenProv ItGSubCover.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** The per-entry ambient shape, and its closure facts. *)
Definition AmbE (e : Code) : Prop :=
  0 <= c_bits e <= 15
  /\ 0 <= c_val e < 65536
  /\ (Z.land (c_op e) 32 <> 0 -> 1 <= c_bits e)
  /\ (c_op e <> 0 -> Z.land (c_op e) 32 = 0 ->
      Z.land (c_op e) 64 = 0 -> 1 <= c_val e)
  /\ (Z.land (c_op e) 16 <> 0 -> Z.land (c_op e) 15 <= 13).

Lemma amb_ok_iff : forall t, amb_ok t <-> (forall i, AmbE (t i)).
Proof. intro t. exact (iff_refl _). Qed.

Lemma amb_tset : forall t i e,
  (forall j, AmbE (t j)) -> AmbE e -> forall j, AmbE (tset t i e j).
Proof.
  intros t i e Ht He j.
  destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite tset_same. exact He.
  - rewrite tset_other by exact Hne. apply Ht.
Qed.

Lemma amb_fill : forall n t bi incr h,
  0 < incr ->
  (forall j, AmbE (t j)) -> AmbE h ->
  forall j, AmbE (it_fill n t bi incr h j).
Proof.
  intros n t bi incr h Hincr Ht Hh j.
  destruct (fill_pointwise n t bi incr h j Hincr) as [-> | ->];
    [exact Hh | apply Ht].
Qed.

(** A written leaf of known width satisfies the ambient shape. *)
Lemma AmbE_of_leafshape : forall ty e,
  LeafShape ty e -> 1 <= c_bits e <= 15 -> AmbE e.
Proof.
  intros ty e (Hop3 & Hdz & Hopr & Hvr & H15 & H258 & Hlive) Hb.
  split; [lia|].
  split; [exact Hvr|].
  split; [intro; lia|].
  split; [exact Hlive|].
  intro H16. specialize (H15 H16).
  unfold x15_bound in H15.
  destruct (Z.eqb ty CT_DISTS); lia.
Qed.

(** Small widths have bits 4 and 5 clear. *)
Lemma land_small_pow2 : forall w k,
  0 <= w < 2 ^ k -> 0 < k -> Z.land w (2 ^ k) = 0.
Proof.
  intros w k Hw Hk.
  apply land_pow2_zero_iff; [lia|].
  destruct (Z.eq_dec w 0) as [->|Hnz]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  apply Z.log2_lt_pow2; lia.
Qed.

(** A written sub-table pointer satisfies it, given the value cap the
    write-site's [it_enough] test just certified. *)
Lemma AmbE_pointer : forall w b v,
  1 <= w <= 15 -> 0 <= b <= 15 -> 1 <= v < 65536 ->
  AmbE (mkCodeT w b v).
Proof.
  intros w b v Hw Hb Hv.
  split; [rewrite bits_mkCodeT by lia; lia|].
  split; [rewrite val_mkCodeT_id by lia; lia|].
  rewrite op_mkCodeT_id by lia.
  split.
  { intro H32. exfalso. apply H32.
    change 32 with (2 ^ 5).
    apply land_small_pow2; [|lia].
    change (2 ^ 5) with 32. lia. }
  split.
  { intros _ _ _. rewrite val_mkCodeT_id by lia. lia. }
  { intro H16. exfalso. apply H16.
    change 16 with (2 ^ 4).
    apply land_small_pow2; [|lia].
    change (2 ^ 4) with 16. lia. }
Qed.

(** The finish fix-up marker. *)
Lemma AmbE_marker : forall b, 1 <= b <= 15 -> AmbE (mkCodeT 64 b 0).
Proof.
  intros b Hb.
  split; [rewrite bits_mkCodeT by lia; lia|].
  split; [apply val_mkCodeT_range|].
  rewrite op_mkCodeT_id by lia.
  split; [intro Hc; exfalso; vm_compute in Hc; apply Hc; reflexivity|].
  split; [intros _ _ Hc; exfalso; vm_compute in Hc; discriminate Hc|].
  intro Hc. exfalso. vm_compute in Hc. apply Hc. reflexivity.
Qed.

Lemma zcount_nonneg : forall n i0 lens b, 0 <= zcount n i0 lens b.
Proof.
  induction n as [|k IH]; intros i0 lens b; cbn [zcount]; [lia|].
  specialize (IH (i0 + 1) lens b).
  destruct (Z.eqb (lens i0) b); lia.
Qed.

(** membership in the histogram: a live symbol's length has positive count *)
Lemma zcount_member : forall n i0 lens j,
  i0 <= j < i0 + Z.of_nat n -> 1 <= zcount n i0 lens (lens j).
Proof.
  induction n as [|k IH]; intros i0 lens j Hj; cbn [zcount] in *;
    [lia|].
  rewrite Nat2Z.inj_succ in Hj.
  destruct (Z.eq_dec j i0) as [->|Hne].
  - rewrite Z.eqb_refl.
    pose proof (zcount_nonneg k (i0 + 1) lens (lens i0)). lia.
  - assert (Hin : 1 <= zcount k (i0 + 1) lens (lens j))
      by (apply IH; lia).
    destruct (Z.eqb (lens i0) (lens j)); lia.
Qed.


(** ** One trip preserves the ambient contract — every exit *)

Lemma amb_step : forall ty c cnt0 st,
  ty = x_type c ->
  (x_type c = CT_LENS \/ x_type c = CT_DISTS \/ x_max c <= x_root c) ->
  0 < x_codes c ->
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  LeafShape ty (it_here c st) ->
  (forall j, AmbE (s_tbl st j)) ->
  match it_step c st with
  | ItCont st' => forall j, AmbE (s_tbl st' j)
  | ItBreak st' => forall j, AmbE (s_tbl st' j)
  | ItOverflow t => forall j, AmbE (t j)
  end.
Proof.
  intros ty c cnt0 st Hcty Hty3 Hcod Hctx Hinv Hled Hherel Hamb.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof Hinv as Hinv2.
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hled as (HrootB & Hledph).
  assert (Hbits_here : c_bits (it_here c st) = s_len st - s_drop st).
  { apply bits_here_val.
    destruct Hphase as [(Hd & _) | (Hd & Hrl & _)]; rewrite Hd; lia. }
  assert (Hbh2 : 1 <= c_bits (it_here c st) <= 15).
  { rewrite Hbits_here.
    destruct Hphase as [(Hd & _ & _ & _ & Hlr) | (Hd & Hrl & _)];
      rewrite Hd; lia. }
  pose proof (AmbE_of_leafshape ty _ Hherel Hbh2) as Hhere_amb.
  assert (Hincr : 0 < Z.shiftl 1 (s_len st - s_drop st)).
  { rewrite shiftl1
      by (destruct Hphase as [(Hd & _) | (Hd & Hrl & _)]; rewrite Hd; lia).
    apply pow2_pos_z.
    destruct Hphase as [(Hd & _) | (Hd & Hrl & _)]; rewrite Hd; lia. }
  assert (Hfillamb : forall j, AmbE
            (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                                / Z.shiftl 1 (s_len st - s_drop st)))
               (s_tbl st)
               (s_next st + Z.shiftr (s_huff st) (s_drop st))
               (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st) j))
    by (apply amb_fill; [exact Hincr | exact Hamb | exact Hhere_amb]).
  assert (Hlensmx : forall i, 0 <= i < x_codes c -> x_lens c i <= x_max c).
  { intros i Hi.
    destruct (Z_le_gt_dec (x_lens c i) (x_max c)) as [?|Hgt2];
      [assumption | exfalso].
    assert (Hz : cnt0 (x_lens c i) = 0)
      by (apply Hmxz; pose proof (Hlens i Hi); lia).
    rewrite Hcnt0 in Hz. unfold sw_cnt in Hz.
    rewrite it_count_spec in Hz.
    unfold zzero, zconst in Hz.
    pose proof (zcount_member (Z.to_nat (x_codes c)) 0 (x_lens c) i
                  ltac:(lia)) as Hm.
    lia. }
  unfold it_step. cbv zeta.
  destruct (Z.eqb
              (zset (s_count st) (s_len st) (s_count st (s_len st) - 1)
                 (s_len st)) 0) eqn:Hhit.
  - destruct (Z.eqb (s_len st) (x_max c)) eqn:Hmxeq; cbn [andb];
      cbv beta match iota.
    + cbn [s_tbl]. exact Hfillamb.
    + set (L1 := x_lens c (x_work c (s_sym st + 1))) in *.
      assert (HL1r : 0 <= L1 <= x_max c).
      { unfold L1.
        assert (Hwr : 0 <= x_work c (s_sym st + 1) < x_codes c)
          by (rewrite Hwork; apply sort_zzero_range; exact Hcod).
        split; [apply Hlens; lia | apply Hlensmx; lia]. }
      destruct (Z.ltb (x_root c) L1) eqn:Hgt; cbn [andb].
      * apply Z.ltb_lt in Hgt.
        destruct (Z.eqb (Z.land (it_rev_incr (s_huff st) (s_len st))
                           (x_mask c)) (s_low st)) eqn:Hsame;
          cbn [andb negb]; cbv beta match iota.
        -- cbn [s_tbl]. exact Hfillamb.
        -- (* new window *)
           replace (if Z.eqb (s_drop st) 0 then x_root c else s_drop st)
             with (x_root c)
             by (destruct Hphase as [(Hd & _) | (Hd & _)]; rewrite Hd;
                 [ rewrite Z.eqb_refl; reflexivity
                 | replace (Z.eqb (x_root c) 0) with false
                     by (symmetry; apply Z.eqb_neq; lia); reflexivity ]).
           match goal with
           | |- context [it_enough _ (_ + Z.shiftl 1 ?cv)] =>
               remember cv as curr' eqn:Hcurr'
           end.
           assert (Hcb' : 1 <= curr' <= 15 - x_root c).
           { pose proof (it_subsz_bounds 16%nat
                          (zset (s_count st) (s_len st)
                             (s_count st (s_len st) - 1))
                          (x_root c) (x_max c) (L1 - x_root c)
                          (Z.shiftl 1 (L1 - x_root c))) as HB.
             rewrite <- Hcurr' in HB. lia. }
           destruct (it_enough (x_type c) (s_used st + Z.shiftl 1 curr'))
             eqn:Hen; cbv beta match iota.
           ++ exact Hfillamb.
           ++ cbn [s_tbl].
              intro j. apply amb_tset; [exact Hfillamb|].
              assert (Hnx' : 1 <= s_next st + Z.shiftl 1 (s_curr st)
                             < 65536).
              { destruct Hledph
                  as [(Hd0 & Hu0 & Hn0)
                     | (Hd2 & Hcb & Hue & Hnx2 & Hu16 & _)].
                - destruct Hphase as [(Hd & Hc & Hnx & _) | (Hd & _)];
                    [| exfalso; clear -Hd Hd0 Hroot; lia].
                  rewrite Hn0, Hc, shiftl1 by lia.
                  assert (Hq1 : (2:Z) ^ x_root c <= 2 ^ 15)
                    by (apply Z.pow_le_mono_r; lia).
                  assert (Hq2 : (2:Z) ^ 15 = 32768) by reflexivity.
                  pose proof (pow2_pos_z (x_root c) ltac:(lia)) as Hq3.
                  clear -Hq1 Hq2 Hq3. lia.
                - rewrite shiftl1 by (clear -Hcb; lia).
                  pose proof (pow2_pos_z (s_curr st) ltac:(clear -Hcb; lia))
                    as Hq1.
                  pose proof (pow2_pos_z (x_root c) ltac:(lia)) as Hq2.
                  assert (Hcap : s_used st + Z.shiftl 1 curr' <= 852).
                  { destruct Hty3 as [HtL | [HtD | Hcap3]];
                      [ rewrite HtL in Hen | rewrite HtD in Hen
                      | exfalso; clear -Hcap3 Hgt HL1r; lia ];
                      unfold it_enough in Hen; cbn in Hen;
                      rewrite ?orb_false_r in Hen;
                      apply Z.ltb_ge in Hen;
                      unfold ENOUGH_LENS, ENOUGH_DISTS in Hen; lia. }
                  rewrite shiftl1 in Hcap by (clear -Hcb'; lia).
                  pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia))
                    as Hq4.
                  clear -Hue Hnx2 Hq1 Hq2 Hq4 Hcap. lia. }
              apply AmbE_pointer;
                [clear -Hcb' Hroot; lia | clear -Hroot; lia | exact Hnx'].
      * cbv beta match iota. cbn [s_tbl]. exact Hfillamb.
  - cbn [andb]. cbv beta match iota.
    set (L1 := s_len st) in *.
    assert (HL1r : 0 <= L1 <= x_max c).
    { unfold L1. split; [lia|].
      destruct (Z_le_gt_dec L1 (x_max c)) as [?|Hgx];
        [assumption | exfalso].
      rewrite (Hmxz L1 ltac:(lia)) in HwinU. lia. }
    destruct (Z.ltb (x_root c) L1) eqn:Hgt; cbn [andb].
    + apply Z.ltb_lt in Hgt.
      destruct (Z.eqb (Z.land (it_rev_incr (s_huff st) L1)
                         (x_mask c)) (s_low st)) eqn:Hsame;
        cbn [andb negb]; cbv beta match iota.
      * cbn [s_tbl]. exact Hfillamb.
      * (* new window *)
        replace (if Z.eqb (s_drop st) 0 then x_root c else s_drop st)
          with (x_root c)
          by (destruct Hphase as [(Hd & _) | (Hd & _)]; rewrite Hd;
              [ rewrite Z.eqb_refl; reflexivity
              | replace (Z.eqb (x_root c) 0) with false
                  by (symmetry; apply Z.eqb_neq; lia); reflexivity ]).
        match goal with
        | |- context [it_enough _ (_ + Z.shiftl 1 ?cv)] =>
            remember cv as curr' eqn:Hcurr'
        end.
        assert (Hcb' : 1 <= curr' <= 15 - x_root c).
        { pose proof (it_subsz_bounds 16%nat
                    (zset (s_count st) L1 (s_count st L1 - 1))
                    (x_root c) (x_max c) (L1 - x_root c)
                    (Z.shiftl 1 (L1 - x_root c))) as HB.
          rewrite <- Hcurr' in HB. lia. }
        destruct (it_enough (x_type c) (s_used st + Z.shiftl 1 curr'))
          eqn:Hen; cbv beta match iota.
        ++ exact Hfillamb.
        ++ cbn [s_tbl].
           intro j. apply amb_tset; [exact Hfillamb|].
           assert (Hnx' : 1 <= s_next st + Z.shiftl 1 (s_curr st)
                       < 65536).
           { destruct Hledph
               as [(Hd0 & Hu0 & Hn0)
                  | (Hd2 & Hcb & Hue & Hnx2 & Hu16 & _)].
             - destruct Hphase as [(Hd & Hc & Hnx & _) | (Hd & _)];
                 [| exfalso; clear -Hd Hd0 Hroot; lia].
               rewrite Hn0, Hc, shiftl1 by lia.
               assert (Hq1 : (2:Z) ^ x_root c <= 2 ^ 15)
                 by (apply Z.pow_le_mono_r; lia).
               assert (Hq2 : (2:Z) ^ 15 = 32768) by reflexivity.
               pose proof (pow2_pos_z (x_root c) ltac:(lia)) as Hq3.
               clear -Hq1 Hq2 Hq3. lia.
             - rewrite shiftl1 by (clear -Hcb; lia).
               pose proof (pow2_pos_z (s_curr st) ltac:(clear -Hcb; lia))
                 as Hq1.
               pose proof (pow2_pos_z (x_root c) ltac:(lia)) as Hq2.
               assert (Hcap : s_used st + Z.shiftl 1 curr' <= 852).
               { destruct Hty3 as [HtL | [HtD | Hcap3]];
                [ rewrite HtL in Hen | rewrite HtD in Hen
                | exfalso; clear -Hcap3 Hgt HL1r; lia ];
                unfold it_enough in Hen; cbn in Hen;
                rewrite ?orb_false_r in Hen;
                apply Z.ltb_ge in Hen;
                unfold ENOUGH_LENS, ENOUGH_DISTS in Hen; lia. }
               rewrite shiftl1 in Hcap by (clear -Hcb'; lia).
               pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia))
                 as Hq4.
               clear -Hue Hnx2 Hq1 Hq2 Hq4 Hcap. lia. }
           apply AmbE_pointer;
             [clear -Hcb' Hroot; lia | clear -Hroot; lia | exact Hnx'].
    + cbv beta match iota. cbn [s_tbl]. exact Hfillamb.
Qed.

(** the [it_pre] root clamp only ever RAISES a root that is already
    at least the max — shape-generic, so the caller needs no spelling *)
Lemma clamp_ge : forall mx r0 mn,
  mx <= r0 ->
  mx <= (if (if mx <? r0 then mx else r0) <? mn
         then mn else (if mx <? r0 then mx else r0)).
Proof.
  intros mx r0 mn H.
  destruct (Z.ltb mx r0) eqn:E1.
  - destruct (Z.ltb mx mn) eqn:E2;
      [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; lia.
  - destruct (Z.ltb r0 mn) eqn:E2;
      [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; lia.
Qed.

(** existence from a positive count *)
Lemma zcount_pos_ex : forall n i0 lens b,
  0 < zcount n i0 lens b ->
  exists j, i0 <= j < i0 + Z.of_nat n /\ lens j = b.
Proof.
  induction n as [|k IH]; intros i0 lens b H; cbn [zcount] in H; [lia|].
  destruct (Z.eqb_spec (lens i0) b) as [He|Hne].
  - exists i0. split; [lia | exact He].
  - destruct (IH (i0 + 1) lens b ltac:(lia)) as [j [Hj Hl]].
    exists j. split; [lia | exact Hl].
Qed.

(** the break's fix-up write *)
Lemma amb_break_finish : forall ty c cnt0 st st1,
  ty = x_type c ->
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  LeafShape ty (it_here c st) ->
  (forall j, AmbE (s_tbl st j)) ->
  it_step c st = ItBreak st1 ->
  forall j, AmbE (it_finish st1 j).
Proof.
  intros ty c cnt0 st st1 Hcty Hctx Hinv Hherel Hamb Hstep.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  assert (Hbits_here : c_bits (it_here c st) = s_len st - s_drop st).
  { apply bits_here_val.
    destruct Hphase as [(Hd & _) | (Hd & Hrl & _)]; rewrite Hd; lia. }
  assert (Hbh2 : 1 <= c_bits (it_here c st) <= 15).
  { rewrite Hbits_here.
    destruct Hphase as [(Hd & _ & _ & _ & Hlr) | (Hd & Hrl & _)];
      rewrite Hd; lia. }
  pose proof (AmbE_of_leafshape ty _ Hherel Hbh2) as Hhere_amb.
  assert (Hincr : 0 < Z.shiftl 1 (s_len st - s_drop st)).
  { rewrite shiftl1
      by (destruct Hphase as [(Hd & _) | (Hd & Hrl & _)]; rewrite Hd; lia).
    apply pow2_pos_z.
    destruct Hphase as [(Hd & _) | (Hd & Hrl & _)]; rewrite Hd; lia. }
  assert (Hfillamb : forall j, AmbE
            (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                                / Z.shiftl 1 (s_len st - s_drop st)))
               (s_tbl st)
               (s_next st + Z.shiftr (s_huff st) (s_drop st))
               (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st) j))
    by (apply amb_fill; [exact Hincr | exact Hamb | exact Hhere_amb]).
  unfold it_step in Hstep. cbv zeta in Hstep.
  destruct (Z.eqb (zset (s_count st) (s_len st)
                     (s_count st (s_len st) - 1) (s_len st)) 0) eqn:Hhit;
    cbn [andb] in Hstep;
    [| exfalso;
       repeat match type of Hstep with
              | (if ?b then _ else _) = _ => destruct b
              end;
       discriminate Hstep ].
  destruct (Z.eqb (s_len st) (x_max c)) eqn:Hmxeq; cbn [andb] in Hstep;
    [| exfalso;
       repeat match type of Hstep with
              | (if ?b then _ else _) = _ => destruct b
              end;
       discriminate Hstep ].
  injection Hstep as Hst1. subst st1.
  unfold it_finish.
  cbn [s_huff s_next s_len s_drop s_tbl].
  destruct (Z.eqb (it_rev_incr (s_huff st) (s_len st)) 0).
  - exact Hfillamb.
  - intro j. apply amb_tset; [exact Hfillamb|].
    apply AmbE_marker.
    destruct Hphase as [(Hd & _ & _ & _ & Hlr) | (Hd & Hrl & _)];
      rewrite Hd; lia.
Qed.

(** through the loop *)
Lemma amb_loop : forall n ty c cnt0 st r,
  ty = x_type c ->
  (x_type c = CT_LENS \/ x_type c = CT_DISTS \/ x_max c <= x_root c) ->
  0 < x_codes c ->
  (forall st', LeafShape ty (it_here c st')) ->
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  (forall j, AmbE (s_tbl st j)) ->
  it_loop n c st = Some r ->
  match r with
  | ItBreak st1 => forall j, AmbE (it_finish st1 j)
  | ItOverflow t => forall j, AmbE (t j)
  | ItCont _ => True
  end.
Proof.
  induction n as [|n IH]; intros ty c cnt0 st r Hcty Hty3 Hcod Hhere Hctx
                                 Hinv Hled Hamb Hl;
    cbn [it_loop] in Hl; [discriminate Hl|].
  destruct (it_step c st) as [st'|st'|t'] eqn:Hs.
  - pose proof (amb_step ty c cnt0 st Hcty Hty3 Hcod Hctx Hinv Hled
                  (Hhere st) Hamb) as HA.
    rewrite Hs in HA.
    exact (IH ty c cnt0 st' r Hcty Hty3 Hcod Hhere Hctx
             (cov_step_cont c cnt0 st st' Hctx Hinv Hs)
             (ledger_step_cont ty c cnt0 st st'
                Hcty Hty3 Hctx Hinv Hled (Hhere st) Hs)
             HA Hl).
  - injection Hl as <-.
    exact (amb_break_finish ty c cnt0 st st' Hcty Hctx Hinv (Hhere st)
             Hamb Hs).
  - injection Hl as <-.
    pose proof (amb_step ty c cnt0 st Hcty Hty3 Hcod Hctx Hinv Hled
                  (Hhere st) Hamb) as HA.
    rewrite Hs in HA. exact HA.
Qed.

(** the CODES call's [match] parameter *)
Lemma it_pre_go_codes_match : forall lens codes root0 t0 c st,
  it_pre CT_CODES lens codes root0 t0 = PreGo c st ->
  x_match c = 20.
Proof.
  intros lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete CT_CODES lft _); [discriminate H|].
  destruct (it_enough CT_CODES _); [discriminate H|].
  injection H as Hc _. rewrite <- Hc. cbn [x_match].
  vm_compute (Z.eqb CT_CODES CT_LENS).
  vm_compute (Z.eqb CT_CODES CT_DISTS).
  reflexivity.
Qed.

Lemma it_pre_go_codesf : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_codes c = codes.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  injection H as Hc _. rewrite <- Hc. cbn [x_codes]. reflexivity.
Qed.

(** the root and max fields, in their construction shapes *)
Lemma it_pre_go_rootmax : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_max c = it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)
  /\ x_root c
     = (let mx := it_findmax 15%nat MAXBITS
                    (it_count (Z.to_nat codes) 0 lens zzero) in
        let r1 := if Z.ltb mx root0 then mx else root0 in
        let mn := it_findmin 16%nat 1 mx
                    (it_count (Z.to_nat codes) 0 lens zzero) in
        if Z.ltb r1 mn then mn else r1).
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  injection H as Hc _. rewrite <- Hc. cbn [x_root x_max].
  split; reflexivity.
Qed.

(** ** THE ENDPOINT: [dyn_amb_wb]'s content, with the CODES guard *)

Theorem it_model_amb : forall ty lens codes root0 cs k o,
  amb_ok cs ->
  it_wf ty lens codes root0 ->
  (ty = CT_CODES -> forall i, 0 <= i < codes -> lens i <= root0) ->
  it_model ty lens codes root0 (fun i => cs (k + i)) = Some o ->
  amb_ok (codes_wb cs k (o_tbl o)).
Proof.
  intros ty lens codes root0 cs k o Hamb Hwf Hguard Hmodel.
  rewrite amb_ok_iff in Hamb.
  rewrite amb_ok_iff.
  assert (Ht0 : forall j, AmbE ((fun i => cs (k + i)) j))
    by (intro j; apply Hamb).
  assert (Hwb : forall t, (forall j, AmbE (t j)) ->
            forall i, AmbE (codes_wb cs k t i)).
  { intros t Htt i. unfold codes_wb.
    destruct (Z.leb k i); [apply Htt | apply Hamb]. }
  destruct Hwf as (Hc0 & Hlens & Hroot0 & Hkinds).
  assert (Hcodes : 0 <= codes) by lia.
  unfold it_model in Hmodel.
  destruct (it_pre ty lens codes root0 (fun i => cs (k + i)))
    as [ | temp | | c st] eqn:Hpre.
  - injection Hmodel as <-. cbn [o_tbl]. exact (Hwb _ Ht0).
  - rewrite (it_pre_empty_shape _ _ _ _ _ _ Hpre) in Hmodel.
    injection Hmodel as <-. cbn [o_tbl].
    apply Hwb. intro j.
    apply amb_tset; [apply amb_tset; [exact Ht0|]|]; apply AmbE_marker; lia.
  - injection Hmodel as <-. cbn [o_tbl]. exact (Hwb _ Ht0).
  - destruct (cov_pre ty lens codes root0 (fun i => cs (k + i)) c st
                Hcodes Hlens Hroot0 Hpre) as [Hctx Hinv].
    pose proof (ledger_pre ty lens codes root0 (fun i => cs (k + i)) c st
                  Hcodes Hlens Hroot0 Hpre) as Hled.
    assert (Hcty : ty = x_type c)
      by (symmetry; exact (it_pre_go_type ty lens codes root0 _ c st Hpre)).
    pose proof (it_pre_go_codesf ty lens codes root0 _ c st Hpre) as Hcodc.
    assert (Hcod : 0 < x_codes c) by lia.
    assert (Hamb0 : forall j, AmbE (s_tbl st j))
      by (rewrite (it_pre_go_tbl ty lens codes root0 _ c st Hpre);
          exact Ht0).
    pose proof (it_pre_go_work ty lens codes root0 _ c st Hpre) as Hwk.
    assert (Hwr : forall s, 0 <= x_work c s < codes)
      by (intro s; rewrite Hwk; apply sort_work_range; lia).
    assert (Hty3 : x_type c = CT_LENS \/ x_type c = CT_DISTS
                   \/ x_max c <= x_root c).
    { destruct Hkinds as [(Hk & Hcap)|[(Hk & Hcap)|(Hk & Hcap)]];
        [right; right | left; rewrite <- Hcty; exact Hk
        | right; left; rewrite <- Hcty; exact Hk].
      (* CODES: the guard forces every length under root0, so max <= root *)
      specialize (Hguard Hk).
      destruct (it_pre_go_rootmax ty lens codes root0 _ c st Hpre)
        as [Hmxf Hrootf].
      pose proof Hctx as (Hroot & _ & Hmx & Hmxnz & Hmxz & Hnn & _ & _
                          & Hcnt0 & _ & _ & _ & Hrootmx).
      (* the max length is realised by a live symbol *)
      assert (Hex : exists j, 0 <= j < codes /\ lens j = x_max c).
      { assert (Hnz : sw_cnt lens codes (x_max c) <> 0) by exact Hmxnz.
        unfold sw_cnt in Hnz.
        rewrite it_count_spec in Hnz. unfold zzero, zconst in Hnz.
        assert (Hp : 0 < zcount (Z.to_nat codes) 0 lens (x_max c)).
        { pose proof (zcount_nonneg (Z.to_nat codes) 0 lens (x_max c)).
          lia. }
        destruct (zcount_pos_ex _ _ _ _ Hp) as [j [Hj Hl]].
        exists j. split; [lia | exact Hl]. }
      destruct Hex as [j [Hj Hlj]].
      assert (Hmxr0 : x_max c <= root0)
        by (rewrite <- Hlj; apply Hguard; exact Hj).
      rewrite Hmxf in Hmxr0 |- *. rewrite Hrootf.
      cbv zeta.
      apply clamp_ge. exact Hmxr0. }
    assert (Hhere : forall st', LeafShape ty (it_here c st')).
    { intros st'.
      destruct Hkinds as [(Hk & Hcap)|[(Hk & Hcap)|(Hk & Hcap)]].
      - subst ty.
        apply (here_leafshape_codes c st'
                 (it_pre_go_codes_match lens codes root0 _ c st Hpre)).
        intro s. pose proof (Hwr s). lia.
      - subst ty.
        destruct (it_pre_go_lens_arrays lens codes root0 _ c st Hpre)
          as (Hm & Hb & He).
        apply (here_leafshape_lens c st' Hm Hb He).
        intro s. pose proof (Hwr s). lia.
      - subst ty.
        destruct (it_pre_go_dists lens codes root0 _ c st Hpre)
          as (Hm & Hb & He).
        apply (here_leafshape_dists c st' Hm Hb He).
        intro s. pose proof (Hwr s). lia. }
    destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:Hloop;
      [|discriminate Hmodel].
    pose proof (amb_loop (S (Z.to_nat codes)) ty c (sw_cnt lens codes) st r
                  Hcty Hty3 Hcod Hhere Hctx Hinv Hled Hamb0 Hloop) as HA.
    destruct r as [st'|st'|tt].
    + discriminate Hmodel.
    + injection Hmodel as <-. cbn [o_tbl]. exact (Hwb _ HA).
    + injection Hmodel as <-. cbn [o_tbl]. exact (Hwb _ HA).
Qed.

Print Assumptions amb_step.
Print Assumptions amb_break_finish.
Print Assumptions it_model_amb.
