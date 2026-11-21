(** * ItGMarkersPop — the population corollary: a marker in the root
    window pins the count histogram to EXACTLY ONE 1-bit code.

    OWNER: an earlier development run.  This is g1's population obligation from the round's
    division of labor (residue table-read = q4's; i=1 + population = mine).
    The separator complete-vs-max1 is NOT derivable at the output level
    (both worlds have o_bits=1, o_used=2), so it comes from CovCtxOk's
    acceptance dichotomy, THREADED through the walk: sibling duplicates of
    [nom_break_endgame]/[nom_loop] from ItGMarkers.v ( — the
    chair-passed file, NOT touched) with the dichotomy selection
    [x_max c = 1 /\ it_mass = 2^14] added to the conclusion.  The complete
    arm was already exfalso under a marker; the max1 arm has both facts in
    scope — the strengthening costs two [split; [exact _|]] lines.

    Proof bodies otherwise VERBATIM from the adopted bed.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblGeom ItGTblCover ItGSubCover ItGTblRev ItGTblLeafPos
  ItGAmb.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6K.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGMarkers.
Import ItGMarkers.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Huff InftreesBridge ItGTblSortWin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGPfWin.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Lemma nom_break_endgame_pop : forall c cnt0 st st1,
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  c_op (it_here c st) <> 64 ->
  NoM64 c (it_mass 15%nat 1 cnt0) st ->
  (s_drop st = 0 -> s_used st = 2 ^ x_root c) ->
  it_step c st = ItBreak st1 ->
  forall j, 0 <= j < 2 ^ x_root c ->
  c_op (it_finish st1 j) = 64 ->
  x_root c = 1 /\ x_max c = 1 /\ it_mass 15%nat 1 cnt0 = 2 ^ 14
  /\ s_used st1 = 2 /\ it_finish st1 j = mkCodeT 64 1 0.
Proof.
  intros c cnt0 st st1 Hctx Hinv Hh64 HS Hused0 Hstep j Hj.
  pose proof (nom_fill_census c cnt0 st Hctx Hinv Hh64 HS) as Hfillc.
  destruct HS as [Hcen Hlow64].
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  unfold it_step in Hstep. cbv zeta in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1))
    in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  destruct (Z.eqb (cnt1 (s_len st)) 0) eqn:Hhit; cbn [andb] in Hstep;
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
  apply Z.eqb_eq in Hhit. apply Z.eqb_eq in Hmxeq.
  (* the counts, and hence the mass, are exhausted *)
  assert (Hcnt1 : forall l, 1 <= l <= 15 -> cnt1 l = 0).
  { intros l Hl. unfold cnt1, zset.
    destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
    - unfold cnt1, zset in Hhit. rewrite Z.eqb_refl in Hhit. exact Hhit.
    - rewrite (Hcnt l Hl).
      destruct (Z.ltb_spec l (s_len st)) as [H1|H1]; [reflexivity|].
      destruct (Z.eqb_spec l (s_len st)) as [H2|H2]; [contradiction|].
      apply Hmxz. lia. }
  assert (Hmass0 : it_mass 15%nat 1 cnt1 = 0)
    by (apply it_mass_zero_on; intros i Hi; apply Hcnt1; cbn in Hi; lia).
  assert (Hposbrk : Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
                    = it_mass 15%nat 1 cnt0).
  { unfold Pos in *. rewrite <- (pos_advance (it_mass 15%nat 1 cnt0)
                                  (s_count st) (s_len st) ltac:(lia)).
    unfold cnt1 in Hmass0. rewrite Hmass0. ring. }
  rewrite Hposbrk in Hfillc.
  injection Hstep as Hst1. subst st1.
  assert (Hhuff' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
    by (rewrite (to_nat_pow (s_len st) ltac:(lia)); exact Hhuff).
  pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st)
                ltac:(lia) Hhuff') as Hinc.
  rewrite (Z2Nat.id (s_len st)) in Hinc by lia.
  unfold it_finish.
  cbn [s_huff s_next s_len s_drop s_low s_used s_tbl].
  destruct Hcase as [Hfull | [Hmx1 Hhalf]].
  - (* COMPLETE: the census reaches the whole table; no marker survives *)
    intros H64. exfalso.
    destruct (Z.eqb huff1 0) eqn:Hz.
    + (* wrapped: the finish is the bare fill, and the census covers cell j *)
      cbv beta iota in H64.
      unshelve epose proof (Hfillc j Hj _) as Hq.
      { rewrite Hfull.
        pose proof (zrev_lt (Z.to_nat (x_root c)) j) as Hltj.
        rewrite (to_nat_pow (x_root c) ltac:(lia)) in Hltj.
        pose proof (pow2_pos_z (15 - x_root c) ltac:(lia)).
        assert (Hsplit : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        pose proof (zrev_nonneg (Z.to_nat (x_root c)) j). nia. }
      replace (0 + j) with j in Hq by lia.
      exact (Hq H64).
    + (* no wrap is impossible at a complete break *)
      apply Z.eqb_neq in Hz.
      destruct Hinc as [[Hw _] | [Hr Ha]]; [exact (Hz Hw)|].
      pose proof (zrev_lt (Z.to_nat (s_len st)) huff1) as Hlt1.
      rewrite (to_nat_pow (s_len st) ltac:(lia)) in Hlt1.
      pose proof (pow2_pos_z (15 - s_len st) ltac:(lia)).
      assert (Hsplit : 2 ^ s_len st * 2 ^ (15 - s_len st) = 2 ^ 15)
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      rewrite Hpos, Hfull in Hposbrk.
      pose proof (zrev_nonneg (Z.to_nat (s_len st)) (s_huff st)).
      (* nia cannot witness the division step; hand it the strict
         product inequality explicitly (mul-mono at B > 0). *)
      assert (Hstrict : zrev (Z.to_nat (s_len st)) huff1
                          * 2 ^ (15 - s_len st)
                        < 2 ^ s_len st * 2 ^ (15 - s_len st))
        by (apply Z.mul_lt_mono_pos_r; lia).
      (* nia also cannot multiply Ha by the variable factor B, and Ha is
         spelled with [it_rev_incr ...] while Hstrict speaks of [huff1];
         bridge both by hand, then the contradiction is linear. *)
      assert (Hradv : zrev (Z.to_nat (s_len st)) huff1 * 2 ^ (15 - s_len st)
                      = zrev (Z.to_nat (s_len st)) (s_huff st)
                          * 2 ^ (15 - s_len st)
                        + 2 ^ (15 - s_len st))
        by (unfold huff1; rewrite Ha; ring).
      lia.
  - (* INCOMPLETE-BUT-ACCEPTED: max = 1 forces root = 1; the fix-up marker
       at index 1 is the ONLY 64 in the two-cell window *)
    assert (Hr1 : x_root c = 1) by lia.
    assert (Hl1 : s_len st = 1) by lia.
    destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & _)];
      [|exfalso; lia].
    pose proof (Hused0 Hd) as Husedv.
    (* the loop stopped at position 0: the single unit is the whole mass *)
    assert (Hposzero : Pos (it_mass 15%nat 1 cnt0) st = 0).
    { rewrite Hl1 in Hposbrk.
      replace (15 - 1) with 14 in Hposbrk by lia. lia. }
    assert (Hzh : zrev (Z.to_nat (s_len st)) (s_huff st) = 0).
    { rewrite Hpos in Hposzero.
      pose proof (pow2_pos_z (15 - s_len st) ltac:(lia)).
      pose proof (zrev_nonneg (Z.to_nat (s_len st)) (s_huff st)). nia. }
    assert (Hadv : zrev (Z.to_nat (s_len st)) huff1
                   = zrev (Z.to_nat (s_len st)) (s_huff st) + 1
                   /\ 0 <= huff1 < 2 ^ s_len st).
    { destruct Hinc as [[Hw Hz1] | [Hr Ha]]; [exfalso | tauto].
      rewrite Hzh in Hz1. rewrite Hl1 in Hz1.
      change (2 ^ 1) with 2 in Hz1. lia. }
    destruct Hadv as [Hadv Hrange].
    assert (Hhuff1 : huff1 = 1).
    { apply (zrev_inj (Z.to_nat (s_len st))).
      - rewrite (to_nat_pow (s_len st) ltac:(lia)). lia.
      - rewrite (to_nat_pow (s_len st) ltac:(lia)), Hl1.
        change (2 ^ 1) with 2. lia.
      - rewrite Hadv, Hzh, Hl1. change (Z.to_nat 1) with 1%nat.
        rewrite (zrev_one 0). reflexivity. }
    intros H64.
    destruct (Z.eqb huff1 0) eqn:Hz;
      [exfalso; apply Z.eqb_eq in Hz; lia|].
    cbv beta iota in H64.
    (* normalise ONLY the tset index and the marker payload: the fill term
       must stay syntactically shared with the census in [Hfillc] *)
    replace (s_next st + huff1) with 1 in H64 |- * by lia.
    replace (mkCodeT 64 (s_len st - s_drop st) 0) with (mkCodeT 64 1 0)
      in H64 |- * by (f_equal; lia).
    split; [exact Hr1|].
    split; [exact Hmx1|].
    split; [exact Hhalf|].
    split.
    { rewrite Husedv, Hr1. reflexivity. }
    destruct (Z.eq_dec j 1) as [->|Hne].
    + rewrite tset_same. reflexivity.
    + exfalso.
      assert (Hj0 : j = 0).
      { rewrite Hr1 in Hj. change (2 ^ 1) with 2 in Hj. lia. }
      subst j.
      rewrite tset_other in H64 by lia.
      (* the census covers cell 0: its one unit is the whole half-mass *)
      unshelve epose proof
        (Hfillc 0 ltac:(rewrite Hr1; change ((2:Z) ^ 1) with 2; lia) _)
        as Hq.
      { rewrite Hhalf, Hr1.
        change (Z.to_nat 1) with 1%nat. rewrite zrev_zero.
        replace (15 - 1) with 14 by lia. lia. }
      replace (0 + 0) with 0 in Hq by lia.
      exact (Hq H64).
Qed.

Lemma nom_loop_pop : forall n ty c cnt0 st st1,
  ty = x_type c ->
  (x_type c = CT_LENS \/ x_type c = CT_DISTS \/ x_max c <= x_root c) ->
  (forall st', LeafShape ty (it_here c st')) ->
  (forall st', c_op (it_here c st') <> 64) ->
  0 < x_codes c ->
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  NoM64 c (it_mass 15%nat 1 cnt0) st ->
  it_loop n c st = Some (ItBreak st1) ->
  forall j, 0 <= j < 2 ^ x_root c ->
  c_op (it_finish st1 j) = 64 ->
  x_root c = 1 /\ x_max c = 1 /\ it_mass 15%nat 1 cnt0 = 2 ^ 14
  /\ s_used st1 = 2 /\ it_finish st1 j = mkCodeT 64 1 0.
Proof.
  induction n as [|n IH]; intros ty c cnt0 st st1 Hcty Hty Hhere Hh64 Hcpos
                                 Hctx Hinv Hled HS Hl;
    cbn [it_loop] in Hl; [discriminate Hl|].
  destruct (it_step c st) as [st'|st'|t'] eqn:Hs.
  - exact (IH ty c cnt0 st' st1 Hcty Hty Hhere Hh64 Hcpos Hctx
             (cov_step_cont c cnt0 st st' Hctx Hinv Hs)
             (ledger_step_cont ty c cnt0 st st' Hcty Hty Hctx Hinv Hled
                (Hhere st) Hs)
             (nom_step_cont c cnt0 st st' Hcpos Hctx Hinv (Hh64 st) HS Hs)
             Hl).
  - injection Hl as <-.
    apply (nom_break_endgame_pop c cnt0 st st' Hctx Hinv (Hh64 st) HS);
      [|exact Hs].
    (* the used-fact, from the ledger's phase-1 arm *)
    intros Hd0.
    destruct Hled as [Hroote Hphl].
    destruct Hphl as [(H1 & H2 & H3) | (H2 & _)]; [exact H2|].
    exfalso. destruct Hctx as (Hroot & _). lia.
  - discriminate Hl.
Qed.

(** it_mass at a one-bit histogram is just the count of 1-bit codes,
    scaled. *)
Lemma it_mass_mx1 : forall cnt : zarr,
  (forall l, 2 <= l <= 15 -> cnt l = 0) ->
  it_mass 15%nat 1 cnt = cnt 1 * 2 ^ 14.
Proof.
  intros cnt H. cbn.
  rewrite (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)),
          (H 5 ltac:(lia)), (H 6 ltac:(lia)), (H 7 ltac:(lia)),
          (H 8 ltac:(lia)), (H 9 ltac:(lia)), (H 10 ltac:(lia)),
          (H 11 ltac:(lia)), (H 12 ltac:(lia)), (H 13 ltac:(lia)),
          (H 14 ltac:(lia)), (H 15 ltac:(lia)).
  ring.
Qed.

(** The driver, array level: PreGo + accepted + a marker anywhere in the
    root window forces the one-code histogram. *)
Theorem marker_population_counts : forall ty lens codes root0 t0 c st out,
  (ty = CT_LENS \/ ty = CT_DISTS) ->
  (ty = CT_DISTS -> codes <= 30) ->
  it_wf ty lens codes root0 ->
  it_pre ty lens codes root0 t0 = PreGo c st ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  (exists i, 0 <= i < 2 ^ (o_bits out) /\ c_op (o_tbl out i) = 64) ->
  sw_cnt lens codes 1 = 1
  /\ (forall l, 2 <= l <= 15 -> sw_cnt lens codes l = 0).
Proof.
  intros ty lens codes root0 t0 c st out Hty Hd30 Hwf Hpre Hmodel Hret Hmark.
  destruct Hwf as (Hc0 & Hlens & Hroot0 & Hkinds).
  assert (Hcodes : 0 <= codes) by lia.
  unfold it_model in Hmodel. rewrite Hpre in Hmodel.
  cbv beta iota in Hmodel.
  destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
    as [Hctx Hinv].
  pose proof (ledger_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0
                Hpre) as Hled.
  assert (Hcty : ty = x_type c)
    by (symmetry; exact (it_pre_go_type ty lens codes root0 t0 c st Hpre)).
  assert (Htyc : x_type c = CT_LENS \/ x_type c = CT_DISTS
                 \/ x_max c <= x_root c)
    by (rewrite <- Hcty; destruct Hty as [?|?]; [left|right; left];
        assumption).
  assert (Hcx : x_codes c = codes)
    by (exact (it_pre_go_codesf ty lens codes root0 t0 c st Hpre)).
  assert (Hcpos : 0 < x_codes c) by lia.
  assert (Hhere : forall st', LeafShape ty (it_here c st')).
  { intros st'.
    pose proof (it_pre_go_work ty lens codes root0 t0 c st Hpre) as Hwk.
    assert (Hwr : forall s, 0 <= x_work c s < codes)
      by (intros s; rewrite Hwk; apply sort_work_range; lia).
    destruct Hty as [HL|HD].
    - subst ty.
      destruct (it_pre_go_lens_arrays lens codes root0 t0 c st Hpre)
        as (Hm & Hb & He).
      apply (here_leafshape_lens c st' Hm Hb He).
      intros s. pose proof (Hwr s).
      destruct Hkinds as [(Hk & Hcap)|[(Hk & Hcap)|(Hk & Hcap)]];
        try (exfalso; vm_compute in Hk; discriminate Hk).
      lia.
    - subst ty.
      destruct (it_pre_go_dists lens codes root0 t0 c st Hpre)
        as (Hm & Hb & He).
      apply (here_leafshape_dists c st' Hm Hb He).
      intros s. pose proof (Hwr s).
      destruct Hkinds as [(Hk & Hcap)|[(Hk & Hcap)|(Hk & Hcap)]];
        try (exfalso; vm_compute in Hk; discriminate Hk).
      lia. }
  assert (Hh64 : forall st', c_op (it_here c st') <> 64).
  { intros st'.
    pose proof (it_pre_go_work ty lens codes root0 t0 c st Hpre) as Hwk.
    assert (Hwr : forall s, 0 <= x_work c s < codes)
      by (intros s; rewrite Hwk; apply sort_work_range; lia).
    rewrite it_here_entry.
    destruct Hty as [HL|HD].
    - subst ty.
      destruct (it_pre_go_lens_arrays lens codes root0 t0 c st Hpre)
        as (Hm & Hb & He).
      apply (it_entry_op_not64_lens c _ _ Hm He).
      pose proof (Hwr (s_sym st')).
      destruct Hkinds as [(Hk & Hcap)|[(Hk & Hcap)|(Hk & Hcap)]];
        try (exfalso; vm_compute in Hk; discriminate Hk).
      lia.
    - subst ty.
      destruct (it_pre_go_dists lens codes root0 t0 c st Hpre)
        as (Hm & Hb & He).
      apply (it_entry_op_not64_dists c _ _ Hm He).
      pose proof (Hwr (s_sym st')).
      specialize (Hd30 eq_refl).
      lia. }
  assert (HS0 : NoM64 c (it_mass 15%nat 1 (PngModel.ItGTblSortWin.sw_cnt lens codes)) st).
  { pose proof (it_pre_go_count ty lens codes root0 t0 c st Hpre) as Hcnt.
    destruct (it_pre_go_shape ty lens codes root0 t0 c st Hpre)
      as [Hd0 Hn0].
    split.
    - intros k Hk Hu. exfalso.
      unfold Pos in Hu. rewrite Hcnt in Hu.
      pose proof (zrev_nonneg (Z.to_nat (x_root c)) k).
      pose proof Hctx as Hctx'. destruct Hctx' as (Hroot & _).
      pose proof (pow2_pos_z (15 - x_root c) ltac:(lia)).
      assert (Hprod : 0 < (zrev (Z.to_nat (x_root c)) k + 1)
                          * 2 ^ (15 - x_root c))
        by (apply Z.mul_pos_pos; lia).
      clear -Hu Hprod. lia.
    - intros Hdr. exfalso.
      pose proof Hctx as Hctx'. destruct Hctx' as (Hroot & _). lia. }
  destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hloop;
    try discriminate Hmodel.
  - (* ItBreak: the accepted build *)
    injection Hmodel as <-. cbn [o_bits o_used o_tbl] in Hmark.
    destruct Hmark as (i & Hi & H64).
    destruct (nom_loop_pop (S (Z.to_nat codes)) ty c
                (PngModel.ItGTblSortWin.sw_cnt lens codes) st st'
                Hcty Htyc Hhere Hh64 Hcpos Hctx Hinv Hled HS0 Hloop i Hi H64)
      as (Hr1 & Hmx1 & Hhalf & _ & _).
    (* the dichotomy's right arm, transported to the histogram *)
    pose proof Hctx as Hctx'.
    destruct Hctx' as (_ & _ & _ & _ & Hmxz & _).
    assert (Hz2 : forall l, 2 <= l <= 15 -> sw_cnt lens codes l = 0)
      by (intros l Hl; apply Hmxz; lia).
    split; [|exact Hz2].
    rewrite (it_mass_mx1 _ Hz2) in Hhalf. lia.
  - (* ItOverflow: rejected *)
    injection Hmodel as <-. cbn in Hret. lia.
Qed.

(** The window corollary, list level: what the B3 assemblies consume. *)
Corollary marker_population_counts_win :
  forall ty (l1 l2 : list nat) root0 t0 c st out,
    (ty = CT_LENS \/ ty = CT_DISTS) ->
    (ty = CT_DISTS -> Z.of_nat (length l1) <= 30) ->
    it_wf ty (zlens (l1 ++ l2)) (Z.of_nat (length l1)) root0 ->
    it_pre ty (zlens (l1 ++ l2)) (Z.of_nat (length l1)) root0 t0
      = PreGo c st ->
    it_model ty (zlens (l1 ++ l2)) (Z.of_nat (length l1)) root0 t0
      = Some out ->
    o_ret out = 0 ->
    (exists i, 0 <= i < 2 ^ (o_bits out) /\ c_op (o_tbl out i) = 64) ->
    count_len l1 1%nat = 1%nat
    /\ (forall l : nat, (2 <= l <= 15)%nat -> count_len l1 l = 0%nat).
Proof.
  intros ty l1 l2 root0 t0 c st out Hty Hd30 Hwf Hpre Hmodel Hret Hmark.
  destruct (marker_population_counts ty (zlens (l1 ++ l2))
              (Z.of_nat (length l1)) root0 t0 c st out Hty Hd30 Hwf Hpre
              Hmodel Hret Hmark) as [H1 Hz2].
  assert (HC : CountsOf (it_cnt0 (zlens (l1 ++ l2)) (Z.of_nat (length l1)))
                 l1 15%nat).
  { apply (counts_of_it_count_agree _ _ l1 15%nat eq_refl).
    apply zlens_app_window. }
  assert (Htie : it_cnt0 (zlens (l1 ++ l2)) (Z.of_nat (length l1))
                 = sw_cnt (zlens (l1 ++ l2)) (Z.of_nat (length l1)))
    by reflexivity.
  split.
  - pose proof (HC 1%nat ltac:(lia)) as Hb.
    rewrite Htie in Hb. change (Z.of_nat 1%nat) with 1 in Hb.
    rewrite H1 in Hb. lia.
  - intros l Hl.
    pose proof (HC l ltac:(lia)) as Hb.
    rewrite Htie in Hb.
    rewrite (Hz2 (Z.of_nat l) ltac:(lia)) in Hb. lia.
Qed.

Set Printing Width 2000.
Print Assumptions nom_break_endgame_pop.
Print Assumptions nom_loop_pop.
Print Assumptions it_mass_mx1.
Print Assumptions marker_population_counts.
Print Assumptions marker_population_counts_win.

