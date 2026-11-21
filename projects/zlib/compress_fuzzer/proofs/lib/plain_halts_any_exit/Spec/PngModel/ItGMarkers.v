(** * ItGMarkers — B3 support: the marker population of accepted builds.

    OWNER: an earlier development run (dyn round Leg B3; freeze v4 75426016 working text v3).
    Three facts the zr_two_own-v3 inhabitation needs about MARKERS
    (entries [mkCodeT 64 1 0], written ONLY by [it_pre]'s PreEmpty pair
    and [it_finish]'s incomplete fixup — the two-writer census):

    - [marker_population]: an accepted build carries a root marker only
      in the PreEmpty or max==1 populations (elsewhere [it_finish] is a
      no-op because complete codes end with [s_huff = 0]).
    - [no_child_markers]: no accepted build has a marker in the
      sub-table region [2^root, used) — incompleteness forces max==1
      which forces root=1 and no sub-table; complete codes fill
      kraft-exactly.
    - [width_covers] ([P1]): the builder's [it_subsz] sizing covers the
      class — every codeword whose root prefix spells i fits in
      root + op at the pointer i.

    This file starts with EXECUTION ANCHORS (vm-checked shapes of the two
    marker-producing witness families) so the walk lemmas' statements are
    grounded before the inductions land.

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

(* ==========================================================================
   1.  Execution anchors: the two marker-producing populations, computed.
   ========================================================================== *)

(** The one-distance-code table (B1's witness family): accepted, root 1,
    coded entry at slot 0, THE EXACT MARKER at slot 1. *)
Example anchor_dists_one :
  match it_model CT_DISTS (zlens [1%nat]) 1 6 tnone with
  | Some out =>
      (o_ret out =? 0) && (o_bits out =? 1) && (o_used out =? 2)
      && (c_op (o_tbl out 1) =? 64) && (c_bits (o_tbl out 1) =? 1)
      && (c_val (o_tbl out 1) =? 0)
      && negb (c_op (o_tbl out 0) =? 64)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** The EOB-only LENS table (q6's C1 witness): accepted (lens 256 <> 0
    passes the machine's NO-EOB check upstream), table [96,1,0; 64,1,0]. *)
Example anchor_lens_eob_only :
  match it_model CT_LENS (fun i => if i =? 256 then 1 else 0) 257 9 tnone with
  | Some out =>
      (o_ret out =? 0) && (o_bits out =? 1) && (o_used out =? 2)
      && (c_op (o_tbl out 0) =? 96)
      && (c_op (o_tbl out 1) =? 64) && (c_bits (o_tbl out 1) =? 1)
      && (c_val (o_tbl out 1) =? 0)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** A COMPLETE two-code build carries NO marker anywhere in [0, used):
    the no-child/no-root-marker claim's smallest positive anchor. *)
Example anchor_complete_two :
  match it_model CT_DISTS (zlens [1;1]%nat) 2 6 tnone with
  | Some out =>
      (o_ret out =? 0)
      && (Z.eqb (o_used out) 2)
      && negb (c_op (o_tbl out 0) =? 64)
      && negb (c_op (o_tbl out 1) =? 64)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions anchor_dists_one.
Print Assumptions anchor_lens_eob_only.
Print Assumptions anchor_complete_two.

(* ==========================================================================
   2.  The fill never writes the exact marker record: op-enumeration.

       [it_entry]'s three arms give op in {0} u {x_extra values} u {96}.
       LENS: every lext value (junk 203/77 included) differs from
       64-EXACT, so no population premise is needed for THIS fact.
       DISTS: dext[30] = dext[31] = 64 — the boundary q6's gate-2
       measured; the population bound (ndist <= 30 => work <= 29) is the
       truth condition, carried as the j-range premise.
   ========================================================================== *)

Lemma lext_not64_table :
  forallb (fun j => negb (lext (Z.of_nat j) =? 64)) (seq 0 31) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dext_not64_table :
  forallb (fun j => negb (dext (Z.of_nat j) =? 64)) (seq 0 30) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lext_not64 : forall j, 0 <= j <= 30 -> lext j <> 64.
Proof.
  intros j Hj.
  pose proof (table_fact _ 31%nat j lext_not64_table ltac:(lia)) as H.
  cbn beta in H. rewrite Z2Nat.id in H by lia.
  apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma dext_not64 : forall j, 0 <= j <= 29 -> dext j <> 64.
Proof.
  intros j Hj.
  pose proof (table_fact _ 30%nat j dext_not64_table ltac:(lia)) as H.
  cbn beta in H. rewrite Z2Nat.id in H by lia.
  apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

(** The builder's entry is never op-64-exact — LENS at the full work
    range, DISTS at the population range. *)
Lemma it_entry_op_not64_lens : forall c w b,
  x_match c = 257 -> x_extra c = lext ->
  0 <= w <= 287 ->
  c_op (ZReproQ6K.it_entry c w b) <> 64.
Proof.
  intros c w b Hm He Hw.
  unfold ZReproQ6K.it_entry. rewrite Hm, He.
  destruct (Z.ltb (w + 1) 257).
  - rewrite op_mkCodeT_id by lia. lia.
  - destruct (Z.leb 257 w) eqn:H2.
    + apply Z.leb_le in H2.
      pose proof (lext_not64 (w - 257) ltac:(lia)) as Hn.
      pose proof (proj1 (leaf_opb_sound CT_LENS (lext (w - 257))
                    (lext_leaf (w - 257) ltac:(lia)))) as _.
      assert (Hrng : 0 <= lext (w - 257) < 256).
      { destruct (leaf_opb_sound CT_LENS (lext (w - 257))
                    (lext_leaf (w - 257) ltac:(lia))) as (_ & _ & _ & Hr).
        exact Hr. }
      rewrite op_mkCodeT_id by lia. exact Hn.
    + rewrite op_mkCodeT_id by lia. lia.
Qed.

Lemma it_entry_op_not64_dists : forall c w b,
  x_match c = 0 -> x_extra c = dext ->
  0 <= w <= 29 ->
  c_op (ZReproQ6K.it_entry c w b) <> 64.
Proof.
  intros c w b Hm He Hw.
  unfold ZReproQ6K.it_entry. rewrite Hm, He.
  destruct (Z.ltb (w + 1) 0) eqn:H1.
  - apply Z.ltb_lt in H1. lia.
  - destruct (Z.leb 0 w) eqn:H2.
    + pose proof (dext_not64 (w - 0) ltac:(lia)) as Hn.
      assert (Hrng : 0 <= dext (w - 0) < 256).
      { destruct (leaf_opb_sound CT_DISTS (dext (w - 0))
                    (dext_leaf (w - 0) ltac:(lia))) as (_ & _ & _ & Hr).
        exact Hr. }
      rewrite op_mkCodeT_id by lia. exact Hn.
    + apply Z.leb_gt in H2. lia.
Qed.

(* ==========================================================================
   3.  The acceptance dichotomy: complete or the one-bit incomplete code.
       [it_incomplete ty lft mx = false] with ty in {LENS, DISTS}
       unfolds to lft <= 0 \/ mx = 1.
   ========================================================================== *)

Lemma accept_complete_or_max1 : forall ty lft mx,
  (ty = CT_LENS \/ ty = CT_DISTS) ->
  it_incomplete ty lft mx = false ->
  lft <= 0 \/ mx = 1.
Proof.
  intros ty lft mx Hty H.
  unfold it_incomplete in H.
  apply andb_false_iff in H.
  destruct H as [H | H].
  - left. apply Z.ltb_ge in H. exact H.
  - right.
    apply orb_false_iff in H. destruct H as [_ H].
    apply negb_false_iff, Z.eqb_eq in H. exact H.
Qed.

Print Assumptions it_entry_op_not64_lens.
Print Assumptions it_entry_op_not64_dists.
Print Assumptions accept_complete_or_max1.

(* ==========================================================================
   4.  The shared S-generic loop carrier (one engine, two ledgers:
       an earlier development run's ownership payload and this file's op-census both
       instantiate S once; the CovInv thread rides the landed
       cov_step_cont so neither walk re-does the loop induction).
   ========================================================================== *)

Lemma cov_loop_side : forall (S : ItSt -> Prop) (c : ItCtx) (cnt0 : zarr),
  CovCtxOk c cnt0 ->
  (forall st st', CovInv c cnt0 st -> S st ->
     it_step c st = ItCont st' -> S st') ->
  (forall st st1, CovInv c cnt0 st -> S st ->
     it_step c st = ItBreak st1 -> S st1) ->
  forall n st st1,
    CovInv c cnt0 st -> S st ->
    it_loop n c st = Some (ItBreak st1) ->
    S st1.
Proof.
  intros S c cnt0 Hctx Hcont Hbrk.
  induction n as [|k IH]; intros st st1 Hinv HS Hloop;
    cbn [it_loop] in Hloop; [discriminate Hloop|].
  destruct (it_step c st) as [st'|st'|t] eqn:Hs.
  - exact (IH st' st1 (cov_step_cont c cnt0 st st' Hctx Hinv Hs)
             (Hcont st st' Hinv HS Hs) Hloop).
  - injection Hloop as <-. exact (Hbrk st _ Hinv HS Hs).
  - discriminate Hloop.
Qed.

Print Assumptions cov_loop_side.

(* ==========================================================================
   5.  The root-window op-census walk (B3 piece 2, root-scoped).

       Payload-swapped shadow of the landed coverage machinery: the census
       [c_op e <> 64] rides [GenBelow] through the loop.  The payload is
       WINDOW-FREE (unlike SubLedger's), so the step lemma needs none of
       the ledger's window bookkeeping: [pos_advance] is the whole
       advancement argument, and CovInv (landed preservation) supplies the
       geometry.  Scope: the ROOT window only — the sub-region census is
       the two-phase ledger mirror, priced separately.
   ========================================================================== *)

Definition NoM64 (c : ItCtx) (M0 : Z) (st : ItSt) : Prop :=
  GenBelow (fun e => c_op e <> 64) (x_root c) 15 (s_tbl st) 0 (Pos M0 st)
  /\ (s_drop st = x_root c -> c_op (s_tbl st (s_low st)) <> 64).

(** [it_subsz] never grows past the lookahead ceiling, and never shrinks. *)
Lemma it_subsz_ge : forall n cnt drop mx curr left,
  curr <= it_subsz n cnt drop mx curr left.
Proof.
  induction n as [|k IH]; intros cnt drop mx curr left; cbn [it_subsz];
    [lia|].
  destruct (Z.ltb (curr + drop) mx); [|lia].
  destruct (Z.leb (left - cnt (curr + drop)) 0); [lia|].
  pose proof (IH cnt drop mx (curr + 1) ((left - cnt (curr + drop)) * 2)).
  lia.
Qed.

Lemma it_subsz_bound : forall n cnt drop mx curr left,
  it_subsz n cnt drop mx curr left <= Z.max curr (mx - drop).
Proof.
  induction n as [|k IH]; intros cnt drop mx curr left; cbn [it_subsz].
  - lia.
  - destruct (Z.ltb_spec (curr + drop) mx) as [Hlt|Hge]; [|lia].
    destruct (Z.leb (left - cnt (curr + drop)) 0); [lia|].
    pose proof (IH cnt drop mx (curr + 1) ((left - cnt (curr + drop)) * 2)).
    lia.
Qed.

(** The trip's fill keeps the root census, advancing it one code's worth. *)
Lemma nom_fill_census : forall c cnt0 st,
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  c_op (it_here c st) <> 64 ->
  NoM64 c (it_mass 15%nat 1 cnt0) st ->
  GenBelow (fun e => c_op e <> 64) (x_root c) 15
    (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                        / Z.shiftl 1 (s_len st - s_drop st)))
             (s_tbl st)
             (s_next st + Z.shiftr (s_huff st) (s_drop st))
             (Z.shiftl 1 (s_len st - s_drop st))
             (it_here c st))
    0
    (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)).
Proof.
  intros c cnt0 st Hctx Hinv Hh64 [Hcen Hlow64].
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes
                    & Hlens & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)].
  - (* phase 1: the fill lands in the root window *)
    rewrite Hd, Hnx, Hc.
    rewrite Z.sub_0_r, Z.shiftr_0_r.
    rewrite !shiftl1 by lia.
    rewrite Hpos.
    apply gen_step_short; [lia | lia | lia | exact Hhuff | exact Hh64 |].
    rewrite <- Hpos. exact Hcen.
  - (* phase 2: the fill misses the root window entirely *)
    rewrite Hpos.
    apply gen_step_long; [lia | lia | lia | lia | exact Hhuff | | | |].
    + (* base + 2^w <= bi *)
      rewrite Hd.
      pose proof (Z.shiftr_nonneg (s_huff st) (x_root c)) as [_ Hs].
      specialize (Hs ltac:(lia)). lia.
    + (* 0 < incr *)
      rewrite shiftl1 by lia. apply pow2_pos_z. lia.
    + rewrite <- Hpos. exact Hcen.
    + (* the low cell already carries the census *)
      replace (0 + s_huff st mod 2 ^ x_root c) with (s_low st) by lia.
      exact (Hlow64 Hd).
Qed.

(** The census survives one fall-through trip. *)
Lemma nom_step_cont : forall c cnt0 st st',
  0 < x_codes c ->
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  c_op (it_here c st) <> 64 ->
  NoM64 c (it_mass 15%nat 1 cnt0) st ->
  it_step c st = ItCont st' ->
  NoM64 c (it_mass 15%nat 1 cnt0) st'.
Proof.
  intros c cnt0 st st' Hcpos Hctx Hinv Hh64 HS Hstep.
  pose proof (nom_fill_census c cnt0 st Hctx Hinv Hh64 HS) as Hfill.
  destruct HS as [Hcen Hlow64].
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes
                    & Hlens & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof Hinv as Hinv2.
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  unfold it_step in Hstep. cbv zeta in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1))
    in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  set (tbl1 := it_fill
                 (Z.to_nat (Z.shiftl 1 (s_curr st)
                            / Z.shiftl 1 (s_len st - s_drop st)))
                 (s_tbl st)
                 (s_next st + Z.shiftr (s_huff st) (s_drop st))
                 (Z.shiftl 1 (s_len st - s_drop st))
                 (it_here c st)) in *.
  assert (HposAdv : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                    = Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)).
  { unfold cnt1. apply pos_advance. lia. }
  (* the new length is still a table length *)
  assert (Hlen1 : forall s, 0 <= x_lens c (x_work c s) <= 15).
  { intros s.
    assert (Hwr : 0 <= x_work c s < x_codes c)
      by (rewrite Hwork; apply sort_work_range; lia).
    apply Hlens. lia. }
  (* the sub-table width at a creation, bounded *)
  assert (Hcurr' : forall L1, 1 <= L1 <= 15 -> x_root c < L1 ->
            1 <= it_subsz 16%nat cnt1 (x_root c) (x_max c)
                   (L1 - x_root c) (Z.shiftl 1 (L1 - x_root c))
            /\ it_subsz 16%nat cnt1 (x_root c) (x_max c)
                 (L1 - x_root c) (Z.shiftl 1 (L1 - x_root c))
               <= 15 - x_root c).
  { intros L1 HL1 Hgt.
    split.
    - pose proof (it_subsz_ge 16%nat cnt1 (x_root c) (x_max c)
                    (L1 - x_root c) (Z.shiftl 1 (L1 - x_root c))). lia.
    - pose proof (it_subsz_bound 16%nat cnt1 (x_root c) (x_max c)
                    (L1 - x_root c) (Z.shiftl 1 (L1 - x_root c))). lia. }
  (* the drop after a creation is always the root *)
  assert (Hdrop' : (if Z.eqb (s_drop st) 0 then x_root c else s_drop st)
                   = x_root c).
  { destruct (Z.eqb_spec (s_drop st) 0) as [He|Hne]; [reflexivity|].
    destruct Hphase as [(Hd & _) | (Hd & _)]; [contradiction | exact Hd]. }
  destruct (Z.eqb (cnt1 (s_len st)) 0) eqn:Hhit; cbn [andb] in Hstep.
  - (* window exhausted *)
    destruct (Z.eqb (s_len st) (x_max c)) eqn:Hmxeq; cbn [andb] in Hstep;
      [discriminate Hstep|].
    cbv beta iota in Hstep.
    rewrite Hdrop' in Hstep.
    destruct (Z.ltb (x_root c) (x_lens c (x_work c (s_sym st + 1))))
      eqn:Hgt; cbn [andb] in Hstep.
    + destruct (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) eqn:Hsame;
        cbn [negb andb] in Hstep; cbv beta iota in Hstep.
      * (* same prefix: plain sub fill *)
        injection Hstep as Hst'. subst st'.
        split.
        { unfold Pos. cbn [s_count s_tbl]. fold (Pos (it_mass 15%nat 1 cnt0) st).
          replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
            with (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
            by (symmetry; exact HposAdv).
          exact Hfill. }
        { cbn [s_drop s_low s_tbl]. intros Hd2.
          destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                             | (Hd & Hrl & Hnx & Hlow & Hlb)];
            [exfalso; lia|].
          unfold tbl1.
          rewrite it_fill_get
            by (rewrite shiftl1 by lia; apply pow2_pos_z; lia).
          assert (Hlowlt : 0 <= s_low st < 2 ^ x_root c)
            by (rewrite Hlow; apply Z.mod_pos_bound; apply pow2_pos_z; lia).
          pose proof (Z.shiftr_nonneg (s_huff st) (s_drop st)) as [_ Hs].
          specialize (Hs ltac:(lia)).
          replace (Z.leb (s_next st + Z.shiftr (s_huff st) (s_drop st))
                     (s_low st)) with false
            by (symmetry; apply Z.leb_gt; lia).
          cbn [andb]. exact (Hlow64 Hd2). }
      * (* new prefix: sub-table creation *)
        (* TEMPLATE INCANTATION (ledger_step_cont's NEW WINDOW arm): fold
           the it_subsz tower behind a variable BEFORE the destruct and
           injection — destructing the raw tower leaves two tower copies
           inside the record, and injection/subst then grind kernel
           conversion on them (measured: ~75 min; the folded form is
           milliseconds). *)
        match type of Hstep with
        | (if it_enough _ (_ + Z.shiftl 1 ?cv) then _ else _) = _ =>
            remember cv as currN eqn:HcurrN
        end.
        match type of Hstep with
        | (if ?b then _ else _) = _ =>
            remember b as enN eqn:HenN; destruct enN
        end; cbv beta iota in Hstep; [discriminate Hstep|].
        injection Hstep as Hst'. subst st'.
        (* v2 of this repair (OOM postmortem): the fold-back rewrite
           reinstated the towers and poisoned every downstream lia
           (1.26GB .lia.cache, OOM-killed group — the opaque-app-hyp
           class). KEEP the fold; convert the helper's bounds TO the
           variable; clear the tower equation before any arithmetic. *)
        destruct (Hcurr' (x_lens c (x_work c (s_sym st + 1)))
                    ltac:(pose proof (Hlen1 (s_sym st + 1));
                          apply Z.ltb_lt in Hgt; lia)
                    ltac:(apply Z.ltb_lt in Hgt; exact Hgt)) as [Hc1 Hc2].
        rewrite <- HcurrN in Hc1, Hc2.
        clear HcurrN HenN.
        split.
        { unfold Pos. cbn [s_count s_tbl]. fold (Pos (it_mass 15%nat 1 cnt0) st).
          replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
            with (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
            by (symmetry; exact HposAdv).
          apply gen_tset; [|exact Hfill].
          rewrite op_mkCodeT_id by lia. lia. }
        { cbn [s_drop s_low s_tbl]. intros _.
          rewrite tset_same.
          rewrite op_mkCodeT_id by lia. lia. }
    + (* no creation: plain *)
      cbv beta iota in Hstep.
      injection Hstep as Hst'. subst st'.
      split.
      { unfold Pos. cbn [s_count s_tbl]. fold (Pos (it_mass 15%nat 1 cnt0) st).
        replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
          with (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
          by (symmetry; exact HposAdv).
        exact Hfill. }
      { cbn [s_drop s_low s_tbl]. intros Hd2.
        destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                           | (Hd & Hrl & Hnx & Hlow & Hlb)];
          [exfalso; lia|].
        unfold tbl1.
        rewrite it_fill_get
          by (rewrite shiftl1 by lia; apply pow2_pos_z; lia).
        assert (Hlowlt : 0 <= s_low st < 2 ^ x_root c)
          by (rewrite Hlow; apply Z.mod_pos_bound; apply pow2_pos_z; lia).
        pose proof (Z.shiftr_nonneg (s_huff st) (s_drop st)) as [_ Hs].
        specialize (Hs ltac:(lia)).
        replace (Z.leb (s_next st + Z.shiftr (s_huff st) (s_drop st))
                   (s_low st)) with false
          by (symmetry; apply Z.leb_gt; lia).
        cbn [andb]. exact (Hlow64 Hd2). }
  - (* window continues: len1 = s_len st *)
    cbv beta iota in Hstep.
    rewrite Hdrop' in Hstep.
    destruct (Z.ltb (x_root c) (s_len st)) eqn:Hgt; cbn [andb] in Hstep.
    + destruct (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) eqn:Hsame;
        cbn [negb andb] in Hstep; cbv beta iota in Hstep.
      * injection Hstep as Hst'. subst st'.
        split.
        { unfold Pos. cbn [s_count s_tbl]. fold (Pos (it_mass 15%nat 1 cnt0) st).
          replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
            with (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
            by (symmetry; exact HposAdv).
          exact Hfill. }
        { cbn [s_drop s_low s_tbl]. intros Hd2.
          destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                             | (Hd & Hrl & Hnx & Hlow & Hlb)];
            [exfalso; lia|].
          unfold tbl1.
          rewrite it_fill_get
            by (rewrite shiftl1 by lia; apply pow2_pos_z; lia).
          assert (Hlowlt : 0 <= s_low st < 2 ^ x_root c)
            by (rewrite Hlow; apply Z.mod_pos_bound; apply pow2_pos_z; lia).
          pose proof (Z.shiftr_nonneg (s_huff st) (s_drop st)) as [_ Hs].
          specialize (Hs ltac:(lia)).
          replace (Z.leb (s_next st + Z.shiftr (s_huff st) (s_drop st))
                     (s_low st)) with false
            by (symmetry; apply Z.leb_gt; lia).
          cbn [andb]. exact (Hlow64 Hd2). }
      * match type of Hstep with
        | (if it_enough _ (_ + Z.shiftl 1 ?cv) then _ else _) = _ =>
            remember cv as currM eqn:HcurrM
        end.
        match type of Hstep with
        | (if ?b then _ else _) = _ =>
            remember b as enM eqn:HenM; destruct enM
        end; cbv beta iota in Hstep; [discriminate Hstep|].
        injection Hstep as Hst'. subst st'.
        destruct (Hcurr' (s_len st) ltac:(lia)
                    ltac:(apply Z.ltb_lt in Hgt; exact Hgt)) as [Hc1 Hc2].
        rewrite <- HcurrM in Hc1, Hc2.
        clear HcurrM HenM.
        split.
        { unfold Pos. cbn [s_count s_tbl]. fold (Pos (it_mass 15%nat 1 cnt0) st).
          replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
            with (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
            by (symmetry; exact HposAdv).
          apply gen_tset; [|exact Hfill].
          rewrite op_mkCodeT_id by lia. lia. }
        { cbn [s_drop s_low s_tbl]. intros _.
          rewrite tset_same.
          rewrite op_mkCodeT_id by lia. lia. }
    + cbv beta iota in Hstep.
      injection Hstep as Hst'. subst st'.
      split.
      { unfold Pos. cbn [s_count s_tbl]. fold (Pos (it_mass 15%nat 1 cnt0) st).
        replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
          with (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
          by (symmetry; exact HposAdv).
        exact Hfill. }
      { cbn [s_drop s_low s_tbl]. intros Hd2.
        destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                           | (Hd & Hrl & Hnx & Hlow & Hlb)];
          [exfalso; lia|].
        unfold tbl1.
        rewrite it_fill_get
          by (rewrite shiftl1 by lia; apply pow2_pos_z; lia).
        assert (Hlowlt : 0 <= s_low st < 2 ^ x_root c)
          by (rewrite Hlow; apply Z.mod_pos_bound; apply pow2_pos_z; lia).
        pose proof (Z.shiftr_nonneg (s_huff st) (s_drop st)) as [_ Hs].
        specialize (Hs ltac:(lia)).
        replace (Z.leb (s_next st + Z.shiftr (s_huff st) (s_drop st))
                   (s_low st)) with false
          by (symmetry; apply Z.leb_gt; lia).
        cbn [andb]. exact (Hlow64 Hd2). }
Qed.

Print Assumptions nom_step_cont.

(* ==========================================================================
   6.  The break trip, to the endgame: a surviving root-window marker
       forces the degenerate max=1 table.
   ========================================================================== *)

Lemma nom_break_endgame : forall c cnt0 st st1,
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  c_op (it_here c st) <> 64 ->
  NoM64 c (it_mass 15%nat 1 cnt0) st ->
  (s_drop st = 0 -> s_used st = 2 ^ x_root c) ->
  it_step c st = ItBreak st1 ->
  forall j, 0 <= j < 2 ^ x_root c ->
  c_op (it_finish st1 j) = 64 ->
  x_root c = 1 /\ s_used st1 = 2 /\ it_finish st1 j = mkCodeT 64 1 0.
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

Print Assumptions nom_break_endgame.

(* ==========================================================================
   7.  The loop and the driver.
   ========================================================================== *)

Lemma nom_loop : forall n ty c cnt0 st st1,
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
  x_root c = 1 /\ s_used st1 = 2 /\ it_finish st1 j = mkCodeT 64 1 0.
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
    apply (nom_break_endgame c cnt0 st st' Hctx Hinv (Hh64 st) HS);
      [|exact Hs].
    (* the used-fact, from the ledger's phase-1 arm *)
    intros Hd0.
    destruct Hled as [Hroote Hphl].
    destruct Hphl as [(H1 & H2 & H3) | (H2 & _)]; [exact H2|].
    exfalso. destruct Hctx as (Hroot & _). lia.
  - discriminate Hl.
Qed.

(** The driver, ROOT-SCOPED: [o_ret out = 0] plus a marker op anywhere in
    the ROOT WINDOW pins the whole table to the degenerate max=1 build.

    STUCK/OUT-OF-SCOPE, deliberately: [no_child_markers] (the sub-region,
    indices [2^bits, used)) is NOT derivable from this root-scoped walk.
    Its honest price is a payload-swapped mirror of [ledger_step_cont]'s
    phase-2 sub-window machinery (~1365 lines — 7x what this walk's design
    assumed), or subsumption by an earlier development run's ownership ledger, which
    carries positive per-position ownership of the sub-region.
    [width_covers] is out of scope per the directive. *)
Theorem loop_no64_root : forall ty lens codes root0 t0 out,
  (ty = CT_LENS \/ ty = CT_DISTS) ->
  (ty = CT_DISTS -> codes <= 30) ->
  it_wf ty lens codes root0 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  forall i, 0 <= i < 2 ^ (o_bits out) ->
  c_op (o_tbl out i) = 64 ->
  o_bits out = 1 /\ o_used out = 2 /\ o_tbl out i = mkCodeT 64 1 0.
Proof.
  intros ty lens codes root0 t0 out Hty Hd30 Hwf Hmodel Hret.
  destruct Hwf as (Hc0 & Hlens & Hroot0 & Hkinds).
  assert (Hcodes : 0 <= codes) by lia.
  unfold it_model in Hmodel.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hmodel as <-. cbn in Hret. lia.
  - (* PreEmpty: BOTH cells are the marker; the conclusion holds outright *)
    rewrite (it_pre_empty_shape ty lens codes root0 t0 temp Hpre) in Hmodel.
    injection Hmodel as <-. cbn [o_bits o_used o_tbl].
    intros i Hi H64. change ((2:Z) ^ 1) with 2 in Hi.
    split; [reflexivity|]. split; [reflexivity|].
    destruct (Z.eq_dec i 1) as [->|Hne].
    + rewrite tset_same. reflexivity.
    + assert (i = 0) by lia. subst i.
      rewrite tset_other by lia. rewrite tset_same. reflexivity.
  - injection Hmodel as <-. cbn in Hret. lia.
  - (* PreGo: the loop *)
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
    (* the op census on the entry the loop duplicates *)
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
    (* the initial census: position 0 covers nothing, and phase 1 has no
       live low cell *)
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
    + (* ItBreak: the accepted build *)
      injection Hmodel as <-. cbn [o_bits o_used o_tbl].
      intros i Hi H64.
      exact (nom_loop (S (Z.to_nat codes)) ty c (PngModel.ItGTblSortWin.sw_cnt lens codes) st st'
               Hcty Htyc Hhere Hh64 Hcpos Hctx Hinv Hled HS0 Hloop i Hi H64).
    + (* ItOverflow: rejected *)
      injection Hmodel as <-. cbn in Hret. lia.
Qed.

Print Assumptions nom_loop.
Print Assumptions loop_no64_root.

(** The population corollary: a marker in the root window happens ONLY in
    the degenerate one-bit, two-cell table. *)
Corollary marker_population : forall ty lens codes root0 t0 out,
  (ty = CT_LENS \/ ty = CT_DISTS) ->
  (ty = CT_DISTS -> codes <= 30) ->
  it_wf ty lens codes root0 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  forall i, 0 <= i < 2 ^ (o_bits out) -> c_op (o_tbl out i) = 64 ->
  o_bits out = 1 /\ o_used out = 2.
Proof.
  intros ty lens codes root0 t0 out Hty Hd30 Hwf Hmodel Hret i Hi H64.
  destruct (loop_no64_root ty lens codes root0 t0 out Hty Hd30 Hwf Hmodel
              Hret i Hi H64) as (H1 & H2 & _).
  exact (conj H1 H2).
Qed.

Print Assumptions marker_population.
