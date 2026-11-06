(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngTake MngGeoX MngOwn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section TX.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis HXU : XNU X s.
Hypothesis HL : layout_ok L s.

#[using="R U HI HL"] Lemma regions_apart_X : forall (a1 a2 : ameta) g1 g2 lo1 n1 lo2 n2,
  usedX X s g1 a1 -> usedX X s g2 a2 -> prid (am_mem a1) <> prid (am_mem a2) ->
  0 <= lo1 -> lo1 + n1 <= poff (am_mem a1) + group_extent a1 + IB ->
  0 <= lo2 -> lo2 + n2 <= poff (am_mem a2) + group_extent a2 + IB ->
  ly_reg L (prid (am_mem a1)) + lo1 + n1 <= ly_reg L (prid (am_mem a2)) + lo2 \/
  ly_reg L (prid (am_mem a2)) + lo2 + n2 <= ly_reg L (prid (am_mem a1)) + lo1.
Proof. LiaFast.lf_pins (fun (R U HI HL : LiaFast.U) => LiaFast.u0).
  intros a1 a2 g1 g2 lo1 n1 lo2 n2 U1 U2 Hne H1 H2 H3 H4.
  pose proof HL as (_ & _ & Ldisj & _).
  destruct (used_group_region X R U s g1 a1 HI U1) as (rg1 & Hr1 & Hk1 & Hl1 & Ho1 & He1 & _).
  destruct (used_group_region X R U s g2 a2 HI U2) as (rg2 & Hr2 & Hk2 & Hl2 & Ho2 & He2 & _).
  assert (F1 : In (LMem (SP (prid (am_mem a1)) 0), rg_len rg1) (footprint s)) by (apply footprint_region_In; assumption).
  assert (F2 : In (LMem (SP (prid (am_mem a2)) 0), rg_len rg2) (footprint s)) by (apply footprint_region_In; assumption).
  destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj F1 F2 ltac:(intro E; injection E; intros; contradiction)) as [D|D];
    unfold ranges_disjoint in D; cbn [crange fst snd loc_addr] in D; rewrite ?region_loc in D; unfold IB in *; lia.
Qed.

#[using="R U HI HXU HL"] Theorem image_outside_free_slot_X : forall c g am k,
  usedX X s g am -> 0 <= k <= am_last am -> ss_fr (nth_slot am k) = None ->
  In c (image s) -> ~ In c (slot_cells am k) ->
  ranges_disjoint (cell_range L c) (free_slot_range L am k).
Proof. LiaFast.lf_pins (fun (R U HI HXU HL : LiaFast.U) => LiaFast.u0).
  intros c g am k Hg Hk Hfr Hc Hnk. pose proof HL as (_ & _ & PW & _).
  pose proof (inv_groups HI g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  destruct (used_group_region X R U s g am HI Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  pose proof (footprint_region_In s _ _ Hr Hkd Hl) as InR.
  pose proof (slot_in_span X R U s HI g am k Hg Hk) as [S1 S1'].
  assert (BI : range_incl (free_slot_range L am k) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg))).
  { unfold free_slot_range, crange, range_incl, loc_addr. cbn [fst snd].
    unfold slot_start in *. destruct (am_mem am) as [r o]. cbn [padd prid poff] in *. unfold group_extent, IB, UNIT in *. lia. }
  assert (VIA : forall e, In e (footprint s) -> e <> (LMem (SP (prid (am_mem am)) 0), rg_len rg) ->
            range_incl (cell_range L c) (crange L e) -> ranges_disjoint (cell_range L c) (free_slot_range L am k)).
  { intros e He Hne Hincl.
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He InR Hne) as [D|D].
    - eapply ranges_disjoint_incl; [exact D | exact Hincl | exact BI].
    - apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact BI | exact Hincl]. }
  destruct (In_image_inv s c Hc) as [Hcc | [(a & next & Ha & Hcc) | (g' & am' & Hg' & Hcc)]].
  - destruct (In_ctx_cells s c Hcc) as (off & E & Ho' & Hw). apply (VIA (LCtx 0, CTX_SIZE)); [left; reflexivity | discriminate |].
    unfold cell_range, crange, range_incl, loc_addr. rewrite E. cbn [fst snd]. lia.
  - destruct (In_area_cells s a next c Hcc) as (d & E & Hd & Hw).
    pose proof (inv_areas HI) as (_ & A2 & _). destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _).
    apply (VIA (LMem a, PGSZ)).
    + right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
    + rewrite Ea. intros E2. injection E2 as _ Eo _. unfold PGSZ in Hoa. lia.
    + unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
  - apply (used_metas_usedX_X X R U s g' am' HI HXU) in Hg'.
    destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
    2:{ destruct (used_group_region X R U s g' am' HI Hg') as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
        destruct (In_group_cells_span X R U s g' am' c HI Hg' Hcc) as (d & E & Hd & Hw).
        apply (VIA (LMem (SP (prid (am_mem am')) 0), rg_len rg')); [apply footprint_region_In; assumption | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep) |].
        unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in *. lia. }
    assert (GOAL : forall d, mc_loc c = LMem (padd (am_mem am') d) ->
              (poff (am_mem am') + d + Z.of_nat (mc_w c) <= poff (slot_start am k) - 3 \/
               poff (slot_start am k) + stride_of am - 5 < poff (am_mem am') + d) ->
              ranges_disjoint (cell_range L c) (free_slot_range L am k)).
    { intros d E D. unfold cell_range, free_slot_range, ranges_disjoint, loc_addr. rewrite E. cbn [fst snd].
      unfold slot_start in *. destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. lia. }
    destruct (sptr_eq_dec g' g) as [->|Hne].
    + pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
      unfold group_cells in Hcc. apply in_app_iff in Hcc as [Hcc|Hcc].
      * destruct Hcc as [<-|[<-|[]]].
        -- apply (GOAL 0); [cbn; rewrite padd_0; reflexivity|]. left. rewrite poff_slot_start. cbn [mc_w Z.of_nat Pos.of_succ_nat]. unfold UNIT in *. nia.
        -- destruct (am_maplen am =? 0); (apply (GOAL 8); [reflexivity|]); left; rewrite poff_slot_start; cbn [mc_w Z.of_nat Pos.of_succ_nat]; unfold UNIT in *; nia.
      * apply in_flat_map in Hcc as [j [Hj Hcj]]. apply In_zseq in Hj.
        destruct (Z.eq_dec j k) as [->|Hjk]; [contradiction|].
        destruct (In_slot_cells X R U s g am j c HI Hg ltac:(lia) Hcj) as (d & E & Lo & Hiw & _).
        apply (GOAL d E). rewrite poff_slot_start.
        assert (j < k \/ k < j) as [Hlt|Hlt] by lia; [left|right];
          [assert (stride_of am * j + stride_of am <= stride_of am * k) by nia | assert (stride_of am * k + stride_of am <= stride_of am * j) by nia];
          unfold UNIT, IB in *; lia.
    + pose proof (extent_pos _ _ _ _ _ (inv_groups HI g' am' Hg')) as Pa'.
      destruct (inv_laminar HI g' am' g am Hg' Hg Hne Hsame) as [Dj | [I | I]].
      * destruct (In_group_cells_span X R U s g' am' c HI Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
        unfold spans_disjoint in Dj. rewrite poff_slot_start. rewrite poff_slot_start in S1, S1'.
        unfold UNIT, IB in *. destruct Dj; [left|right]; lia.
      * destruct (In_group_cells_span X R U s g' am' c HI Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
        destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
        destruct (Z.eq_dec j0 k) as [->|Hji]; [rewrite Hfr in Hfr0; discriminate|].
        pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
        rewrite Mem0, poff_slot_start in Lo0, Hi0.
        destruct (same_group_starts am j0 k Hji Sp) as [LE|LE]; rewrite !poff_slot_start in *; unfold group_extent, UNIT, IB in *; [left|right]; lia.
      * destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
        pose proof (inv_groups HI g' am' Hg') as (_ & _ & Gsl' & _). pose proof (Gsl' j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
        destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' Fn'].
        destruct (group_cells_vs_body X R U s g' am' j' (poff (slot_start am k) - 3) (poff (slot_start am k) + stride_of am - 4) c HI Hg' Hj' Hcc) as (d & E & D).
        -- rewrite Hfr', Off'. rewrite Mem0 in Lo0. rewrite !poff_slot_start in *. unfold UNIT, IB in *. lia.
        -- rewrite Mem0 in Hi0. rewrite !poff_slot_start in *. unfold group_extent, UNIT, IB in *. lia.
        -- apply (GOAL d E). lia.
Qed.

#[using="R U HI HXU HL"] Theorem free_slot_outside_blocks_X : forall g am k b,
  usedX X s g am -> 0 <= k <= am_last am -> ss_fr (nth_slot am k) = None ->
  In b (user_blocks s) -> ranges_disjoint (block_range L b) (free_slot_range L am k).
Proof. LiaFast.lf_pins (fun (R U HI HXU HL : LiaFast.U) => LiaFast.u0).
  intros g am k b Hg Hk Hfr Hb.
  destruct (in_user_blocks_inv s b Hb) as (h & ah & j & f & Hh & Hj & Hf & Kf & ->).
  apply (used_metas_usedX_X X R U s h ah HI HXU) in Hh as Uh.
  pose proof (inv_groups HI h ah Uh) as (_ & _ & Gslh & _). pose proof (Gslh j Hj) as (_ & _ & T3). rewrite Hf in T3.
  destruct T3 as (_ & _ & (Nf & Of & Ff & _) & _).
  pose proof (slot_in_span X R U s HI h ah j Uh Hj) as [SJ1 SJ2].
  pose proof (slot_in_span X R U s HI g am k Hg Hk) as [SK1 SK2].
  pose proof (stride_pos _ _ _ _ _ (inv_groups HI h ah Uh)) as Sh.
  pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hg)) as Sg.
  unfold ranges_disjoint, block_range, free_slot_range, frame_ptr. cbn [fst snd].
  rewrite (loc_padd L (slot_start ah j) (UNIT * fr_off f)).
  assert (Eloc : forall r, loc_addr L (LMem r) = ly_reg L (prid r) + poff r) by (intros [rr oo]; reflexivity).
  rewrite !Eloc. rewrite !prid_slot_start.
  destruct (Nat.eq_dec (prid (am_mem am)) (prid (am_mem ah))) as [Er|Er].
  - rewrite Er.
    assert (D : poff (slot_start am k) + stride_of am <= poff (slot_start ah j) \/
                poff (slot_start ah j) + stride_of ah <= poff (slot_start am k)).
    { destruct (sptr_eq_dec g h) as [<-|Hgh].
      - pose proof (usedX_fun _ _ _ _ _ Hg Uh) as <-. destruct (Z.eq_dec k j) as [->|Hkj]; [rewrite Hfr in Hf; discriminate|].
        exact (same_group_starts am k j Hkj Sg).
      - destruct (inv_laminar HI g am h ah Hg Uh Hgh Er) as [D | [I | I]].
        + unfold spans_disjoint in D. unfold group_extent, UNIT, IB in *. lia.
        + destruct (inside_slot_start X R U s HI _ _ _ _ _ Hg Uh Hk I) as (j0 & fr0 & Hj0 & Hfj & Hkj & A & B).
          destruct (Z.eq_dec j0 j) as [->|Hji]; [rewrite Hf in Hfj; injection Hfj as <-; rewrite Kf in Hkj; discriminate|].
          destruct (same_group_starts ah j0 j Hji Sh); unfold UNIT in *; lia.
        + destruct (inside_slot_start X R U s HI _ _ _ _ _ Uh Hg Hj I) as (j0 & fr0 & Hj0 & Hfj & Hkj & A & B).
          destruct (Z.eq_dec j0 k) as [->|Hji]; [rewrite Hfr in Hfj; discriminate|].
          destruct (same_group_starts am j0 k Hji Sg); unfold UNIT in *; lia. }
    unfold UNIT, IB in *. lia.
  - destruct (used_group_region X R U s g am HI Hg) as (rgG & _ & _ & _ & HoG & _).
    destruct (used_group_region X R U s h ah HI Uh) as (rgH & _ & _ & _ & HoH & _).
    destruct (regions_apart_X am ah g h (poff (slot_start am k) - 3) (stride_of am - 1) (poff (slot_start ah j) + UNIT * fr_off f) (fr_n f) Hg Uh Er)
      as [D|D].
    + unfold UNIT in *. lia.
    + unfold group_extent, UNIT, IB in *. lia.
    + unfold UNIT in *. lia.
    + unfold group_extent, UNIT, IB in *. lia.
    + unfold UNIT, IB in *. lia.
    + unfold UNIT, IB in *. lia.
Qed.
End TX.
