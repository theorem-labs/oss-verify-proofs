(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngImage MngHeap MngWb MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AXF_ff3 AXG_ffpost.
Import AX2S.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section PostM2.
Variable segs : list Segment.

#[using="Type"] Theorem freed_slot_markers2 : forall L s m m' g am i fr (spz : Z),
  WF s -> repr L s (bview segs m) -> markers_hold L s (bview segs m) ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall x, ~ (spz - 1024 <= x < spz) -> ~ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) ->
     (forall a, In a (st_areas s) -> ~ (loc_addr L (LMem a) <= x < loc_addr L (LMem a) + 4096)) -> bview segs m' x = bview segs m x) ->
  markers_hold L (s_fast s g am i fr) (bview segs m').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m m' g am i fr spz HW HR HM HF Hk HFP BV.
  apply (freed_slot_markers_gen segs L s m m' g am i fr spz HW HR HM HF Hk HFP).
  intros x H1 H2 H3 H4. exact (BV x H1 H2 H3).
Qed.

#[using="Type"] Theorem freed_slot_repr_bv : forall L s m (bv' : byteview) g am i fr (spz : Z),
  WF s -> repr L s (bview segs m) -> In (g, am, i, fr) (frames s) ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall x, ~ (spz - 1024 <= x < spz) -> ~ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) ->
     ~ (loc_addr L (LMem g) + 28 <= x < loc_addr L (LMem g) + 32) -> bv' x = bview segs m x) ->
  bv' (loc_addr L (LMem (frame_ptr am i fr)) - 3) = Some 255 ->
  (forall k, (k < 2)%nat -> bv' (loc_addr L (LMem (frame_ptr am i fr)) - 2 + Z.of_nat k) = Some 0) ->
  (forall k, (k < 4)%nat -> bv' (loc_addr L (LMem g) + 28 + Z.of_nat k) = Some (le_byte (am_freed am + bit i) 4 k)) ->
  repr L (s_fast s g am i fr) (bv').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m bv' g am i fr spz HW HR HF HFP BV WR3 WR2 WRF.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (Ch4 & Ch3 & Ch16 & Cgm & Cmem & Cav & Cfr & Cbits & Geo & _ & Hland & Hasrt & Hff).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  destruct HR as (HL & HC & HFM).
  set (p := frame_ptr am i fr) in *.
  set (pa := loc_addr L (LMem p)) in *. set (G := loc_addr L (LMem g)) in *.
  (* [comment removed for export] *)
  assert (FP : forall c, In c (image s) -> 1 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= spz - 1024).
  { intros c Hc. destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl).
    pose proof (proj2 (proj2 (proj2 HL)) rg Hrg) as R. pose proof (HFP rg Hrg) as S.
    unfold range_incl, cell_range, crange in *. cbn [fst snd] in *. lia. }
  pose proof (FP _ Ch3) as F3. pose proof (FP _ Ch16) as F16. pose proof (FP _ Cfr) as FF.
  cbn [mc_loc mc_w] in F3, F16, FF. rewrite !loc_padd in F3, F16, FF. fold p in F3, F16. fold pa G in F3, F16, FF. unfold META_freed in FF.
  assert (D3F : ranges_disjoint (cell_range L (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))))
                                (cell_range L (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))))).
  { apply (image_pair_disjoint s L); [exact HW | exact HL | exact Ch3 | exact Cfr | intro E; injection E; intros; discriminate]. }
  assert (D16F : ranges_disjoint (cell_range L (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))))
                                 (cell_range L (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))))).
  { apply (image_pair_disjoint s L); [exact HW | exact HL | exact Ch16 | exact Cfr | intro E; injection E; intros; discriminate]. }
  unfold ranges_disjoint, cell_range in D3F, D16F. cbn [mc_loc mc_w fst snd] in D3F, D16F. rewrite !loc_padd in D3F, D16F.
  fold p in D3F, D16F. fold pa G in D3F, D16F. unfold META_freed in D3F, D16F.
  assert (Hst : loc_addr L (LMem (slot_start am i)) = pa - 16 * fr_off fr).
  { unfold pa, p, frame_ptr. rewrite loc_padd. unfold UNIT. ring. }
  apply (repr_update L s (s_fast s g am i fr) (bview segs m) (bv')
           [MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr)); MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr));
            MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))]
           (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am + bit i))
            :: (if fr_off fr =? 0 then [MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ 255);
                                       MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ 0)] else []))
           HW (conj HL (conj HC HFM))).
  - exact HL.
  - change (footprint (s_fast s g am i fr)) with (footprint s). apply Forall_forall. intros rg Hrg x Hx.
    pose proof (proj1 (Forall_forall _ _) HFM rg Hrg x Hx) as Hm. pose proof (HFP rg Hrg) as Hb.
    destruct (Z_lt_le_dec x (pa - 3)) as [A1|A1]; [| destruct (Z_lt_le_dec x pa) as [A2|A2]].
    + destruct (Z_lt_le_dec x (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec x (G + 32)) as [B2|B2]].
      * rewrite BV by lia. exact Hm.
      * replace x with (G + 28 + Z.of_nat (Z.to_nat (x - (G + 28)))) by lia. rewrite WRF by lia. discriminate.
      * rewrite BV by lia. exact Hm.
    + destruct (Z.eq_dec x (pa - 3)) as [->|Hne]; [rewrite WR3; discriminate|].
      replace x with (pa - 2 + Z.of_nat (Z.to_nat (x - (pa - 2)))) by lia. rewrite WR2 by lia. discriminate.
    + destruct (Z_lt_le_dec x (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec x (G + 32)) as [B2|B2]].
      * rewrite BV by lia. exact Hm.
      * replace x with (G + 28 + Z.of_nat (Z.to_nat (x - (G + 28)))) by lia. rewrite WRF by lia. discriminate.
      * rewrite BV by lia. exact Hm.
  - intros c [<-|[<-|[<-|[]]]]; assumption.
  - intros c Hc.
    assert (Mg : MT s g = Some (MUsed am)) by (apply (used_metas_iff s g am (proj1 (inv_keys HW))); exact Hu).
    destruct (image_setm s g am (fast_meta am i fr) HW Mg) as (U & P1 & P2).
    pose proof (Permutation_NoDup P1 (nodup_image L s HW HL)) as ND.
    apply (Permutation_in c P2) in Hc.
    apply (used_metas_usedX s g am HW) in Hu as Hux.
    pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & _).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HW g am Hux)) as Sp.
    pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfri in S3. destruct S3 as (Hal & _ & FOK & Hhdr).
    destruct FOK as (Fn & Foff & Ffit & _).
    assert (Epoff : poff p = poff (slot_start am i) + 16 * fr_off fr) by (unfold p, frame_ptr; rewrite poff_padd; reflexivity).
    assert (Eprid : prid p = prid (slot_start am i)) by (unfold p, frame_ptr; apply prid_padd).
    assert (InS : forall c0, In c0 (meta_slot_cells g (Some (MUsed am)) ++ group_cells g am) -> In c0 (image s)).
    { intros c0 H0. apply (Permutation_in c0 (Permutation_sym P1)). apply in_app_iff. right. exact H0. }
    apply in_app_iff in Hc as [HU|Hc].
    + left. split; [apply (Permutation_in c (Permutation_sym P1)); apply in_app_iff; left; exact HU|].
      intros HCo. apply (nodup_app_disj U _ c ND HU).
      assert (HGCi : forall c0, In c0 (slot_cells am i) -> In c0 (meta_slot_cells g (Some (MUsed am)) ++ group_cells g am)).
      { intros c0 H0. apply in_app_iff. right. unfold group_cells. apply in_app_iff. right. apply in_flat_map.
        exists i. split; [apply In_zseq; lia | exact H0]. }
      destruct HCo as [<-|[<-|[<-|[]]]].
      * apply HGCi. unfold slot_cells. rewrite Hfri. apply in_app_iff. right. apply in_app_iff.
        destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
        -- left. rewrite (Hhdr E0). replace (padd p (-3)) with (padd (slot_start am i) (-3)).
           ++ left. reflexivity.
           ++ unfold p, frame_ptr. rewrite E0. destruct (slot_start am i). cbn. f_equal. lia.
        -- right. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). right. left. reflexivity.
      * apply HGCi. unfold slot_cells. rewrite Hfri. apply in_app_iff. right. apply in_app_iff.
        destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
        -- left. rewrite (Hhdr E0). replace (padd p (-2)) with (padd (slot_start am i) (-2)).
           ++ right. left. reflexivity.
           ++ unfold p, frame_ptr. rewrite E0. destruct (slot_start am i). cbn. f_equal. lia.
        -- right. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). right. right. left. reflexivity.
      * apply in_app_iff. left. unfold meta_slot_cells. right. right. right. right. left. reflexivity.
    + apply in_app_iff in Hc as [HMS|HGC].
      * unfold meta_slot_cells in HMS. cbn [fast_meta am_set_freed upd_slot am_set_slots am_prev am_next am_mem am_avail am_freed] in HMS.
        assert (EB : meta_bits (fast_meta am i fr) = meta_bits am) by reflexivity.
        assert (MSi : forall c0, In c0 (meta_slot_cells g (Some (MUsed am))) -> In c0 (image s)).
        { intros c0 H0. apply InS. apply in_app_iff. left. exact H0. }
        destruct HMS as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
        -- left. split; [apply MSi; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; try (inversion E; fail).
           revert E. apply cell_neq_off. rewrite !poff_padd. unfold META_avail, META_freed. lia.
        -- right. left. reflexivity.
        -- left. rewrite EB. split; [apply MSi; right; right; right; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
      * pose proof (NoDup_app_remove_l _ _ ND) as ND2.
        assert (C3MS : In (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))) (meta_slot_cells g (Some (MUsed am)))).
        { unfold meta_slot_cells. right. right. right. right. left. reflexivity. }
        assert (NC3 : forall c0, In c0 (group_cells g am) -> c0 <> MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))).
        { intros c0 H0 E. subst c0. exact (nodup_app_disj _ _ _ ND2 C3MS H0). }
        assert (GCi : forall c0, In c0 (group_cells g am) -> In c0 (image s)).
        { intros c0 H0. apply InS. apply in_app_iff. right. exact H0. }
        destruct Gm as (Mlast & _ & Mlen & _).
        assert (Hsl : forall j, 0 <= j -> nth_slot (fast_meta am i fr) j = if j =? i then fast_slot am i fr else nth_slot am j).
        { intros j Hj. unfold fast_meta. change (nth_slot (am_set_freed (am_freed am + bit i) (upd_slot am i (fast_slot am i fr))) j)
            with (nth_slot (upd_slot am i (fast_slot am i fr)) j). apply nth_slot_upd_slot; [lia | exact Hj | rewrite Mlen; lia]. }
        unfold group_cells in HGC. apply in_app_iff in HGC as [HH|HSC].
        -- (* [comment removed for export] *)
           change (am_mem (fast_meta am i fr)) with (am_mem am) in HH. change (am_maplen (fast_meta am i fr)) with (am_maplen am) in HH.
           change (am_aidx (fast_meta am i fr)) with (am_aidx am) in HH.
           left. split; [apply GCi; unfold group_cells; apply in_app_iff; left; exact HH|].
           assert (HG0 : In c (group_cells g am)) by (unfold group_cells; apply in_app_iff; left; exact HH).
           destruct (am_maplen am =? 0); cbn in HH; destruct HH as [<-|[<-|[]]]; intros [E|[E|[E|[]]]];
             first [inversion E; fail | exact (NC3 _ HG0 E) | exact (NC3 _ HG0 (eq_sym E))].
        -- apply in_flat_map in HSC as (j & Hj & Hcj). apply In_zseq in Hj.
           change (am_last (fast_meta am i fr)) with (am_last am) in Hj.
           assert (GCj : forall j0 c0, 0 <= j0 <= am_last am -> In c0 (slot_cells am j0) -> In c0 (group_cells g am)).
           { intros j0 c0 Hj0 H0. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists j0. split; [apply In_zseq; lia | exact H0]. }
           destruct (Z.eq_dec j i) as [->|Hne].
           ++ assert (Es : slot_cells (fast_meta am i fr) i =
                            MCell (LMem (padd (slot_start am i) (-4))) 1 (VZ 0)
                            :: match ss_hdr (fast_slot am i fr) with
                               | Some (h3, h16) => [MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ h3); MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ h16)]
                               | None => [] end).
              { unfold slot_cells. rewrite (Hsl i ltac:(lia)), Z.eqb_refl. unfold fast_slot.
                destruct (fr_off fr =? 0); cbn [ss_hdr ss_fr app]; rewrite ?app_nil_r; reflexivity. }
              rewrite Es in Hcj. destruct Hcj as [<-|Hcj].
              ** left. split; [apply GCi, (GCj i); [lia | left; reflexivity]|].
                 intros [E|[E|[E|[]]]]; try (inversion E; fail); revert E; apply cell_neq_off; rewrite !poff_padd; fold p; rewrite Epoff; clear - Foff; unfold UNIT in *; lia.
              ** unfold fast_slot in Hcj. destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
                 --- cbn [ss_hdr] in Hcj. right. replace (fr_off fr =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0).
                     destruct Hcj as [<-|[<-|[]]]; [right; left; reflexivity | right; right; left; reflexivity].
                 --- cbn [ss_hdr] in Hcj. left.
                     assert (Hin : In c (slot_cells am i)).
                     { unfold slot_cells. apply in_app_iff. right. apply in_app_iff. left. exact Hcj. }
                     split; [apply GCi, (GCj i); [lia | exact Hin]|].
                     destruct (ss_hdr (nth_slot am i)) as [[h3' h16']|]; [|destruct Hcj].
                     intros [E|[E|[E|[]]]]; try (inversion E; fail);
                       destruct Hcj as [<-|[<-|[]]]; try (inversion E; fail); revert E; apply cell_neq_off; rewrite !poff_padd; fold p; rewrite Epoff;
                       clear - Foff E0; unfold UNIT in *; lia.
           ++ assert (Es : slot_cells (fast_meta am i fr) j = slot_cells am j).
              { unfold slot_cells. rewrite (Hsl j ltac:(lia)). replace (j =? i) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
              rewrite Es in Hcj. left. split; [apply GCi, (GCj j); [lia | exact Hcj]|].
              pose proof (Gsl j ltac:(lia)) as (_ & _ & T3).
              assert (Hfit : forall fr0, ss_fr (nth_slot am j) = Some fr0 -> 0 <= fr_off fr0 /\ 0 <= fr_n fr0 /\ UNIT * fr_off fr0 + fr_n fr0 <= stride_of am - IB).
              { intros fr0 E0. rewrite E0 in T3. destruct T3 as (_ & _ & (N0 & O0 & F0 & _) & _). lia. }
              destruct (slot_cells_span am j c Sp Hfit Hcj) as (q & Eq & Hq1 & Hq2).
              pose proof (same_group_starts am i j ltac:(lia) Sp) as SGS.
              intros [E|[E|[E|[]]]].
              ** rewrite <- E in Eq. cbn [mc_loc] in Eq. injection Eq as Eq. rewrite <- Eq in Hq2. rewrite poff_padd in Hq2.
                 fold p in Hq2. rewrite Epoff in Hq2. clear - Hq2 SGS Foff Ffit Fn. unfold UNIT, IB in *. lia.
              ** rewrite <- E in Eq. cbn [mc_loc] in Eq. injection Eq as Eq. rewrite <- Eq in Hq2. rewrite poff_padd in Hq2.
                 fold p in Hq2. rewrite Epoff in Hq2. clear - Hq2 SGS Foff Ffit Fn. unfold UNIT, IB in *. lia.
              ** exact (NC3 c (GCj j c ltac:(lia) Hcj) (eq_sym E)).
  - constructor.
    + intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd. fold G. unfold META_freed. rewrite WRF by exact Hk. reflexivity.
    + destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0]; [|constructor].
      constructor; [|constructor; [|constructor]].
      * intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Hst, E0. destruct k as [|k]; [|cbn in Hk; lia].
        replace (pa - 16 * 0 + -3 + Z.of_nat 0) with (pa - 3) by ring. rewrite WR3. reflexivity.
      * intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Hst, E0.
        replace (pa - 16 * 0 + -2 + Z.of_nat k) with (pa - 2 + Z.of_nat k) by ring. rewrite WR2 by exact Hk.
        destruct k as [|[|k]]; [reflexivity | reflexivity | cbn in Hk; lia].
  - intros a Ha.
    destruct (Z_lt_le_dec a (pa - 3)) as [A1|A1]; [| destruct (Z_lt_le_dec a pa) as [A2|A2]].
    + destruct (Z_lt_le_dec a (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec a (G + 32)) as [B2|B2]].
      * destruct (Z_lt_le_dec a (spz - 1024)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
      * left. exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold G. unfold META_freed. lia.
      * destruct (Z_lt_le_dec a (spz - 1024)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
    + left. destruct (Z.eq_dec a (pa - 3)) as [->|Hne].
      * exists (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))). split; [left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold pa. lia.
      * exists (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))). split; [right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold pa. lia.
    + destruct (Z_lt_le_dec a (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec a (G + 32)) as [B2|B2]].
      * destruct (Z_lt_le_dec a (spz - 1024)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
      * left. exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold G. unfold META_freed. lia.
      * destruct (Z_lt_le_dec a (spz - 1024)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
Qed.


#[using="Type"] Theorem freed_slot_markers3 : forall L s m m' g am i fr (spz : Z),
  WF s -> repr L s (bview segs m) -> markers_hold L s (bview segs m) ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall x, ~ (spz - 1024 <= x < spz) -> ~ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) ->
     (forall a, In a (st_areas s) -> ~ (loc_addr L (LMem a) <= x < loc_addr L (LMem a) + 4096)) ->
     ~ (ly_ctx L <= x < ly_ctx L + CTX_SIZE) -> bview segs m' x = bview segs m x) ->
  markers_hold L (s_fast s g am i fr) (bview segs m').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m m' g am i fr spz HW HR HM HF Hk HFP BV.
  exact (freed_slot_markers_gen segs L s m m' g am i fr spz HW HR HM HF Hk HFP BV).
Qed.
End PostM2.

(* [comment removed for export] *)
Lemma flat_map_flat_map' : forall {A B C} (f : B -> list C) (g : A -> list B) l,
  flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
Proof. intros A B C f g l. induction l as [|x t IH]; [reflexivity|]. cbn [flat_map]. rewrite flat_map_app'. rewrite IH. reflexivity. Qed.

Lemma markers_eq : forall s, markers s = flat_map (fun gm : sptr * ameta => meta_markers (snd gm)) (used_metas s).
Proof. reflexivity. Qed.

Lemma markers_set_meta : forall s q am am', MT s q = Some (MUsed am) -> meta_markers am' = meta_markers am ->
  markers (set_meta s q (MUsed am')) = markers s.
Proof.
  intros s q am am' Hq Hm. rewrite !markers_eq. unfold used_metas, set_meta. cbn [st_metas set_metas].
  unfold MT in Hq. induction (st_metas s) as [|[k y] t IH]; [discriminate|].
  cbn [mupdate mlookup] in *. destruct (sptr_eqb q k) eqn:E.
  - injection Hq as ->. cbn [flat_map app fst snd]. rewrite Hm. reflexivity.
  - cbn [flat_map]. rewrite !flat_map_app'. rewrite (IH Hq). reflexivity.
Qed.
