(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngWb MngGeoX MngLt MngSurgery MngExc MngGM MngNtfPre MngShape MngTake.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngNtfM MngNtfS MngMWP MngMW0 MngMW1 MngTakeR MngTakeRX MngGeo MngGeoMX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma segs_none_heap_mk : forall a, (a < 0x10000 \/ 0x99000 <= a) -> find_segment SEGS a 1 = None.
Proof.
  intros a Ha.
  assert (H : forallb (fun sg => (0x10000 <=? Z.of_N (seg_base sg)) && (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 0x99000)) SEGS = true)
    by (vm_compute; reflexivity).
  revert H. generalize SEGS as l. induction l as [|sg t IH]; intros H; [reflexivity|]. cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. cbn [find_segment].
  replace ((Z.of_N (seg_base sg) <=? a) && (a + 1 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) with false
    by (symmetry; apply andb_false_iff; destruct Ha; [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]).
  exact (IH H2).
Qed.

(* [comment removed for export] *)
Lemma heap_byte_mk : forall (m : word -> option byte) a z, 0 <= a < 2^64 -> (a < 0x10000 \/ 0x99000 <= a) ->
  bview SEGS m a = Some z -> m (wa a) = Some (Z_to_bv 8 z).
Proof.
  intros m a z Ha Hh H. destruct (bview_some SEGS m a z H) as (_ & Hw & Hr).
  unfold wview in Hw. destruct (m (wa a)) as [b|] eqn:E.
  - cbn [ov_read_bytes] in Hr. rewrite E in Hr. injection Hr as <-. reflexivity.
  - exfalso. apply Hw. rewrite (u_wa_small a) by lia. rewrite segs_none_heap_mk by exact Hh. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma holds_same_byte : forall L (bv bv' : byteview) c a, cell_holds L bv c -> cell_holds L bv' c -> (forall z, mc_val c <> VLo5 z) ->
  in_rng (cell_range L c) a -> bv' a = bv a.
Proof.
  intros L bv bv' [l w v] a H1 H2 Hv Ha. unfold cell_holds in *. cbn [mc_loc mc_w mc_val] in *. unfold in_rng, cell_range in Ha. cbn [fst snd mc_loc mc_w] in Ha.
  destruct v as [z|z|p|] ; try (exfalso; exact (Hv _ eq_refl));
    (replace a with (loc_addr L l + Z.of_nat (Z.to_nat (a - loc_addr L l))) by lia;
     rewrite (H1 (Z.to_nat (a - loc_addr L l)) ltac:(lia)), (H2 (Z.to_nat (a - loc_addr L l)) ltac:(lia)); reflexivity).
Qed.

Lemma slot_cells_gshape : forall a b i, gshape a b -> slot_cells b i = slot_cells a i.
Proof.
  intros a b i G. pose proof G as (A1 & A2 & A3 & A4 & A5).
  assert (ES : slot_start b i = slot_start a i) by (unfold slot_start; rewrite (stride_gshape a b G), A1; reflexivity).
  assert (EN : nth_slot b i = nth_slot a i) by (unfold nth_slot; rewrite A5; reflexivity).
  assert (EH : forall fr, hdr_byte3 b i fr = hdr_byte3 a i fr /\ hdr_off16 b i fr = hdr_off16 a i fr).
  { intros fr. unfold hdr_byte3, hdr_off16, rsv_code. rewrite (stride_gshape a b G). split; reflexivity. }
  unfold slot_cells. rewrite ES, EN. destruct (ss_fr (nth_slot a i)) as [fr|]; [|reflexivity].
  destruct (fr_off fr =? 0); [reflexivity|]. destruct (EH fr) as (E1 & E2). rewrite E1, E2. reflexivity.
Qed.

Lemma slot_cells_VZ : forall am i c, In c (slot_cells am i) -> exists z, mc_val c = VZ z.
Proof.
  intros am i c Hin. unfold slot_cells in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
  - destruct Hin as [<-|[]]. eexists; reflexivity.
  - destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hin]. destruct Hin as [<-|[<-|[]]]; eexists; reflexivity.
  - destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hin]. destruct (fr_off fr =? 0); [destruct Hin|].
    destruct Hin as [<-|[<-|[<-|[]]]]; eexists; reflexivity.
Qed.

Lemma markers_width_any : forall s c, In c (markers s) -> (1 <= mc_w c)%nat.
Proof.
  intros s c H. unfold markers in H. apply in_flat_map in H as [[g2 a2] [_ H]]. cbn [snd] in H. unfold meta_markers in H.
  apply in_app_iff in H as [H|[<-|[]]]; [|cbn; lia].
  apply in_flat_map in H as [i [_ H]]. destruct (ss_fr (nth_slot a2 i)) as [f|]; [|destruct H].
  destruct (fr_kind f); [|destruct H]. unfold marker_cells in H. destruct H as [<-|H]; [cbn; lia|].
  apply in_app_iff in H as [H|H]; [destruct (0 <? _); [destruct H as [<-|[]]; cbn; lia | destruct H]|].
  destruct (5 <=? _); [destruct H as [<-|[<-|[]]]; cbn; lia | destruct H].
Qed.

Lemma markers_val_any : forall s c, In c (markers s) -> exists z, mc_val c = VZ z.
Proof.
  intros s c H. unfold markers in H. apply in_flat_map in H as [[g2 a2] [_ H]]. cbn [snd] in H. unfold meta_markers in H.
  apply in_app_iff in H as [H|[<-|[]]]; [|exists 0; reflexivity].
  apply in_flat_map in H as [i [_ H]]. destruct (ss_fr (nth_slot a2 i)) as [f|]; [|destruct H].
  destruct (fr_kind f); [|destruct H]. unfold marker_cells in H. destruct H as [<-|H]; [exists 0; reflexivity|].
  apply in_app_iff in H as [H|H]; [destruct (0 <? _); [destruct H as [<-|[]]; exists 0; reflexivity | destruct H]|].
  destruct (5 <=? _); [destruct H as [<-|[<-|[]]]; eexists; reflexivity | destruct H].
Qed.

Theorem markers_keep : forall HTOP X R U X' R' U' L s m L' s' m' sp0 K,
  CUT HTOP X R U L s m sp0 K -> markers_hold L s (bview SEGS m) ->
  CUT HTOP X' R' U' L' s' m' sp0 K -> GROW sp0 K L s m L' s' m' ->
  (forall q a', In (q, a') (used_metas s') -> (exists a, In (q, a) (used_metas s) /\ gshape a a') \/ (length (st_regions s) <= prid (am_mem a'))%nat) ->
  forall c, In c (markers s) -> cell_holds L' (bview SEGS m') c.
Proof.
  intros HTOP X R U X' R' U' L s m L' s' m' sp0 K C MK C' GR HU c Hc.
  pose proof C as [HI HX N HG HD HT HTB]. pose proof C' as [HI' HX' N' HG' HD' HT' HTB'].
  pose proof (XNU_of_XNM X s HX) as XU. pose proof (XNU_of_XNM X' s' HX') as XU'.
  pose proof (nc_ctx _ _ _ _ _ _ _ N') as Hctx'. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  pose proof GR as (HE & RM & _ & SI & CH).
  destruct (marker_in_region_X X R U s L c HI XU Hc) as (r & rg & o & Hr & Kr & Lr & Ec & Oc & Wc).
  assert (Hlt : (r < length (st_regions s))%nat) by exact (region_of_lt s r rg Hr).
  pose proof RM as (Rlen & RMl). destruct (RMl r rg Hr Lr) as (rg' & Hr' & Lr' & Kr' & Len').
  destruct (HG r rg Hr Lr) as (B1 & _ & B3 & B4). unfold ranges_disjoint in B4. cbn [fst snd] in B4.
  assert (ELr : ly_reg L' r = ly_reg L r) by exact (proj2 (proj2 (proj2 HE)) r Hlt).
  pose proof (proj1 (Forall_forall _ _) MK c Hc) as HH.
  pose proof (markers_width_any s c Hc) as W1. destruct (markers_val_any s c Hc) as (zc & Vc).
  assert (EL : loc_addr L' (mc_loc c) = loc_addr L (mc_loc c)) by (rewrite Ec; cbn [loc_addr prid poff]; rewrite ELr; reflexivity).
  assert (HH' : cell_holds L' (bview SEGS m) c).
  { unfold cell_holds in *. rewrite EL. rewrite Vc in *. cbn [sval_num] in *. exact HH. }
  apply (cell_holds_frame L' (bview SEGS m) (bview SEGS m') c W1 HH'). intros a Ha. apply MngWb.bview_ext.
  assert (Ea : ly_reg L r + o <= a < ly_reg L r + o + Z.of_nat (mc_w c)).
  { unfold in_rng, cell_range in Ha. rewrite EL, Ec in Ha. cbn [fst snd loc_addr prid poff] in Ha. exact Ha. }
  assert (Ha64 : 0 <= a < 2^64) by (clear - Ea B1 B3 HTB Oc Wc Len'; unfold PGSZ in *; lia).
  destruct (decide (m' (wa a) = m (wa a))) as [E|Hne]; [exact E|]. exfalso.
  (* [comment removed for export] *)
  assert (OTHER : forall r2 rg2, region_of s' r2 = Some rg2 -> rg_live rg2 = true -> r2 <> r ->
                    ly_reg L' r2 <= a < ly_reg L' r2 + rg_len rg2 -> False).
  { intros r2 rg2 Hr2 Hl2 Hne2 Ha2. pose proof (HD' r2 r rg2 rg' Hne2 Hr2 Hr' Hl2 Lr') as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
    rewrite ELr in D. clear - D Ha2 Ea Oc Wc Len'. lia. }
  destruct (CH a Ha64 Hne) as [A | [(c' & Hc' & Hin) | [(r2 & rg2 & Hr2 & Hl2 & Hge & Ha2) | (r2 & rg2 & Hr2 & Hl2 & Hk2 & Ha2)]]].
  - clear - A Ea B3 HT Oc Wc Len'. lia.
  - destruct (In_image_inv s' c' Hc') as [Hcx | [(a0 & next & Ha0 & Hca) | (g' & a' & Hg' & Hcg)]].
    + destruct (In_ctx_cells s' c' Hcx) as (off & E & Ho & Hw). unfold in_rng, cell_range in Hin. rewrite E in Hin. cbn [fst snd loc_addr] in Hin.
      rewrite Hctx' in Hin. unfold CTX_SIZE in Hw. clear - Hin Hw Ho B4 Ea Oc Wc. lia.
    + destruct (In_area_cells s' a0 next c' Hca) as (d & E & Hd & Hw).
      destruct (area_range HTOP X' R' U' s' L' a0 HI' HG' Ha0) as (ra & rga & Ea0 & Hra & Hla & Hka & A1 & A2 & _ & _).
      apply (OTHER ra rga Hra Hla).
      * intros Eq. rewrite Eq in Hra. rewrite Hr' in Hra. injection Hra as <-. exact (Hka (eq_trans Kr' Kr)).
      * unfold in_rng, cell_range in Hin. rewrite E, loc_padd in Hin. cbn [fst snd] in Hin. unfold PGSZ in *. clear - Hin A1 A2 Hd Hw. lia.
    + destruct (HU g' a' Hg') as [(a0 & Hg0 & GS) | New].
      * apply (used_metas_usedX_X X R U s g' a0 HI XU) in Hg0. pose proof (usedX_MT _ _ _ _ Hg0) as [Mg0 _].
        pose proof GS as (GA1 & GA2 & GA3 & GA4 & GA5).
        destruct (used_group_region X R U s g' a0 HI Hg0) as (rg0 & Hr0 & Hk0 & Hl0 & Ho0 & Hext0 & _).
        assert (Hlt0 : (prid (am_mem a0) < length (st_regions s))%nat) by exact (region_of_lt s _ rg0 Hr0).
        assert (EM : loc_addr L' (LMem (am_mem a')) = loc_addr L (LMem (am_mem a0))).
        { rewrite <- GA1. destruct (am_mem a0) as [rr oo] eqn:Em. cbn [loc_addr prid poff] in *. rewrite (proj2 (proj2 (proj2 HE)) rr Hlt0). reflexivity. }
        unfold group_cells in Hcg. apply in_app_iff in Hcg as [Hhd | Hsl].
        -- (* [comment removed for export] *)
           assert (Hh12 : loc_addr L (LMem (am_mem a0)) <= a < loc_addr L (LMem (am_mem a0)) + 12).
           { unfold in_rng, cell_range in Hin.
             destruct Hhd as [<-|[Hx|[]]]; [cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat] in Hin; rewrite EM in Hin; lia|].
             destruct (am_maplen a' =? 0); rewrite <- Hx in Hin; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat] in Hin; rewrite loc_padd, EM in Hin; lia. }
           destruct (markers_vs_hdr_X X R U s HI XU c g' a0 Hc Mg0) as (qc & Eqc & Dq).
           rewrite Ec in Eqc. injection Eqc as <-. cbn [prid poff] in Dq.
           destruct (Nat.eq_dec r (prid (am_mem a0))) as [Er|Er].
           ++ rewrite <- Er in Dq. destruct Dq as [Dq|Dq]; [exact (Dq eq_refl)|].
              assert (Eloc : loc_addr L (LMem (am_mem a0)) = ly_reg L r + poff (am_mem a0)) by (rewrite Er; destruct (am_mem a0); reflexivity).
              rewrite Eloc in Hh12. clear - Dq Hh12 Ea. lia.
           ++ pose proof (HD r (prid (am_mem a0)) rg rg0 Er Hr Hr0 Lr Hl0) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
              assert (Eloc : loc_addr L (LMem (am_mem a0)) = ly_reg L (prid (am_mem a0)) + poff (am_mem a0)) by (destruct (am_mem a0); reflexivity).
              rewrite Eloc in Hh12. pose proof (ext28_X X R U s HI g' a0 Hg0) as X28. unfold IB in Hext0.
              clear - D Hh12 Ea Oc Wc Ho0 Hext0 X28. lia.
        -- (* [comment removed for export] *)
           apply in_flat_map in Hsl as (i & Hi & Hci). rewrite (slot_cells_gshape a0 a' i GS) in Hci.
           assert (Hc0 : In c' (image s)).
           { unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (g', a0).
             split; [exact (proj2 (used_metas_usedX_X X R U s g' a0 HI XU) Hg0)|]. cbn [fst snd]. unfold group_cells. apply in_app_iff. right.
             apply in_flat_map. exists i. split; [rewrite GA3; exact Hi | exact Hci]. }
           pose proof (repr_x_holds L s (bview SEGS m) [] c' (nc_repr _ _ _ _ _ _ _ N) Hc0 (fun H => H)) as H0.
           pose proof (repr_x_holds L' s' (bview SEGS m') [] c' (nc_repr _ _ _ _ _ _ _ N') Hc' (fun H => H)) as H1.
           pose proof (cell_holds_ext X R U s L L' HI HX HE (bview SEGS m) c' Hc0 H0) as H0'.
           destruct (slot_cells_VZ a0 i c' Hci) as (zz & Vz).
           pose proof (holds_same_byte L' (bview SEGS m) (bview SEGS m') c' a H0' H1 ltac:(intros z E; rewrite Vz in E; discriminate E) Hin) as Eb.
           assert (Hdef : exists z, bview SEGS m a = Some z).
           { unfold cell_holds in H0'. rewrite Vz in H0'. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin.
             pose proof (H0' (Z.to_nat (a - loc_addr L' (mc_loc c'))) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
             replace (loc_addr L' (mc_loc c') + (a - loc_addr L' (mc_loc c'))) with a in Hb by ring. eexists. exact Hb. }
           destruct Hdef as (zb & Ezb).
           assert (Hoff : a < 0x10000 \/ 0x99000 <= a) by (clear - B4 Ea Oc Wc; lia).
           apply Hne. rewrite (heap_byte_mk m a zb Ha64 Hoff Ezb). rewrite <- Eb in Ezb. exact (heap_byte_mk m' a zb Ha64 Hoff Ezb).
      * (* [comment removed for export] *)
        apply (used_metas_usedX_X X' R' U' s' g' a' HI' XU') in Hg'.
        destruct (group_cell_home_X L' X' R' U' s' g' a' c' HI' Hg' Hcg) as (rgn & Hrn & Hkn & Hln & _ & Incl).
        apply (OTHER (prid (am_mem a')) rgn Hrn Hln); [clear - New Hlt; lia|].
        unfold range_incl, in_rng, cell_range, crange in *. cbn [fst snd] in *. clear - Incl Hin. cbn [loc_addr prid poff] in Incl. lia.
  - apply (OTHER r2 rg2 Hr2 Hl2 ltac:(clear - Hge Hlt; lia) Ha2).
  - apply (OTHER r2 rg2 Hr2 Hl2).
    + intros Eq. subst r2. rewrite Hr' in Hr2. injection Hr2 as <-. exact (Hk2 (eq_trans Kr' Kr)).
    + exact Ha2.
Qed.

(* [comment removed for export] *)
Lemma meta_markers_gshape : forall a b, gshape a b -> meta_markers b = meta_markers a.
Proof.
  intros a b G. pose proof G as (A1 & A2 & A3 & A4 & A5).
  assert (ST : stride_of b = stride_of a) by (symmetry; exact (stride_gshape a b G)).
  unfold meta_markers, marker_cells, gend_cell, slot_end, frame_rsv, slot_start, nth_slot. rewrite ST, <- A1, <- A3, <- A5. reflexivity.
Qed.

Lemma markers_shape : forall s s', SHP s s' -> markers s' = markers s.
Proof.
  intros s s' (_ & _ & C & _). unfold markers, used_metas. revert C. generalize (st_metas s) as l, (st_metas s') as l'. intros l l' C.
  induction C as [|[p x] [p' y] t t' (E1 & E2) H IH]; [reflexivity|]. cbn [fst snd] in E1, E2. subst p'.
  cbn [flat_map]. rewrite !flat_map_app, IH. f_equal.
  destruct x as [pr nx| |a]; destruct y as [pr' nx'| |b]; cbn in E2; try contradiction; cbn; try reflexivity.
  rewrite !app_nil_r. exact (meta_markers_gshape a b E2).
Qed.

Lemma used_shape : forall s s', SHP s s' -> forall q a', In (q, a') (used_metas s') -> exists a, In (q, a) (used_metas s) /\ gshape a a'.
Proof.
  intros s s' (_ & _ & C & _) q a' Hin. unfold used_metas in *. revert Hin. revert C. generalize (st_metas s) as l, (st_metas s') as l'. intros l l' C.
  induction C as [|[p x] [p' y] t t' (E1 & E2) H IH]; intros Hin; [destruct Hin|]. cbn [fst snd] in E1, E2. subst p'.
  cbn [flat_map] in *. apply in_app_iff in Hin as [Hin|Hin].
  - destruct y as [pr' nx'| |b]; [destruct Hin | destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
    destruct x as [pr nx| |a]; cbn in E2; try contradiction. exists a. split; [left; reflexivity | exact E2].
  - destruct (IH Hin) as (a & Ha & G). exists a. split; [apply in_app_iff; right; exact Ha | exact G].
Qed.
