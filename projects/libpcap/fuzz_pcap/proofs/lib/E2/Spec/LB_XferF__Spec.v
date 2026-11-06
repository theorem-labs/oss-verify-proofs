(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WKill.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2 MI_WSlot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module LB_XferF.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WKill. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WKill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WNtf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.LB_WNtf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma ncarved_dom st1 st2 : (forall m, s_metas st2 !! m <> None <-> s_metas st1 !! m <> None) -> ncarved st2 = ncarved st1.
Proof.
  intros H. unfold ncarved, zlen. rewrite !length_map_to_list. f_equal. rewrite <- !size_dom. apply set_size_proper.
  apply set_equiv. intros m. rewrite !elem_of_dom, <- !not_eq_None_Some. apply H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XFERF.
Variables (X1 X2 : extras) (st1 st2 : mstate) (L1 L2 : mled) (BL : list blk) (LS1 LS2 : lhead -> list aptr) (P : Z -> Z).
Variable ex : option aptr.   (* [comment removed for export] *)
Hypothesis INV1 : INVL X1 st1 L1 BL LS1.
Hypothesis INV2 : INVL X2 st2 L2 BL LS2.
Hypothesis IDLE : x_idle X2 = x_idle X1.
Hypothesis F : FFR st1 st2.
Hypothesis HAQ : AQ st1 BL P.
(* [comment removed for export] *)
Hypothesis S_cls : forall k, In k BL -> exists m i, s_slots st1 !! bslot k = Some (m, i)
      /\ (m_sizeclass (MR st1 m) < 48 -> bsize k < MMAP_THRESHOLD
            /\ m_sizeclass (MR st1 m) - 1 <= size_to_class (bsize k) <= m_sizeclass (MR st1 m) + 1)
      /\ (m_sizeclass (MR st1 m) = 63 -> MMAP_THRESHOLD <= bsize k
            /\ round_up_pg (bsize k + IB + UNIT) <= m_maplen (MR st1 m) * 4096 <= round_up_pg (bsize k + IB + UNIT) + PGSZ).
Hypothesis S_one : forall b m ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> m_last_idx (MR st1 m) = 0 -> m_maplen (MR st1 m) <> 0 ->
      m_sizeclass (MR st1 m) < 48 ->
      m_maplen (MR st1 m) * 4096 <= S_ (m_sizeclass (MR st1 m)) + UNIT
      \/ (34 <= m_sizeclass (MR st1 m) /\ m_maplen (MR st1 m) * 4096 <= round_up_pg (S_ (m_sizeclass (MR st1 m)) + UNIT)).
Hypothesis S_map : forall b m ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st1 m) < 48 -> m_maplen (MR st1 m) <> 0 ->
      m_maplen (MR st1 m) * 4096 <= cnt_of (MR st1 m) * S_ (m_sizeclass (MR st1 m)) + 4111.
Hypothesis S_std : forall b m ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> stdg st1 m = true ->
      (m_maplen (MR st1 m) = 0 <-> std_nested (m_sizeclass (MR st1 m)) = true)
      /\ (m_maplen (MR st1 m) = 0 -> exists p i, s_slots st1 !! b = Some (p, i) /\ m_sizeclass (MR st1 p) = bighost (m_sizeclass (MR st1 m)))
      /\ (m_maplen (MR st1 m) <> 0 -> m_maplen (MR st1 m) * 4096 = std_len (m_sizeclass (MR st1 m))).
Hypothesis S_small : forall c, 0 <= c < 48 -> nsc st1 c < 160.
Hypothesis S_63 : forall b m ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st1 m) = 63 -> Some m <> ex ->
      In (slot_start' (MR st1 m) 0) (map bslot BL).
Hypothesis S_host : forall b m ai p i, s_groups st1 !! b = Some (mkGhdr (Some m) ai) -> m_maplen (MR st1 m) = 0 ->
      s_slots st1 !! b = Some (p, i) -> m_sizeclass (MR st1 p) <= 23.
Hypothesis S_leak : forall m mr, s_metas st1 !! m = Some mr -> m_mem mr = None -> m_next mr <> None \/ In m (x_idle X1).
Hypothesis S_pages : 101 * apages st1 <= ncarved st1 + c_avail_meta_count (s_ctx st1).
Hypothesis S_brk : forall rid r, s_regions st1 !! rid = Some r -> r_kind r = RKBrk -> 101 * (r_len r / PGSZ - 2) <= ncarved st1.
Hypothesis S_len : forall rid r, s_regions st1 !! rid = Some r -> r_kind r = RKMeta ->
      exists j, 1 <= j <= c_meta_alloc_shift (s_ctx st1) /\ r_len r = 2 ^ j * PGSZ.
Hypothesis S_dist : forall rid1 rid2 r1 r2, s_regions st1 !! rid1 = Some r1 -> s_regions st1 !! rid2 = Some r2 ->
      r_kind r1 = RKMeta -> r_kind r2 = RKMeta -> rid1 <> rid2 -> r_len r1 <> r_len r2.
Hypothesis S_shift : 1 <= c_meta_alloc_shift (s_ctx st1) -> 101 * (2 ^ c_meta_alloc_shift (s_ctx st1) - 1) <= 2 * ncarved st1 + 101.
(* [comment removed for export] *)
Hypothesis EXGONE : forall b m ai, ex = Some m -> s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> False.

Let IM2 : inv_M X2 st2 LS2 := proj1 (proj2 (proj2 INV2)).
Let IG2 : inv_G X2 st2 LS2 := proj1 (proj2 (proj2 (proj2 (proj2 INV2)))).
Let IS2 : inv_S X2 st2 BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV2))))).

(* [comment removed for export] *)
#[using="CE X2 L2 BL LS2 INV2 F IM2"] Lemma x_geom m b : hosts st2 b m -> geom (MR st2 m) = geom (MR st1 m).
Proof.
  intros Hh. destruct (ffr_meta _ _ F m) as [E|[Z2 _]]; [exact E|]. exfalso.
  rewrite (hosts_mem _ _ _ IM2 _ _ Hh) in Z2. discriminate.
Qed.

#[using="CE X2 L2 BL LS2 INV2 F IM2"] Lemma x_MR m b : hosts st2 b m ->
  m_mem (MR st2 m) = m_mem (MR st1 m) /\ m_sizeclass (MR st2 m) = m_sizeclass (MR st1 m) /\ m_last_idx (MR st2 m) = m_last_idx (MR st1 m)
  /\ m_maplen (MR st2 m) = m_maplen (MR st1 m) /\ get_stride (MR st2 m) = get_stride (MR st1 m)
  /\ (forall i, slot_start' (MR st2 m) i = slot_start' (MR st1 m) i) /\ cnt_of (MR st2 m) = cnt_of (MR st1 m).
Proof.
  intros Hh. pose proof (x_geom m b Hh) as G. pose proof (geom_stride _ _ G) as S. unfold geom in G. inversion G.
  unfold slot_start', cnt_of. rewrite S, H0, H2. repeat split; auto.
Qed.

(* [comment removed for export] *)
#[using="F"] Lemma x_group b m ai : s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> exists ai1, s_groups st1 !! b = Some (mkGhdr (Some m) ai1).
Proof.
  intros H. destruct (ffr_groups _ _ F _ _ H) as ([gm gai] & H1 & E). cbn in E. subst gm. exists gai. exact H1.
Qed.

(* [comment removed for export] *)
#[using="CE X2 L2 BL LS2 INV2 F IS2"] Lemma x_slot s m i : s_slots st2 !! s = Some (m, i) -> s_slots st1 !! s = Some (m, i) /\ exists b, hosts st2 b m.
Proof.
  intros H. split; [exact (ffr_slots _ _ F _ _ H)|]. destruct (is_valid _ _ _ IS2 _ _ _ H) as ([b Hb] & _). exists b. exact Hb.
Qed.

#[using="CE X2 L2 LS2 INV2 F IM2 IS2"] Lemma x_slotcls k : In k BL -> slotcls st2 (bslot k) = slotcls st1 (bslot k).
Proof.
  intros Hk. destruct (is_blocks _ _ _ IS2 k Hk) as (m & i & Hs & _). unfold slotcls. rewrite Hs.
  destruct (x_slot _ _ _ Hs) as [Hs1 [b Hb]]. rewrite Hs1. unfold cls. destruct (x_MR m b Hb) as (_ & E & _). rewrite E. reflexivity.
Qed.

#[using="F"] Lemma x_gmetas m b : In (m, b) (gmetas st2) -> In (m, b) (gmetas st1) /\ hosts st2 b m.
Proof.
  intros H. apply gmetas_in in H as [ai H]. destruct (x_group _ _ _ H) as [ai1 H1]. split; [apply gmetas_in; exists ai1; exact H1| exists ai; exact H].
Qed.

#[using="Type"] Lemma dec_pair2 : forall x y : aptr * aptr, {x = y} + {x <> y}.
Proof. intros x y. apply (decide (x = y)). Qed.

(* [comment removed for export] *)
#[using="F"] Lemma x_sum_le (F1 F2 : aptr * aptr -> Z) :
  (forall m b, In (m, b) (gmetas st2) -> hosts st2 b m -> F2 (m, b) <= F1 (m, b)) ->
  (forall mb, In mb (gmetas st1) -> 0 <= F1 mb) ->
  zsum (map F2 (gmetas st2)) <= zsum (map F1 (gmetas st1)).
Proof.
  intros HF HP. apply (zsum_inj_le dec_pair2 F2 F1 (fun x => x)); [apply gmetas_nodup| | auto| exact HP].
  intros [m b] Hin. destruct (x_gmetas m b Hin) as [H1 Hh]. split; [exact H1| exact (HF m b Hin Hh)].
Qed.

#[using="CE X1 L1 L2 LS1 LS2 ex INV1 INV2 IDLE F HAQ S_cls S_one S_map S_std S_small S_63 S_host S_leak S_pages S_brk S_len S_dist S_shift EXGONE IM2 IG2 IS2"] Theorem SINV_xfer : SINV X2 st2 BL /\ AQ st2 BL P /\ (forall c, 0 <= c < 48 -> gcnt st2 c <= gcnt st1 c) /\ ncarved st2 = ncarved st1.
Proof.
  pose proof (ncarved_dom st1 st2 (ffr_dom _ _ F)) as NC.
  pose proof INV1 as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  assert (GC : forall c, 0 <= c < 48 -> gcnt st2 c <= gcnt st1 c).
  { intros c Hc. rewrite !gcnt_gmetas. apply x_sum_le.
    - intros m b Hin Hh. cbn. destruct (x_MR m b Hh) as (_ & E2 & _ & _ & _ & _ & E7). rewrite E2, E7. lia.
    - intros [m b] Hin. cbn. destruct (gfacts _ _ _ _ _ INV1 m b Hin) as ([? ?] & _). destruct (_ =? _); lia. }
  assert (NS : forall c, nsc st2 c <= nsc st1 c).
  { intros c. unfold nsc. apply x_sum_le.
    - intros m b Hin Hh. cbn. destruct (x_MR m b Hh) as (_ & E2 & _ & _ & E5 & _ & E7). unfold cls, stdg, cls. rewrite E2, E7, E5. lia.
    - intros [m b] Hin. cbn. destruct (gfacts _ _ _ _ _ INV1 m b Hin) as ([? ?] & _). destruct (_ && _); lia. }
  assert (AP : apages st2 = apages st1).
  { unfold apages, regions_l. rewrite (ffr_regions _ _ F). apply zsum_map_ext. intros [rid r] _. cbn.
    unfold frontier. rewrite (ffr_amas _ _ F). reflexivity. }
  split; [| split; [| split; [exact GC| exact NC]]].
  - constructor.
    + intros k Hk. destruct (is_blocks _ _ _ IS2 k Hk) as (m & i & Hs & _). exists m, i. split; [exact Hs|].
      destruct (x_slot _ _ _ Hs) as [Hs1 [b Hb]]. destruct (x_MR m b Hb) as (_ & E2 & _ & E4 & _).
      destruct (S_cls k Hk) as (m1 & i1 & Hs1' & C1 & C2). rewrite Hs1 in Hs1'. assert (m1 = m) by congruence. subst m1.
      rewrite E2, E4. auto.
    + intros b m ai Hg Hl Hml Hc. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & E2 & E3 & E4 & _).
      rewrite E2, E3, E4 in *. exact (S_one _ _ _ Hg1 Hl Hml Hc).
    + intros b m ai Hg Hc Hml. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & E2 & _ & E4 & _ & _ & E7).
      rewrite E2, E4, E7 in *. exact (S_map _ _ _ Hg1 Hc Hml).
    + intros b m ai Hg SG. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & E2 & _ & E4 & E5 & _ & E7).
      assert (SG1 : stdg st1 m = true) by (unfold stdg, cls in SG |- *; rewrite <- E2, <- E5, <- E7; exact SG).
      destruct (S_std _ _ _ Hg1 SG1) as (Q1 & Q2 & Q3). rewrite E2, E4. split; [exact Q1|]. split; [| exact Q3].
      intros Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG2 _ _ _ Hg) ltac:(rewrite E4; exact Z0)) as (p & i & Hs & _).
      exists p, i. split; [exact Hs|]. destruct (x_slot _ _ _ Hs) as [Hs1 [bp Hp]]. destruct (Q2 Z0) as (p1 & i1 & Hs1' & Ep).
      rewrite Hs1 in Hs1'. assert (p1 = p) by congruence. subst p1. destruct (x_MR p bp Hp) as (_ & Ep2 & _). rewrite Ep2. exact Ep.
    + intros c Hc. pose proof (NS c). pose proof (S_small c Hc). lia.
    + intros b m ai Hg Hc. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & E2 & _ & _ & _ & E6 & _).
      rewrite (E6 0). apply (S_63 _ _ _ Hg1); [rewrite <- E2; exact Hc|]. intros E. exact (EXGONE _ _ _ (eq_sym E) Hg).
    + intros b m ai p i Hg Z0 Hs. destruct (x_group _ _ _ Hg) as [ai1 Hg1]. destruct (x_MR m b (ex_intro _ ai Hg)) as (_ & _ & _ & E4 & _).
      destruct (x_slot _ _ _ Hs) as [Hs1 [bp Hp]]. destruct (x_MR p bp Hp) as (_ & Ep2 & _). rewrite Ep2.
      apply (S_host b m ai1 p i Hg1); [rewrite <- E4; exact Z0| exact Hs1].
    + intros m mr Hm Z0. destruct (ffr_meta _ _ F m) as [G|[_ N2]]; [| left; unfold MR, get_meta_rec in N2; rewrite Hm in N2; exact N2].
      assert (Hm1 : s_metas st1 !! m <> None) by (apply (ffr_dom _ _ F); rewrite Hm; discriminate).
      destruct (s_metas st1 !! m) as [mr1|] eqn:E1; [| congruence].
      unfold geom, MR, get_meta_rec in G. rewrite Hm, E1 in G. cbn in G.
      assert (Z1 : m_mem mr1 = None) by congruence.
      destruct (S_leak m mr1 E1 Z1) as [N1|I1]; [| right; rewrite IDLE; exact I1].
      destruct (ffr_keepq _ _ F m ltac:(unfold MR, get_meta_rec; rewrite E1; exact Z1) ltac:(unfold MR, get_meta_rec; rewrite E1; exact N1)) as [_ N2].
      left. unfold MR, get_meta_rec in N2. rewrite Hm in N2. exact N2.
    + rewrite AP, NC, (ffr_amc _ _ F). exact S_pages.
    + intros rid r Hr K. rewrite NC. rewrite (ffr_regions _ _ F) in Hr. exact (S_brk rid r Hr K).
    + intros rid r Hr K. rewrite (ffr_shift _ _ F). rewrite (ffr_regions _ _ F) in Hr. exact (S_len rid r Hr K).
    + intros rid1 rid2 r1 r2 H1 H2 K1 K2 NE. rewrite (ffr_regions _ _ F) in H1, H2. exact (S_dist _ _ _ _ H1 H2 K1 K2 NE).
    + rewrite (ffr_shift _ _ F), NC. exact S_shift.
  - constructor.
    + exact (aq_live _ _ _ HAQ).
    + intros c Hc. pose proof (GC c Hc). pose proof (aq_slots _ _ _ HAQ c Hc). lia.
    + exact (aq_big _ _ _ HAQ).
    + rewrite NC. exact (aq_carved _ _ _ HAQ).
    + exact (aq_P _ _ _ HAQ).
Qed.
End XFERF.

End WithCeil.
End LB_XferF.

(* [comment removed for export] *)
Module LB_WTry.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WKill. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Bits OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WKill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WNtf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WTry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WTry2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.LB_WNtf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CE : CEIL}.
Section TRYQ.
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

(* [comment removed for export] *)
#[using="HP HF"] Lemma fin_okQ st0 st LS m (mask : Z) :
  INVL X st L BL LS -> TA_frame st0 st sc -> FFR st0 st -> active st sc = Some m -> m_avail (MR st m) = mask -> mask <> 0 ->
  exists st1 first LS1, ta_fin st m mask k = k st1 first /\ TA_POST X L BL sc st0 st1 first LS1 /\ FFR st0 st1.
Proof.
  intros INV TF FF HA AM MNZ. destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4).
  rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|].
  split; [| eapply FFR_trans; [exact FF| apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr]]].
  split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
  right. exists m, bm, ai, (ctz32 (lowbit mask)).
  assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
  assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
  rewrite MRm. destruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
  split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.

#[using="HP HF Hsc"] Theorem try_avail_okQ st LS :
  INVL X st L BL LS ->
  exists st1 first LS1, try_avail sc st k bail = k st1 first /\ TA_POST X L BL sc st st1 first LS1 /\ FFR st st1.
Proof.
  intros INV. unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ eexists _, _, LS. split; [reflexivity|]. split; [split; [apply taf_refl| left; auto]| apply FFR_refl]. }
  fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ exact (fin_okQ st st LS m _ INV (taf_refl st sc) (FFR_refl st) HA eq_refl ANZ). }
  (* [comment removed for export] *)
  assert (STEP1 : exists st1 m1 LS1,
    (if m_freed (MR st m) =? 0
     then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
     else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
    /\ GOODH X st1 L BL LS1 sc m1 /\ (TA_frame st st1 sc /\ FFR st st1)
    \/ (m_freed (MR st m) = 0 /\ active (dequeue (LActive sc) m st) sc = None /\ exists LS1, INVL X (dequeue (LActive sc) m st) L BL LS1)).
  { pose proof (hd_facts X st L BL LS sc m INV HA) as (_ & _ & bm0 & ai0 & Hbm0).
    pose proof (FFR_dequeue_INV X st L BL LS m bm0 sc INV (ex_intro _ ai0 Hbm0) (hd_in X st L BL LS sc m INV HA)) as FD.
    destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
    - destruct (dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ) as (LS1 & rest & INV1 & HL & HA1 & NXT).
      rewrite HA1. destruct rest as [|m1 rest']; cbn.
      + exists st, m, LS. right. split; [exact FZ|]. split; [first [reflexivity| rewrite HA1; reflexivity]| exists LS1; exact INV1].
      + exists (dequeue (LActive sc) m st), m1, LS1. left. split; [reflexivity|]. split; [| split; [apply taf_dequeue| exact FD]].
        destruct (NXT m1 eq_refl) as [A1 F1].
        assert (NE : m1 <> m).
        { intros ->. pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left. }
        pose proof (dequeue_data (LActive sc) m st m1) as D. destruct (data_same _ _ 0 D) as (_ & _ & Ea & Ef & _).
        split; [exact INV1|]. split; [first [reflexivity| rewrite HA1; reflexivity]|]. rewrite Ea, Ef. auto.
    - destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st LS m mn (conj INV (conj HA (conj AZ FNZ))) Hn) as [LS1 G1].
      exists (set_active sc (Some mn) st), mn, LS1. left. split; [reflexivity|]. split; [exact G1| split; [apply taf_set_active| apply (FFR_set_head st (LActive sc))]]. }
  destruct STEP1 as (st1 & m1 & LS1 & [(E1 & G1 & [TF1 FF1])|(FZ & HA1 & LS1' & INV1)]).
  2:{ rewrite (proj2 (Z.eqb_eq _ _) FZ), HA1. eexists _, 0, LS1'. split; [reflexivity|]. split; [split; [apply taf_dequeue| left; auto]|].
      pose proof (hd_facts X st L BL LS sc m INV HA) as (_ & _ & bm0 & ai0 & Hbm0).
      exact (FFR_dequeue_INV X st L BL LS m bm0 sc INV (ex_intro _ ai0 Hbm0) (hd_in X st L BL LS sc m INV HA)). }
  rewrite E1. clear E1.
  (* [comment removed for export] *)
  assert (STEP2 : exists st2 m2 LS2,
    (let mr := get_meta_rec st1 m1 in
     if (m_freed (MR st1 m1) =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0)
     then match m_next mr with Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn)) | None => (st1, m1, m_freed (MR st1 m1)) end
     else (st1, m1, m_freed (MR st1 m1))) = (st2, m2, m_freed (MR st2 m2))
    /\ GOODH X st2 L BL LS2 sc m2 /\ (TA_frame st st2 sc /\ FFR st st2)).
  { cbn zeta. fold (MR st1 m1). destruct (_ && _).
    - pose proof G1 as (INV1 & HA1 & _). destruct (hd_next X st1 L BL LS1 sc m1 INV1 HA1) as (mn & Hn & _). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st1 LS1 m1 mn G1 Hn) as [LS2 G2].
      exists (set_active sc (Some mn) st1), mn, LS2. split; [reflexivity|]. split; [exact G2| split; [eapply taf_trans; [exact TF1| apply taf_set_active]| eapply FFR_trans; [exact FF1| apply (FFR_set_head st1 (LActive sc))]]].
    - exists st1, m1, LS1. auto. }
  destruct STEP2 as (st2 & m2 & LS2 & E2 & G2 & [TF2 FF2]). cbn zeta in E2. fold (MR st1 m1) in E2 |- *.
  match goal with |- context [let '(p, mask) := ?t in _] => change t with (st2, m2, m_freed (MR st2 m2)) end || rewrite E2.
  cbn iota. fold (MR st2 m2).
  destruct G2 as (INV2 & HA2 & AZ2 & FNZ2).
  destruct (hd_facts X st2 L BL LS2 sc m2 INV2 HA2) as (_ & Esc2 & b2 & ai2 & Hb2).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb2) as GO2.
  pose proof (g_masks _ _ _ _ _ _ GO2) as (W1 & W2 & W3 & W4 & W5 & W6). pose proof (g_ai _ _ _ _ _ _ GO2) as AI2. pose proof (g_li _ _ _ _ _ _ GO2) as LI2.
  rewrite (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ (ex_intro _ ai2 Hb2)). cbn [default].
  assert (GAI : group_active_idx st2 b2 = ai2).
  { unfold group_active_idx, get_group. rewrite Hb2. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
  rewrite GAI.
  (* [comment removed for export] *)
  assert (STEP3 : exists st3 m3 LS3 b3 ai3,
    (if Z.land (m_freed (MR st2 m2)) (mask_upto ai2) =? 0
     then if negb (optr_eqb (m_next (MR st2 m2)) (Some m2))
          then match m_next (MR st2 m2) with Some mn => (set_active sc (Some mn) st2, mn) | None => (st2, m2) end
          else (let cnt := ai2 + 2 in
                let size := size_class (m_sizeclass (MR st2 m2)) * UNIT in
                let span := UNIT + size * cnt in
                let cnt := span_loop 300 cnt span size in
                let cnt := if m_last_idx (MR st2 m2) + 1 <? cnt then m_last_idx (MR st2 m2) + 1 else cnt in
                (set_group_active_idx b2 (cnt - 1) st2, m2))
     else (st2, m2)) = (st3, m3)
    /\ GOODH X st3 L BL LS3 sc m3 /\ (TA_frame st st3 sc /\ FFR st st3)
    /\ s_groups st3 !! b3 = Some (mkGhdr (Some m3) ai3) /\ Z.land (m_freed (MR st3 m3)) (mask_upto ai3) <> 0).
  { destruct (Z.eqb_spec (Z.land (m_freed (MR st2 m2)) (mask_upto ai2)) 0) as [LZ|LNZ].
    - (* [comment removed for export] *)
      pose proof (land_mask_upto_zero_above _ _ W2 (proj1 AI2) LZ) as ABOVE.
      assert (PART : ai2 < m_last_idx (MR st2 m2)).
      { destruct (Z.eq_dec (m_freed (MR st2 m2)) 0) as [|NZ]; [contradiction|].
        destruct (Z.lt_ge_cases ai2 (m_last_idx (MR st2 m2))) as [|GE]; [assumption|]. exfalso. apply NZ.
        apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. destruct (Z.testbit (m_freed (MR st2 m2)) i) eqn:E; [| reflexivity].
        pose proof (ABOVE i Hi E). pose proof (W4 i Hi E). lia. }
      destruct (hd_next X st2 L BL LS2 sc m2 INV2 HA2) as (mn & Hn & Hin). rewrite Hn.
      destruct (optr_eqb_spec (Some mn) (Some m2)) as [E|NE]; cbn [negb].
      + (* [comment removed for export] *)
        set (cnt0 := span_loop 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)).
        set (cnt := if m_last_idx (MR st2 m2) + 1 <? cnt0 then m_last_idx (MR st2 m2) + 1 else cnt0).
        pose proof (span_loop_ge 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)) as SL. fold cnt0 in SL.
        assert (CR : ai2 + 1 <= cnt - 1 <= m_last_idx (MR st2 m2)) by (unfold cnt; destruct (Z.ltb_spec (m_last_idx (MR st2 m2) + 1) cnt0); lia).
        unfold set_group_active_idx, get_group. rewrite Hb2. cbn [g_meta].
        replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia).
        set (st3 := Malloc.set_groups _ st2).
        assert (INV3 : INVL X st3 L BL LS2).
        { apply (INVL_set_ai X st2 L BL LS2 m2 b2 ai2 (cnt - 1) INV2 Hb2); [lia| | intros _; rewrite Esc2; exact (hd_in X st2 L BL LS2 sc m2 INV2 HA2)].
          intros i Hi Hb. unfold tbit in Hb. rewrite AZ2, Z.bits_0 in Hb. discriminate. }
        exists st3, m2, LS2, b2, (cnt - 1). split; [reflexivity|].
        split; [split; [exact INV3| split; [exact HA2| auto]]|].
        split.
        { split; [eapply taf_trans; [exact TF2| constructor; auto; try (intros h _; destruct h; reflexivity)]|].
          eapply FFR_trans; [exact FF2|]. unfold st3. constructor; cbn; auto; try tauto.
          intros bb h' Hbb. destruct (aptr_eq_dec bb b2) as [->|NE]; [rewrite lookup_insert_eq in Hbb; inversion Hbb; subst; eexists; split; [exact Hb2| reflexivity]|].
          rewrite lookup_insert_ne in Hbb by congruence. exists h'. auto. }
        split; [unfold st3; cbn; rewrite lookup_insert_eq; reflexivity|].
        change (MR st3 m2) with (MR st2 m2). intros E0.
        assert (Tb : Z.testbit (Z.land (m_freed (MR st2 m2)) (mask_upto (cnt - 1))) (ai2 + 1) = true).
        { rewrite Z.land_spec, testbit_mask_upto by lia. unfold tbit in W6. rewrite (W6 (ai2 + 1)) by lia. cbn. apply Z.leb_le. lia. }
        rewrite E0, Z.bits_0 in Tb. discriminate.
      + (* [comment removed for export] *)
        destruct (rotate_ok X L BL sc HF st2 LS2 m2 mn (conj INV2 (conj HA2 (conj AZ2 FNZ2))) Hn) as [LS3 G3].
        assert (NEm : mn <> m2) by congruence.
        destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV2)))) sc mn Hin) as (_ & [b3 [ai3 Hb3]] & Esc3).
        pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb3) as GO3.
        assert (FULL : ai3 = m_last_idx (MR st2 mn)).
        { pose proof (g_ai _ _ _ _ _ _ GO3) as AI3. destruct (Z.lt_ge_cases ai3 (m_last_idx (MR st2 mn))) as [LT|]; [| lia]. exfalso.
          apply NEm. eapply (ig_onepartial _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2)))))); [exact Hb3| exact Hb2| exact LT| exact PART| congruence]. }
        exists (set_active sc (Some mn) st2), mn, LS3, b3, ai3. split; [reflexivity|]. split; [exact G3|].
        split; [split; [eapply taf_trans; [exact TF2| apply taf_set_active]| eapply FFR_trans; [exact FF2| apply (FFR_set_head st2 (LActive sc))]]|]. split; [exact Hb3|].
        change (MR (set_active sc (Some mn) st2) mn) with (MR st2 mn).
        pose proof (g_masks _ _ _ _ _ _ GO3) as (V1 & V2 & V3 & V4 & V5 & V6).
        pose proof (g_ai _ _ _ _ _ _ GO3) as AI3.
        rewrite (land_mask_upto_all (m_freed (MR st2 mn)) ai3 V2 ltac:(clear -AI3; lia) ltac:(rewrite FULL; exact V4)).
        destruct G3 as (_ & _ & _ & F3). exact F3.
    - exists st2, m2, LS2, b2, ai2. split; [reflexivity|]. split; [split; [exact INV2| auto]|]. auto. }
  destruct STEP3 as (st3 & m3 & LS3 & b3 & ai3 & E3 & G3 & [TF3 FF3] & Hb3 & ACT).
  match goal with |- context [let '(st4, m4) := ?t in _] => change t with (st3, m3) end || rewrite E3.
  cbn iota. clear E3.
  (* [comment removed for export] *)
  destruct G3 as (INV3 & HA3 & AZ3 & FNZ3).
  destruct (hd_facts X st3 L BL LS3 sc m3 INV3 HA3) as (_ & Esc3 & _).
  rewrite (activate_group_eq X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3).
  pose proof (INVL_activate X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3 ltac:(rewrite Esc3; exact (hd_head X st3 L BL LS3 sc m3 INV3 HA3))) as INV4.
  set (st4 := upd_meta m3 _ st3) in INV4 |- *.
  rewrite (guard_true 40) by (apply Bool.negb_true_iff; apply Z.eqb_neq; exact ACT).
  pose proof (INVL_decay_bounces X st4 L BL LS3 (m_sizeclass (get_meta_rec st4 m3)) INV4) as INV5.
  set (st5 := decay_bounces _ st4) in INV5 |- *.
  assert (MR5 : MR st5 m3 = m_set_avail (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) (m_set_freed (Z.ldiff (m_freed (MR st3 m3)) (mask_upto ai3)) (MR st3 m3))).
  { transitivity (MR st4 m3); [unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); reflexivity|]. unfold st4, MR. apply get_meta_rec_upd_same. }
  assert (HA5 : active st5 sc = Some m3) by (unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); exact HA3).
  destruct (fin_okQ st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5) as (st6 & first & LS6 & E6 & POST).
  - eapply taf_trans; [exact TF3|]. eapply taf_trans; [apply taf_upd_meta| apply taf_decay].
  - eapply FFR_trans; [exact FF3|]. apply (FFR_trans st3 st4 st5).
    + unfold st4. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV3))))) _ _ _ Hb3))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr].
    + unfold st5, decay_bounces. destruct (sc_in_seq_range _ && _); [apply FFR_ctx; reflexivity| apply FFR_refl].
  - exact HA5.
  - rewrite MR5. reflexivity.
  - exact ACT.
  - exists st6, first, LS6. split; [exact E6| exact POST].
Qed.
End TRYQ.

End WithCeil.
End LB_WTry.

(* [comment removed for export] *)
Module LB_Tree.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Fixpoint fbnd {R} (B : Z) (L : mled) (t : M R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (EPeek _ _ _) k => forall v, fbnd B L (k v)
  | SVis (EUndef _) _ => True
  | SVis e k => BOUND L e B /\ forall a, answer_ok L e a = true -> fbnd B (event_post L e a) (k a)
  end.

#[using="Type"] Lemma fbnd_ret {R} B L (r : R) : fbnd B L (SRet r).
Proof. exact I. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma fbnd_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) B :
  strel RR t1 t2 -> forall L, fbnd B L t1 -> fbnd B L t2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L H; cbn [fbnd] in *; [exact I|].
  destruct e; try (destruct H as [HB H1]; split; [exact HB|]; intros a Ha; apply IH; apply H1; exact Ha).
  - intros v. apply IH. apply H.
  - exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fbnd_steq {R} (t1 t2 : M R) B : steq t1 t2 -> forall L, fbnd B L t1 -> fbnd B L t2.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros L H; cbn [fbnd] in *; [exact I|].
  destruct e; try (destruct H as [HB H1]; split; [exact HB|]; intros a Ha; apply IH; apply H1; exact Ha).
  - intros v. apply IH. apply H.
  - exact I.
Qed.

(* [comment removed for export] *)
Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).

#[using="Type"] Lemma fbnd_prun {R} B : forall (t : M R) L o, fbnd B L t -> fbnd B L (prun pans pupd o t).
Proof.
  induction t as [r|e k IH]; intros L o H; cbn [fbnd] in *; [exact I|].
  unfold prun. destruct e; cbn [eruns psel]; try (destruct H as [HB Hk]; split; [exact HB|]; intros a Ha; apply IH; apply Hk; exact Ha).
  - apply IH. apply H.
  - exact I.
Qed.
End PRUN.

(* [comment removed for export] *)
#[using="Type"] Lemma qtree_intro {R} B : forall (t : M R) L Post, ctree_ok L t Post -> fbnd B L t -> qtree B L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post HC HB; cbn [ctree_ok fbnd qtree] in *; [exact HC|].
  destruct HC as [He Hk].
  destruct e; try (destruct HB as [HB1 HB2]; split; [exact He|]; split; [exact HB1|]; intros z Hz; apply IH; [apply Hk; exact Hz| apply HB2; exact Hz]);
    cbn in He; destruct He.
Qed.

#[using="Type"] Lemma qtree_elim {R} B : forall (t : M R) L Post, qtree B L t Post -> ctree_ok L t Post /\ fbnd B L t.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ctree_ok fbnd qtree] in *; [split; [exact H| exact I]|].
  destruct H as (He & HB & Hk).
  destruct e; try (cbn in He; destruct He; fail);
    (split; [split; [exact He|]; intros z Hz; apply (IH z _ Post); apply Hk; exact Hz
           | split; [exact HB|]; intros z Hz; apply (IH z _ Post); apply Hk; exact Hz]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma BOUND_mono L e B B' : BOUND L e B -> B <= B' -> BOUND L e B'.
Proof.
  intros [H HR] HB. split; [intros z Hz; specialize (H z Hz); lia| exact HR].
Qed.

#[using="Type"] Lemma fbnd_mono {R} B B' : B <= B' -> forall (t : M R) L, fbnd B L t -> fbnd B' L t.
Proof.
  intros HB. induction t as [r|e k IH]; intros L H; cbn [fbnd] in *; [exact I|].
  destruct e; try (destruct H as [H1 H2]; split; [exact (BOUND_mono H1 HB)|]; intros a Ha; apply IH; apply H2; exact Ha).
  - intros v. apply IH. apply H.
  - exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint fqtree {R} (B : Z) (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> fqtree B L (k v) Post
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ BOUND L e B /\ forall a, if answer_ok L e a then fqtree B (event_post L e a) (k a) Post else rejects (k a)
  end.

#[using="Type"] Lemma fqtree_ftree {R} B (t : M R) : forall L Post, fqtree B L t Post -> ftree L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [fqtree ftree] in *; [exact H|].
  destruct e; try (destruct H as (He & HB & Hk); split; [exact He|]; intros a; specialize (Hk a); case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

(* [comment removed for export] *)
Fixpoint fbnd8 {R} (B : Z) (L : mled) (t : M R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> fbnd8 B L (k v)
  | SVis (EUndef _) _ => True
  | SVis e k => BOUND L e B /\ forall a, answer_ok L e a = true -> fbnd8 B (event_post L e a) (k a)
  end.

#[using="Type"] Lemma fqtree_fbnd8 {R} B (t : M R) : forall L Post, fqtree B L t Post -> fbnd8 B L t.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [fqtree fbnd8] in *; [exact I|].
  destruct e; try (destruct H as (He & HB & Hk); split; [exact HB|]; intros a Ha; specialize (Hk a); rewrite Ha in Hk; apply (IH a _ Post); exact Hk).
  - intros v Hv. apply (IH v _ Post). apply H. exact Hv.
  - exact I.
Qed.

Section PRUN8.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

#[using="Hpans"] Lemma fbnd8_prun {R} B : forall (t : M R) L o, fbnd8 B L t -> fbnd B L (prun pans pupd o t).
Proof.
  induction t as [r|e k IH]; intros L o H; cbn [fbnd8 fbnd] in *; [exact I|].
  unfold prun. destruct e; cbn [eruns psel]; try (destruct H as [HB Hk]; split; [exact HB|]; intros a Ha; apply IH; apply Hk; exact Ha).
  - apply IH. apply H. apply Hpans.
  - exact I.
Qed.
End PRUN8.

(* [comment removed for export] *)
#[using="Type"] Lemma fqtree_ret {R} B L (r : R) Post : Post L r -> fqtree B L (SRet r) Post.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma fqtree_vis {R} B L e (k : Z -> M R) Post :
  is_peek e = false -> is_undef e = false ->
  event_pre L e -> BOUND0 L e B ->
  (forall a, answer_ok L e a = true -> fqtree B (event_post L e a) (k a) Post) ->
  (forall a, answer_ok L e a = false -> rejects (k a)) ->
  REQB e B ->
  fqtree B L (SVis e k) Post.
Proof.
  intros Hp Hu He HB Hk Hr HQ. destruct e; cbn in Hp, Hu; try discriminate; cbn [fqtree]; split; auto; split; try (split; auto; fail);
  try (split; [exact HB| exact HQ]); intros a; case_ans; auto.
Qed.

#[using="Type"] Lemma fqtree_vis_inv {R} B L e (k : Z -> M R) Post :
  fqtree B L (SVis e k) Post -> is_peek e = false ->
  event_pre L e /\ BOUND L e B /\ forall a, answer_ok L e a = true -> fqtree B (event_post L e a) (k a) Post.
Proof.
  intros H Hp. destruct e; cbn in Hp; try discriminate; cbn [fqtree] in H; try (destruct H; fail).
  all: destruct H as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a Ha; specialize (Hk a); rewrite Ha in Hk; exact Hk.
Qed.

#[using="Type"] Lemma fqtree_peek {R} B L p c h (k : Z -> M R) Post :
  (forall v, 0 <= v < 256 -> fqtree B L (k v) Post) -> fqtree B L (SVis (EPeek p c h) k) Post.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma fqtree_mono {R} B (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, fqtree B L t Post -> fqtree B L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [fqtree] in *; [auto|].
  destruct e; try (destruct H as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

#[using="Type"] Lemma fqtree_bind {R S} B (t : M R) (f : R -> M S) Post Q L :
  fqtree B L t Post -> (forall L' r, Post L' r -> fqtree B L' (f r) Q) -> fqtree B L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [fqtree sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk).
    + intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
    + destruct H.
Qed.

#[using="Type"] Lemma fqtree_guard {R} B L tag (c : bool) (k bail : M R) Post :
  c = true -> fqtree B L k Post -> fqtree B L (guard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

#[using="Type"] Lemma fqtree_guard_inv {R} B L tag (c : bool) (k bail : M R) Post :
  fqtree B L (guard tag c k bail) Post -> c = true /\ fqtree B L k Post.
Proof. unfold guard. destruct c; cbn; [auto| intros H; destruct H]. Qed.

#[using="Type"] Lemma fqtree_steq {R} B (t t' : M R) : steq t t' -> forall L P, fqtree B L t P -> fqtree B L t' P.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros L P H; [exact H|].
  destruct e; cbn [fqtree] in H |- *; try exact H.
  5: { intros v Hv. apply IH. apply H. exact Hv. }
  all: destruct H as (He & HB & H3); split; [exact He|]; split; [exact HB|]; intros a; specialize (H3 a); case_ans; [apply IH; exact H3|].
  all: specialize (Hk a); destruct (rejects_inv _ H3) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fqtree_of_ret {R} B L (t : M R) (r : R) Post : t = SRet r -> Post L r -> fqtree B L t Post.
Proof. intros -> H. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fqtree_monoB {R} B B' (t : M R) : B <= B' -> forall L P, fqtree B L t P -> fqtree B' L t P.
Proof.
  intros HB. induction t as [r|e k IH]; intros L P H; cbn [fqtree] in *; [exact H|].
  destruct e; try (destruct H as (He & H1 & H2); split; [exact He|]; split; [exact (BOUND_mono H1 HB)|]; intros a; specialize (H2 a); case_ans; [apply IH; exact H2| exact H2]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CTRL.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

(* [comment removed for export] *)
#[using="Hpans"] Theorem qtree_of_full {R1 R2} (RR : (O * R1)%type -> R2 -> Prop) B (t : M R1) (tc : M R2) L Post (PostC : mled -> R2 -> Prop) o :
  fqtree B L t Post -> strel RR (prun pans pupd o t) tc ->
  (forall L' x r2, RR x r2 -> Post L' (snd x) -> PostC L' r2) ->
  qtree B L tc PostC.
Proof.
  intros FQ REL HP. apply qtree_intro.
  - apply ptree_ctree_ok. eapply (ptree_strel REL); [exact HP|].
    exact (ftree_prun pans pupd Hpans t L Post o (@fqtree_ftree _ B t L Post FQ)).
  - eapply (@fbnd_strel _ _ RR _ tc B REL). apply (fbnd8_prun pans pupd Hpans). exact (@fqtree_fbnd8 _ B t L Post FQ).
Qed.
End CTRL.

(* [comment removed for export] *)
#[using="Type"] Lemma lbytes_event_post_munmap L a len z : (forall g, In g (ld_groups L) -> 0 <= snd g) ->
  gm (event_post L (EMunmap a len) z) + BB (event_post L (EMunmap a len) z) <= gm L + BB L.
Proof.
  intros POS. cbn [event_post]. rewrite BB_set_groups.
  assert (H : forall l, (forall g, In g l -> 0 <= snd g) ->
    fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (g_remove a l)) <= fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) l)).
  { induction l as [|[b l0] l IH]; intros P0; cbn; [lia|]. pose proof (P0 (b, l0) (or_introl eq_refl)) as Hl0. cbn in Hl0.
    destruct (b =? a); cbn.
    - assert (0 <= mmap_len l0) by (unfold mmap_len, page_round_up_Z; rewrite page_size_eq; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
      lia.
    - specialize (IH ltac:(intros g Hg; apply P0; right; exact Hg)). lia. }
  unfold gm. cbn [ld_groups ld_metas set_groups]. specialize (H (ld_groups L) POS). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fbnd8_ret {R} B L (r : R) : fbnd8 B L (SRet r).
Proof. exact I. Qed.

#[using="Type"] Lemma fbnd8_bind {R S} B (t : M R) (f : R -> M S) (Post : mled -> R -> Prop) : forall L,
  fqtree B L t Post -> (forall L' r, Post L' r -> fbnd8 B L' (f r)) -> fbnd8 B L (sbind t f).
Proof.
  induction t as [r|e k IH]; intros L FT Hf; cbn [fbnd8 fqtree sbind] in *.
  - apply Hf. exact FT.
  - destruct e; try (destruct FT as (_ & HB & FK); split; [exact HB|]; intros a Ha; specialize (FK a); rewrite Ha in FK;
      apply IH; [exact FK| exact Hf]).
    + intros v Hv. apply IH; [apply FT; exact Hv| exact Hf].
    + destruct FT.
Qed.

#[using="Type"] Lemma fbnd8_of_fqtree {R} B (t : M R) L Post : fqtree B L t Post -> fbnd8 B L t.
Proof. intros H. exact (@fqtree_fbnd8 _ B t L Post H). Qed.

#[using="Type"] Lemma fbnd8_rd8 {R} B L st q (k : Z -> M R) : (forall v, fbnd8 B L (k v)) -> fbnd8 B L (rd8 st q k).
Proof.
  intros H. unfold rd8. destruct (cell_read _ _) as [v|h]; [apply H|].
  cbn [fbnd8]. intros v Hv. destruct (peek_answer_ok v); [apply H| exact I].
Qed.

#[using="Type"] Lemma fbnd8_rd16 {R} B L st q (k : Z -> M R) : (forall v, fbnd8 B L (k v)) -> fbnd8 B L (rd16 st q k).
Proof. intros H. unfold rd16. apply fbnd8_rd8. intros b0. apply fbnd8_rd8. intros b1. apply H. Qed.

#[using="Type"] Lemma fbnd8_mono {R} B B' : B <= B' -> forall (t : M R) L, fbnd8 B L t -> fbnd8 B' L t.
Proof.
  intros HB. induction t as [r|e k IH]; intros L H; cbn [fbnd8] in *; [exact I|].
  destruct e; try (destruct H as [H1 H2]; split; [exact (BOUND_mono H1 HB)|]; intros a Ha; apply IH; apply H2; exact Ha).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact I.
Qed.

#[using="Type"] Lemma fbnd8_steq {R} (t1 t2 : M R) B : steq t1 t2 -> forall L, fbnd8 B L t1 -> fbnd8 B L t2.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros L H; cbn [fbnd8] in *; [exact I|].
  destruct e; try (destruct H as [HB H1]; split; [exact HB|]; intros a Ha; apply IH; apply H1; exact Ha).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fbnd8_enframe_full B L st g idx n ctr (k : mstate -> aptr -> M (mstate * optr)) :
  (forall st' p, fbnd8 B L (k st' p)) -> fbnd8 B L (enframe_full st g idx n ctr k).
Proof.
  intros Hk. unfold enframe_full, enframe_read_off. apply fbnd8_rd8. intros b3.
  destruct (negb (b3 =? 0)).
  - apply fbnd8_rd16. intros o16. destruct (enframe_at _ _ _ _ _). apply Hk.
  - destruct (enframe_at _ _ _ _ _). apply Hk.
Qed.

Section CTRL8.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

(* [comment removed for export] *)
#[using="Hpans"] Theorem qtree_of_full8 {R1 R2} (RR : (O * R1)%type -> R2 -> Prop) B (t : M R1) (tc : M R2) L Post (PostC : mled -> R2 -> Prop) o :
  ftree L t Post -> fbnd8 B L t -> strel RR (prun pans pupd o t) tc ->
  (forall L' x r2, RR x r2 -> Post L' (snd x) -> PostC L' r2) ->
  qtree B L tc PostC.
Proof.
  intros FT FB REL HP. apply qtree_intro.
  - apply ptree_ctree_ok. eapply (ptree_strel REL); [exact HP|]. exact (ftree_prun pans pupd Hpans t L Post o FT).
  - eapply (@fbnd_strel _ _ RR _ tc B REL). apply (fbnd8_prun pans pupd Hpans). exact FB.
Qed.
End CTRL8.

End WithCeil.
End LB_Tree.

(* [comment removed for export] *)
Module LB_StmtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv MI_TF2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv LB_Quant. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition bigb (n : Z) : Z := if MMAP_THRESHOLD <=? n then round_up_pg (n + IB + UNIT) + PGSZ else 0.

(* [comment removed for export] *)
Definition ROOM (BL : list blk) (P : Z -> Z) (n : Z) : Prop :=
  (n < MMAP_THRESHOLD -> LR BL (size_to_class n) + 1 <= P (size_to_class n))
  /\ (MMAP_THRESHOLD <= n -> n63 BL + 1 <= P 63).

Definition CORE_POSTQ (n : Z) (BL : list blk) (P : Z -> Z) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
  match snd r with
  | None => SINV x0 (fst r) BL /\ AQ (fst r) BL P
  | Some (g, idx) => forall bg off, hosts (fst r) bg g ->
      SINV x0 (fst r) ((((fst bg, sstart (MR (fst r) g) idx), off), n) :: BL)
      /\ AQ (fst r) ((((fst bg, sstart (MR (fst r) g) idx), off), n) :: BL) P
  end.

Definition malloc_core_fq_stmt : Prop :=
  forall st L BL LS P n B,
    INVL x0 st L BL LS -> TF0 st -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
    PHI P + R63 BL + bigb n <= B + 3 * PGSZ -> bigb n <= QMAX ->
    fqtree B L (malloc_core full_lay st n) (CORE_POSTQ n BL P).

End WithCeil.
End LB_StmtA.

(* [comment removed for export] *)
Module MI_Realloc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WGroup. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2 MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WEnframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WEnframe2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
Section HDR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Local Notation R := (MR st).
Let p : aptr := aadd c (UNIT * off).
Let stride := get_stride (R m).
Let start : aptr := aadd bm (UNIT + stride * i).
Let ea : aptr := aadd start (stride - IB).

#[using="off n ai a ar ka BF"] Lemma start_eq : start = c.
Proof.
  subst start stride. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). unfold sstart, aadd.
  rewrite <- (gbase_bm st c off n m bm i ai a ar ka BF). cbn. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition realloc_body (st0 : mstate) (n' : Z) : M (mstate * optr) :=
  let bail := ret (st0, @None aptr) in
  let avail := snd ea - snd p in
  if (n' <=? avail) && (n' <? MMAP_THRESHOLD) && (m_sizeclass (R m) <=? size_to_class n' + 1) then
    ret (havoc p n' (set_size p ea n' i st), Some p)
  else
    let fallback (st1 : mstate) : M (mstate * optr) :=
      '(st2, q) <-- malloc st1 n' ;;
      match q with
      | None => ret (st2, None)
      | Some q => st3 <-- free st2 (Some p) ;; ret (st3, Some q)
      end in
    if (48 <=? m_sizeclass (R m)) && (MMAP_THRESHOLD <=? n') then
      guard 70 (m_sizeclass (R m) =? 63) (
        let base := snd p - snd start in
        let needed := round_up_pg (n' + base + UNIT + IB) in
        let oldlen := m_maplen (R m) * 4096 in
        let rid := fst start in
        if oldlen =? needed then ret (resize63 st rid needed p n' i, Some p)
        else
          SVis (EMremap (conc st (rid, 0)) oldlen needed) (fun r =>
            if negb (mremap_answer_ok st rid (conc st (rid, 0)) oldlen needed r) then bad_answer bail
            else if is_err r then fallback st
            else ret (big_resize st m rid r needed p n' i, Some p)))
        bail
    else fallback st.
End HDR.

(* [comment removed for export] *)
#[using="Type"] Lemma realloc_eq st0 c off n m bm i ai a ar ka n' :
  let st := set_tick (N.succ (s_tick st0)) st0 in
  blk_facts st c off n m bm i ai a ar ka ->
  size_overflows n' = false ->
  realloc st0 (Some (aadd c (UNIT * off))) n' = realloc_body st c off m bm i st0 n'.
Proof.
  intros st BF Hov. unfold realloc. rewrite Hov. fold st.
  rewrite (get_meta_eq st c off n m bm i ai a ar ka BF). cbv beta zeta.
  unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta zeta iota.
  match goal with |- get_nominal_size st ?pp ?e ?k ?b = _ =>
    change (get_nominal_size st pp e k b) with (get_nominal_size st pp (aadd (aadd bm (UNIT + get_stride (MR st m) * i)) (get_stride (MR st m) - IB)) k b) end.
  rewrite (get_nominal_size_eq st c off n m bm i ai a ar ka BF).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma wr8_cells_at q v st rid o :
  r_cells (get_shadow (wr8 q v st) rid) !! o = if aptr_eqb (rid, o) q then Some (Z.land v 255, s_tick st) else r_cells (get_shadow st rid) !! o.
Proof.
  unfold wr8. rewrite get_shadow_upd_shadow. destruct (aptr_eqb_spec (rid, o) q) as [E|NE].
  - rewrite <- E. cbn [fst snd]. rewrite N.eqb_refl. cbn. rewrite lookup_insert_eq. reflexivity.
  - destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn. rewrite lookup_insert_ne; [reflexivity|].
    intros Eo. apply NE. rewrite <- Eo. destruct q; reflexivity.
Qed.
#[using="Type"] Lemma wrs_cells_lastw l : forall st rid o,
  r_cells (get_shadow (wrs l st) rid) !! o =
  match lastw l (rid, o) None with Some w => Some (Z.land w 255, s_tick st) | None => r_cells (get_shadow st rid) !! o end.
Proof.
  induction l as [|[a v] l IH]; intros st rid o; cbn [wrs lastw]; [reflexivity|].
  rewrite IH. replace (s_tick (wr8 a v st)) with (s_tick st) by reflexivity.
  rewrite wr8_cells_at. destruct (aptr_eqb_spec a (rid, o)) as [->|NE].
  - rewrite aptr_eqb_refl. rewrite lastw_acc. destruct (lastw l (rid, o) None); reflexivity.
  - rewrite (aptr_eqb_neq (rid, o) a) by congruence. destruct (lastw l (rid, o) None); reflexivity.
Qed.
#[using="Type"] Lemma lastw_in l : forall q w, lastw l q None = Some w -> In q (map fst l).
Proof.
  induction l as [|[a v] l IH]; intros q w H; cbn in H; [discriminate|].
  cbn. destruct (aptr_eqb_spec a q) as [->|NE]; [left; reflexivity| right; eapply IH; exact H].
Qed.
#[using="Type"] Lemma cell_read_cur (S : mstate) rid o v : TKS S (s_tick S) -> r_cells (get_shadow S rid) !! o = Some (v, s_tick S) ->
  cell_read (get_shadow S rid) o = Known v.
Proof.
  intros TK Hcl. unfold cell_read. rewrite Hcl. rewrite (not_stale_cur _ _ (o mod 16) (sh_ticks_of _ _ TK)). reflexivity.
Qed.

Section RESIZE.
Variables (X1 : extras) (st : mstate) (L : mled) (BL1 : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off : Z) (m bm : aptr) (i ai : Z).
Hypothesis INV1 : INVL X1 st L BL1 LS.
Hypothesis HP1 : x_pend X1 = Some c.
Hypothesis Hhost : s_groups st !! bm = Some (mkGhdr (Some m) ai).
Hypothesis Hslot : s_slots st !! c = Some (m, i).
Local Notation R := (MR st).
Hypothesis Hgb : gbase (R m) = bm.
Hypothesis Hc : c = (fst bm, sstart (R m) i).
Hypothesis Hi : 0 <= i <= m_last_idx (R m).
Hypothesis Hli : m_last_idx (R m) <= 31.
Hypothesis Hoff : 0 <= off <= 255.
Let stride := get_stride (R m).
Hypothesis S16 : 16 <= stride /\ stride mod 16 = 0.
Hypothesis B16 : 0 <= snd bm /\ snd bm mod 16 = 0.
Variable n' : Z.

Let p : aptr := aadd c (UNIT * off).
Let ea : aptr := aadd (aadd bm (UNIT + stride * i)) (stride - IB).
Let res' : Z := stride - IB - UNIT * off - n'.
Let q : Z := (snd c + UNIT * off - snd bm - UNIT) / UNIT.

Let IM := proj1 (proj2 (proj2 INV1)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV1)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).

#[using="Hc"] Lemma ip_c : c = (fst bm, sstart (R m) i). Proof. exact Hc. Qed.
#[using="S16"] Lemma ip_stride : 16 <= stride /\ stride mod 16 = 0. Proof. exact S16. Qed.
#[using="Type"] Lemma ip_p_snd : snd p = snd c + UNIT * off. Proof. reflexivity. Qed.
#[using="Hc"] Lemma ip_ea_fst : fst ea = fst c. Proof. rewrite ip_c. reflexivity. Qed.
#[using="off Hgb Hc n' res' q"] Lemma ip_ea_snd : snd ea = snd c + stride - IB.
Proof. subst ea. rewrite ip_c. unfold aadd, sstart. cbn [snd]. rewrite Hgb. fold stride. lia. Qed.
#[using="Hgb Hc q"] Lemma ip_res : snd ea - snd p - n' = res'. Proof. rewrite ip_ea_snd, ip_p_snd. unfold res'. clear. lia. Qed.
#[using="Hslot"] Lemma ip_slots : s_slots st !! c = Some (m, i). Proof. exact Hslot. Qed.
#[using="CEc X1 L BL1 LS m bm i ai INV1 Hhost Hc IG"] Lemma ip_region : exists r, s_regions st !! (fst c) = Some r /\ r_kind r = RKGroup.
Proof. rewrite ip_c. cbn [fst]. exact (ig_region _ _ _ IG _ _ Hhost). Qed.

(* [comment removed for export] *)
Definition SL : list (aptr * Z) :=
  (if negb (res' =? 0) then [(aadd ea (- res'), 0)] else [])
  ++ (if 5 <=? res' then [(aadd ea (-4), res'); (aadd (aadd ea (-4)) 1, Z.shiftr res' 8); (aadd (aadd ea (-4)) 2, Z.shiftr res' 16); (aadd (aadd ea (-4)) 3, Z.shiftr res' 24); (aadd ea (-5), 0)] else [])
  ++ [(aadd p (-3), Z.land i 31 + Z.shiftl (if 5 <=? res' then 5 else res') 5)].

#[using="Hgb Hc q"] Lemma set_size_eq : set_size p ea n' i st = wrs SL st.
Proof.
  unfold set_size, SL. rewrite ip_res.
  destruct (res' =? 0); cbn beta iota delta [wr32 wrs app negb];
    destruct (5 <=? res'); cbn beta iota delta [wrs app negb]; reflexivity.
Qed.

Definition stw : mstate := wrs SL st.
(* [comment removed for export] *)
Variable hl : Z.
Definition stf : mstate := havoc p hl stw.

#[using="Type"] Lemma stw_ctrl : ctrl_eq st stw /\ s_tick stw = s_tick st. Proof. exact (wrs_ctrl SL st). Qed.
#[using="CEc X1 L BL1 LS INV1 q"] Lemma stw_TKS : TKS stw (s_tick st). Proof. unfold stw. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV1)]. Qed.
#[using="Type"] Lemma stf_ctrl : ctrl_eq st stf /\ s_tick stf = s_tick st.
Proof.
  destruct stw_ctrl as [C T]. destruct (havoc_ctrl p hl stw) as [C' T']. split; [exact (ctrl_eq_trans _ _ _ C C')| rewrite T'; exact T].
Qed.
#[using="st m bm i Hgb Hc Hi Hli stride S16 B16 n' res' q"] Lemma p16 : snd p mod 16 = 0.
Proof.
  rewrite ip_p_snd, ip_c. cbn [snd]. unfold sstart. rewrite Hgb. fold stride.
  destruct S16 as [S1 S2]. destruct B16 as [B1 B2]. unfold UNIT in *.
  pose proof (Z.div_mod stride 16 ltac:(lia)) as H. pose proof (Z.div_mod (snd bm) 16 ltac:(lia)) as H0.
  rewrite S2 in H. rewrite B2 in H0.
  replace (snd bm + 16 + stride * i + 16 * off) with ((snd bm `div` 16 + 1 + (stride `div` 16) * i + off) * 16) by nia.
  apply Z_mod_mult.
Qed.
#[using="CEc X1 L BL1 LS INV1 q"] Lemma stw_hav u hls : r_hav (get_shadow stw (fst p)) !! u = Some hls -> hl_ticks hls (s_tick stw).
Proof.
  intros Hu ch Hch. pose proof stw_TKS as TK. rewrite <- (proj2 stw_ctrl) in TK. exact (proj1 (sh_ticks_of _ _ TK) u hls ch Hu Hch).
Qed.

Hypothesis Hn' : 0 <= n'.
Hypothesis HL1 : n' <= hl.
Hypothesis Hfit : UNIT * off + n' <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n' < 2 ^ 32.
#[using="Hfit"] Lemma ip_res_nonneg : 0 <= res'. Proof. assert (E : res' = stride - IB - UNIT * off - n') by reflexivity. clear -E Hn' Hfit. unfold UNIT, IB in *. lia. Qed.

(* [comment removed for export] *)
#[using="Hgb Hc S16 B16 q Hn' Hfit"] Lemma SL_addrs q0 : In q0 (map fst SL) -> fst q0 = fst c /\ snd p - 3 <= snd q0 < snd ea /\ ~ (snd p <= snd q0 < snd p + n').
Proof.
  intros Hin. pose proof ip_res_nonneg as R0. pose proof ip_res as RE. pose proof ip_ea_fst as EF.
  unfold SL in Hin.
  destruct (Z.eqb_spec res' 0) as [Z0|Z0]; destruct (Z.leb_spec 5 res') as [R5|R5]; cbn [negb app map fst In] in Hin;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
    unfold aadd; cbn [fst snd]; (split; [first [exact EF| reflexivity]| unfold IB, UNIT in *; lia]).
Qed.

#[using="CEc X1 L BL1 LS INV1 Hgb Hc Hi Hli S16 B16 q Hn' HL1"] Lemma stf_read_out q0 : ~ (fst q0 = fst p /\ snd p <= snd q0 < snd p + hl) ->
  cell_read (get_shadow stf (fst q0)) (snd q0) = cell_read (get_shadow stw (fst q0)) (snd q0).
Proof.
  intros Hq. unfold stf. destruct (Z.eq_dec hl 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out p hl stw p16 ltac:(lia) stw_hav). exact Hq.
Qed.

#[using="CEc X1 L BL1 LS INV1 Hgb Hc Hi Hli S16 B16 q Hn' HL1"] Lemma stf_TKS : TKS stf (s_tick st).
Proof.
  unfold stf. destruct (Z.eq_dec hl 0) as [N0|NZ].
  - rewrite havoc_le0 by lia. apply stw_TKS.
  - rewrite <- (proj2 stw_ctrl). apply TKS_havoc; [apply p16| lia| rewrite (proj2 stw_ctrl); apply stw_TKS].
Qed.

(* [comment removed for export] *)
#[using="CEc X1 L BL1 LS INV1 Hgb Hc Hi Hli S16 B16 q Hn' HL1"] Lemma stf_fresh rid o v : r_cells (get_shadow stw rid) !! o = Some (v, s_tick st) -> cell_read (get_shadow stf rid) o = Known v.
Proof.
  intros Hcl. apply cell_read_cur.
  - rewrite (proj2 stf_ctrl). exact stf_TKS.
  - rewrite (proj2 stf_ctrl). unfold stf. destruct (Z.eq_dec hl 0) as [N0|NZ]; [rewrite havoc_le0 by lia; exact Hcl|].
    rewrite (havoc_cells p hl stw ltac:(lia)). exact Hcl.
Qed.

#[using="CEc X1 L BL1 LS INV1 Hgb Hc Hi Hli S16 B16 q Hn' HL1"] Lemma stf_known_w x w :
  lastw SL (fst c, x) None = Some w -> known stf (fst c, x) (Z.land w 255).
Proof.
  intros HL. unfold known, SHd. cbn [fst snd]. apply stf_fresh. unfold stw. rewrite wrs_cells_lastw, HL. reflexivity.
Qed.

#[using="CEc X1 L BL1 LS INV1 Hgb Hc Hi Hli Hoff S16 B16 q Hn' HL1"] Lemma stf_known_old x v : ~ (snd p <= x < snd p + hl) ->
  lastw SL (fst c, x) None = None -> known st (fst c, x) v -> known stf (fst c, x) v.
Proof.
  intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw SL st (fst c, x) (TKS_of _ _ _ _ _ INV1)). rewrite HL. exact K.
Qed.

#[using="Hgb Hc S16 B16 q Hn' Hfit"] Lemma SL_not_in x : snd p <= x < snd p + n' -> ~ In (fst c, x) (map fst SL).
Proof. intros Hx Hin. destruct (SL_addrs _ Hin) as (_ & _ & NR). apply NR. exact Hx. Qed.

(* [comment removed for export] *)
Hypothesis K4 : known st (fst c, snd c + UNIT * off - 4) 0.
Hypothesis K2 : known st (fst c, snd c + UNIT * off - 2) (byte_of q 0).
Hypothesis K1 : known st (fst c, snd c + UNIT * off - 1) (byte_of q 1).
Hypothesis Q : 0 <= q < 2^16.
(* [comment removed for export] *)
Hypothesis TFp : forall sh o v t, s_shadow st !! (fst c) = Some sh -> r_cells sh !! o = Some (v, t) ->
  snd c + UNIT * off <= o < snd c + UNIT * off + n' -> (t < s_tick st)%N.

#[using="CEc X1 L BL1 LS INV1 Hgb Hc Hi Hli S16 B16 q Hn' HL1 Hfit Q TFp"] Lemma stf_unknown x : snd p <= x < snd p + n' -> unknown stf (fst c, x).
Proof.
  intros Hx. unfold unknown, SHd, stf. cbn [fst snd].
  destruct (cell_read_havoc_in p hl stw p16 ltac:(lia) stw_hav (fst c, x) eq_refl ltac:(cbn [fst snd]; lia)) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hcl. unfold stw in Hcl. rewrite wrs_cells_other in Hcl by (apply SL_not_in; exact Hx).
  rewrite (proj2 stw_ctrl). destruct (get_shadow_cells_some st _ _ _ Hcl) as (sh & Hs & Hc'). apply (TFp _ _ _ _ Hs Hc'). rewrite <- ip_p_snd. exact Hx.
Qed.

(* [comment removed for export] *)
Local Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?x ?y] =>
      first [ rewrite (aptr_eqb_neq x y) by (unfold aadd; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq x y)) by (unfold aadd; cbn [fst snd]; unfold IB, UNIT in *; f_equal; try lia; first [exact ip_ea_fst| symmetry; exact ip_ea_fst]) ]
  end.

#[using="CEc X1 L BL1 LS INV1 Hgb Hc Hi Hli Hoff S16 B16 q Hn' HL1 Hfit Hres K4 K2 K1 Q TFp"] Lemma blk_ok : blk_shadow_ok stf ((c, off), n') m i.
Proof.
  pose proof ip_stride as [S16a SM]. destruct stf_ctrl as [CE TK].
  assert (MRE : MR stf m = R m) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof ip_res_nonneg as R0. pose proof ip_res as RE. pose proof ip_ea_snd as EAS. pose proof ip_ea_fst as EAF. pose proof ip_p_snd as PS.
  assert (Eres : res' = stride - IB - UNIT * off - n') by reflexivity.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, Hgb. fold stride.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n') with res' by lia. fold q.
  assert (NP' : forall x, x < snd p -> ~ (snd p <= x < snd p + hl)) by (intros; lia).
  assert (EAD : forall d, aadd ea d = (fst c, snd c + stride - IB + d)) by (intros d; unfold aadd at 1; rewrite EAF, EAS; reflexivity).
  assert (PD : forall d, aadd p d = (fst c, snd c + UNIT * off + d)) by (intros d; reflexivity).
  split; [| split; [| split; [| split; [| split; [exact Q| split; [| split]]]]]].
  - (* [comment removed for export] *) apply stf_known_old; [apply NP'; lia| | exact K4].
    unfold SL. rewrite !EAD, !PD. destruct (negb (res' =? 0)); destruct (5 <=? res'); cbn [lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *)
    replace (i + 32 * Z.min res' 5) with (Z.land (Z.land i 31 + Z.shiftl (if 5 <=? res' then 5 else res') 5) 255).
    2:{ replace (Z.land i 31) with i by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 res').
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply stf_known_w.
    unfold SL. rewrite !EAD, !PD. destruct (negb (res' =? 0)); destruct (5 <=? res'); cbn [lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) apply stf_known_old; [apply NP'; lia| | exact K2].
    unfold SL. rewrite !EAD, !PD. destruct (Z.eqb_spec res' 0); destruct (Z.leb_spec 5 res'); cbn [negb lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) apply stf_known_old; [apply NP'; lia| | exact K1].
    unfold SL. rewrite !EAD, !PD. destruct (Z.eqb_spec res' 0); destruct (Z.leb_spec 5 res'); cbn [negb lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (E5 : (5 <=? res') = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (res' =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact Hres]]]]].
    1-4: apply stf_known_w;
         unfold SL; rewrite E5, EZ, !EAD, !PD; cbn [negb lastw app]; repeat aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stf_known_w _ 0).
    unfold SL; rewrite E5, EZ, !EAD, !PD; cbn [negb lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    apply (stf_known_w _ 0).
    assert (EZ : (res' =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold SL; rewrite EZ, !EAD, !PD. destruct (Z.leb_spec 5 res'); cbn [negb lastw app];
      try (destruct (Z.eq_dec res' 5)); try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros x Hx. apply stf_unknown. rewrite PS. exact Hx.
Qed.

(* [comment removed for export] *)
#[using="CEc X1 L BL1 LS ai INV1 Hhost Hgb Hc S16 B16 q IG Hn' HL1 Hfit Q"] Lemma stf_DOMS : DOMS st stf.
Proof.
  unfold stf. destruct (Z.eq_dec hl 0) as [N0|NZ].
  - rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV1)|]. intros q0 Hin. destruct (SL_addrs q0 Hin) as (F & _). rewrite F. exact ip_region.
  - apply DOMS_havoc; [lia| | unfold p, aadd; cbn [fst]; exact ip_region]. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV1)|]. intros q0 Hin. destruct (SL_addrs q0 Hin) as (F & _). rewrite F. exact ip_region.
Qed.
(* [comment removed for export] *)
#[using="CEc X1 L BL1 LS INV1 Hgb Hc Hi Hli Hoff S16 B16 q Hn' HL1 Hfit Q"] Lemma stf_read_far q0 : ~ inT (fst c) (sstart (R m) i - 3) (sstart (R m) (i + 1) - 4) q0 ->
  ~ (fst q0 = fst p /\ snd p + n' <= snd q0 < snd p + hl) ->
  cell_read (get_shadow stf (fst q0)) (snd q0) = cell_read (get_shadow st (fst q0)) (snd q0).
Proof.
  intros Hq Hq2. pose proof ip_stride as [S16a _]. pose proof ip_ea_snd as EAS. pose proof ip_p_snd as PS.
  assert (Cs : snd c = sstart (R m) i) by (rewrite ip_c; reflexivity).
  assert (NQ : ~ (fst q0 = fst p /\ snd p <= snd q0 < snd p + hl)).
  { intros [F Rg]. destruct (Z.lt_ge_cases (snd q0) (snd p + n')) as [LT|GE]; [| apply Hq2; split; [exact F| lia]].
    apply Hq. unfold inT. split; [rewrite F; reflexivity|]. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
  rewrite (stf_read_out q0 NQ). unfold stw. apply wrs_read_other.
  intros Hin. destruct (SL_addrs q0 Hin) as (F & Rg & _). apply Hq. unfold inT. split; [exact F|]. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia.
Qed.

(* [comment removed for export] *)
#[using="ai INV1 HP1 Hhost Hslot Hgb Hc Hi Hli Hoff S16 B16 q IG Hn' HL1 Hfit Hres K4 K2 K1 Q TFp"] Theorem resize_INVL : snd p + hl <= snd c + stride - IB ->
  INVL (mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1)) stf L (((c, off), n') :: BL1) LS.
Proof.
  intros HLT. destruct stf_ctrl as [CE TK]. pose proof ip_p_snd as PS.
  assert (Cs : snd c = sstart (R m) i) by (rewrite ip_c; reflexivity).
  apply (INVL_add_block X1 st stf L BL1 LS c off n' INV1 HP1 CE TK).
  - intros m2 i2 Hs q0 Hq. rewrite ip_slots in Hs. inversion Hs. subst m2 i2. apply stf_read_far; [exact Hq|].
    intros [F Rg]. apply Hq. split; [rewrite F; reflexivity|]. rewrite sstart_succ, <- Cs. fold stride. unfold UNIT, IB in *. lia.
  - exact stf_DOMS.
  - exact stf_TKS.
  - intros m2 i2 Hs. rewrite ip_slots in Hs. inversion Hs. subst m2 i2.
    split; [exact Hoff|]. split; [exact Hn'|]. split; [exact Hfit| exact blk_ok].
Qed.

(* [comment removed for export] *)
#[using="ai INV1 HP1 Hhost Hslot Hgb Hc Hi Hli Hoff S16 B16 q IG Hn' HL1 Hfit Hres K4 K2 K1 Q TFp"] Theorem resize_INVL_tail : snd p + hl = snd c + stride -> m_maplen (R m) <> 0 -> i = m_last_idx (R m) ->
  r_cells (get_shadow st (fst c)) !! (snd c + stride - IB) = Some (0, s_tick st) ->
  INVL (mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1)) stf L (((c, off), n') :: BL1) LS.
Proof.
  intros HLE TOP LAST E0. destruct stf_ctrl as [CE TK]. pose proof ip_p_snd as PS. pose proof ip_ea_snd as EAS. pose proof ip_ea_fst as EAF.
  assert (Cs : snd c = sstart (R m) i) by (rewrite ip_c; reflexivity).
  apply (INVL_add_block_tail X1 st stf L BL1 LS c off n' INV1 HP1 CE TK).
  - intros m2 i2 Hs. rewrite ip_slots in Hs. inversion Hs. subst m2 i2. split; [exact TOP| exact LAST].
  - intros m2 i2 Hs q0 Hq. rewrite ip_slots in Hs. inversion Hs. subst m2 i2. apply stf_read_far.
    + intros [F Rg]. apply Hq. split; [exact F| lia].
    + intros [F Rg]. apply Hq. split; [rewrite F; reflexivity|]. rewrite sstart_succ, <- Cs. fold stride. unfold UNIT, IB in *. lia.
  - intros m2 i2 Hs. rewrite ip_slots in Hs. inversion Hs. subst m2 i2. rewrite sstart_succ, <- Cs. fold stride.
    rewrite (stf_fresh (fst c) (snd c + stride - 4) 0).
    + symmetry. apply cell_read_cur; [exact (TKS_of _ _ _ _ _ INV1)| exact E0].
    + unfold stw. rewrite wrs_cells_lastw. destruct (lastw SL (fst c, snd c + stride - 4) None) as [w|] eqn:EL; [| exact E0].
      exfalso. pose proof (lastw_in _ _ _ EL) as Hin.
      destruct (SL_addrs _ Hin) as (_ & Rg & _). cbn [snd] in Rg. unfold IB in *. lia.
  - exact stf_DOMS.
  - exact stf_TKS.
  - intros m2 i2 Hs. rewrite ip_slots in Hs. inversion Hs. subst m2 i2.
    split; [exact Hoff|]. split; [exact Hn'|]. split; [exact Hfit| exact blk_ok].
Qed.
End RESIZE.

(* [comment removed for export] *)
Section INPLACE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis NP : x_pend X = None.
Hypothesis Hk : In ((c, off), n) BL.
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Hypothesis TF : TF0 st.
Variable n' : Z.
Hypothesis Hn' : 0 <= n'.
Local Notation R := (MR st).
Let stride := get_stride (R m).
Hypothesis Hfit : UNIT * off + n' <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n' < 2 ^ 32.
Let p : aptr := aadd c (UNIT * off).
Let ea : aptr := aadd (aadd bm (UNIT + stride * i)) (stride - IB).

#[using="n ai a ar ka BF"] Lemma set_size_eq' : set_size p ea n' i st = wrs (SL st c off m bm i n') st.
Proof. apply set_size_eq; [exact (gbase_bm st c off n m bm i ai a ar ka BF)| exact (bf_c _ _ _ _ _ _ _ _ _ _ _ BF)]. Qed.

#[using="n ai a ar ka INV NP Hk BF TF Hn' Hfit Hres"] Theorem inplace_INVL : INVL X (havoc p n' (set_size p ea n' i st)) L (((c, off), n') :: bl_remove c BL) LS.
Proof.
  set (X1 := mkX (x_idle X) (x_zomb X) (Some c) (x_orph X) (x_fresh X)).
  assert (INV1 : INVL X1 st L (bl_remove c BL) LS).
  { change c with (bslot ((c, off), n)). apply (INVL_remove_block X st st L BL LS ((c, off), n) INV Hk NP (ctrl_eq_refl st) eq_refl).
    - intros; reflexivity.
    - exact (DOMS_of _ _ _ _ _ INV).
    - exact (TKS_of _ _ _ _ _ INV). }
  replace X with (mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1)) by (destruct X; cbn; cbn in NP; rewrite NP; reflexivity).
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite (gbase_bm st c off n m bm i ai a ar ka BF) in SH. destruct SH as (K4 & K3 & K2 & K1 & Q & _).
  rewrite set_size_eq'.
  apply (resize_INVL X1 st L (bl_remove c BL) LS c off m bm i ai INV1 eq_refl
           (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) (gbase_bm st c off n m bm i ai a ar ka BF)
           (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) (bf_off _ _ _ _ _ _ _ _ _ _ _ BF)
           (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) n' n' Hn' ltac:(lia) Hfit Hres K4 K2 K1 Q).
  - intros sh o v t Hs Hcl _. exact (TF _ _ _ _ _ Hs Hcl).
  - cbn [aadd snd]. fold stride. unfold UNIT, IB in *. lia.
Qed.
End INPLACE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition realloc_post (st : mstate) (BL : list blk) (c : cptr) (n' : Z) (L' : mled) (r : mstate * optr) : Prop :=
  match snd r with
  | None => exists LS', INVL x0 (fst r) L' BL LS'
  | Some q => exists c' off' LS', q = aadd c' (UNIT * off') /\ 0 <= off' <= 255
      /\ INVL x0 (fst r) L' (((c', off'), n') :: bl_remove c BL) LS' /\ (c' = c \/ ~ In c' (map bslot BL))
  end.

#[using="Type"] Lemma bl_remove_cons_ne c c' off' n' BL : c' <> c -> bl_remove c (((c', off'), n') :: BL) = ((c', off'), n') :: bl_remove c BL.
Proof. intros NE. cbn [bl_remove bslot fst]. destruct (aptr_eqb_spec c' c); [congruence| reflexivity]. Qed.

#[using="Type"] Lemma fallback_ft st L BL LS c off n n' :
  INVL x0 st L BL LS -> In ((c, off), n) BL -> 0 <= n' ->
  ftree L ('(st2, q) <-- malloc st n' ;;
           match q with
           | None => ret (st2, None)
           | Some q => st3 <-- free st2 (Some (aadd c (UNIT * off))) ;; ret (st3, Some q)
           end)
        (realloc_post st BL c n').
Proof.
  intros INV Hk Hn'.
  eapply ftree_bind; [exact (malloc_INVL st L BL LS n' INV Hn')|].
  intros L1 [st2 [q|]] (LIVE & GP1 & RES); cbn [fst snd] in RES.
  - destruct RES as (c' & off' & LS1 & Eq & Hoff & INV1 & Hni).
    assert (NE : c' <> c) by (intros ->; apply Hni; change c with (bslot ((c, off), n)); apply in_map; exact Hk).
    eapply ftree_bind; [exact (free_INVL_closed st2 L1 (((c', off'), n') :: BL) LS1 c off n INV1 ltac:(right; exact Hk))|].
    intros L2 st3 [LS2 INV2]. apply ftree_ret. unfold realloc_post. cbn [fst snd].
    exists c', off', LS2. split; [exact Eq|]. split; [exact Hoff|]. rewrite (bl_remove_cons_ne c c' off' n' BL NE) in INV2. split; [exact INV2| right; exact Hni].
  - destruct RES as (LS1 & INV1). apply ftree_ret. unfold realloc_post. cbn [fst snd]. exists LS1. exact INV1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma stride_small X st L BL LS c off n m bm i ai a ar ka :
  INVL X st L BL LS -> blk_facts st c off n m bm i ai a ar ka -> m_sizeclass (MR st m) < 48 -> get_stride (MR st m) < 2 ^ 20.
Proof.
  intros INV BF Hsc. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
  pose proof (g_stride _ _ _ _ _ _ GO Hsc) as (_ & _ & S3). pose proof (g_li _ _ _ _ _ _ GO) as LI0. pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 _].
  unfold cnt_of in S3. nia.
Qed.

#[using="Type"] Theorem realloc_ft_nobig st0 L BL LS c off n n' :
  INVL x0 st0 L BL LS -> In ((c, off), n) BL -> 0 <= n' -> size_overflows n' = false ->
  (n' < MMAP_THRESHOLD \/ forall m i, s_slots st0 !! c = Some (m, i) -> m_sizeclass (MR st0 m) < 48) ->
  ftree L (realloc st0 (Some (aadd c (UNIT * off))) n') (realloc_post st0 BL c n').
Proof.
  intros INV0 Hk Hn' Hov Hsmall.
  set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (INV : INVL x0 st L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV0]).
  assert (TF : TF0 st) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV0)| cbn; lia]).
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  rewrite (realloc_eq st0 c off n m bm i ai a ar ka n' BF Hov). fold st.
  assert (MRE : MR st m = MR st0 m) by reflexivity.
  assert (SM : n' < MMAP_THRESHOLD \/ m_sizeclass (MR st m) < 48).
  { destruct Hsmall as [H|H]; [left; exact H| right]. rewrite MRE. apply (H m i). pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. exact Hs. }
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 _]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof (ip_ea_snd st c off m bm i (gbase_bm st c off n m bm i ai a ar ka BF) (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) n') as EAS. cbn zeta in EAS.
  unfold realloc_body.
  match goal with |- ftree _ (if ?cnd then _ else _) _ => destruct cnd eqn:EC end.
  - (* [comment removed for export] *)
    apply andb_prop in EC as [EC E3]. apply andb_prop in EC as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3.
    rewrite EAS in E1. cbn [aadd snd] in E1.
    assert (Hsc : m_sizeclass (MR st m) < 48).
    { pose proof (size_to_class_ok n' ltac:(lia)) as [ST _]. destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(H48 & _)|H63]; lia. }
    pose proof (stride_small x0 st L BL LS c off n m bm i ai a ar ka INV BF Hsc) as SS.
    apply ftree_ret. unfold realloc_post. cbn [fst snd]. exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| left; reflexivity].
    apply (inplace_INVL x0 st L BL LS c off n m bm i ai a ar ka INV eq_refl Hk BF TF n' Hn'); unfold IB, UNIT in *; lia.
  - match goal with |- ftree _ (if ?cnd then _ else _) _ => destruct cnd eqn:EB end.
    + exfalso. apply andb_prop in EB as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
    + apply (fallback_ft st L BL LS c off n n' INV Hk Hn').
Qed.

End WithCeil.
End MI_Realloc.
