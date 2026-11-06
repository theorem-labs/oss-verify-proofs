(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 LB_Tables LB_Inv LB_Sum LB_Bound LB_WNtf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ncarved_dom st1 st2 : (forall m, s_metas st2 !! m <> None <-> s_metas st1 !! m <> None) -> ncarved st2 = ncarved st1.
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
            /\ (size_to_class (bsize k) = m_sizeclass (MR st1 m) \/ size_to_class (bsize k) = m_sizeclass (MR st1 m) - 1))
      /\ (m_sizeclass (MR st1 m) = 63 -> MMAP_THRESHOLD <= bsize k /\ m_maplen (MR st1 m) * 4096 = round_up_pg (bsize k + IB + UNIT)).
Hypothesis S_mis : forall c, MIS st1 BL c <= 13.
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
Lemma x_geom m b : hosts st2 b m -> geom (MR st2 m) = geom (MR st1 m).
Proof.
  intros Hh. destruct (ffr_meta _ _ F m) as [E|[Z2 _]]; [exact E|]. exfalso.
  rewrite (hosts_mem _ _ _ IM2 _ _ Hh) in Z2. discriminate.
Qed.

Lemma x_MR m b : hosts st2 b m ->
  m_mem (MR st2 m) = m_mem (MR st1 m) /\ m_sizeclass (MR st2 m) = m_sizeclass (MR st1 m) /\ m_last_idx (MR st2 m) = m_last_idx (MR st1 m)
  /\ m_maplen (MR st2 m) = m_maplen (MR st1 m) /\ get_stride (MR st2 m) = get_stride (MR st1 m)
  /\ (forall i, slot_start' (MR st2 m) i = slot_start' (MR st1 m) i) /\ cnt_of (MR st2 m) = cnt_of (MR st1 m).
Proof.
  intros Hh. pose proof (x_geom m b Hh) as G. pose proof (geom_stride _ _ G) as S. unfold geom in G. inversion G.
  unfold slot_start', cnt_of. rewrite S, H0, H2. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma x_group b m ai : s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> exists ai1, s_groups st1 !! b = Some (mkGhdr (Some m) ai1).
Proof.
  intros H. destruct (ffr_groups _ _ F _ _ H) as ([gm gai] & H1 & E). cbn in E. subst gm. exists gai. exact H1.
Qed.

(* [comment removed for export] *)
Lemma x_slot s m i : s_slots st2 !! s = Some (m, i) -> s_slots st1 !! s = Some (m, i) /\ exists b, hosts st2 b m.
Proof.
  intros H. split; [exact (ffr_slots _ _ F _ _ H)|]. destruct (is_valid _ _ _ IS2 _ _ _ H) as ([b Hb] & _). exists b. exact Hb.
Qed.

Lemma x_slotcls k : In k BL -> slotcls st2 (bslot k) = slotcls st1 (bslot k).
Proof.
  intros Hk. destruct (is_blocks _ _ _ IS2 k Hk) as (m & i & Hs & _). unfold slotcls. rewrite Hs.
  destruct (x_slot _ _ _ Hs) as [Hs1 [b Hb]]. rewrite Hs1. unfold cls. destruct (x_MR m b Hb) as (_ & E & _). rewrite E. reflexivity.
Qed.

Lemma x_gmetas m b : In (m, b) (gmetas st2) -> In (m, b) (gmetas st1) /\ hosts st2 b m.
Proof.
  intros H. apply gmetas_in in H as [ai H]. destruct (x_group _ _ _ H) as [ai1 H1]. split; [apply gmetas_in; exists ai1; exact H1| exists ai; exact H].
Qed.

Lemma dec_pair2 : forall x y : aptr * aptr, {x = y} + {x <> y}.
Proof. intros x y. apply (decide (x = y)). Qed.

(* [comment removed for export] *)
Lemma x_sum_le (F1 F2 : aptr * aptr -> Z) :
  (forall m b, In (m, b) (gmetas st2) -> hosts st2 b m -> F2 (m, b) <= F1 (m, b)) ->
  (forall mb, In mb (gmetas st1) -> 0 <= F1 mb) ->
  zsum (map F2 (gmetas st2)) <= zsum (map F1 (gmetas st1)).
Proof.
  intros HF HP. apply (zsum_inj_le dec_pair2 F2 F1 (fun x => x)); [apply gmetas_nodup| | auto| exact HP].
  intros [m b] Hin. destruct (x_gmetas m b Hin) as [H1 Hh]. split; [exact H1| exact (HF m b Hin Hh)].
Qed.

Theorem SINV_xfer : SINV X2 st2 BL /\ AQ st2 BL P /\ (forall c, 0 <= c < 48 -> gcnt st2 c <= gcnt st1 c) /\ ncarved st2 = ncarved st1.
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
    + intros c. etransitivity; [| apply (S_mis c)]. apply Z.eq_le_incl. unfold MIS. apply zcount_ext. intros k Hk. rewrite (x_slotcls k Hk). reflexivity.
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
