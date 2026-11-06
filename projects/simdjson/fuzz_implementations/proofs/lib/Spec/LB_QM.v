(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import STree Malloc KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Pres3 MI_Pres4 MI_WFree2 MI_WAMeta
  LB_Tables LB_Inv LB_Sum LB_Bound LB_WNtf LB_XferF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Record SG (st : mstate) (BL : list blk) : Prop := mkSG {
  sg_cls : forall k, In k BL -> exists m i, s_slots st !! bslot k = Some (m, i)
      /\ (m_sizeclass (MR st m) < 48 -> bsize k < MMAP_THRESHOLD
            /\ (size_to_class (bsize k) = m_sizeclass (MR st m) \/ size_to_class (bsize k) = m_sizeclass (MR st m) - 1))
      /\ (m_sizeclass (MR st m) = 63 -> MMAP_THRESHOLD <= bsize k /\ m_maplen (MR st m) * 4096 = round_up_pg (bsize k + IB + UNIT));
  sg_mis : forall c, MIS st BL c <= 13;
  sg_map : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) < 48 -> m_maplen (MR st m) <> 0 ->
      m_maplen (MR st m) * 4096 <= cnt_of (MR st m) * S_ (m_sizeclass (MR st m)) + 4111;
  sg_std : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> stdg st m = true ->
      (m_maplen (MR st m) = 0 <-> std_nested (m_sizeclass (MR st m)) = true)
      /\ (m_maplen (MR st m) = 0 -> exists p i, s_slots st !! b = Some (p, i) /\ m_sizeclass (MR st p) = bighost (m_sizeclass (MR st m)))
      /\ (m_maplen (MR st m) <> 0 -> m_maplen (MR st m) * 4096 = std_len (m_sizeclass (MR st m)));
  sg_small : forall c, 0 <= c < 48 -> nsc st c < 160;
  sg_63 : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) = 63 ->
      In (slot_start' (MR st m) 0) (map bslot BL);
  sg_host : forall b m ai p i, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_maplen (MR st m) = 0 ->
      s_slots st !! b = Some (p, i) -> m_sizeclass (MR st p) <= 23
}.

Record QM (X : extras) (st : mstate) (d : Z) : Prop := mkQM {
  qmm_leak : forall m mr, s_metas st !! m = Some mr -> m_mem mr = None -> m_next mr <> None \/ In m (x_idle X);
  qmm_pages : 101 * apages st <= ncarved st + c_avail_meta_count (s_ctx st) + d;
  qmm_brk : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKBrk -> 101 * (r_len r / PGSZ - 2) <= ncarved st;
  qmm_len : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKMeta ->
      exists j, 1 <= j <= c_meta_alloc_shift (s_ctx st) /\ r_len r = 2 ^ j * PGSZ;
  qmm_dist : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 ->
      r_kind r1 = RKMeta -> r_kind r2 = RKMeta -> rid1 <> rid2 -> r_len r1 <> r_len r2;
  qmm_shift : 1 <= c_meta_alloc_shift (s_ctx st) -> 101 * (2 ^ c_meta_alloc_shift (s_ctx st) - 1) <= 2 * ncarved st + 101
}.

Lemma SINV_split X st BL : SINV X st BL <-> SG st BL /\ QM X st 0.
Proof.
  split.
  - intros S. destruct S. split; constructor; auto. lia.
  - intros [G Q]. destruct G, Q. constructor; auto. lia.
Qed.

Lemma QM_X X X' st d : x_idle X' = x_idle X -> QM X st d -> QM X' st d.
Proof. intros E Q. destruct Q. constructor; auto. rewrite E. auto. Qed.

Lemma QM_mono X st d d' : d <= d' -> QM X st d -> QM X st d'.
Proof. intros Hd Q. destruct Q. constructor; auto. lia. Qed.

Lemma SG_frame st st1 BL :
  s_groups st1 = s_groups st -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) ->
  (forall s m i, s_slots st !! s = Some (m, i) -> exists b, hosts st b m) ->
  SG st BL -> SG st1 BL.
Proof.
  intros EG ES GEO SV S.
  assert (GM : forall m, (exists b, hosts st b m) ->
     m_sizeclass (MR st1 m) = m_sizeclass (MR st m) /\ m_maplen (MR st1 m) = m_maplen (MR st m)
     /\ get_stride (MR st1 m) = get_stride (MR st m) /\ cnt_of (MR st1 m) = cnt_of (MR st m)
     /\ (forall i, slot_start' (MR st1 m) i = slot_start' (MR st m) i) /\ stdg st1 m = stdg st m).
  { intros m Hm. pose proof (GEO m Hm) as G. pose proof (geom_stride _ _ G) as STR. unfold geom in G. inversion G.
    unfold cnt_of, slot_start', stdg, cls, cnt_of. rewrite STR, H0, H1, H2, H3. repeat split; reflexivity. }
  assert (HG : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> exists b', hosts st b' m) by (intros b m ai H; exists b, ai; exact H).
  assert (SCL : forall s, slotcls st1 s = slotcls st s).
  { intros s. unfold slotcls, cls. rewrite ES. destruct (s_slots st !! s) as [[m i]|] eqn:E; [| reflexivity].
    destruct (GM m (SV _ _ _ E)) as (E1 & _). rewrite E1. reflexivity. }
  destruct S as [S1 S2 S3 S4 S5 S6 S7]. constructor.
  - intros k Hk. destruct (S1 k Hk) as (m & i & Hs & C1 & C2). exists m, i. rewrite ES.
    destruct (GM m (SV _ _ _ Hs)) as (E1 & E2 & _). rewrite E1, E2. auto.
  - intros c. etransitivity; [| apply (S2 c)]. apply Z.eq_le_incl. unfold MIS. apply zcount_ext. intros k _. rewrite SCL. reflexivity.
  - intros b m ai Hb. rewrite EG in Hb. destruct (GM m (HG _ _ _ Hb)) as (E1 & E2 & E3 & E4 & _). rewrite E1, E2, E4. exact (S3 _ _ _ Hb).
  - intros b m ai Hb. rewrite EG in Hb. destruct (GM m (HG _ _ _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6). rewrite E6, E1, E2, ES.
    intros SD. destruct (S4 _ _ _ Hb SD) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p & i & Hs & Ep). exists p, i. split; [exact Hs|].
    destruct (GM p (SV _ _ _ Hs)) as (Ep1 & _). rewrite Ep1. exact Ep.
  - intros c Hc. replace (nsc st1 c) with (nsc st c); [exact (S5 c Hc)|].
    unfold nsc, gmetas, groups_l. rewrite EG. apply zsum_map_ext. intros mb Hin.
    apply in_flat_map in Hin as ([b h] & Hbh & Hmb). apply mtl_in in Hbh. destruct h as [[m'|] ai]; cbn in Hmb; [| destruct Hmb].
    destruct Hmb as [Hmb|[]]. subst mb. cbn. unfold cls. destruct (GM m' (HG _ _ _ Hbh)) as (E1 & _ & _ & E4 & _ & E6). rewrite E1, E4, E6. reflexivity.
  - intros b m ai Hb. rewrite EG in Hb. destruct (GM m (HG _ _ _ Hb)) as (E1 & _ & _ & _ & E5 & _). rewrite E1, (E5 0). exact (S6 _ _ _ Hb).
  - intros b m ai p i Hb. rewrite EG in Hb. rewrite ES. intros Z0 Hs. destruct (GM m (HG _ _ _ Hb)) as (_ & E2 & _). rewrite E2 in Z0.
    destruct (GM p (SV _ _ _ Hs)) as (Ep1 & _). rewrite Ep1. exact (S7 _ _ _ _ _ Hb Z0 Hs).
Qed.

Lemma group_bytes_ext st st1 : s_regions st1 = s_regions st -> group_bytes st1 = group_bytes st.
Proof. intros E. unfold group_bytes, regions_l. rewrite E. reflexivity. Qed.
Lemma meta_bytes_ext st st1 : s_regions st1 = s_regions st -> meta_bytes st1 = meta_bytes st.
Proof. intros E. unfold meta_bytes, regions_l. rewrite E. reflexivity. Qed.
Lemma brk_pages_ext st st1 : s_regions st1 = s_regions st -> brk_pages st1 = brk_pages st.
Proof. intros E. unfold brk_pages, regions_l. rewrite E. reflexivity. Qed.
Lemma apages_ext st st1 : s_regions st1 = s_regions st -> c_avail_meta_areas (s_ctx st1) = c_avail_meta_areas (s_ctx st) -> apages st1 = apages st.
Proof. intros E C. unfold apages, regions_l, frontier. rewrite E, C. reflexivity. Qed.
Lemma ncarved_ext st st1 : s_metas st1 = s_metas st -> ncarved st1 = ncarved st.
Proof. intros E. unfold ncarved. rewrite E. reflexivity. Qed.

Lemma ncarved_insert_fresh st m v : s_metas st !! m = None -> ncarved (Malloc.set_metas (<[m := v]> (s_metas st)) st) = ncarved st + 1.
Proof.
  intros H. unfold ncarved. cbn. unfold zlen. rewrite (Permutation_length (mtl_insert (s_metas st) m v H)). cbn. lia.
Qed.
Lemma ncarved_insert_old st m v v0 : s_metas st !! m = Some v0 -> ncarved (Malloc.set_metas (<[m := v]> (s_metas st)) st) = ncarved st.
Proof.
  intros H. unfold ncarved. cbn. unfold zlen. rewrite (Permutation_length (mtl_insert_old (s_metas st) m v v0 H)).
  rewrite (Permutation_length (mtl_delete (s_metas st) m v0 H)). reflexivity.
Qed.
Lemma ncarved_upd_meta_old st m f : s_metas st !! m <> None -> ncarved (upd_meta m f st) = ncarved st.
Proof.
  intros H. destruct (s_metas st !! m) as [v0|] eqn:E; [| congruence].
  unfold upd_meta, put_meta. apply (ncarved_insert_old st m _ v0 E).
Qed.
Lemma ncarved_upd_meta_fresh st m f : s_metas st !! m = None -> ncarved (upd_meta m f st) = ncarved st + 1.
Proof. intros H. unfold upd_meta, put_meta. apply (ncarved_insert_fresh st m _ H). Qed.
Lemma ncarved_nonneg st : 0 <= ncarved st.
Proof. unfold ncarved. apply zlen_nonneg. Qed.

Definition apF (st : mstate) (kr : N * region) : Z := if is_metakind_b (snd kr) then frontier st (fst kr) (snd kr) / PGSZ - 1 else 0.
Lemma apages_msum st : apages st = msum (apF st) (s_regions st).
Proof. reflexivity. Qed.
Definition mbF (kr : N * region) : Z := match r_kind (snd kr) with RKMeta => r_len (snd kr) | _ => 0 end.
Lemma meta_bytes_msum st : meta_bytes st = msum mbF (s_regions st).
Proof. reflexivity. Qed.
Definition bpF (kr : N * region) : Z := match r_kind (snd kr) with RKBrk => r_len (snd kr) / PGSZ | _ => 0 end.
Lemma brk_pages_msum st : brk_pages st = msum bpF (s_regions st).
Proof. reflexivity. Qed.
Definition gbF (kr : N * region) : Z := match r_kind (snd kr) with RKGroup => round_up_pg (r_len (snd kr)) | _ => 0 end.
Lemma group_bytes_msum st : group_bytes st = msum gbF (s_regions st).
Proof. reflexivity. Qed.

Lemma apF_nonneg_inv X st L kr : inv_R X st L -> s_regions st !! fst kr = Some (snd kr) -> 0 <= apF st kr.
Proof.
  intros IR H. unfold apF. destruct kr as [rid r]. cbn in H |- *.
  destruct (is_metakind_b r) eqn:K; [| lia].
  assert (FR : PGSZ <= frontier st rid r).
  { unfold is_metakind_b in K. destruct (r_kind r) eqn:Kr; try discriminate.
    - rewrite (ir_brkfront _ _ _ IR _ _ H Kr). pose proof (ir_shape _ _ _ IR _ _ H) as (_ & _ & _ & _ & _ & MK). destruct (MK ltac:(left; exact Kr)). unfold PGSZ in *. lia.
    - exact (proj1 (proj1 (proj2 (ir_metalen _ _ _ IR _ _ H Kr)))). }
  unfold PGSZ in *. apply Z.lt_le_pred || idtac. assert (1 <= frontier st rid r / 4096) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma apages_adv X st L rid off r :
  inv_R X st L -> c_avail_meta_areas (s_ctx st) = Some (rid, off) -> s_regions st !! rid = Some r -> is_metakind r -> off mod PGSZ = 0 ->
  apages (adv st (rid, off)) = apages st + 1.
Proof.
  intros IR HC Hr MK OM. rewrite !apages_msum.
  change (s_regions (adv st (rid, off))) with (s_regions st).
  rewrite (msum_delete (apF (adv st (rid, off))) (s_regions st) rid r Hr), (msum_delete (apF st) (s_regions st) rid r Hr).
  assert (E : msum (apF (adv st (rid, off))) (delete rid (s_regions st)) = msum (apF st) (delete rid (s_regions st))).
  { apply msum_ext. intros q rq Hq. rewrite lookup_delete_Some in Hq. destruct Hq as [NE _]. unfold apF, frontier, adv. cbn. rewrite HC.
    destruct (N.eqb_spec rid q); [congruence| reflexivity]. }
  rewrite E. unfold apF. cbn [fst snd]. replace (is_metakind_b r) with true.
  2:{ unfold is_metakind_b. destruct MK as [K|K]; rewrite K; reflexivity. }
  unfold frontier, adv. cbn. rewrite HC, N.eqb_refl.
  unfold PGSZ in *. replace ((off + 4096) / 4096) with (off / 4096 + 1); [lia|]. rewrite <- (Z.div_add off 1 4096) by lia. f_equal. all: try lia.
Qed.

Lemma apages_full X st L : inv_R X st L -> c_avail_meta_area_count (s_ctx st) = 0 ->
  apages st = msum (fun kr => if is_metakind_b (snd kr) then r_len (snd kr) / PGSZ - 1 else 0) (s_regions st).
Proof.
  intros IR HC. rewrite apages_msum. apply msum_ext. intros q rq Hq. unfold apF. cbn. rewrite (frontier_full X st L q rq IR HC Hq). reflexivity.
Qed.

Lemma apages_ge_region X st L rid r : inv_R X st L -> s_regions st !! rid = Some r -> is_metakind r ->
  frontier st rid r / PGSZ - 1 <= apages st.
Proof.
  intros IR Hr MK. rewrite apages_msum, (msum_delete (apF st) (s_regions st) rid r Hr).
  assert (NN : 0 <= msum (apF st) (delete rid (s_regions st))).
  { apply msum_nonneg. intros q rq Hq. rewrite lookup_delete_Some in Hq. destruct Hq as [_ Hq]. apply (apF_nonneg_inv X st L (q, rq) IR Hq). }
  unfold apF at 1. cbn [fst snd]. replace (is_metakind_b r) with true; [lia|]. unfold is_metakind_b. destruct MK as [K|K]; rewrite K; reflexivity.
Qed.

Lemma apages_nonneg X st L : inv_R X st L -> 0 <= apages st.
Proof. intros IR. rewrite apages_msum. apply msum_nonneg. intros q rq Hq. apply (apF_nonneg_inv X st L (q, rq) IR Hq). Qed.

Lemma exhausted_shift X st L d : inv_R X st L -> QM X st d ->
  c_avail_meta_area_count (s_ctx st) = 0 -> c_avail_meta_count (s_ctx st) = 0 -> d <= 0 ->
  1 <= c_meta_alloc_shift (s_ctx st) -> 101 * (2 ^ c_meta_alloc_shift (s_ctx st) - 1) <= ncarved st.
Proof.
  intros IR Q HC HK Hd HS.
  destruct (ir_shift _ _ _ IR) as [S0 [SZ|(rid & r & Hr & K & E)]]; [lia|].
  pose proof (apages_ge_region X st L rid r IR Hr ltac:(right; exact K)) as G.
  rewrite (frontier_full X st L rid r IR HC Hr), E in G. unfold PGSZ in G. rewrite Z.div_mul in G by lia.
  pose proof (qmm_pages _ _ _ Q) as QP. rewrite HK in QP. nia.
Qed.

Lemma exhausted_brk X st L d rid r : inv_R X st L -> QM X st d ->
  c_avail_meta_area_count (s_ctx st) = 0 -> c_avail_meta_count (s_ctx st) = 0 -> d <= 0 ->
  s_regions st !! rid = Some r -> r_kind r = RKBrk -> 101 * (r_len r / PGSZ - 1) <= ncarved st.
Proof.
  intros IR Q HC HK Hd Hr K.
  pose proof (apages_ge_region X st L rid r IR Hr ltac:(left; exact K)) as G.
  rewrite (frontier_full X st L rid r IR HC Hr) in G.
  pose proof (qmm_pages _ _ _ Q) as QP. rewrite HK in QP. nia.
Qed.

Lemma MR_of_lookup st x mr : s_metas st !! x = Some mr -> MR st x = mr.
Proof. intros H. unfold MR, get_meta_rec. rewrite H. reflexivity. Qed.

Lemma geom_data' r r' : data_of r' = data_of r -> geom r' = geom r.
Proof. apply geom_data. Qed.

Lemma am_reuse_q X st L BL LS m rest d :
  INVL X st L BL LS -> LS LFree = m :: rest -> QM X st d ->
  let st1 := dequeue LFree m st in
  QM (xidle X (m :: x_idle X)) st1 d /\ ncarved st1 = ncarved st /\ s_regions st1 = s_regions st /\ apages st1 = apages st
  /\ (forall x, data_of (MR st1 x) = data_of (MR st x)).
Proof.
  intros INV HL Q. cbn zeta.
  assert (Hm : In m (LS LFree)) by (rewrite HL; left; reflexivity).
  pose proof (listed_present X st L BL LS INV m LFree Hm) as Pm.
  pose proof (listed_next X st L BL LS INV m LFree Hm) as Nm.
  assert (RG : s_regions (dequeue LFree m st) = s_regions st) by apply s_regions_dequeue.
  assert (AP : apages (dequeue LFree m st) = apages st) by (apply apages_ext; [exact RG| apply c_avail_meta_areas_dequeue]).
  assert (DOM : forall x, s_metas (dequeue LFree m st) !! x <> None <-> s_metas st !! x <> None).
  { intros x. split; [| apply dequeue_keys_mono]. intros H. destruct (dequeue_keys LFree m st x H) as [H'|[->|[Hp|Hn]]]; [exact H'| exact Pm| |].
    - apply (listed_present X st L BL LS INV x LFree). exact (prev_listed X st L BL LS INV LFree m x Hm Hp).
    - apply (listed_present X st L BL LS INV x LFree). exact (next_listed X st L BL LS INV LFree m x Hm Hn). }
  pose proof (ncarved_dom st (dequeue LFree m st) DOM) as NC.
  pose proof (dequeue_data LFree m st) as DD.
  split; [| split; [exact NC| split; [exact RG| split; [exact AP| exact DD]]]].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor.
  - intros x mr Hx Z0. destruct (aptr_eq_dec x m) as [->|NE]; [right; left; reflexivity|].
    assert (Px : s_metas st !! x <> None) by (apply DOM; rewrite Hx; discriminate).
    destruct (s_metas st !! x) as [mr0|] eqn:E0; [| congruence].
    pose proof (DD x) as Dx. rewrite (MR_of_lookup _ _ _ Hx), (MR_of_lookup _ _ _ E0) in Dx. apply data_of_eq in Dx as (Em & _).
    destruct (Q1 x mr0 E0 ltac:(congruence)) as [N0|I0]; [| right; right; exact I0]. left.
    pose proof (dequeue_next LFree m st x) as DN. rewrite (MR_of_lookup _ _ _ Hx), (MR_of_lookup _ _ _ E0) in DN.
    rewrite DN. destruct (aptr_eqb_spec x m) as [E|_]; [congruence|].
    destruct (optr_eqb (m_next (MR st m)) (Some m)); [exact N0|]. destruct (optr_eqb (m_prev (MR st m)) (Some x)); [exact Nm| exact N0].
  - rewrite AP, NC, c_avail_meta_count_dequeue. exact Q2.
  - rewrite RG, NC. exact Q3.
  - rewrite RG, c_meta_alloc_shift_dequeue. exact Q4.
  - rewrite RG. exact Q5.
  - rewrite c_meta_alloc_shift_dequeue, NC. exact Q6.
Qed.

Lemma carve_rest_q s p :
  s_regions (carve_rest s p) = s_regions s /\ s_metas (carve_rest s p) = s_metas s
  /\ c_avail_meta_areas (s_ctx (carve_rest s p)) = c_avail_meta_areas (s_ctx s)
  /\ c_avail_meta_count (s_ctx (carve_rest s p)) = NSLOTS
  /\ c_meta_alloc_shift (s_ctx (carve_rest s p)) = c_meta_alloc_shift (s_ctx s)
  /\ c_avail_meta_area_count (s_ctx (carve_rest s p)) = c_avail_meta_area_count (s_ctx s).
Proof. unfold carve_rest. destruct (c_meta_area_tail (ctx s)); cbn; repeat split; reflexivity. Qed.

Lemma QM_carve_rest X s p d : QM X s d -> c_avail_meta_count (s_ctx s) = 0 -> d <= 101 -> QM X (carve_rest s p) 0.
Proof.
  intros Q HC Hd. destruct (carve_rest_q s p) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof (ncarved_ext s (carve_rest s p) R2) as NC. pose proof (apages_ext s (carve_rest s p) R1 R3) as AP.
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?R1, ?R2, ?R4, ?R5, ?NC, ?AP; auto.
  rewrite HC in Q2. unfold NSLOTS. lia.
Qed.

Lemma QM_adv X st L rid off r d : inv_R X st L -> c_avail_meta_areas (s_ctx st) = Some (rid, off) ->
  s_regions st !! rid = Some r -> is_metakind r -> off mod PGSZ = 0 ->
  QM X st d -> QM X (adv st (rid, off)) (d + 101).
Proof.
  intros IR HC Hr MK OM Q. pose proof (apages_adv X st L rid off r IR HC Hr MK OM) as AP.
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; cbn -[adv apages ncarved]; auto.
  change (ncarved (adv st (rid, off))) with (ncarved st). change (c_avail_meta_count (s_ctx (adv st (rid, off)))) with (c_avail_meta_count (s_ctx st)). rewrite AP. lia.
Qed.

Definition take_st (st : mstate) (m : aptr) : mstate :=
  upd_meta m (fun r => m_set_prev None (m_set_next None r))
    (upd_ctx (fun c => set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st).

Lemma am_take_unfold {T} st m (k : mstate -> optr -> M T) bail :
  c_avail_meta (s_ctx st) = Some m -> am_take st k bail = k (take_st st m) (Some m).
Proof. intros H. unfold am_take, ctx. rewrite H. reflexivity. Qed.

Lemma take_fresh X st L BL LS m : INVL X st L BL LS -> 0 < c_avail_meta_count (s_ctx st) -> c_avail_meta (s_ctx st) = Some m ->
  s_metas st !! m = None.
Proof.
  intros INV HC Hm. destruct (ia_avail _ (proj1 (proj2 INV))) as [A1 A2]. destruct (A2 HC) as (a & _ & Ea & FREE).
  rewrite Hm in Ea. inversion Ea. apply FREE. lia.
Qed.

Lemma QM_take X st m d : s_metas st !! m = None -> QM X st d ->
  QM (xidle X (m :: x_idle X)) (take_st st m) d /\ ncarved (take_st st m) = ncarved st + 1
  /\ s_regions (take_st st m) = s_regions st /\ apages (take_st st m) = apages st
  /\ (forall x, x <> m -> MR (take_st st m) x = MR st x).
Proof.
  intros Hm Q.
  assert (NC : ncarved (take_st st m) = ncarved st + 1).
  { unfold take_st. rewrite ncarved_upd_meta_fresh; [reflexivity|]. rewrite s_metas_upd_ctx. exact Hm. }
  assert (RG : s_regions (take_st st m) = s_regions st) by reflexivity.
  assert (AP : apages (take_st st m) = apages st) by (apply apages_ext; reflexivity).
  assert (MRx : forall x, x <> m -> MR (take_st st m) x = MR st x).
  { intros x NE. unfold take_st, MR. rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x m); [congruence|]. reflexivity. }
  split; [| auto].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?RG, ?NC, ?AP; auto.
  - intros x mr Hx Z0. unfold take_st in Hx. rewrite lookup_metas_upd in Hx. destruct (aptr_eqb_spec x m) as [->|NE].
    + right. left. reflexivity.
    + rewrite s_metas_upd_ctx in Hx. destruct (Q1 x mr Hx Z0) as [N0|I0]; [left; exact N0| right; right; exact I0].
  - unfold take_st. cbn -[apages ncarved take_st]. rewrite <- RG at 1 || idtac. cbn in Q2 |- *. lia.
  - intros rid r Hr K. specialize (Q3 rid r Hr K). lia.
  - intros HS. specialize (Q6 HS). cbn in HS, Q6 |- *. lia.
Qed.

Lemma msum_regions_insert_fresh (F : N * region -> Z) st rid r :
  s_regions st !! rid = None -> msum F (<[rid := r]> (s_regions st)) = F (rid, r) + msum F (s_regions st).
Proof. intros H. apply msum_insert. exact H. Qed.

Section NEWMETA_Q.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r : Z) (d : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Hypothesis HK : c_avail_meta_count (s_ctx st) = 0.
Hypothesis Q : QM X st d.
Hypothesis Hd : d <= 0.
Let n : Z := Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)).
Let len : Z := n * PGSZ.
Let rid := s_next_rid st.
Let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                              (set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (rid, PGSZ)) c)))
                   (fst (new_region RKMeta r len st)).

Lemma nmq_regions : s_regions st2 = <[rid := mkRegion RKMeta r len]> (s_regions st).
Proof. reflexivity. Qed.

Lemma QM_new_meta :
  QM X st2 0 /\ ncarved st2 = ncarved st /\ apages st2 = apages st /\ group_bytes st2 = group_bytes st
  /\ meta_bytes st2 = meta_bytes st + len /\ brk_pages st2 = brk_pages st /\ (forall x, MR st2 x = MR st x)
  /\ c_meta_alloc_shift (s_ctx st2) = c_meta_alloc_shift (s_ctx st) + 1
  /\ (1 <= c_meta_alloc_shift (s_ctx st) -> 101 * (2 ^ c_meta_alloc_shift (s_ctx st) - 1) <= ncarved st).
Proof.
  pose proof (proj1 INV) as IR. pose proof (nm_fresh X st L BL LS INV) as FR. fold rid in FR.
  destruct (nm_n X st L BL LS INV) as [En N2]. fold n in En, N2.
  pose proof (proj1 (ir_shift _ _ _ IR)) as S0.
  assert (NC : ncarved st2 = ncarved st) by reflexivity.
  assert (MRx : forall x, MR st2 x = MR st x) by reflexivity.
  assert (SH : c_meta_alloc_shift (s_ctx st2) = c_meta_alloc_shift (s_ctx st) + 1) by reflexivity.
  assert (EX : 1 <= c_meta_alloc_shift (s_ctx st) -> 101 * (2 ^ c_meta_alloc_shift (s_ctx st) - 1) <= ncarved st).
  { intros HS. exact (exhausted_shift X st L d IR Q Hcnt HK Hd HS). }
  assert (AP : apages st2 = apages st).
  { rewrite !apages_msum, nmq_regions, (msum_regions_insert_fresh _ st rid _ FR).
    assert (Z0 : apF st2 (rid, mkRegion RKMeta r len) = 0).
    { unfold apF. cbn [fst snd is_metakind_b r_kind]. unfold frontier. cbn. fold rid. rewrite N.eqb_refl. reflexivity. }
    rewrite Z0, Z.add_0_l. apply msum_ext. intros q rq Hq. unfold apF. cbn [fst snd].
    rewrite (frontier_full X st L q rq IR Hcnt Hq). unfold frontier. cbn. fold rid.
    destruct (N.eqb_spec rid q) as [<-|]; [rewrite FR in Hq; discriminate| reflexivity]. }
  assert (GB : group_bytes st2 = group_bytes st).
  { rewrite !group_bytes_msum, nmq_regions, (msum_regions_insert_fresh _ st rid _ FR). unfold gbF at 1. cbn. lia. }
  assert (MB : meta_bytes st2 = meta_bytes st + len).
  { rewrite !meta_bytes_msum, nmq_regions, (msum_regions_insert_fresh _ st rid _ FR). unfold mbF at 1. cbn. lia. }
  assert (BP : brk_pages st2 = brk_pages st).
  { rewrite !brk_pages_msum, nmq_regions, (msum_regions_insert_fresh _ st rid _ FR). unfold bpF at 1. cbn. lia. }
  split; [| repeat split; auto].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor.
  - intros m mr Hm. exact (Q1 m mr Hm).
  - rewrite AP, NC. change (c_avail_meta_count (s_ctx st2)) with (c_avail_meta_count (s_ctx st)). lia.
  - intros q rq Hq K. rewrite NC. rewrite nmq_regions in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. inversion Hq. subst rq. cbn in K. discriminate.
    + rewrite lookup_insert_ne in Hq by congruence. exact (Q3 q rq Hq K).
  - intros q rq Hq K. rewrite SH. rewrite nmq_regions in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. inversion Hq. subst rq. cbn. exists (c_meta_alloc_shift (s_ctx st) + 1). split; [lia|].
      unfold len. rewrite En. reflexivity.
    + rewrite lookup_insert_ne in Hq by congruence. destruct (Q4 q rq Hq K) as (j & Hj & E). exists j. split; [lia| exact E].
  - intros q1 q2 r1 r2 H1 H2 K1 K2 NE. rewrite nmq_regions in H1, H2.
    assert (OLD : forall q rq, s_regions st !! q = Some rq -> r_kind rq = RKMeta -> r_len rq < len).
    { intros q rq Hq K. destruct (Q4 q rq Hq K) as (j & Hj & E). rewrite E. unfold len. rewrite En.
      apply Z.mul_lt_mono_pos_r; [unfold PGSZ; lia|]. apply Z.pow_lt_mono_r; lia. }
    destruct (N.eq_dec q1 rid) as [->|NE1]; destruct (N.eq_dec q2 rid) as [->|NE2]; try congruence.
    + rewrite lookup_insert_eq in H1. inversion H1. subst r1. rewrite lookup_insert_ne in H2 by congruence. cbn. pose proof (OLD _ _ H2 K2). lia.
    + rewrite lookup_insert_eq in H2. inversion H2. subst r2. rewrite lookup_insert_ne in H1 by congruence. cbn. pose proof (OLD _ _ H1 K1). lia.
    + rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (Q5 _ _ _ _ H1 H2 K1 K2 NE).
  - rewrite SH, NC. intros _. pose proof (ncarved_nonneg st) as N0.
    destruct (Z.lt_ge_cases (c_meta_alloc_shift (s_ctx st)) 1) as [LT|GE].
    + assert (E0 : c_meta_alloc_shift (s_ctx st) = 0) by lia. rewrite E0. cbn. lia.
    + specialize (EX GE). rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.
End NEWMETA_Q.

Section BRKGROW_Q.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z) (d : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkLive rid off.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Hypothesis HK : c_avail_meta_count (s_ctx st) = 0.
Hypothesis Q : QM X st d.
Hypothesis Hd : d <= 0.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st.
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c))) st1.
Let st3 := adv st2 (rid, off).

Lemma QM_brk_grow :
  QM X st3 101 /\ ncarved st3 = ncarved st /\ apages st3 = apages st + 1 /\ group_bytes st3 = group_bytes st
  /\ meta_bytes st3 = meta_bytes st /\ brk_pages st3 = brk_pages st + 1 /\ (forall x, MR st3 x = MR st x)
  /\ c_avail_meta_count (s_ctx st3) = 0 /\ 101 * (off / PGSZ - 1) <= ncarved st.
Proof.
  pose proof (proj1 INV) as IR.
  destruct (bg_region X st L BL LS rid off INV Hbrk) as (r & Hr & K & Elen & _ & _ & B0 & BM & OM & O2 & _).
  pose proof (bg_lookup st rid off) as LK. fold st1 st2 st3 in LK.
  assert (RG : s_regions st3 = <[rid := mkRegion RKBrk (r_base r) (off + PGSZ)]> (s_regions st)).
  { apply map_eq. intros q. rewrite LK. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite lookup_insert_eq, Hr; cbn; rewrite K; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. }
  assert (MS : s_metas st3 = s_metas st) by (unfold st3, adv, st2; rewrite !s_metas_upd_ctx; unfold st1; apply s_metas_upd_region).
  assert (CX : s_ctx st1 = s_ctx st) by (unfold st1; apply s_ctx_upd_region).
  assert (NC : ncarved st3 = ncarved st) by (unfold ncarved; rewrite MS; reflexivity).
  assert (MRx : forall x, MR st3 x = MR st x) by (intros x; unfold MR, get_meta_rec; rewrite MS; reflexivity).
  assert (EXB : 101 * (off / PGSZ - 1) <= ncarved st).
  { rewrite <- Elen. exact (exhausted_brk X st L d rid r IR Q Hcnt HK Hd Hr K). }
  assert (CUR : c_avail_meta_areas (s_ctx st3) = Some (rid, off + 4096)).
  { unfold st3, adv, st2. rewrite !s_ctx_upd_ctx. reflexivity. }
  assert (FR3 : forall q rq, frontier st3 q rq = if (rid =? q)%N then off + 4096 else r_len rq) by (intros q rq; unfold frontier; rewrite CUR; reflexivity).
  assert (AP : apages st3 = apages st + 1).
  { rewrite !apages_msum, RG, (msum_insert_old _ (s_regions st) rid _ r Hr).
    rewrite (msum_delete (apF st3) (s_regions st) rid r Hr), (msum_delete (apF st) (s_regions st) rid r Hr).
    assert (E2 : msum (apF st3) (delete rid (s_regions st)) = msum (apF st) (delete rid (s_regions st))).
    { apply msum_ext. intros q rq Hq. rewrite lookup_delete_Some in Hq. destruct Hq as [NE Hq]. unfold apF. cbn [fst snd].
      rewrite (frontier_full X st L q rq IR Hcnt Hq), FR3. destruct (N.eqb_spec rid q); [congruence| reflexivity]. }
    rewrite E2. unfold apF. cbn [fst snd]. replace (is_metakind_b r) with true by (unfold is_metakind_b; rewrite K; reflexivity).
    cbn [is_metakind_b r_kind r_len]. rewrite (frontier_full X st L rid r IR Hcnt Hr), Elen, !FR3, N.eqb_refl.
    unfold PGSZ. replace ((off + 4096) / 4096) with (off / 4096 + 1) by (rewrite <- (Z.div_add off 1 4096) by lia; f_equal; lia). lia. }
  assert (GB : group_bytes st3 = group_bytes st).
  { rewrite !group_bytes_msum, RG, (msum_insert_old _ (s_regions st) rid _ r Hr). unfold gbF at 1 3. cbn [fst snd r_kind]. rewrite K. lia. }
  assert (MB : meta_bytes st3 = meta_bytes st).
  { rewrite !meta_bytes_msum, RG, (msum_insert_old _ (s_regions st) rid _ r Hr). unfold mbF at 1 3. cbn [fst snd r_kind]. rewrite K. lia. }
  assert (BP : brk_pages st3 = brk_pages st + 1).
  { rewrite !brk_pages_msum, RG, (msum_insert_old _ (s_regions st) rid _ r Hr). unfold bpF at 1 3. cbn [fst snd r_kind r_len]. rewrite K, Elen.
    unfold PGSZ. replace ((off + 4096) / 4096) with (off / 4096 + 1) by (rewrite <- (Z.div_add off 1 4096) by lia; f_equal; lia). lia. }
  assert (CK : c_avail_meta_count (s_ctx st3) = 0) by (unfold st3, adv, st2; rewrite !s_ctx_upd_ctx; cbn; rewrite CX; exact HK).
  assert (CS : c_meta_alloc_shift (s_ctx st3) = c_meta_alloc_shift (s_ctx st)) by (unfold st3, adv, st2; rewrite !s_ctx_upd_ctx; cbn; rewrite CX; reflexivity).
  split; [| repeat split; auto].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?MS, ?NC, ?AP, ?CK, ?CS.
  - exact Q1.
  - rewrite HK in Q2. lia.
  - intros q rq Hq Kq. rewrite RG in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. inversion Hq. subst rq. cbn [r_len].
      unfold PGSZ in *. replace ((off + 4096) / 4096) with (off / 4096 + 1) by (rewrite <- (Z.div_add off 1 4096) by lia; f_equal; lia). lia.
    + rewrite lookup_insert_ne in Hq by congruence. exact (Q3 q rq Hq Kq).
  - intros q rq Hq Kq. rewrite RG in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. inversion Hq. subst rq. cbn in Kq. discriminate.
    + rewrite lookup_insert_ne in Hq by congruence. exact (Q4 q rq Hq Kq).
  - intros q1 q2 r1 r2 H1 H2 K1 K2 NE. rewrite RG in H1, H2.
    destruct (N.eq_dec q1 rid) as [->|NE1]; [rewrite lookup_insert_eq in H1; inversion H1; subst r1; cbn in K1; discriminate|].
    destruct (N.eq_dec q2 rid) as [->|NE2]; [rewrite lookup_insert_eq in H2; inversion H2; subst r2; cbn in K2; discriminate|].
    rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (Q5 _ _ _ _ H1 H2 K1 K2 NE).
  - exact Q6.
Qed.
End BRKGROW_Q.

Section BRKFIRST_Q.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (cur : Z) (d : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkUntried.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Hypothesis HK : c_avail_meta_count (s_ctx st) = 0.
Hypothesis Q : QM X st d.
Hypothesis Hd : d <= 0.
Let base : Z := round_up_pg cur.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKBrk base (2 * PGSZ) st).
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c))) st1.
Let st3 := adv st2 (rid, PGSZ).

Lemma QM_brk_first :
  QM X st3 101 /\ ncarved st3 = ncarved st /\ apages st3 = apages st + 1 /\ group_bytes st3 = group_bytes st
  /\ meta_bytes st3 = meta_bytes st /\ brk_pages st3 = brk_pages st + 2 /\ (forall x, MR st3 x = MR st x)
  /\ c_avail_meta_count (s_ctx st3) = 0 /\ brk_pages st = 0.
Proof.
  pose proof (proj1 INV) as IR.
  pose proof (bf_fresh X st L BL LS cur INV) as FR. fold rid in FR.
  pose proof (bf_nobrk X st L BL LS INV Hbrk) as NB.
  assert (RG : s_regions st3 = <[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)) by reflexivity.
  assert (NC : ncarved st3 = ncarved st) by reflexivity.
  assert (MRx : forall x, MR st3 x = MR st x) by reflexivity.
  assert (FR3 : forall q rq, frontier st3 q rq = if (rid =? q)%N then PGSZ + 4096 else r_len rq) by (intros; reflexivity).
  assert (AP : apages st3 = apages st + 1).
  { rewrite !apages_msum, RG, (msum_regions_insert_fresh _ st rid _ FR).
    assert (E2 : msum (apF st3) (s_regions st) = msum (apF st) (s_regions st)).
    { apply msum_ext. intros q rq Hq. unfold apF. cbn [fst snd]. rewrite (frontier_full X st L q rq IR Hcnt Hq), FR3.
      destruct (N.eqb_spec rid q) as [<-|]; [rewrite FR in Hq; discriminate| reflexivity]. }
    rewrite E2. unfold apF. cbn [fst snd is_metakind_b r_kind r_len]. rewrite FR3, N.eqb_refl. unfold PGSZ. cbn. lia. }
  assert (GB : group_bytes st3 = group_bytes st).
  { rewrite !group_bytes_msum, RG, (msum_regions_insert_fresh _ st rid _ FR). unfold gbF at 1. cbn. lia. }
  assert (MB : meta_bytes st3 = meta_bytes st).
  { rewrite !meta_bytes_msum, RG, (msum_regions_insert_fresh _ st rid _ FR). unfold mbF at 1. cbn. lia. }
  assert (BP0 : brk_pages st = 0).
  { rewrite brk_pages_msum. unfold msum. transitivity (zsum (map (fun _ : N * region => 0) (map_to_list (s_regions st)))); [| rewrite zsum_map_const; lia].
    apply zsum_map_ext. intros [q rq] Hq. apply mtl_in in Hq. unfold bpF. cbn. destruct (r_kind rq) eqn:Kq; try reflexivity. exfalso. exact (NB q rq Hq Kq). }
  assert (BP : brk_pages st3 = brk_pages st + 2).
  { rewrite !brk_pages_msum, RG, (msum_regions_insert_fresh _ st rid _ FR). unfold bpF at 1. cbn [fst snd r_kind r_len]. unfold PGSZ. rewrite Z.div_mul by lia. lia. }
  assert (CK : c_avail_meta_count (s_ctx st3) = 0) by (cbn; exact HK).
  split; [| repeat split; auto].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?NC, ?AP, ?CK.
  - exact Q1.
  - rewrite HK in Q2. lia.
  - intros q rq Hq Kq. rewrite RG in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. inversion Hq. subst rq. cbn [r_len]. unfold PGSZ. rewrite Z.div_mul by lia. pose proof (ncarved_nonneg st). lia.
    + rewrite lookup_insert_ne in Hq by congruence. exact (Q3 q rq Hq Kq).
  - intros q rq Hq Kq. change (c_meta_alloc_shift (s_ctx st3)) with (c_meta_alloc_shift (s_ctx st)). rewrite RG in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. inversion Hq. subst rq. cbn in Kq. discriminate.
    + rewrite lookup_insert_ne in Hq by congruence. exact (Q4 q rq Hq Kq).
  - intros q1 q2 r1 r2 H1 H2 K1 K2 NE. rewrite RG in H1, H2.
    destruct (N.eq_dec q1 rid) as [->|NE1]; [rewrite lookup_insert_eq in H1; inversion H1; subst r1; cbn in K1; discriminate|].
    destruct (N.eq_dec q2 rid) as [->|NE2]; [rewrite lookup_insert_eq in H2; inversion H2; subst r2; cbn in K2; discriminate|].
    rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (Q5 _ _ _ _ H1 H2 K1 K2 NE).
  - exact Q6.
Qed.
End BRKFIRST_Q.
