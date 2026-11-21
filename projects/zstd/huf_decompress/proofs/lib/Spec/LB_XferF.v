(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (10 recorded proofs replaced by written proofs (ncarved_dom, x_geom, x_MR and 7 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 LB_Tables LB_Inv LB_Sum LB_Bound LB_WNtf.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_XferF () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp;fin_map_dom;elem_of_domC47Corelib4Init5Logic8eq_ind_rC35stdpp;fin_map_dom8size_domC47Corelib4Init9Datatypes3fstC35stdpp9decidable;prod_eq_decC35stdpp8fin_sets?set_size_properC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_mapsBlength_map_to_listC35stdpp4sets9set_equivC35stdpp4base7elem_ofC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4gmap4gsetC35stdpp4gmap=gset_elementsC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp6option@not_eq_None_SomeC35stdpp4base7is_SomeC35stdpp4base3domC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C35stdpp4gmap8gset_domI47Corelib4Init9Datatypes6option00C35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC47Corelib4Init5Logic3iffC35stdpp8fin_maps8map_sizeC35stdpp4base4sizeC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes6lengthK47Corelib4Init5Logic2eq01C35stdpp8fin_sets8set_sizeC35stdpp4gmap<gset_elem_ofC35stdpp4gmap:gset_emptyC35stdpp4gmap>gset_singletonC35stdpp4gmap:gset_unionC35stdpp4gmapAgset_intersectionC35stdpp4gmap?gset_differenceC35stdpp4gmap<gset_fin_setC35stdpp4setsBset_equiv_instanceC35stdpp4base5equivC35stdpp4gmap=gset_dom_specC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6LB_Inv7ncarvedC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC47Corelib7Classes?RelationClasses8symmetryI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_SymmetricI59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decI47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic3and00C47Corelib7Classes?RelationClasses?iff_equivalenceC59OSSVerify5KrLib4Spec6LB_Sum;zsum_inj_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum:zcount_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf8ffr_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf4geomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec8LB_XferF6x_geomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf;geom_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1N01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf:ffr_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf9ffr_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6MI_Inv9is_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6LB_Inv7slotclsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3clsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_XferF6x_slotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_XferF4x_MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv6gmetasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound9gmetas_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_XferF7x_groupC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec8LB_Bound<gmetas_nodupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_XferF8x_gmetasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_XferF9dec_pair2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf7ffr_domC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_XferF;ncarved_domC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv4SINV00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv2AQ00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec8LB_Bound6gfactsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib4Spec8LB_XferF8x_sum_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound;gcnt_gmetasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables4cmaxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables2S_C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6LB_Inv3nscC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv=is_metakind_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf8ffr_amasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum<zsum_map_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf;ffr_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv6apagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib7Classes?RelationClassesCPreOrder_TransitiveC59OSSVerify5KrLib4Spec6LB_Inv3MISC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_XferF9x_slotclsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:eq_le_inclC47Corelib7Classes?RelationClasses<transitivityC59OSSVerify5KrLib4Spec6LB_Inv4stdgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables:std_nestedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7std_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7bighostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf9ffr_keepqC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf7ffr_amcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf9ffr_shiftC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6LB_Inv4SINV01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7aq_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv8aq_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3CAPC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec6LB_Inv6aq_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4NCAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv9aq_carvedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4aq_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv5aq_pqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6LB_Inv2AQ01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith6BinInt1Z;le_preorderK47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~".
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
    + exact (aq_pq _ _ _ HAQ).
Qed.
End XFERF.
