(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (25 recorded proofs replaced by written proofs (cnt_tab_ok, cnt0_of_ge128, bump_big and 22 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Pres3 MI_Pres4 MI_WFree2 MI_Cnt MI_WCreate2 MI_WSlot
  LB_Tables LB_Inv LB_Sum LB_Bound LB_WNtf LB_XferF LB_QM LB_Cnt.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_AG () := "C47Corelib7Classes?RelationClasses9ReflexiveC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC46Stdlib7Sorting;PermutationGPermutation_EquivalenceC35stdpp8fin_maps:map_insertI35stdpp8fin_maps6FinMap00C47Corelib4Init9Datatypes3fstC46Stdlib7Sorting;Permutation>Permutation_inC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC46Stdlib5Lists4List7forallbC59OSSVerify5KrLib4Spec9LB_Tables?forallb_classesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG9cnt_tab_fC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symI47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes4andbK46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc9small_cntC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec9LB_Tables7classesC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203c59OSSVerify5KrLib4Spec5LB_AG:cnt_tab_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt7cnt0_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables4cmaxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4evenC46Stdlib4Bool4Bool<andb_false_rC35stdpp7tactics<f_equal_helpK47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6MI_Cnt4bumpC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec6MI_Cnt3adjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG;nest_host_fC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec6MI_Cnt9cnt0_listC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC59OSSVerify5KrLib4Spec6MI_Cnt7cnt0_inC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG=nest_host_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG4rankC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6LB_Inv6zcountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum=zsum_map_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum<zsum_map_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum>zcount_eq_zsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum9mtl_nodupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum:zcount_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM<MR_of_lookupC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib4Spec5LB_AG5MR_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate23agtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2<agt_MR_otherC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec;MI_WCreate2:agt_groupsC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables2S_C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6LB_Inv4stdgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7bighostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables:std_nestedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7std_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG9aq_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG6aq_oldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG<aq_hosts_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_totalC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapC47Corelib7Classes?RelationClassesFEquivalence_TransitiveC59OSSVerify5KrLib4Spec6LB_Sum:mtl_insertC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_flat_mapC46Stdlib7Sorting;Permutation@Permutation_reflC47Corelib7Classes?RelationClasses<transitivityC59OSSVerify5KrLib4Spec6LB_Inv6gmetasC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7slotclsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG<aq_slots_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound9gmetas_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum9zsum_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG9aq_gmetasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG6aq_sumC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib4Spec5LB_AG<gmetas_hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound;gcnt_gmetasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG;aq_stdg_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3nscC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7ncarvedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate23agGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4zlenC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec6LB_Sum:mtl_deleteC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_lengthC59OSSVerify5KrLib4Spec6LB_Sum>mtl_insert_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate29agt_metasC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec8LB_XferF;ncarved_domC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9is_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG>aq_slotcls_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv2LSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3MISC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5LB_QM2SG00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5LB_QM2QM00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv2AQ00C1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NK47Corelib7Numbers7BinNums1N02C57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posK47Corelib7Numbers7BinNums1Z03c59OSSVerify5KrLib4Spec5LB_AG6aq_MISC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6LB_Cnt;nsc_le_gcntC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG6aq_nscC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5LB_QM2SG01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2;agt_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_usage_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate27agt_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM:apages_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv6apagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5LB_QM2QM01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv2LRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3CAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3n63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4NCAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4PQOKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG7aq_gcntC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6LB_Inv2AQ01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5LB_AG:aq_ncarvedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cnt_tab_f (sc : Z) : bool :=
  (if sc <? 9 then (small_cnt sc 0 <=? 32) && (1 <=? small_cnt sc 0) else true) && (med_cnt (Z.land sc 3) <=? 32) && (1 <=? med_cnt (Z.land sc 3)).
Lemma cnt_tab_ok sc : 0 <= sc < 48 -> (sc < 9 -> 1 <= small_cnt sc 0 <= 32) /\ 1 <= med_cnt (Z.land sc 3) <= 32.
Proof.
  intros Hsc. assert (H : forallb cnt_tab_f classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes _ H sc Hsc) as T. unfold cnt_tab_f in T.
  apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2]. apply Z.leb_le in T2. apply Z.leb_le in T3.
  split; [| lia]. intros H9. replace (sc <? 9) with true in T1 by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in T1 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

(* [comment removed for export] *)
Lemma cnt0_of_ge128 sc u : 0 <= sc < 48 -> 128 <= u -> cnt0_of sc u = cmax sc.
Proof.
  intros Hsc Hu. destruct (cnt_tab_ok sc Hsc) as [S0 M0]. unfold cnt0_of, cmax, S_.
  destruct (Z.ltb_spec sc 9) as [L9|G9].
  - unfold small_cnt_pick. replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; specialize (S0 L9); lia). reflexivity.
  - f_equal. cbn [halve_even]. replace (u <? 4 * med_cnt (Z.land sc 3)) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.

Lemma bump_big size c : 8 <= c -> bump size c = c.
Proof. intros H. unfold bump. replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Lemma adj_small sc size c : adj sc size c = c \/ adj sc size c <= 5.
Proof. unfold adj. repeat (destruct (_ && _); [right; lia|]). left. reflexivity. Qed.

(* [comment removed for export] *)
Definition nest_host_f (sc : Z) : bool :=
  let size := UNIT * size_class sc in
  forallb (fun cnt0 => let cnt1 := bump size cnt0 in
     (PGSZ / 2 <? size * cnt1 + UNIT)
     || (let j := size_to_class (UNIT + cnt1 * size - IB) in (j =? 15) || (j =? 19) || (j =? 23))) (cnt0_list sc).
Lemma nest_host_all : forallb nest_host_f classes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nest_host sc u : 0 <= sc < 48 ->
  let size := UNIT * size_class sc in let cnt1 := bump size (cnt0_of sc u) in
  size * cnt1 + UNIT <= PGSZ / 2 ->
  let j := size_to_class (UNIT + cnt1 * size - IB) in j = 15 \/ j = 19 \/ j = 23.
Proof.
  intros Hsc. cbn zeta. intros HB. pose proof (forallb_classes _ nest_host_all sc Hsc) as T. unfold nest_host_f in T.
  rewrite forallb_forall in T. specialize (T _ (cnt0_in sc u)). cbn zeta in T.
  apply orb_prop in T as [T|T]; [apply Z.ltb_lt in T; lia|].
  apply orb_prop in T as [T|T]; [apply orb_prop in T as [T|T]|]; apply Z.eqb_eq in T; auto.
Qed.

(* [comment removed for export] *)
Definition rank (c : Z) : Z := if c <? 15 then 0 else if c <? 19 then 1 else if c <? 23 then 2 else 3.
Lemma rank_host c j : 0 <= c < j -> (j = 15 \/ j = 19 \/ j = 23) -> rank c + 1 <= rank j <= 3.
Proof. intros Hc Hj. unfold rank. destruct Hj as [->|[->| ->]]; destruct (Z.ltb_spec c 15); destruct (Z.ltb_spec c 19); destruct (Z.ltb_spec c 23); cbn; lia. Qed.
Lemma rank_range c : 0 <= rank c <= 3.
Proof. unfold rank. destruct (c <? 15); [lia|]. destruct (c <? 19); [lia|]. destruct (c <? 23); lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AGTQ.
Variables (X X' : extras) (stI st : mstate) (L L' : mled) (BL : list blk) (LS LS' : lhead -> list aptr) (P : Z -> Z).
Variables (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.
(* [comment removed for export] *)
Hypothesis INV : INVL X stI L BL LS.
Hypothesis INV' : INVL X' st' L' BL LS'.
Hypothesis LKg : s_groups st = s_groups stI.
Hypothesis LKs : s_slots st = s_slots stI.
Hypothesis LKr : s_regions st = s_regions stI.
Hypothesis LKm : forall x, x <> m -> s_metas st !! x = s_metas stI !! x.
Hypothesis LKc : c_avail_meta_count (s_ctx st) = c_avail_meta_count (s_ctx stI) /\ c_avail_meta_areas (s_ctx st) = c_avail_meta_areas (s_ctx stI)
  /\ c_meta_alloc_shift (s_ctx st) = c_meta_alloc_shift (s_ctx stI).
Hypothesis Hm : s_metas st !! m <> None.
Hypothesis HmI : s_metas stI !! m = Some meta0.
Hypothesis Hp : s_groups stI !! p = None.
Hypothesis SGst : SG stI BL.
Hypothesis Q : QM X stI 0.
Hypothesis XI : forall x, In x (x_idle X) -> x = m \/ In x (x_idle X').
Hypothesis HAQ : AQ stI BL P.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis ROOM : gcnt stI sc <= CAP P sc.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis NEWG : m_sizeclass (MR st' m) = sc /\ m_last_idx (MR st' m) = cnt - 1.
Hypothesis QG_map : m_maplen (MR st' m) <> 0 -> m_maplen (MR st' m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots stI !! p = None.
Hypothesis QG_nest : m_maplen (MR st' m) = 0 -> exists g i, s_slots stI !! p = Some (g, i) /\ m_sizeclass (MR stI g) <= 23
   /\ (stdg st' m = true -> m_sizeclass (MR stI g) = bighost sc).
Hypothesis QG_std : stdg st' m = true -> (m_maplen (MR st' m) = 0 <-> std_nested sc = true) /\ (m_maplen (MR st' m) <> 0 -> m_maplen (MR st' m) * 4096 = std_len sc).
Hypothesis QG_small : stdg st' m = false -> gcnt stI sc < 128.

Lemma MR_st x : x <> m -> MR st x = MR stI x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite (LKm x NE). reflexivity. Qed.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let IM' := proj1 (proj2 (proj2 INV')).
Let IG' := proj1 (proj2 (proj2 (proj2 (proj2 INV')))).
Let IS' := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))).

Lemma aq_old x : (exists b, hosts stI b x) -> x <> m /\ MR st' x = MR stI x.
Proof.
  intros [b [aix Hb]]. assert (NE : x <> m).
  { intros ->. pose proof (hosts_mem _ _ _ IM _ _ (ex_intro _ aix Hb)) as MM. rewrite (MR_of_lookup stI m meta0 HmI) in MM. cbn in MM. discriminate. }
  split; [exact NE|]. unfold st'. rewrite agt_MR_other by exact NE. apply MR_st. exact NE.
Qed.

Lemma aq_groups : s_groups st' = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups stI).
Proof. unfold st'. rewrite agt_groups, LKg. reflexivity. Qed.

Lemma aq_hosts_old b x : hosts stI b x -> hosts st' b x.
Proof.
  intros [aix Hb]. exists aix. rewrite aq_groups. rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite Hp in Hb. discriminate.
Qed.

Lemma aq_slots_old s v : s_slots stI !! s = Some v -> s_slots st' !! s = Some v.
Proof.
  intros Hs. destruct v as [x i]. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es).
  destruct (aq_old x (ex_intro _ b Hb)) as [NE MRx].
  pose proof (is_total _ _ _ IS' b x i (aq_hosts_old b x Hb) ltac:(rewrite MRx; exact Hi)) as T. rewrite MRx, <- Es in T. exact T.
Qed.

Lemma aq_gmetas : Permutation (gmetas st') ((m, p) :: gmetas stI).
Proof.
  unfold gmetas, groups_l. rewrite aq_groups.
  etransitivity; [apply Permutation_flat_map; apply mtl_insert; exact Hp|]. cbn. apply Permutation_refl.
Qed.

Lemma aq_stdg_old x : (exists b, hosts stI b x) -> stdg st' x = stdg stI x.
Proof. intros Hx. destruct (aq_old x Hx) as [_ E]. unfold stdg, cls. rewrite E. reflexivity. Qed.

Lemma aq_slotcls_old s : s_slots stI !! s <> None -> slotcls st' s = slotcls stI s.
Proof.
  intros Hs. destruct (s_slots stI !! s) as [[x i]|] eqn:E; [| congruence]. unfold slotcls. rewrite (aq_slots_old _ _ E), E.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & _). destruct (aq_old x (ex_intro _ b Hb)) as [_ MRx]. unfold cls. rewrite MRx. reflexivity.
Qed.

Lemma gmetas_hosts x b : In (x, b) (gmetas stI) -> exists b', hosts stI b' x.
Proof. intros H. apply gmetas_in in H as [aix Hb]. exists b, aix. exact Hb. Qed.

(* [comment removed for export] *)
Lemma aq_sum (F F' : aptr * aptr -> Z) :
  (forall x b, In (x, b) (gmetas stI) -> F' (x, b) = F (x, b)) ->
  zsum (map F' (gmetas st')) = F' (m, p) + zsum (map F (gmetas stI)).
Proof.
  intros HF. rewrite (zsum_map_perm _ _ _ aq_gmetas). cbn [map]. rewrite zsum_cons. f_equal. apply zsum_map_ext. intros [x b] Hin. apply HF. exact Hin.
Qed.
Lemma aq_count (F F' : aptr * aptr -> bool) :
  (forall x b, In (x, b) (gmetas stI) -> F' (x, b) = F (x, b)) ->
  zcount F' (gmetas st') = (if F' (m, p) then 1 else 0) + zcount F (gmetas stI).
Proof. intros HF. rewrite !zcount_eq_zsum. apply (aq_sum (fun x => if F x then 1 else 0)). intros x b Hin. rewrite (HF x b Hin). reflexivity. Qed.

Lemma aq_gcnt c : gcnt st' c = (if sc =? c then cnt else 0) + gcnt stI c.
Proof.
  rewrite !gcnt_gmetas. rewrite (aq_sum (fun mb => if m_sizeclass (MR stI (fst mb)) =? c then cnt_of (MR stI (fst mb)) else 0)).
  - cbn [fst]. destruct NEWG as [E1 E2]. unfold cnt_of. rewrite E1, E2. destruct (sc =? c); lia.
  - intros x b Hin. cbn [fst]. destruct (aq_old x (gmetas_hosts x b Hin)) as [_ E]. rewrite E. reflexivity.
Qed.

Lemma aq_nsc c : nsc st' c = (if (sc =? c) && negb (stdg st' m) then cnt else 0) + nsc stI c.
Proof.
  unfold nsc. rewrite (aq_sum (fun mb => if (cls stI (fst mb) =? c) && negb (stdg stI (fst mb)) then cnt_of (MR stI (fst mb)) else 0)).
  - cbn [fst]. destruct NEWG as [E1 E2]. unfold cls, cnt_of. rewrite E1, E2. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
  - intros x b Hin. cbn [fst]. pose proof (gmetas_hosts x b Hin) as Hx. rewrite (aq_stdg_old x Hx). destruct (aq_old x Hx) as [_ E]. unfold cls. rewrite E. reflexivity.
Qed.

Lemma aq_ncarved : ncarved st' = ncarved stI.
Proof.
  transitivity (ncarved st).
  - destruct (s_metas st !! m) as [r|] eqn:E; [| congruence]. unfold ncarved, st'. rewrite agt_metas. unfold zlen.
    rewrite (Permutation_length (mtl_insert_old (s_metas st) m _ r E)), (Permutation_length (mtl_delete (s_metas st) m r E)). reflexivity.
  - apply ncarved_dom. intros x. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite HmI; split; [congruence| intros _; exact Hm]|]. rewrite (LKm x NE). tauto.
Qed.

Lemma aq_LS c : LB_Inv.LS st' BL c = LB_Inv.LS stI BL c.
Proof.
  unfold LB_Inv.LS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (aq_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.
Lemma aq_MIS c : MIS st' BL c = MIS stI BL c.
Proof.
  unfold MIS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (aq_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.

Theorem agt_quant : SG st' BL /\ QM X' st' 0 /\ AQ st' BL P.
Proof.
  destruct NEWG as [E1 E2].
  assert (GRP' : forall b x aix, s_groups st' !! b = Some (mkGhdr (Some x) aix) -> (x = m /\ b = p) \/ (x <> m /\ s_groups stI !! b = Some (mkGhdr (Some x) aix) /\ MR st' x = MR stI x)).
  { intros b x aix Hb. rewrite aq_groups in Hb. destruct (aptr_eq_dec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. inversion Hb. left. auto.
    - rewrite lookup_insert_ne in Hb by congruence. right. destruct (aq_old x (ex_intro _ b (ex_intro _ aix Hb))) as [NEx MRx]. auto. }
  split; [| split].
  - (* [comment removed for export] *) destruct SGst as [S1 S2 S3 S4 S5 S6 S7]. constructor.
    + intros k Hk. destruct (S1 k Hk) as (x & i & Hs & C1 & C2). exists x, i. split; [exact (aq_slots_old _ _ Hs)|].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _). destruct (aq_old x (ex_intro _ b Hb)) as [_ MRx]. rewrite MRx. auto.
    + intros c. rewrite aq_MIS. apply S2.
    + intros b x aix Hb Hc Hml. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * rewrite E1, E2 in *. unfold cnt_of. rewrite E2. replace (cnt - 1 + 1) with cnt by lia. exact (proj1 (QG_map Hml)).
      * rewrite MRx in *. exact (S3 _ _ _ Hb0 Hc Hml).
    + intros b x aix Hb SD. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * rewrite E1. destruct (QG_std SD) as [Q1 Q3]. split; [exact Q1|]. split; [| exact Q3].
        intros Z0. destruct (QG_nest Z0) as (g & i & Hs & _ & BH). exists g, i. split; [exact (aq_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact (BH SD).
      * rewrite (aq_stdg_old x (ex_intro _ b (ex_intro _ aix Hb0))) in SD. rewrite MRx. destruct (S4 _ _ _ Hb0 SD) as (Q1 & Q2 & Q3).
        split; [exact Q1|]. split; [| exact Q3]. intros Z0. destruct (Q2 Z0) as (g & i & Hs & Eg). exists g, i. split; [exact (aq_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact Eg.
    + intros c Hc. rewrite aq_nsc. specialize (S5 c Hc). destruct (Z.eqb_spec sc c) as [<-|NE]; cbn [andb]; [| lia].
      destruct (stdg st' m) eqn:SD; cbn [negb]; [lia|]. pose proof (QG_small eq_refl). pose proof (nsc_le_gcnt X stI L BL LS INV sc). lia.
    + intros b x aix Hb H63. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite E1 in H63; lia|]. rewrite MRx in *. exact (S6 _ _ _ Hb0 H63).
    + intros b x aix g i Hb Z0 Hs'. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * destruct (QG_nest Z0) as (g0 & i0 & Hs & C23 & _). rewrite (aq_slots_old _ _ Hs) in Hs'. assert (g0 = g) by congruence. subst g0.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact C23.
      * rewrite MRx in Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb0) Z0) as (g0 & i0 & Hs & _).
        rewrite (aq_slots_old _ _ Hs) in Hs'. assert (g0 = g /\ i0 = i) as [-> ->] by (split; congruence).
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact (S7 _ _ _ _ _ Hb0 Z0 Hs).
  - (* [comment removed for export] *) destruct LKc as (C1 & C2 & C3).
    assert (RG' : s_regions st' = s_regions stI) by (unfold st'; rewrite agt_regions; exact LKr).
    assert (AP' : apages st' = apages stI) by (apply apages_ext; [exact RG'| unfold st'; rewrite agt_ctx; cbn; exact C2]).
    assert (CK' : c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx stI)) by (unfold st'; rewrite agt_ctx; cbn; exact C1).
    assert (SH' : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx stI)) by (unfold st'; rewrite agt_ctx; cbn; exact C3).
    destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?RG', ?aq_ncarved, ?AP', ?CK', ?SH'; auto.
    intros x mr Hx Z0. unfold st' in Hx. rewrite agt_metas in Hx. destruct (aptr_eq_dec x m) as [->|NE].
    + rewrite lookup_insert_eq in Hx. inversion Hx. subst mr. exfalso. revert Z0.
      unfold agG, m_set_sizeclass, m_set_freeable, m_set_last_idx, m_set_mem, m_set_freed, m_set_avail. destruct (MR st m). cbn. discriminate.
    + rewrite lookup_insert_ne in Hx by congruence. rewrite (LKm x NE) in Hx.
      destruct (Q1 x mr Hx Z0) as [N0|I0]; [left; exact N0|]. destruct (XI x I0) as [->|I1]; [congruence| right; exact I1].
  - (* [comment removed for export] *) destruct HAQ as [A1 A2 A3 A4 A5]. constructor; auto.
    + intros c Hc. rewrite aq_gcnt. specialize (A2 c Hc). destruct (Z.eqb_spec sc c) as [<-|NE]; lia.
    + rewrite aq_ncarved. exact A4.
Qed.
End AGTQ.
