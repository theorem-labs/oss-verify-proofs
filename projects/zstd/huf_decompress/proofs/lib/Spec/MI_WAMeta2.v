(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (INVL_am_init, am_take_ft, am_carve_ft and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WAMeta2 () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init9Datatypes3sndC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps<lookup_emptyC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4gmap:gmap_emptyI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WAMeta27am_initC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I59OSSVerify5KrLib4Spec9MI_WAMeta8AM_frame00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ia_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC35stdpp4base5emptyI47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc:set_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC46Stdlib5Lists4List6filterC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indK59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec7MI_Ext29inv_M_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext29inv_L_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext2<group_ok_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext29inv_S_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext;inv_SH_viewC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC56Stdlib6NArith6BinNat1N2leK59OSSVerify5KrLib4Spec9MI_WAMeta8AM_frame01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec9MI_WAMeta8amf_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N;le_preorderC59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree9ftree_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta:am_take_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta;am_carve_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9am_finishC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<am_after_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9MI_WAMeta7L_frame00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres35xidleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta9amf_transC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta:INVL_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta:carve_restC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WAMeta2:am_take_ftC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv9ir_cursorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta<ma_event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta3advC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta=INVL_meta_advC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9bump_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9MI_WAMeta7L_frame01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WAMeta2;am_carve_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree7rejectsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic5proj2K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta<nm_event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7lrangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_LedgerAmmap_answer_ok_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta=INVL_new_metaC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC35stdpp8fin_maps:map_insertK59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WAMeta2<am_finish_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_brkphC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6shiftlK59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_meta_alloc_shiftC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv=lbrk_pages_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WAMeta2<INVL_am_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>brk0_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres46xfreshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4<INVL_dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List4fupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4=dequeue_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7im_idleC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec7MI_List<dequeue_headC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec6MI_Inv6ir_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib4Spec9MI_WFree2;round_up_geC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec6Malloc=brk_answer_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WAMeta2Albrk_pages_ok_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<brk_pages_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_Ledger?brk_pages_ok_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9brk_quietC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta>INVL_brk_firstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDmmap_fixed_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta=INVL_brk_deadC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WAMeta2?am_after_brk_ftC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>andb_false_iffC46Stdlib4Bool4Bool=orb_false_iffC46Stdlib4Bool4Bool>negb_false_iffK59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta<bg_event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8ir_shapeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ir_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta9bg_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta=INVL_brk_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4Spec6MI_Inv8ia_availC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8MI_Pres4=ctx_but_heads00C1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z6inj_leK59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<lhead_eq_decC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec4KInv4MAPFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv5MAPFXC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_init (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

Lemma INVL_am_init X st L BL LS : INVL X st L BL LS ->
  INVL X (am_init st) L BL LS /\ c_init_done (s_ctx (am_init st)) = 1 /\ AM_frame st (am_init st).
Proof.
  intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). unfold am_init, ctx.
  destruct (ia_secret _ IA) as [S0 [(I0 & C0 & A0)|(I1 & C1)]].
  - rewrite I0. cbn. set (st' := upd_ctx _ st).
    split; [| split; [reflexivity| constructor; cbn; auto; first [reflexivity| lia]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; try assumption.
    + destruct IA; constructor; try assumption.
      * cbn. split; [exact S0|]. right. auto.
      * intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. rewrite A0 in Ha. rewrite lookup_empty in Ha. discriminate.
    + apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
    + apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
      intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
    + apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
    + apply (inv_SH_view st st'); try reflexivity. exact ISH.
  - rewrite I1. cbn. split; [exact INV|]. split; [exact I1| apply amf_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM.
Variables (T : Type) (BL : list blk) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled).
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 (Some m)) Post.

Lemma am_take_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_count (s_ctx st) -> ftree L (am_take st k bail) Post.
Proof.
  intros INV AF LF HC. destruct (am_take_ok X st L BL LS INV HC k bail) as (m & st2 & -> & INV2 & AF2 & NI).
  eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| exact LF].
Qed.

Lemma am_carve_ft s p L LS : INVL X s L BL LS ->
  c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
  AM_frame st0 s -> L_frame L0 L -> ftree L (am_take (carve_rest s p) k bail) Post.
Proof.
  intros INV H1 H2 H3 H4 H5 H6 AF LF. destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  eapply am_take_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC].
Qed.

Lemma am_finish_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 ->
  ftree L (am_finish st true k bail) Post.
Proof.
  intros INV AF LF HC HI.
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply ftree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| |].
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_ft; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')|].
      destruct LF; constructor; assumption.
    + eapply KN; [exact INV| exact AF| exact LF].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

Lemma am_after_brk_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  c_init_done (s_ctx st) = 1 -> ftree L (am_after_brk st true k bail) Post.
Proof.
  intros INV AF LF HI. unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - apply ftree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| |].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply KN; [exact INV| exact AF| exact LF].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        eapply am_finish_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI].
Qed.

Lemma lbrk_pages_ok_ext L1 L2 lo len :
  ld_resv L1 = ld_resv L2 -> ld_groups L1 = ld_groups L2 -> ld_metas L1 = ld_metas L2 -> ld_brkreg L1 = ld_brkreg L2 ->
  ld_atop L1 = ld_atop L2 ->
  lbrk_pages_ok L1 lo len = lbrk_pages_ok L2 lo len.
Proof. intros E1 E2 E3 E4 E5. unfold lbrk_pages_ok, lranges. rewrite E1, E2, E3, E4, E5. reflexivity. Qed.

Theorem alloc_meta_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> ftree L (alloc_meta st k bail) Post.
Proof.
  intros INV0 AF0 LF.
  destruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF. clear AF0 AFi INV0.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  (* [comment removed for export] *)
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
    eapply KS; [exact INV1| | | exact LF].
    { intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
    eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
    all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
              destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
    all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
    all: try (intros rid r H _; rewrite F1; exact H).
    all: rewrite ?F3; lia. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia]. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  - (* [comment removed for export] *)
    destruct IBK as [BP NB].
    apply ftree_vis; [reflexivity| reflexivity| left; auto| |].
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply ftree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| |].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply ftree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| |].
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (KInv.set_brkph (BPGuard cur) (KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
           destruct LF; constructor; assumption.
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead (KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - (* [comment removed for export] *) eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI].
  - (* [comment removed for export] *)
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
        destruct LF; constructor; assumption.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AM.
