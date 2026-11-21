(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (INVL_set_tick, small_stride, malloc_small_ft and 3 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2
  MI_WSlot MI_WSlot2 MI_WSlot3 MI_WEnframe MI_WEnframe2 MI_Bits.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WMalloc () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~C35stdpp4base6ElemOfC35stdpp4base4fmapC35stdpp4base6LookupI35stdpp4base<list_elem_of00C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list9NoDup_nilC35stdpp4base?list_elem_of_InI35stdpp4base5NoDup00C35stdpp8fin_maps@lookup_delete_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6MI_Ext:inv_R_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_A_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_M_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_L_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_G_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_S_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext?inv_SH_set_tickC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8g_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC35stdpp4base6lookupK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec9MI_WSlot3=alloc_slot_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WAMeta2:am_take_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree9ftree_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree:ftree_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt@size_to_class_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WMalloc9CORE_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes2idK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib4Spec6MI_Cnt=size_class_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt9lor1_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6of_natK35stdpp4base5NoDup01C59OSSVerify5KrLib4Spec9MI_WSlot29SLOT_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot4X_asC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WMalloc<small_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry28hd_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_masksC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib4Spec7MI_Bits<lowbit_idiomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib4Spec8MI_WSlot5GP_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry27hd_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WTry9ta_fin_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitFget_meta_rec_upd_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula02C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF28TF0_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF27TF0_TF2C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z7testbitK46Stdlib9micromega5Tauto8GFormula0:K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2x0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega5Tauto4kind02C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9brk_quietC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree2<brk_quiet_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7lrangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_LedgerAmmap_answer_ok_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot7GP_reflC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_LedgerEINVL_new_group_regionC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib4Spec9MI_Ledger9ng_lookupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WSlot2Dshadow_next_rid_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WSlot2?step_seq_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3=INVL_step_seqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9MI_WAMeta8AM_frame00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9MI_WAMeta7L_frame00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec9MI_WAMeta9lf_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8g_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta7lf_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec9MI_Ledger7ng_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta;amf_regionsC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib4Spec6MI_Inv6ir_idsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib4Spec6MI_KitEs_regions_set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitDs_regions_set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta8amf_ssecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree2>INVL_drop_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xorphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree7rejectsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres35xidleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta:amf_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta8amf_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2;create63_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitAs_regions_upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@s_secret_upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3AINVL_mmap_counterC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt@round_up_pg_specC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta8amf_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta7lf_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WAMeta2=alloc_meta_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_brkphC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertC46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib4Spec;MI_WCreate23F63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_ltK47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv4MAPFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv5MAPFXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00c59OSSVerify5KrLib4Spec:MI_WMalloc=malloc_big_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WMalloc?malloc_small_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib4Spec:MI_WMalloc=INVL_set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup6TKS_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2<TF0_tick_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WMalloc>malloc_core_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot8GP_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:ce_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9ce_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_nodupC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list:NoDup_consC59OSSVerify5KrLib4Spec<MI_WEnframe2:enframe_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6mallocC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C35stdpp4base7elem_ofC56Stdlib6ZArith4Znat3N2Z8inj_succC56Stdlib6ZArith4Znat3N2Z6inj_leC59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_set_tick X st L BL LS t : (s_tick st <= t)%N -> INVL X st L BL LS -> INVL X (set_tick t st) L BL LS.
Proof.
  intros Ht (IR & IA & IM & IL & IG & IS & ISH).
  assert (CE : ctrl_eq st (set_tick t st)) by (constructor; reflexivity).
  split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
  split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
  split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
  apply inv_SH_set_tick; [exact Ht| exact ISH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CORE_POST (st0 : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
  ld_live L1 = ld_live L /\ GP st0 (fst r) /\
  match snd r with
  | None => exists LS1, INVL x0 (fst r) L1 BL LS1
  | Some (g, idx) => exists LS1 bg, let st1 := fst r in
      hosts st1 bg g /\ 0 <= idx <= m_last_idx (MR st1 g)
      /\ INVL (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
      /\ n + IB <= get_stride (MR st1 g) /\ TF2 st1 /\ get_stride (MR st1 g) - IB - n < 2 ^ 32
  end.

Lemma small_stride X st L BL LS bg g : INVL X st L BL LS -> hosts st bg g -> m_sizeclass (MR st g) < 48 -> get_stride (MR st g) < 2 ^ 20.
Proof.
  intros INV [ai Hb] Hsc. pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
  destruct (g_stride _ _ _ _ _ _ GO Hsc) as (_ & _ & LT). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of in LT.
  pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ (ex_intro _ ai Hb)) as [S _]. unfold UNIT in S. nia.
Qed.

Section CORE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis Hn : 0 <= n.

(* [comment removed for export] *)
Lemma malloc_small_ft : n < MMAP_THRESHOLD ->
  ftree L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POST st n L BL).
Proof.
  intros Hlt. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end).
  assert (SC' : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc).
  { subst sc. destruct (active st sc0); [auto|].
    destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
    match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
    apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (lor1_even sc0 ltac:(lia) EV). split; [lia|].
    pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  clearbody sc. destruct SC' as [SC' FIT'].
  destruct (active st sc) as [gp|] eqn:HA.
  - (* [comment removed for export] *)
    destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
    + rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb].
      (* [comment removed for export] *)
      apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POST st n L BL) FUEL sc [] st L BL LS n); try assumption.
      * unfold FUEL. cbn. lia.
      * apply NoDup_nil_2.
      * intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
        -- cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
        -- replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
           exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
           pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
    + (* [comment removed for export] *)
      destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
      pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
      destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
      assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
      rewrite LNZ. cbn [negb ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_eq; reflexivity|].
      pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
      set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
      assert (MR1 : forall x, x <> gp -> MR st1 x = MR st x) by (intros x NE; unfold st1, MR; apply get_meta_rec_upd_other; exact NE).
      assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ get_stride (MR st1 gp) = get_stride (MR st gp) /\ (forall i, sstart (MR st1 gp) i = sstart (MR st gp) i) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
      { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; repeat split; reflexivity. }
      destruct MRg as (ML & MS & MSS & MSC).
      exists LS, bm. rewrite ML, MS, MSS. split; [exists ai; exact Hbm|]. split; [exact Hidx|]. split; [exact INV1|].
      rewrite Esc in STR. split; [lia|].
      split; [apply TF0_TF2; apply (TF0_ctrl st st1); [reflexivity| reflexivity| exact TF]|].
      pose proof (small_stride _ _ _ _ _ bm gp INV (ex_intro _ ai Hbm) ltac:(lia)). unfold IB. lia.
  - (* [comment removed for export] *)
    change (lowbit 0) with 0. cbn [negb Z.eqb].
    apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POST st n L BL) FUEL sc [] st L BL LS n); try assumption.
    + unfold FUEL. cbn. lia.
    + apply NoDup_nil_2.
    + intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
      * cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
      * replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
        exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
        pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
Qed.

(* [comment removed for export] *)
Lemma malloc_big_ft : MMAP_THRESHOLD <= n -> size_overflows n = false ->
  ftree L
    (SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (s_atop st) (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
      if is_err r then ret (st, None) else
      let '(st1, rid) := new_region RKGroup r (n + IB + UNIT) st in
      let st2 := step_seq st1 in
      alloc_meta st2 (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st, @None (aptr * Z))))
        | Some g =>
          let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
                       (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
          let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
          let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
          let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
          ret (st7, Some (g, 0))
        end) (ret (st, @None (aptr * Z)))))
    (CORE_POST st n L BL).
Proof.
  intros Hbig Hov. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
    unfold LEN_MAX. clear -HN. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. exists LS. exact INV.
    + destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
      rewrite <- Est1, <- Erid in INV1.
      set (L1 := KInv.set_groups ((a, needed) :: ld_groups L) L) in *.
      assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
      assert (NS1 : s_shadow st1 !! rid = None).
      { rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
      assert (TF1 : TF0 (step_seq st1)).
      { destruct (step_seq_fields st1) as (A & B & _). apply (TF0_ctrl st1); [exact A| exact B|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
      pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
      destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
      eapply (alloc_meta_ft (mstate * option (aptr * Z)) BL (CORE_POST st n L BL) _ _ (xorph x0 (Some rid)) (step_seq st1) L1);
        [ | | exact INV2| apply amf_refl| apply lf_refl].
      * (* [comment removed for export] *)
        intros st3 L3 LS3 INV3 AF LF. cbn beta iota.
        apply ftree_vis; [reflexivity| reflexivity| | |].
        -- cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV3))|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd event_post].
           split; [cbn; rewrite (lf_live _ _ LF); reflexivity|].
           split.
           { split.
             - intros q rq Hq Kq. unfold drop_region. rewrite s_regions_set_shadow, s_regions_set_regions. rewrite lookup_delete_ne.
               + apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
               + intros ->. pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hq). rewrite Erid in H. lia.
             - transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity. }
           exists LS3.
           pose proof (INVL_drop_orph (xorph x0 (Some rid)) st3 L3 BL LS3 rid (mkRegion RKGroup a needed) INV3 eq_refl
                         (amf_regions _ _ AF rid _ ltac:(rewrite SS4; exact Hr1) eq_refl)) as INV4.
           cbn [r_base xorph x_idle x_zomb x_pend x_fresh x_orph] in INV4. exact INV4.
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 g INV3 NIg AF LF. cbn beta iota zeta.
        change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl (step_seq st1)); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
        cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3.
        destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
          as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6).
        match goal with |- ftree _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
        cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [cbn; exact (lf_live _ _ LF)|].
        split.
        { split.
          - intros q rq Hq Kq. rewrite s_regions_upd_ctx, RG6. apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
          - rewrite s_secret_upd_ctx. transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity. }
        pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
        set (st7 := upd_ctx _ st6) in *.
        assert (MR7 : MR st7 g = MR st6 g) by reflexivity.
        exists LS3, (rid, 0). rewrite MR7, MR6. cbn [m_last_idx].
        assert (SS0 : sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0 = 16).
        { unfold sstart, gbase. cbn -[Z.mul Z.add get_stride]. unfold UNIT. lia. }
        rewrite SS0. change (fst (rid, 0)) with rid.
        split; [exists 0; exact GR6|]. split; [lia|]. split; [exact INV7|].
        rewrite STR6. pose proof (round_up_pg_spec needed) as [RU _]. unfold needed, IB, UNIT in *.
        split; [lia|]. split; [apply TF0_TF2; apply (TF0_ctrl st6); [reflexivity| reflexivity| exact TF6]| lia].
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

Theorem malloc_core_ft : ftree L (malloc_core full_lay st n) (CORE_POST st n L BL).
Proof.
  unfold malloc_core.
  destruct (size_overflows n) eqn:Hov.
  - cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. exists LS. exact INV.
  - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
    + exact (malloc_big_ft Hbig Hov).
    + exact (malloc_small_ft Hsmall).
Qed.
End CORE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem malloc_INVL st L BL LS n :
  INVL x0 st L BL LS -> 0 <= n ->
  ftree L (malloc st n) (fun L' r =>
    ld_live L' = ld_live L /\ GP st (fst r) /\
    match snd r with
    | None => exists LS', INVL x0 (fst r) L' BL LS'
    | Some p => exists c off LS', p = aadd c (UNIT * off) /\ 0 <= off <= 255
        /\ INVL x0 (fst r) L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
    end).
Proof.
  intros INV Hn. unfold malloc.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  eapply ftree_bind; [exact (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)|].
  intros L1 [st1 r] (LIVE & GP1 & RES). cbn [fst snd] in RES, GP1 |- *.
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  destruct r as [[g idx]|].
  - destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    apply (enframe_ft (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32).
    intros off st' Ho Hf INV' CE TK. cbn [fst snd]. split; [exact LIVE|]. split; [eapply GP_trans; [exact GP0| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]]|].
    exists (fst bg, sstart (MR st1 g) idx), off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV'|].
    pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))))) as ND. cbn [map bslot fst] in ND.
    apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
  - destruct RES as (LS1 & INV1). cbn [ftree ret fst snd]. split; [exact LIVE|]. split; [exact GP0|]. exists LS1. exact INV1.
Qed.
