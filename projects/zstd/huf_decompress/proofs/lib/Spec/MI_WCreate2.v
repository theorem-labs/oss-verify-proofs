(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (38 recorded proofs replaced by written proofs (land31_id, land63_id, land52_id and 35 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_WGroup MI_WCreate MI_Cnt MI_TF2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WCreate2 () := "C46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC35stdpp8fin_maps:map_insertI35stdpp8fin_maps6FinMap00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~K35stdpp8fin_maps6FinMap01C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp8fin_maps9insert_idC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic2or02I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3divC35stdpp4base5emptyK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C35stdpp8fin_maps<lookup_emptyC59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2Acell_read_shadow0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate23agtC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C35stdpp4base6insertI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate29agt_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate23agGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6MI_Kit@lookup_add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate28agt_rec3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_usage_mapC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib4Spec;MI_WCreate27agt_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2=TF0_hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF28TF0_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF22TWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2<TW_hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF27TW_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6MI_Inv7im_idleC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec8MI_Pres3AINVL_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate27top_MRmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt<grp_ok_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6shiftrC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc59OSSVerify5KrLib4Spec;MI_WCreate29land52_idC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate29land63_idC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib4Spec;MI_WCreate29land31_idC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt@round_up_pg_specC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes3nat00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate28agt_MR_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt=created_masksC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z2gtC59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_gt_casesc59OSSVerify5KrLib4Spec;MI_WCreate26one5_AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate26one5_BC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4Spec;MI_WCreate2>known_noshadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C35stdpp8fin_maps6map_eqC59OSSVerify5KrLib4Spec6MI_Kit@s_metas_upd_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2:agt_groupsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate29agt_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6ia_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate29agt_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv=ia_usage_keysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WCreate;INVL_createC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate27agt_TF0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib4Spec;MI_WCreate27top_MR4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate29top_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate28top_INV3C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_metasC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt6zrangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc59OSSVerify5KrLib4Spec;MI_WCreate26hdr3_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt>forallb_zrangeC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib4Spec;MI_WCreate28hdr3_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt=nest_ok_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Arith@size_class_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8sub_diagC59OSSVerify5KrLib4Spec6MI_Cnt=size_class_leC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup7nl_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup3wrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF26TF2_TFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup>nest_layout_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;nest_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup2TFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres23inTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup5nl_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate29nst_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext8ce_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@get_meta_rec_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2<set_metas_idC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2:nst_layoutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate27nst_MRmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6MR_extC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2:hdr3_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2:sstart_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;hosts_gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC59OSSVerify5KrLib4Spec6MI_Inv8g_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C59OSSVerify5KrLib4Spec7MI_Geom7sstart0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;sstart_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom8hosts_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_alignC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C59OSSVerify5KrLib4Spec6MI_Inv8is_totalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext8ce_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9ce_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9hosts_extC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z7mul_1_rC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib4Spec9MI_WGroup5zlistC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec9MI_WGroup8in_zlistC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC46Stdlib5Lists4List7map_appC59OSSVerify5KrLib4Spec6MI_TF2?wrs_cells_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2<TF2_ghdr_oldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2:agt_shadowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2;agt_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate29agt_areasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2<agt_next_ridC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate28agt_tickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2:agt_secretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2<agt_reservedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate28agt_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6ce_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF22PSC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4=idle_not_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2<agt_MR_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2<geom_kept_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF27PS_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF27TW_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF26TW_wrsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate26agt_TWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2:agt_activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2<agt_get_headC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc59OSSVerify5KrLib4Spec;MI_WCreate27nst_st3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate29nst_hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc59OSSVerify5KrLib4Spec;MI_WCreate2?round_up_pg_divC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate23F63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate26c63_mlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7ir_orphC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate25c63_FC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate27c63_MRgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;testbit_0_lC56Stdlib6ZArith6BinInt1Z7comparec59OSSVerify5KrLib4Spec;MI_WCreate26one5_EC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc59OSSVerify5KrLib4Spec;MI_WCreate2:c63_strideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WCreate2;c63_nogroupC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03c59OSSVerify5KrLib4Spec;MI_WCreate28c63_rec5C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land31_id x : 0 <= x <= 31 -> Z.land x 31 = x.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land63_id x : 0 <= x <= 63 -> Z.land x 63 = x.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land52_id x : 0 <= x < 2 ^ 52 -> Z.land x (2 ^ 52 - 1) = x.
Proof. intros. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma one5_A (A B E : Prop) : A -> ~ B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
Lemma one5_B (A B E : Prop) : ~ A -> B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
Lemma one5_E (A B E : Prop) : ~ A -> ~ B -> E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.

Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read. cbn. rewrite !lookup_empty. reflexivity. Qed.

Lemma known_noshadow st rid o : s_shadow st !! rid = None -> known st (rid, o) 0.
Proof. intros H. unfold known, SHd, get_shadow. cbn. rewrite H. cbn. apply cell_read_shadow0. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition agG (sc : Z) (p : aptr) (cnt ai : Z) (r : meta) : meta :=
  m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
    (m_set_mem (Some p) (m_set_freed (mask_upto (cnt - 1) - mask_upto ai) (m_set_avail (mask_upto ai) r))))).

Definition agt (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
  let st0 := hdr_havoc p st in
  let st1 := set_usage sc (usage st0 sc + cnt) st0 in
  let st2 := upd_meta m (agG sc p cnt ai) st1 in
  let st3 := put_group p (Some m) ai st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

Lemma ag_tail_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
  ag_tail full_lay st sc m p cnt ai k = k (agt st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

Section AGT.
Variables (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.
Let mr' := agG sc p cnt ai (MR st m).

Lemma agt_metas : s_metas st' = <[m := mr']> (s_metas st).
Proof. reflexivity. Qed.
Lemma agt_MR_m : MR st' m = mr'.
Proof. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_eq. reflexivity. Qed.
Lemma agt_MR_other x : x <> m -> MR st' x = MR st x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma agt_groups : s_groups st' = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
Lemma agt_rec3 :
  get_meta_rec (put_group p (Some m) ai (upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p st) sc + cnt) (hdr_havoc p st)))) m = mr'.
Proof. unfold get_meta_rec. cbn -[agG get_meta_rec]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma agt_slots s : 0 <= cnt -> 0 < get_stride mr' ->
  s_slots st' !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod get_stride mr' =? 0) && ((snd s - snd p - UNIT) / get_stride mr' <? cnt)
  then Some (m, (snd s - snd p - UNIT) / get_stride mr') else s_slots st !! s.
Proof. intros Hc Hs. unfold st', agt. cbn zeta. rewrite agt_rec3. rewrite lookup_add_slots by assumption. reflexivity. Qed.
Lemma agt_shadow : s_shadow st' = s_shadow (hdr_havoc p st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;4p;2p;1g00YMj43Tg01?Vj22Tg00lnj10Tg00<>j21Tg00igg012Sg012lg010aC3p,1pp,2st'2#0'1o"). Qed.
Lemma agt_regions : s_regions st' = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;4p;1p;2g00YMj42Tg01NVj11Tg00<>j20Tg00igg012Sg012lg01OPC2p,2st#1'0o"). Qed.
Lemma agt_areas : s_areas st' = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;4p;6p;1p;2g015mj44Tg016Kj63Tg00YMj40Tg01PIj11Tg00<>j22Tg00IGg00igR0g012SR1g00BYR2g00jER3C4P0P1g012lP2P3g00j^E3g01QAC0p,2st#1'2o"). Qed.
Lemma agt_next_rid : s_next_rid st' = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;1p;2g01R8j11Tg00<>j20Tg00igp,2st#1'0o"). Qed.
Lemma agt_tick : s_tick st' = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;1p;2g01S3j11Tg00<>j20Tg00igp,2st#1'0o"). Qed.
Lemma agt_secret : s_secret st' = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;1p;2g01Sjj11Tg00<>j20Tg00BYp,2st#1'0o"). Qed.
Lemma agt_reserved : s_reserved st' = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;2p;1g00^fj23Tg005]j12Tg01Tcj10Tg00<>j21Tg00BYR0/30#2p,2st#0'1o"). Qed.
Lemma agt_atop : s_atop st' = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;1p;2g01U^j11Tg00<>j20Tg00BYp,2st#1'0o"). Qed.
Lemma agt_ctx : s_ctx st' = set_usage_map (<[sc := usage st sc + cnt]> (c_usage (s_ctx st))) (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p;4p;2p;1p;7g00YMj49Tg00O_j48Tg00MBj40Tg01@Pj21Tg01AFj27Tg01VUj12Tg01WKj13Tg017dj74Tg01XCj25Tg00<>j26Tg01YAg00BYR0P0P0g00jER1g00j^R2P0C9R3P0P0P3P0P1P2P0C8C0p,2scR0p,2stR2/10p,3cnt'7%22R2#3F4/52'6o"). Qed.
Lemma agt_usage sc0 : usage st' sc0 = usage st sc0 + (if sc0 =? sc then cnt else 0).
Proof.
  unfold usage at 1. unfold ctx. rewrite agt_ctx. cbn -[usage]. destruct (Z.eqb_spec sc0 sc) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. unfold usage, ctx. lia.
Qed.
Lemma agt_active sc0 : active st' sc0 = active st sc0.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "h03sc0p;2g01^8j21Tg00<>j20Tg00BYR0g00S7p,2stf0R1'1'0X00P1O1W0o"). Qed.
Lemma agt_get_head h : get_head st' h = get_head st h.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AGT"] "p'0h01hh13sc0i001li012scp;2p;3p;1g01^oj20Tg004cj33Tg01_hj12Tg00<>j21Tg01``R0P0g00S7R1p,3st'f0R2'0p,2stR3/0233P2g00BY%22,03,11W1P2O1g01aX,03,11n0110000021010100X00P2O1W0o"). Qed.

Lemma agt_TF0 : TF0 st -> TF0 st'.
Proof. intros H. apply (TF0_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. exact H. Qed.
Lemma agt_TW P : TW st P -> TW st' P.
Proof. intros H. apply (TW_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TW_hdr_havoc. exact H. Qed.
End AGT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AG_TOP.
Variables (idle0 : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m : aptr) (rid : N) (r : region) (sc cnt needed ai : Z).
Let X := mkX (m :: idle0) [] None (Some rid) None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st2 L BL LS.
Hypothesis Hr : s_regions st2 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st2 !! rid = None.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hai : 0 <= ai <= cnt - 1.
Hypothesis Hai0 : sc = 0 -> ai = cnt - 1.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF0 st2.
Hypothesis NIm : ~ In m idle0.
Let p : aptr := (rid, 0).
Let ml := Z.shiftr needed 12.
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let st3 := upd_ctx MC st2.
Let st4 := upd_meta m (m_set_maplen ml) st3.
Let st' := agt st4 sc m p cnt ai.
Let mr' := agG sc p cnt ai (m_set_maplen ml meta0).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma top_MRm : MR st2 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.

Lemma top_INV3 : INVL X st3 L BL LS.
Proof. exact (INVL_mmap_counter X st2 L BL LS INV). Qed.

Lemma top_MR4 : MR st4 m = m_set_maplen ml meta0.
Proof. unfold st4, MR. rewrite get_meta_rec_upd_same. f_equal. exact top_MRm. Qed.

Lemma top_facts :
  let size := UNIT * size_class sc in
  let stride := get_stride mr' in
  1 <= cnt <= 32 /\ ml = needed / 4096 /\ 1 <= ml <= 256 /\ UNIT + stride * cnt <= ml * 4096
  /\ (stride <= size \/ 28 <= sc) /\ (cnt - 1 = 0 -> 27 <= sc) /\ stride * cnt < 2 ^ 20 /\ 16 <= stride /\ stride mod 16 = 0
  /\ ml * 4096 = round_up_pg needed /\ 0 < needed
  /\ mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.
Proof.
  unfold ml in *. pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml).
  { unfold mr', agG, m_set_sizeclass, m_set_freeable, m_set_last_idx, m_set_mem, m_set_freed, m_set_avail, m_set_maplen. cbn.
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite land52_id by lia. reflexivity. }
  assert (Es : get_stride mr' = (if (cnt - 1 =? 0) && negb (ml =? 0) then ml * 4096 - UNIT else UNIT * size_class sc)).
  { rewrite Emr. unfold get_stride. cbn. reflexivity. }
  cbn zeta. unfold ml in *.
  assert (RU : needed / 4096 * 4096 = round_up_pg needed).
  { destruct (round_up_pg_spec needed) as [A B]. pose proof (Z.div_mod needed 4096 ltac:(lia)). rewrite G2 in H.
    pose proof (Z.div_mod (round_up_pg needed) 4096 ltac:(lia)). rewrite B in H0. nia. }
  rewrite Es. repeat split; try assumption; try lia.
Qed.

Theorem ag_top_ok :
  INVL X' st' L BL LS /\ TF0 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) ai)
  /\ (forall sc0, active st' sc0 = active st2 sc0) /\ (forall h, get_head st' h = get_head st2 h)
  /\ s_tick st' = s_tick st2.
Proof.
  pose proof top_facts as TFX. cbn zeta in TFX. destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
  pose proof top_INV3 as INV3. pose proof INV3 as (IR & IA & IM3 & IL & IG & IS & ISH).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite top_MR4; reflexivity).
  pose proof (created_masks ai (cnt - 1) Hai ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  assert (Sp : get_stride mr' > 0) by lia.
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st3 st' L BL LS m p ai mr' INV3 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - exact Hai0.
    - left. lia.
    - unfold tbit. repeat split; try lia; assumption.
    - intros _. rewrite <- Emr. repeat split; lia.
    - rewrite <- Emr. lia.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X'].
      destruct (Z.le_gt_cases i ai).
      + apply one5_A; [apply M7; lia| intros Hf; exact (M5 i ltac:(lia) (M7 i ltac:(lia)) Hf)| discriminate].
      + apply one5_B; [intros Ha; pose proof (M3 i ltac:(lia) Ha); lia| apply M6; lia| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - left. rewrite <- Emr. cbn [snd fst x_orph x_pend X X' p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. replace (m_maplen mr') with ml by (rewrite Emr; reflexivity).
      split; [exact F10|]. unfold cnt_of. replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity). lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - unfold st'. rewrite agt_metas. unfold st4. rewrite s_metas_upd_meta. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. fold st4. first [rewrite top_MR4; exact Emr| unfold mr'; f_equal; exact top_MR4].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st4 sc m p cnt ai s); [| lia| rewrite top_MR4; fold mr'; lia].
      rewrite top_MR4. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. repeat split; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx in Hv. cbn in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { unfold st'. apply agt_TF0. apply (TF0_ctrl st2); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'm|]. split; [unfold st'; rewrite agt_groups, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros; reflexivity|]. split; [intros h; destruct h; reflexivity| reflexivity].
Qed.
End AG_TOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_metas_id st v : v = s_metas st -> Malloc.set_metas v st = st.
Proof. destruct st; cbn; intros ->; reflexivity. Qed.

Definition hdr3_f (i : Z) : bool := (Z.land (Z.lor (Z.land i 31) 192) 255 =? i + 192) && (Z.land (i + 192) 31 =? i).
Lemma hdr3_all : forallb hdr3_f (zrange 0 32) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) [] "p;2p;1p;3g00<>j25Tg003Aj10Tg002Hj12Tg03OHj21Tg03P?j34Tg004cj33Tg00H3R0g00HSR1'5g00BYg03P[g00E]g00F;#0#0#0#0#0#2'134=301do"). Qed.
Lemma hdr3_facts i : 0 <= i <= 31 -> Z.land (Z.lor (Z.land i 31) 192) 255 = i + 192 /\ Z.land (i + 192) 31 = i.
Proof.
  intros Hi. pose proof (forallb_zrange hdr3_f 0 32 i hdr3_all ltac:(lia) ltac:(lia)) as H. unfold hdr3_f in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Section AG_NESTED.
Variables (idle0 : list aptr) (st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m g bg : aptr) (aig idx sc cnt : Z).
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).
Let p : aptr := (fst bg, sstart (MR st1 g) idx).
Let X := mkX (m :: idle0) [] (Some p) None None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st1 L BL LS.
Hypothesis Hg : s_groups st1 !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st1 g).
Hypothesis SCg : m_sizeclass (MR st1 g) = j.
Hypothesis STR : get_stride (MR st1 g) = UNIT * size_class j.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF2 st1.
Hypothesis NIm : ~ In m idle0.
Let st2 := nest_layout st1 g idx j size cnt.
Let st3 := upd_meta m (m_set_maplen 0) st2.
Let st' := agt st3 sc m p cnt (cnt - 1).
Let mr' := agG sc p cnt (cnt - 1) meta0.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma nst_MRm : MR st1 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.
Lemma nst_hosts : hosts st1 bg g.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate2 ()) ["AG_NESTED"] "h02aip;1p;4p;6p;2p;3g00_Fj1:Tg015mj49Tg016Kj62Tg00YMj41Tg00Nnj48Tg01=fj14Tg00iSj63Tg00`Xj20Tg01<oj25Tg004cj36Tg02i<j47Tg00BYR0g01>_R1#:g00IGR2P1P2g00igR3g012SR4P0g00jER5C9R6P3P4g012lP0P5g00j^E2R5P1C1P2P6P5P1C8p,2bgp,3st1#4E3p,1g,02f0'5,0136X00p,3aigp,2HgC7o"). Qed.

Lemma nst_facts :
  2 <= cnt <= 32 /\ sc < j <= 23 /\ UNIT + cnt * size <= UNIT * size_class j /\ size * cnt < 2 ^ 20
  /\ 16 <= size /\ size mod 16 = 0 /\ size_class j <= 127
  /\ mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0
  /\ get_stride mr' = size.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0.
  destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  pose proof (size_class_bound sc Hsc) as SB.
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0).
  { unfold mr', agG, m_set_sizeclass, m_set_freeable, m_set_last_idx, m_set_mem, m_set_freed, m_set_avail. cbn.
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite Z.sub_diag. reflexivity. }
  assert (SJ : size_class j <= 127) by (change 127 with (size_class 23); apply size_class_le; lia).
  repeat split; try lia.
  - unfold size, UNIT. lia.
  - unfold size, UNIT. rewrite Z.mul_comm. apply Z_mod_mult.
  - exact Emr.
  - rewrite Emr. unfold get_stride. cbn -[Z.eqb size_class Z.mul]. replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nst_layout :
  INVL X st2 L BL LS /\ ctrl_eq st1 st2 /\ s_tick st2 = s_tick st1
  /\ known st2 (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
  /\ known st2 (aadd p (-2)) (Z.land ((snd p - (snd bg + UNIT)) / UNIT) 255)
  /\ known st2 (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr ((snd p - (snd bg + UNIT)) / UNIT) 8) 255)
  /\ (forall k, 0 <= k <= cnt -> known st2 (aadd p (UNIT + k * size - 4)) 0)
  /\ st2 = wrs (nl_list st1 g bg idx size cnt) st1.
Proof.
  pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _ & _).
  pose proof (nest_layout_ok X st1 L BL LS g bg aig idx j size cnt INV Hg Hidx eq_refl STR N6 N5 ltac:(lia) ltac:(rewrite STR; exact N3)
                (TF2_TF X st1 L BL LS INV TF)) as (A & _ & C & D & E & F & G & H & _).
  refine (conj A (conj C (conj D (conj E (conj F (conj G (conj H _))))))). apply (nl_eq X st1 L BL LS g bg aig idx j size cnt INV Hg STR).
Qed.

Lemma nst_st3 : st3 = st2.
Proof.
  pose proof nst_layout as (INV2 & CE & _).
  unfold st3, upd_meta, put_meta. apply set_metas_id.
  assert (E : get_meta_rec st2 m = meta0) by (rewrite (get_meta_rec_ext st1 st2 m (ce_metas _ _ CE)); exact nst_MRm).
  rewrite E. change (m_set_maplen 0 meta0) with meta0. apply insert_id. rewrite (ce_metas _ _ CE). exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))).
Qed.

Theorem ag_nested_ok :
  INVL X' st' L BL LS /\ TF2 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) (cnt - 1))
  /\ (forall sc0, active st' sc0 = active st1 sc0) /\ (forall h, get_head st' h = get_head st1 h)
  /\ s_tick st' = s_tick st1.
Proof.
  pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & Emr & Es).
  pose proof nst_layout as (INV2 & CE & TK2 & K3 & K2 & K1 & KZ & Ewrs).
  pose proof INV as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  pose proof INV2 as (IR & IA & IM2 & IL & IG2 & IS2 & ISH).
  pose proof nst_st3 as E3.
  assert (MR2 : forall x, MR st2 x = MR st1 x) by (intros x; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite E3, MR2, nst_MRm; reflexivity).
  pose proof (created_masks (cnt - 1) (cnt - 1) ltac:(lia) ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  rewrite Z.sub_diag in *.
  pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg)) as LI31.
  pose proof (hdr3_facts idx ltac:(lia)) as [H3a H3b].
  pose proof (sstart_res X st1 L BL LS INV bg g idx nst_hosts) as PR. fold p in PR.
  assert (P16 : snd p mod 16 = 0).
  { unfold p. cbn [snd]. unfold IB in PR. pose proof (Z.div_mod (sstart (MR st1 g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st1 g) idx) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (sstart (MR st1 g) idx) 16 ltac:(lia)). lia. }
  pose proof (hosts_gbase _ _ _ IM1 _ _ nst_hosts) as GB.
  assert (S0 : sstart (MR st1 g) idx = snd bg + UNIT + get_stride (MR st1 g) * idx) by (unfold sstart; rewrite GB; reflexivity).
  assert (Q : (snd p - snd bg - UNIT) / UNIT = size_class j * idx).
  { unfold p. cbn [snd]. rewrite S0, STR. unfold UNIT. replace (snd bg + 16 + 16 * size_class j * idx - snd bg - 16) with ((size_class j * idx) * 16) by lia. apply Z.div_mul. lia. }
  assert (Qr : 0 <= size_class j * idx < 2 ^ 16).
  { pose proof (size_class_bound j ltac:(clear - N2 Hsc; lia)) as SB.
    destruct (g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg) ltac:(rewrite SCg; clear - N2; lia)) as (_ & _ & LT).
    rewrite STR in LT. unfold cnt_of in LT. clear - SB LT Hidx. unfold UNIT in LT. nia. }
  assert (NH : s_groups st1 !! p = None).
  { pose proof (is_part _ _ _ IS1 _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite (slot_start'_eq _ _ _ IM1 _ _ _ nst_hosts) in P5. fold p in P5.
    destruct (s_groups st1 !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st2 st' L BL LS m p (cnt - 1) mr' INV2 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - left. lia.
    - unfold tbit. repeat split; try lia; try assumption; try (intros i Hi Hb; rewrite Z.bits_0 in Hb; discriminate).
    - intros _. rewrite <- Emr, Es. unfold size. clear - N1 N4. repeat split; lia.
    - rewrite <- Emr, Es. lia.
    - unfold UNIT. split; [| exact P16]. unfold p. cbn [snd]. pose proof (sstart0 _ _ _ IM1 _ _ nst_hosts). pose proof (sstart_mono _ _ _ IG1 _ _ 0 idx nst_hosts ltac:(lia)).
      destruct (hosts_ok _ _ _ IG1 _ _ nst_hosts) as (a0 & _ & GO). pose proof (g_align _ _ _ _ _ _ GO). unfold UNIT in *. lia.
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn [x_idle X X'] in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X']. apply one5_A; [apply M7; lia| rewrite Z.bits_0; discriminate| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - right. rewrite <- Emr. cbn [x_pend x_orph X X']. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists g, idx, bg. rewrite !MR2.
      split; [rewrite (ce_slots _ _ CE); unfold p; rewrite <- (slot_start'_eq _ _ _ IM1 _ _ idx nst_hosts); exact (is_total _ _ _ IS1 _ _ _ nst_hosts Hidx)|].
      split; [apply (proj2 (hosts_ext st1 st2 (ce_groups _ _ CE) bg g)); exact nst_hosts|].
      split; [reflexivity|]. split; [exact Hidx|]. split; [reflexivity|].
      split; [rewrite Es; unfold p; cbn [snd]; rewrite STR; unfold cnt_of; replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity); unfold size in N3 |- *; lia|].
      split; [rewrite SCg; replace (m_sizeclass mr') with sc by (rewrite Emr; reflexivity); lia|].
      split; [rewrite STR, SCg; reflexivity|].
      split; [exists (idx + 192); split; [| split; [exact H3b| clear - Hidx LI31; lia]]; rewrite <- H3a; exact K3|].
      rewrite Q. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. rewrite <- Q.
      replace (snd p - snd bg - UNIT) with (snd p - (snd bg + UNIT)) by lia.
      split; [exact K2|]. split; [replace (fst p, snd p - 1) with (aadd (aadd p (-2)) 1) by (unfold aadd; cbn [fst snd]; f_equal; lia); exact K1|].
      replace ((snd p - (snd bg + UNIT)) / UNIT) with (size_class j * idx) by (rewrite <- Q; f_equal; lia). exact Qr.
    - rewrite <- Emr. intros i Hi. rewrite Es. replace (fst p, snd p + UNIT + size * i - IB) with (aadd p (UNIT + i * size - 4)) by (unfold aadd, IB; f_equal; lia).
      apply KZ. unfold cnt_of in Hi. rewrite ?Emr in Hi. cbn [m_last_idx] in Hi. lia.
    - intros o v tk Ho Hc. rewrite Ewrs in Hc. rewrite wrs_cells_other in Hc.
      + rewrite TK2. exact (TF2_ghdr_old X st1 L BL LS INV p TF P16 o v tk Ho Hc).
      + unfold nl_list. rewrite map_app. intros Hin. apply in_app_iff in Hin. unfold p in Ho. cbn [snd] in Ho. destruct Hin as [Hin|Hin].
        * cbn [map fst In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold aadd in E; cbn [fst snd] in E; clear - E Ho N1 N5; lia.
        * apply in_zlist in Hin as (k & Hk & E). apply (f_equal snd) in E. unfold aadd in E. cbn [fst snd] in E. unfold UNIT in E.
          assert (0 <= k * size) by (apply Z.mul_nonneg_nonneg; clear - Hk N5; lia). clear - E Ho H Hk N5. lia.
    - unfold st'. rewrite agt_metas. rewrite E3. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. rewrite MR2, nst_MRm. first [exact Emr| reflexivity].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups, E3. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st3 sc m p cnt (cnt - 1) s); [| lia| rewrite E3, MR2, nst_MRm; fold mr'; rewrite Es; lia].
      rewrite E3, MR2, nst_MRm. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - unfold st'. rewrite agt_shadow, E3. reflexivity.
    - unfold st'. rewrite agt_regions, E3. reflexivity.
    - unfold st'. rewrite agt_areas, E3. reflexivity.
    - unfold st'. rewrite agt_next_rid, E3. reflexivity.
    - unfold st'. rewrite agt_tick, E3. reflexivity.
    - unfold st'. rewrite agt_secret, E3. reflexivity.
    - unfold st'. rewrite agt_reserved, E3. reflexivity.
    - unfold st'. rewrite agt_atop, E3. reflexivity.
    - unfold st'. rewrite agt_ctx, E3. repeat split; reflexivity.
    - unfold st'. rewrite agt_ctx, E3. cbn [c_mmap_counter set_usage_map]. rewrite (ce_ctx _ _ CE). pose proof (ia_ctx _ IA1) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage, E3. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx, E3 in Hv. cbn [c_usage set_usage_map] in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. rewrite (ce_ctx _ _ CE) in Hv. exact (ia_usage_keys _ IA1 sc0 v Hv). }
  split; [exact INV'|]. split.
  { (* [comment removed for export] *)
    unfold TF2. unfold st'. rewrite E3.
    apply (TW_mono _ (fun q => PS st1 q \/ In q (map fst (nl_list st1 g bg idx size cnt)))).
    2:{ apply agt_TW. rewrite Ewrs. apply TW_wrs; [| intros q Hq; right; exact Hq]. apply (TW_mono _ (PS st1)); [intros q Hq; left; exact Hq| exact TF]. }
    intros q [Hq|Hq].
    - apply (PS_mono st1); [| exact Hq]. apply geom_kept_of.
      + intros b h Hb. rewrite <- E3. fold st'. unfold st'. rewrite agt_groups, E3, (ce_groups _ _ CE).
        rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite NH in Hb. discriminate.
      + intros b x Hx. rewrite <- E3. fold st'. rewrite (agt_MR_other st3 sc m p cnt (cnt - 1) x), E3, MR2; [reflexivity|].
        intros ->. exact (idle_not_live _ _ _ _ _ INV m ltac:(left; reflexivity) (ex_intro _ b Hx)).
    - assert (Hm' : hosts (agt st2 sc m p cnt (cnt - 1)) p m) by (exists (Z.land (cnt - 1) 31); rewrite agt_groups, lookup_insert_eq; reflexivity).
      assert (R' : MR (agt st2 sc m p cnt (cnt - 1)) m = mr') by (rewrite <- E3; exact MR'm).
      exists p, m. split; [exact Hm'|]. rewrite R'.
      unfold nl_list in Hq. rewrite map_app in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
      + cbn [map fst In app] in Hq. assert (E : fst q = fst p /\ snd p - 3 <= snd q <= snd p - 1).
        { destruct Hq as [E|[E|[E|[E|[E|[]]]]]]; subst q; unfold aadd, p; cbn [fst snd]; split; first [reflexivity| lia]. }
        destruct E as [E1 E2]. split; [symmetry; exact E1|]. right. split; [rewrite Emr; reflexivity| exact E2].
      + apply in_zlist in Hq as (k & Hk & ->). unfold aadd. cbn [fst snd]. split; [reflexivity|]. left. exists k.
        split; [unfold cnt_of; rewrite Emr; cbn [m_last_idx]; clear - Hk; lia|].
        unfold sstart. replace (gbase mr') with p by (rewrite Emr; reflexivity). rewrite Es. unfold p. cbn [snd]. unfold sstart, UNIT, IB. lia. }
  split; [exact MR'm|].
  split; [unfold st'; rewrite agt_groups, E3, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros sc0; unfold st'; rewrite agt_active, E3; unfold active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  split; [intros h; unfold st'; rewrite agt_get_head, E3; unfold get_head, active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  unfold st'. rewrite agt_tick, E3. exact TK2.
Qed.
End AG_NESTED.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma round_up_pg_div x : 0 < x -> (x + 4095) / 4096 * 4096 = round_up_pg x.
Proof.
  intros Hx. destruct (round_up_pg_spec x) as [A B].
  pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as M1.
  pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)) as D2. rewrite B in D2. nia.
Qed.

Definition F63 (rid : N) (ml : Z) (mr : meta) : meta :=
  m_set_freed 0 (m_set_avail 0 (m_set_maplen ml (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr)))))).

Section CREATE63.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g : aptr) (rid : N) (r : region) (needed : Z).
Let X := mkX [g] [] None (Some rid) None.
Let p : aptr := (rid, 0).
Let X' := mkX [] [] (Some (rid, 16)) None None.
Hypothesis INV : INVL X st3 L BL LS.
Hypothesis Hr : s_regions st3 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st3 !! rid = None.
Hypothesis Hn : 0 < needed < 2 ^ 63.
Hypothesis TF : TF0 st3.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.

Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).

Lemma c63_MRg : MR st3 g = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))). reflexivity. Qed.

Lemma c63_ml : 1 <= ml < 2 ^ 52 /\ ml * 4096 = round_up_pg needed.
Proof.
  unfold ml. split; [| apply round_up_pg_div; lia].
  split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
Qed.

Lemma c63_F : F63 rid ml meta0 = mr'.
Proof.
  pose proof c63_ml as [M _]. unfold F63, mr', m_set_freed, m_set_avail, m_set_maplen, m_set_sizeclass, m_set_freeable, m_set_last_idx, m_set_mem. cbn.
  rewrite land52_id by lia. reflexivity.
Qed.

Lemma c63_stride : get_stride mr' = ml * 4096 - UNIT.
Proof. pose proof c63_ml as [M _]. unfold get_stride, mr'. cbn -[Z.mul Z.sub Z.eqb]. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Lemma c63_nogroup : s_groups st3 !! p = None.
Proof. destruct (ir_orph _ _ _ IR rid eq_refl) as (r0 & _ & _ & NG). apply NG. reflexivity. Qed.

Lemma c63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. cbn -[F63 get_meta_rec]. rewrite lookup_insert_eq. fold (MR st3 g). rewrite c63_MRg. exact c63_F. Qed.

Theorem create63_ok :
  INVL X' st6 L BL LS /\ TF0 st6 /\ MR st6 g = mr' /\ s_groups st6 !! p = Some (mkGhdr (Some g) 0)
  /\ s_ctx st6 = s_ctx st3 /\ s_tick st6 = s_tick st3 /\ s_regions st6 = s_regions st3
  /\ get_stride mr' = ml * 4096 - UNIT /\ ml * 4096 = round_up_pg needed.
Proof.
  pose proof c63_ml as [M RU]. pose proof c63_stride as Es.
  pose proof INV as (IR0 & IA & IM0 & IL & IG & IS & ISH).
  assert (Emetas : s_metas st6 = <[g := mr']> (s_metas st3)).
  { change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g). rewrite c63_MRg, c63_F. reflexivity. }
  assert (MR'g : MR st6 g = mr') by (unfold MR, get_meta_rec; rewrite Emetas, lookup_insert_eq; reflexivity).
  assert (GAI : group_active_idx st4 p = 0).
  { unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite c63_nogroup. reflexivity. }
  assert (Egroups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3)).
  { change (s_groups st6) with (s_groups st5). unfold st5. rewrite GAI. reflexivity. }
  assert (INV' : INVL X' st6 L BL LS).
  { apply (INVL_create X X' st3 st6 L BL LS g p 0 mr' INV ltac:(left; reflexivity)).
    all: cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed mr'].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - right. lia.
    - unfold tbit. repeat split; try lia; intros i Hi Hb; rewrite Z.testbit_0_l in Hb; discriminate.
    - lia.
    - fold mr'. rewrite Es. unfold UNIT. split; [lia|]. replace (ml * 4096 - 16) with ((ml * 256 - 1) * 16) by lia. apply Z_mod_mult.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - right. split; reflexivity.
    - reflexivity.
    - intros x Hx. destruct Hx.
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X' fst snd p]. apply one5_E; [rewrite Z.testbit_0_l; discriminate| rewrite Z.testbit_0_l; discriminate|].
      assert (i = 0) by lia. subst i. rewrite Z.mul_0_r. reflexivity.
    - intros s Hs. cbn [x_pend X'] in Hs. inversion Hs. subst s. exists 0. split; [lia|]. cbn [fst snd p]. rewrite Z.mul_0_r. reflexivity.
    - intros H. lia.
    - left. cbn [x_orph x_pend X X' fst snd p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. split; [exact RU|]. fold mr'. rewrite Es. unfold UNIT. lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn [fst p] in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - exact Emetas.
    - exact Egroups.
    - intros s. unfold st6. rewrite c63_rec5. rewrite lookup_add_slots; [| lia| rewrite Es; unfold UNIT; lia]. fold mr'. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - repeat split; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. replace (sc0 =? 63) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r. reflexivity.
    - intros sc0 v Hv. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { apply (TF0_ctrl (hdr_havoc p st4)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. apply (TF0_ctrl st3); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'g|]. split; [rewrite Egroups, lookup_insert_eq; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Es| exact RU].
Qed.
End CREATE63.
