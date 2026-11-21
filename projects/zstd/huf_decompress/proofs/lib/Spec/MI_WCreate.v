(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (32 recorded proofs replaced by written proofs (res_excl, one5_iff_create, C_MR and 29 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WGroup.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WCreate () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List7map_extC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C47Corelib4Init5Logic3notK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC35stdpp8fin_maps:map_insertI35stdpp8fin_maps6FinMap00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp8fin_maps;map_to_listC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC46Stdlib5Lists4List8map_consC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6InsertC46Stdlib5Lists4List:map_ext_inC35stdpp4base?list_elem_of_InC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base5EmptyC35stdpp8fin_mapsCelem_of_map_to_listC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp8fin_mapsBmap_to_list_insertC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps7MapFoldC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indI47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7im_idleC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj2I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate7m_meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List=In_removelastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List5In_tlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4=idle_not_liveC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit<aptr_eqb_neqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate4C_MRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7ir_orphC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate8C_groupsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate7C_hostsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate6p_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate:m_not_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate>C_hosts_old_neC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate:C_MR_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib4Spec:MI_WCreate6gbase'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate7sstart'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_InvBslot_start'_sstartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N6eqb_eqC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6NArith6BinNat1N8eqb_reflC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega7EnvRing3Pol02C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multc59OSSVerify5KrLib4Spec:MI_WCreate5nslotC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega3Op206c59OSSVerify5KrLib4Spec:MI_WCreate7C_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate=new_key_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom8sep_hdr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;sstart_succC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec7MI_Geom8hosts_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate@old_slot_not_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5g_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9is_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6im_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreateAold_hosts_not_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill7none_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill5gtermC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:fold_rightI35stdpp4base<list_elem_of00C35stdpp4base7elem_ofC59OSSVerify5KrLib4Spec8MI_WKill9zsum_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill;gcnt_unfoldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate3MRmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate6C_MR_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ish_ticksC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC35stdpp8fin_maps<lookup_emptyC56Stdlib6NArith6BinNat1N7compareC59OSSVerify5KrLib4Spec9MI_Shadow8hl_ticksC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_ShadowGcell_read_hdr_havoc_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit>get_shadow_extC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate4C_TKC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate:C_read_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec9MI_ShadowFcell_read_hdr_havoc_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_alignC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC59OSSVerify5KrLib4Spec7MI_Geom;hosts_gbaseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib4Spec:MI_WCreate=C_unknown_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate=C_unknown_hdrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate8res_exclC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate;C_known_outC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapC59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom7sep_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflc59OSSVerify5KrLib4Spec:MI_WCreate:C_frontierC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_transK59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate6C_keysC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_symc59OSSVerify5KrLib4Spec:MI_WCreate6gcnt_CC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate;C_hosts_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00c59OSSVerify5KrLib4Spec:MI_WCreate:C_get_headC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:removelastC46Stdlib5Lists4List:in_app_iffc59OSSVerify5KrLib4Spec:MI_WCreate:m_unlistedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC59OSSVerify5KrLib4Spec7MI_List:linked_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate;C_slots_oldC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9g_partialC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate5slot'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate;C_slots_newC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate;C_MR_hostedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib4Spec:MI_WCreate;blk_not_newC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate9p_not_newC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate=new_not_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate?one5_iff_createC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom7sstart0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;sstart_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WNtf8one5_iffC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6inv_SH01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ig_regionC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specC59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup=TKS_hdr_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate8hdr0_resC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate;C_known_resC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MI_WCreate=C_unknown_anyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallc59OSSVerify5KrLib4Spec:MI_WCreate9blk_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityC59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma res_excl a o : a mod 16 = 0 -> 12 <= o mod 16 -> ~ (a <= o < a + 12).
Proof.
  intros Ha Ho [H1 H2]. pose proof (Z.div_mod a 16 ltac:(lia)) as Da. pose proof (Z.div_mod o 16 ltac:(lia)) as Do.
  pose proof (Z.mod_pos_bound o 16 ltac:(lia)) as Bo. rewrite Ha in Da.
  set (qa := a / 16) in *. set (qo := o / 16) in *. set (r := o mod 16) in *. clearbody qa qo r. lia.
Qed.

(* [comment removed for export] *)
Lemma one5_iff_create (A B E : Prop) (C D : Prop) : one5 A B False False E -> ~ C -> ~ D -> one5 A B C D E.
Proof. unfold one5. tauto. Qed.

Section CREATE.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m p : aptr) (ai : Z) (mr' : meta).
Hypothesis INV : INVL X st L BL LS.
Hypothesis IDLE : In m (x_idle X).

(* [comment removed for export] *)
Let sc' := m_sizeclass mr'.
Let last' := m_last_idx mr'.
Let cnt := last' + 1.
Let stride' := get_stride mr'.
Hypothesis R_prev : m_prev mr' = None.
Hypothesis R_next : m_next mr' = None.
Hypothesis R_mem : m_mem mr' = Some p.
Hypothesis R_freeable : m_freeable mr' = 1.
Hypothesis R_maplen : 0 <= m_maplen mr'.
Hypothesis R_li : 0 <= last' <= 31.
Hypothesis R_ai : 0 <= ai <= last'.
Hypothesis R_full0 : sc' = 0 -> ai = last'.
Hypothesis R_sc : (0 <= sc' < 48 /\ m_maplen mr' <= 256) \/ (sc' = 63 /\ last' = 0 /\ m_maplen mr' <> 0).
Hypothesis R_masks : 0 <= m_avail mr' /\ 0 <= m_freed mr'
  /\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> i <= ai)
  /\ (forall i, 0 <= i -> tbit (m_freed mr') i = true -> i <= last')
  /\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> tbit (m_freed mr') i = true -> False)
  /\ (forall i, ai < i <= last' -> tbit (m_freed mr') i = true).
Hypothesis R_stride : sc' < 48 ->
  (stride' <= UNIT * size_class sc' \/ 28 <= sc') /\ (last' = 0 -> m_maplen mr' <> 0 /\ 27 <= sc') /\ stride' * cnt < 2^20.
Hypothesis R_stride16 : 16 <= stride' /\ stride' mod 16 = 0.
Hypothesis R_align : 0 <= snd p /\ snd p mod UNIT = 0.

(* [comment removed for export] *)
Hypothesis X_fresh : x_fresh X' = Some m \/ (sc' = 63 /\ x_fresh X' = x_fresh X).
Hypothesis X_fresh_old : x_fresh X = None.
Hypothesis X_idle : forall x, In x (x_idle X') -> In x (x_idle X) /\ x <> m.
Hypothesis X_zomb : x_zomb X' = x_zomb X.
Hypothesis X_nozomb : x_zomb X = [].
Hypothesis X_part : forall i, 0 <= i <= last' ->
  one5 (tbit (m_avail mr') i = true) (tbit (m_freed mr') i = true) False False (x_pend X' = Some (fst p, snd p + UNIT + stride' * i)).
Hypothesis X_pend' : forall s, x_pend X' = Some s -> exists i, 0 <= i <= last' /\ s = (fst p, snd p + UNIT + stride' * i).
(* [comment removed for export] *)
Hypothesis NOPART : ai < last' -> LS (LActive sc') = [].

(* [comment removed for export] *)
Hypothesis SITE :
  (m_maplen mr' <> 0 /\ snd p = 0 /\ x_orph X = Some (fst p) /\ x_orph X' = None /\ x_pend X = None
     /\ exists r, s_regions st !! (fst p) = Some r /\ r_kind r = RKGroup /\ m_maplen mr' * 4096 = round_up_pg (r_len r)
        /\ snd p + UNIT + stride' * cnt <= m_maplen mr' * 4096)
  \/ (m_maplen mr' = 0 /\ x_pend X = Some p /\ x_pend X' = None /\ x_orph X' = x_orph X /\ x_orph X = None
     /\ exists pm ip bpm, s_slots st !! p = Some (pm, ip) /\ hosts st bpm pm /\ fst bpm = fst p /\ 0 <= ip <= m_last_idx (MR st pm)
        /\ p = (fst bpm, sstart (MR st pm) ip)
        /\ snd p + UNIT + stride' * cnt <= sstart (MR st pm) ip + get_stride (MR st pm)
        /\ sc' < m_sizeclass (MR st pm) < 48 /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
        /\ (exists v3, known st (fst p, snd p - 3) v3 /\ Z.land v3 31 = ip /\ 0 <= v3 < 256)
        /\ known st (fst p, snd p - 2) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 0)
        /\ known st (fst p, snd p - 1) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 1)
        /\ 0 <= (snd p - snd bpm - UNIT) / UNIT < 2^16).

(* [comment removed for export] *)
Hypothesis SH_hdr0 : forall i, 0 <= i <= cnt -> known st (fst p, snd p + UNIT + stride' * i - IB) 0.
Hypothesis SH_ghdr : forall o v tk, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, tk) -> (tk < s_tick st)%N.

(* [comment removed for export] *)
Hypothesis E_metas : s_metas st' = <[m := mr']> (s_metas st).
Hypothesis E_groups : s_groups st' = <[p := mkGhdr (Some m) ai]> (s_groups st).
Hypothesis E_slots : forall s, s_slots st' !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride' =? 0) && ((snd s - snd p - UNIT) / stride' <? cnt)
  then Some (m, (snd s - snd p - UNIT) / stride') else s_slots st !! s.
Hypothesis E_shadow : s_shadow st' = s_shadow (hdr_havoc p st).
Hypotheses (E_regions : s_regions st' = s_regions st) (E_areas : s_areas st' = s_areas st) (E_next_rid : s_next_rid st' = s_next_rid st)
           (E_tick : s_tick st' = s_tick st) (E_secret : s_secret st' = s_secret st) (E_reserved : s_reserved st' = s_reserved st)
           (E_atop : s_atop st' = s_atop st).
Hypothesis E_ctx :
  c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
  /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st) /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st)
  /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st) /\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st)
  /\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st) /\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st)
  /\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st) /\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st)
  /\ c_active (s_ctx st') = c_active (s_ctx st) /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st).
Hypothesis E_mc : 0 <= c_mmap_counter (s_ctx st') < 2^32.
Hypothesis E_usage : forall sc0, 0 <= sc0 < 48 -> usage st' sc0 = usage st sc0 + (if sc0 =? sc' then cnt else 0).
Hypothesis E_usage_keys : forall sc0 v, c_usage (s_ctx st') !! sc0 = Some v -> 0 <= sc0 < 48.

(* [comment removed for export] *)
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Ltac slim := try clear SITE; try clear E_ctx; try clear E_slots; try clear X_part; try clear X_pend'; try clear R_masks; try clear R_stride; try clear R_sc;
             try clear E_usage; try clear E_usage_keys; try clear SH_hdr0; try clear SH_ghdr; try clear X_idle; try clear NOPART.
Local Tactic Notation "lia" := slim; Lia.lia.
Local Tactic Notation "nia" := slim; Lia.nia.

Lemma m_meta0 : s_metas st !! m = Some meta0.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "p;1p;4p;6p;2p;3g00lGj1<Tg00lij4;Tg00mGj60Tg00gHj41Tg00Zlj4:Tg00mhj12Tg00n`j63Tg00o4j24Tg0039j35Tg00oVj26Tg00I=j17Tg010Nj68Tg011Fj39Tg011aR0#<g00ThR1P0P1g012XR2g0136R3g00KkR4g013OR5C;R6P2P3g013hP4P5g014FE0R5P0C1P1P6P5P0C:p,1mR5p,2stR6#2E3g014d,4035p,2LSR0/65#7p,1XP6P0p,2IMP5p,4IDLEE839o"). Qed.
Lemma m_unlisted h : ~ In m (LS h).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "h01hh11Hp;3p;1p;4p;6p;2g015Zj3>Tg00lGj1=Tg00lij42Tg00mGj61Tg00gHj4<Tg00Zlj48Tg00mhj13Tg00n`j64Tg00o4j25Tg0039j36Tg00oVj27Tg00I=j10Tg010Nj69Tg0161j4;Tg016Kj4:Tg016fR0g00ThR1p,1mR2p,2LSR3f0R4O13>R5g011aR6#=P1P6P1g012XR7g0136R8g00KkR9g013OR:C2R;P7P8g013hP9P:g014FE1R:P6C<P1P;P:P6C8P2p,2stR:#3E4g014d,56361732#0p,1XP:P3p,2IMP2p,4IDLEE9P0P5X00f1P4C;C:W1%05eX00P4O1W0o"). Qed.
Lemma MRm : MR st m = meta0.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "h01op;1p;2p;5p;3p;4p;6g00lGj1=Tg00o4j2<Tg017^j12Tg018:j51Tg0039j30Tg00:8j2:Tg00lij43Tg00mGj64Tg00gHj45Tg00Zlj46Tg00mhj17Tg00n`j68Tg0018j69Tg018Uj2;Tg011aR0#=R1g014dR2,<0P0P0%20P2f0D1=002X011:02g00ThR1P0P1g012XR3g0136R4g00KkR5g013OR6C3R7P3P4g013hP5P6g014FE4R6P0C5P1P7P6P0C6p,1mR6p,2stR7#7E8g019HE91;76=002eo"). Qed.
Lemma m_not_live : ~ live_group st m.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "p;8p100Thp4p70R0p101:Dp4p710p8P0p101;Cp4p710p8g01<:j80Tp,1Xp,2stp,1Lp,2BLp,2LSp,3INVp,1mp,4IDLEG0o"). Qed.

Lemma C_MR x : MR st' x = if aptr_eqb x m then mr' else MR st x.
Proof. unfold MR, get_meta_rec. rewrite E_metas. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
Lemma C_MR_other x : x <> m -> MR st' x = MR st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "h01xh12NEh21bh31mp;3p;1p;2p;6g0039j30Tg00I=j17Tg01=Nj23Tg018Uj21Tg00:8j26Tg01A@j35Tg0018j62Tg01B=j14Tg00ThR0f0R1p,1mR2500#7g011aR3g00QbR4P3f1R5/32R6p,3mr'R7p,2stR8/15R9n0100000020000f2,18R89031X33P4g01C6P4P3P1P7P8n0100000020000=038X241639P6A5521E2p,3st'/15%45E2W1X00P1O1W0o"). Qed.
Lemma C_MR_m : MR st' m = mr'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "h01bh11mp;2p;3p;1p;6g01=Nj26Tg018Uj22Tg0039j30Tg00:8j23Tg01CVj15Tg0018j61Tg01B=j14Tg011aR0g00QbR1P0p,1mR2/62R3p,3mr'R4p,2st/22R5n0100000020000f0R6=004X10P1g00RBP1P0P6P4P5n0100000020000=004X011304P3%52E1p,3st'/22%42E1o"). Qed.
Lemma C_keys x : s_metas st' !! x <> None <-> s_metas st !! x <> None.
Proof. rewrite E_metas. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite lookup_insert_eq, m_meta0; split; discriminate| rewrite lookup_insert_ne by congruence; tauto]. Qed.

(* [comment removed for export] *)
Lemma p_free : s_groups st !! p = None.
Proof.
  destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & _)].
  - destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). apply NG. reflexivity.
  - destruct Hpm as [aipm Hpm]. pose proof (is_part _ _ _ IS _ _ _ ip Hpm Hip) as P. cbn zeta in P.
    rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm)), <- Ep, HP in P. unfold one5 in P.
    destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.

Lemma C_groups b : s_groups st' !! b = if aptr_eqb b p then Some (mkGhdr (Some m) ai) else s_groups st !! b.
Proof. rewrite E_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
Lemma C_hosts b x : hosts st' b x <-> (b = p /\ x = m) \/ (b <> p /\ hosts st b x).
Proof.
  unfold hosts. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
  - split; [intros [a H]; inversion H; auto| intros [[_ ->]|[NE _]]; [exists ai; reflexivity| congruence]].
  - split; [intros H; right; auto| intros [[E _]|[_ H]]; [congruence| exact H]].
Qed.
Lemma C_hosts_old b x : hosts st b x -> hosts st' b x.
Proof. intros H. apply C_hosts. destruct (aptr_eq_dec b p) as [->|NE]; [| right; auto]. destruct H as [a H]. rewrite p_free in H. discriminate. Qed.
Lemma C_hosts_old_ne b x : hosts st b x -> x <> m.
Proof. intros H ->. exact (m_not_live (ex_intro _ b H)). Qed.
Lemma C_MR_hosted b x : hosts st b x -> MR st' x = MR st x.
Proof. intros H. apply C_MR_other. exact (C_hosts_old_ne b x H). Qed.

(* [comment removed for export] *)
Lemma gbase' : gbase mr' = p.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "h01op;2p;1p;4p;5p;3p;6g00o4j29Tg01`^j28Tg017^j12Tg01b6j41Tg018:j57Tg0039j30Tg00:8j23Tg02<hj14Tg0018j65Tg02=^j16Tg00a;R0g00ThR1p,1pR2'9g012XR3g00KkR4'8R5P5%25P3P4g02>Tg00P;C1f0D7=012X001312p,3mr'R0#4p,5R_memE5%60=012eo"). Qed.
Lemma sstart' i : sstart mr' i = snd p + UNIT + stride' * i.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "h01ih11ap;3p;2p;1p;6g01H2j32Tg004Tj20Tg01e>j14Tg00=Mj21Tg0039j33Tg00:8j28Tg02=^j17Tg0018j65Tg01dGj26Tg00KkR0g00ThR1p,1pR2g012XR3f0R4720g01kQR5'0p,3mr'R6#4f1R7'1'0A2302/05R5p,7stride'R3/17'0530X111134,05R5,80%76g02?2E51664=305eX00P4O1W0o"). Qed.
Lemma slot' i : slot_start' mr' i = (fst p, snd p + UNIT + stride' * i).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WCreate ()) ["CREATE"] "h01ah11ih21zp;1p;2p;3p;6p;4g02=^j1>Tg01dGj25Tg01H2j3=Tg004Tj22Tg00=Mj26Tg0039j33Tg00:8j29Tg02?mj18Tg0018j61Tg023Jj27Tg02@ij2:Tg00YYj3<Tg01b6j4;Tg012XR0g00KkR1f0R23<p=4P0P1f1R3P2C;p=0g00ThR4p,3mr'R5#>R6#41552R7'0p,1pR8#4R9A=018g01kQ'2R0p,7stride'R:/63'2'0R;9342X04P4P8%421553'0=34;X04P116:2,20R01092=34;X211090,94P7%82E1P6g02?2E117521:52E1X11P2O1X11o"). Qed.

(* [comment removed for export] *)
Definition nslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j).
Lemma C_slots s : (s_slots st' !! s = s_slots st !! s /\ ~ nslot s) \/ (exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j) /\ s_slots st' !! s = Some (m, j)).
Proof.
  unfold nslot. pose proof (E_slots s) as ES. destruct R_stride16 as [SP SM]. clear - ES SP SM. subst cnt last'.
  rewrite ES. clear ES. set (d := snd s - snd p - UNIT).
  destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod stride' =? 0) && (d / stride' <? m_last_idx mr' + 1)) eqn:E.
  - right. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
    apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
    exists (d / stride'). split; [split; [apply Z.div_pos; lia| exact E4]|]. split; [| reflexivity].
    pose proof (Z.div_mod d stride' ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
    destruct s as [sr so]. cbn in E1, d |- *. subst sr. f_equal. lia.
  - left. split; [reflexivity|]. intros (j & Hj & Es). subst s. cbn in d.
    assert (Ed : d = stride' * j) by (unfold d; lia). clearbody d.
    rewrite N.eqb_refl in E. cbn in E.
    assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; nia). rewrite E2 in E. cbn in E.
    assert (E3 : (d mod stride' =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult). rewrite E3 in E. cbn in E.
    assert (E4 : (d / stride' <? m_last_idx mr' + 1) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia). rewrite E4 in E. discriminate.
Qed.
Lemma C_slots_old s : ~ nslot s -> s_slots st' !! s = s_slots st !! s.
Proof. intros N. destruct (C_slots s) as [[E _]|(j & Hj & Es & _)]; [exact E|]. exfalso. apply N. exists j. auto. Qed.
Lemma C_slots_new j : 0 <= j < cnt -> s_slots st' !! (fst p, snd p + UNIT + stride' * j) = Some (m, j).
Proof.
  intros Hj. destruct (C_slots (fst p, snd p + UNIT + stride' * j)) as [[_ N]|(j' & Hj' & Es & E)]; [exfalso; apply N; exists j; auto|].
  rewrite E. inversion Es. destruct R_stride16 as [SP _]. assert (j' = j) by (clear - H0 SP Hj Hj'; nia). subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma new_key_range j : 0 <= j < cnt -> snd p < snd p + UNIT + stride' * j /\ snd p + UNIT + stride' * j + 16 <= snd p + UNIT + stride' * cnt.
Proof. intros Hj. destruct R_stride16 as [SP _]. clear - Hj SP. subst cnt last'. unfold UNIT. split; [nia|]. assert (stride' * j + stride' <= stride' * (m_last_idx mr' + 1)) by nia. lia. Qed.

Lemma old_slot_not_new s x i : s_slots st !! s = Some (x, i) -> ~ nslot s.
Proof.
  intros Hs (j & Hj & ->). destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es. inversion Es.
  destruct (new_key_range j Hj) as [K1 K2].
  destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hf & Hip & Ep & FIT & _)].
  - (* [comment removed for export] *)
    destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx]. rewrite (NG bx) in Hxx; [discriminate|]. rewrite <- H0. reflexivity.
  - (* [comment removed for export] *)
    destruct Hpm as [aipm Hpm'].
    assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
    assert (Hf2 : fst bx = fst bpm) by (rewrite Ep in H0; cbn in H0; congruence).
    assert (Hi2 : 0 <= i <= m_last_idx (MR st x) + 1) by (clear - Hi; lia).
    pose proof (@sep_hdr0 _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi2) as D.
    rewrite sstart_succ in D. rewrite Ep in H1, K1, K2, FIT. cbn in H1, K1, K2, FIT.
    assert (NEQ : x <> pm \/ i <> ip).
    { destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->. clear - H1 K1. lia. }
    specialize (D NEQ). clear - D H1 K1 K2 FIT Hj. lia.
Qed.

Lemma old_hosts_not_new b x : hosts st b x -> ~ nslot b.
Proof.
  intros Hx N. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO).
  destruct (Z.eq_dec (m_maplen (MR st x)) 0) as [Hml|Hml].
  - destruct (g_nest _ _ _ _ _ _ GO Hml) as (px & ix & Hs & _). exact (old_slot_not_new _ _ _ Hs N).
  - destruct (g_top _ _ _ _ _ _ GO Hml) as [B0 _]. destruct N as (j & Hj & ->). cbn in B0. destruct (new_key_range j Hj) as [K1 K2]. destruct R_align as [A0 _]. clear - B0 K1 A0. lia.
Qed.

Lemma p_not_new : ~ nslot p.
Proof. intros (j & Hj & E). destruct (new_key_range j Hj) as [K _]. apply (f_equal snd) in E. cbn in E. clear - K E. lia. Qed.

Lemma blk_not_new k : In k BL -> ~ nslot (bslot k).
Proof. intros Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). exact (old_slot_not_new _ _ _ Hs). Qed.

(* [comment removed for export] *)
Lemma new_not_group j : 0 <= j < cnt -> s_groups st !! (fst p, snd p + UNIT + stride' * j) = None.
Proof.
  intros Hj. destruct (s_groups st !! (fst p, snd p + UNIT + stride' * j)) as [h|] eqn:E; [| reflexivity]. exfalso.
  destruct (im_hdr _ _ _ IM _ _ E) as (x & Ex & _). apply (old_hosts_not_new (fst p, snd p + UNIT + stride' * j) x); [| exists j; auto].
  destruct h as [hm ha]. cbn in Ex. subst hm. exists ha. exact E.
Qed.

Lemma gcnt_C sc0 : gcnt st' sc0 = (if sc' =? sc0 then cnt else 0) + gcnt st sc0.
Proof.
  rewrite !gcnt_unfold, E_groups.
  rewrite (zsum_perm _ _ (Permutation_map (gterm st' sc0) (map_to_list_insert (s_groups st) p (mkGhdr (Some m) ai) p_free))). cbn.
  unfold gterm at 1. cbn. rewrite C_MR_m. fold sc' cnt. f_equal.
  f_equal. apply map_ext_in. intros [b hb] Hin. apply In_map_to_list_regions in Hin || (apply (proj2 (list_elem_of_In _ _)) in Hin; apply elem_of_map_to_list in Hin).
  unfold gterm. cbn. destruct (g_meta hb) as [x|] eqn:Ex; [| reflexivity].
  rewrite (C_MR_other x); [reflexivity|]. intros ->.
  destruct (im_hdr _ _ _ IM _ _ Hin) as (x' & Ex' & Hmem & _). rewrite Ex in Ex'. inversion Ex'. subst x'. rewrite MRm in Hmem. discriminate.
Qed.

Lemma C_get_head h : get_head st' h = get_head st h.
Proof.
  destruct E_ctx as (_ & _ & F3 & _ & _ & _ & _ & _ & _ & _ & F11 & _). destruct h; cbn; unfold active, ctx; rewrite ?F11, ?F3; reflexivity.
Qed.
Lemma C_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. destruct E_ctx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _). unfold frontier. rewrite F10. reflexivity. Qed.

(* [comment removed for export] *)
Lemma C_TK u hl : r_hav (get_shadow st (fst p)) !! u = Some hl -> hl_ticks hl (s_tick st).
Proof.
  intros Hu ch Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn in Hu.
  - exact (proj1 (proj2 (ish_ticks _ _ ISH _ _ E)) u hl ch Hu Hin).
  - rewrite lookup_empty in Hu. discriminate.
Qed.
Lemma C_read_out q : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros Hq. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst q) E_shadow). apply (cell_read_hdr_havoc_out p st (proj2 R_align) C_TK q Hq). Qed.
Lemma C_known_out q v : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
Lemma C_unknown_out q : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
Lemma C_unknown_hdr o : 0 <= o < 12 -> unknown st' (fst p, snd p + o).
Proof.
  intros Ho. unfold unknown, SHd. cbn [fst snd]. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst p) E_shadow).
  apply (cell_read_hdr_havoc_in p st (proj2 R_align) (fst p, snd p + o)); [reflexivity| cbn; lia|].
  cbn [fst snd]. intros v tk H. apply (SH_ghdr (snd p + o) v tk); [clear - Ho; lia| exact H].
Qed.

Lemma hdr0_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
  intros Hx. pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG SM]. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase _ _ _ IM _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma C_unknown_any q : unknown st q -> unknown st' q.
Proof.
  intros U. destruct (N.eq_dec (fst q) (fst p)) as [E|NE]; [| apply C_unknown_out; [tauto| exact U]].
  destruct (Z.lt_ge_cases (snd q) (snd p)) as [L1|G1]; [apply C_unknown_out; [lia| exact U]|].
  destruct (Z.lt_ge_cases (snd q) (snd p + 12)) as [L2|G2]; [| apply C_unknown_out; [lia| exact U]].
  replace q with (fst p, snd p + (snd q - snd p)) by (destruct q; cbn in *; subst; f_equal; lia). apply C_unknown_hdr. lia.
Qed.

Lemma C_known_res q v : 12 <= snd q mod 16 -> known st q v -> known st' q v.
Proof. intros R K. apply C_known_out; [| exact K]. intros [_ H]. exact (res_excl _ _ (proj2 R_align) R H). Qed.

(* [comment removed for export] *)
Lemma blk_clear k x i : In k BL -> s_slots st !! bslot k = Some (x, i) -> fst (bslot k) = fst p ->
  snd (bslot k) + get_stride (MR st x) - IB <= snd p \/ snd p + 12 <= snd (bslot k) - IB.
Proof.
  intros Hk Hs Hf. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
  destruct SITE as [(Hml & P0 & HO & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hfp & Hip & Ep & _)].
  - exfalso. destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx].
    rewrite (NG bx) in Hxx; [discriminate|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ a Hxx)) in Es. rewrite Es in Hf. exact Hf.
  - destruct Hpm as [aipm Hpm']. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es.
    assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
    assert (Hf2 : fst bx = fst bpm) by (rewrite Es, Ep in Hf; cbn in Hf; exact Hf).
    pose proof (is_part _ _ _ IS _ _ _ i (proj2 (hosts_ok _ _ _ IG _ _ Hx) ) Hi) as P5 || pose proof I as P5.
    destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx).
    pose proof (is_part _ _ _ IS _ _ _ i Hbx Hi) as Q5. cbn zeta in Q5. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx), <- Es in Q5. unfold one5 in Q5.
    assert (U : In (bslot k) (map bslot BL)) by (apply in_map; exact Hk).
    assert (NH2 : s_groups st !! (fst bx, sstart (MR st x) i) = None).
    { rewrite <- Es. apply none_of. intros Hh. destruct Q5 as (_ & _ & _ & _ & _ & _ & _ & _ & nCD & _). apply nCD. split; [exact U| exact Hh]. }
    assert (NE : x <> pm \/ i <> ip).
    { destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->.
      pose proof (is_part _ _ _ IS _ _ _ ip Hpm' Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm')), <- Ep, HP in P.
      unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity].
      pose proof (hosts_inj _ _ _ IM _ _ _ Hx (ex_intro _ aipm Hpm')) as Ebx. rewrite Ebx in Es. rewrite Ep, <- Es. exact U. }
    pose proof (@sep_ext _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi NE NH2) as D.
    rewrite !sstart_succ in D. rewrite Es. cbn [snd]. rewrite Ep. cbn [snd].
    pose proof (stride_ge _ _ _ IG _ _ (ex_intro _ aipm Hpm')) as [SGp _]. unfold IB, UNIT in *. clear - D SGp. lia.
Qed.

Theorem INVL_create : INVL X' st' L BL LS.
Proof.
  destruct E_ctx as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
  destruct R_masks as (W1 & W2 & W3 & W4 & W5 & W6). destruct R_stride16 as [SP SM]. destruct R_align as [P0 P16].
  assert (XO : forall rid, x_orph X' = Some rid -> x_orph X = Some rid /\ m_maplen mr' = 0).
  { intros rid Ho. destruct SITE as [(_ & _ & _ & HO' & _)|(Hml & _ & _ & HO' & _)]; [rewrite HO' in Ho; discriminate| rewrite HO' in Ho; auto]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?E_regions, ?E_next_rid, ?E_reserved, ?E_atop, ?F6, ?F7, ?F10, ?F15; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite C_frontier. reflexivity.
    + intros rid r H1 H2. rewrite C_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite C_frontier. exact (ir_brkfront rid r H1 H2).
    + intros rid Ho. destruct (XO rid Ho) as [Ho' Hml]. destruct (ir_orph rid Ho') as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
      intros b Hb. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [| exact (NG b Hb)]. exfalso.
      destruct SITE as [(Hml' & _)|(_ & _ & _ & _ & HO0 & _)]; [exact (Hml' Hml)| rewrite HO0 in Ho'; discriminate].
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?E_regions, ?E_areas, ?E_secret, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14; try assumption.
    + destruct ia_ctx as (_ & C2 & C3 & C4). split; [exact E_mc|]. auto.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite C_frontier. auto.
    + intros x mr Hx. assert (K : s_metas st' !! x <> None) by congruence. apply C_keys in K. destruct (s_metas st !! x) as [mr0|] eqn:E; [| congruence]. exact (ia_metas x mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply C_keys in K. apply K. apply Hk. exact Hk2.
    + intros sc0 Hsc0. rewrite (E_usage sc0 Hsc0), (ia_usage sc0 Hsc0), gcnt_C. rewrite Z.eqb_sym. destruct (sc' =? sc0); lia.
  - (* [comment removed for export] *) destruct IM as [Q1 Q2 Q3 Q4 Q5] eqn:EIM; constructor.
    + intros x Hx. destruct (aptr_eq_dec x m) as [E|NE]; [subst x; rewrite C_MR_m, R_mem in Hx; discriminate|]. rewrite (C_MR_other x NE) in Hx |- *. exact (Q1 x Hx).
    + intros x b Hx. rewrite X_zomb. destruct (aptr_eq_dec x m) as [E|NE].
      * subst x. rewrite C_MR_m, R_mem in Hx. inversion Hx. subst b. left. apply C_hosts. left. auto.
      * rewrite (C_MR_other x NE) in Hx. destruct (Q2 x b Hx) as [H|H]; [left; apply C_hosts_old; exact H| right; exact H].
    + intros b h. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
      * intros E. inversion E. subst h. exists m. cbn. rewrite C_MR_m, R_mem. fold last'. auto.
      * intros Hb. destruct (Q3 b h Hb) as (x & Ex & Hmem & Hai). exists x.
        assert (NEx : x <> m) by (intros ->; rewrite MRm in Hmem; discriminate). rewrite (C_MR_other x NEx). auto.
    + intros x Hx. destruct (X_idle x Hx) as [Hx' NE]. destruct (Q4 x Hx') as [E NI]. split; [| exact NI]. rewrite E_metas, lookup_insert_ne by congruence. exact E.
    + intros z Hz. rewrite X_zomb, X_nozomb in Hz. destruct Hz.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. rewrite C_get_head. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros x Hx; rewrite C_MR_other; try reflexivity; intros ->; apply (m_unlisted h); rewrite E.
      * apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
      * apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
    + intros x. destruct (aptr_eqb_spec x m) as [->|NE].
      * rewrite C_MR_m, R_next, R_prev. split; [| reflexivity]. split; [intros [h H]; exfalso; exact (m_unlisted h H)| intros H; exfalso; apply H; reflexivity].
      * rewrite (C_MR_other x NE). apply L5.
    + intros x Hx. destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE). apply L6. exact Hx.
    + intros sc x Hx. destruct (L7 sc x Hx) as (A1 & [b Hb] & A3).
      destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE).
      split; [exact A1|]. split; [exists b; apply C_hosts_old; exact Hb| exact A3].
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
    + intros x b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
      * (* [comment removed for export] *)
        intros E. inversion E. subst x aix. constructor; rewrite ?C_MR_m, ?E_regions; fold sc' last' stride'.
        -- apply C_keys. rewrite m_meta0. discriminate.
        -- exact R_li.
        -- exact R_ai.
        -- destruct R_sc as [A|(A1 & A2 & A3)]; [left; exact A| right]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros [h H]. exact (m_unlisted h H).
        -- exact R_freeable.
        -- exact R_maplen.
        -- exact (conj W1 (conj W2 (conj W3 (conj W4 (conj W5 W6))))).
        -- intros NF Hlt. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)|]. destruct R_sc as [[A _]|(_ & L0 & _)]; unfold sc' in *; lia.
        -- intros NF Hsc NI. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
        -- intros NF sc Hin Hnh. exfalso. exact (m_unlisted _ Hin).
        -- exact R_stride.
        -- intros NF Hsc LT. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
        -- exact (conj P0 P16).
        -- intros Hml. destruct SITE as [(_ & B0 & _ & _ & _ & r & Hr & Hk & Hlen & Hend)|(Hml0 & _)]; [| exfalso; exact (Hml Hml0)].
           split; [exact B0|]. exists r. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|].
           unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact Hend.
        -- intros Hml. destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & FIT & Hsc & Hstr & _)]; [exfalso; exact (Hml1 Hml)|].
           exists pm, ip. rewrite (C_MR_hosted _ _ Hpm). split; [rewrite C_slots_old; [exact Hs| exact p_not_new]|].
           rewrite (hosts_gbase _ _ _ IM _ _ Hpm). split; [exact Hf|]. split; [| split; [exact Hsc| exact Hstr]].
           unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact FIT.
        -- exact R_full0.
      * (* [comment removed for export] *)
        intros Hb. pose proof (G1 x b aix Hb) as GO. assert (Hx : hosts st b x) by (exists aix; exact Hb).
        pose proof (C_hosts_old_ne _ _ Hx) as NEx. assert (NF : x_fresh X <> Some x) by (rewrite X_fresh_old; discriminate).
        assert (NF' : x_fresh X' <> Some x) by (destruct X_fresh as [XF|[_ XF]]; rewrite XF; [congruence| rewrite X_fresh_old; discriminate]).
        destruct GO; constructor; rewrite ?(C_MR_other x NEx), ?E_regions; try assumption.
        -- apply C_keys. exact g_present.
        -- intros _. exact (g_partial NF).
        -- intros _. exact (g_unlisted NF).
        -- intros _. exact (g_rest NF).
        -- intros _. exact (g_under NF).
        -- intros Hml. destruct (g_nest Hml) as (px & ix & Hs & REST). exists px, ix.
           destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
           split; [rewrite C_slots_old; [exact Hs| exact (old_slot_not_new _ _ _ Hs)]| exact REST].
    + intros b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb]; [discriminate| exact (G2 b aix)].
    + intros m1 m2 b1 b2 ai1 ai2. rewrite !C_groups.
      destruct (aptr_eqb_spec b1 p) as [->|N1]; destruct (aptr_eqb_spec b2 p) as [->|N2].
      * intros E1 E2. inversion E1. inversion E2. subst. reflexivity.
      * intros E1 H2. inversion E1. subst m1 ai1. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai2 H2)). fold last' sc'. intros P1 P2 Esc.
        exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H2) ltac:(rewrite X_fresh_old; discriminate) P2) as IN. rewrite <- Esc, (NOPART P1) in IN. exact IN.
      * intros H1 E2. inversion E2. subst m2 ai2. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai1 H1)). fold last' sc'. intros P1 P2 Esc.
        exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H1) ltac:(rewrite X_fresh_old; discriminate) P1) as IN. rewrite Esc, (NOPART P2) in IN. exact IN.
      * intros H1 H2. rewrite (C_MR_hosted _ _ (ex_intro _ ai1 H1)), (C_MR_hosted _ _ (ex_intro _ ai2 H2)). exact (G3 m1 m2 b1 b2 ai1 ai2 H1 H2).
    + intros rid r Hr Hk Ho. rewrite E_regions in Hr.
      destruct (N.eq_dec rid (fst p)) as [->|NE].
      * destruct SITE as [(Hml & B0 & HO & _)|(Hml & _ & _ & HO' & HO & _)].
        -- exists m. split; [apply C_hosts; left; split; [destruct p; cbn in B0 |- *; subst; reflexivity| reflexivity]|]. rewrite C_MR_m. exact Hml.
        -- destruct (G4 (fst p) r Hr Hk ltac:(rewrite HO; discriminate)) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
      * assert (Ho0 : x_orph X <> Some rid).
        { destruct SITE as [(_ & _ & HO & _)|(_ & _ & _ & HO' & HO & _)]; [rewrite HO; congruence| rewrite HO; discriminate]. }
        destruct (G4 rid r Hr Hk Ho0) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
    + intros b h. rewrite C_groups, E_regions. destruct (aptr_eqb_spec b p) as [->|NEb]; [| exact (G5 b h)]. intros _.
      destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & _)]; [exists r; auto|].
      destruct Hpm as [a Hpm]. destruct (G5 _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto.
  - (* [comment removed for export] *) destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
    + intros s x i Hs. destruct (C_slots s) as [[Es NS]|(j & Hj & -> & Es)].
      * rewrite Es in Hs. destruct (S1' s x i Hs) as ([b Hb] & Hi & E). rewrite (C_MR_hosted _ _ Hb). split; [exists b; apply C_hosts_old; exact Hb| auto].
      * rewrite Es in Hs. inversion Hs. subst x i. rewrite C_MR_m. fold last'. split; [exists p; apply C_hosts; left; auto|]. split; [lia|]. rewrite slot'. reflexivity.
    + intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * rewrite C_MR_m in Hi |- *. rewrite slot'. apply C_slots_new. fold last' in Hi. lia.
      * rewrite (C_MR_hosted _ _ Hx) in Hi |- *. rewrite C_slots_old; [exact (S2 b x i Hx Hi)|].
        apply (old_hosts_not_new_slot b x i Hx Hi) || (intros N; destruct N as (j & Hj & E); exact (old_slot_not_new _ _ _ (S2 b x i Hx Hi) (ex_intro _ j (conj Hj E)))).
    + intros b x aix i. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
      * intros E Hi. inversion E. subst x aix. rewrite C_MR_m in Hi |- *. cbn zeta. rewrite slot', C_groups. fold last' in Hi.
        pose proof (X_part i Hi) as P5.
        eapply one5_iff_create; [exact P5| |]; cbn.
        -- intros Hin. apply in_map_iff in Hin as (k & Ek & Hk). apply (blk_not_new k Hk). exists i. split; [clear -Hi; lia| exact Ek].
        -- destruct (aptr_eqb_spec (fst p, snd p + UNIT + stride' * i) p) as [Eip|NE]; [exfalso; apply p_not_new; exists i; split; [clear -Hi; lia| symmetry; exact Eip]|].
           rewrite (new_not_group i ltac:(clear -Hi; lia)). intros H; apply H; reflexivity.
      * intros Hb Hi. assert (Hx : hosts st b x) by (exists aix; exact Hb).
        rewrite (C_MR_hosted _ _ Hx) in Hi |- *. cbn zeta. rewrite C_groups.
        pose proof (S3 b x aix i Hb Hi) as P5. cbn zeta in P5.
        set (s := slot_start' (MR st x) i) in *.
        assert (NSs : ~ nslot s) by (apply (old_slot_not_new s x i); exact (S2 b x i Hx Hi)).
        destruct (aptr_eqb_spec s p) as [Esp|NEsp].
        -- (* [comment removed for export] *)
           destruct SITE as [(_ & B0 & _ & _ & HPX & _)|(_ & HPX & HPX' & _)].
           ++ exfalso. rewrite Esp in *. pose proof (S2 b x i Hx Hi) as Hs. fold s in Hs. rewrite Esp in Hs.
              destruct (S1' _ _ _ Hs) as ([bb Hbb] & _ & Eps). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hbb) in Eps.
              pose proof (sstart0 _ _ _ IM _ _ Hbb). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hbb ltac:(lia)).
              destruct (hosts_ok _ _ _ IG _ _ Hbb) as (a0 & _ & GO0). pose proof (g_align _ _ _ _ _ _ GO0) as [A00 _].
              apply (f_equal snd) in Eps. cbn in Eps. unfold UNIT in *. clear - B0 Eps H H0 A00. lia.
           ++ rewrite Esp in P5 |- *. rewrite HPX in P5. rewrite HPX'.
              revert P5. unfold one5. clear. intros P5.
              assert (NN : ~ (@None aptr = Some p)) by discriminate. assert (SS : Some (mkGhdr (Some m) ai) <> None) by discriminate.
              tauto.
        -- eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P5].
           split.
           ++ intros HPs. exfalso. destruct SITE as [(_ & _ & _ & _ & HPX & _)|(_ & HPX & _)]; rewrite HPX in HPs; [discriminate| inversion HPs; exact (NEsp (eq_sym H0))].
           ++ intros HPs. exfalso. destruct (X_pend' _ HPs) as (j & Hj & Ej). apply NSs. exists j. split; [fold last' in Hj; lia| exact Ej].
    + intros s Hs. destruct (X_pend' _ Hs) as (j & Hj & ->). rewrite C_slots_new; [discriminate| fold last' in Hj; lia].
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (x & i & Hs & REST). exists x, i.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hbx] & _). rewrite (C_MR_hosted _ _ Hbx).
      split; [rewrite C_slots_old; [exact Hs| exact (blk_not_new k Hk)]| exact REST].
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
    assert (REGp : exists r, s_regions st !! fst p = Some r /\ r_kind r = RKGroup).
    { destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & [a Hpm] & Hf & _)]; [exists r; auto|].
      destruct (ig_region _ _ _ IG _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto. }
    constructor.
    + intros rid sh. rewrite E_shadow, E_regions. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst p)) as [->|NE].
      * intros _. exact REGp.
      * rewrite lookup_insert_ne by congruence. exact (D1 rid sh).
    + intros rid sh Hsh. rewrite E_tick. rewrite E_shadow in Hsh. exact (TKS_hdr_havoc st p D2 rid sh Hsh).
    + intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * rewrite C_MR_m in Hi |- *. rewrite sstart'. apply C_known_out; [| apply SH_hdr0; unfold cnt_of in Hi; fold last' cnt in Hi; exact Hi].
        cbn. intros [_ H]. unfold IB, UNIT in H. destruct (Z.eq_dec i 0) as [->|NZ]; [lia|]. unfold cnt_of in Hi. assert (stride' * 1 <= stride' * i) by nia. lia.
      * rewrite (C_MR_hosted _ _ Hx) in Hi |- *. apply C_known_res; [cbn; rewrite (hdr0_res _ _ i Hx); lia| exact (D3 b x i Hx Hi)].
    + intros b x o Hx Ho. apply C_hosts in Hx as [[-> ->]|[NEb Hx]]; [apply C_unknown_hdr; exact Ho| apply C_unknown_any; exact (D4 b x o Hx Ho)].
    + intros b x px ix Hx Hml Hs. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * (* [comment removed for export] *)
        rewrite C_MR_m in Hml. rewrite (C_slots_old p p_not_new) in Hs.
        destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs0 & Hpm & Hf & Hip & Ep & _ & _ & _ & (v3 & K3 & E3 & R3) & K2 & K1 & Q)]; [exfalso; exact (Hml1 Hml)|].
        rewrite Hs0 in Hs. inversion Hs. subst px ix. rewrite (C_MR_hosted _ _ Hpm), (hosts_gbase _ _ _ IM _ _ Hpm). cbn zeta.
        split; [exists v3; split; [apply C_known_out; [cbn; lia| exact K3]| auto]|].
        split; [apply C_known_out; [cbn; lia| exact K2]|]. split; [apply C_known_out; [cbn; lia| exact K1]| exact Q].
      * rewrite (C_MR_hosted _ _ Hx) in Hml. rewrite (C_slots_old b (old_hosts_not_new _ _ Hx)) in Hs.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
        destruct (D5 b x px ix Hx Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
        destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx). pose proof (g_align _ _ _ _ _ _ GOx) as [A0 A16]. unfold UNIT in A16.
        assert (RS : forall d r, 0 <= r < 16 -> d = r - 16 -> 12 <= r -> 12 <= (snd b + d) mod 16).
        { intros d r Hr -> H12. pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as Db. rewrite A16 in Db.
          replace (snd b + (r - 16)) with (r + (snd b / 16 - 1) * 16) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. exact H12. }
        split; [exists v3; split; [apply C_known_res; [cbn; replace (snd b - 3) with (snd b + (13 - 16)) by lia; apply (RS _ 13); lia| exact K3]| auto]|].
        split; [apply C_known_res; [cbn; replace (snd b - 2) with (snd b + (14 - 16)) by lia; apply (RS _ 14); lia| exact K2]|].
        split; [apply C_known_res; [cbn; replace (snd b - 1) with (snd b + (15 - 16)) by lia; apply (RS _ 15); lia| exact K1]| exact Q].
    + intros k x i Hk Hs. rewrite (C_slots_old _ (blk_not_new k Hk)) in Hs.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es). rewrite (C_MR_hosted _ _ Hx).
      pose proof (D6 k x i Hk Hs) as B. cbn zeta in B |- *. destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      (* [comment removed for export] *)
      assert (OUT : forall o, snd (bslot k) - IB <= o < snd (bslot k) + get_stride (MR st x) - IB -> ~ (fst (bslot k) = fst p /\ snd p <= o < snd p + 12)).
      { intros o Ho [Hf Hin]. pose proof (blk_clear k x i Hk Hs Hf) as D. unfold IB in *. clear - Ho Hin D. lia. }
      destruct (is_blocks _ _ _ IS k Hk) as (x' & i' & Hs' & Hoff & Hn & Hfit). rewrite Hs in Hs'. inversion Hs'. subst x' i'.
      pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG _]. unfold IB, UNIT in *.
      assert (K : forall o v, snd (bslot k) - 4 <= o < snd (bslot k) + get_stride (MR st x) - 4 -> known st (fst (bslot k), o) v -> known st' (fst (bslot k), o) v).
      { intros o v Ho Ko. apply C_known_out; [apply (OUT o Ho)| exact Ko]. }
      split; [apply K; [lia| exact A1]|]. split; [apply K; [lia| exact A2]|]. split; [apply K; [lia| exact A3]|]. split; [apply K; [lia| exact A4]|].
      split; [exact A5|]. split.
      * intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). split; [apply K; [lia| exact B1]|]. split; [apply K; [lia| exact B2]|]. split; [apply K; [lia| exact B3]|].
        split; [apply K; [lia| exact B4]|]. split; [apply K; [lia| exact B5]| exact B6].
      * split; [intros Hr; apply K; [lia| apply A7; exact Hr]|]. intros a Ha. apply C_unknown_any. apply A8. exact Ha.
Qed.

End CREATE.
