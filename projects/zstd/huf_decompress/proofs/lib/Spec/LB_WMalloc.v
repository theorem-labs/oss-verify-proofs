(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (35 recorded proofs replaced by written proofs (MIS_le_LS, SG_add_block, AQ_add_block and 32 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep KLink KEv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2 MI_WSlot MI_WSlot2 MI_WSlot3 MI_WMalloc MI_Bits
  LB_Tables LB_Inv LB_Sum LB_Kernel LB_KCount LB_Embed LB_Bound LB_Count LB_WNtf LB_XferF LB_Tree LB_QM LB_WAMeta LB_WTry LB_Cnt LB_AG LB_StmtA LB_WFree LB_WSlot.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_WMalloc () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C47Corelib7Classes?RelationClasses9ReflexiveI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec6LB_Inv4zlenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6LB_Sum=zsum_map_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum<zsum_map_extC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationGPermutation_EquivalenceC35stdpp8fin_maps:map_insertI35stdpp8fin_maps6FinMap00C47Corelib4Init9Datatypes3fstC46Stdlib7Sorting;Permutation>Permutation_inC35stdpp4base;RelDecisionC35stdpp8fin_maps;map_to_listC59OSSVerify5KrLib4Spec6LB_Sum9mtl_nodupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_eq_iffC35stdpp4base6ElemOfC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6InsertI35stdpp4base<list_elem_of00C35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv6zcountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum;zcount_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum:zcount_extC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C46Stdlib5Lists4List6nth_okC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7slotclsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib5Lists4List6filterC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes6option00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6LB_Inv3MISC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv2LSC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec5LB_QM2SG00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables2S_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6LB_Inv4stdgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables:std_nestedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC35stdpp4base6lookupC59OSSVerify5KrLib4Spec9LB_Tables7bighostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7std_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3nscC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6LB_Inv3clsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega7EnvRing5PExpr04K59OSSVerify5KrLib4Spec5LB_QM2SG01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableK46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec7LB_Tree6fqtreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree:fqtree_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree:fqtree_visC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv2AQ00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_StmtA4ROOMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv2LRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3n63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3CAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7ncarvedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4NCAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4PQOKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv5isbigC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00K59OSSVerify5KrLib4Spec6LB_Inv2AQ01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum9zsum_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3R63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_StmtA4bigbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6leb_leC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC59OSSVerify5KrLib4Spec5KStep>round_up_pg_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt@size_to_class_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z4evenC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltI59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv8ia_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt=size_class_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec6MI_Cnt9lor1_evenC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z8ltb_specC59OSSVerify5KrLib4Spec6Malloc5clz32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<nth_overflowK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib4Spec6Malloc<size_classesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate23F63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec;MI_WCreate25c63_FC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate27c63_MRgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@s_metas_upd_metaC1?~~~~~~~~~~~~~~~C35stdpp4base6insertK59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2;c63_nogroupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc9q63_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4iterC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc9set_slotsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init5Logic4True00c59OSSVerify5KrLib4Spec:LB_WMalloc8q63_rec5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc6q63_MRC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7ir_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc?q63_nogroup_ridC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc:q63_noslotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc9q63_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc7q63_oldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc=q63_slots_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapC47Corelib7Classes?RelationClassesFEquivalence_TransitiveC59OSSVerify5KrLib4Spec6LB_Sum:mtl_insertC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_flat_mapC46Stdlib7Sorting;Permutation@Permutation_reflC47Corelib7Classes?RelationClasses<transitivityC59OSSVerify5KrLib4Spec6LB_Inv6gmetasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc:q63_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound9gmetas_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc:q63_gmetasC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc@q63_gmetas_hostsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc7q63_sumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound;gcnt_gmetasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc7q63_MRgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables4cmaxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate26c63_mlC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib4Spec;MI_WCreate2:c63_strideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc<q63_stdg_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7im_idleC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6LB_Sum:mtl_deleteC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_lengthC59OSSVerify5KrLib4Spec6LB_Sum>mtl_insert_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9is_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc?q63_slotcls_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_WAMeta9exit_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot=alloc_slot_fqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5LB_QM2QM00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot3BLFC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib4Spec:LB_WMallocBsize_to_class_ne62C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc7q63_MISC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc7q63_nscC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM:apages_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv6apagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5LB_QM2QM01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc8q63_gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc;q63_ncarvedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2x0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc:q63_stdg_gC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv4SINV00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_totalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM:SINV_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc9MIS_le_LSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Cnt:LS_le_gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot7BLF_MISC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc<SG_add_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WFree6SINV_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc<AQ_add_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_StmtA:CORE_POSTQC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc;small_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3PHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc:bigb_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib4Spec8LB_WSlot:SINV_QPOSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot5QPOSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~K35stdpp4base5NoDup01C59OSSVerify5KrLib4Spec5LB_AG:rank_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_AG4rankC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WSlot29SLOT_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot4X_asC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot:QPOST_SINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc:small_leafC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry28hd_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Bits<lowbit_idiomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry27hd_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WTry9ta_fin_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9g_presentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf4geomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf<FFR_upd_metaC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec7LB_WNtf3FFR00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WFree:SINV_SINVxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WFree:SINVx_xferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9hosts_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot7BLF_ffrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02c59OSSVerify5KrLib4Spec:LB_WMalloc8bigb_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt@round_up_pg_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc<mmap_len_rupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv5aq_pqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4NCNTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Count<ledger_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib4Spec8LB_Embed2QBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9brk_quietC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree2<brk_quiet_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot=state_bytes_BC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel2gmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel2BBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel=BB_set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel<gm_add_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_brkphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7lrangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_LedgerAmmap_answer_ok_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec9MI_LedgerEINVL_new_group_regionC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib4Spec9MI_Ledger9ng_lookupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta8nm_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WSlot2Dshadow_next_rid_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WSlot2?step_seq_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF28TF0_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3=INVL_step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlotFQPOST_new_group_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot>qsame_step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot;QPOST_qsameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv;group_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM3gbFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib4Spec5LB_QMImsum_regions_insert_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM@group_bytes_msumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM?group_bytes_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM4QM_XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_CntAncarved_le_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7ngroupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Cnt:ngroups_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv2NGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WSlot=group_bytes_BC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9MI_WAMeta8AM_frame00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9MI_WAMeta7L_frame00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta;amf_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ir_groupsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List9filter_InC59OSSVerify5KrLib4Spec6LB_Sum6mtl_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8ir_shapeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta9lf_groupsC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesCPreOrder_TransitiveC59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_TreeHlbytes_event_post_munmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound<ledger_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv:meta_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv9brk_pagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound=regions_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound4ORPHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WFree>SINV_drop_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree7rejectsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres35xidleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta:amf_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta8amf_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2;create63_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3AINVL_mmap_counterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc9c63_quantC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5LB_QM8SG_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv9aq_carvedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_WAMeta8AQ_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta8amf_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta7lf_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_WAMeta=alloc_meta_fqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xorphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum4msumC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv4MAPFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_KCount4RMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_KCount4NMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv5MAPFXC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbC56Stdlib6ZArith6BinInt1Z;le_preorderc59OSSVerify5KrLib4Spec:LB_WMalloc=malloc_big_fqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc?malloc_small_fqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_WMalloc>malloc_core_fqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_StmtA4NREQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_StmtACmalloc_core_fq_stmtC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma MIS_le_LS st BL c : MIS st BL c <= LS st BL c.
Proof.
  unfold MIS, LS. induction BL as [|k l IH]; [unfold zcount, zlen; cbn; lia|].
  rewrite !zcount_cons. destruct (slotcls st (bslot k)) as [c'|]; [| lia]. destruct (c' =? c); cbn [andb]; [destruct (size_to_class (bsize k) =? c - 1); lia| lia].
Qed.

Lemma SG_add_block st BL c off n m i :
  SG st BL -> s_slots st !! c = Some (m, i) -> m_sizeclass (MR st m) < 48 -> 0 <= n < MMAP_THRESHOLD ->
  (size_to_class n = m_sizeclass (MR st m) \/ (size_to_class n = m_sizeclass (MR st m) - 1 /\ MIS st BL (m_sizeclass (MR st m)) <= 12)) ->
  SG st (((c, off), n) :: BL).
Proof.
  intros S Hs Hsc Hn CLS. destruct S as [S1 S2 S3 S4 S5 S6 S7]. constructor; auto.
  - intros k [<-|Hk]; [| exact (S1 k Hk)]. exists m, i. cbn [bslot bsize fst snd]. split; [exact Hs|].
    split; [intros _; split; [lia| destruct CLS as [E|[E _]]; [left; exact E| right; exact E]]| intros E63; exfalso; lia].
  - intros c'. unfold MIS. rewrite zcount_cons. fold (MIS st BL c'). cbn [bslot bsize fst snd]. unfold slotcls at 1. rewrite Hs. unfold cls.
    destruct (Z.eqb_spec (m_sizeclass (MR st m)) c') as [<-|NE]; cbn [andb]; [| pose proof (S2 c'); lia].
    destruct (Z.eqb_spec (size_to_class n) (m_sizeclass (MR st m) - 1)) as [E|NE]; [| pose proof (S2 (m_sizeclass (MR st m))); lia].
    destruct CLS as [E'|[_ M]]; [exfalso; lia| lia].
  - intros b x ai Hb H63. right. exact (S6 b x ai Hb H63).
Qed.

Lemma AQ_add_block st BL P c off n :
  AQ st BL P -> 0 <= n -> ROOM BL P n -> AQ st (((c, off), n) :: BL) P.
Proof.
  intros A Hn [R1 R2]. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  - intros c' Hc'. unfold LR. rewrite zcount_cons. fold (LR BL c'). cbn [bsize snd]. unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; cbn [negb andb]; [exact (A1 c' Hc')|].
    destruct (Z.eqb_spec (size_to_class n) c') as [<-|NE]; [specialize (R1 LT); lia| exact (A1 c' Hc')].
  - unfold n63. rewrite zcount_cons. fold (n63 BL). unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; [specialize (R2 GE); lia| exact A3].
Qed.

Lemma R63_cons c off n BL : R63 (((c, off), n) :: BL) = bigb n + R63 BL.
Proof. unfold R63, bigb, isbig. cbn [map bsize snd]. rewrite zsum_cons. reflexivity. Qed.

Lemma bigb_small n : n < MMAP_THRESHOLD -> bigb n = 0.
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

Lemma bigb_big n : MMAP_THRESHOLD <= n -> bigb n = round_up_pg (n + IB + UNIT).
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

Lemma mmap_len_rup l : mmap_len l = round_up_pg l.
Proof. unfold mmap_len. symmetry. apply round_up_pg_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma small_class X st L BL LS n : INVL X st L BL LS -> 0 <= n < MMAP_THRESHOLD ->
  let sc0 := size_to_class n in
  let sc := match active st sc0 with
            | Some _ => sc0
            | None =>
              if (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0) then
                let usage1 := usage st (Z.lor sc0 1) in
                let usage1 := match active st (Z.lor sc0 1) with
                              | None => usage1 + 3
                              | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc0 1))) in
                                          if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                              end in
                if usage1 <=? 12 then Z.lor sc0 1 else sc0
              else sc0
            end in
  0 <= sc < 48 /\ n + IB <= UNIT * size_class sc /\ (size_to_class n = sc \/ (size_to_class n = sc - 1 /\ gcnt st sc <= 12)).
Proof.
  intros INV Hn. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT]. cbn zeta.
  set (sc0 := size_to_class n) in *.
  destruct (active st sc0); [auto|].
  destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (lor1_even sc0 ltac:(lia) EV).
  assert (U : usage st (sc0 + 1) = gcnt st (sc0 + 1)) by exact (ia_usage _ (proj1 (proj2 INV)) (sc0 + 1) ltac:(lia)).
  match goal with |- context [if ?c then sc0 + 1 else sc0] => destruct c eqn:LE end; [| auto].
  apply Z.leb_le in LE.
  pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [lia|]. split; [unfold UNIT in *; lia|]. right. split; [lia|].
  rewrite <- U. destruct (active st (sc0 + 1)); [| lia]. destruct (_ && _); lia.
Qed.

Lemma size_to_class_ne62 m : size_to_class m <> 62.
Proof.
  unfold size_to_class.
  set (n' := Z.shiftr (m + IB - 1) 4). destruct (Z.ltb_spec n' 10) as [LT|GE]; [lia|].
  set (i := (28 - clz32 (n' + 1)) * 4 + 8).
  assert (S61 : forall k, 48 <= k -> size_class k = 0).
  { intros k Hk. unfold size_class. rewrite nth_overflow; [reflexivity|]. cbn. lia. }
  destruct (size_class (i + 1) <? n' + 1) eqn:E1.
  - destruct (size_class (i + 2) <? n' + 1) eqn:E2; [lia|]. intros E. replace (i + 2) with 62 in E2 by lia.
    rewrite (S61 62 ltac:(lia)) in E2. apply Z.ltb_ge in E2. lia.
  - destruct (size_class i <? n' + 1) eqn:E2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section C63Q.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Variables (g : aptr) (rid : N) (r : region) (needed n off : Z).
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
Hypothesis En : needed = n + IB + UNIT.
Hypothesis Hbig : MMAP_THRESHOLD <= n.
Hypothesis SG3 : SG st3 BL.
Hypothesis Q3 : QM X st3 0.
Hypothesis A3 : AQ st3 BL P.
Hypothesis R63room : n63 BL + 1 <= P 63.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.
Let k0 : blk := (((rid, 16), off), n).

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma q63_metas : s_metas st6 = <[g := mr']> (s_metas st3).
Proof.
  change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g).
  rewrite (c63_MRg st3 L BL LS g rid INV). unfold ml, mr', p. rewrite (c63_F rid needed Hn). reflexivity.
Qed.

Lemma q63_groups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
  change (s_groups st6) with (s_groups st5). unfold st5, put_group. cbn [s_groups Malloc.set_groups].
  unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite (c63_nogroup st3 L BL LS g rid INV). reflexivity.
Qed.

Lemma q63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. change (s_metas st5) with (s_metas st6). rewrite q63_metas, lookup_insert_eq. reflexivity. Qed.

Lemma q63_slots : s_slots st6 = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
  unfold st6, add_slots. rewrite q63_rec5. cbn [Z.iter Pos.iter snd s_slots set_slots].
  replace (aadd p (UNIT + get_stride mr' * 0)) with (rid, 16); [reflexivity|].
  unfold aadd, p. cbn [fst snd]. f_equal. unfold UNIT. lia.
Qed.

Lemma q63_MR x : x <> g -> MR st6 x = MR st3 x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite q63_metas, lookup_insert_ne by congruence. reflexivity. Qed.

Lemma q63_MRg : MR st6 g = mr'.
Proof. unfold MR, get_meta_rec. rewrite q63_metas, lookup_insert_eq. reflexivity. Qed.

Lemma q63_old x : (exists b, hosts st3 b x) -> x <> g /\ MR st6 x = MR st3 x.
Proof.
  intros [b Hb]. assert (NE : x <> g).
  { intros ->. pose proof (hosts_mem _ _ _ IM _ _ Hb) as MM. rewrite (c63_MRg st3 L BL LS g rid INV) in MM. cbn in MM. discriminate. }
  split; [exact NE| exact (q63_MR x NE)].
Qed.

Lemma q63_nogroup_rid b : fst b = rid -> s_groups st3 !! b = None.
Proof. intros Hb. destruct (ir_orph _ _ _ (proj1 INV) rid eq_refl) as (r0 & _ & _ & NG). exact (NG b Hb). Qed.

Lemma q63_noslot : s_slots st3 !! (rid, 16) = None.
Proof.
  destruct (s_slots st3 !! (rid, 16)) as [[x i]|] eqn:E; [| reflexivity]. exfalso.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM x b i Hb) in Es. assert (Eb : fst b = rid) by (inversion Es; reflexivity).
  destruct Hb as [ai Hb]. rewrite (q63_nogroup_rid b Eb) in Hb. discriminate.
Qed.

Lemma q63_slots_old s v : s_slots st3 !! s = Some v -> s_slots st6 !! s = Some v.
Proof. intros Hs. rewrite q63_slots, lookup_insert_ne; [exact Hs|]. intros <-. rewrite q63_noslot in Hs. discriminate. Qed.

Lemma q63_slotcls_old s : s_slots st3 !! s <> None -> slotcls st6 s = slotcls st3 s.
Proof.
  intros Hs. destruct (s_slots st3 !! s) as [[x i]|] eqn:E; [| congruence]. unfold slotcls. rewrite (q63_slots_old _ _ E), E.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & _). destruct (q63_old x (ex_intro _ b Hb)) as [_ MRx]. unfold cls. rewrite MRx. reflexivity.
Qed.

Lemma q63_gmetas : Permutation (gmetas st6) ((g, p) :: gmetas st3).
Proof.
  unfold gmetas, groups_l. rewrite q63_groups.
  etransitivity; [apply Permutation_flat_map; apply mtl_insert; exact (q63_nogroup_rid p eq_refl)|]. cbn. apply Permutation_refl.
Qed.

Lemma q63_gmetas_hosts x b : In (x, b) (gmetas st3) -> exists b', hosts st3 b' x.
Proof. intros H. apply gmetas_in in H as [aix Hb]. exists b, aix. exact Hb. Qed.

Lemma q63_sum (F F' : aptr * aptr -> Z) :
  (forall x b, In (x, b) (gmetas st3) -> F' (x, b) = F (x, b)) ->
  zsum (map F' (gmetas st6)) = F' (g, p) + zsum (map F (gmetas st3)).
Proof.
  intros HF. rewrite (zsum_map_perm _ _ _ q63_gmetas). cbn [map]. rewrite zsum_cons. f_equal. apply zsum_map_ext. intros [x b] Hin. apply HF. exact Hin.
Qed.

Lemma q63_gcnt c : c <> 63 -> gcnt st6 c = gcnt st3 c.
Proof.
  intros NE. rewrite !gcnt_gmetas. rewrite (q63_sum (fun mb => if m_sizeclass (MR st3 (fst mb)) =? c then cnt_of (MR st3 (fst mb)) else 0)).
  - cbn [fst]. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass]. replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - intros x b Hin. cbn [fst]. destruct (q63_old x (q63_gmetas_hosts x b Hin)) as [_ E]. rewrite E. reflexivity.
Qed.

Lemma q63_stdg_g : stdg st6 g = false.
Proof.
  unfold stdg, cls. rewrite q63_MRg. cbn [m_sizeclass]. unfold mr', ml, p. rewrite (c63_stride rid needed Hn).
  pose proof (c63_ml needed Hn) as [M _]. replace (_ =? S_ 63) with false; [apply andb_false_r|].
  symmetry. apply Z.eqb_neq. unfold S_. change (size_class 63) with 0. unfold UNIT. lia.
Qed.

Lemma q63_stdg_old x : (exists b, hosts st3 b x) -> stdg st6 x = stdg st3 x.
Proof. intros Hx. destruct (q63_old x Hx) as [_ E]. unfold stdg, cls. rewrite E. reflexivity. Qed.

Lemma q63_nsc c : 0 <= c < 48 -> nsc st6 c = nsc st3 c.
Proof.
  intros Hc. unfold nsc. rewrite (q63_sum (fun mb => if (cls st3 (fst mb) =? c) && negb (stdg st3 (fst mb)) then cnt_of (MR st3 (fst mb)) else 0)).
  - cbn [fst]. unfold cls at 1. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass]. replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). cbn. reflexivity.
  - intros x b Hin. cbn [fst]. pose proof (q63_gmetas_hosts x b Hin) as Hx. rewrite (q63_stdg_old x Hx). destruct (q63_old x Hx) as [_ E]. unfold cls. rewrite E. reflexivity.
Qed.

Lemma q63_ncarved : ncarved st6 = ncarved st3.
Proof.
  unfold ncarved. rewrite q63_metas.
  pose proof (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))) as Hg.
  change (zlen (map_to_list (<[g:=mr']> (s_metas st3))) = zlen (map_to_list (s_metas st3))).
  unfold zlen. rewrite (Permutation_length (mtl_insert_old (s_metas st3) g mr' _ Hg)), (Permutation_length (mtl_delete (s_metas st3) g _ Hg)). reflexivity.
Qed.

Lemma q63_MIS c : MIS st6 BL c = MIS st3 BL c.
Proof.
  unfold MIS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (q63_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.

Theorem c63_quant : SG st6 (k0 :: BL) /\ QM x0 st6 0 /\ AQ st6 (k0 :: BL) P /\ BLF st3 st6 BL.
Proof.
  pose proof (c63_ml needed Hn) as [M RU].
  assert (GRP' : forall b x aix, s_groups st6 !! b = Some (mkGhdr (Some x) aix) -> (x = g /\ b = p) \/ (x <> g /\ s_groups st3 !! b = Some (mkGhdr (Some x) aix) /\ MR st6 x = MR st3 x)).
  { intros b x aix Hb. rewrite q63_groups in Hb. destruct (aptr_eq_dec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. inversion Hb. left. auto.
    - rewrite lookup_insert_ne in Hb by congruence. right. destruct (q63_old x (ex_intro _ b (ex_intro _ aix Hb))) as [NEx MRx]. auto. }
  assert (BF : BLF st3 st6 BL).
  { intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). apply q63_slotcls_old. rewrite Hs. discriminate. }
  split; [| split; [| split; [| exact BF]]].
  - (* [comment removed for export] *) destruct SG3 as [S1 S2 S3 S4 S5 S6 S7]. constructor.
    + intros k [<-|Hk].
      * exists g, 0. unfold k0. cbn [bslot bsize fst snd]. rewrite q63_slots, lookup_insert_eq, q63_MRg. unfold mr'. cbn [m_sizeclass m_maplen].
        split; [reflexivity|]. split; [intros; exfalso; lia|]. intros _. split; [exact Hbig|]. unfold ml in *. rewrite RU, En. reflexivity.
      * destruct (S1 k Hk) as (x & i & Hs & C1 & C2). exists x, i. split; [exact (q63_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _). destruct (q63_old x (ex_intro _ b Hb)) as [_ MRx]. rewrite MRx. auto.
    + intros c. unfold MIS. rewrite zcount_cons. fold (MIS st6 BL c). rewrite q63_MIS. unfold k0. cbn [bslot bsize fst snd].
      unfold slotcls. rewrite q63_slots, lookup_insert_eq. unfold cls. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass].
      pose proof (S2 c). pose proof (size_to_class_ne62 n).
      destruct (Z.eqb_spec 63 c) as [<-|NE]; cbn [andb]; [| lia]. replace (size_to_class n =? 63 - 1) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    + intros b x aix Hb Hc Hml. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Hc; unfold mr' in Hc; cbn in Hc; lia|].
      rewrite MRx in *. exact (S3 _ _ _ Hb0 Hc Hml).
    + intros b x aix Hb SD. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_stdg_g in SD; discriminate|].
      rewrite (q63_stdg_old x (ex_intro _ b (ex_intro _ aix Hb0))) in SD. rewrite MRx. destruct (S4 _ _ _ Hb0 SD) as (Q1 & Q2 & Q3').
      split; [exact Q1|]. split; [| exact Q3']. intros Z0. destruct (Q2 Z0) as (g0 & i0 & Hs & Eg). exists g0, i0. split; [exact (q63_slots_old _ _ Hs)|].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (q63_old g0 (ex_intro _ bg Hbg)) as [_ MRg0]. rewrite MRg0. exact Eg.
    + intros c Hc. rewrite (q63_nsc c Hc). exact (S5 c Hc).
    + intros b x aix Hb H63. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * left. rewrite q63_MRg. unfold k0, slot_start', mr'. cbn -[Z.add Z.mul]. unfold p. cbn [fst snd]. f_equal. rewrite (c63_stride rid needed Hn) || idtac. unfold UNIT. lia.
      * right. rewrite MRx in *. exact (S6 _ _ _ Hb0 H63).
    + intros b x aix g0 i Hb Z0 Hs'. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Z0; unfold mr' in Z0; cbn in Z0; unfold ml in Z0; lia|].
      rewrite MRx in Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb0) Z0) as (g1 & i1 & Hs & _).
      rewrite (q63_slots_old _ _ Hs) in Hs'. assert (g1 = g0 /\ i1 = i) as [-> ->] by (split; congruence).
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (q63_old g0 (ex_intro _ bg Hbg)) as [_ MRg0]. rewrite MRg0. exact (S7 _ _ _ _ _ Hb0 Z0 Hs).
  - (* [comment removed for export] *)
    assert (RG' : s_regions st6 = s_regions st3) by reflexivity.
    assert (CX' : s_ctx st6 = s_ctx st3) by reflexivity.
    assert (AP' : apages st6 = apages st3) by (apply apages_ext; [exact RG'| rewrite CX'; reflexivity]).
    destruct Q3 as [Q1 Q2 Q3' Q4 Q5 Q6]. constructor; rewrite ?RG', ?q63_ncarved, ?AP', ?CX'; auto.
    intros x mr Hx Z0. rewrite q63_metas in Hx. destruct (aptr_eq_dec x g) as [->|NE].
    + rewrite lookup_insert_eq in Hx. inversion Hx. subst mr. cbn in Z0. discriminate.
    + rewrite lookup_insert_ne in Hx by congruence. destruct (Q1 x mr Hx Z0) as [N0|I0]; [left; exact N0|]. cbn in I0. destruct I0 as [I0|[]]. congruence.
  - (* [comment removed for export] *) destruct A3 as [A1 A2 A3' A4 A5]. constructor; auto.
    + intros c Hc. unfold LR. rewrite zcount_cons. fold (LR BL c). unfold isbig, k0. cbn [bsize snd]. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig). cbn. exact (A1 c Hc).
    + intros c Hc. rewrite (q63_gcnt c ltac:(lia)). exact (A2 c Hc).
    + unfold n63. rewrite zcount_cons. fold (n63 BL). unfold isbig, k0. cbn [bsize snd]. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig). lia.
    + rewrite q63_ncarved. exact A4.
Qed.
End C63Q.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section COREQ.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z) (n B : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis SI : SINV x0 st BL.
Hypothesis HAQ : AQ st BL P.
Hypothesis Hn : 0 <= n.
Hypothesis HR : ROOM BL P n.
Hypothesis HB : PHI P + R63 BL + bigb n <= B + 3 * PGSZ.
Hypothesis HNR : n <= NREQ.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma small_leaf st1 L1 LS1 g bg idx sc X1 :
  INVL X1 st1 L1 BL LS1 -> x_idle X1 = [] -> hosts st1 bg g -> 0 <= idx <= m_last_idx (MR st1 g) ->
  m_sizeclass (MR st1 g) = sc -> 0 <= sc < 48 ->
  (size_to_class n = sc \/ (size_to_class n = sc - 1 /\ gcnt st sc <= 12)) ->
  SINV X1 st1 BL -> AQ st1 BL P -> BLF st st1 BL -> n < MMAP_THRESHOLD ->
  CORE_POSTQ n BL P L1 (st1, Some (g, idx)).
Proof.
  intros INV1 HX Hh Hidx SCg Hsc CLS SI1 A1 BF Hlt. unfold CORE_POSTQ. cbn [fst snd]. intros bg' off Hh'.
  pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ _ Hh' Hh) as ->.
  pose proof (is_total _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1)))))) bg g idx Hh Hidx) as T.
  rewrite (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) g bg idx Hh) in T.
  split.
  - apply (SINV_X X1 x0); [rewrite HX; reflexivity|]. apply SINV_split in SI1 as [G1 Q1]. apply SINV_split. split; [| exact Q1].
    apply (SG_add_block st1 BL _ off n g idx G1 T ltac:(lia) ltac:(lia)). rewrite SCg.
    destruct CLS as [E|[E G12]]; [left; exact E| right]. split; [exact E|].
    rewrite (BLF_MIS st st1 BL sc BF). pose proof (MIS_le_LS st BL sc). pose proof (LS_le_gcnt x0 st L BL LS INV sc). lia.
  - exact (AQ_add_block st1 BL P _ off n A1 Hn HR).
Qed.


Lemma malloc_small_fq : n < MMAP_THRESHOLD ->
  fqtree B L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POSTQ n BL P).
Proof.
  intros Hlt. pose proof (small_class x0 st L BL LS n INV ltac:(lia)) as SCF. cbn zeta in SCF.
  pose proof HB as HB0. rewrite (bigb_small n Hlt), Z.add_0_r in HB0.
  pose proof (SINV_QPOST P [] BL st x0 eq_refl SI HAQ) as QP.
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end) in *.
  clearbody sc. destruct SCF as (SC' & FIT' & CLS).
  assert (SLOT : fqtree B L (alloc_slot full_lay FUEL st sc n (fun st1 idx =>
             if idx <? 0 then ret (st1, None)
             else match active st1 sc with
                  | Some gp => ret (st1, Some (gp, idx))
                  | None => SVis (EUndef UBadPtr) (fun _ => ret (st, @None (aptr * Z)))
                  end) (ret (st, None))) (CORE_POSTQ n BL P)).
  { apply (alloc_slot_fq (mstate * option (aptr * Z)) P B (CORE_POSTQ n BL P) FUEL sc [] st L BL LS n); try assumption.
    - unfold FUEL. cbn. lia.
    - apply NoDup_nil_2.
    - pose proof (rank_range sc). unfold zlen. cbn. lia.
    - intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES) QP1 GC1 BF1.
      destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
      + change (-1 <? 0) with true. cbn iota. apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd].
        exact (QPOST_SINV P [] BL st1 x0 eq_refl QP1).
      + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. apply fqtree_ret.
        destruct (QPOST_SINV P [] BL st1 (xpend (X_as []) (Some (fst bg, sstart (MR st1 g) idx))) eq_refl QP1) as [SI1 A1].
        apply (small_leaf st1 L1 LS1 g bg idx sc _ INV1 eq_refl (ex_intro _ ai Hg) Hidx SCg SC' CLS SI1 A1 BF1 Hlt). }
  destruct (active st sc) as [gp|] eqn:HA; [| exact SLOT].
  destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
  { rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb]. exact SLOT. }
  (* [comment removed for export] *)
  destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
  pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
  destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
  assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
  rewrite LNZ. cbn [negb]. apply fqtree_ret.
  pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
  set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
  assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
  { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; split; reflexivity. }
  destruct MRg as [ML MSC].
  assert (F01 : FFR st st1).
  { unfold st1. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ GO)| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr]. }
  destruct (SINVx_xfer x0 (xpend x0 (Some (fst bm, sstart (MR st gp) (ctz32 (lowbit (m_avail (MR st gp))))))) st st1 L L BL LS LS P None INV INV1 eq_refl F01 HAQ (SINV_SINVx _ _ _ SI) ltac:(intros; discriminate)) as (SI1 & A1 & _).
  apply (small_leaf st1 L LS gp bm _ sc _ INV1 eq_refl); try assumption.
  - apply (proj2 (hosts_ext st st1 eq_refl bm gp)). exists ai. exact Hbm.
  - rewrite ML. exact Hidx.
  - rewrite MSC. exact Esc.
  - exact (BLF_ffr _ st st1 L BL LS INV1 F01).
Qed.

(* [comment removed for export] *)
Lemma malloc_big_fq : MMAP_THRESHOLD <= n -> size_overflows n = false ->
  fqtree B L
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
    (CORE_POSTQ n BL P).
Proof.
  intros Hbig Hov. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  pose proof HB as HB0. rewrite (bigb_big n Hbig) in HB0. fold needed in HB0.
  pose proof (round_up_pg_spec needed) as [[RU1 RU2] _].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (SINV_QPOST P [] BL st x0 eq_refl SI HAQ) as QP. destruct QP as (SGst & Qst & Ast).
  (* [comment removed for export] *)
  assert (HQB : QB L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) B).
  { intros _. split.
    - rewrite mmap_len_rup. unfold RMAX. unfold NREQ in HNR. unfold needed, IB, UNIT in RU2 |- *. lia.
    - pose proof (aq_pq _ _ _ HAQ) as [PQ1 PQ2].
      pose proof (ledger_count x0 st L BL LS P INV SI HAQ eq_refl ltac:(lia)) as LC.
      unfold NMAX. unfold zlen in LC. lia. }
  apply fqtree_vis; [reflexivity| reflexivity| | exact HQB| | |].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
    unfold LEN_MAX. clear -HN. lia.
  - (* [comment removed for export] *)
    intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    pose proof (state_bytes_B x0 st L BL LS P (B - round_up_pg needed) INV eq_refl eq_refl SI HAQ ltac:(lia)) as SB.
    destruct (is_err a); [lia|]. rewrite gm_add_group, BB_set_groups, mmap_len_rup. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. split; [exact SI| exact HAQ].
    + destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
      rewrite <- Est1, <- Erid in INV1.
      set (L1 := KInv.set_groups ((a, needed) :: ld_groups L) L) in *.
      assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
      assert (FR : s_regions st !! rid = None) by (rewrite Erid; exact (nm_fresh _ _ _ _ _ INV)).
      assert (NS1 : s_shadow st1 !! rid = None).
      { rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
      assert (TF1 : TF0 (step_seq st1)).
      { destruct (step_seq_fields st1) as (A' & B' & _). apply (TF0_ctrl st1); [exact A'| exact B'|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
      pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
      destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
      (* [comment removed for export] *)
      pose proof (QPOST_new_group_region P [] BL st x0 L LS a needed INV (conj SGst (conj Qst Ast))) as QP1. rewrite <- Est1 in QP1.
      pose proof (QPOST_qsame P [] BL st1 (step_seq st1) _ L1 LS INV1 (qsame_step_seq st1) QP1) as (SG2 & Q2 & A2).
      set (st2 := step_seq st1) in *.
      assert (GB2 : group_bytes st2 = group_bytes st + round_up_pg needed).
      { rewrite (group_bytes_ext st1 st2 SS4). rewrite !group_bytes_msum, Est1. unfold new_region. cbn [fst s_regions set_next_rid set_regions].
        rewrite <- Erid. rewrite (msum_regions_insert_fresh gbF st rid _ FR). unfold gbF at 1. cbn. lia. }
      pose proof (proj2 (SINV_split (xorph x0 (Some rid)) st2 BL) (conj SG2 (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2))) as SI2.
      pose proof (ledger_count (xorph x0 (Some rid)) st2 L1 BL LS P INV2 SI2 A2 eq_refl ltac:(pose proof (aq_pq _ _ _ A2) as [PQ1 _]; lia)) as LC2.
      pose proof (aq_pq _ _ _ A2) as [_ PQ2'].
      eapply (alloc_meta_fq (mstate * option (aptr * Z)) BL P B (CORE_POSTQ n BL P) _ _ (xorph x0 (Some rid)) st2 L1 LS INV2 SG2 A2);
        [ | | lia| | | exact INV2| apply amf_refl| apply lf_refl| | reflexivity| reflexivity].
      * (* [comment removed for export] *)
        intros HFH. pose proof (ncarved_le_groups (xorph x0 (Some rid)) st2 L1 BL LS INV2 0 (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2) HFH eq_refl) as NC.
        pose proof (ngroups_le (xorph x0 (Some rid)) st2 L1 BL LS P INV2 SG2 A2) as NG0. cbn [x_idle xorph x0] in NC. unfold zlen in NC. cbn [length] in NC. change (Z.of_nat 0) with 0 in NC. unfold NCAP. lia.
      * (* [comment removed for export] *)
        rewrite GB2. pose proof (group_bytes_B x0 st L BL LS P (B - round_up_pg needed) INV eq_refl eq_refl SI HAQ ltac:(lia)). lia.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 INV3 AF LF SI3 A3' GC3 GEO3. cbn beta iota.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        pose proof (proj1 INV3) as IR3.
        assert (GPOS : forall g, In g (ld_groups L3) -> 0 <= snd g).
        { intros g Hg. apply (Permutation_in _ (ir_groups _ _ _ IR3)) in Hg. apply in_map_iff in Hg as ([q rq] & <- & Hin). cbn.
          apply filter_In in Hin as [Hin _]. apply mtl_in in Hin. pose proof (ir_shape _ _ _ IR3 _ _ Hin) as (_ & _ & L0 & _). lia. }
        apply fqtree_vis; [reflexivity| reflexivity| | exact I| | |].
        -- cbn. split; [exact (brk_quiet_of _ _ _ IR3)|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
        -- intros z Hz. etransitivity; [apply lbytes_event_post_munmap; exact GPOS|].
           pose proof (ledger_bound _ st3 L3 BL LS3 INV3) as LB3. pose proof (regions_bound _ st3 L3 BL LS3 P INV3 SI3 A3' eq_refl) as RB3.
           unfold ORPH in RB3. cbn [x_orph xorph x0] in RB3. rewrite Hr3 in RB3. cbn [r_len] in RB3. lia.
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd].
           destruct (SINV_drop_orph _ st3 L3 BL LS3 P rid _ INV3 Hr3 eq_refl SI3 A3') as [S'' A'']. split; [exact (SINV_X (xorph x0 (Some rid)) x0 _ _ eq_refl S'')| exact A''].
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 g INV3 NIg AF LF SI3 A3' NC3 GC3 GEO3. cbn beta iota zeta.
        change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl st2); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
        cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3, SI3.
        destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
          as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6).
        match goal with |- fqtree _ _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
        apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. intros bg off Hh.
        pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
        set (st7 := upd_ctx _ st6) in *.
        assert (Hh6 : hosts st6 bg g) by exact Hh.
        pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV6))) _ _ _ Hh6 (ex_intro _ 0 GR6)) as ->.
        assert (MR7 : MR st7 g = MR st6 g) by reflexivity. rewrite MR7, MR6.
        replace (sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0) with 16 by (unfold sstart, gbase; cbn -[Z.mul Z.add get_stride]; unfold UNIT; lia).
        change (fst (rid, 0)) with rid.
        apply SINV_split in SI3 as [SG3 Q3].
        destruct (c63_quant st3 L3 BL LS3 P g rid needed n off INV3 ltac:(lia) eq_refl Hbig SG3 Q3 A3' ltac:(exact (proj2 HR Hbig)))
          as (SG6 & Q6 & A6 & _).
        fold st6 in SG6, Q6, A6.
        assert (SV6 : forall s x i, s_slots st6 !! s = Some (x, i) -> exists b, hosts st6 b x).
        { intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV6)))))) _ _ _ Hs)). }
        split.
        -- apply SINV_split. split.
           ++ apply (SG_frame st6 st7 _ eq_refl eq_refl ltac:(intros; reflexivity) SV6 SG6).
           ++ destruct Q6 as [Q1' Q2' Q3' Q4' Q5' Q6']. constructor; auto.
        -- apply (AQ_frame st6 st7 _ P eq_refl ltac:(intros; reflexivity)); [| exact A6]. exact (aq_carved _ _ _ A6).
      * (* [comment removed for export] *)
        split; [exact (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2)|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

Theorem malloc_core_fq : fqtree B L (malloc_core full_lay st n) (CORE_POSTQ n BL P).
Proof.
  unfold malloc_core.
  destruct (size_overflows n) eqn:Hov.
  - apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. split; [exact SI| exact HAQ].
  - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
    + exact (malloc_big_fq Hbig Hov).
    + exact (malloc_small_fq Hsmall).
Qed.
End COREQ.

Theorem malloc_core_fq_proof : malloc_core_fq_stmt.
Proof. intros st L BL LS P n B INV TF SI HAQ Hn HNR HR HB. exact (malloc_core_fq st L BL LS P n B INV TF SI HAQ Hn HR HB HNR). Qed.

Check (malloc_core_fq_proof : malloc_core_fq_stmt).
