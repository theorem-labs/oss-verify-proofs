(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (15 recorded proofs replaced by written proofs (MIS_sub, LR_sub, n63_sub and 12 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 MI_Cnt MI_Sim KStep KLink KEv LB_Tables LB_Inv LB_Sum LB_Kernel LB_Embed LB_Bound LB_WNtf LB_XferF LB_Tree.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_WFree () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C46Stdlib5Lists4List2hdC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum<zsum_map_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc7dec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?nontrivial_freeC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib4Spec6LB_Inv6zcountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum?zsum_map_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum;zcount_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum=zcount_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum:zcount_extC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC59OSSVerify5KrLib4Spec6Malloc7mapinfoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7slotclsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MI_Inv9bl_removeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec6LB_Inv3MISC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6LB_Inv5isbigC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6LB_Inv2LRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3n63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C46Stdlib5Lists4List:fold_rightC59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec6MI_Cnt@round_up_pg_specC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6LB_Sum9zsum_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3R63C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C47Corelib4Init5Logic6or_indI47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv4SINV00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv2AQ00C1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_mapsBlookup_delete_SomeC47Corelib4Init5Logic:not_eq_symK47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7ncarvedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv=is_metakind_bC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum;msum_deleteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv6apagesC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables2S_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4stdgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables:std_nestedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7bighostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7std_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3nscC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK59OSSVerify5KrLib4Spec6LB_Inv4SINV01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3CAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4NCAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4PQOKC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6LB_Inv2AQ01C1?~~~~~~~~~~~~~~~C35stdpp4base6deleteC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6LB_Sum4msumC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveI59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree6LR_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree7n63_subC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6MI_Ext8ce_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9ce_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4zlenC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC46Stdlib6ZArith:ZArith_dec8Z_lt_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z=testbit_neg_rK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z:bits_inj_0K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WNtf2:dec_hdr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree?ftree_guard_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf8ntf_allQC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec7LB_WNtf3FFR00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4Spec8LB_WFree5SINVx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_XferF9SINV_xferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ap_removeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6MR_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6ce_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:ce_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext8ce_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables4cmaxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree<In_bl_removeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib7Classes?RelationClassesCPreOrder_TransitiveC56Stdlib6ZArith6BinInt1Z:eq_le_inclc59OSSVerify5KrLib4Spec8LB_WFree7MIS_subC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<transitivityC46Stdlib5Lists4List8flat_mapC59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_totalC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec3KEv<in_ap_removeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree>bl_remove_map'C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4Spec8LB_WFree5SINVx01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorderC59OSSVerify5KrLib4Spec7LB_Tree6fqtreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree:fqtree_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree<fqtree_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WNtf2@free_INVL_closedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim;free_prefixC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8free_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9dec_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound=regions_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv;group_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv:meta_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv9brk_pagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3PHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound4ORPHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound<ledger_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel2gmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel2BBC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib4Spec8LB_WFree6AQ_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree7AQ_ctrlC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ir_groupsC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List9filter_InC59OSSVerify5KrLib4Spec6LB_Sum6mtl_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8ir_shapeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_aiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib4Spec8LB_WFree=mask_le0_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<okay_to_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:g_freeableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib4Spec6Malloc7testbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool=orb_false_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib4Spec6MI_Inv9g_presentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf4geomC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf<FFR_upd_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree<SINVx_prefixC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree:SINVx_xferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv6im_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf8ffr_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_TreeHlbytes_event_post_munmapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree>SINV_drop_orphC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_WFree6SINV_XC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterK59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib4Spec9MI_WFree25xorphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree7rejectsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2x0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsb".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma MIS_sub st BL c c0 : MIS st (bl_remove c0 BL) c <= MIS st BL c.
Proof.
  unfold MIS. induction BL as [|k l IH]; cbn; [lia|]. destruct (aptr_eqb (bslot k) c0); rewrite ?zcount_cons; [| lia].
  pose proof (zcount_nonneg (fun k0 : blk => match slotcls st (bslot k0) with Some c' => (c' =? c) && (size_to_class (bsize k0) =? c - 1) | None => false end) l).
  destruct (match slotcls st (bslot k) with Some c' => (c' =? c) && (size_to_class (bsize k) =? c - 1) | None => false end); lia.
Qed.
Lemma LR_sub BL c c0 : LR (bl_remove c0 BL) c <= LR BL c.
Proof.
  unfold LR. induction BL as [|k l IH]; cbn; [lia|]. destruct (aptr_eqb (bslot k) c0); rewrite ?zcount_cons; [| lia].
  pose proof (zcount_nonneg (fun k0 : blk => negb (isbig k0) && (size_to_class (bsize k0) =? c)) l). destruct (negb (isbig k) && _); lia.
Qed.
Lemma n63_sub BL c0 : n63 (bl_remove c0 BL) <= n63 BL.
Proof.
  unfold n63. induction BL as [|k l IH]; cbn; [lia|]. destruct (aptr_eqb (bslot k) c0); rewrite ?zcount_cons; [| lia].
  pose proof (zcount_nonneg isbig l). destruct (isbig k); lia.
Qed.
Lemma R63_sub BL c0 : R63 (bl_remove c0 BL) <= R63 BL.
Proof.
  unfold R63. induction BL as [|k l IH]; cbn [bl_remove map]; [unfold zsum; cbn; lia|]. destruct (aptr_eqb (bslot k) c0); cbn [map]; rewrite ?zsum_cons; [| lia].
  assert (0 <= (if isbig k then round_up_pg (bsize k + IB + UNIT) else 0)).
  { unfold isbig. destruct (Z.leb_spec MMAP_THRESHOLD (bsize k)); [pose proof (round_up_pg_spec (bsize k + IB + UNIT)); unfold MMAP_THRESHOLD, IB, UNIT in *; lia| lia]. }
  assert (0 <= zsum (map (fun k0 => if isbig k0 then round_up_pg (bsize k0 + IB + UNIT) else 0) (bl_remove c0 l))).
  { apply zsum_map_nonneg. intros k0 _. unfold isbig. destruct (Z.leb_spec MMAP_THRESHOLD (bsize k0)); [pose proof (round_up_pg_spec (bsize k0 + IB + UNIT)); unfold MMAP_THRESHOLD, IB, UNIT in *; lia| lia]. }
  lia.
Qed.
Lemma In_bl_remove k c0 BL : In k (bl_remove c0 BL) -> In k BL.
Proof. induction BL as [|k' l IH]; cbn; [tauto|]. destruct (aptr_eqb (bslot k') c0); cbn; tauto. Qed.

(* [comment removed for export] *)
Lemma SINV_drop_orph X st L BL LS P rid r : INVL X st L BL LS -> s_regions st !! rid = Some r -> r_kind r = RKGroup ->
  SINV X st BL -> AQ st BL P -> SINV X (drop_region rid st) BL /\ AQ (drop_region rid st) BL P.
Proof.
  intros INV Hr K SI HAQ.
  assert (RG : forall q rq, s_regions (drop_region rid st) !! q = Some rq <-> s_regions st !! q = Some rq /\ q <> rid).
  { intros q rq. unfold drop_region. cbn. rewrite lookup_delete_Some. split; intros [A1 A2]; split; auto. }
  assert (NC : ncarved (drop_region rid st) = ncarved st) by reflexivity.
  assert (AP : apages (drop_region rid st) = apages st).
  { unfold apages, regions_l. change (zsum (map ?f (map_to_list (s_regions (drop_region rid st))))) with (msum f (s_regions (drop_region rid st))).
    change (zsum (map ?f (map_to_list (s_regions st)))) with (msum f (s_regions st)).
    unfold drop_region. cbn. rewrite (msum_delete _ (s_regions st) rid r Hr). unfold is_metakind_b at 2. rewrite K. cbn.
    unfold msum. apply zsum_map_ext. intros [q rq] Hq. cbn. unfold frontier. cbn. reflexivity. }
  split.
  - destruct SI. constructor; cbn -[drop_region]; rewrite ?NC, ?AP; auto.
    + intros q rq Hq Kq. apply RG in Hq as [Hq _]. eauto.
    + intros q rq Hq Kq. apply RG in Hq as [Hq _]. eauto.
    + intros q1 q2 r1 r2 H1 H2 K1 K2 NE. apply RG in H1 as [H1 _]. apply RG in H2 as [H2 _]. eauto.
  - destruct HAQ. constructor; cbn -[drop_region]; rewrite ?NC; auto.
Qed.

(* [comment removed for export] *)
Lemma SINV_X X X' st BL : x_idle X' = x_idle X -> SINV X st BL -> SINV X' st BL.
Proof. intros E S. destruct S. constructor; auto. rewrite E. auto. Qed.

Lemma AQ_sub st BL P c0 : AQ st BL P -> AQ st (bl_remove c0 BL) P.
Proof.
  intros A. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  - intros c Hc. pose proof (LR_sub BL c c0). specialize (A1 c Hc). lia.
  - pose proof (n63_sub BL c0). lia.
Qed.

Lemma AQ_ctrl st st1 BL P : ctrl_eq st st1 -> AQ st BL P -> AQ st1 BL P.
Proof.
  intros CE A. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  - intros c Hc. unfold gcnt, MR, get_meta_rec. rewrite (ce_groups _ _ CE), (ce_metas _ _ CE). apply A2. exact Hc.
  - unfold ncarved. rewrite (ce_metas _ _ CE). exact A4.
Qed.

(* [comment removed for export] *)
Lemma mask_le0_zero x : 0 <= x -> (forall i, 0 <= i -> Z.testbit x i = true -> i <= 0) -> Z.testbit x 0 = false -> x = 0.
Proof.
  intros Hx Hb H0. apply Z.bits_inj_0. intros j.
  destruct (Z_lt_dec j 0) as [Hn|Hn]; [apply Z.testbit_neg_r; lia|].
  destruct (Z.testbit x j) eqn:E; [| reflexivity]. exfalso.
  pose proof (Hb j ltac:(lia) E). assert (j = 0) by lia. subst j. rewrite H0 in E. discriminate.
Qed.

(* [comment removed for export] *)
Record SINVx (X : extras) (st : mstate) (BL : list blk) (ex : option aptr) : Prop := mkSINVx {
  sx_cls : forall k, In k BL -> exists m i, s_slots st !! bslot k = Some (m, i)
      /\ (m_sizeclass (MR st m) < 48 -> bsize k < MMAP_THRESHOLD
            /\ (size_to_class (bsize k) = m_sizeclass (MR st m) \/ size_to_class (bsize k) = m_sizeclass (MR st m) - 1))
      /\ (m_sizeclass (MR st m) = 63 -> MMAP_THRESHOLD <= bsize k /\ m_maplen (MR st m) * 4096 = round_up_pg (bsize k + IB + UNIT));
  sx_mis : forall c, MIS st BL c <= 13;
  sx_map : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) < 48 -> m_maplen (MR st m) <> 0 ->
      m_maplen (MR st m) * 4096 <= cnt_of (MR st m) * S_ (m_sizeclass (MR st m)) + 4111;
  sx_std : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> stdg st m = true ->
      (m_maplen (MR st m) = 0 <-> std_nested (m_sizeclass (MR st m)) = true)
      /\ (m_maplen (MR st m) = 0 -> exists p i, s_slots st !! b = Some (p, i) /\ m_sizeclass (MR st p) = bighost (m_sizeclass (MR st m)))
      /\ (m_maplen (MR st m) <> 0 -> m_maplen (MR st m) * 4096 = std_len (m_sizeclass (MR st m)));
  sx_small : forall c, 0 <= c < 48 -> nsc st c < 160;
  sx_63 : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) = 63 -> Some m <> ex ->
      In (slot_start' (MR st m) 0) (map bslot BL);
  sx_host : forall b m ai p i, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_maplen (MR st m) = 0 ->
      s_slots st !! b = Some (p, i) -> m_sizeclass (MR st p) <= 23;
  sx_leak : forall m mr, s_metas st !! m = Some mr -> m_mem mr = None -> m_next mr <> None \/ In m (x_idle X);
  sx_pages : 101 * apages st <= ncarved st + c_avail_meta_count (s_ctx st);
  sx_brk : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKBrk -> 101 * (r_len r / PGSZ - 2) <= ncarved st;
  sx_len : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKMeta ->
      exists j, 1 <= j <= c_meta_alloc_shift (s_ctx st) /\ r_len r = 2 ^ j * PGSZ;
  sx_dist : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 ->
      r_kind r1 = RKMeta -> r_kind r2 = RKMeta -> rid1 <> rid2 -> r_len r1 <> r_len r2;
  sx_shift : 1 <= c_meta_alloc_shift (s_ctx st) -> 101 * (2 ^ c_meta_alloc_shift (s_ctx st) - 1) <= 2 * ncarved st + 101
}.

Lemma SINVx_xfer X1 X2 st1 st2 L1 L2 BL LS1 LS2 P ex :
  INVL X1 st1 L1 BL LS1 -> INVL X2 st2 L2 BL LS2 -> x_idle X2 = x_idle X1 -> FFR st1 st2 -> AQ st1 BL P -> SINVx X1 st1 BL ex ->
  (forall b m ai, ex = Some m -> s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> False) ->
  SINV X2 st2 BL /\ AQ st2 BL P /\ (forall c, 0 <= c < 48 -> gcnt st2 c <= gcnt st1 c) /\ ncarved st2 = ncarved st1.
Proof.
  intros I1 I2 ID F A S EX. destruct S.
  eapply (SINV_xfer X1 X2 st1 st2 L1 L2 BL LS1 LS2 P ex); eauto.
Qed.

Lemma bl_remove_map' c BL : map bslot (bl_remove c BL) = ap_remove c (map bslot BL).
Proof.
  induction BL as [|k BL IH]; cbn; [reflexivity|]. destruct (aptr_eqb (bslot k) c); [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma SINVx_prefix X X' st st1 L BL LS c m i ex :
  INVL X st L BL LS -> ctrl_eq st st1 -> x_idle X' = x_idle X -> s_slots st !! c = Some (m, i) ->
  (m_sizeclass (MR st m) = 63 -> ex = Some m) ->
  SINV X st BL -> SINVx X' st1 (bl_remove c BL) ex.
Proof.
  intros INV CE ID Hs HEX S.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (NC : ncarved st1 = ncarved st) by (unfold ncarved; rewrite (ce_metas _ _ CE); reflexivity).
  assert (AP : apages st1 = apages st).
  { unfold apages, regions_l, frontier. rewrite (ce_regions _ _ CE), (ce_ctx _ _ CE). reflexivity. }
  assert (SCL : forall s, slotcls st1 s = slotcls st s) by (intros s; unfold slotcls, cls; rewrite (ce_slots _ _ CE); destruct (s_slots st !! s) as [[? ?]|]; [rewrite MR1|]; reflexivity).
  assert (STD : forall x, stdg st1 x = stdg st x) by (intros x; unfold stdg, cls; rewrite !MR1; reflexivity).
  destruct S. constructor; rewrite ?(ce_slots _ _ CE), ?(ce_groups _ _ CE), ?(ce_metas _ _ CE), ?(ce_regions _ _ CE), ?(ce_ctx _ _ CE), ?NC, ?AP, ?ID; auto.
  - intros k Hk. destruct (qb_cls k (In_bl_remove _ c _ Hk)) as (m0 & i0 & H0 & H1 & H2). exists m0, i0. rewrite !MR1. auto.
  - intros c'. etransitivity; [| apply (qb_mis c')]. etransitivity; [| apply (MIS_sub st BL c' c)]. apply Z.eq_le_incl. unfold MIS. apply zcount_ext. intros k _. rewrite SCL. reflexivity.
  - intros b m' ai Hg. rewrite !MR1. intros A1 A2. exact (qg_map _ _ _ Hg A1 A2).
  - intros b m' ai Hg. rewrite STD, !MR1. intros SG. destruct (qg_std _ _ _ Hg SG) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p' & i' & Hs' & E'). exists p', i'. rewrite (MR1 p'). auto.
  - intros c' Hc'. replace (nsc st1 c') with (nsc st c'); [apply qg_small; exact Hc'|].
    unfold nsc, gmetas, groups_l, cls. rewrite (ce_groups _ _ CE). apply zsum_map_ext. intros mb _. rewrite STD, MR1. reflexivity.
  - intros b m' ai Hg C63 NE. rewrite !MR1 in C63 |- *. rewrite bl_remove_map'. apply in_ap_remove; [exact (qg_63 _ _ _ Hg C63)|].
    intros E. pose proof (is_total _ _ _ IS b m' 0 (ex_intro _ ai Hg) ltac:(pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)); lia)) as T.
    rewrite E, Hs in T. assert (m' = m) by congruence. subst m'. apply NE. symmetry. apply HEX. exact C63.
  - intros b m' ai p' i' Hg. rewrite !MR1. intros Z0 Hs'. exact (qg_host _ _ _ _ _ Hg Z0 Hs').
Qed.

Lemma SINV_SINVx X st BL : SINV X st BL -> SINVx X st BL None.
Proof. intros S. destruct S. constructor; auto. intros b m ai Hg H63 _. eauto. Qed.

Section FREEQ.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z) (c : cptr) (off n : Z) (B : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis SI : SINV x0 st BL.
Hypothesis HAQ : AQ st BL P.
Hypothesis Hk : In ((c, off), n) BL.
Hypothesis HB : PHI P + R63 BL <= B + 3 * PGSZ.

Theorem free_fq :
  fqtree B L (free st (Some (aadd c (UNIT * off))))
        (fun L' st' => exists LS', INVL x0 st' L' (bl_remove c BL) LS' /\ SINV x0 st' (bl_remove c BL) /\ AQ st' (bl_remove c BL) P).
Proof.
  pose proof (free_INVL_closed st L BL LS c off n INV Hk) as FT.
  destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
  cbn zeta in FH, INV1, Hm1, Hi, Ec, NA, NF, SC, AGREE.
  set (p := aadd c (UNIT * off)) in *. set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)) in *.
  unfold free in FT |- *. rewrite FH in FT |- *. cbn [sbind] in FT |- *.
  (* [comment removed for export] *)
  assert (LB0 : gm L + BB L <= B).
  { pose proof (regions_bound x0 st L BL LS P INV SI HAQ eq_refl) as R1. pose proof (ledger_bound x0 st L BL LS INV) as R2.
    unfold ORPH in R1. cbn [x_orph x0] in R1. lia. }
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE1)).
  assert (HAQ1 : AQ st1 (bl_remove c BL) P) by (apply (AQ_ctrl st st1); [exact CE1| apply AQ_sub; exact HAQ]).
  pose proof INV1 as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  destruct Hm1 as [ai Hg1].
  pose proof (ig_ok _ _ _ IG1 _ _ _ Hg1) as GO1.
  (* [comment removed for export] *)
  assert (GPOS : forall g, In g (ld_groups L) -> 0 <= snd g).
  { intros g Hg. apply (Permutation_in _ (ir_groups _ _ _ IR1)) in Hg. apply in_map_iff in Hg as ([rid r] & <- & Hin). cbn.
    apply filter_In in Hin as [Hin _]. apply mtl_in in Hin. pose proof (ir_shape _ _ _ IR1 _ _ Hin) as (_ & _ & L0 & _). lia. }
  (* [comment removed for export] *)
  pose proof (g_masks _ _ _ _ _ _ GO1) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO1) as AI.
  assert (C63 : m_sizeclass (MR st1 m) = 63 ->
            m_freed (MR st1 m) = 0 /\ m_avail (MR st1 m) = 0 /\ m_last_idx (MR st1 m) = 0 /\ i = 0 /\ okay_to_free st1 m = true).
  { intros H63. pose proof (g_sc _ _ _ _ _ _ GO1) as [[R48 _]|(_ & LI0 & ML & NL)]; [lia|].
    assert (Hi0 : i = 0) by lia. unfold tbit in NA, NF. rewrite Hi0 in NA, NF.
    assert (FZ : m_freed (MR st1 m) = 0) by (apply mask_le0_zero; [exact M2| intros j Hj Hb; pose proof (M4 j Hj Hb); lia| exact NF]).
    assert (AZ : m_avail (MR st1 m) = 0) by (apply mask_le0_zero; [exact M1| intros j Hj Hb; pose proof (M3 j Hj Hb); lia| exact NA]).
    split; [exact FZ|]. split; [exact AZ|]. split; [exact LI0|]. split; [exact Hi0|].
    unfold okay_to_free. change (get_meta_rec st1 m) with (MR st1 m). rewrite (g_freeable _ _ _ _ _ _ GO1), H63. reflexivity. }
  unfold free_tail in FT |- *. change (get_meta_rec st1 m) with (MR st1 m) in FT |- *.
  apply ftree_guard_inv in FT as [GC FT]. apply fqtree_guard; [exact GC|].
  destruct (negb ((m_freed (MR st1 m) =? 0) || (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))))) eqn:BR.
  - (* [comment removed for export] *)
    cbn [fqtree ftree ret] in FT |- *. destruct FT as [LS' INV']. exists LS'. split; [exact INV'|].
    assert (N63 : m_sizeclass (MR st1 m) <> 63).
    { intros H63. destruct (C63 H63) as (FZ & _). apply Bool.negb_true_iff in BR. apply Bool.orb_false_iff in BR as [BR1 _]. apply Z.eqb_neq in BR1. exact (BR1 FZ). }
    assert (F : FFR st1 (upd_meta m (m_set_freed (m_freed (MR st1 m) + bit i)) st1)).
    { apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ GO1)| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr]. }
    destruct (SINVx_xfer (xpend x0 (Some c)) x0 st1 _ L L (bl_remove c BL) LS LS' P None INV1 INV' eq_refl F HAQ1
               (SINVx_prefix x0 (xpend x0 (Some c)) st st1 L BL LS c m i None INV CE1 eq_refl Hs ltac:(intros H63; exfalso; apply N63; rewrite MR1; exact H63) SI)
               ltac:(intros; discriminate)) as (S' & A' & _).
    split; [exact S'| exact A'].
  - (* [comment removed for export] *)
    set (K := fun (st2 : mstate) (mi : mapinfo) => match mi with
          | Some (base, len) => if negb (len =? 0) then SVis (EMunmap (conc st2 base) len) (fun ru : Z => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1)) else ret st2
          | None => ret st2 end) in FT |- *.
    destruct (ntf_allQ mstate FUEL dec_hdr dec_hdr (dec_hdr_ok mstate) (dec_hdr_ok mstate) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i K (ret st1)
                INV1 (ex_intro _ ai Hg1) Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))
      as (st' & mi & LS' & EQ & _ & [RG SEC] & [F CASE] & POST).
    rewrite EQ in FT |- *.
    set (ex := if m_sizeclass (MR st1 m) =? 63 then Some m else None).
    assert (SX1 : SINVx (xpend x0 (Some c)) st1 (bl_remove c BL) ex).
    { apply (SINVx_prefix x0 (xpend x0 (Some c)) st st1 L BL LS c m i ex INV CE1 eq_refl Hs); [| exact SI].
      intros H63. unfold ex. rewrite MR1, H63. reflexivity. }
    (* [comment removed for export] *)
    assert (EXG : forall st2, FFR st1 st2 -> (forall X2 L2 LS2, INVL X2 st2 L2 (bl_remove c BL) LS2 ->
              (s_groups st2 !! bm = None \/ ((Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))) && okay_to_free st1 m) = false) ->
              forall b m0 ai0, ex = Some m0 -> s_groups st2 !! b = Some (mkGhdr (Some m0) ai0) -> False)).
    { intros st2 F2 X2 L2 LS2 INV2 CASE2 b m0 ai0 Hex Hb. unfold ex in Hex.
      destruct (Z.eqb_spec (m_sizeclass (MR st1 m)) 63) as [H63|]; [| discriminate]. assert (m0 = m) by congruence. subst m0.
      destruct (C63 H63) as (FZ & AZ & LI0 & Hi0 & OK).
      destruct CASE2 as [GONE|CF].
      - pose proof (im_hdr _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ Hb) as (m' & Em & MEM & _). cbn in Em. assert (m' = m) by congruence. subst m'.
        destruct (ffr_meta _ _ F2 m) as [G|[Z2 _]]; [| rewrite MEM in Z2; discriminate].
        pose proof (im_hdr _ _ _ IM1 _ _ Hg1) as (m'' & Em'' & MEM1 & _). cbn in Em''. assert (m'' = m) by congruence. subst m''.
        unfold geom in G. rewrite MEM, MEM1 in G. assert (b = bm) by congruence. subst b. rewrite GONE in Hb. discriminate.
      - rewrite FZ, AZ, LI0, Hi0, OK in CF. cbn in CF. discriminate. }
    destruct mi as [[base len]|].
    + destruct POST as (r & Hb0 & Hr & Kr & Elen & Lpos & INV'). cbn [K] in FT |- *.
      replace (negb (len =? 0)) with true in FT |- * by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      cbn [ftree] in FT. destruct FT as [PRE FK].
      apply fqtree_vis; [reflexivity| reflexivity| exact PRE| exact I| |  |].
      * intros z Hz. etransitivity; [apply lbytes_event_post_munmap; exact GPOS| exact LB0].
      * intros a Ha. specialize (FK a). rewrite Ha in FK. cbn [answer_ok] in Ha. rewrite Ha in FK |- *.
        cbn [fqtree ftree ret] in FK |- *. destruct FK as [LS'' INV'']. exists LS''. split; [exact INV''|].
        destruct (SINVx_xfer (xpend x0 (Some c)) _ st1 st' L L (bl_remove c BL) LS LS' P ex INV1 INV' eq_refl F HAQ1 SX1
                   (EXG st' F _ L LS' INV' ltac:(destruct CASE as [G|[? _]]; [left; exact G| discriminate]))) as (S' & A' & _).
        destruct (SINV_drop_orph _ st' L (bl_remove c BL) LS' P (fst base) r INV' Hr Kr S' A') as [S'' A''].
        split; [| exact A'']. exact (SINV_X _ x0 _ _ eq_refl S'') || exact (SINV_X (xorph (xpend (xpend x0 (Some c)) None) (Some (fst base))) x0 _ _ eq_refl S'').
      * intros a Ha. specialize (FK a). rewrite Ha in FK. cbn [answer_ok] in Ha. rewrite Ha. exact I.
    + cbn [K fqtree ftree ret] in FT |- *. destruct FT as [LS'' INV'']. exists LS''. split; [exact INV''|].
      destruct (SINVx_xfer (xpend x0 (Some c)) _ st1 st' L L (bl_remove c BL) LS LS' P ex INV1 POST eq_refl F HAQ1 SX1
                 (EXG st' F _ L LS' POST ltac:(destruct CASE as [G|(_ & _ & G)]; [left; exact G| right; exact G]))) as (S' & A' & _).
      split; [exact S'| exact A'].
Qed.
End FREEQ.
