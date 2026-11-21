(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (19 recorded proofs replaced by written proofs (ptree_follow_lafter, followk_follow, follow_sbind and 16 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree MI_WFree2 MI_WNtf2 MI_WGroup MI_Cnt MI_TF2 MI_WSlot MI_WSlot2 MI_WSlot3 MI_WEnframe MI_WEnframe2 MI_WMalloc.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Sim () := "C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim6lafterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim7followkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ptreeC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_insertC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec7MI_Tree:ptree_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree;ptree_strelC1?~~~~~~~~~~~~~~~C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec7MI_Tree:ftree_prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree>eruns_vis_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree;eruns_sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9dec_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?nontrivial_freeC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree7rejectsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree;rejects_invC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC45stdpp>list_relations4list9NoDup_nilC35stdpp4base?list_elem_of_InC35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib4Spec4KInv5cpath00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv5cpath01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv5cpath02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indI59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec5STree9strel_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5strel00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec7MI_Tree<strel_followC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib4Spec5STree=strel_eq_steqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree4steq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree8steq_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim<strel_lafterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_SimCptree_follow_lafterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim>followk_followC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib4Spec4KInv9brk_phase02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_brkphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec4KInv:set_brkregC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec4KInv9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_groupsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec4KInv9bump_metaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9cpath_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim?event_post_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim<follow_sbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim=strel_followkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_SimAstrel_follow_someC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim;steq_followC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim=ptree_followkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4CRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree:guard_trueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WNtf2:dec_hdr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WNtf2?ntf_slots_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WNtf29ntf_spec2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec8MI_WFree;block_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8MI_WFree9blk_facts00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8free_hdrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9bl_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree;free_hdr_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext;ctrl_eq_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext<ctrl_eq_wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext=ctrl_eq_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree7bf_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree4bf_cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree8bf_hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree4bf_iC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree9bf_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec8MI_WFree6bf_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree6bf_fitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree4bf_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec7MI_Geom;sstart_succC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres23inTC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MI_KitCcell_read_wr8_otherC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ig_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7ish_domC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree27wr8_domC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6MI_Inv9ish_ticksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree27wr8_tksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres2AINVL_remove_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9ce_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext8ce_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6MR_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib4Spec8MI_WFree7bf_notAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree7bf_notFC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib4Spec6Malloc7testbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec6MI_Inv2x0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_leC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6Malloc7mapinfoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim;free_prefixC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6hdr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrlGfree_tail_slots_controlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4freeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z8lor_specC59OSSVerify5KrLib4Spec6MI_Ext:ce_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9ce_secretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim8prun_retC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xorphC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic5proj1K59OSSVerify5KrLib4Spec6Malloc<undef_reason04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim;INVL_hdr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl<free_controlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4FRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WNtf2@free_INVL_closedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim:cpath_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5cfreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6mallocC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WMalloc=INVL_set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup6TKS_ofC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6MI_TF2<TF0_tick_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WMalloc9CORE_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WMalloc>malloc_core_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>strip_set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl@malloc_core_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Sim<lafter_sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4MRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>malloc_controlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WMalloc;malloc_INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl;strip_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot5GP_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot8GP_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl=slot_of_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_WEnframe2:enframe_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_nodupC1?~~~~~~~~~~~~~~~I35stdpp4base<list_elem_of00C45stdpp>list_relations4list:NoDup_consC46Stdlib9micromega;ZifyClasses5mkappC59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base7elem_ofC56Stdlib6ZArith4Znat3N2Z8inj_succC56Stdlib6ZArith4Znat3N2Z6inj_ltC59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8lay_noneC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Set Implicit Arguments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint lafter {R} (L : mled) (t : M R) (ans : list Z) {struct t} : mled :=
  match t, ans with
  | SRet _, _ => L
  | SVis (EUndef _) _, _ => L
  | SVis e k, a :: ans' => lafter (event_post L e a) (k a) ans'
  | SVis _ _, [] => L
  end.

(* [comment removed for export] *)
Fixpoint followk {R} (t : M R) (ans : list Z) {struct t} : option (R * list Z) :=
  match t, ans with
  | SRet r, _ => Some (r, ans)
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => followk (k a) ans'
  | SVis _ _, [] => None
  end.

Lemma ptree_follow_lafter {R} : forall (t : M R) L Post ans r,
  ptree L t Post -> follow t ans = Some r -> cpath L t (lafter L t ans) r /\ Post (lafter L t ans) r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ptree follow lafter] in *.
  - inversion Hf; subst. split; [constructor| exact H].
  - destruct e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); case_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as [Hp HP]; split; [econstructor; eauto| exact HP]
      | destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

Lemma followk_follow {R} : forall (t : M R) ans x rest, followk t ans = Some (x, rest) -> follow t ans = Some x.
Proof.
  induction t as [r0|e k IH]; intros ans x rest H; cbn [followk follow] in *.
  - inversion H. reflexivity.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Lemma follow_sbind {R S} : forall (t : M R) (k : R -> M S) ans,
  follow (sbind t k) ans = match followk t ans with Some (x, rest) => follow (k x) rest | None => None end.
Proof.
  induction t as [r0|e k0 IH]; intros k ans; cbn [sbind followk follow]; [reflexivity|].
  destruct e; destruct ans as [|a ans']; cbn [follow]; try reflexivity; apply IH.
Qed.

Lemma lafter_sbind {R S} : forall (t : M R) (k : R -> M S) L ans x rest,
  followk t ans = Some (x, rest) -> lafter L (sbind t k) ans = lafter (lafter L t ans) (k x) rest.
Proof.
  induction t as [r0|e k0 IH]; intros k L ans x rest H; cbn [sbind followk lafter] in *.
  - inversion H. reflexivity.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; cbn [lafter]; apply IH; exact H.
Qed.

Lemma strel_followk {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall ans x1 rest, followk t1 ans = Some (x1, rest) ->
  exists x2, followk t2 ans = Some (x2, rest) /\ RR x1 x2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans x1 rest H; cbn [followk] in *.
  - inversion H. subst. eauto.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Lemma strel_lafter {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L ans; cbn [lafter]; [reflexivity|].
  destruct e; destruct ans; try reflexivity; apply IH.
Qed.

Lemma strel_follow_some {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) ans r1 :
  strel RR t1 t2 -> follow t1 ans = Some r1 -> exists r2, follow t2 ans = Some r2 /\ RR r1 r2.
Proof.
  intros H Hf. pose proof (strel_follow H ans) as F. rewrite Hf in F.
  destruct (follow t2 ans) as [r2|]; [exists r2; auto| destruct F].
Qed.

Lemma steq_follow {R} (t1 t2 : M R) ans : steq t1 t2 -> follow t1 ans = follow t2 ans.
Proof.
  intros H. apply strel_eq_steq in H. pose proof (strel_follow H ans) as F.
  destruct (follow t1 ans), (follow t2 ans); cbn in F; try reflexivity; [congruence| destruct F| destruct F].
Qed.

Lemma steq_followk {R} (t1 t2 : M R) : steq t1 t2 -> forall ans, followk t1 ans = followk t2 ans.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros ans; cbn [followk]; [reflexivity|].
  destruct e; destruct ans; try reflexivity; apply IH.
Qed.

Lemma steq_lafter {R} (t1 t2 : M R) : steq t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof. intros H. apply strel_eq_steq in H. apply (strel_lafter H). Qed.

Lemma ptree_followk {R} (t : M R) L Post ans x rest :
  ptree L t Post -> followk t ans = Some (x, rest) -> Post (lafter L t ans) x.
Proof. intros HP Hf. exact (proj2 (ptree_follow_lafter t L Post ans HP (followk_follow _ _ Hf))). Qed.

(* [comment removed for export] *)
Lemma event_post_live L e z : ld_live (event_post L e z) = ld_live L.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.

Lemma cpath_live {R} L (t : M R) L' r : cpath L t L' r -> ld_live L' = ld_live L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Unset Implicit Arguments.

Section SIM.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Local Notation PRUN := (prun pans pupd).

Lemma prun_ret {R} o (x : R) : PRUN o (SRet x) = SRet (o, x).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_prefix st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  exists m bm i,
    let p := aadd c (UNIT * off) in
    let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
    free_hdr st p = SRet (Some (st1, m, i))
    /\ ctrl_eq st st1 /\ strip st1 = strip st /\ s_slots st !! c = Some (m, i)
    /\ INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS /\ hosts st1 bm m
    /\ 0 <= i <= m_last_idx (MR st1 m) /\ c = (fst bm, sstart (MR st1 m) i)
    /\ tbit (m_avail (MR st1 m)) i = false /\ tbit (m_freed (MR st1 m)) i = false
    /\ (0 <= m_sizeclass (MR st1 m) < 48 \/ m_sizeclass (MR st1 m) = 63)
    /\ free_tail dec_hdr st1 m i = free_tail dec_slots st1 m i.
Proof.
  intros INV Hk.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  exists m, bm, i. cbn zeta.
  set (p := aadd c (UNIT * off)).
  set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).
  pose proof (free_hdr_eq st c off n m bm i ai a ar ka BF) as FH. fold p in FH. fold st1 in FH.
  assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
  assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hm. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  assert (STR1 : strip st1 = strip st).
  { destruct CE1 as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10]. unfold strip. rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9, C10. reflexivity. }
  assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
  { change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
    - intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
      subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
        intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ;
        pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _]; pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF); pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF);
        pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF); unfold UNIT, IB in *; lia.
    - subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
      change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
      assert (HP : P (fst bm)) by (destruct (ig_region _ _ _ IG _ _ Hm) as (r & Hr & Hkr); exists r; auto).
      assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
    - subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }
  assert (Hm1 : hosts st1 bm m). { exists ai. rewrite (ce_groups _ _ CE1). exact Hm. }
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE1)).
  assert (SC : 0 <= m_sizeclass (MR st1 m) < 48 \/ m_sizeclass (MR st1 m) = 63).
  { rewrite MR1. destruct (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hm)) as [[? ?]|[? ?]]; lia. }
  split; [exact FH|]. split; [exact CE1|]. split; [exact STR1|]. split; [exact Hs|]. split; [exact INV1|]. split; [exact Hm1|].
  rewrite !MR1. split; [exact Hi|]. split; [exact Ec|].
  split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [rewrite <- MR1; exact SC|].
  unfold free_tail.
  rewrite (ntf_slots_agree mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i _ (ret st1) INV1 Hm1); [reflexivity| | | | | |].
  - rewrite MR1. exact Hi.
  - cbn. rewrite MR1, Ec. reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold FUEL. lia.
  - unfold FUEL. lia.
Qed.

(* [comment removed for export] *)
Theorem INVL_hdr_ok st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL -> hdr_ok pans pupd st (aadd c (UNIT * off)) c.
Proof.
  intros INV Hk. destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
  cbn zeta in FH, AGREE, STR1.
  eexists _, m, i. split; [| split; [exact STR1| split; [exact Hs|]]].
  - intros o. rewrite FH. reflexivity.
  - intros o. rewrite AGREE, <- STR1. apply free_tail_slots_control.
Qed.

(* [comment removed for export] *)
Theorem free_leaf_facts st L BL LS c off n o ans o' st' :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  follow (PRUN o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  (forall rid r, s_regions st' !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st' = s_secret st.
Proof.
  intros INV Hk Hf. destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
  cbn zeta in *.
  set (st1 := wr16 (aadd (aadd c (UNIT * off)) (-2)) 0 (wr8 (aadd (aadd c (UNIT * off)) (-3)) 255 st)) in *.
  unfold free in Hf. rewrite FH in Hf. cbn [sbind] in Hf. unfold free_tail in Hf.
  rewrite (guard_true 60) in Hf by (unfold testbit; rewrite Z.lor_spec; fold (MR st1 m); unfold tbit in NA, NF; rewrite NA, NF; reflexivity).
  fold (MR st1 m) in Hf.
  pose proof (ce_regions _ _ CE1) as RG1. pose proof (ce_secret _ _ CE1) as SE1.
  destruct (negb ((m_freed (MR st1 m) =? 0) || (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))))).
  - rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. split; [intros rid r H; rewrite <- RG1; exact H| rewrite <- SE1; reflexivity].
  - destruct (ntf_spec2 mstate FUEL dec_hdr dec_hdr (dec_hdr_ok _) (dec_hdr_ok _) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1 Hm1 Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))
      as (st2 & mi & LS2 & EQ & _ & [RG2 SE2] & _).
    rewrite EQ in Hf.
    assert (K2 : (forall rid r, s_regions st2 !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st2 = s_secret st).
    { split; [intros rid r H; rewrite <- RG1, <- RG2; exact H| rewrite <- SE1, <- SE2; reflexivity]. }
    destruct mi as [[base len]|].
    + destruct (negb (len =? 0)).
      * unfold prun in Hf. rewrite (eruns_vis_keep) in Hf by reflexivity. destruct ans as [|a ans']; [cbn [follow] in Hf; discriminate Hf|]. cbn [follow] in Hf.
        destruct (munmap_answer_ok a).
        -- change (eruns (psel pans) pupd (pupd o (EMunmap (conc st2 base) len) a) (ret (drop_region (fst base) st2))) with
             (PRUN (pupd o (EMunmap (conc st2 base) len) a) (SRet (drop_region (fst base) st2))) in Hf.
           rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'.
           split; [| exact (proj2 K2)]. intros rid r H. unfold drop_region in H. cbn in H.
           destruct (N.eq_dec rid (fst base)) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate H|]. rewrite lookup_delete_ne in H by congruence. apply (proj1 K2). exact H.
        -- unfold bad_answer in Hf. rewrite eruns_vis_keep in Hf by reflexivity. cbn [follow] in Hf. discriminate Hf.
      * rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. exact K2.
    + rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. exact K2.
Qed.

(* [comment removed for export] *)
Theorem free_sim st L BL LS c off n o ans o' st' :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  follow (PRUN o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  let t := cfree (strip st) (Some c) in
  let L' := lafter L t ans in
  follow t ans = Some (strip st') /\ cpath L t L' (strip st') /\ ld_live L' = ld_live L
  /\ exists LS', INVL x0 st' L' (bl_remove c BL) LS'.
Proof.
  intros INV Hk Hf. cbn zeta.
  pose proof (free_control pans pupd st (aadd c (UNIT * off)) c o (INVL_hdr_ok st L BL LS c off n INV Hk)) as REL.
  pose proof (ftree_prun pans pupd Hpans (free st (Some (aadd c (UNIT * off)))) L _ o (free_INVL_closed st L BL LS c off n INV Hk)) as PT.
  destruct (strel_follow_some ans REL Hf) as (cs' & Hf2 & FR). unfold FREL in FR. cbn in FR. subst cs'.
  split; [exact Hf2|].
  pose proof (ptree_strel REL L _ (fun _ _ => True) ltac:(intros; exact I) PT) as PT2.
  destruct (ptree_follow_lafter _ L _ ans PT2 Hf2) as [CP _].
  split; [exact CP|]. split; [exact (cpath_live CP)|].
  destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ POST]. cbn in POST.
  rewrite <- (strel_lafter REL L ans). exact POST.
Qed.

(* [comment removed for export] *)
Theorem malloc_sim st L BL LS n o ans o' st' r :
  INVL x0 st L BL LS -> 0 <= n ->
  follow (PRUN o (malloc st n)) ans = Some (o', (st', r)) ->
  let t := cmalloc (strip st) n in
  let L' := lafter L t ans in
  exists rc, follow t ans = Some (strip st', rc) /\ cpath L t L' (strip st', rc) /\ ld_live L' = ld_live L /\ GP st st' /\
    match r, rc with
    | None, None => exists LS', INVL x0 st' L' BL LS'
    | Some pf, Some c => exists off LS', pf = aadd c (UNIT * off) /\ 0 <= off <= 255
                         /\ INVL x0 st' L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
    | _, _ => False
    end.
Proof.
  intros INV Hn Hf. cbn zeta.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  set (K := fun x : mstate * option (aptr * Z) => let '(st1, r) := x in
        match r with
        | None => ret (st1, @None aptr)
        | Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
        end).
  assert (E1 : steq (PRUN o (malloc st n)) (sbind (PRUN o (malloc_core full_lay st0 n)) (fun x => PRUN (fst x) (K (snd x))))).
  { unfold malloc, prun. apply eruns_sbind. }
  rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
  destruct (followk (PRUN o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].
  (* [comment removed for export] *)
  pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  set (L1 := lafter L (PRUN o (malloc_core full_lay st0 n)) ans) in *.
  destruct CP as (LIVE1 & GP1 & CP).
  (* [comment removed for export] *)
  pose proof (malloc_core_ctrl pans pupd n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans
               = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
  { unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
  rewrite LT.
  (* [comment removed for export] *)
  assert (PT2 : ptree L (cmalloc (strip st) n) (fun _ _ => True)).
  { eapply (ptree_strel (malloc_control pans pupd Hpans st n o)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans pupd Hpans (malloc st n) L _ o (malloc_INVL st L BL LS n INV Hn)). }
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  destruct rg as [[g idx]|].
  - destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.
    (* [comment removed for export] *)
    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
      (fun _ res => exists off, 0 <= off <= 255 /\ snd res = Some (aadd c0 (UNIT * off))
                      /\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ GP st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [exact Ho|]; split; [reflexivity|]; split; [exact INV2|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9, C10; reflexivity| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]])).
    pose proof (ftree_prun pans pupd Hpans _ L1 _ o1 EF) as PTE.
    cbn [K fst snd] in Hf.
    destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Ho & Er & INV2 & SS2 & GP2)]. cbn [fst snd] in Er, INV2, SS2, GP2. subst r.
    exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
    split; [rewrite <- LT; pose proof (ptree_follow_lafter _ L _ ans PT2 ltac:(rewrite FT, SS1; reflexivity)) as [C _]; rewrite SS2; exact C|].
    split; [exact LIVE1|]. split; [exact (GP_trans _ _ _ GP0 GP2)|].
    exists off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV2|].
    pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV2))))))) as ND. cbn [map bslot fst] in ND.
    apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
  - destruct CP as (LS1 & INV1). cbn [K fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
    exists None. split; [rewrite FT, SS1; reflexivity|].
    split; [rewrite <- LT; pose proof (ptree_follow_lafter _ L _ ans PT2 ltac:(rewrite FT, SS1; reflexivity)) as [C _]; exact C|].
    split; [exact LIVE1|]. split; [exact GP0|]. exists LS1. exact INV1.
Qed.
End SIM.
