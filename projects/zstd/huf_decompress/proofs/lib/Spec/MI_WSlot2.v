(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (ag_arith, shadow_next_rid_none, LS_empty_of and 6 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2 MI_WSlot.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WSlot2 () := "C47Corelib7Classes9Morphisms:respectfulC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC45stdpp>list_relations4list9NoDup_nilC35stdpp4gmap;gmap_lookupC35stdpp4base6ElemOfC35stdpp4base4fmapC35stdpp4base6LookupI35stdpp4base<list_elem_of00C35stdpp4base?list_elem_of_InC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot26REC_OKC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6MI_CntAalloc_group_arithC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt7cnt0_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec6MI_Cnt7nest_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot27ag_cnt1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot27ag_cnt2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot26ag_cn3C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesCPreOrder_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6MI_Cnt@round_up_pg_specC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6MI_Cnt6grp_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC56Stdlib6ZArith6BinInt1Z;le_preorderI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6MI_Inv7ish_domC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6MI_Inv6ir_idsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC47Corelib4Init5Logic9False_indC35stdpp4base6lookupC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_ltI59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C35stdpp4gmap:gmap_emptyC35stdpp4base5emptyC59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot2Eaccount_bounce_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot4X_asC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot2?step_seq_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3CINVL_account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3=INVL_step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF28TF0_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<free_meta_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2:ag_tail_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree9ftree_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt<grp_ok_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec4KInv9brk_quietC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree2<brk_quiet_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7lrangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_LedgerAmmap_answer_ok_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List5fm_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot<free_idle_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec7MI_List4fupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4;queue_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List8queue_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8MI_Pres4=ctx_but_heads00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot5GP_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot8GP_transC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_LedgerEINVL_new_group_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xorphC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib4Spec9MI_Ledger9ng_lookupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot2Dshadow_next_rid_noneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot2;LS_empty_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt8clamp_aiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib4Spec;MI_WCreate23agtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate29ag_top_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate23agGC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate29top_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_Ledger7ng_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2;agt_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2:agt_secretC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z7div_modK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega5Tauto8GFormula02C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib4Spec6MI_TF27TF0_TF2C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_brkphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree7rejectsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega5Tauto4kind02c59OSSVerify5KrLib4Spec9MI_WSlot2:st1'_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv4MAPFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv5MAPFXC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt=nest_ok_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~C35stdpp4base7elem_ofC45stdpp>list_relations4list:NoDup_consC46Stdlib5Lists4List2Inc59OSSVerify5KrLib4Spec9MI_WSlot29SLOT_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate2<ag_nested_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;nest_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate29nst_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrlAstrip_nest_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl?s_regions_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>s_secret_stripC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8sub_diagC59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WAMeta2=alloc_meta_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot2:ag_mmap_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot2:ag_nest_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot27AG_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC59OSSVerify5KrLib4Spec6Malloc7lh_nestC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9MI_WAMeta8AM_frame00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9MI_WAMeta7L_frame00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta:amf_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta7lf_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot6GP_amfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta:amf_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta8amf_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres35xidleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WSlot28ag_arithC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec9MI_WAMeta8amf_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta7lf_reflC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SLOT_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st1 : mstate) (idx : Z) (L1 : mled) (LS1 : lhead -> list aptr) : Prop :=
  (forall sc', sc' < sc -> active st1 sc' = active st sc') /\ ld_live L1 = ld_live L /\ GP st st1 /\
  ((idx = -1 /\ INVL (X_as idle) st1 L1 BL LS1 /\ TF0 st1)
   \/ (exists g bg ai, 0 <= idx <= m_last_idx (MR st1 g) /\ active st1 sc = Some g
         /\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ m_sizeclass (MR st1 g) = sc
         /\ req + IB <= get_stride (MR st1 g)
         /\ (sc < 28 -> get_stride (MR st1 g) = UNIT * size_class sc)
         /\ INVL (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
         /\ TF2 st1)).

(* [comment removed for export] *)
Definition AG_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st2 : mstate) (go : optr) (L2 : mled) (LS2 : lhead -> list aptr) : Prop :=
  (forall sc', sc' <= sc -> active st2 sc' = active st sc') /\ ld_live L2 = ld_live L /\ GP st st2 /\
  match go with
  | None => INVL (X_as idle) st2 L2 BL LS2 /\ TF0 st2
  | Some m => exists b ai last ml,
      s_groups st2 !! b = Some (mkGhdr (Some m) ai)
      /\ MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml
      /\ 0 <= ai <= last /\ last <= 31
      /\ req + IB <= get_stride (MR st2 m)
      /\ (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc)
      /\ (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0)
      /\ INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 /\ TF2 st2
  end.

(* [comment removed for export] *)
Definition REC_OK (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop) : Prop :=
  forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
  sc < j < 48 ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
  (forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
  ftree L (rec st j req k bail) Post.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ag_cnt1 (sc u0 : Z) : Z :=
  let size := UNIT * size_class sc in
  let cnt := cnt0_of sc u0 in
  if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_cnt2 (sc cnt1 u1 : Z) (nosmall : bool) : Z :=
  if (u1 <? 4 * cnt1) && negb nosmall then adj sc (UNIT * size_class sc) cnt1 else cnt1.

Definition ag_cn3 (sc req cnt2 u1 : Z) (nosmall : bool) : Z * Z :=
  let size := UNIT * size_class sc in
  let needed := round_up_pg (size * cnt2 + UNIT) in
  if negb nosmall && (cnt2 <=? 7) then
    let req' := round_up_pg (req + IB + UNIT) in
    if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
  else (cnt2, needed).

Lemma ag_arith sc req u0 u1 ns c3 n3 :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  let size := UNIT * size_class sc in
  (PGSZ / 2 < size * ag_cnt1 sc u0 + UNIT ->
   ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns = (c3, n3) ->
   grp_ok sc c3 n3 = true /\ ((c3 = 1 /\ n3 = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (size * c3 + UNIT <= n3)))
  /\ (size * ag_cnt1 sc u0 + UNIT <= PGSZ / 2 -> nest_ok sc (ag_cnt1 sc u0) = true).
Proof.
  intros Hsc Hreq Hfit. pose proof (alloc_group_arith sc req u0 u1 ns Hsc Hreq Hfit) as AR. cbn zeta in AR.
  change (if (cnt0_of sc u0 =? 1) && (UNIT * size_class sc * cnt0_of sc u0 + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc u0) with (ag_cnt1 sc u0) in AR.
  destruct AR as [AR1 AR2]. cbn zeta. split; [| exact AR2].
  intros HB E. specialize (AR1 HB).
  change (if (u1 <? 4 * ag_cnt1 sc u0) && negb ns
          then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 2
               else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 5
               else ag_cnt1 sc u0
          else ag_cnt1 sc u0) with (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in AR1.
  set (c2 := ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in *. clearbody c2.
  unfold ag_cn3 in E. cbn zeta in E.
  destruct (negb ns && (c2 <=? 7)).
  - destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [R|(R1 & R2 & R3)]; [left; exact R| right; rewrite R2 at 1; lia].
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
      right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
  - inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
    right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shadow_next_rid_none X st L BL LS : INVL X st L BL LS -> s_shadow st !! s_next_rid st = None.
Proof.
  intros INV. destruct (s_shadow st !! s_next_rid st) as [sh|] eqn:E; [| reflexivity]. exfalso.
  destruct (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E) as (r & Hr & _).
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hr). lia.
Qed.

Lemma LS_empty_of X st L BL LS sc : INVL X st L BL LS -> active st sc = None -> LS (LActive sc) = [].
Proof.
  intros INV HA. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma step_seq_fields st : let st' := step_seq st in
  s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
  /\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); cbn; repeat split; reflexivity. Qed.

Lemma account_bounce_fields sc0 st : let st' := account_bounce sc0 st in
  s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
  /\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof.
  unfold account_bounce. destruct (sc_in_seq_range sc0); [| cbn; repeat split; reflexivity].
  destruct (negb (unmap_seq st (sc0 - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc0 - 7) <? 10)); [| cbn; repeat split; reflexivity].
  destruct (bounces st (sc0 - 7) + 1 <? 100); cbn; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MMAP_BRANCH.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

Lemma st1'_facts :
  INVL (X_as (m :: idle)) st1' L1 BL LS1 /\ s_shadow st1' = s_shadow st1 /\ s_tick st1' = s_tick st1
  /\ (forall sc', active st1' sc' = active st1 sc') /\ TF0 st1' /\ s_regions st1' = s_regions st1 /\ s_secret st1' = s_secret st1.
Proof.
  destruct (account_bounce_fields sc st1) as (A1 & A2 & A3 & A4 & _). destruct (step_seq_fields (account_bounce sc st1)) as (B1 & B2 & B3 & B4 & _).
  assert (SH : s_shadow st1' = s_shadow st1) by (unfold st1'; rewrite B1, A1; reflexivity).
  assert (TK : s_tick st1' = s_tick st1) by (unfold st1'; rewrite B2, A2; reflexivity).
  split; [apply INVL_step_seq; apply INVL_account_bounce; exact INV1|].
  split; [exact SH|]. split; [exact TK|]. split; [intros sc'; unfold st1'; rewrite B3, A3; reflexivity|].
  split; [exact (TF0_ctrl st1 st1' SH TK TF1)|]. split; [unfold st1'; rewrite B4, A4; reflexivity|].
  unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
Qed.

Theorem ag_mmap_ft :
  ftree L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (s_atop st1') (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  destruct st1'_facts as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1').
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - (* [comment removed for export] *) cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + (* [comment removed for export] *)
      rewrite free_meta_eq.
      destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
        unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'. }
      split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
    + (* [comment removed for export] *)
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
      rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
      assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
      { rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
      assert (NS : s_shadow st2 !! rid = None).
      { rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
      assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
      assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
      assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      assert (HAI0 : sc = 0 -> AI = cnt - 1).
      { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
        pose proof (grp_ok_sound sc cnt needed GRP) as (Gc & _).
        replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      destruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
                  INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      eapply HK. split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1|]. split.
        - intros q rq Hq Kq. rewrite agt_regions. cbn. rewrite Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
        - rewrite agt_secret. cbn. rewrite Est2. cbn. exact SS1'. }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
                    = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
      split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NEST_BRANCH.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

Theorem ag_nest_ft :
  ftree L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
  - exact N5.
  - lia.
  - intros st2 idx L2 LS2 (ACT & LIVE & GP2 & RES). destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
    + (* [comment removed for export] *)
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
        unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
      split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      eapply HK. split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
        - rewrite agt_regions. change (s_regions (nest_layout st2 g idx j size cnt) = s_regions st2).
          rewrite <- (s_regions_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity.
        - rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
          rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity. }
      exists (fst bg, sstart (MR st2 g) idx), (cnt - 1), (cnt - 1), 0.
      rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
      rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
      split; [exact INV'| exact TF'].
Qed.
End NEST_BRANCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AG.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.

Theorem alloc_group_ft idle st L BL LS req (k : mstate -> optr -> M T) bail :
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None ->
  (forall st2 go L2 LS2, AG_POST idle sc req st L BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post) ->
  ftree L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
  intros INV TF ND Hsc Hreq Hfit HA HK. unfold alloc_group.
  eapply (alloc_meta_ft T BL Post _ bail (X_as idle) st L); [ | | exact INV| apply amf_refl| apply lf_refl].
  - (* [comment removed for export] *)
    intros st1 L1 LS1 INV1 AF LF. cbn beta iota. eapply HK.
    split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
    exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
  - (* [comment removed for export] *)
    intros st1 L1 LS1 m INV1 NIm AF LF. cbn beta iota zeta.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    + (* [comment removed for export] *)
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns). 
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        ftree L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (s_atop st1') (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        exact (ag_mmap_ft T idle st st1 L L1 BL LS1 m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED HK). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + (* [comment removed for export] *)
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      exact (ag_nest_ft T rec idle st st1 L L1 BL LS1 m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST HK).
Qed.
End AG.
