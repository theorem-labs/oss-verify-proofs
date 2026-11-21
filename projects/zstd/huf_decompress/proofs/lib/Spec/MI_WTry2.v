(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (17 recorded proofs replaced by written proofs (taf_trans, taf_upd_meta, taf_set_active and 14 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 MI_WTry.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WTry2 () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC47Corelib4Init9Datatypes3appC45stdpp>list_relations4list9NoDup_nilC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4base6ElemOfC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertI35stdpp4base<list_elem_of00C35stdpp8fin_maps@lookup_insert_eqC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp9decidable;decide_TrueI35stdpp8fin_maps6FinMap00C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01k59OSSVerify5KrLib4Spec8MI_WTry28TA_frame01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4Spec8MI_WTry28TA_frame00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitGget_head_set_head_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry28taf_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec8MI_Pres4=dequeue_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec7MI_List<dequeue_headC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idI59OSSVerify5KrLib4Spec8MI_Pres4=ctx_but_heads00C1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<lhead_eq_decC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv7il_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01c59OSSVerify5KrLib4Spec8MI_WTry27hd_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9il_activeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry25hd_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres49old_listsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List=lists_next_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry25GOODHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4;INVL_rotateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List4fupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc>set_active_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4;next_listedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry27hd_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_restC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry28hd_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres46xfreshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres35xidleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4<INVL_dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<dequeue_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List7data_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WNtf29data_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_aiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z6bits_0C59OSSVerify5KrLib4Spec8MI_Pres45m_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4@INVL_clear_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry27hd_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=optr_eqb_specC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec7MI_List?lists_singletonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6il_dllC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6linkedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=optr_eqb_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec6MI_Inv8il_nodupC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list:NoDup_consK35stdpp4base<list_elem_of01C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04I35stdpp4base5NoDup00C35stdpp4base7elem_ofI59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega7EnvRing5PExpr01C59OSSVerify5KrLib4Spec8MI_ArithAtestbit_mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WFree:guard_trueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WNtfAactivate_group_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry27TA_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WTry9ta_fin_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry2<taf_upd_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry29taf_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitFget_meta_rec_upd_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry2?set_avail_viewsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbK59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specc59OSSVerify5KrLib4Spec8MI_WTry2Ddequeue_exhausted_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry2;taf_dequeueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry29rotate_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry2>taf_set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry2Iland_mask_upto_zero_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WTry<span_loop_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib4Spec7MI_WTry;INVL_set_aiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv=ig_onepartialC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry2Bland_mask_upto_allC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WNtf=INVL_activateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3BINVL_decay_bouncesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry29taf_decayC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WTry26fin_okC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03K46Stdlib9micromega=RingMicromega3Op201".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Record TA_frame (st st1 : mstate) (sc : Z) : Prop := mkTAF {
  taf_regions : s_regions st1 = s_regions st;
  taf_shadow : s_shadow st1 = s_shadow st;
  taf_tick : s_tick st1 = s_tick st;
  taf_slots : s_slots st1 = s_slots st;
  taf_areas : s_areas st1 = s_areas st;
  taf_next_rid : s_next_rid st1 = s_next_rid st;
  taf_heads : forall h, h <> LActive sc -> get_head st1 h = get_head st h;
  taf_usage : forall sc', usage st1 sc' = usage st sc';
  taf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
  taf_ssec : s_secret st1 = s_secret st;
  taf_secret : c_secret (s_ctx st1) = c_secret (s_ctx st) /\ c_init_done (s_ctx st1) = c_init_done (s_ctx st)
}.
Lemma taf_refl st sc : TA_frame st st sc.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WTry2 ()) [] "h02sch12sth21Hh31hh43sc'p;4p;1p;2p;6p;3p;>p10000R0p4p710R1p1000gp4p710R2p8P0p4p7210P2p8g001ER0p4p70R3p1002:p4p710p8P3P1p8P3p1002Qp4p710R1p8P3p1002mp4p710R4p8P3p1003Kp4p7210p8P3p1003hp4p710R5p8P3P2p8P3p1004FR6p4p710R7p8P3p1004bR8p4p710R9p8P3P8p4p7210R8p8P3p1005;p4p710p8P3p1005Xp4p710p8P3p1006>R:p4p710p8P3p1006WR;p4p710p8P3p1006oR<p4p710p8P3p1007Op4p710p8P3p1007fp4p710p8P3p1008=p4p710p8P3p1008UR=p4p710p8P3p1008lR>p4p710p8P3p1009HR?p4p710p8P3P?p4p7210p8P3p1009\p4p710p8P3p100:5p4p73110R?p8P3p100:GR@p4p710RAp8P3p100:[RBp4p710RCp8P3p100:op4p710p8P3p100;Kp4p7<111111111110R3p8g00;mRDp4p70REP1p8PEP4p8PEp100<bp4p710R4p8PEP2p8PEP6p4p7210p8PEP6p4p73110R6p8PEp100=@R1p4p7511100RFp8PEP:p4p741110R:p8PEP<p4p741110R<p8PEP@p4p7210p8PEP@p4p73110R@p8PEPBp4p7210p8PEPBp4p73110RBp8PEP3p8P5P9p8P5P8p8P4P2p8p100=Zp4p710P2p8P1p4p73101R4p100>LREp4p73110p8P4P6p8P4p100>ep4p710p8P4p100?8R6p4p7201p8P4p100?Jp4p7201p8P4P@p8P4PBp8P4p100?\RBp4p73110p8P4p100@6p4p7201p8P1p4p710R4PEp4p710p8P4P7p8P4P9p8P4P8p8P4PAp8P4PCp8P4PBp4p710p8g00@IRBp4p710R4P5p8P4P9p8P4P8p8P4P?p8PBp4p741110R?P>p4p73101p8P3P2p8P:PFp8PFP:p8P;p4p741110R;P1p4p76111100R:p8P:P;p8P<P1p4p771111100R;p8P;P<p8P=p4p741110R=P1p4p7:1111111100R1p8P1P=p8P6p4p7200R6P?p8P?P6p8PBj41Tg00@]j1FTg00AWj20Tg00B1j13Tg00Bjj1ETg00Caj4;Tg00D?j6:Tg00D`j24Tg00E@j16Tg00F8j17Tg00G0j18Tg00Gkj19Tg00Hcj32Tg00I=j1DTg00IVj2CTg00JOj2BTg00KEj1<Tg00L;j1=Tg00M:j1>Tg00N3j1?Tg00Nlj1@Tg00Ohj4ATg00PCl>5Tg00Q@RBg00R9R6f1R?P?f0R=g00RWR1g00S5R<g00SNR;g00SlC1%F?'0P1P<P;g00TeC1%3?'0%E?,01P0P1P<P6g00U^R:C;RFP1P<P;P6P:g00V7E:R:1406C1%6?'0P0PFP:g00VUC1%7?'0%8?,01g00WLR1%9?921=#Df3/C?,0DW2W3f2/B=,06X46%<?RD#=,06%>?,06%?DR1=261%@DRD=26D1061106DCAM>5X06X1BP?P=O2W0W1o"). Qed.
Lemma taf_trans a b c sc : TA_frame a b sc -> TA_frame b c sc -> TA_frame a c sc.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A12 [A10 A11]] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B12 [B10 B11]]; constructor; try congruence.
  all: try (intros h Hh; rewrite (B7 h Hh); apply A7; exact Hh).
  all: try (intros sc'; rewrite (B8 sc'); apply A8).
  all: split; congruence.
Qed.
Lemma taf_upd_meta st m f sc : TA_frame st (upd_meta m f st) sc.
Proof. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_set_active st sc v : TA_frame st (set_active sc v st) sc.
Proof.
  constructor; auto; try (intros h Hh; change (set_active sc v st) with (set_head (LActive sc) v st); apply get_head_set_head_other; exact Hh).
Qed.
Lemma taf_decay st sc sc0 : TA_frame st (decay_bounces sc0 st) sc.
Proof. unfold decay_bounces. destruct (sc_in_seq_range _ && _); [| apply taf_refl]. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_dequeue st sc m : TA_frame st (dequeue (LActive sc) m st) sc.
Proof.
  destruct (dequeue_frame (LActive sc) m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC). destruct FC.
  constructor; auto.
  all: try (intros h Hh; rewrite dequeue_head; destruct (decide (h = LActive sc)); [congruence| reflexivity]).
  all: try (intros sc'; unfold usage, ctx; rewrite cb_usage; reflexivity).
  all: try (split; assumption).
Qed.

(* [comment removed for export] *)
Section HEADFACTS.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HA : active st sc = Some m.
Lemma hd_list : exists rest, LS (LActive sc) = m :: rest.
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as H. change (get_head st (LActive sc)) with (active st sc) in H. rewrite HA in H.
  destruct (LS (LActive sc)) as [|a rest]; cbn in H; [discriminate|]. inversion H. exists rest. reflexivity.
Qed.
Lemma hd_in : In m (LS (LActive sc)).
Proof. destruct hd_list as [rest ->]. left. reflexivity. Qed.
Lemma hd_facts : 0 <= sc < 48 /\ m_sizeclass (MR st m) = sc /\ exists b ai, s_groups st !! b = Some (mkGhdr (Some m) ai).
Proof.
  destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m hd_in) as (A & [b [ai Hb]] & C). split; [exact A|]. split; [exact C|]. exists b, ai. exact Hb.
Qed.
Lemma hd_head : head_of (LS (LActive sc)) = Some m.
Proof. destruct hd_list as [rest ->]. reflexivity. Qed.
Lemma hd_next : exists mn, m_next (MR st m) = Some mn /\ In mn (LS (LActive sc)).
Proof.
  destruct (lists_next_in st LS (old_lists _ _ _ _ _ INV) (LActive sc) m hd_in) as (y & Hy & E & _). exists y. auto.
Qed.
End HEADFACTS.

(* [comment removed for export] *)
Definition GOODH (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr) : Prop :=
  INVL X st L BL LS /\ active st sc = Some m /\ m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0.

Section STEPS.
Variables (X : extras) (L : mled) (BL : list blk) (sc : Z).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

(* [comment removed for export] *)
Lemma rotate_ok st LS m mn :
  GOODH X st L BL LS sc m -> m_next (MR st m) = Some mn ->
  exists LS', GOODH X (set_active sc (Some mn) st) L BL LS' sc mn.
Proof.
  intros (INV & HA & AV & FR) Hn.
  destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  assert (INV' : INVL X (set_head (LActive sc) (Some mn) st) L BL (fupd LS (LActive sc) (rest ++ [m]))).
  { apply (INVL_rotate X st L BL LS sc m mn rest INV HL Hn). intros _ _. auto. }
  exists (fupd LS (LActive sc) (rest ++ [m])). split; [exact INV'|].
  split; [unfold active, set_active, ctx; cbn; rewrite lookup_insert_eq; reflexivity|].
  change (MR (set_active sc (Some mn) st) mn) with (MR st mn).
  pose proof (next_listed X st L BL LS INV (LActive sc) m mn (hd_in X st L BL LS sc m INV HA) Hn) as Hin.
  destruct (aptr_eq_dec mn m) as [->|NE]; [auto|].
  destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc mn Hin) as (_ & [bb [aa Hbb]] & _).
  apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
  rewrite (hd_head X st L BL LS sc m INV HA). congruence.
Qed.

(* [comment removed for export] *)
Lemma dequeue_exhausted_ok st LS m :
  INVL X st L BL LS -> active st sc = Some m -> m_avail (MR st m) = 0 -> m_freed (MR st m) = 0 ->
  exists LS' rest, INVL X (dequeue (LActive sc) m st) L BL LS' /\ LS (LActive sc) = m :: rest
    /\ active (dequeue (LActive sc) m st) sc = head_of rest
    /\ (forall m1, head_of rest = Some m1 -> m_avail (MR st m1) = 0 /\ m_freed (MR st m1) <> 0).
Proof.
  intros INV HA AV FR. destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & b & ai & Hb).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
  pose proof (INVL_dequeue X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)) as INV1.
  assert (INV2 : INVL (xfresh (xfresh X (Some m)) None) (dequeue (LActive sc) m st) L BL (fupd LS (LActive sc) ([] ++ rest))).
  { apply (INVL_clear_fresh _ _ L BL _ m INV1 eq_refl). intros bb aix Hbb.
    destruct (dequeue_frame (LActive sc) m st) as (_ & _ & _ & _ & G5 & _). rewrite G5 in Hbb.
    pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ (ex_intro _ aix Hbb) (ex_intro _ ai Hb)) as ->. rewrite Hb in Hbb. inversion Hbb. subst aix.
    pose proof (dequeue_data (LActive sc) m st m) as D. destruct (data_same _ _ 0 D) as (_ & El & Ea & Ef & Es & _).
    rewrite El, Ea, Ef, Es. split; [| split; [intros; auto| split; [| intros; auto]]].
    - intros Hlt. exfalso. pose proof (g_masks _ _ _ _ _ _ GO) as (_ & _ & _ & _ & _ & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
      specialize (M6 (m_last_idx (MR st m)) ltac:(lia)). unfold tbit in M6. rewrite FR, Z.bits_0 in M6. discriminate.
    - intros sc0 Hin. exfalso. cbn in Hin.
      apply (m_out X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)). exists (LActive sc0). exact Hin. }
  replace (xfresh (xfresh X (Some m)) None) with X in INV2 by (destruct X; cbn in HF |- *; subst; reflexivity).
  exists (fupd LS (LActive sc) ([] ++ rest)), rest. split; [exact INV2|]. split; [exact HL|]. split.
  - change (active (dequeue (LActive sc) m st) sc) with (get_head (dequeue (LActive sc) m st) (LActive sc)). rewrite dequeue_head.
    rewrite decide_True by reflexivity. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. rewrite HL in HH. cbn in HH.
    destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
    destruct (optr_eqb_spec (Some mn) (Some m)) as [E|NE].
    + inversion E. subst mn. pose proof (proj1 (lists_singleton st LS (old_lists _ _ _ _ _ INV) (LActive sc) m rest HL) Hn) as ER. rewrite ER. reflexivity.
    + change (get_head st (LActive sc)) with (active st sc). rewrite HA, optr_eqb_refl. rewrite HL in Hin. destruct Hin as [->|Hin]; [congruence|].
      destruct rest as [|a rest']; [destruct Hin|]. cbn.
      pose proof (il_dll _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as D. rewrite HL in D. cbn [dll app] in D. destruct D as (D1 & _). rewrite Hn in D1. exact D1.
  - intros m1 Hm1. destruct rest as [|a rest']; cbn in Hm1; [discriminate|]. inversion Hm1. subst a.
    assert (Hin : In m1 (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
    destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m1 Hin) as (_ & [bb [aa Hbb]] & _).
    apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
    rewrite HL. cbn. intros E. inversion E. subst m1.
    pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left.
Qed.
End STEPS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mask_upto_all f n : 0 <= f -> 0 <= n -> (forall i, 0 <= i -> Z.testbit f i = true -> i <= n) -> Z.land f (mask_upto n) = f.
Proof.
  intros Hf Hn H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask_upto by lia.
  destruct (Z.testbit f i) eqn:E; [| reflexivity]. cbn. apply Z.leb_le. exact (H i Hi E).
Qed.

Lemma land_mask_upto_zero_above f n : 0 <= f -> 0 <= n -> Z.land f (mask_upto n) = 0 ->
  forall i, 0 <= i -> Z.testbit f i = true -> n < i.
Proof.
  intros Hf Hn H i Hi Hb. destruct (Z.lt_ge_cases n i) as [|LE]; [assumption|]. exfalso.
  assert (T : Z.testbit (Z.land f (mask_upto n)) i = true) by (rewrite Z.land_spec, testbit_mask_upto, Hb by lia; cbn; apply Z.leb_le; lia).
  rewrite H, Z.bits_0 in T. discriminate.
Qed.

Section TRY.
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

Definition TA_POST (st st1 : mstate) (first : Z) (LS1 : lhead -> list aptr) : Prop :=
  TA_frame st st1 sc /\
  ((first = 0 /\ active st1 sc = None /\ INVL X st1 L BL LS1)
   \/ (exists g bg ai idx, first <> 0 /\ 0 <= first /\ ctz32 first = idx /\ active st1 sc = Some g
         /\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ 0 <= idx <= m_last_idx (MR st1 g)
         /\ m_sizeclass (MR st1 g) = sc /\ UNIT * size_class sc <= get_stride (MR st1 g)
         /\ INVL (xpend X (Some (fst bg, sstart (MR st1 g) idx))) st1 L BL LS1)).

Lemma set_avail_views v r : m_last_idx (m_set_avail v r) = m_last_idx r /\ m_sizeclass (m_set_avail v r) = m_sizeclass r
  /\ get_stride (m_set_avail v r) = get_stride r /\ (forall i, sstart (m_set_avail v r) i = sstart r i).
Proof. destruct r; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma fin_ok st0 st LS m (mask : Z) :
  INVL X st L BL LS -> TA_frame st0 st sc -> active st sc = Some m -> m_avail (MR st m) = mask -> mask <> 0 ->
  exists st1 first LS1, ta_fin st m mask k = k st1 first /\ TA_POST st0 st1 first LS1.
Proof.
  intros INV TF HA AM MNZ. destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4).
  rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|]. split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
  right. exists m, bm, ai, (ctz32 (lowbit mask)).
  assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
  assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
  rewrite MRm. destruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
  split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.

Theorem try_avail_ok st LS :
  INVL X st L BL LS ->
  exists st1 first LS1, try_avail sc st k bail = k st1 first /\ TA_POST st st1 first LS1.
Proof.
  intros INV. unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ eexists _, _, LS. split; [reflexivity|]. split; [apply taf_refl| left; auto]. }
  fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ exact (fin_ok st st LS m _ INV (taf_refl st sc) HA eq_refl ANZ). }
  (* [comment removed for export] *)
  assert (STEP1 : exists st1 m1 LS1,
    (if m_freed (MR st m) =? 0
     then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
     else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
    /\ GOODH X st1 L BL LS1 sc m1 /\ TA_frame st st1 sc
    \/ (m_freed (MR st m) = 0 /\ active (dequeue (LActive sc) m st) sc = None /\ exists LS1, INVL X (dequeue (LActive sc) m st) L BL LS1)).
  { destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
    - destruct (dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ) as (LS1 & rest & INV1 & HL & HA1 & NXT).
      rewrite HA1. destruct rest as [|m1 rest']; cbn.
      + exists st, m, LS. right. split; [exact FZ|]. split; [first [reflexivity| rewrite HA1; reflexivity]| exists LS1; exact INV1].
      + exists (dequeue (LActive sc) m st), m1, LS1. left. split; [reflexivity|]. split; [| apply taf_dequeue].
        destruct (NXT m1 eq_refl) as [A1 F1].
        assert (NE : m1 <> m).
        { intros ->. pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left. }
        pose proof (dequeue_data (LActive sc) m st m1) as D. destruct (data_same _ _ 0 D) as (_ & _ & Ea & Ef & _).
        split; [exact INV1|]. split; [first [reflexivity| rewrite HA1; reflexivity]|]. rewrite Ea, Ef. auto.
    - destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st LS m mn (conj INV (conj HA (conj AZ FNZ))) Hn) as [LS1 G1].
      exists (set_active sc (Some mn) st), mn, LS1. left. split; [reflexivity|]. split; [exact G1| apply taf_set_active]. }
  destruct STEP1 as (st1 & m1 & LS1 & [(E1 & G1 & TF1)|(FZ & HA1 & LS1' & INV1)]).
  2:{ rewrite (proj2 (Z.eqb_eq _ _) FZ), HA1. eexists _, 0, LS1'. split; [reflexivity|]. split; [apply taf_dequeue| left; auto]. }
  rewrite E1. clear E1.
  (* [comment removed for export] *)
  assert (STEP2 : exists st2 m2 LS2,
    (let mr := get_meta_rec st1 m1 in
     if (m_freed (MR st1 m1) =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0)
     then match m_next mr with Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn)) | None => (st1, m1, m_freed (MR st1 m1)) end
     else (st1, m1, m_freed (MR st1 m1))) = (st2, m2, m_freed (MR st2 m2))
    /\ GOODH X st2 L BL LS2 sc m2 /\ TA_frame st st2 sc).
  { cbn zeta. fold (MR st1 m1). destruct (_ && _).
    - pose proof G1 as (INV1 & HA1 & _). destruct (hd_next X st1 L BL LS1 sc m1 INV1 HA1) as (mn & Hn & _). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st1 LS1 m1 mn G1 Hn) as [LS2 G2].
      exists (set_active sc (Some mn) st1), mn, LS2. split; [reflexivity|]. split; [exact G2| eapply taf_trans; [exact TF1| apply taf_set_active]].
    - exists st1, m1, LS1. auto. }
  destruct STEP2 as (st2 & m2 & LS2 & E2 & G2 & TF2). cbn zeta in E2. fold (MR st1 m1) in E2 |- *.
  match goal with |- context [let '(p, mask) := ?t in _] => change t with (st2, m2, m_freed (MR st2 m2)) end || rewrite E2.
  cbn iota. fold (MR st2 m2).
  destruct G2 as (INV2 & HA2 & AZ2 & FNZ2).
  destruct (hd_facts X st2 L BL LS2 sc m2 INV2 HA2) as (_ & Esc2 & b2 & ai2 & Hb2).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb2) as GO2.
  pose proof (g_masks _ _ _ _ _ _ GO2) as (W1 & W2 & W3 & W4 & W5 & W6). pose proof (g_ai _ _ _ _ _ _ GO2) as AI2. pose proof (g_li _ _ _ _ _ _ GO2) as LI2.
  rewrite (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ (ex_intro _ ai2 Hb2)). cbn [default].
  assert (GAI : group_active_idx st2 b2 = ai2).
  { unfold group_active_idx, get_group. rewrite Hb2. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
  rewrite GAI.
  (* [comment removed for export] *)
  assert (STEP3 : exists st3 m3 LS3 b3 ai3,
    (if Z.land (m_freed (MR st2 m2)) (mask_upto ai2) =? 0
     then if negb (optr_eqb (m_next (MR st2 m2)) (Some m2))
          then match m_next (MR st2 m2) with Some mn => (set_active sc (Some mn) st2, mn) | None => (st2, m2) end
          else (let cnt := ai2 + 2 in
                let size := size_class (m_sizeclass (MR st2 m2)) * UNIT in
                let span := UNIT + size * cnt in
                let cnt := span_loop 300 cnt span size in
                let cnt := if m_last_idx (MR st2 m2) + 1 <? cnt then m_last_idx (MR st2 m2) + 1 else cnt in
                (set_group_active_idx b2 (cnt - 1) st2, m2))
     else (st2, m2)) = (st3, m3)
    /\ GOODH X st3 L BL LS3 sc m3 /\ TA_frame st st3 sc
    /\ s_groups st3 !! b3 = Some (mkGhdr (Some m3) ai3) /\ Z.land (m_freed (MR st3 m3)) (mask_upto ai3) <> 0).
  { destruct (Z.eqb_spec (Z.land (m_freed (MR st2 m2)) (mask_upto ai2)) 0) as [LZ|LNZ].
    - (* [comment removed for export] *)
      pose proof (land_mask_upto_zero_above _ _ W2 (proj1 AI2) LZ) as ABOVE.
      assert (PART : ai2 < m_last_idx (MR st2 m2)).
      { destruct (Z.eq_dec (m_freed (MR st2 m2)) 0) as [|NZ]; [contradiction|].
        destruct (Z.lt_ge_cases ai2 (m_last_idx (MR st2 m2))) as [|GE]; [assumption|]. exfalso. apply NZ.
        apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. destruct (Z.testbit (m_freed (MR st2 m2)) i) eqn:E; [| reflexivity].
        pose proof (ABOVE i Hi E). pose proof (W4 i Hi E). lia. }
      destruct (hd_next X st2 L BL LS2 sc m2 INV2 HA2) as (mn & Hn & Hin). rewrite Hn.
      destruct (optr_eqb_spec (Some mn) (Some m2)) as [E|NE]; cbn [negb].
      + (* [comment removed for export] *)
        set (cnt0 := span_loop 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)).
        set (cnt := if m_last_idx (MR st2 m2) + 1 <? cnt0 then m_last_idx (MR st2 m2) + 1 else cnt0).
        pose proof (span_loop_ge 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)) as SL. fold cnt0 in SL.
        assert (CR : ai2 + 1 <= cnt - 1 <= m_last_idx (MR st2 m2)) by (unfold cnt; destruct (Z.ltb_spec (m_last_idx (MR st2 m2) + 1) cnt0); lia).
        unfold set_group_active_idx, get_group. rewrite Hb2. cbn [g_meta].
        replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia).
        set (st3 := Malloc.set_groups _ st2).
        assert (INV3 : INVL X st3 L BL LS2).
        { apply (INVL_set_ai X st2 L BL LS2 m2 b2 ai2 (cnt - 1) INV2 Hb2); [lia| | intros _; rewrite Esc2; exact (hd_in X st2 L BL LS2 sc m2 INV2 HA2)].
          intros i Hi Hb. unfold tbit in Hb. rewrite AZ2, Z.bits_0 in Hb. discriminate. }
        exists st3, m2, LS2, b2, (cnt - 1). split; [reflexivity|].
        split; [split; [exact INV3| split; [exact HA2| auto]]|].
        split; [eapply taf_trans; [exact TF2| constructor; auto; try (intros h _; destruct h; reflexivity)]|].
        split; [unfold st3; cbn; rewrite lookup_insert_eq; reflexivity|].
        change (MR st3 m2) with (MR st2 m2). intros E0.
        assert (Tb : Z.testbit (Z.land (m_freed (MR st2 m2)) (mask_upto (cnt - 1))) (ai2 + 1) = true).
        { rewrite Z.land_spec, testbit_mask_upto by lia. unfold tbit in W6. rewrite (W6 (ai2 + 1)) by lia. cbn. apply Z.leb_le. lia. }
        rewrite E0, Z.bits_0 in Tb. discriminate.
      + (* [comment removed for export] *)
        destruct (rotate_ok X L BL sc HF st2 LS2 m2 mn (conj INV2 (conj HA2 (conj AZ2 FNZ2))) Hn) as [LS3 G3].
        assert (NEm : mn <> m2) by congruence.
        destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV2)))) sc mn Hin) as (_ & [b3 [ai3 Hb3]] & Esc3).
        pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb3) as GO3.
        assert (FULL : ai3 = m_last_idx (MR st2 mn)).
        { pose proof (g_ai _ _ _ _ _ _ GO3) as AI3. destruct (Z.lt_ge_cases ai3 (m_last_idx (MR st2 mn))) as [LT|]; [| lia]. exfalso.
          apply NEm. eapply (ig_onepartial _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2)))))); [exact Hb3| exact Hb2| exact LT| exact PART| congruence]. }
        exists (set_active sc (Some mn) st2), mn, LS3, b3, ai3. split; [reflexivity|]. split; [exact G3|].
        split; [eapply taf_trans; [exact TF2| apply taf_set_active]|]. split; [exact Hb3|].
        change (MR (set_active sc (Some mn) st2) mn) with (MR st2 mn).
        pose proof (g_masks _ _ _ _ _ _ GO3) as (V1 & V2 & V3 & V4 & V5 & V6).
        pose proof (g_ai _ _ _ _ _ _ GO3) as AI3.
        rewrite (land_mask_upto_all (m_freed (MR st2 mn)) ai3 V2 ltac:(clear -AI3; lia) ltac:(rewrite FULL; exact V4)).
        destruct G3 as (_ & _ & _ & F3). exact F3.
    - exists st2, m2, LS2, b2, ai2. split; [reflexivity|]. split; [split; [exact INV2| auto]|]. auto. }
  destruct STEP3 as (st3 & m3 & LS3 & b3 & ai3 & E3 & G3 & TF3 & Hb3 & ACT).
  match goal with |- context [let '(st4, m4) := ?t in _] => change t with (st3, m3) end || rewrite E3.
  cbn iota. clear E3.
  (* [comment removed for export] *)
  destruct G3 as (INV3 & HA3 & AZ3 & FNZ3).
  destruct (hd_facts X st3 L BL LS3 sc m3 INV3 HA3) as (_ & Esc3 & _).
  rewrite (activate_group_eq X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3).
  pose proof (INVL_activate X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3 ltac:(rewrite Esc3; exact (hd_head X st3 L BL LS3 sc m3 INV3 HA3))) as INV4.
  set (st4 := upd_meta m3 _ st3) in INV4 |- *.
  rewrite (guard_true 40) by (apply Bool.negb_true_iff; apply Z.eqb_neq; exact ACT).
  pose proof (INVL_decay_bounces X st4 L BL LS3 (m_sizeclass (get_meta_rec st4 m3)) INV4) as INV5.
  set (st5 := decay_bounces _ st4) in INV5 |- *.
  assert (MR5 : MR st5 m3 = m_set_avail (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) (m_set_freed (Z.ldiff (m_freed (MR st3 m3)) (mask_upto ai3)) (MR st3 m3))).
  { transitivity (MR st4 m3); [unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); reflexivity|]. unfold st4, MR. apply get_meta_rec_upd_same. }
  assert (HA5 : active st5 sc = Some m3) by (unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); exact HA3).
  destruct (fin_ok st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5) as (st6 & first & LS6 & E6 & POST).
  - eapply taf_trans; [exact TF3|]. eapply taf_trans; [apply taf_upd_meta| apply taf_decay].
  - exact HA5.
  - rewrite MR5. reflexivity.
  - exact ACT.
  - exists st6, first, LS6. split; [exact E6| exact POST].
Qed.
End TRY.
