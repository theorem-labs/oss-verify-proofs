(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (dec_hdr_ok, dec_slots_ok, rem_notin and 11 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WNtf2 () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib4Spec8MI_WNtf27decodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC35stdpp4base;RelDecisionC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC45stdpp>list_relations4list9NoDup_nilC35stdpp4gmap;gmap_lookupC46Stdlib5Lists4List6nth_okC35stdpp4base6ElemOfC35stdpp4base4fmapC35stdpp4base6lookupI35stdpp4base<list_elem_of00C35stdpp4base?list_elem_of_InC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf26DEC_OKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7decoderC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?nontrivial_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI35stdpp4base5NoDup00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc9dec_slotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf26NTF_ATC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec8MI_Pres33remC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C35stdpp4base8DecisionC46Stdlib5Lists4List6removeK47Corelib4Init5Logic2or01C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2or02C46Stdlib5Lists4List2InI47Corelib4Init5Logic5False00I47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec8MI_Pres4;queue_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8MI_Pres4=ctx_but_heads00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List5fm_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List8queue_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3=INVL_unzombieC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres35xzombC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib4Spec8MI_WNtf29rem_notinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List4fupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_put_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@lookup_metas_putC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List7data_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4:INVL_queueC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec7MI_List<free_meta_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill:dec_hdr_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:free_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree28NTF_SPECC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf2:dec_hdr_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc=set_usage_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4=zomb_not_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4=idle_not_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill6fg_st1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill9INVL_killC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill4K_MRC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xorphC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf2@INVL_free_zombieC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill9K_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf2=regions_fm_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill8kill_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:record_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3=INVL_step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3?INVL_record_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C35stdpp4gmap:gmap_emptyC35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7mapinfoC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<okay_to_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:data_of_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec7MI_List?get_stride_dataC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list:NoDup_consC46Stdlib5Lists4List:in_app_iffC35stdpp4base7elem_ofC59OSSVerify5KrLib4Spec8MI_WFree:guard_trueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List8queue_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WNtfAactivate_group_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf2=free_group_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf2:ntf_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_aiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec9MI_WFree2;add_bit_lorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree26bit_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6MI_Inv:g_freeableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C46Stdlib4Bool4Bool:orb_true_rC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib4Spec8MI_ArithAtestbit_mask_uptoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Arith;testbit_bitC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib4Bool4Bool;orb_false_rC59OSSVerify5KrLib4Spec8MI_Pres4>INVL_set_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres46xfreshC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf29data_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_linkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6MI_Inv9il_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitC59OSSVerify5KrLib4Spec6MI_Inv8il_nodupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres35xidleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4<INVL_dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4=dequeue_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<dequeue_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<dequeue_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List7fupd_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=optr_eqb_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf2>head_of_eq_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_restC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WNtf=INVL_activateC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6MI_KitFget_meta_rec_upd_otherC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib4Spec8MI_Pres4=free_not_liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4;head_listedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WNtf8INVL_aorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9g_presentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:queue_dataC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7lor_0_lK59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4@INVL_clear_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres49old_listsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List;lists_notinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:g_unlistedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC47Corelib4Init5Logic6or_indC59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03c59OSSVerify5KrLib4Spec8MI_WNtf27ntf_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf2<dec_slots_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree29free_INVLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WNtf28ntf_specC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition decodes (T : Type) (st : mstate) (p pm : aptr) (ip : Z) : Prop :=
  s_slots st !! p = Some (pm, ip) /\ forall (k : aptr -> Z -> M T) (bail : M T), dec_hdr st p k bail = k pm ip.
Definition DEC_OK (T : Type) (dec : decoder T) : Prop :=
  forall st p pm ip (k : aptr -> Z -> M T) (bail : M T), decodes T st p pm ip -> dec st p k bail = k pm ip.
Lemma dec_hdr_ok T : DEC_OK T dec_hdr.
Proof. intros st p pm ip k bail [_ H]. apply H. Qed.
Lemma dec_slots_ok T : DEC_OK T dec_slots.
Proof. intros st p pm ip k bail [H _]. unfold dec_slots. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Definition NTF_AT (T : Type) (f : nat) : Prop :=
  forall (dec1 dec2 : decoder T), DEC_OK T dec1 -> DEC_OK T dec2 ->
  forall X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  exists st' mi LS',
    nontrivial_free dec1 f st g i k bail = k st' mi /\ nontrivial_free dec2 f st g i k bail = k st' mi /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    match mi with
    | None => INVL (xpend X None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
    end.

Lemma rem_notin g l : ~ In g l -> rem g l = l.
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|]. intros H.
  unfold rem. cbn. destruct (aptr_eq_dec g x) as [->|NE]; [exfalso; apply H; left; reflexivity|].
  cbn. f_equal. apply IH. tauto.
Qed.

Lemma regions_fm_st st g : s_regions (fm_st st g) = s_regions st.
Proof. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 st)) as (E & _). rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma INVL_free_zombie idle zomb pend orph st L BL LS g :
  INVL (mkX idle (g :: zomb) pend orph None) st L BL LS ->
  ~ In g zomb -> ~ In g idle ->
  exists LS', INVL (mkX idle zomb pend orph None) (fm_st st g) L BL LS'.
Proof.
  intros INV NZ NI.
  pose proof (INVL_unzombie _ st L BL LS g INV ltac:(left; reflexivity)) as INV1. cbn in INV1.
  unfold xzomb in INV1. cbn in INV1.
  unfold rem in INV1. cbn in INV1. destruct (aptr_eq_dec g g) as [_|NE]; [| congruence]. cbn in INV1.
  fold (rem g zomb) in INV1. rewrite (rem_notin g zomb NZ) in INV1.
  eexists. unfold fm_st.
  apply (INVL_queue _ (put_meta g meta0 st) L BL LS g LFree INV1).
  - unfold MR. rewrite get_meta_rec_put_same. reflexivity.
  - rewrite lookup_metas_put, aptr_eqb_refl. discriminate.
  - cbn. split; [unfold MR; rewrite get_meta_rec_put_same; reflexivity|]. split; [exact NI| exact NZ].
Qed.

Section FG.
Variables (T : Type) (f : nat).
Hypothesis IHf : NTF_AT T f.
Variables (dec1 dec2 : decoder T).
Hypothesis D1 : DEC_OK T dec1.
Hypothesis D2 : DEC_OK T dec2.
Variables (idle zomb : list aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Variables (k : mstate -> mapinfo -> M T) (bail : M T).
Let X := mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis NL : m_next (MR st g) = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
  tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Hypothesis FUEL : 49 - m_sizeclass (MR st g) <= Z.of_nat (S f).

Theorem free_group_ok :
  exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st g k bail = k st' mi /\
    free_group T dec2 (nontrivial_free dec2 f) st g k bail = k st' mi /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    match mi with
    | None => INVL (mkX idle zomb None None None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
    end.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (KSEC : forall U, s_secret (del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1)
            (del_group bg (upd_ctx (fun c => set_usage_map U c) st))) = s_secret st) by (intros; reflexivity).
  assert (FMSEC : forall s, s_secret (fm_st s g) = s_secret s).
  { intros s0. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s0)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
  assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
  assert (NZ : ~ In g zomb) by (intros Hz; exact (zomb_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  assert (NI : ~ In g idle) by (intros Hz; exact (idle_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  destruct (fg_st1 X st L BL LS g bg ai INV Hg) as (S1 & U1 & U2). cbn zeta in S1, U1, U2.
  unfold free_group. fold (MR st g).
  set (st1 := if m_sizeclass (MR st g) <? 48 then set_usage (m_sizeclass (MR st g)) (usage st (m_sizeclass (MR st g)) - (m_last_idx (MR st g) + 1)) st else st) in *.
  rewrite (hosts_mem _ _ _ IM _ _ Hgh).
  set (stk := del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1) (del_group bg st1)).
  pose proof (INVL_kill X st st1 L BL LS g bg ai i INV Hg eq_refl NL eq_refl Hi eq_refl ALL S1 U1 U2) as INVK.
  cbn [x_idle x_zomb X] in INVK. fold stk in INVK.
  pose proof (K_MR st st1 g bg S1 U1 U2) as KMR. fold stk in KMR.
  destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; cbn [negb].
  - (* [comment removed for export] *)
    destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2
                (fun m idx => nontrivial_free dec1 f stk m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail Hml)
      as (pm & ip & bpm & EQ & Hs' & Hpm' & Hf & Hip & Ep & Hsc).
    fold stk in EQ, Hs', Hpm'.
    assert (DQ : decodes T stk bg pm ip).
    { split; [exact Hs'|]. intros k' bail'.
      destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2 k' bail' Hml) as (pm' & ip' & bpm' & EQ' & Hs'' & _).
      fold stk in EQ', Hs''. rewrite Hs' in Hs''. inversion Hs''. subst. exact EQ'. }
    rewrite (D1 stk bg pm ip _ bail DQ), (D2 stk bg pm ip _ bail DQ).
    destruct (IHf dec1 dec2 D1 D2 (mkX idle (g :: zomb) (Some bg) None None) stk L BL LS pm bpm ip
                  (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail INVK Hpm')
      as (st3 & mi & LS3 & EQ3 & EQ3b & REG3 & POST3).
    + rewrite KMR. exact Hip.
    + cbn. rewrite KMR, Ep. reflexivity.
    + reflexivity.
    + reflexivity.
    + lia.
    + rewrite KMR. lia.
    + rewrite EQ3, EQ3b. rewrite !free_meta_eq. exists (fm_st st3 g), mi.
      destruct mi as [[base len]|].
      * destruct POST3 as (r & B0 & Hr & Hk & Hlen & Hpos & INV3). cbn in INV3.
        destruct (INVL_free_zombie idle zomb None (Some (fst base)) st3 L BL LS3 g INV3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|]. exists r.
        split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
      * cbn in POST3. destruct (INVL_free_zombie idle zomb None None st3 L BL LS3 g POST3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]| exact INV4].
  - (* [comment removed for export] *)
    rewrite !free_meta_eq.
    destruct (kill_top X st st1 L BL LS g bg ai INV Hg S1 U1 U2 Hml) as (r & B0 & Hr & Hk & Hlen & Hpos).
    fold stk in Hr.
    assert (INV2 : INVL (mkX idle (g :: zomb) None (Some (fst bg)) None) (record_seq (m_sizeclass (MR st g)) (step_seq stk)) L BL LS).
    { apply INVL_record_seq. apply INVL_step_seq. unfold stk. cbn [negb] in INVK. exact INVK. }
    destruct (INVL_free_zombie idle zomb None (Some (fst bg)) _ L BL LS g INV2 NZ NI) as [LS4 INV4].
    assert (RS : forall sc s, s_regions (record_seq sc (step_seq s)) = s_regions s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    assert (RSS : forall sc s, s_secret (record_seq sc (step_seq s)) = s_secret s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    eexists _, _, LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, RS, FMSEC, RSS.
    split; [split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|]. cbn. exists r. cbn.
    split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
Qed.
End FG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ntf_unfold {T} dec f st g i (k : mstate -> mapinfo -> M T) bail :
  nontrivial_free dec (S f) st g i k bail =
    (if (Z.lor (m_freed (MR st g)) (m_avail (MR st g)) + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g then
      match m_next (MR st g) with
      | Some _ =>
        guard 50 (m_sizeclass (MR st g) <? 48) (
          match optr_eqb (active st (m_sizeclass (MR st g))) (Some g), active (dequeue (LActive (m_sizeclass (MR st g))) g st) (m_sizeclass (MR st g)) with
          | true, Some a => activate_group a (dequeue (LActive (m_sizeclass (MR st g))) g st)
                              (fun st2 _ => free_group T dec (nontrivial_free dec f) st2 g k bail) bail
          | _, _ => free_group T dec (nontrivial_free dec f) (dequeue (LActive (m_sizeclass (MR st g))) g st) g k bail
          end) bail
      | None => free_group T dec (nontrivial_free dec f) st g k bail
      end
    else if Z.lor (m_freed (MR st g)) (m_avail (MR st g)) =? 0 then
      guard 51 (m_sizeclass (MR st g) <? 48) (
        if negb (optr_eqb (active st (m_sizeclass (MR st g))) (Some g))
        then queue (LActive (m_sizeclass (MR st g))) g st (fun st' => k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st') None) bail
        else k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None) bail
    else
      k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma data_same r r' i : data_of r' = data_of r ->
  sstart r' i = sstart r i /\ m_last_idx r' = m_last_idx r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
  /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r /\ m_mem r' = m_mem r.
Proof.
  intros D. pose proof (proj1 (data_of_eq r' r) D) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold sstart, gbase. rewrite (get_stride_data _ _ D), E1. repeat split; auto.
Qed.

Lemma head_of_eq_app (l1 l2 : list aptr) g : NoDup (l1 ++ g :: l2) -> head_of (l1 ++ g :: l2) = Some g -> l1 = [].
Proof.
  intros ND H. destruct l1 as [|a l1']; [reflexivity|]. cbn in H. inversion H. subst a. exfalso.
  cbn in ND. apply NoDup_cons in ND as [N _]. apply N. apply elem_of_list_In || apply list_elem_of_In. apply in_app_iff. right. left. reflexivity.
Qed.

Theorem ntf_all T : forall f, NTF_AT T f.
Proof.
  induction f as [|f IH]; intros dec1 dec2 D1 D2 X st L BL LS g bg i k bail INV Hgh Hi HP HF HO F1 F2; [lia|].
  destruct X as [idle zomb pend orph fresh]. cbn in HP, HF, HO. subst pend orph fresh.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof Hgh as [ai Hg].
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi. cbn [x_pend] in Pi.
  assert (NA : tbit (m_avail (MR st g)) i = false) by (destruct (tbit (m_avail (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
  assert (NB : tbit (m_freed (MR st g)) i = false) by (destruct (tbit (m_freed (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
  clear Pi.
  rewrite !ntf_unfold.
  set (mask := Z.lor (m_freed (MR st g)) (m_avail (MR st g))).
  assert (MN : 0 <= mask) by (apply Z.lor_nonneg; auto).
  assert (MI : Z.testbit mask i = false) by (unfold mask; rewrite Z.lor_spec; unfold tbit in NA, NB; rewrite NA, NB; reflexivity).
  assert (MADD : mask + bit i = Z.lor mask (bit i)) by (rewrite bit_eq; apply add_bit_lor; auto; lia).
  (* [comment removed for export] *)
  assert (NU : okay_to_free st g = false -> m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
  { intros OK Hsc. unfold okay_to_free in OK. fold (MR st g) in OK. rewrite (g_freeable _ _ _ _ _ _ GO) in OK. cbn [Z.eqb] in OK.
    destruct (Z.ltb_spec (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))); [| lia].
    rewrite Bool.orb_true_r in OK. discriminate. }
  destruct ((mask + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g) eqn:C1.
  - (* [comment removed for export] *)
    apply Bool.andb_true_iff in C1 as [CM COK]. apply Z.eqb_eq in CM.
    assert (ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i -> tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true).
    { intros j Hj NE. assert (T1 : Z.testbit (mask + bit i) j = true) by (rewrite CM, testbit_mask_upto by lia; apply Z.leb_le; lia).
      rewrite MADD, Z.lor_spec, testbit_bit in T1 by lia. destruct (Z.eqb_spec i j); [lia|]. rewrite Bool.orb_false_r in T1.
      unfold mask in T1. rewrite Z.lor_spec in T1. unfold tbit. destruct (Z.testbit (m_freed (MR st g)) j); [right; reflexivity|]. left. exact T1. }
    pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
    (* [comment removed for export] *)
    assert (FGT : forall st2 LS2,
      INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) st2 L BL LS2 ->
      s_groups st2 = s_groups st -> data_of (MR st2 g) = data_of (MR st g) -> m_next (MR st2 g) = None ->
      exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st2 g k bail = k st' mi /\
        free_group T dec2 (nontrivial_free dec2 f) st2 g k bail = k st' mi /\
        (s_regions st' = s_regions st2 /\ s_secret st' = s_secret st2) /\
        match mi with
        | None => INVL (mkX idle zomb None None None) st' L BL LS'
        | Some (base, len) => exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
            /\ len = round_up_pg (r_len r) /\ 0 < len /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
        end).
    { intros st2 LS2 INV2 HG2 DD2 NL2. destruct (data_same _ _ i DD2) as (Es & El & Ea & Ef & Esc & Eml & Emem).
      rewrite <- Es in INV2.
      apply (free_group_ok T f IH dec1 dec2 D1 D2 idle zomb st2 L BL LS2 g bg ai i k bail INV2).
      - rewrite HG2. exact Hg.
      - exact NL2.
      - rewrite El. exact Hi.
      - rewrite El, Ea, Ef. exact ALL.
      - rewrite Esc. exact F2. }
    destruct (m_next (MR st g)) as [nx|] eqn:NX.
    + (* [comment removed for export] *)
      assert (Lg : in_list LS g) by (apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
      destruct Lg as [h Hin]. destruct h as [sc|]; [| exfalso; exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
      destruct (il_active _ _ IL sc g Hin) as (Hsc & _ & Esc). rewrite Esc.
      rewrite !(guard_true 50) by (apply Z.ltb_lt; lia).
      destruct (in_split _ _ Hin) as (l1 & l2 & HL).
      pose proof (il_nodup _ _ IL (LActive sc)) as ND. rewrite HL in ND.
      assert (INV1 : INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) (dequeue (LActive sc) g st) L BL (fupd LS (LActive sc) (l1 ++ l2))).
      { apply (INVL_dequeue _ _ st L BL LS g (LActive sc) l1 l2 INV HL). left. exists sc. auto. }
      set (st1 := dequeue (LActive sc) g st) in *. set (LS1 := fupd LS (LActive sc) (l1 ++ l2)) in *.
      destruct (dequeue_frame (LActive sc) g st) as (RG1 & _ & _ & _ & G1 & _ & _ & SE1 & _). fold st1 in G1, RG1, SE1.
      pose proof (dequeue_data (LActive sc) g st) as DG1. fold st1 in DG1.
      assert (NL1 : m_next (MR st1 g) = None) by (unfold st1; rewrite dequeue_next, aptr_eqb_refl; reflexivity).
      assert (HD1 : active st1 sc = head_of (l1 ++ l2)).
      { pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV1)))) (LActive sc)) as H. unfold LS1 in H. rewrite fupd_eq in H. exact H. }
      destruct (optr_eqb (active st sc) (Some g)) eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1|].
      * (* [comment removed for export] *)
        destruct (optr_eqb_spec (active st sc) (Some g)) as [HD|]; [| discriminate].
        assert (El1 : l1 = []).
        { apply (head_of_eq_app l1 l2 g ND). rewrite <- HL. rewrite <- (il_head _ _ IL (LActive sc)). exact HD. }
        subst l1. cbn in HD1, HL, ND. destruct l2 as [|a' l2']; cbn in HD1; [discriminate|]. inversion HD1. subst a'.
        assert (Hain : In a (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
        assert (NEa : a <> g) by (intros ->; apply NoDup_cons in ND as [N _]; apply N; apply list_elem_of_In; left; reflexivity).
        destruct (il_active _ _ IL sc a Hain) as (_ & [ba [aia Ha]] & Esca).
        pose proof (g_rest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha) ltac:(discriminate) sc Hain ltac:(rewrite HL; cbn; congruence)) as [AZa FZa].
        pose proof (dequeue_data (LActive sc) g st a) as Da. fold st1 in Da.
        destruct (data_same _ _ 0 Da) as (_ & _ & Eaa & _ & Esa & _).
        assert (Ha1 : s_groups st1 !! ba = Some (mkGhdr (Some a) aia)) by (rewrite G1; exact Ha).
        assert (AV1 : m_avail (MR st1 a) = 0) by (rewrite Eaa; exact AZa).
        assert (HEAD1 : head_of (LS1 (LActive (m_sizeclass (MR st1 a)))) = Some a).
        { rewrite Esa, Esca. unfold LS1. rewrite fupd_eq. reflexivity. }
        rewrite !(activate_group_eq _ st1 L BL LS1 a ba aia INV1 Ha1 AV1).
        pose proof (INVL_activate _ st1 L BL LS1 a ba aia INV1 Ha1 AV1 HEAD1) as INV2.
        set (st2 := upd_meta a _ st1) in INV2 |- *.
        destruct (FGT st2 LS1 INV2) as (st' & mi & LS' & EQ & EQb & REG & POST).
        -- unfold st2. cbn. exact G1.
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact (DG1 g).
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact NL1.
        -- exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|].
           split; [destruct REG as [RA RB]; rewrite RA, RB; unfold st2; split; [etransitivity; [| exact RG1]; reflexivity| etransitivity; [| exact SE1]; reflexivity]| exact POST].
      * destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]| exact POST].
      * destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]| exact POST].
    + (* [comment removed for export] *)
      destruct (FGT st LS INVf eq_refl eq_refl NX) as (st' & mi & LS' & EQ & POST). exists st', mi, LS'. split; [exact EQ| exact POST].
  - (* [comment removed for export] *)
    assert (OKF : m_last_idx (MR st g) = 0 -> okay_to_free st g = false).
    { intros L0. rewrite L0 in C1. assert (i = 0) by lia. subst i.
      assert (mask = 0).
      { apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0. unfold mask. rewrite Z.lor_spec.
        destruct (Z.eq_dec j 0) as [->|NE]; [unfold tbit in NA, NB; rewrite NA, NB; reflexivity|].
        destruct (Z.testbit (m_freed (MR st g)) j) eqn:EF; [pose proof (M4 j Hj EF); lia|].
        destruct (Z.testbit (m_avail (MR st g)) j) eqn:EA; [pose proof (M3 j Hj EA); lia|]. reflexivity. }
      rewrite H in C1. cbn in C1. exact C1. }
    assert (C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
    { intros Hsc. destruct (Z.eq_dec (m_last_idx (MR st g)) 0) as [L0|L0]; [exact (NU (OKF L0) Hsc)|].
      unfold get_stride. destruct (Z.eqb_spec (m_last_idx (MR st g)) 0); [lia|]. cbn. lia. }
    destruct (Z.eqb_spec mask 0) as [MZ|MNZ].
    + (* [comment removed for export] *)
      assert (AZ : m_avail (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (FZ : m_freed (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (Hsc : 0 <= m_sizeclass (MR st g) < 48).
      { destruct (g_sc _ _ _ _ _ _ GO) as [[H _]|(E63 & L0 & _)]; [exact H|]. exfalso.
        rewrite (OKF L0) in NU. unfold okay_to_free in OKF. fold (MR st g) in OKF. rewrite (g_freeable _ _ _ _ _ _ GO), E63 in OKF.
        cbn in OKF. discriminate (OKF L0). }
      rewrite !(guard_true 51) by (apply Z.ltb_lt; lia).
      destruct (optr_eqb_spec (active st (m_sizeclass (MR st g))) (Some g)) as [HD|NHD]; cbn [negb].
      * (* [comment removed for export] *)
        eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|]. cbn.
        apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
        -- intros _ sc _ _. exact AZ.
        -- intros _ _. exists (LActive (m_sizeclass (MR st g))). apply (head_listed _ _ _ _ _ INV). exact HD.
        -- exact C3.
      * (* [comment removed for export] *)
        assert (NL : m_next (MR st g) = None).
        { destruct (m_next (MR st g)) as [nx|] eqn:NX; [| reflexivity]. exfalso.
          assert (Lg : in_list LS g) by (apply (proj1 (proj1 (il_link _ _ IL g))) || apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
          destruct Lg as [h Hin]. destruct h as [sc|]; [| exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
          destruct (il_active _ _ IL sc g Hin) as (_ & _ & Esc). subst sc.
          apply NHD. rewrite <- Esc at 1 || idtac.
          destruct (g_rest _ _ _ _ _ _ GO ltac:(discriminate) _ Hin) as [_ FNZ]; [| exact (FNZ FZ) || congruence].
          rewrite <- (il_head _ _ IL (LActive (m_sizeclass (MR st g)))). intros E. apply NHD. exact (eq_sym E) || (symmetry; exact E). }
        assert (NP : m_prev (MR st g) = None) by (exact (proj2 (il_link _ _ IL g) NL)).
        rewrite !(queue_eq (LActive (m_sizeclass (MR st g))) g st _ bail NL NP).
        pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
        pose proof (INVL_queue _ st L BL LS g (LActive (m_sizeclass (MR st g))) INVf NL (g_present _ _ _ _ _ _ GO)) as INVq.
        cbn [x_fresh x_idle x_zomb] in INVq. specialize (INVq ltac:(repeat split; auto; lia; fail)) || specialize (INVq (conj Hsc (conj (ex_intro _ bg Hgh) (conj eq_refl eq_refl)))).
        set (stq := queue_st (LActive (m_sizeclass (MR st g))) g st) in *.
        set (LSq := fupd LS (LActive (m_sizeclass (MR st g))) (LS (LActive (m_sizeclass (MR st g))) ++ [g])) in *.
        destruct (queue_frame (LActive (m_sizeclass (MR st g))) g st) as (RGq & _ & _ & _ & Gq & _ & _ & SEq & _). fold stq in Gq, RGq, SEq.
        pose proof (queue_data (LActive (m_sizeclass (MR st g))) g st g) as Dq. fold stq in Dq.
        destruct (data_same _ _ i Dq) as (Es & El & Ea & Ef & Esc & Eml & Emem).
        assert (INVa : INVL (mkX idle zomb None None (Some g)) (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) stq) L BL LSq).
        { apply (INVL_aor (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) stq L BL LSq g bg ai i INVq).
          - rewrite Gq. exact Hg.
          - rewrite El. exact Hi.
          - cbn. rewrite Es. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - rewrite Esc. unfold stq, MR. rewrite (get_stride_data _ _ Dq). exact C3. }
        eexists _, None, LSq. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; rewrite RGq, SEq; split; reflexivity|]. cbn.
        apply (INVL_clear_fresh _ _ L BL LSq g INVa eq_refl).
        intros b ai' Hb. unfold MR. rewrite get_meta_rec_upd_same. cbn [m_last_idx m_sizeclass m_avail m_freed m_set_freed]. fold (MR stq g). rewrite El, Esc, Ea, Ef.
        assert (ING : In g (LSq (LActive (m_sizeclass (MR st g))))) by (unfold LSq; rewrite fupd_eq; apply in_app_iff; right; left; reflexivity).
        split; [intros _; exact ING|]. split; [intros _ NI; exfalso; apply NI; eexists; exact ING|].
        split; [intros sc _ _; split; [exact AZ|]; rewrite FZ, Z.lor_0_l; unfold bit; pose proof (Z.pow_pos_nonneg 2 i); lia|].
        intros Hsc' LT. exfalso. pose proof (C3 Hsc') as GE.
        replace (get_stride (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) (MR stq g))) with (get_stride (MR stq g)) in LT by (destruct (MR stq g); reflexivity).
        rewrite (get_stride_data _ _ Dq) in LT. lia.
    + (* [comment removed for export] *)
      eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|]. cbn.
      apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
      * intros _ sc Hin Hnh. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
      * intros _ Hsc. destruct (m_next (MR st g)) as [nx|] eqn:NX.
        -- apply (proj2 (proj1 (il_link _ _ IL g))). rewrite NX. discriminate.
        -- exfalso. destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc (fun H => lists_notin st LS (old_lists _ _ _ _ _ INV) g NX _ (proj2 (In_nth _ _ g H) ))) || idtac.
           assert (NIL : ~ in_list LS g) by (intros [h Hin]; exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NX h Hin)).
           destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NIL) as [A0 F0]. apply MNZ. unfold mask. rewrite A0, F0. reflexivity.
      * exact C3.
Qed.

Theorem ntf_spec : NTF_SPEC.
Proof.
  intros T f X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2.
  destruct (ntf_all T f dec_hdr dec_hdr (dec_hdr_ok T) (dec_hdr_ok T) X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2) as (st' & mi & LS' & EQ & _ & _ & POST).
  exists st', mi, LS'. split; [exact EQ| exact POST].
Qed.

(* [comment removed for export] *)
Theorem ntf_slots_agree T f X st L BL LS g bg i (k : mstate -> mapinfo -> M T) bail :
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  nontrivial_free dec_slots f st g i k bail = nontrivial_free dec_hdr f st g i k bail.
Proof.
  intros INV Hg Hi HP HF HO F1 F2.
  destruct (ntf_all T f dec_hdr dec_slots (dec_hdr_ok T) (dec_slots_ok T) X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2) as (st' & mi & LS' & EQ1 & EQ2 & _).
  rewrite EQ1, EQ2. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem ntf_spec2 T f : NTF_AT T f.
Proof. apply ntf_all. Qed.

(* [comment removed for export] *)
Theorem free_INVL_closed st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  ftree L (free st (Some (aadd c (UNIT * off))))
        (fun L' st' => exists LS', INVL x0 st' L' (bl_remove c BL) LS').
Proof. exact (free_INVL ntf_spec st L BL LS c off n). Qed.
