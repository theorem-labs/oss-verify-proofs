(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (24 recorded proofs replaced by written proofs (GP_trans, GP_eq, GP_amf and 21 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WSlot () := "C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC47Corelib4Init9Datatypes3appC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2IDC35stdpp4gmapBgmap_dep_ne_lookupC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps9insert_idI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap8gmap_key00I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC35stdpp4gmapBgmap_partial_alterI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9MI_WAMeta8AM_frame00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta;amf_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WAMeta8amf_ssecC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8MI_WTry28TA_frame00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry2;taf_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry28taf_ssecC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot5GP_eqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot6geo_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C47Corelib4Init9Datatypes3sndI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4Spec8MI_WSlot9geo_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF29geom_keptC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres35xidleC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres27inv_R_XC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres27inv_G_XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree27inv_S_XC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib4Spec8MI_WSlot4X_asC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec6MI_Inv7im_idleC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C35stdpp4base6insertC59OSSVerify5KrLib4Spec;MI_WCreate2<set_metas_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot8fi_metasC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib4Spec8MI_WSlot=INVL_idle_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List8queue_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec7MI_List7data_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4:INVL_queueC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec7MI_List4fupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4;queue_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8MI_Pres4=ctx_but_heads00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec7MI_List:queue_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres48cb_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres45cb_mcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4:cb_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres46cb_seqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<lhead_eq_decC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot6fi_putC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6MI_Inv7il_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC59OSSVerify5KrLib4Spec8MI_ArithAtestbit_mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1ZAsub_nocarry_ldiffK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05c59OSSVerify5KrLib4Spec8MI_WSlot>mask_upto_predC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt=created_masksC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib4Spec8MI_WSlot>testbit_avail'C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WCreate26one5_EC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WCreate?one5_iff_createC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_gt_casesI35stdpp4gmap8gmap_dep00C35stdpp9countable6encodeC59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC59OSSVerify5KrLib4Spec7MI_Geom9sstart_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib4Spec;MI_WCreate26one5_AC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib4Spec;MI_WCreate26one5_BC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres1@INVL_mask_changeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot9fin_hostsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot6st3_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitFget_meta_rec_upd_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List8queue_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot7fin_MR3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitAget_head_upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@s_metas_upd_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot8fin_INV3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List7fupd_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot9fin_emptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:queue_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:data_of_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot=fin_MR3_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot7fin_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres4@INVL_clear_freshC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot=geom_kept_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF28TF2_keptC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot8fin_INV4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot<fin_queue_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot7fin_LS4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot7fin_MR4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WSlot9fin_head3C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition X_as (idle : list aptr) : extras := mkX idle [] None None None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GP (st st' : mstate) : Prop :=
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r)
  /\ s_secret st' = s_secret st.
Lemma GP_refl st : GP st st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WSlot ()) [] "h01rh13ridh22sth31Hh42_Hp;1p;4p;6p;2p;3p-1R0g0000R1p4p710R2p8P0P1p4p7210R0p8p1000Dp4p70R3p10019p4p710p8P3p1001Pp4p710R4p8P3p1001lp4p710R5p8P3p1002Jp4p7210R6p8P3p1002gp4p710R7p8P3p1003ER8p4p710R9p8P3P8p4p7210R8p8P3p1003bp4p710R:p8P3p1004@R;p4p710R<p8P3P;p4p7210R;p8P3p1004Yp4p710p8P3g0056R=p4p710p8P3p1005OR>p4p710p8P3p1005gp4p710p8P3p1006>p4p710p8P3p1006Up4p710p8P3p1006mR?p4p710p8P3p1007DR@p4p710p8P3p1007`p4p710p8P3p10089p4p73110RAp8P3P2p8p1008Kp4p70R3P4p8P3P5p8P3P6p8P3P9p8P3P8p8P3P:p8P3p1009@p5p710p8P3p1009\p4p710p8P3P=p4p741110R8p8P3P0p8P3P1p4p73110R0p8P3p100:<p4p7<111111111110R9p8P3p100:^p4p7<111111111110p8P7P<p8P7P;p8p100;9R3p4p73101R6p100;SR5p4p73110p8P6p100;lR4p4p73110p8P6p100<Hp4p710p8P6p100<[RBp4p7201p8P6p100<mp4p7201p8P6P0p8P6p100=?R0p4p73110p8P6p100=SRCp4p73110p8P6p100=mp4p7201p8P3p4p710R6P5p4p710p8P6P4p4p710p8P6P<p8P6P;p8P6P2p8P6P0p4p710p8P6PCp4p710p8p100>@p4p710RCP7p8PCP<p8PCP;p8PCPAp8g00>XRCp4p710R6P7p8P6P<p8P6P;p8P6PAp8PCp4p741110RAP@p4p73101p8p100>lp4p70p100?ap4p7210p8P9P:p8P8P3p4p7511100R:p8P:P8p8P>p4p741110R>P3p4p76111100R8p8P8P>p8p100@=p4p741110R>P3p4p771111100R8p8P8P>p8P?p4p741110R?P3p4p7:1111111100R3p8P3P?p8PBp4p7200RBPAp8PAPBp8g00@]j1:TPCj49TP=j48Tg00A?j12TP1j63Tg00B9j21Tg00B[j30Tg00C5j17Tg00Clj15Tg00Dej26Tg00E?j44Tg00EZR1g00FSR=g00G1RC%:CRBP=PCP=g00GjRAg00HCR?PCC9R3P=PAP?PCC8R?f1RAf2R>#2E3f0R8,1C30R:g00Ha%7Ag00IY30R9P=PCP3P?f3f4#2E311C>50B[[]0]1g00JQRB%58R>;0>PAX49X3:X0CX1=16B>C4X21P8O1W2o"). Qed.
Lemma GP_trans a b c : GP a b -> GP b c -> GP a c.
Proof. intros [H1 S1] [H2 S2]. split; [intros rid r H K; exact (H2 rid r (H1 rid r H K) K)| congruence]. Qed.
Lemma GP_eq st st' : s_regions st' = s_regions st -> s_secret st' = s_secret st -> GP st st'.
Proof. intros E S. split; [intros rid r H _; rewrite E; exact H| exact S]. Qed.
Lemma GP_amf st st' : AM_frame st st' -> GP st st'.
Proof. intros AF. split; [exact (amf_regions _ _ AF)| exact (amf_ssec _ _ AF)]. Qed.
Lemma GP_taf st st' sc : TA_frame st st' sc -> GP st st'.
Proof. intros TF. apply GP_eq; [exact (taf_regions _ _ _ TF)| exact (taf_ssec _ _ _ TF)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition geo_of (r : meta) : (optr * Z * Z * Z)%type := (m_mem r, m_last_idx r, m_maplen r, m_sizeclass r).

Lemma geo_facts r r' : geo_of r' = geo_of r ->
  (forall i, sstart r' i = sstart r i) /\ cnt_of r' = cnt_of r /\ m_maplen r' = m_maplen r /\ get_stride r' = get_stride r.
Proof.
  unfold geo_of. intros H. injection H. intros E1 E2 E3 E4.
  assert (ES : get_stride r' = get_stride r) by (unfold get_stride; rewrite E2, E3, E1; reflexivity).
  unfold sstart, cnt_of, gbase. rewrite ES, E4, E3, E2. auto.
Qed.

Lemma geom_kept_geo st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall x, geo_of (MR st' x) = geo_of (MR st x)) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  destruct (geo_facts _ _ (HM m)) as (A & B & C & _). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_idle_sub X idle' st L BL LS :
  (forall x, In x idle' -> In x (x_idle X)) -> INVL X st L BL LS -> INVL (xidle X idle') st L BL LS.
Proof.
  intros SUB (IR & IA & IM & IL & IG & IS & ISH).
  split; [exact (inv_R_X X (xidle X idle') st L eq_refl IR)|]. split; [exact IA|].
  split.
  { destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn; auto. }
  split; [exact IL|]. split; [exact (inv_G_X X (xidle X idle') st LS eq_refl eq_refl IG)|]. split; [exact (inv_S_X X (xidle X idle') st BL eq_refl IS)| exact ISH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FREE_IDLE.
Variables (idle : list aptr) (m : aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL (X_as (m :: idle)) st L BL LS.
Hypothesis NIm : ~ In m idle.
Let st' := fm_st st m.
Let LS' := fupd LS LFree (LS LFree ++ [m]).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma fi_metas : s_metas st !! m = Some meta0.
Proof. exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). Qed.
Lemma fi_put : put_meta m meta0 st = st.
Proof. unfold put_meta. apply set_metas_id. apply insert_id. exact fi_metas. Qed.

Lemma free_idle_ok :
  INVL (X_as idle) st' L BL LS'
  /\ s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_regions st' = s_regions st /\ s_next_rid st' = s_next_rid st
  /\ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st).
Proof.
  pose proof (INVL_idle_sub (X_as (m :: idle)) idle st L BL LS ltac:(intros x Hx; right; exact Hx) INV) as INV1.
  assert (MRm : MR st m = meta0) by (unfold MR, get_meta_rec; rewrite fi_metas; reflexivity).
  unfold st', fm_st. rewrite fi_put.
  pose proof (INVL_queue (xidle (X_as (m :: idle)) idle) st L BL LS m LFree INV1 ltac:(rewrite MRm; reflexivity)
                ltac:(rewrite fi_metas; discriminate) ltac:(cbn; rewrite MRm; split; [reflexivity| tauto])) as INV2.
  destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
  split; [exact INV2|]. split; [exact F2|]. split; [exact F7|]. split; [exact F5|]. split; [exact F6|]. split; [exact F1|]. split; [exact F3|].
  split; [intros sc; change (active ?s sc) with (get_head s (LActive sc)); rewrite queue_head; destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]|].
  split; [intros sc; unfold usage, ctx; rewrite (cb_usage _ _ FC); reflexivity|].
  split; [exact (cb_mc _ _ FC)|]. split; [exact (cb_bounces _ _ FC)| exact (cb_seq _ _ FC)].
Qed.
End FREE_IDLE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FINISH.
Variables (T : Type) (idle : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m b : aptr) (ai last sc ml : Z) (k : mstate -> M T) (bail : M T).
Let X2 := mkX idle [] None None (Some m).
Hypothesis INV : INVL X2 st2 L BL LS.
Hypothesis Hb : s_groups st2 !! b = Some (mkGhdr (Some m) ai).
Hypothesis Em : MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml.
Hypothesis Hai : 0 <= ai <= last.
Hypothesis Hl : last <= 31.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis HA : active st2 sc = None.
Hypothesis UND : get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0.
Hypothesis TF : TF2 st2.

Let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2.
Let st4 := queue_st (LActive sc) m st3.
Let LS4 := fupd LS (LActive sc) (LS (LActive sc) ++ [m]).
Let s0 : aptr := (fst b, sstart (MR st2 m) 0).

Lemma fin_hosts : hosts st2 b m.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WSlot ()) ["FINISH"] "h02aip;1p;4p;6p;2p;3g00@]j1:Tg00eQj49Tg00eoj62Tg00>Xj41Tg0056j48Tg00fPj14Tg0000j63Tg00B9j20Tg00i2j25Tg00B[j36Tg00iij47Tg00JQR0g00l9R1#:g000DR2P1P2g00FSR3g00GjR4P0g00m0R5C9R6P3P4g00HCP0P5g00mIE2R5P1C1P2P6P5P1C8p,1bp,3st2#4E3p,1m,02f0'5,0136X00p,2aip,2HbC7o"). Qed.
Lemma fin_empty : LS (LActive sc) = [].
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma mask_upto_pred a : 0 <= a -> mask_upto a - 1 = Z.ldiff (mask_upto a) 1.
Proof.
  intros Ha. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (Z.testbit 1 i) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma testbit_avail' i : 0 <= i -> Z.testbit (mask_upto ai - 1) i = ((1 <=? i) && (i <=? ai)).
Proof.
  intros Hi. rewrite mask_upto_pred by lia. rewrite Z.ldiff_spec, testbit_mask_upto by lia.
  change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.leb_spec i ai); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.

Lemma st3_eq : st3 = upd_meta m (fun r => m_set_avail (mask_upto ai - 1) (m_set_freed (mask_upto last - mask_upto ai) r)) st2.
Proof.
  unfold st3, upd_meta. f_equal. fold (MR st2 m). rewrite Em. reflexivity.
Qed.

Lemma fin_INV3 : INVL (mkX idle [] (Some s0) None (Some m)) st3 L BL LS.
Proof.
  rewrite st3_eq.
  pose proof (created_masks ai last Hai Hl) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Elast : m_last_idx (MR st2 m) = last) by (rewrite Em; reflexivity).
  apply (INVL_mask_change X2 st2 L BL LS m b ai (mask_upto ai - 1) (mask_upto last - mask_upto ai) (Some s0) INV Hb).
  - rewrite Elast. unfold tbit. split; [unfold mask_upto; assert (P2 : 2 ^ 1 <= 2 ^ (ai + 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 1) with 2 in P2; lia|].
    split; [exact M2|]. split; [intros i Hi Hb'; rewrite testbit_avail' in Hb' by lia; apply andb_true_iff in Hb' as [_ Hb']; apply Z.leb_le in Hb'; exact Hb'|].
    split; [exact M4|]. split; [| exact M6].
    intros i Hi Ha Hf. rewrite testbit_avail' in Ha by lia. apply andb_true_iff in Ha as [_ Ha]. apply Z.leb_le in Ha. exact (M5 i Hi (M7 i ltac:(lia)) Hf).
  - rewrite Elast. intros i Hi. cbn zeta. unfold tbit.
    pose proof (is_part _ _ _ IS _ _ _ i Hb ltac:(rewrite Elast; exact Hi)) as P5. cbn zeta in P5. rewrite Em in P5. cbn [m_avail m_freed x_pend X2] in P5.
    rewrite <- Em in P5.
    destruct P5 as (_ & _ & nAC & nAD & _ & nBC & nBD & _ & _ & _ & _).
    rewrite testbit_avail' by lia.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + assert (A0 : Z.testbit (mask_upto ai) 0 = true) by (apply M7; lia).
      apply one5_iff_create; [apply one5_E| intros C; exact (nAC (conj A0 C))| intros D; exact (nAD (conj A0 D))].
      * cbn. discriminate.
      * intros F. exact (M5 0 ltac:(lia) A0 F).
      * unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
    + destruct (Z.le_gt_cases i ai) as [Hle|Hgt].
      * assert (A : Z.testbit (mask_upto ai) i = true) by (apply M7; lia).
        apply one5_iff_create; [apply one5_A| intros C; exact (nAC (conj A C))| intros D; exact (nAD (conj A D))].
        -- replace (1 <=? i) with true by (symmetry; apply Z.leb_le; lia). replace (i <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- intros F. exact (M5 i ltac:(lia) A F).
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
      * assert (F : Z.testbit (mask_upto last - mask_upto ai) i = true) by (apply M6; lia).
        apply one5_iff_create; [apply one5_B| intros C; exact (nBC (conj F C))| intros D; exact (nBD (conj F D))].
        -- replace (i <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. discriminate.
        -- exact F.
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
  - right. split; [intros s Hs; discriminate|]. intros s Hs. inversion Hs. exists 0. rewrite Elast. split; [lia|].
    rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
Qed.

Lemma fin_MR3 : MR st3 m = mkMeta None None (Some b) (mask_upto ai - 1) (mask_upto last - mask_upto ai) last 1 sc ml.
Proof. unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 m). rewrite Em. reflexivity. Qed.
Lemma fin_MR3_other x : x <> m -> MR st3 x = MR st2 x.
Proof. intros NE. unfold st3, MR. apply get_meta_rec_upd_other. exact NE. Qed.

Lemma fin_queue_eq : queue (LActive sc) m st3 k bail = k st4.
Proof. apply queue_eq; fold (MR st3 m); rewrite fin_MR3; reflexivity. Qed.

Lemma fin_head3 : get_head st3 (LActive sc) = None.
Proof. unfold st3. rewrite get_head_upd_meta. cbn. exact HA. Qed.

Lemma fin_INV4 : INVL (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4.
Proof.
  apply (INVL_queue (mkX idle [] (Some s0) None (Some m)) st3 L BL LS m (LActive sc) fin_INV3).
  - rewrite fin_MR3. reflexivity.
  - unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
  - cbn. split; [exact Hsc|]. split; [exists b; exists ai; exact Hb|]. split; [rewrite fin_MR3; reflexivity| reflexivity].
Qed.

Lemma fin_LS4 : LS4 (LActive sc) = [m].
Proof. unfold LS4. rewrite fupd_eq, fin_empty. reflexivity. Qed.

Lemma fin_MR4 : geo_of (MR st4 m) = geo_of (MR st3 m) /\ m_avail (MR st4 m) = m_avail (MR st3 m) /\ m_freed (MR st4 m) = m_freed (MR st3 m).
Proof.
  pose proof (queue_data (LActive sc) m st3 m) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  unfold geo_of. fold st4 in D1, D2, D3, D4, D5, D6, D7. rewrite D1, D4, D7, D6, D2, D3. auto.
Qed.

Lemma fin_geo x : geo_of (MR st4 x) = geo_of (MR st2 x).
Proof.
  pose proof (queue_data (LActive sc) m st3 x) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  fold st4 in D1, D2, D3, D4, D5, D6, D7. unfold geo_of. rewrite D1, D4, D6, D7.
  destruct (aptr_eq_dec x m) as [->|NE].
  - rewrite fin_MR3, Em. reflexivity.
  - rewrite (fin_MR3_other x NE). reflexivity.
Qed.

Theorem slot_finish_ok :
  exists LS',
    queue (LActive sc) m st3 k bail = k st4
    /\ INVL (xpend (X_as idle) (Some s0)) st4 L BL LS'
    /\ TF2 st4
    /\ active st4 sc = Some m /\ (forall sc', sc' <> sc -> active st4 sc' = active st2 sc')
    /\ s_groups st4 = s_groups st2 /\ s_tick st4 = s_tick st2 /\ s_shadow st4 = s_shadow st2
    /\ m_last_idx (MR st4 m) = last /\ m_sizeclass (MR st4 m) = sc /\ get_stride (MR st4 m) = get_stride (MR st2 m)
    /\ (forall i, sstart (MR st4 m) i = sstart (MR st2 m) i) /\ s_regions st4 = s_regions st2 /\ s_secret st4 = s_secret st2.
Proof.
  exists LS4. destruct (queue_frame (LActive sc) m st3) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC). fold st4 in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, FC.
  pose proof fin_INV4 as INV4.
  assert (G4 : s_groups st4 = s_groups st2) by (rewrite F5; reflexivity).
  destruct (geo_facts _ _ (fin_geo m)) as (S1 & S2 & S3 & S4).
  split; [exact fin_queue_eq|].
  split.
  { (* [comment removed for export] *)
    apply (INVL_clear_fresh (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4 m INV4 eq_refl).
    intros b' ai' Hb'. rewrite G4 in Hb'.
    assert (Eb : b' = b /\ ai' = ai).
    { pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ fin_hosts (ex_intro _ ai' Hb')) as <-. rewrite Hb in Hb'. inversion Hb'. auto. }
    destruct Eb as [-> ->].
    assert (Esc : m_sizeclass (MR st4 m) = sc) by (pose proof (fin_geo m) as G; unfold geo_of in G; rewrite Em in G; injection G; intros; congruence).
    rewrite Esc. split; [| split; [| split]].
    - intros _. rewrite fin_LS4. left. reflexivity.
    - intros _ NI. exfalso. apply NI. exists (LActive sc). rewrite fin_LS4. left. reflexivity.
    - intros sc0 Hin Hh. exfalso.
      pose proof (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV4)))) (LActive sc0) (LActive sc) m Hin ltac:(rewrite fin_LS4; left; reflexivity)) as E.
      inversion E. subst sc0. rewrite fin_LS4 in Hh. apply Hh. reflexivity.
    - intros _ HU. destruct fin_MR4 as (_ & EA & EF). rewrite EA, EF, fin_MR3. cbn. rewrite S4 in HU.
      destruct (UND HU) as [-> ->]. cbn. split; reflexivity. }
  split.
  { apply (TF2_kept st2 st4); [rewrite F2; reflexivity| rewrite F7; reflexivity| | exact TF].
    apply geom_kept_geo; [intros bb h Hh; rewrite G4; exact Hh| apply fin_geo]. }
  split; [change (active st4 sc) with (get_head st4 (LActive sc)); unfold st4; rewrite queue_head; destruct (decide (LActive sc = LActive sc)); [rewrite fin_head3; reflexivity| congruence]|].
  split; [intros sc' NE; change (active st4 sc') with (get_head st4 (LActive sc')); change (active st2 sc') with (get_head st2 (LActive sc')); unfold st4; rewrite queue_head; destruct (decide (LActive sc' = LActive sc)); [congruence|]; unfold st3; rewrite get_head_upd_meta; reflexivity|].
  split; [exact G4|]. split; [rewrite F7; reflexivity|]. split; [rewrite F2; reflexivity|].
  pose proof (fin_geo m) as G. unfold geo_of in G. rewrite Em in G. injection G. intros E4 E3 E2 E1.
  split; [exact E2|]. split; [exact E4|]. split; [exact S4|]. split; [exact S1|]. split; [rewrite F1; reflexivity| rewrite F8; reflexivity].
Qed.
End FINISH.
