(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (fin_okQ, try_avail_okQ)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 MI_WTry MI_WTry2 LB_Tables LB_Inv LB_Sum LB_Bound LB_WNtf.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_WTry () := "C47Corelib7Classes?RelationClasses9ReflexiveI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec8MI_WFree:guard_trueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WNtfAactivate_group_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC45stdpp>list_relations4list9NoDup_nilC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4base6ElemOfC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6lookupC35stdpp4base6InsertI35stdpp4base<list_elem_of00C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8MI_WTry28TA_frame00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec7LB_WNtf3FFR00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry28hd_factsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec8MI_WTry27TA_POSTC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry27hd_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WTry9ta_fin_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec8MI_WTry2<taf_upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry29taf_transC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MI_KitFget_meta_rec_upd_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry2?set_avail_viewsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9g_presentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf4geomC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf<FFR_upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf9FFR_transC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbK59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec8MI_WTry25GOODHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry25hd_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf?FFR_dequeue_INVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry2Ddequeue_exhausted_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec6MI_Inv8il_nodupC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list:NoDup_consK35stdpp4base<list_elem_of01C59OSSVerify5KrLib4Spec7MI_List<dequeue_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List7data_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf9data_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry2;taf_dequeueC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec8MI_WTry27hd_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry29rotate_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry2>taf_set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf<FFR_set_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_aiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry2Iland_mask_upto_zero_aboveC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9bits_inj'C59OSSVerify5KrLib4Spec6MI_Kit=optr_eqb_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WTry<span_loop_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib4Spec7MI_WTry;INVL_set_aiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8MI_WTry28TA_frame01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityC47Corelib4Init5Logic3iffC59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec7LB_WNtf3FFR01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib4Spec8MI_ArithAtestbit_mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_specC59OSSVerify5KrLib4Spec6MI_Inv9il_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv=ig_onepartialC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib4Spec8MI_WTry2Bland_mask_upto_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_WNtf=INVL_activateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3BINVL_decay_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WTry29taf_decayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc?set_bounces_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf7FFR_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_WNtf8FFR_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_WTry7fin_okQC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib4Spec8MI_WTry28taf_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base7elem_ofC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic4True00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveI59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section TRYQ.
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

(* [comment removed for export] *)
Lemma fin_okQ st0 st LS m (mask : Z) :
  INVL X st L BL LS -> TA_frame st0 st sc -> FFR st0 st -> active st sc = Some m -> m_avail (MR st m) = mask -> mask <> 0 ->
  exists st1 first LS1, ta_fin st m mask k = k st1 first /\ TA_POST X L BL sc st0 st1 first LS1 /\ FFR st0 st1.
Proof.
  intros INV TF FF HA AM MNZ. destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4).
  rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|].
  split; [| eapply FFR_trans; [exact FF| apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr]]].
  split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
  right. exists m, bm, ai, (ctz32 (lowbit mask)).
  assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
  assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
  rewrite MRm. destruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
  split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.

Theorem try_avail_okQ st LS :
  INVL X st L BL LS ->
  exists st1 first LS1, try_avail sc st k bail = k st1 first /\ TA_POST X L BL sc st st1 first LS1 /\ FFR st st1.
Proof.
  intros INV. unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ eexists _, _, LS. split; [reflexivity|]. split; [split; [apply taf_refl| left; auto]| apply FFR_refl]. }
  fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ exact (fin_okQ st st LS m _ INV (taf_refl st sc) (FFR_refl st) HA eq_refl ANZ). }
  (* [comment removed for export] *)
  assert (STEP1 : exists st1 m1 LS1,
    (if m_freed (MR st m) =? 0
     then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
     else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
    /\ GOODH X st1 L BL LS1 sc m1 /\ (TA_frame st st1 sc /\ FFR st st1)
    \/ (m_freed (MR st m) = 0 /\ active (dequeue (LActive sc) m st) sc = None /\ exists LS1, INVL X (dequeue (LActive sc) m st) L BL LS1)).
  { pose proof (hd_facts X st L BL LS sc m INV HA) as (_ & _ & bm0 & ai0 & Hbm0).
    pose proof (FFR_dequeue_INV X st L BL LS m bm0 sc INV (ex_intro _ ai0 Hbm0) (hd_in X st L BL LS sc m INV HA)) as FD.
    destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
    - destruct (dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ) as (LS1 & rest & INV1 & HL & HA1 & NXT).
      rewrite HA1. destruct rest as [|m1 rest']; cbn.
      + exists st, m, LS. right. split; [exact FZ|]. split; [first [reflexivity| rewrite HA1; reflexivity]| exists LS1; exact INV1].
      + exists (dequeue (LActive sc) m st), m1, LS1. left. split; [reflexivity|]. split; [| split; [apply taf_dequeue| exact FD]].
        destruct (NXT m1 eq_refl) as [A1 F1].
        assert (NE : m1 <> m).
        { intros ->. pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left. }
        pose proof (dequeue_data (LActive sc) m st m1) as D. destruct (data_same _ _ 0 D) as (_ & _ & Ea & Ef & _).
        split; [exact INV1|]. split; [first [reflexivity| rewrite HA1; reflexivity]|]. rewrite Ea, Ef. auto.
    - destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st LS m mn (conj INV (conj HA (conj AZ FNZ))) Hn) as [LS1 G1].
      exists (set_active sc (Some mn) st), mn, LS1. left. split; [reflexivity|]. split; [exact G1| split; [apply taf_set_active| apply (FFR_set_head st (LActive sc))]]. }
  destruct STEP1 as (st1 & m1 & LS1 & [(E1 & G1 & [TF1 FF1])|(FZ & HA1 & LS1' & INV1)]).
  2:{ rewrite (proj2 (Z.eqb_eq _ _) FZ), HA1. eexists _, 0, LS1'. split; [reflexivity|]. split; [split; [apply taf_dequeue| left; auto]|].
      pose proof (hd_facts X st L BL LS sc m INV HA) as (_ & _ & bm0 & ai0 & Hbm0).
      exact (FFR_dequeue_INV X st L BL LS m bm0 sc INV (ex_intro _ ai0 Hbm0) (hd_in X st L BL LS sc m INV HA)). }
  rewrite E1. clear E1.
  (* [comment removed for export] *)
  assert (STEP2 : exists st2 m2 LS2,
    (let mr := get_meta_rec st1 m1 in
     if (m_freed (MR st1 m1) =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0)
     then match m_next mr with Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn)) | None => (st1, m1, m_freed (MR st1 m1)) end
     else (st1, m1, m_freed (MR st1 m1))) = (st2, m2, m_freed (MR st2 m2))
    /\ GOODH X st2 L BL LS2 sc m2 /\ (TA_frame st st2 sc /\ FFR st st2)).
  { cbn zeta. fold (MR st1 m1). destruct (_ && _).
    - pose proof G1 as (INV1 & HA1 & _). destruct (hd_next X st1 L BL LS1 sc m1 INV1 HA1) as (mn & Hn & _). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st1 LS1 m1 mn G1 Hn) as [LS2 G2].
      exists (set_active sc (Some mn) st1), mn, LS2. split; [reflexivity|]. split; [exact G2| split; [eapply taf_trans; [exact TF1| apply taf_set_active]| eapply FFR_trans; [exact FF1| apply (FFR_set_head st1 (LActive sc))]]].
    - exists st1, m1, LS1. auto. }
  destruct STEP2 as (st2 & m2 & LS2 & E2 & G2 & [TF2 FF2]). cbn zeta in E2. fold (MR st1 m1) in E2 |- *.
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
    /\ GOODH X st3 L BL LS3 sc m3 /\ (TA_frame st st3 sc /\ FFR st st3)
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
        split.
        { split; [eapply taf_trans; [exact TF2| constructor; auto; try (intros h _; destruct h; reflexivity)]|].
          eapply FFR_trans; [exact FF2|]. unfold st3. constructor; cbn; auto; try tauto.
          intros bb h' Hbb. destruct (aptr_eq_dec bb b2) as [->|NE]; [rewrite lookup_insert_eq in Hbb; inversion Hbb; subst; eexists; split; [exact Hb2| reflexivity]|].
          rewrite lookup_insert_ne in Hbb by congruence. exists h'. auto. }
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
        split; [split; [eapply taf_trans; [exact TF2| apply taf_set_active]| eapply FFR_trans; [exact FF2| apply (FFR_set_head st2 (LActive sc))]]|]. split; [exact Hb3|].
        change (MR (set_active sc (Some mn) st2) mn) with (MR st2 mn).
        pose proof (g_masks _ _ _ _ _ _ GO3) as (V1 & V2 & V3 & V4 & V5 & V6).
        pose proof (g_ai _ _ _ _ _ _ GO3) as AI3.
        rewrite (land_mask_upto_all (m_freed (MR st2 mn)) ai3 V2 ltac:(clear -AI3; lia) ltac:(rewrite FULL; exact V4)).
        destruct G3 as (_ & _ & _ & F3). exact F3.
    - exists st2, m2, LS2, b2, ai2. split; [reflexivity|]. split; [split; [exact INV2| auto]|]. auto. }
  destruct STEP3 as (st3 & m3 & LS3 & b3 & ai3 & E3 & G3 & [TF3 FF3] & Hb3 & ACT).
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
  destruct (fin_okQ st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5) as (st6 & first & LS6 & E6 & POST).
  - eapply taf_trans; [exact TF3|]. eapply taf_trans; [apply taf_upd_meta| apply taf_decay].
  - eapply FFR_trans; [exact FF3|]. apply (FFR_trans st3 st4 st5).
    + unfold st4. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV3))))) _ _ _ Hb3))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr].
    + unfold st5, decay_bounces. destruct (sc_in_seq_range _ && _); [apply FFR_ctx; reflexivity| apply FFR_refl].
  - exact HA5.
  - rewrite MR5. reflexivity.
  - exact ACT.
  - exists st6, first, LS6. split; [exact E6| exact POST].
Qed.
End TRYQ.
