(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (17 recorded proofs replaced by written proofs (INVL_ctx_scalars, ctx_scalars_refl, ia_ctx_facts and 14 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Pres3 () := "C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3sndC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib4Spec7MI_List=In_removelastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List5In_tlC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC46Stdlib5Lists4List6nth_okC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC46Stdlib5Lists4List:map_ext_inC35stdpp4base?list_elem_of_InC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_transC35stdpp4base5emptyC35stdpp8fin_mapsCelem_of_map_to_listC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_extC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap9gmap_foldI59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4Spec8MI_Pres3>ctx_scalars_eq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transK59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes2idK59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext29inv_M_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext29inv_L_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext2<group_ok_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext29inv_S_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext;inv_SH_viewC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulC35stdpp8fin_maps;map_to_listC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4Spec8MI_Pres3>ctx_scalars_eq01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6ia_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib4Spec8MI_Pres3<ia_ctx_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp8fin_maps<lookup_emptyC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib4Spec8MI_Pres3@INVL_ctx_scalarsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6Malloc:record_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C57Corelib7BinNums6IntDef1Z3subC47Corelib4Init5Logic6eq_symC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?set_bounces_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbc59OSSVerify5KrLib4Spec8MI_Pres3=bounces_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib4Spec8MI_Pres3?INVL_set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6removeC46Stdlib5Lists4List9in_removeC46Stdlib5Lists4List<in_in_removec59OSSVerify5KrLib4Spec8MI_Pres33remC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~I35stdpp4base<list_elem_of00C35stdpp4base7elem_ofC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6MI_Kit@get_meta_rec_putC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit<aptr_eqb_neqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres34uz_RC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7im_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6im_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres3:uz_R_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres3>present_of_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@lookup_metas_putC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres27inv_R_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres3?gcnt_ext_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib4Spec8MI_Pres36in_remC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:removelastC46Stdlib5Lists4List:in_app_iffC47Corelib4Init5Logic6or_indC46Stdlib5Lists4List2tlC59OSSVerify5KrLib4Spec7MI_List:linked_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_reflC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6inv_SH01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ctx_scalars_eq (c c' : mctx) : Prop := mkCS {
  cs_secret : c_secret c' = c_secret c;
  cs_init : c_init_done c' = c_init_done c;
  cs_fmh : c_free_meta_head c' = c_free_meta_head c;
  cs_am : c_avail_meta c' = c_avail_meta c;
  cs_amc : c_avail_meta_count c' = c_avail_meta_count c;
  cs_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
  cs_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
  cs_mah : c_meta_area_head c' = c_meta_area_head c;
  cs_mat : c_meta_area_tail c' = c_meta_area_tail c;
  cs_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
  cs_active : c_active c' = c_active c;
  cs_usage : c_usage c' = c_usage c;
  cs_brk : c_brk c' = c_brk c;
  (* [comment removed for export] *)
  cs_mc : 0 <= c_mmap_counter c' < 2^32;
  cs_seq : 0 <= c_seq c' < 256;
  cs_bounces : forall i v, c_bounces c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256;
  cs_unmap : forall i v, c_unmap_seq c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256
}.

Section CTX.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (f : mctx -> mctx).
Hypothesis INV : INVL X st L BL LS.
Hypothesis CS : ctx_scalars_eq (s_ctx st) (f (s_ctx st)).
Let st' := upd_ctx f st.

Theorem INVL_ctx_scalars : INVL X st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH). destruct CS as [cs_secret cs_init cs_fmh cs_am cs_amc cs_amac cs_shift cs_mah cs_mat cs_amas cs_active cs_usage cs_brk cs_mc cs_seq cs_bounces cs_unmap].
  assert (FR : forall rid r, frontier st' rid r = frontier st rid r) by (intros; unfold frontier, st'; cbn; rewrite cs_amas; reflexivity).
  assert (HE : forall h, get_head st' h = get_head st h) by (intros [sc|]; unfold st'; cbn; unfold active, ctx; cbn; rewrite ?cs_active, ?cs_fmh; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; unfold st'; cbn; rewrite ?cs_shift, ?cs_brk, ?cs_amac, ?cs_amas; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
    + intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
  - destruct IA; constructor; unfold st'; cbn; rewrite ?cs_secret, ?cs_init, ?cs_fmh, ?cs_am, ?cs_amc, ?cs_amac, ?cs_mah, ?cs_mat, ?cs_amas, ?cs_active, ?cs_usage; try assumption.
    + split; [exact cs_mc|]. split; [exact cs_seq|]. split; [exact cs_bounces| exact cs_unmap].
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
    + intros sc Hsc. unfold usage, ctx. cbn. rewrite cs_usage. exact (ia_usage sc Hsc).
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| exact HE| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto|]. eapply G1. exact Hb.
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End CTX.

Lemma ctx_scalars_refl c :
  0 <= c_mmap_counter c < 2^32 -> 0 <= c_seq c < 256 ->
  (forall i v, c_bounces c !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256) ->
  (forall i v, c_unmap_seq c !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256) ->
  ctx_scalars_eq c c.
Proof. intros; constructor; auto. Qed.

Lemma ia_ctx_facts st : inv_A st ->
  0 <= c_mmap_counter (s_ctx st) < 2^32 /\ 0 <= c_seq (s_ctx st) < 256
  /\ (forall i v, c_bounces (s_ctx st) !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256)
  /\ (forall i v, c_unmap_seq (s_ctx st) !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256).
Proof. intros IA. exact (ia_ctx _ IA). Qed.

Lemma INVL_step_seq X st L BL LS : INVL X st L BL LS -> INVL X (step_seq st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold step_seq. destruct (Z.eqb_spec (c_seq (ctx st)) 255) as [E|NE]; apply INVL_ctx_scalars; auto; constructor; cbn; auto; try lia.
  - intros i v H. rewrite lookup_empty in H. discriminate.
  - unfold ctx in NE. lia.
Qed.

Lemma INVL_record_seq X st L BL LS sc : INVL X st L BL LS -> INVL X (record_seq sc st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold record_seq. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros i v. destruct (Z.eq_dec i (sc - 7)) as [->|NEi].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C4.
Qed.

Lemma INVL_set_bounce X st L BL LS i v : INVL X st L BL LS -> 0 <= i < 32 -> 0 <= v < 256 -> INVL X (set_bounce i v st) L BL LS.
Proof.
  intros INV Hi Hv. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold set_bounce. apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  intros j w. destruct (Z.eq_dec j i) as [->|NE].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C3.
Qed.

Lemma bounces_range st i : inv_A st -> 0 <= bounces st i < 256.
Proof.
  intros IA. pose proof (ia_ctx_facts st IA) as (_ & _ & C3 & _). unfold bounces, ctx.
  destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 _ _ E)).
Qed.

Lemma INVL_account_bounce X st L BL LS sc : INVL X st L BL LS -> INVL X (account_bounce sc st) L BL LS.
Proof.
  intros INV. unfold account_bounce. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (negb _ && _); [| exact INV].
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  destruct (Z.ltb_spec (bounces st (sc - 7) + 1) 100); apply INVL_set_bounce; auto; lia.
Qed.

Lemma INVL_decay_bounces X st L BL LS sc : INVL X st L BL LS -> INVL X (decay_bounces sc st) L BL LS.
Proof.
  intros INV. unfold decay_bounces. destruct (sc_in_seq_range sc && _) eqn:E; [| exact INV].
  apply Bool.andb_true_iff in E as [E1 E2]. unfold sc_in_seq_range in E1. apply Bool.andb_true_iff in E1 as [E0 E1]. apply Z.leb_le in E0. apply Z.ltb_lt in E1.
  apply Bool.negb_true_iff in E2. apply Z.eqb_neq in E2.
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  apply INVL_set_bounce; auto; lia.
Qed.

Lemma INVL_mmap_counter X st L BL LS : INVL X st L BL LS ->
  INVL X (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  apply INVL_ctx_scalars; auto; constructor; cbn; auto. unfold u32. apply Z.mod_pos_bound. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rem (g : aptr) (l : list aptr) : list aptr := remove (fun x y => aptr_eq_dec x y) g l.
Definition xzomb (X : extras) (l : list aptr) : extras := mkX (x_idle X) l (x_pend X) (x_orph X) (x_fresh X).
Definition xidle (X : extras) (l : list aptr) : extras := mkX l (x_zomb X) (x_pend X) (x_orph X) (x_fresh X).

Lemma in_rem x g l : In x (rem g l) <-> In x l /\ x <> g.
Proof. unfold rem. split; [apply in_remove|]. intros [H NE]. apply in_in_remove; auto. Qed.

(* [comment removed for export] *)
Lemma present_of_mem st m b : m_mem (MR st m) = Some b -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.
Lemma present_of_next st m x : m_next (MR st m) = Some x -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.

Lemma gcnt_ext_groups st st' :
  s_groups st' = s_groups st ->
  (forall b h m, s_groups st !! b = Some h -> g_meta h = Some m ->
     m_sizeclass (MR st' m) = m_sizeclass (MR st m) /\ cnt_of (MR st' m) = cnt_of (MR st m)) ->
  forall sc, gcnt st' sc = gcnt st sc.
Proof.
  intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext_in. intros [b h] Hin. cbn.
  destruct (g_meta h) as [m|] eqn:Eh; [| reflexivity].
  apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
  destruct (HM b h m Hin Eh) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Section UNZOMBIE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hz : In g (x_zomb X).
Let X' := xzomb X (rem g (x_zomb X)).
Let st' := put_meta g meta0 st.

Lemma uz_R x : MR st' x = if aptr_eqb x g then meta0 else MR st x.
Proof. unfold st', MR. apply get_meta_rec_put. Qed.
Lemma uz_R_other x : x <> g -> MR st' x = MR st x.
Proof. intros NE. rewrite uz_R, aptr_eqb_neq by exact NE. reflexivity. Qed.

Theorem INVL_unzombie : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (im_zomb _ _ _ IM g Hz) as (NIg & Ng & Pg & bg & Mg & NGg).
  assert (NLg : forall b, ~ hosts st b g).
  { intros b [ai Hb]. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hm & _). cbn in Em. inversion Em. subst m. rewrite Mg in Hm. inversion Hm. subst. rewrite Hb in NGg. discriminate. }
  assert (RG : forall b m, hosts st b m -> MR st' m = MR st m).
  { intros b m Hm. apply uz_R_other. intros ->. exact (NLg b Hm). }
  assert (KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None).
  { intros x. unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
    split; [intros _; exact (present_of_mem st g bg Mg)| intros _; discriminate]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_X X); [reflexivity|]. destruct IR; constructor; try assumption.
  - destruct IA; constructor; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply gcnt_ext_groups; [reflexivity|].
      intros b h m Hb Eh. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Em & Hm & _). rewrite Eh in Em. inversion Em. subst m'.
      rewrite (RG b m); [auto|]. destruct h as [gm gai]. cbn in Eh. subst gm. exists gai. exact Hb.
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite uz_R in Hm |- *. destruct (aptr_eqb m g); [reflexivity|]. apply M1. exact Hm.
    + intros m b Hm. rewrite uz_R in Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [cbn in Hm; discriminate|].
      destruct (M2 m b Hm) as [H|H]; [left; exact H| right]. cbn. apply in_rem. auto.
    + intros b h Hb. destruct (M3 b h Hb) as (m & Em & Hm & Hai). exists m.
      assert (NE : m <> g) by (intros ->; apply (NLg b); destruct h as [gm gai]; cbn in Em; subst gm; exists gai; exact Hb).
      rewrite (uz_R_other m NE). auto.
    + intros m Hm. cbn in Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec m g) as [->|NE]; [reflexivity| exact E].
    + intros z Hz'. cbn in Hz'. apply in_rem in Hz' as [Hz' NE]. destruct (M5 z Hz') as (A1 & A2 & A3 & b & A4 & A5).
      rewrite (uz_R_other z NE). repeat split; auto. exists b. auto.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros x Hx; rewrite uz_R_other; try reflexivity; intros ->; apply NIg; exists h; rewrite E.
      * apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
      * apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
    + intros m. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite uz_R, aptr_eqb_refl. cbn. split; [| reflexivity]. split; [intros H; exfalso; exact (NIg H)| intros H; exfalso; apply H; reflexivity].
      * rewrite (uz_R_other m NE). apply L5.
    + intros m Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists LFree; exact Hm|]. rewrite (uz_R_other m NE). apply L6. exact Hm.
    + intros sc m Hm. destruct (L7 sc m Hm) as (A1 & A2 & A3).
      destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists (LActive sc); exact Hm|]. rewrite (uz_R_other m NE). auto.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    + intros m b ai Hb. pose proof (G1 m b ai Hb) as GO.
      assert (NE : m <> g) by (intros ->; exact (NLg b (ex_intro _ ai Hb))).
      destruct GO; constructor; rewrite ?(uz_R_other m NE); try assumption.
      * apply KEYS. exact g_present.
      * intros Hml. destruct (g_nest Hml) as (p & i & Hs & Hf & He & Hsc & Hst).
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _).
        assert (NEp : p <> g) by (intros ->; exact (NLg bp Hp)).
        exists p, i. rewrite (uz_R_other p NEp). auto 10.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2.
      rewrite (uz_R_other m1) by (intros ->; exact (NLg b1 (ex_intro _ ai1 H1))).
      rewrite (uz_R_other m2) by (intros ->; exact (NLg b2 (ex_intro _ ai2 H2))). eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (RG _ _ Hm). auto.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
    + intros s m i Hs. destruct (S1 s m i Hs) as ([b Hb] & Hi & E). rewrite (RG _ _ Hb). split; [exists b; exact Hb| auto].
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (S2 b); auto.
    + intros b m ai i Hb Hi. rewrite (RG b m (ex_intro _ ai Hb)) in Hi |- *. apply (S3 b m ai i Hb Hi).
    + intros k Hk. destruct (S6 k Hk) as (m & i & Hs & rest). exists m, i. split; [exact Hs|].
      destruct (S1 _ _ _ Hs) as ([b Hb] & _). rewrite (RG _ _ Hb). exact rest.
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (D3 b m i Hb Hi).
    + intros b m p i Hb Hml Hs. rewrite (RG _ _ Hb) in Hml.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _). rewrite (RG _ _ Hp). apply (D5 b m p i Hb Hml Hs).
    + intros k m i Hk Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & _). rewrite (RG _ _ Hb). apply (D6 k m i Hk Hs).
Qed.
End UNZOMBIE.
