(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (11 recorded proofs replaced by written proofs (INVL_init, INVL_set_live, cpath_follow and 8 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_List MI_Ext
  MI_Pres2 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Contracts () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps<lookup_emptyC47Corelib4Init9Datatypes3sndC35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec4KInv8ctree_okC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_mapsAmap_to_list_emptyC59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~C35stdpp4base6ElemOfC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6lookupI35stdpp4base<list_elem_of00C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List8map_consI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6Malloc5minitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC47Corelib4Init9Datatypes2idK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8led_initC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;Permutation@Permutation_reflC35stdpp8fin_maps;map_to_listC59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~K35stdpp4base5NoDup01I35stdpp4base5NoDup00C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minK59OSSVerify5KrLib4Spec6MI_Inv6inv_SH01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decI47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decI59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C35stdpp9countable;Z_countableK47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~C35stdpp9countable;N_countableI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec6MI_Inv2x0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8set_liveC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim6lafterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree:ptree_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree>ptree_ctree_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree;ptree_strelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree:ftree_prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree<strel_followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9cpath_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv5cpath00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv5cpath01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv5cpath02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9bl_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ap_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes7reflect00C46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib4Spec<MI_Contracts5pans0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv6creach00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts6SIMRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts9INVL_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts<cpath_followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4MRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>malloc_controlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim:malloc_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts=INVL_set_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts8In_bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4FRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim;INVL_hdr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl<free_controlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim8free_simC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts=bl_remove_mapC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec4KInv:creach_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5cfreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts5pupd0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts;pans0_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts:creach_simC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv7ir_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WMalloc;malloc_INVLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_Contracts>ctree_ok_pathsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WNtf2@free_INVL_closedC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_init secret resv atop : 0 <= secret < 2 ^ 64 -> 0 < atop <= atop_hi ->
  INVL x0 (minit secret resv atop) (led_init resv atop) [] (fun _ => []).
Proof.
  intros Hs Ha.
  assert (NOH : forall b m, ~ hosts (minit secret resv atop) b m) by (intros b m [ai H]; cbn in H; rewrite lookup_empty in H; discriminate).
  assert (MR0 : forall m, MR (minit secret resv atop) m = meta0) by (intros m; unfold MR, get_meta_rec; cbn; rewrite lookup_empty; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - constructor; cbn; try (intros; rewrite lookup_empty in *; discriminate).
    + split; [reflexivity|]. split; [reflexivity| exact Ha].
    + rewrite map_to_list_empty. cbn. apply Permutation_refl.
    + rewrite map_to_list_empty. cbn. apply Permutation_refl.
    + split; [lia| left; reflexivity].
    + intros b l. split; [discriminate|]. intros (rid & r & H & _). rewrite lookup_empty in H. discriminate.
    + split; [reflexivity|]. intros rid r H. rewrite lookup_empty in H. discriminate.
    + split; [lia|]. split; [lia|]. intros rid off H. discriminate.
  - constructor; cbn; try (intros; rewrite lookup_empty in *; discriminate).
    + split; [lia|]. split; [lia|]. split; intros i v H; rewrite lookup_empty in H; discriminate.
    + split; [exact Hs|]. left. repeat split; reflexivity.
    + intros _. split; reflexivity.
    + split; [unfold NSLOTS; lia|]. intros H. lia.
    + intros sc Hsc. unfold usage, gcnt. cbn. rewrite lookup_empty, map_to_list_empty. reflexivity.
  - constructor; cbn.
    + intros m _. rewrite MR0. reflexivity.
    + intros m b H. rewrite MR0 in H. discriminate.
    + intros b h H. rewrite lookup_empty in H. discriminate.
    + intros m [].
    + intros z [].
  - constructor; cbn.
    + intros h. destruct h; cbn; [unfold active; cbn; rewrite lookup_empty|]; reflexivity.
    + intros h. exact I.
    + intros h. constructor.
    + intros h1 h2 m [].
    + intros m. rewrite MR0. cbn. split; [| reflexivity]. split; [intros [h []]| congruence].
    + intros m [].
    + intros sc m [].
    + intros h H. exfalso. apply H. reflexivity.
  - constructor; cbn.
    + intros m b ai H. rewrite lookup_empty in H. discriminate.
    + intros b ai H. rewrite lookup_empty in H. discriminate.
    + intros m1 m2 b1 b2 ai1 ai2 H. rewrite lookup_empty in H. discriminate.
    + intros rid r H. rewrite lookup_empty in H. discriminate.
    + intros b h H. rewrite lookup_empty in H. discriminate.
  - constructor; cbn.
    + intros s m i H. rewrite lookup_empty in H. discriminate.
    + intros b m i H. exfalso. exact (NOH _ _ H).
    + intros b m ai i H. rewrite lookup_empty in H. discriminate.
    + intros s H. discriminate.
    + constructor.
    + intros k [].
  - constructor; cbn.
    + intros rid sh H. rewrite lookup_empty in H. discriminate.
    + intros rid sh H. rewrite lookup_empty in H. discriminate.
    + intros b m i H. exfalso. exact (NOH _ _ H).
    + intros b m o H. exfalso. exact (NOH _ _ H).
    + intros b m p i H. exfalso. exact (NOH _ _ H).
    + intros k m i [].
Qed.

Lemma INVL_set_live X st L BL LS v : INVL X st L BL LS -> INVL X st (set_live v L) BL LS.
Proof.
  intros (IR & IA & IM & IL & IG & IS & ISH). split; [| split; [exact IA| split; [exact IM| split; [exact IL| split; [exact IG| split; [exact IS| exact ISH]]]]]].
  destruct IR; constructor; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cpath_follow {R} L (t : M R) L' r : cpath L t L' r -> exists ans, follow t ans = Some r /\ lafter L t ans = L'.
Proof.
  induction 1 as [L0 r0|L0 e k z L1 r0 Hz Hp IH].
  - exists []. split; reflexivity.
  - destruct IH as (ans & Hf & Hl). exists (z :: ans).
    destruct e; cbn [follow lafter]; try (split; [exact Hf| exact Hl]). cbn in Hz. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ctree_ok_paths {R} : forall (t : M R) L (P1 P2 : mled -> R -> Prop),
  ctree_ok L t P1 -> (forall L' r, cpath L t L' r -> P2 L' r) -> ctree_ok L t P2.
Proof.
  induction t as [r|e k IH]; intros L P1 P2 H HP; cbn [ctree_ok] in *.
  - apply HP. constructor.
  - destruct H as [He Hk]. split; [exact He|]. intros z Hz. apply (IH z _ P1); [apply Hk; exact Hz|].
    intros L' r Hp. apply HP. econstructor; eauto.
Qed.

Lemma bl_remove_map c BL : map bslot (bl_remove c BL) = ap_remove c (map bslot BL).
Proof.
  induction BL as [|k BL IH]; cbn; [reflexivity|]. destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

Lemma In_bslot c BL : In c (map bslot BL) -> exists off n, In ((c, off), n) BL.
Proof.
  intros H. apply in_map_iff in H as ([[c' off] n] & E & Hin). cbn in E. subst c'. exists off, n. exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pans0 (_ : unit) (_ : aptr) (_ _ : Z) : Z := 0.
Definition pupd0 (o : unit) (_ : ev) (_ : Z) : unit := o.
Lemma pans0_range : forall o p c h, 0 <= pans0 o p c h < 256.
Proof. intros. unfold pans0. lia. Qed.

Definition SIMREL (cs : mstate) (L : mled) : Prop :=
  exists st BL LS, strip st = cs /\ INVL x0 st L BL LS /\ ld_live L = map bslot BL.

Theorem creach_sim cs L : creach cs L -> SIMREL cs L.
Proof.
  induction 1 as [resv atop Ha|cs L n L' cs' r CR IH Hn CP|cs L c L' cs' CR IH Hc CP].
  - exists (minit 0 resv atop), [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; [lia| exact Ha]| reflexivity].
  - destruct IH as (st & BL & LS & <- & INV & LIVE).
    destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL in RES, LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
    + destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
      exists st', (((c, off), n) :: BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. reflexivity.
    + destruct RES as (LS' & INV'). exists st', BL, LS'. split; [reflexivity|]. split; [exact INV'|]. rewrite LIVE'. exact LIVE.
  - destruct IH as (st & BL & LS & <- & INV & LIVE).
    rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
    destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
    rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
    destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
    rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in INV', LIVE'.
    exists st', (bl_remove c BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. symmetry. apply bl_remove_map.
Qed.

(* [comment removed for export] *)
Lemma creach_atop cs L : creach cs L -> s_atop cs = ld_atop L.
Proof.
  intros H. destruct (creach_sim cs L H) as (st & BL & LS & <- & INV & _).
  destruct (ir_resv _ _ _ (proj1 INV)) as (_ & E & _). rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem cmalloc_contract_proof : forall cs L n,
  creach cs L -> 0 <= n ->
  ctree_ok L (cmalloc cs n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
  intros cs L n CR Hn. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
  apply (ctree_ok_paths _ L (fun _ _ => True)).
  - apply ptree_ctree_ok. eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range st n tt)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc st n) L _ tt (malloc_INVL st L BL LS n INV Hn)).
  - intros L' [cs' r] CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. cbn [snd]. rewrite HL in LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try exact I; try (exfalso; exact RES).
    destruct RES as (off & LS' & _ & _ & _ & NI). rewrite LIVE', LIVE. exact NI.
Qed.

Theorem cfree_contract_proof : forall cs L c,
  creach cs L -> In c (ld_live L) -> ctree_ok L (cfree cs (Some c)) (fun _ _ => True).
Proof.
  intros cs L c CR Hc. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
  apply ptree_ctree_ok.
  eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
  eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.
