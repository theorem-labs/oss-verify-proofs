(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (one5_A_to_E, tafin_listed, ta_fin_ok and 5 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_WKill MI_WNtf.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WTry () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C47Corelib4Init9Datatypes2IDC35stdpp4gmapBgmap_dep_ne_lookupC35stdpp8fin_maps@delete_insert_eqC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp8fin_mapsBmap_to_list_deleteC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap8gmap_key00I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indI47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6MI_Inv4g_aiC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec7MI_Bits<lowbit_idiomC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib4Spec6MI_Inv7g_underC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsFreflexive_proper_proxyC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_WTry;one5_A_to_EC1?~~~~~~~~~~~~~~~I35stdpp4gmap8gmap_dep00C35stdpp9countable6encodeC47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z8lt_totalC59OSSVerify5KrLib4Spec7MI_Geom9sstart_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec7MI_WNtf8one5_iffC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool;andb_true_rC59OSSVerify5KrLib4Spec6MI_Inv9il_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec8MI_Pres1@INVL_mask_changeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init5Logic2ex00K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes?RelationClasses;reflexivityK46Stdlib9micromega=RingMicromega5Psatz06I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C47Corelib7Classes>Morphisms_PropIiff_iff_iff_impl_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI46Stdlib9micromega:ZMicromega;ZArithProof00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>impl_ReflexiveC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib4Spec7MI_WTry<tafin_listedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_WTry9sa_lookupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_WTry8sa_hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC46Stdlib5Lists4List6filterI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WKill9zsum_permC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib4Spec6MI_Ext=dll_ext_metasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_WTry7sa_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext2<group_ok_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7iff_symK59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minK59OSSVerify5KrLib4Spec6MI_Inv6inv_SH01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:fold_rightC59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma one5_A_to_E (A B C D E A' E' : Prop) : A -> ~ A' -> E' -> one5 A B C D E -> one5 A' B C D E'.
Proof. unfold one5. tauto. Qed.

Section TAFIN.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m bm : aptr) (ai : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hm : s_groups st !! bm = Some (mkGhdr (Some m) ai).
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st m)))) = Some m.
Let mask := m_avail (MR st m).
Hypothesis MNZ : mask <> 0.
Let first := lowbit mask.
Let idx := ctz32 first.
Let st' := upd_meta m (m_set_avail (mask - first)) st.

Lemma tafin_listed : In m (LS (LActive (m_sizeclass (MR st m)))).
Proof. destruct (LS (LActive (m_sizeclass (MR st m)))); cbn in HEAD; [discriminate|]. inversion HEAD. left. reflexivity. Qed.

Theorem ta_fin_ok :
  INVL (xpend X (Some (fst bm, sstart (MR st m) idx))) st' L BL LS
  /\ 0 <= idx <= m_last_idx (MR st m) /\ first <> 0 /\ 0 <= first
  /\ UNIT * size_class (m_sizeclass (MR st m)) <= get_stride (MR st m).
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hmh : hosts st bm m) by (exists ai; exact Hm).
  assert (MPOS : 0 < mask) by (unfold mask in *; lia).
  destruct (lowbit_idiom mask MPOS) as (k0 & K0 & EL & EC & TB & A0 & TA).
  assert (Eidx : idx = k0) by (unfold idx, first; exact EC).
  assert (Hk0 : k0 <= ai) by (apply M3; [exact K0| exact TB]).
  assert (NU : UNIT * size_class (m_sizeclass (MR st m)) <= get_stride (MR st m)).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(E63 & _)].
    - destruct (Z.lt_ge_cases (get_stride (MR st m)) (UNIT * size_class (m_sizeclass (MR st m)))) as [LT|GE]; [| exact GE].
      exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite HF; discriminate) ltac:(lia) LT) as [A _]. unfold mask in MNZ. exact (MNZ A).
    - rewrite E63. change (size_class 63) with 0. pose proof (stride_ge _ _ _ IG _ _ Hmh) as [SG _]. unfold UNIT in *. lia. }
  assert (Ef : st' = upd_meta m (fun r => m_set_avail (mask - first) (m_set_freed (m_freed (MR st m)) r)) st).
  { unfold st', upd_meta, MR. destruct (get_meta_rec st m); reflexivity. }
  rewrite Ef.
  assert (FNZ : first <> 0 /\ 0 <= first) by (unfold first; rewrite EL; clear -K0; pose proof (Z.pow_pos_nonneg 2 k0); split; [lia| apply Z.pow_nonneg; lia]).
  rewrite Eidx.
  pose proof (stride_ge _ _ _ IG _ _ Hmh) as [SG _].
  split; [| split; [clear -K0 Hk0 AI; lia| split; [exact (proj1 FNZ)| split; [exact (proj2 FNZ)| exact NU]]]]. replace X with (mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) (x_fresh X)) at 1 by (destruct X; reflexivity).
  apply (INVL_mask_change X st L BL LS m bm ai (mask - first) (m_freed (MR st m)) (Some (fst bm, sstart (MR st m) k0)) INV Hm).
  - unfold first. split; [exact A0|]. split; [exact M2|]. split; [| split; [exact M4| split; [| exact M6]]].
    + intros i Hi. unfold tbit. rewrite TA by exact Hi. rewrite Bool.andb_true_iff. intros [H _]. exact (M3 i Hi H).
    + intros i Hi. unfold tbit. rewrite TA by exact Hi. rewrite Bool.andb_true_iff. intros [H _]. exact (M5 i Hi H).
  - intros j Hj. cbn zeta. unfold first, tbit. rewrite TA by (clear -Hj; lia).
    pose proof (is_part _ _ _ IS _ _ _ j Hm Hj) as P. cbn zeta in P. rewrite HP in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hmh) in P |- *.
    unfold tbit in P. destruct (Z.eqb_spec k0 j) as [<-|NE].
    + eapply one5_A_to_E; [exact TB| rewrite TB; cbn; discriminate| reflexivity| exact P].
    + rewrite Bool.andb_true_r. eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P].
      split; [discriminate|]. intros E. exfalso. inversion E.
      destruct (Z.lt_total k0 j) as [LT|[EQ|LT]]; [| lia|].
      * pose proof (sstart_lt _ _ _ IG _ _ k0 j Hmh LT) as SL. clear -SL SG H0. unfold UNIT in *. lia.
      * pose proof (sstart_lt _ _ _ IG _ _ j k0 Hmh LT) as SL. clear -SL SG H0. unfold UNIT in *. lia.
  - right. split; [rewrite HP; discriminate|]. intros s Hs. inversion Hs. subst s. exists k0. split; [clear -K0 Hk0 AI; lia|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hmh). reflexivity.
  - intros _ sc Hin Hnh. exfalso. destruct (il_active _ _ IL sc m Hin) as (_ & _ & Esc). subst sc. exact (Hnh (eq_sym HEAD)).
  - intros _ _ NI. exfalso. apply NI. eexists. exact tafin_listed.
  - intros _ Hsc LT. exfalso. clear -LT NU. lia.
Qed.
End TAFIN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SETAI.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m b : aptr) (ai ai' : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hm : s_groups st !! b = Some (mkGhdr (Some m) ai).
Hypothesis Hai' : ai <= ai' <= m_last_idx (MR st m).
Hypothesis AV : forall i, 0 <= i -> tbit (m_avail (MR st m)) i = true -> i <= ai'.
Hypothesis LISTED : ai' < m_last_idx (MR st m) -> In m (LS (LActive (m_sizeclass (MR st m)))).
Let st' := Malloc.set_groups (<[b := mkGhdr (Some m) ai']> (s_groups st)) st.

Lemma sa_lookup bb : s_groups st' !! bb = if aptr_eqb bb b then Some (mkGhdr (Some m) ai') else s_groups st !! bb.
Proof.
  unfold st'. cbn. destruct (aptr_eqb_spec bb b) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma sa_hosts bb x : hosts st' bb x <-> hosts st bb x.
Proof.
  unfold hosts. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [| tauto].
  split; intros [a H]; [rewrite Hm; inversion H; subst; eexists; reflexivity| rewrite Hm in H; inversion H; subst; eexists; reflexivity].
Qed.
Lemma sa_live x : live_group st' x <-> live_group st x.
Proof. unfold live_group. split; intros [bb H]; exists bb; apply sa_hosts; exact H. Qed.

Theorem INVL_set_ai : INVL X st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (GNE : forall bb h, s_groups st' !! bb = Some h -> (bb = b /\ h = mkGhdr (Some m) ai') \/ (bb <> b /\ s_groups st !! bb = Some h)).
  { intros bb h. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [intros H; inversion H; auto| auto]. }
  assert (GN : forall bb, s_groups st' !! bb <> None <-> s_groups st !! bb <> None).
  { intros bb. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [rewrite Hm; split; discriminate| tauto]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; try assumption.
    intros rid Ho. destruct (ir_orph rid Ho) as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
    intros bb Hbb. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [| exact (NG bb Hbb)]. specialize (NG b Hbb). rewrite Hm in NG. discriminate.
  - destruct IA; constructor; try assumption.
    intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). unfold gcnt.
    change (s_groups st') with (<[b:=mkGhdr (Some m) ai']> (s_groups st)).
    rewrite <- (zsum_perm _ _ (Permutation_map _ (map_to_list_delete (s_groups st) b _ Hm))).
    rewrite <- (zsum_perm _ _ (Permutation_map _ (map_to_list_delete (<[b:=mkGhdr (Some m) ai']> (s_groups st)) b (mkGhdr (Some m) ai') ltac:(apply lookup_insert_eq)))).
    cbn [map zsum fold_right snd g_meta]. rewrite delete_insert_eq. reflexivity.
  - destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; try assumption.
    + intros x bb Hx. destruct (Q2 x bb Hx) as [H|H]; [left; apply sa_hosts; exact H| right; exact H].
    + intros bb h Hbb. apply GNE in Hbb as [[-> ->]|[NE Hbb]]; [| exact (Q3 bb h Hbb)].
      exists m. cbn [g_meta g_active_idx]. split; [reflexivity|]. split; [exact (hosts_mem _ _ _ (mkIM _ _ _ Q1 Q2 Q3 Q4 Q5) _ _ (ex_intro _ ai Hm))| change (MR st' m) with (MR st m); lia].
    + intros z Hz. destruct (Q5 z Hz) as (A1 & A2 & A3 & bz & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      exists bz. split; [exact A4|]. rewrite sa_lookup. destruct (aptr_eqb_spec bz b) as [->|NE]; [rewrite Hm in A5; discriminate| exact A5].
  - destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. apply (dll_ext_metas st st' eq_refl). apply L2.
    + intros sc x Hx. destruct (L7 sc x Hx) as (B1 & B2 & B3). split; [exact B1|]. split; [apply sa_live; exact B2| exact B3].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros x bb aix Hbb. apply GNE in Hbb as [[-> E]|[NE Hbb]].
      * inversion E. subst x aix. destruct GO; constructor; change (MR st') with (MR st); try assumption.
        -- lia.
        -- destruct g_masks as (W1 & W2 & W3 & W4 & W5 & W6). split; [exact W1|]. split; [exact W2|]. split; [exact AV|]. split; [exact W4|]. split; [exact W5|].
           intros i Hi. apply W6. lia.
        -- intros NF Hlt. apply LISTED. exact Hlt.
        -- intros Hsc0. pose proof (g_full0 Hsc0). lia.
      * apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 x bb aix Hbb)].
    + intros bb aix Hbb. apply GNE in Hbb as [[_ E]|[NE Hbb]]; [discriminate| exact (G2 bb aix Hbb)].
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2 P1 P2 Esc. change (MR st') with (MR st) in P1, P2, Esc.
      apply GNE in H1 as [[-> E1]|[N1 H1]]; apply GNE in H2 as [[-> E2]|[N2 H2]].
      * inversion E1. inversion E2. subst. reflexivity.
      * inversion E1. subst m1 ai1. eapply G3; [exact Hm| exact H2| lia| exact P2| exact Esc].
      * inversion E2. subst m2 ai2. eapply G3; [exact H1| exact Hm| exact P1| lia| exact Esc].
      * eapply G3; eassumption.
    + intros rid r Hr K Ho. destruct (G4 rid r Hr K Ho) as (x & Hx & Hml). exists x. split; [apply sa_hosts; exact Hx| exact Hml].
    + intros bb h Hbb. apply GNE in Hbb as [[-> _]|[NE Hbb]]; [exact (G5 _ _ Hm)| exact (G5 bb h Hbb)].
  - destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
    + intros s x i Hs. destruct (S1 s x i Hs) as (B1 & B2 & B3). split; [apply sa_live; exact B1| auto].
    + intros bb x i Hbb Hi. apply (S2 bb); [apply sa_hosts; exact Hbb| exact Hi].
    + intros bb x aix i Hbb Hi. cbn zeta. change (MR st') with (MR st) in Hi |- *.
      eapply one5_iff; [reflexivity| reflexivity| reflexivity| apply iff_sym; apply GN| reflexivity|].
      apply GNE in Hbb as [[-> E]|[NE Hbb]]; [inversion E; subst x aix; exact (S3 b m ai i Hm Hi)| exact (S3 bb x aix i Hbb Hi)].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    + intros bb x i Hbb Hi. apply (D3 bb x i); [apply sa_hosts; exact Hbb| exact Hi].
    + intros bb x o Hbb Ho. apply (D4 bb x o); [apply sa_hosts; exact Hbb| exact Ho].
    + intros bb x p i Hbb Hml Hs. apply (D5 bb x p i); [apply sa_hosts; exact Hbb| exact Hml| exact Hs].
Qed.
End SETAI.

(* [comment removed for export] *)
Lemma span_loop_ge f : forall cnt span size, cnt <= span_loop f cnt span size.
Proof. induction f as [|f IH]; intros; cbn; [lia|]. destruct (_ <? _); [| lia]. pose proof (IH (cnt + 1) (span + size) size). lia. Qed.
