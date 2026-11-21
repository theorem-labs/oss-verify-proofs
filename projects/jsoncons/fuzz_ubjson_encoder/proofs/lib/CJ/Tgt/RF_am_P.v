(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocRep F_malloc_free MallocTree MallocFacts_B MallocKit_B MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Export MallocFacts_AM.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_am_A F_am_K F_am_C F_am_D F_am_E F_am_G.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Export F_am_P.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Tgt Require Import RMallocRep.
Import ListNotations.
Open Scope Z_scope.

Notation RAMpre := (@AMpre_g _ ref_reserved).
Notation ram_pre := (am_pre_g ref_reserved).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_am_P () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C35stdpp4base7is_SomeI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;c_init_doneC13~~~C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:set_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc=set_init_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AM7AMpre_g00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:secret_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_countC13~~~C56Stdlib6ZArith6BinInt1Z2leC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~K47Corelib7Numbers7BinNums8positive01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_meta_alloc_shiftC13~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~I47Corelib4Init5Logic2eq00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B:ci_links_t00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_free_meta_headC13~~~K47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~I47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_metasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<c_avail_metaC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6moduloC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AM;fresh_aboveC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_next_ridC13~~~C56Stdlib6NArith6BinNat1N2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree7ptrs_inC13~~~C56Stdlib6NArith6BinNat1N2leC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP@secret_val_rangeC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or02C47Corelib4Init5Logic3iffK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B:ci_links_t01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AM7AMpre_g01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_E:am_init_stC13~~~K46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<ref_reservedC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~K47Corelib7Numbers7BinNums8positive03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5meta0C13~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8AREA_HDRC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9META_SIZEC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4PGSZC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~I47Corelib4Init5Logic4True00K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind01C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_P@ram_init_regionsC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_P3AMI00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>c_mmap_counterC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7c_usageC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;c_unmap_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9c_bouncesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AM<amp_s_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_slotsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6s_tickC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AM8amp_ptrsC13~~~C47Corelib4Init5Logic5proj2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AM8amp_rposC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_P3AMI01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AM:amp_secretC13~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z6inj_leI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree7optr_inC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6a_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6g_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree6am_rel00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_P;ctx_core_eqC13~~~C47Corelib4Init9Datatypes2idC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5usageC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7bouncesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9unmap_seqC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree6am_rel01C13~~~C35stdpp6option;from_optionc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_P=ram_rel_finalC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B9clr_linksC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8put_metaC13~~~C47Corelib4Init5Logic7f_equalC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BFget_meta_rec_put_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BEget_meta_rec_put_sameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BDmeta_slot_same_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BBmeta_slot_put_metaC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_P@rptrs_in_upd_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_A2@ptrs_in_put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<upd_meta_putC13~~~C56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_A7am_tookC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocDset_avail_meta_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>set_avail_metaC13~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega6VarMap1t01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_K8carve_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocIset_avail_meta_area_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_meta_area_tailC13~~~C35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic5proj1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_C=carve_st_someC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_C=carve_st_noneC13~~~K47Corelib4Init9Datatypes4prod01K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area01C13~~~C35stdpp4base6insertC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9set_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocDset_avail_meta_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7a_checkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8a_nslotsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B7deq_midC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8optr_eqbC13~~~C47Corelib4Init9Datatypes4negbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8get_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8aptr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;aptr_eqb_eqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_free_meta_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep=aptr_eqb_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B@get_meta_rec_putC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free=optr_eqb_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B;dequeue_midC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7dequeueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8set_headC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead02C13~~~K47Corelib4Init9Datatypes4bool02K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate03C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate02C13~~~C56Stdlib6NArith6BinNat1N4succK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;set_regionsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<set_next_ridC13~~~K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_A2Bptrs_in_new_regionC13~~~K46Stdlib9micromega5Tauto8GFormula03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:new_regionC13~~~C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat3N2Z8inj_succK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.



Section PURE.
Variable st : mstate.
Hypothesis AMP : RAMpre st.

Lemma rAMpre_init : RAMpre (am_init_st st).
Proof.
  unfold am_init_st. destruct (c_init_done (ctx st) =? 0); [| exact AMP].
  destruct AMP as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17]. split; cbn; try assumption.
  - rewrite A3. pose_secret. lia.
  - right; reflexivity.
  - destruct A8 as [L1 L2 L3 L4]. split; cbn; assumption.
Qed.

Lemma ram_init_regions : s_regions (am_init_st st) = s_regions st.
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma ram_init_brk : c_brk (ctx (am_init_st st)) = c_brk (ctx st).
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma ram_init_conc q : conc (am_init_st st) q = conc st q.
Proof. unfold conc, get_region. rewrite ram_init_regions. reflexivity. Qed.

Lemma rAMI_init : AMI st (am_init_st st).
Proof.
  unfold am_init_st. destruct (c_init_done (ctx st) =? 0);
  (split; [ repeat split; reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | intros rid r Hr; exists r; repeat split; auto; lia
          | intros rid r' H1 H2; cbn in H1; congruence
          | cbn; lia
          | intros P _ HP; exact HP || (destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); repeat split; assumption)
          | intros rid Hrid; apply (proj2 (amp_ptrs st AMP)); exact Hrid
          | exact (amp_rpos st AMP) ]).
  - cbn. rewrite (amp_s_secret st AMP). pose_secret. lia.
  - exact (amp_secret st AMP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rptrs_in_upd_ctx (P : N -> Prop) st0 f :
  optr_in P (c_free_meta_head (f (ctx st0))) -> optr_in P (c_avail_meta (f (ctx st0))) ->
  optr_in P (c_meta_area_head (f (ctx st0))) -> optr_in P (c_meta_area_tail (f (ctx st0))) ->
  optr_in P (c_avail_meta_areas (f (ctx st0))) -> c_active (f (ctx st0)) = c_active (ctx st0) ->
  match c_brk (f (ctx st0)) with BrkLive rid _ => P rid | _ => True end ->
  ptrs_in P st0 -> ptrs_in P (upd_ctx f st0).
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
  rewrite E6.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  split; [exact H6|]. split; [exact E7|]. split; [|split; [exact H9| exact H10]].
  intros g. exact (H8 g).
Qed.

(* [comment removed for export] *)
Lemma ram_rel_final stX st1 mo :
  AMI st stX ->
  c_active (ctx st1) = c_active (ctx stX) -> c_usage (ctx st1) = c_usage (ctx stX) -> c_unmap_seq (ctx st1) = c_unmap_seq (ctx stX) ->
  c_bounces (ctx st1) = c_bounces (ctx stX) -> c_seq (ctx st1) = c_seq (ctx stX) -> c_mmap_counter (ctx st1) = c_mmap_counter (ctx stX) ->
  s_groups st1 = s_groups stX -> s_slots st1 = s_slots stX -> s_shadow st1 = s_shadow stX -> s_tick st1 = s_tick stX ->
  s_reserved st1 = s_reserved stX -> s_regions st1 = s_regions stX -> s_next_rid st1 = s_next_rid stX ->
  (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas st1) !! a)) ->
  (forall g, Some g <> mo -> (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) -> get_meta_rec st1 g = get_meta_rec stX g) ->
  (forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m) ->
  (forall P : N -> Prop, (forall rid r, (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> P rid) -> ptrs_in P stX -> ptrs_in P st1) ->
  am_rel st st1 mo.
Proof.
  intros AI E1 E2 E3 E4 E5 E6 EG ESl ESh ET ERs ER EN HA HM HR HP.
  destruct AI as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  split.
  - intros sc. unfold active. rewrite E1, C7. reflexivity.
  - intros sc. unfold usage. rewrite E2, C8. reflexivity.
  - intros i. unfold bounces. rewrite E4, C10. reflexivity.
  - intros i. unfold unmap_seq. rewrite E3, C9. reflexivity.
  - rewrite E5, C11. reflexivity.
  - rewrite E6, C1. reflexivity.
  - rewrite EG, XG. reflexivity.
  - rewrite ESl, XS. reflexivity.
  - rewrite ESh, XSH. reflexivity.
  - rewrite ET, XT. reflexivity.
  - rewrite ERs, XR. reflexivity.
  - intros g Hg Hm. rewrite (HM g Hg Hm). unfold get_meta_rec. rewrite XM. reflexivity.
  - exact HR.
  - intros rid r Hr. rewrite ER. exact (XREG rid r Hr).
  - intros rid r' H1 H2. rewrite ER in H1. exact (XNEW rid r' H1 H2).
  - rewrite EN. exact XNX.
  - intros a Ha. apply HA. rewrite XA. exact Ha.
  - intros P HPn HP0. apply HP; [intros rid r Hr Hk; apply (HPn rid r); [rewrite ER|]; assumption|].
    apply XP; [| exact HP0]. intros rid r Hr Hk. apply (HPn rid r); [rewrite ER|]; assumption.
  - intros rid Hrid. rewrite ER, ESh, XSH. rewrite EN in Hrid. destruct (XF rid Hrid) as [A B]. split; [exact A| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ram_rel_none stX : AMI st stX -> am_rel st stX None.
Proof.
  intros AI. eapply (ram_rel_final stX stX None AI); try reflexivity; auto.
  - intros m Hm. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ram_rel_take stX q :
  AMI st stX -> c_avail_meta (ctx st) = Some q -> (s_metas st) !! q = None -> meta_slot st q ->
  am_rel st (am_took stX q (c_avail_meta_count (ctx stX) - 1)) (Some q).
Proof.
  intros AI AVM MQ MSq. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  unfold am_took. rewrite upd_meta_put.
  eapply (ram_rel_final stX _ (Some q) AI); try reflexivity.
  - intros a Ha. exact Ha.
  - intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
  - intros m Hm. inversion Hm; subst m. split.
    + rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. reflexivity.
    + apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSq]. cbn. rewrite XA. reflexivity.
  - intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta.
    + cbn. exact I.
    + cbn. exact I.
    + unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. cbn. exact I.
    + pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
      apply rptrs_in_upd_ctx; cbn [c_free_meta_head c_avail_meta c_meta_area_head c_meta_area_tail c_avail_meta_areas c_active c_brk set_avail_meta set_avail_meta_count];
        try assumption; try reflexivity.
      cbn. rewrite C3, AVM in H2. exact H2.
Qed.

(* [comment removed for export] *)
Lemma ram_rel_carve stX p r :
  AMI st stX -> (s_regions stX) !! (fst p) = Some r -> r_kind r <> RKGroup ->
  (s_areas stX) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas stX) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  (forall tl, c_meta_area_tail (ctx stX) = Some tl -> is_Some ((s_areas stX) !! tl)) ->
  am_rel st (am_took (carve_st stX p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof.
  intros AI Hr NK ANone FRESH TL. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (M0 : (s_metas stX) !! (aadd p AREA_HDR) = None).
  { replace (aadd p AREA_HDR) with (aadd p (AREA_HDR + META_SIZE * 0)) by (unfold aadd, AREA_HDR, META_SIZE; f_equal; lia). apply FRESH. unfold NSLOTS; lia. }

  assert (EX : exists stC, carve_st stX p = set_areas (<[p := mkArea (c_secret (ctx stX)) None NSLOTS]> (s_areas stC)) stC
            /\ s_regions stC = s_regions stX /\ s_metas stC = s_metas stX /\ s_groups stC = s_groups stX /\ s_slots stC = s_slots stX
            /\ s_shadow stC = s_shadow stX /\ s_tick stC = s_tick stX /\ s_reserved stC = s_reserved stX /\ s_next_rid stC = s_next_rid stX
            /\ c_active (ctx stC) = c_active (ctx stX) /\ c_usage (ctx stC) = c_usage (ctx stX) /\ c_unmap_seq (ctx stC) = c_unmap_seq (ctx stX)
            /\ c_bounces (ctx stC) = c_bounces (ctx stX) /\ c_seq (ctx stC) = c_seq (ctx stX) /\ c_mmap_counter (ctx stC) = c_mmap_counter (ctx stX)
            /\ (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas stC) !! a))
            /\ (forall P : N -> Prop, P (fst p) -> ptrs_in P stX -> ptrs_in P stC)).
  { destruct (c_meta_area_tail (ctx stX)) as [tl|] eqn:HT.
    - destruct (TL tl eq_refl) as [ar Har]. rewrite (carve_st_some stX p tl ar HT Har ANone). cbv zeta.
      eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
      + intros a Ha. cbn. destruct (decide (a = tl)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence; exact Ha].
      + intros P HP H0. apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
        * destruct H0 as (H1 & _). exact H1.
        * destruct H0 as (_ & H2 & _). exact H2.
        * destruct H0 as (_ & _ & H3 & _). exact H3.
        * exact HP.
        * exact HP.
        * destruct H0 as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
        * pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
          assert (PI : ptrs_in P (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) stX)).
          { apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity. }
          destruct PI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
          unfold ptrs_in. cbn [ctx s_ctx set_areas upd_ctx s_areas s_groups s_metas].
          split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
          split; [exact Q8|]. split; [| exact Q10].
          intros a ar' Ha. destruct (decide (a = tl)) as [->|NE].
          -- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [| exact HP]. exact (proj1 (H9 tl ar Har)).
          -- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
    - rewrite (carve_st_none stX p HT ANone). cbv zeta.
      eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
      + intros a Ha. exact Ha.
      + intros P HP H0. pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption. }
  destruct EX as (stC & EC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & RA & RP).
  rewrite EC. unfold am_took. rewrite upd_meta_put.
  set (stD := set_areas _ stC).
  eapply (ram_rel_final stX _ (Some (aadd p AREA_HDR)) AI); cbn [ctx s_ctx upd_ctx put_meta set_metas set_areas s_groups s_slots s_shadow s_tick s_reserved s_regions s_next_rid s_areas stD
     c_active c_usage c_unmap_seq c_bounces c_seq c_mmap_counter set_avail_meta set_avail_meta_count]; try assumption.
  - intros a Ha. destruct (decide (a = p)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence]. apply RA. exact Ha.
  - intros g Hg _. rewrite get_meta_rec_put_other by congruence. unfold get_meta_rec. cbn. rewrite R2. reflexivity.
  - intros m Hm. inversion Hm; subst m. split.
    + rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn. rewrite R2, M0. reflexivity.
    + apply meta_slot_put_meta. exists p, (mkArea (c_secret (ctx stX)) None NSLOTS), 0. cbn. rewrite lookup_insert_eq.
      split; [reflexivity|]. split; [unfold NSLOTS; lia|]. unfold aadd, AREA_HDR, META_SIZE. f_equal; lia.
  - intros P HPn HP0. assert (HPp : P (fst p)) by (apply (HPn (fst p) r Hr NK)).
    apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
    + unfold get_meta_rec. cbn. rewrite R2, M0. cbn. exact I.
    + apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
      * destruct (RP P HPp HP0) as (H1 & _). exact H1.
      * exact HPp.
      * destruct (RP P HPp HP0) as (_ & _ & H3 & _). exact H3.
      * destruct (RP P HPp HP0) as (_ & _ & _ & H4 & _). exact H4.
      * destruct (RP P HPp HP0) as (_ & _ & _ & _ & H5 & _). exact H5.
      * destruct (RP P HPp HP0) as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
      * pose proof (RP P HPp HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        unfold ptrs_in. cbn [ctx s_ctx set_areas s_areas s_groups s_metas].
        split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
        split; [exact H8|]. split; [| exact H10].
        intros a ar' Ha. destruct (decide (a = p)) as [->|NE].
        -- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [exact HPp| exact I].
        -- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
Qed.

(* [comment removed for export] *)
Lemma ram_rel_deq stI h nx pv :
  AMI st stI ->
  c_free_meta_head (ctx st) = Some h -> c_free_meta_head (ctx stI) = Some h ->
  m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv -> (nx = h <-> pv = h) ->
  meta_slot st h -> clr_links (get_meta_rec st h) = meta0 ->
  m_mem (get_meta_rec st nx) = None -> m_next (get_meta_rec st nx) <> None ->
  m_mem (get_meta_rec st pv) = None -> m_next (get_meta_rec st pv) <> None ->
  am_rel st (dequeue LFree h stI) (Some h).
Proof.
  intros AI FMH FMHI HN HP SELF MSh CL MN NN MP NP. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (GM : forall g, get_meta_rec stI g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite XM; reflexivity).
  rewrite dequeue_mid. unfold deq_mid. rewrite !GM, HN, HP. cbn [optr_eqb negb get_head]. rewrite FMHI.
  destruct (aptr_eqb nx h) eqn:E.
  -
    apply aptr_eqb_eq in E. subst nx. cbn [negb]. rewrite upd_meta_put. unfold set_head.
    eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
    + intros a Ha; exact Ha.
    + intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
    + intros m Hm. inversion Hm; subst m. split.
      * rewrite get_meta_rec_put_same. change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM. exact CL.
      * apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
    + intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
      * change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM, CL0 || (rewrite GM; destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & H8 & _);
          destruct (H8 h) as (_ & _ & Q); rewrite GM in Q; cbn; exact Q).
      * pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
  -
    assert (NEn : nx <> h) by (intros ->; rewrite aptr_eqb_refl in E; discriminate).
    assert (NEp : pv <> h) by (intros Ep; apply NEn; apply (proj2 SELF); exact Ep).
    cbn [negb]. rewrite optr_eqb_refl. rewrite !upd_meta_put. unfold set_head.
    set (st1 := put_meta pv _ stI). set (st2 := put_meta nx _ st1). set (st3 := upd_ctx _ st2).
    assert (R3 : get_meta_rec st3 h = get_meta_rec st h).
    { change (get_meta_rec st3 h) with (get_meta_rec st2 h). unfold st2, st1.
      rewrite !get_meta_rec_put_other by congruence. apply GM. }
    eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
    + intros a Ha; exact Ha.
    + intros g Hg Hm. rewrite get_meta_rec_put_other by congruence.
      change (get_meta_rec st3 g) with (get_meta_rec st2 g). unfold st2, st1.
      assert (g <> nx) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MN| apply NN; exact Hm]).
      assert (g <> pv) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MP| apply NP; exact Hm]).
      rewrite !get_meta_rec_put_other by assumption. reflexivity.
    + intros m Hm. inversion Hm; subst m. split.
      * rewrite get_meta_rec_put_same, R3. exact CL.
      * apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
    + intros P HPn HP0. pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
      destruct (H8 h) as (Q1 & Q2 & Q3). rewrite GM, HP in Q1. rewrite GM, HN in Q2. cbn in Q1, Q2.
      assert (P1 : ptrs_in P st1).
      { unfold st1. apply MallocKit_A2.ptrs_in_put_meta; [| cbn; exact Q2 | | exact HP0].
        - destruct (H8 pv) as (X & _ & _). exact X.
        - destruct (H8 pv) as (_ & _ & X). exact X. }
      assert (P2 : ptrs_in P st2).
      { unfold st2. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact Q1 | | | exact P1].
        - unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [exact Q2|]. destruct (H8 nx) as (_ & X & _). exact X.
        - unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [| destruct (H8 nx) as (_ & _ & X); exact X].
          destruct (H8 pv) as (_ & _ & X). exact X. }
      assert (P3 : ptrs_in P st3).
      { unfold st3. pose proof P2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
        apply rptrs_in_upd_ctx; cbn; try reflexivity.
        - exact Q2.
        - change (ctx st2) with (ctx stI). exact H2.
        - change (ctx st2) with (ctx stI). exact H3.
        - change (ctx st2) with (ctx stI). exact H4.
        - change (ctx st2) with (ctx stI). exact H5.
        - change (ctx st2) with (ctx stI). exact H7.
        - exact P2. }
      apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| | exact P3].
      rewrite R3. rewrite <- GM. exact Q3.
Qed.

(* [comment removed for export] *)
Lemma rAMI_ctx stX f :
  AMI st stX ->
  ctx_core_eq (ctx stX) (f (ctx stX)) -> 0 <= c_secret (f (ctx stX)) < 2^64 ->
  (c_avail_meta_areas (f (ctx stX)) = c_avail_meta_areas (ctx stX)
   \/ exists q r, c_avail_meta_areas (f (ctx stX)) = Some q /\ (s_regions stX) !! (fst q) = Some r /\ r_kind r <> RKGroup) ->
  (c_brk (f (ctx stX)) = c_brk (ctx stX)
   \/ c_brk (f (ctx stX)) = BrkDead
   \/ exists rid off r, c_brk (f (ctx stX)) = BrkLive rid off /\ (s_regions stX) !! rid = Some r /\ r_kind r <> RKGroup) ->
  AMI st (upd_ctx f stX).
Proof.
  intros AI CE SR HA HB. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  split; cbn; try assumption.
  - destruct CC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
    destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
    unfold ctx_core_eq. change (ctx (upd_ctx f stX)) with (f (ctx stX)).
    rewrite D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11. repeat split; assumption.
  - intros P HPn HP0. pose proof (XP P HPn HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
    apply rptrs_in_upd_ctx; rewrite ?D2, ?D3, ?D5, ?D6, ?D7; try assumption; try reflexivity.
    + destruct HA as [-> | (q & r & -> & Hq & Kq)]; [exact H5|]. cbn. exact (HPn _ _ Hq Kq).
    + destruct HB as [-> | [-> | (rid & off & r & -> & Hq & Kq)]]; [exact H7| exact I|]. exact (HPn _ _ Hq Kq).
    + exact (XP P HPn HP0).
Qed.

Lemma rAMI_new_region stX k base len :
  AMI st stX -> k <> RKGroup -> 0 < len ->
  AMI st (fst (new_region k base len stX))
  /\ (s_regions (fst (new_region k base len stX))) !! (s_next_rid stX) = Some (mkRegion k base len)
  /\ (forall q, fst q <> s_next_rid stX -> conc (fst (new_region k base len stX)) q = conc stX q)
  /\ (forall off, conc (fst (new_region k base len stX)) (s_next_rid stX, off) = base + off).
Proof.
  intros AI NK LEN. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  destruct (XF (s_next_rid stX) ltac:(lia)) as [FRr FRs].
  unfold new_region. cbn [fst].
  set (rid := s_next_rid stX). set (st' := set_next_rid _ _).
  assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions stX) !! q).
  { intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
  split; [| split; [| split]].
  - split; cbn -[insert]; try assumption.
    + intros q r Hq. destruct (XREG q r Hq) as (r' & Hr' & REST). exists r'. rewrite LK.
      destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hr'; discriminate|]. auto.
    + intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
    + unfold rid. lia.
    + intros P HPn HP0. apply (MallocKit_A2.ptrs_in_new_region stX base len k). apply XP; [| exact HP0].
      intros q r Hq Hk. apply (HPn q r); [| exact Hk]. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate| exact Hq].
    + intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply XF. unfold rid in Hq. lia.
    + intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia|]. exact (XRP q rq Hq).
  - rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
  - intros q Hq. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [exfalso; apply Hq; exact E| reflexivity].
  - intros off. unfold conc, get_region. cbn [fst snd]. rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
Qed.

Lemma rAMI_grow stX rid r off :
  AMI st stX -> (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> r_len r = off ->
  let st' := set_regions (<[rid := mkRegion (r_kind r) (r_base r) (off + 4096)]> (s_regions stX)) stX in
  AMI st st' /\ (forall q, conc st' q = conc stX q) /\ (s_regions st') !! rid = Some (mkRegion (r_kind r) (r_base r) (off + 4096)).
Proof.
  intros AI Hr NK LEN st'. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion (r_kind r) (r_base r) (off + 4096)) else (s_regions stX) !! q).
  { intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
  assert (CQ : forall q, conc st' q = conc stX q).
  { intros q. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [rewrite E, Hr|]; reflexivity. }
  split; [| split; [exact CQ| rewrite LK; destruct (decide (rid = rid)); [reflexivity| congruence]]].
  split; cbn -[insert]; try assumption.
  - intros q rq Hq. destruct (XREG q rq Hq) as (r' & Hr' & K' & B' & L' & G'). rewrite LK.
    destruct (decide (q = rid)) as [->|NE].
    + rewrite Hr in Hr'. inversion Hr'; subst r'. eexists. split; [reflexivity|]. cbn. split; [exact K'|]. split; [exact B'|]. split; [lia|].
      intros HG. exfalso. apply NK. rewrite K'. exact HG.
    + exists r'. auto.
  - intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
  - intros P HPn HP0. apply XP; [| exact HP0]. intros q rq Hq Hk.
    destruct (decide (q = rid)) as [->|NE].
    + apply (HPn rid (mkRegion (r_kind r) (r_base r) (off + 4096))); [rewrite LK; destruct (decide (rid = rid)); [reflexivity|congruence]|]. cbn. rewrite Hr in Hq. inversion Hq; subst. exact Hk.
    + apply (HPn q rq); [rewrite LK; destruct (decide (q = rid)); [congruence| exact Hq]| exact Hk].
  - intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE].
    + destruct (XF rid Hq) as [A _]. rewrite Hr in A. discriminate.
    + apply XF. exact Hq.
  - intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; pose proof (XRP rid r Hr); lia|]. exact (XRP q rq Hq).
Qed.
End PURE.
End CEIL_WRAP_1.

