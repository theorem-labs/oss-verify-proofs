(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (35 recorded proofs replaced by written proofs (leaf_of_ret_inv, leaf_of_vis_inv, leaf_of_bad and 32 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W9 ASlot_W18 ASlot_I.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_M0 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib6Malloc:MallocTree7leaf_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC35stdpp4base7is_SomeC59OSSVerify5KrLib6Malloc:MallocTree8mrun_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib6Malloc:MallocTree4mrunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree9mrun_peekC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8mrun_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2ex01K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0?leaf_of_vis_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01c59OSSVerify5KrLib6Malloc8ASlot_M02LOC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib6Malloc8ASlot_M0:links_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M07LO_reflC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp4base:decide_relC35stdpp4base6decideC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABEget_meta_rec_put_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABFget_meta_rec_put_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0<rec_set_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M07LO_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M08LO_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0<LO_upd_linksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00c59OSSVerify5KrLib6Malloc8ASlot_M0;leaf_of_badC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9am_finishC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<am_after_brkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M03KOKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M03BOKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M06KOK_LOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0>am_take_leavesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C35stdpp4base6lookupC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbc59OSSVerify5KrLib6Malloc8ASlot_M0?am_carve_leavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0@am_finish_leavesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_meta_alloc_shiftC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6Malloc>brk0_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0:LO_dequeueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0Cam_after_brk_leavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=brk_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<brk_pages_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDmmap_fixed_answer_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat2kSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat2bSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0?leaf_of_ret_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0Aalloc_meta_leavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc9Malloc_fp4mrel01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitK59OSSVerify5KrLib6Malloc7ASlot_I9ENTRY_REL01C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityC46Stdlib9micromega;ZifyClasses5mkrelC47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_ReflexiveC56Stdlib6ZArith4Znat3N2Z6inj_leI59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib6Malloc7ASlot_I9ENTRY_REL00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ASlot_W06ta_rel00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp4mrel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W09tr_shadowC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC59OSSVerify5KrLib6Malloc8ASlot_W09tr_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W0:tr_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W0;tr_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_geomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_bitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W08tr_areasC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_SymmetricC59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc:MallocTree6am_rel00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0Bam_leaf_links_onlyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:amr_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:amr_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;amr_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree7amr_newC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib6Malloc:MallocTree<amr_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree<amr_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree9amr_areasC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib6Malloc7ASlot_I4ALLCC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib6Malloc8ASlot_W07tr_tickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M09ALLC_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8amr_tickC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc>MallocFacts_AS6ISTF_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS4lmemC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ASlot_W93gmf00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr01C59OSSVerify5KrLib6Malloc>MallocFacts_AS6isf_mfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_A8MFACTS_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS6isf_lfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc>MallocFacts_AS6LFACTS00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS8isf_ghdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS=fact_ghdr_unkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8mf_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A:fact_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib6Malloc>MallocFacts_AS5lf_mwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS5mw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8mf_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A:fact_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS;lf_sc0_fullC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK59OSSVerify5KrLib6Malloc8ASlot_W93gmf01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib6Malloc=MallocFacts_A9sstart_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>agent_reservedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS8lf_listsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS:fact_listsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ASlot_W93taf00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9mf_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A;fact_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS8lf_linksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS:fact_linksC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M0<gmf_of_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W97gmf_grpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W97gmf_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W99gmf_linksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A6mf_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8fact_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc8ASlot_W93taf01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc59OSSVerify5KrLib6Malloc8ASlot_M0:sc_mono_fnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Malloc@F_malloc_enframe<forallb_zseqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib6Malloc8ASlot_M0=sc_mono_checkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z6eq_decK46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib6Malloc8ASlot_M0?size_class_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M07nest_fnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>F_malloc_entry5stc_qC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsBsubrelation_properC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Program6Basics4implc59OSSVerify5KrLib6Malloc8ASlot_M0:nest_checkC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop@and_iff_morphismK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W188as_fm_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition links_only (r r' : meta) : Prop :=
  m_mem r' = m_mem r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
  /\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leaf_of_ret_inv {R} o (r r' : R) : leaf_of o (SRet r) r' -> r' = r.
Proof. intros (ans & o' & H). rewrite mrun_ret in H. cbn in H. destruct ans; inversion H; reflexivity. Qed.

Lemma leaf_of_vis_inv {R} o e (k : Z -> Malloc.M R) r :
  leaf_of o (SVis e k) r ->
  match e with
  | EUndef _ => False
  | EPeek p c h => leaf_of o (k (pans_mem o p c h)) r
  | _ => exists z, leaf_of o (k z) r
  end.
Proof.
  intros (ans & o' & H).
  destruct e; try (rewrite mrun_vis in H by exact I; cbn [follow] in H; destruct ans as [|a ans]; [discriminate|]; exists a; exists ans, o'; exact H).
  - rewrite mrun_peek in H. exists ans, o'. exact H.
  - rewrite mrun_vis in H by exact I. cbn [follow] in H. destruct ans; discriminate.
Qed.

Lemma leaf_of_bad {R} o (bail : Malloc.M R) r : leaf_of o (bad_answer bail) r -> False.
Proof. intros H. exact (leaf_of_vis_inv o _ _ r H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LO (st st' : mstate) : Prop := forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).

Lemma LO_refl st : LO st st.
Proof. intros q. repeat split; reflexivity. Qed.
Lemma LO_trans st1 st2 st3 : LO st1 st2 -> LO st2 st3 -> LO st1 st3.
Proof.
  intros A B q. destruct (A q) as (A1&A2&A3&A4&A5&A6&A7). destruct (B q) as (B1&B2&B3&B4&B5&B6&B7).
  repeat split; congruence.
Qed.
Lemma LO_same st st' : (forall q, get_meta_rec st' q = get_meta_rec st q) -> LO st st'.
Proof. intros H q. rewrite H. apply LO_refl. Qed.

Lemma LO_upd_links st m f :
  (forall r, links_only r (f r)) -> LO st (upd_meta m f st).
Proof.
  intros Hf q. unfold upd_meta. destruct (decide (q = m)) as [->|NE].
  - rewrite get_meta_rec_put_same. apply Hf.
  - rewrite get_meta_rec_put_other by exact NE. apply LO_refl.
Qed.

Lemma lo_set_prev v r : links_only r (m_set_prev v r).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M0 ()) ["CANSEC1"] "h01rh11vp;2p;1p;3p;4g00k\j2=Tg00X3j1<Tg00BYj38Tg00Xij14Tg00Yaj1;Tg00ZYj1:Tg00[Tj17Tg00\Oj15Tg00]Kj16Tg00^Dj23Tg00CMj29Tg00^_j41Tg00F>R0f1R1f0R238p=21902p=0g00;>R0g00cCR31=12R4#<%<2R5580%44%42R6'2R7%;4%;2R8'2R9%:4%:2R:'2R;%74%72R<'2R=%54%52R>'2R?%64%62R4'2R@'3RA'3RB'3RC'3RD'31905P7PD%06P9PC%08P;PB%0:P=PA%0<P?P@%0>%04C1C1C1C1C1C1X03X10P1P2O2W0W1o"). Qed.
Lemma lo_set_next v r : links_only r (m_set_next v r).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M0 ()) ["CANSEC1"] "h01rh11vp;2p;1p;3p;4g00lWj2=Tg00X3j1<Tg00BYj38Tg00Xij14Tg00Yaj1;Tg00ZYj1:Tg00[Tj17Tg00\Oj15Tg00]Kj16Tg00^Dj23Tg00CMj29Tg00^_j41Tg00F>R0f1R1f0R238p=21902p=0g00;>R0g00cCR31=12R4#<%<2R5580%44%42R6'2R7%;4%;2R8'2R9%:4%:2R:'2R;%74%72R<'2R=%54%52R>'2R?%64%62R4'2R@'3RA'3RB'3RC'3RD'31905P7PD%06P9PC%08P;PB%0:P=PA%0<P?P@%0>%04C1C1C1C1C1C1X03X10P1P2O2W0W1o"). Qed.
Lemma lo_set_pn v w r : links_only r (m_set_prev v (m_set_next w r)).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M0 ()) ["CANSEC1"] "h01rh11vh21wp;2p;1p;3p;4g00lWj2>Tg00k\j2=Tg00X3j19Tg00BYj34Tg00Xij1<Tg00Yaj1;Tg00ZYj18Tg00[Tj15Tg00\Oj16Tg00]Kj17Tg00^Dj23Tg00CMj2:Tg00^_j40Tg00F>R0f1R1f0R234p=11:02p=2g00;>R0g00cCR3f2R41>12'=R5#9%92R6540%<5%<2R7'1R8%;5%;2R9'1R:%85%82R;'1R<%55%52R='1R>%65%62R?'1R@%75%72R5'1RA'3RB'3RC'3RD'3RE'31:06P8PE%27P:PD%29P<PC%2;P>PB%2=P@PA%2?%25C0C0C0C0C0C0X03X20X10P4P1P2O3W0X20W1o"). Qed.

Lemma rec_set_head h v st q : get_meta_rec (set_head h v st) q = get_meta_rec st q.
Proof. destruct h; reflexivity. Qed.

End CANSEC1.
Ltac lo_peel :=
  first [ apply LO_refl
        | apply LO_same; intros ?; reflexivity
        | eapply LO_trans; [| apply LO_upd_links; intros ?; repeat split; reflexivity]; lo_peel
        | eapply LO_trans; [| apply LO_same; intros ?; apply rec_set_head]; lo_peel ].

Section CANSEC2. Context {rc : runConstT}.
Lemma LO_dequeue h m st : LO st (dequeue h m st).
Proof.
  unfold dequeue. cbv zeta.
  destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m)));
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|];
  try destruct (optr_eqb _ (Some m)); lo_peel.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AML.
Context {R : Type}.
Variable o : mem.
Variable Φ : R -> Prop.

Definition KOK (st : mstate) (k : mstate -> optr -> Malloc.M R) : Prop :=
  forall st2 mo r, LO st st2 -> leaf_of o (k st2 mo) r -> Φ r.
Definition BOK (bail : Malloc.M R) : Prop := forall r, leaf_of o bail r -> Φ r.

Lemma KOK_LO st st1 k : LO st st1 -> KOK st k -> KOK st1 k.
Proof. intros L K st2 mo r L2 H. apply (K st2 mo r); [eapply LO_trans; [exact L| exact L2]| exact H]. Qed.

Lemma am_take_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (am_take st k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_take in H.
  destruct (c_avail_meta (ctx st)) as [m|].
  - eapply K; [| exact H]. lo_peel.
  - destruct (leaf_of_vis_inv o _ _ r H).
Qed.

Lemma am_carve_leaves st p k bail r : KOK st k -> BOK bail -> leaf_of o (am_carve st p k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_carve in H. cbv zeta in H.
  eapply am_take_leaves; [| exact B| exact H].
  eapply KOK_LO; [| exact K]. apply LO_same. intros q.
  destruct (c_meta_area_tail _); reflexivity.
Qed.

Lemma am_finish_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_finish st nu k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_finish in H.
  destruct (c_avail_meta_areas (ctx st)) as [p|]; [| destruct (leaf_of_vis_inv o _ _ r H)].
  cbv zeta in H.
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
    destruct (negb (mprotect_answer_ok z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct ((z =? 0) || (z =? TWO64 - ENOSYS)).
    + eapply am_carve_leaves; [exact K| exact B| exact Hz].
    + exact (K _ _ _ (LO_refl st) Hz).
  - eapply am_carve_leaves; [exact K| exact B| exact H].
Qed.

Lemma am_after_brk_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_after_brk st nu k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_after_brk in H.
  destruct (c_avail_meta_area_count (ctx st) =? 0).
  - destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
    destruct (negb (mmap_answer_ok _ _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct (is_err z); [exact (K _ _ _ (LO_refl st) Hz)|].
    destruct (new_region RKMeta z _ st) as [st1 rid] eqn:E.
    eapply am_finish_leaves; [| exact B| exact Hz].
    eapply KOK_LO; [| exact K]. apply LO_same. intros q.
    replace st1 with (fst (new_region RKMeta z (Z.shiftl 2 (c_meta_alloc_shift (ctx st)) * PGSZ) st)) by (rewrite E; reflexivity). reflexivity.
  - eapply am_finish_leaves; [exact K| exact B| exact H].
Qed.

Lemma alloc_meta_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (alloc_meta st k bail) r -> Φ r.
Proof.
  intros K B H. unfold alloc_meta in H.
  set (stI := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st) in H.
  assert (LI : LO st stI) by (apply LO_same; intros q; subst stI; destruct (c_init_done (ctx st) =? 0); reflexivity).
  pose proof (KOK_LO st stI k LI K) as KI.
  destruct (c_free_meta_head (ctx stI)) as [m|].
  { exact (KI _ _ _ (LO_dequeue LFree m stI) H). }
  destruct (negb (c_avail_meta_count (ctx stI) =? 0)); [eapply am_take_leaves; [exact KI| exact B| exact H]|].
  destruct ((c_avail_meta_area_count (ctx stI) =? 0) && _); [| eapply am_after_brk_leaves; [exact KI| exact B| exact H]].
  destruct (c_brk (ctx stI)) as [| |rid off].
  - (* [comment removed for export] *)
    destruct (leaf_of_vis_inv o _ _ r H) as [cur Hc]. cbv beta in Hc.
    destruct (negb (brk0_answer_ok cur)); [destruct (leaf_of_bad o _ _ Hc)|].
    destruct (leaf_of_vis_inv o _ _ r Hc) as [z Hz]. cbv beta in Hz.
    destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct (negb (z =? _)).
    + eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
    + destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
      destruct (leaf_of_vis_inv o _ _ r Hz) as [w Hw]. cbv beta in Hw.
      destruct (negb (mmap_fixed_answer_ok _ w)); [destruct (leaf_of_bad o _ _ Hw)|].
      destruct (new_region RKBrk _ _ stI) as [st1 rid1] eqn:E.
      eapply am_after_brk_leaves; [| exact B| exact Hw]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
      replace st1 with (fst (new_region RKBrk (round_up_pg cur) (2 * PGSZ) stI)) by (rewrite E; reflexivity). reflexivity.
  - (* [comment removed for export] *) eapply am_after_brk_leaves; [exact KI| exact B| exact H].
  - (* [comment removed for export] *)
    destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
    destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct (negb (z =? _)).
    + eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
    + destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
      eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
      unfold upd_region. destruct (get_region stI rid); reflexivity.
Qed.
End AML.

Lemma am_leaf_links_only : forall o st st' mo,
  leaf_of o (alloc_meta st kS bS) (Some (st', mo)) ->
  forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).
Proof.
  intros o st st' mo H.
  refine (alloc_meta_leaves o (fun r => match r with Some (stX, _) => LO st stX | None => True end) st kS bS (Some (st', mo)) _ _ H).
  - intros st2 mo2 r L HL. apply leaf_of_ret_inv in HL. subst r. exact L.
  - intros r HL. apply leaf_of_ret_inv in HL. subst r. exact I.
Qed.


Lemma links_only_refl r : links_only r r.
Proof. repeat split; reflexivity. Qed.
Lemma links_only_trans a b c : links_only a b -> links_only b c -> links_only a c.
Proof. intros (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). repeat split; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ER_refl_tick st0 t : ENTRY_REL st0 (set_tick t st0).
Proof.
  constructor; try reflexivity; try (intros; tauto).
  - split; [intros rid r H; exists r; cbn; repeat split; auto; lia| cbn; lia| reflexivity].
Qed.

Lemma ER_ta st0 st sc st1 : ENTRY_REL st0 st -> ta_rel sc st st1 -> ENTRY_REL st0 st1.
Proof.
  intros E T. destruct E as [ES EG EGR EM EME EGE EB EA].
  constructor.
  - rewrite (tr_shadow _ _ _ T). exact ES.
  - intros b. rewrite <- (EG b). destruct (tr_groups _ _ _ T b) as [A B].
    split; intros [x Hx]; [destruct (A (ex_intro _ x Hx)) as [y Hy]| destruct (B (ex_intro _ x Hx)) as [y Hy]]; rewrite Hy; eexists; reflexivity.
  - intros rid r Hk. rewrite (tr_regions _ _ _ T). apply EGR. exact Hk.
  - destruct EM as [R1 N1 S1]. split; [| rewrite (tr_next _ _ _ T); exact N1| rewrite (tr_reserved _ _ _ T); exact S1].
    intros rid r Hr. rewrite (tr_regions _ _ _ T). exact (R1 rid r Hr).
  - intros q. destruct (tr_geom _ _ _ T q) as (M & _). rewrite M. apply EME.
  - intros q Hq. destruct (EGE q Hq) as (A1 & A2 & A3). destruct (tr_geom _ _ _ T q) as (M & L & F & S & P). rewrite L, S. repeat split; try assumption.
    unfold get_stride. rewrite L, S, P. exact A1.
  - intros q i Hi Hb. apply (EB q i Hi). apply (tr_bits _ _ _ T q i Hi). exact Hb.
  - intros a Ha. rewrite (tr_areas _ _ _ T). apply EA. exact Ha.
Qed.

Lemma ER_am st0 st st1 m o : ENTRY_REL st0 st -> am_rel st st1 (Some m) ->
  leaf_of o (alloc_meta st kS bS) (Some (st1, Some m)) -> ENTRY_REL st0 st1.
Proof.
  intros E A L. destruct E as [ES EG EGR EM EME EGE EB EA].
  pose proof (am_leaf_links_only o st st1 (Some m) L) as LO.
  constructor.
  - rewrite (amr_shadow _ _ _ A). exact ES.
  - intros b. rewrite <- (EG b). rewrite (amr_groups _ _ _ A). tauto.
  - intros rid r Hk. rewrite <- (EGR rid r Hk). split; intros Hr.
    + destruct ((s_regions st) !! rid) as [r0|] eqn:E0.
      * destruct (amr_regions _ _ _ A rid r0 E0) as (r' & Hr' & K' & _ & _ & G'). rewrite Hr in Hr'. inversion Hr'; subst r'.
        rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      * exfalso. exact (amr_new _ _ _ A rid r Hr E0 Hk).
    + destruct (amr_regions _ _ _ A rid r Hr) as (r' & Hr' & K' & _ & _ & G'). rewrite Hr'. f_equal. apply G'. exact Hk.
  - destruct EM as [R1 N1 S1]. split.
    + intros rid r Hr. destruct (R1 rid r Hr) as (r1 & H1 & K1 & B1 & L1).
      destruct (amr_regions _ _ _ A rid r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. repeat split; try congruence. lia.
    + pose proof (amr_next_rid _ _ _ A). lia.
    + rewrite (amr_reserved _ _ _ A). exact S1.
  - intros q. destruct (LO q) as (M & _). rewrite M. apply EME.
  - intros q Hq. destruct (EGE q Hq) as (A1 & A2 & A3). destruct (LO q) as (M & AV & FR & L2 & F & S & P). rewrite L2, S. repeat split; try assumption.
    unfold get_stride. rewrite L2, S, P. exact A1.
  - intros q i Hi Hb. apply (EB q i Hi). destruct (LO q) as (_ & AV & FR & _). rewrite <- AV, <- FR. exact Hb.
  - intros a Ha. apply (amr_areas _ _ _ A). apply EA. exact Ha.
Qed.

Lemma ticks_ok_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros ES ET [T1 T2]. split; rewrite ES, ET; assumption. Qed.

(* [comment removed for export] *)
Lemma ALLC_tick st0 t :
  (forall rid sh o v tk, (s_shadow st0) !! rid = Some sh -> (r_cells sh) !! o = Some (v, tk) -> (tk <= s_tick st0)%N) ->
  (s_tick st0 < t)%N -> ALLC (set_tick t st0).
Proof. intros H Ht rid sh o v tk Hs Hc. cbn. pose proof (H rid sh o v tk Hs Hc). lia. Qed.

Lemma ALLC_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ALLC st -> ALLC st1.
Proof. intros ES ET H rid sh o v tk Hs Hc. rewrite ET. rewrite ES in Hs. exact (H rid sh o v tk Hs Hc). Qed.

Lemma ALLC_ta st sc st1 : ta_rel sc st st1 -> ALLC st -> ALLC st1.
Proof. intros T. apply ALLC_same; [apply (tr_shadow _ _ _ T)| apply (tr_tick _ _ _ T)]. Qed.

Lemma ALLC_am st st1 mo : am_rel st st1 mo -> ALLC st -> ALLC st1.
Proof. intros A. apply ALLC_same; [apply (amr_shadow _ _ _ A)| apply (amr_tick _ _ _ A)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gmf_of_facts st LB sc g :
  ISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
  intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
  pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
  pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  constructor.
  - exact MSL.
  - exact AVr.
  - exact FRr.
  - exact MW.
  - exact SC48.
  - exact GSC.
  - exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
    + intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
      change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
      exact (X Hmem Hgh S0).
    + intros o Ho. exact (GU b _ o Hgh Ho).
  - intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
  - intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
  - destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
    exists n, p. split; reflexivity.
Qed.

Lemma taf_of_facts st LB sc : ISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
  intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
  pose proof (lf_lists _ LF) as (L1 & L2 & L3).
  change (fact_active (strip st)) with (fact_active st).
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  pose proof (lf_links _ LF) as LK.
  constructor.
  - intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
    change (lmem (strip st) g) with (lmem st g) in LM.
    split; [| exact GSC]. eapply gmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
  - intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
    change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
    split; [eapply gmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
    split; [exact SCn|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
    exact (LKn n Hn).
  - intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
    change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
    split; [eapply gmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
    exact (LKp p Hp).
  - pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sc_mono_fn (a : Z) : bool := forallb (fun b => (size_class a <? size_class b)) (zseq (a + 1) (47 - a)).
Lemma sc_mono_check : forallb sc_mono_fn (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_mono a b : 0 <= a -> a < b < 48 -> size_class a < size_class b.
Proof.
  intros Ha Hb. pose proof (forallb_zseq sc_mono_fn 0 48 a sc_mono_check ltac:(lia) ltac:(lia)) as X. unfold sc_mono_fn in X.
  pose proof (forallb_zseq _ (a + 1) (47 - a) b X ltac:(lia) ltac:(lia)) as Y. apply Z.ltb_lt in Y. exact Y.
Qed.
Lemma size_class_lt_inv a b : 0 <= a < 48 -> 0 <= b < 48 -> size_class a < size_class b -> a < b.
Proof.
  intros Ha Hb H. destruct (Z.lt_ge_cases a b) as [L|G]; [exact L|]. exfalso.
  destruct (Z.eq_dec a b) as [->|NE]; [lia|]. pose proof (size_class_mono b a ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition nest_fn (q : Z) : bool := let j := stc_q q in (0 <=? j) && (j <=? 26) && (q + 1 <=? size_class j).
Lemma nest_check : forallb nest_fn (zseq 1 127) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nest_class_props q : 1 <= q <= 127 ->
  0 <= stc_q q <= 26 /\ q + 1 <= size_class (stc_q q).
Proof.
  intros Hq. pose proof (forallb_zseq nest_fn 1 127 q nest_check ltac:(lia) ltac:(lia)) as X. unfold nest_fn in X. cbv zeta in X.
  rewrite !Bool.andb_true_iff in X. destruct X as [[A B] C]. apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis ER : ENTRY_REL st0 st.
End FPER.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unk_agree_xfer o stA mA stB mB :
  unk_agree stA o mA ->
  s_shadow stB = s_shadow stA ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stB) !! rid = Some r -> (s_regions stA) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stB) !! b) <-> is_Some ((s_groups stA) !! b)) ->
  (forall rid r off h, (s_regions stA) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow stA rid) off = Unknown h -> ~ grp_hdr_cov stA rid off -> mB (wa (r_base r + off)) = mA (wa (r_base r + off))) ->
  unk_agree stB o mB.
Proof.
  intros UA ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow stA rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov stA rid off).
  { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

(* [comment removed for export] *)
Lemma fm_proj st g :
  let st' := as_fm_st st g in
  s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_groups st' = s_groups st /\ s_areas st' = s_areas st
  /\ s_slots st' = s_slots st /\ s_tick st' = s_tick st /\ s_next_rid st' = s_next_rid st /\ s_reserved st' = s_reserved st
  /\ (forall c, active st' c = active st c) /\ (forall i, usage st' i = usage st i)
  /\ c_brk (ctx st') = c_brk (ctx st) /\ c_mmap_counter (ctx st') = c_mmap_counter (ctx st)
  /\ (forall i, bounces st' i = bounces st i) /\ (forall i, unmap_seq st' i = unmap_seq st i) /\ c_seq (ctx st') = c_seq (ctx st).
Proof.
  unfold as_fm_st, as_queue_st, as_fm_link, as_fm_single. cbn [get_head].
  destruct (c_free_meta_head (ctx (put_meta g meta0 st))) as [h|].
  - cbv zeta. destruct (m_prev (get_meta_rec (put_meta g meta0 st) h)) as [p|]; repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.


End CANSEC2.
