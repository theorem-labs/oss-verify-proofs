(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W11 ASlot_W14 ASlot_W15 ASlot_W16 ASlot_W17 ASlot_W18 ASlot_I ASlot_M0 ASlot_M4P ASlot_M4 F_malloc_bigw F_malloc_big.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMallocKit_A3 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W11 RASlot_W14 RASlot_W15 RASlot_W16 RASlot_W17 RASlot_W18 RASlot_W19 RASlot_M0 RASlot_M2 RASlot_M3 RASlot_M5D RASlot_M5F RASlot_M5S RF_malloc_big.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RASlot_M4 () := "C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveK5ARocqVerifyHarness?AgentSubmission4Spec5STree5stree02C47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aptrC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp8fin_maps:map_insertC47Corelib4Init9Datatypes3sndC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base4fmapC35stdpp4base6insertC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4optrI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M48mm_afterC5ARocqVerifyHarness?AgentSubmission5Ubsan9RASlot_M39rHMM_stmtC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree6rimplTC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M4=ag_tail_kq_eqC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc1MC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W18?as_free_meta_eqC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree<rimplT_undefC5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I7ag_mmapC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree?rimplT_from_evtC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree>rimplT_mmap_rwC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:bad_answerC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc9free_metaC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7ag_tailC35stdpp8fin_maps<lookup_emptyI35stdpp4gmap4gmap00C35stdpp8fin_maps@lookup_insert_eqC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_foldK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5Ubsan9RASlot_M37rag_ctxK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:size_classC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission6Malloc>MallocFacts_AS7ta_failI5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_W06ta_rel00K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission6Malloc9MallocNat2kSC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocNat2bSI5ARocqVerifyHarness?AgentSubmission6Malloc>MallocFacts_AS3IST00C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc<get_meta_recC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5Ubsan9RASlot_M24rFRMK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMalloc_fp:rmalloc_fpC5ARocqVerifyHarness?AgentSubmission4Spec6PState4ps_mC5ARocqVerifyHarness?AgentSubmission4Spec6PState5ps_faC5ARocqVerifyHarness?AgentSubmission4Spec6PState5ps_soC5ARocqVerifyHarness?AgentSubmission5Ubsan9RASlot_M3:rcnt_stateI5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I9ENTRY_REL00C5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I4ALLCC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep8ticks_okC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep9meta_slotC5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp9unk_agreeC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep5rmrepC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree8rauxv_okC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree<rpres_exceptC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree;brk_link_psC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission5Ubsan@RAllocSlot_iface<RAS_STACK_geC5ARocqVerifyHarness?AgentSubmission5Ubsan@RAllocSlot_iface9RAS_STACKC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5D;rerrno_lit5C5ARocqVerifyHarness?AgentSubmission6Malloc@MallocFacts_inv4?ist_facts_proofI5ARocqVerifyHarness?AgentSubmission6Malloc>MallocFacts_AS6ISTF_g00C5ARocqVerifyHarness?AgentSubmission6Malloc>MallocFacts_AS6isf_mfI5ARocqVerifyHarness?AgentSubmission6Malloc=MallocFacts_A8MFACTS_g00C5ARocqVerifyHarness?AgentSubmission6Malloc=MallocFacts_A8mf_usageC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5stripC5ARocqVerifyHarness?AgentSubmission6Malloc=MallocFacts_A:fact_usageC5ARocqVerifyHarness?AgentSubmission6Malloc=MallocFacts_A6mf_ctxC5ARocqVerifyHarness?AgentSubmission6Malloc=MallocFacts_A8fact_ctxC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc>c_mmap_counterC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8c_secretC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc;c_init_doneC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5c_seqC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7bouncesC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc9unmap_seqC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc3ctxI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep@size_class_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep2wzC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc;is_bouncingC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W16:mm_cnt_redC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W168mm_finalC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M4@mm_cnt_red_rangeC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega7EnvRing5PExpr01C5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M4>mm_final_propsC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc;round_up_pgC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5usageC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W169mm_usage1C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M4Around_up_pg_propsC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W15<rmm_seq_walkC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M49stS_shapeC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7upd_ctxC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8c_activeC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7c_usageC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5c_brkC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc@c_free_meta_headC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc<c_avail_metaC5ARocqVerifyHarness?AgentSubmission4Spec6MallocBc_avail_meta_countC5ARocqVerifyHarness?AgentSubmission4Spec6MallocGc_avail_meta_area_countC5ARocqVerifyHarness?AgentSubmission4Spec6MallocBc_meta_alloc_shiftC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc@c_meta_area_headC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc@c_meta_area_tailC5ARocqVerifyHarness?AgentSubmission4Spec6MallocBc_avail_meta_areasC47Corelib4Init9Datatypes2idC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5s_ctxC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc9s_regionsC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8s_shadowC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:s_next_ridC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7s_metasC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7s_areasC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8s_groupsC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7s_slotsC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6s_tickC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8s_secretC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:s_reservedC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6s_atopK5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6mstate01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W169rmmc_postC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W169rmmc_walkK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree9ralloc_fpC5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp<new_reg_addrC5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp>free_slot_addrC5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp<grp_hdr_addrC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree:fresh_addrC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6r_kindC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep5lr_loC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6r_baseC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5r_lenK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTreeErpres_except_of_munchC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTreeBrpres_except_transK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree>rauxv_ok_frameC5ARocqVerifyHarness?AgentSubmission5Ubsan<RMallocKit_BArmeta_slot_boundsC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4concC56Stdlib6ZArith6BinInt1Z2geC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W17=rmm_call_walkC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_mm_syscalls?rmmap_anon_postC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_mm_syscalls?rmmap_anon_specC35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep;rregions_wfC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep9rmrep_ctxC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep=rmrep_globalsC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep;rmrep_areasC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep<rmrep_groupsC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep<rmrep_shadowC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep@rregions_wf_atopC5ARocqVerifyHarness?AgentSubmission6Malloc;MallocKit_BDmeta_slot_same_areasC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M0=ticks_ok_sameC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_W0:tr_regionsC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree8mmap_valC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep8rstaticsK5ARocqVerifyHarness?AgentSubmission3Lib6Decode8mmap_ans01C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc;live_rangesC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps9neg_errnoC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc>mmap_answer_okC47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6is_errC5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I5as_kqC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc@set_mmap_counterC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission6Malloc<F_malloc_bigBmmap_answer_ok_errC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W188as_fm_stC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_malloc_bigDrwrapper_munch_keepsC5ARocqVerifyHarness?AgentSubmission6Malloc>MallocFacts_AS6isf_lfC5ARocqVerifyHarness?AgentSubmission6Malloc>MallocFacts_AS;lf_freelistC5ARocqVerifyHarness?AgentSubmission6Malloc>MallocFacts_AS=fact_freelistC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6m_prevK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W17Armm_ret_fail_walkC5ARocqVerifyHarness?AgentSubmission5Ubsan9RASlot_W29rta_frameC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W18<rfailm2_walkC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W186rfailWC5ARocqVerifyHarness?AgentSubmission5Ubsan8RASlot_I9ras_post2C5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5F:rfailW_lowC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5F5rlowWC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5F>rlowW_disjointC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5FBrlowW_disjoint_imgC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W198ras_ret0C5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M07fm_projC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5F<rfailW_shapeC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5F6rmetaWC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMalloc_fp?rmalloc_fp_monoC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTreeArpres_except_monoC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMalloc_fpArmeta_chunk_factsC5ARocqVerifyHarness?AgentSubmission5Ubsan<RMallocKit_BFrpres_except_of_munch'C35stdpp4base5emptyI5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp4mrel00I5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I7as_inv200C5ARocqVerifyHarness?AgentSubmission5Ubsan9RASlot_M0Erauxv_ok_malloc_fp_ERC35stdpp4base7is_SomeC47Corelib4Init5Logic3iffK5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7cellval02C5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp;grp_hdr_covC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMalloc_fp=rregion_factsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission6Malloc;MallocKit_B9ivs_avoidC5ARocqVerifyHarness?AgentSubmission6Malloc;MallocKit_B=avoid_outsideC5ARocqVerifyHarness?AgentSubmission3Lib3Mem;wa_unsignedC47Corelib4Init5Logic8eq_transC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M0>unk_agree_xferC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree;amr_regionsC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree<amr_next_ridC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_W07tr_nextC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_W0;tr_reservedC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree<amr_reservedK5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp4mrel01K5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8brkstate03C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6activeC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_W09tr_activeC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree:amr_activeC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_W08tr_areasC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree9amr_areasC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_W07tr_tickC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree8amr_tickC5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I8ret_spanC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:get_shadowC56Stdlib6NArith6BinNat1N2ltC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5r_havC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6r_havpK5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I7as_inv201C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneK5ARocqVerifyHarness?AgentSubmission3Lib6Decode8mmap_ans02C5ARocqVerifyHarness?AgentSubmission6Malloc<F_malloc_bigCmmap_answer_ok_addrC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc;ranges_freeC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep6W_highC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRepDrmrep_transport_highK5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6region01C56Stdlib6NArith6BinNat1N4succC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc;set_regionsC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc<set_next_ridC5ARocqVerifyHarness?AgentSubmission6Malloc=MallocFacts_A7mf_ptrsC5ARocqVerifyHarness?AgentSubmission6Malloc=MallocFacts_A9fact_ptrsC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree7ptrs_inC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree<ptrs_in_monoC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocKit_A2Fptrs_in_upd_ctx_scalarC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC5ARocqVerifyHarness?AgentSubmission3Lib6Decode8mmap_lenC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocKit_A2Ammap_len_round_upC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep=zeros_outsideC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep<zeros_insideC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep2b8K47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMallocKit_A2@rmrep_new_regionC5ARocqVerifyHarness?AgentSubmission4Spec6MallocAregion_live_rangeC35stdpp8fin_maps;map_to_listC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRepArstatics_reservedC46Stdlib5Lists4List9in_or_appC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree>ranges_free_InC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTreeAranges_free_introC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRepCrreserved_disjoint1C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImgAref_ro_addr_falseC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep=mem_inv_zerosC5ARocqVerifyHarness?AgentSubmission6Malloc<F_malloc_bigBmunch_of_pointwiseC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep@wview_zeros_monoC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aaddI5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree6am_rel00C5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree7optr_inC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6a_nextC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6g_metaC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocKit_A27nr_concC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W176mm_st4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W17?rmm_ret_ok_walkC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc<m_set_maplenK5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4meta01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6m_nextC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5m_memC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7m_availC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7m_freedC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:m_last_idxC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:m_freeableC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc;m_sizeclassC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8put_metaC5ARocqVerifyHarness?AgentSubmission6Malloc;MallocKit_BEget_meta_rec_put_sameC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocKit_B3;rec_upd_ctxC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W17;mm_ai_rangeC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W175mm_aiC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W146rtailWC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep;conc_regionC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W14:rtail_walkC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W148st_modelC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P:sm_slot_okC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P7sm_projC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc9hdr_havocK5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4ghdr01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5S>rmrep_st_modelC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P<sm_meta_slotC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P7sm_concC5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I7er_mrelC5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp<mrel_regionsC5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp=mrel_reservedC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree?ranges_free_subC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree?fresh_addr_antiC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree>In_live_rangesC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep;lr_lo_groupC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00K5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7cellval01C5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P<sm_cell_readC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P>sm_grp_hdr_covC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P?sm_shadow_otherC5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_M5SArgrp_hdr_cov_sameC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4PBsm_grp_hdr_cov_oldC5ARocqVerifyHarness?AgentSubmission6Malloc<F_malloc_bigBunk_agree_transferC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep:meta_cellsC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P9sm_activeC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P;sm_ret_spanC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P=sm_cells_noneC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P;sm_hav_noneC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P<sm_havp_noneC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc3u32C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:get_strideC56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z7mul_0_rC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_M4P6sm_rdvC5ARocqVerifyHarness?AgentSubmission6Malloc8ASlot_M4:ag_mmap_eqC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:alloc_metaC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree7leaf_ofC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc>account_bounceC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8step_seqK5ARocqVerifyHarness?AgentSubmission4Spec6Malloc2ev02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC35stdpp6option;from_optionC47Corelib4Init9Datatypes3fstK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission6Common;MM_syscalls>mmap_fix_errnoC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:new_regionC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8upd_metaC46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission6Malloc@F_malloc_enframe3rdvI5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp7slot_ok00C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc9cell_readC5ARocqVerifyHarness?AgentSubmission4Spec6PState6ps_brkC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7r_cellsC5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission6Common;MM_syscalls8mmap_rawC5ARocqVerifyHarness?AgentSubmission3Lib6Decode<mmap_addr_okC5ARocqVerifyHarness?AgentSubmission6Malloc9ASlot_W145stFinC46Stdlib9micromega;ZifyClasses5mkappI5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6mstate00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes4unit00I5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4meta00C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5meta0K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RCTXK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7PROT_RWI5ARocqVerifyHarness?AgentSubmission4Spec6Malloc2ev00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RASlot_W155rseqWI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8brkstate00I47Corelib4Init5Logic4True00I5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5rkind00K5ARocqVerifyHarness?AgentSubmission4Spec6Malloc5rkind03I5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6region00I47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep<ref_reservedI5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4area00I5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4ghdr00C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8full_layC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree3memC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree8pans_memI5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7cellval00K5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8brkstate01K5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8brkstate02C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6shadow00C56Stdlib6ZArith4Znat3N2Z6inj_ltC56Stdlib6ZArith4Znat3N2Z6inj_leC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8AREA_HDRC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc9META_SIZEC45stdpp7numbers1N6eq_decC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc7shadow0C56Stdlib6ZArith4Znat3N2Z8inj_succI5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4UNITC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep:RSSP_GUARDC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep6RMLOCKC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep=RSIZE_CLASSESK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc;MAP_PRIVATEC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8MAP_ANONI47Corelib4Init5Logic5False00I5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4mctx00C35stdpp9countable;N_countableC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg:RAUXV_CELLC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg;rmmap_entryC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RATPI5ARocqVerifyHarness?AgentSubmission3Lib6Decode8mmap_ans00C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6NSLOTSC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4PGSZK5ARocqVerifyHarness?AgentSubmission4Spec6Malloc<undef_reason04".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rhmm_ok : rHMM_stmt k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof using A1 AR AUX CLO ER FIT HK LO MR RQ SC TP.
  clear A0 F0 IS AC TK UA BL ST MI ERR.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R BIGc.
  destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. atop_facts.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2) as URall. change (fact_usage (strip st2)) with (fact_usage st2) in URall.
  pose proof (mf_ctx _ _ MF2) as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
  change (ctx (strip st2)) with (ctx st2) in FC1, FC2, FC3, FC4. change (bounces (strip st2)) with (bounces st2) in FC5. change (unmap_seq (strip st2)) with (unmap_seq st2) in FC6.
  pose proof (size_class_range sc SC) as SZR.
  unfold rcnt_state.
  replace (size_class sc * UNIT * cnt1) with (UNIT * size_class sc * cnt1) by lia.
  replace (size_class sc * UNIT) with (UNIT * size_class sc) by lia.
  set (size := UNIT * size_class sc) in *.
  assert (SZ : 16 <= size < 2^18) by (subst size; unfold UNIT; lia).
  rewrite A1. rewrite (ag_mmap_eq sc req k bail st2 mm cnt1).
  set (stS := step_seq (account_bounce sc st2)).
  set (nos := is_bouncing sc st2).
  set (u1 := mm_usage1 stS sc (usage st2 sc)).
  set (cR := mm_cnt_red sc size cnt1 u1 nos).
  assert (CRR : 1 <= cR <= 32) by (subst cR; apply mm_cnt_red_range; exact C1R).
  destruct (mm_final size req u1 cR nos) as [c nd] eqn:EF.
  destruct (mm_final_props size req u1 cR nos c nd CRR ltac:(lia) ltac:(lia) ltac:(subst size; unfold UNIT; lia) EF) as (CR & NDM & NDR & NDC).
  assert (NDB : 16 <= nd < 2^40).
  { pose proof (round_up_pg_props (req + 20) ltac:(lia)). pose proof (round_up_pg_props (size * c + 16) ltac:(nia)).
    assert (size * c <= 2^18 * 32) by nia. destruct NDC as [[Ec En]|[LE En]]; rewrite En; lia. }
  cbv beta iota.
  riprefixT.
  eapply evt_cut. { eapply (rmm_seq_walk sc SC); [exact MR3| exact FC4| exact FC5| exact FC6| exact MI3]. }
  cbv beta. intros ms' (u0 & u1' & wa3 & wa6 & wa7 & m4 & -> & -> & MU4 & WM4 & MI4 & MR4).
  fold nos stS in MR4 |- *.
  destruct (stS_shape sc st2) as (fS & ES & HS). fold stS in ES.
  assert (US : forall i, usage stS i = usage st2 i) by (intros i; unfold usage; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (proj2 (HS _))); reflexivity).
  eapply evt_cut.
  { replace (wz (size + 16)) with (wz (size + 16)) by reflexivity.
    eapply (rmmc_walk sc size req nos SC SZ RQ) with (st := stS) (m := m4); [exact MR4| exact C1R| apply URall| intros i; rewrite US; apply URall]. }
  cbv beta. unfold rmmc_post. intros ms' (v0 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & ->).
  fold u1. fold cR. rewrite ?EF. cbn [fst snd].
  assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [exact FR3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ERR4 : rw_cells usegs m4 (errno_addr tp) [C4 errv']).
  { eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4|]. rewrite EA. unfold rseqW, RCTX. cbn. lia. }
  assert (PE04 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4).
  { eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_of_munch; [exact MU4| exact WM4|].
    intros a Ha NC. unfold rseqW. cbn. split; [|exact I]. intros X. apply NC. left. right. right. left. unfold RCTX in *. atop_facts. lia. }
  assert (AUX4 : rauxv_ok m4 (bv_unsigned sp)).
  { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. unfold rseqW, RAUXV_CELL, RCTX, RLIBC. constructor; [cbn; lia| constructor]. }
  pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _).
  eapply evt_cut. { eapply rmm_call_walk. }
  cbv beta. intros ms' ->.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -144) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lia | rewrite SP'; lia | exact CLO
    | rewrite SP', EA; lia | rewrite TP; unfold RATP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  assert (REGS : s_regions stS = s_regions st2) by (rewrite ES; reflexivity).
  assert (SHS : s_shadow stS = s_shadow st2) by (rewrite ES; reflexivity).
  assert (GRS : s_groups stS = s_groups st2) by (rewrite ES; reflexivity).
  assert (ARS : s_areas stS = s_areas st2) by (rewrite ES; reflexivity).
  assert (TKS' : s_tick stS = s_tick st2) by (rewrite ES; reflexivity).
  assert (NRS : s_next_rid stS = s_next_rid st2) by (rewrite ES; reflexivity).
  assert (RSS : s_reserved stS = s_reserved st2) by (rewrite ES; reflexivity).
  assert (ATS : s_atop stS = ATOP) by exact (rregions_wf_atop _ (proj1 MR4)).
  assert (RECS : forall q, get_meta_rec stS q = get_meta_rec st2 q) by (intros q; rewrite ES; reflexivity).
  assert (ACTS : forall c', active stS c' = active st2 c') by (intros c'; unfold active; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (HS _)); reflexivity).
  assert (BRKS : c_brk (ctx stS) = c_brk (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (HS _))))).
  assert (CTRS : c_mmap_counter (ctx stS) = c_mmap_counter (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (HS _)))))).
  assert (FMHS : c_free_meta_head (ctx stS) = c_free_meta_head (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (proj2 (HS _))))))).
  assert (CONCS : forall q, conc stS q = conc st2 q) by (intros q; unfold conc, get_region; rewrite REGS; reflexivity).
  assert (MSLS : meta_slot stS mm) by (eapply meta_slot_same_areas; [exact ARS| exact MSL]).
  assert (TKS : ticks_ok stS) by (eapply ticks_ok_same; [exact SHS| exact TKS'| exact TK3]).
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR as (WF & _). pose proof WF as (RS0 & WR0 & DJ0 & _).
  destruct ans as [e|xa].
  -
    cbn [rmmap_anon_post] in PO.
    destruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He).
    cbn [mmap_val]. unfold mm_after. fold stS. rewrite ATS. destruct (mmap_answer_ok_err (live_ranges stS) nd e He) as [-> ->]. cbn [negb].
    rewrite as_free_meta_eq. cbn [as_kq].
    rewrite SP' in MU6, ST6. rewrite EA in MU6.
    replace (ret_pc (Z_to_bv 64 0x23020)) with (Z_to_bv 64 0x23020) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rwrapper_munch_keeps stS m4 m6 (bv_unsigned sp - 144) lo MR4); [| exact WM6| atop_facts; lia].
      eapply munch_weaken; [| exact MU6]. intros y; cbn; lia. }
    pose proof (lf_freelist _ (isf_lf _ _ F2)) as FFL. change (fact_freelist (strip st2)) with (fact_freelist st2) in FFL.
    assert (FL : forall h, c_free_meta_head (ctx stS) = Some h ->
              meta_slot stS h /\ h <> mm /\ exists p, m_prev (get_meta_rec stS h) = Some p /\ meta_slot stS p /\ p <> mm).
    { intros h Hh. rewrite FMHS in Hh. destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp).
      change (meta_slot (strip st2) h) in MSh. change (get_meta_rec (strip st2) h) with (get_meta_rec st2 h) in MEMh, NXh, HP.
      change (meta_slot (strip st2) p) in MSp. change (get_meta_rec (strip st2) p) with (get_meta_rec st2 p) in MEMp, NXp.
      split; [eapply meta_slot_same_areas; [exact ARS| exact MSh]|].
      split; [intros ->; rewrite G0 in NXh; apply NXh; reflexivity|].
      exists p. rewrite RECS. split; [exact HP|]. split; [eapply meta_slot_same_areas; [exact ARS| exact MSp]|].
      intros ->. rewrite G0 in NXp. apply NXp. reflexivity. }
    riprefixT.
    eapply evt_cut. { eapply rmm_ret_fail_walk. }
    cbv beta. intros ms' ->.
    eapply evt_cut. { rewrite <- (CONCS mm). subst sp'. unfold rFRM in FR6. eapply (rfailm2_walk stS mm MSLS FL); [exact MR6| exact MI6| exact FR6| lia]. }
    cbv beta. intros ms' (s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7).
    assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW stS mm (bv_unsigned sp))).
    { eapply (rfailW_low stS mm m6 _ MR6 MSLS). intros h Hh. destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _).
      split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
    assert (ST7 : stk usegs m7 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [exact ST6| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]]. }
    assert (ERR7 : rw_cells usegs m7 (errno_addr tp) [C4 (Z_to_bv 64 (MM_syscalls.mmap_fix_errno e))]).
    { eapply rw_cells_transport; [exact ERR6| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
    eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
    cbv beta. intros ms' (a1y & a2y & -> & ST8). apply evt_done.
    set (stF := as_fm_st stS mm) in *.
    destruct (fm_proj stS mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
    assert (FS : Forall (rmetaW (bv_unsigned sp) stS) (rfailW stS mm (bv_unsigned sp))).
    { apply (rfailW_shape stS mm _ MSLS). intros h Hh; destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
    assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
    { eapply rpres_except_trans.
      - eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr. exists r. rewrite PF1, REGS. repeat split; auto; lia.
      - eapply rpres_except_trans.
        + eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros X; apply NC; left; [left; lia| right; left; rewrite unsigned_lit by lia; lia].
        + eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
          intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          * cbn in E1, E2. subst lo' hi'. left. do 3 right.
            assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
            destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
            exists rid0, r0. split; [exact H0|]. split; [exact K0|].
            assert (EC : conc stF q = conc stS q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
          * inversion E; subst. left. right. right. left. unfold RCTX in *. atop_facts. lia.
          * inversion E; subst. left. left. lia. }
    apply HK. unfold ras_post2.
    do 14 eexists. exists m7, (Z_to_bv 64 (MM_syscalls.mmap_fix_errno e)). split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
    split; [exact MR7|].
    split; [eapply ticks_ok_same; [rewrite PF2; exact SHS| rewrite PF6; exact TKS'| exact TK3]|].
    split. { eapply (unk_agree_xfer o st2 m3 stF m7 UA3).
      - rewrite PF2. exact SHS.
      - intros rid r Hk Hr. rewrite PF1, REGS in Hr. exact Hr.
      - intros b. rewrite PF3, GRS. split; intros X; exact X.
      - intros rid r off h Hr Hk Ho Hc NG.
        pose proof MR3 as (WF3 & _). pose proof WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). atop_facts.
        destruct (rregion_facts st2 m3 rid r MR3 Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
        transitivity (m6 (wa (r_base r + off))).
        { apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
          pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          - cbn in E1, E2. subst lo' hi'. rewrite CONCS in Ha.
            assert (MSq2 : meta_slot st2 q) by (eapply meta_slot_same_areas; [symmetry; exact ARS| exact MSq]).
            destruct (rmeta_chunk_facts st2 m3 q MR3 MSq2) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
          - inversion E; subst. unfold RCTX in Ha. lia.
          - inversion E; subst. lia. }
        transitivity (m4 (wa (r_base r + off))).
        { apply MU6. rewrite wa_unsigned by lia. cbn. lia. }
        apply MU4. rewrite wa_unsigned by lia. unfold rseqW, RCTX. cbn. lia. }
    split; [exact PE07|].
    split. { split; [| rewrite PF7, NRS, <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite PF8, RSS, (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
             intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. rewrite PF1, REGS. auto. }
    split. { unfold brk_link_ps in *. rewrite PF11, BRKS. destruct (c_brk (ctx st2)) as [| |rid off]; auto.
             unfold conc, get_region. rewrite PF1, REGS. exact BL2. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite PF9, ACTS, (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ARS. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF6, TKS', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split; [rewrite PF12, CTRS; exact FC1|].
    left. reflexivity.
  -
    cbn [rmmap_anon_post] in PO.
    destruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & AOK).
    cbn [mmap_val]. unfold mm_after. fold stS. rewrite ATS.
    destruct (mmap_answer_ok ATOP (live_ranges stS) nd xa) eqn:VOK. 2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    destruct (mmap_answer_ok_addr (live_ranges stS) nd xa ltac:(lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
    rewrite SP' in MU6, ST6.
    assert (RU : round_up_pg nd = nd) by (unfold round_up_pg; change (PGSZ - 1) with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; (Z.div_mod_to_equations; lia)).
    rewrite RU in XC, XRF.
    assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rmrep_transport_high stS m4 m6); [exact MR4| exact MU6| exact WM6| intros lo' hi' [E|[]]; inversion E; atop_facts; lia]. }
    unfold new_region.
    set (rid := s_next_rid stS). set (r0 := {| r_kind := RKGroup; r_base := xa; r_len := nd |}).
    set (stN := set_next_rid (N.succ rid) (set_regions (<[rid:=r0]> (s_regions stS)) stS)).
    assert (EstN : stN = fst (new_region RKGroup xa nd stS)) by reflexivity.
    pose proof (mf_ptrs _ _ MF2) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) stS).
    { rewrite ES. apply ptrs_in_upd_ctx_scalar; try (intros cc; pose proof (HS cc) as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); assumption).
      eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. rewrite NRS. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; rewrite NRS; lia)) as [FRr FRs].
    unfold MM_syscalls.mmap_raw in ST6 |- *. cbn [negb] in ST6 |- *. rewrite mmap_len_round_up, RU in ST6 |- *.
    atop_facts.
    set (mz := apply_zeros m6 [(wa xa, Z_to_bv 64 nd)]) in *.
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + nd <= a) -> mz (wa a) = m6 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + nd -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : rmrep stN mz).
    { rewrite EstN. eapply (rmrep_new_region stS m6 mz xa nd RKGroup MR6 PT1 ltac:(rewrite SHS; exact FRs) X0 XA ltac:(lia));
        rewrite ?mmap_len_round_up, ?RU; [atop_facts; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    pose proof MR6 as (WF6 & _). pose proof WF6 as (RS6 & WR6 & DJ6 & _).
    assert (XI : xa + nd <= 0x10000 \/ 0x5d000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa nd = true).
      { apply ranges_free_intro. intros b kk HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite (rstatics_reserved _ RS6). exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv usegs mz).
    { unfold mz. apply (mem_inv_zeros usegs m6 xa nd); try lia; [exact MI6|]. intros w Hw. apply ref_ro_addr_false. lia. }
    assert (MUz : munch [(xa, xa + nd)] m6 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono usegs m6 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono usegs m6 xa nd); try lia; exact Hw).
    assert (FRz : rw_cells usegs mz (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR6| exact MUz| exact WMz|]. cbn. lia. }
    assert (STz : stk usegs mz lo (bv_unsigned sp + -144)) by exact ST6.
    assert (ERRz : rw_cells usegs mz (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [exact ERR6| exact MUz| exact WMz|]. rewrite EA. cbn. lia. }
    assert (MSLN : meta_slot stN mm) by (eapply meta_slot_same_areas; [| exact MSLS]; rewrite EstN; reflexivity).
    assert (RECN : get_meta_rec stN mm = meta0) by (rewrite EstN; change (get_meta_rec (fst (new_region RKGroup xa nd stS)) mm) with (get_meta_rec stS mm); rewrite RECS; exact G0).
    assert (CTRN : c_mmap_counter (ctx stN) = c_mmap_counter (ctx st2)) by (rewrite EstN; change (ctx (fst (new_region RKGroup xa nd stS))) with (ctx stS); exact CTRS).
    assert (GCN : conc stN mm = conc st2 mm).
    { rewrite <- CONCS. rewrite EstN. apply nr_conc. cbn [fst].
      destruct MSLS as (ar & arr & kk & Ha & Hk & ->). unfold aadd. cbn [fst]. intros E.
      destruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ Ha) as [X _]. exact (X E). }
    replace (ret_pc (Z_to_bv 64 0x23020)) with (Z_to_bv 64 0x23020) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    riprefixT.
    eapply evt_cut.
    { rewrite <- GCN. subst sp'. assert (XA2 : xa + nd <= ATOP) by (atop_facts; lia).
      eapply (rmm_ret_ok_walk stN sc c size nd xa (c_mmap_counter (ctx st2)) mm SC ltac:(lia) SZ ltac:(lia) NDM X0 XA2 MSLN RECN CTRN FC1);
        [exact MRz| exact MIz]. }
    cbv beta. intros ms' (xa3 & xa4 & m8 & -> & MU8 & WM8 & MI8 & MR8 & CTR8).
    set (stT := mm_st4 stN nd mm) in *.
    assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (ML : 0 <= Z.shiftr nd 12 < 2^52) by (rewrite ND12; (Z.div_mod_to_equations; lia)).
    assert (RECT : get_meta_rec stT mm = {| m_prev := None; m_next := None; m_mem := None; m_avail := 0; m_freed := 0; m_last_idx := 0; m_freeable := 0; m_sizeclass := 0; m_maplen := Z.shiftr nd 12 |}).
    { unfold stT, mm_st4. rewrite rec_upd_ctx. unfold upd_meta. rewrite get_meta_rec_put_same, RECN. unfold m_set_maplen, meta0. cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass].
      f_equal. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (HrT : (s_regions stT) !! rid = Some r0) by (unfold stT, mm_st4, upd_meta; cbn; first [apply lookup_insert_eq | rewrite EstN; apply nr_lookup_new]).
    assert (GNT : forall off, (s_groups stT) !! (rid, off) = None).
    { intros off. change (s_groups stT) with (s_groups stS). destruct ((s_groups stS) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
      destruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
    assert (SHT : (s_shadow stT) !! rid = None) by (change (s_shadow stT) with (s_shadow stS); rewrite SHS; exact FRs).
    assert (ACTT : active stT sc = None).
    { unfold stT, mm_st4. unfold active, ctx, upd_ctx, upd_meta. cbn. change (c_active (s_ctx stS) !! sc) with (active stS sc). rewrite ACTS, (amr_active _ _ _ REL). exact ACT0. }
    assert (TKT : ticks_ok stT).
    { eapply ticks_ok_same; [| | exact TK3]; [change (s_shadow stT) with (s_shadow stS); exact SHS| change (s_tick stT) with (s_tick stS); exact TKS']. }
    pose proof (mm_ai_range stN c size nd mm ltac:(lia) SZ) as AIR.
    eapply evt_cut.
    { replace (Z_to_bv 64 xa) with (Z_to_bv 64 (conc stT (rid, 0))) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; f_equal; lia).
      change (conc stN mm) with (conc stT mm).
      eapply (rtail_walk stT sc c (mm_ai c size) (Z.shiftr nd 12) mm (rid, 0) r0 SC ltac:(lia) AIR ML);
        [eapply meta_slot_same_areas; [| exact MSLN]; reflexivity| exact RECT| exact HrT| reflexivity| cbn; lia| cbn; reflexivity
        | cbn [snd r_len r0]; rewrite RU; lia| apply GNT
        | intros b' gh Hb' Hf'; exfalso; destruct b' as [b1 b2]; cbn in Hf'; subst b1; rewrite GNT in Hb'; discriminate
        | intros o' v t Ho Hc; exfalso; unfold get_shadow in Hc; rewrite SHT in Hc; cbn in Hc; rewrite lookup_empty in Hc; discriminate
        | change (usage stT sc) with (usage stS sc); rewrite US; apply URall
        | exact ACTT| exact TKT| exact MR8| exact MI8]. }
    cbv beta. intros ms' (s0x & a1x & a2x & a3x & a4x & m9 & -> & MU9 & WM9 & MI9 & MR9 & TK9).
    assert (GT : conc stT mm = conc st2 mm) by (change (conc stT mm) with (conc stN mm); exact GCN).
    assert (PT : conc stT (rid, 0) = xa) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; lia).
    assert (FR9 : rw_cells usegs m9 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; atop_facts; lia].
      eapply rw_cells_transport; [exact FRz| exact MU8| exact WM8|]. rewrite GCN. unfold RCTX. cbn. atop_facts. lia. }
    assert (ST9 : stk usegs m9 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; atop_facts; lia].
      eapply stk_transport_disjoint; [exact STz| exact MU8| exact WM8| rewrite GCN; unfold RCTX; cbn; atop_facts; lia]. }
    eapply evt_cut. { unfold rFRM in FR9. eapply (ras_ret0 sp gp tp); [exact MR9| exact MI9| exact FR9| exact ST9| exact CLO| lia]. }
    cbv beta. intros ms' (a1y & a2y & -> & ST10). apply evt_done.
    rewrite (ag_tail_kq_eq sc k bail stT mm (rid, 0) c (mm_ai c size)); [| rewrite RECT; reflexivity| rewrite RECT; reflexivity| exact ACTT].
    apply HK.
    set (ai := mm_ai c size) in *. set (ml := Z.shiftr nd 12) in *.
    set (stF := st_model stT sc c ai mm (rid, 0)).
    assert (C32 : 1 <= c <= 32) by lia.
    assert (EML : nd = 4096 * ml) by (subst ml; rewrite ND12; (Z.div_mod_to_equations; lia)).
    assert (ML28 : 1 <= ml < 2^28) by lia.
    assert (Hk0 : r_kind r0 = RKGroup) by reflexivity.
    assert (LEN0 : r_len r0 = nd) by reflexivity.
    assert (MST : meta_slot stT mm) by (eapply meta_slot_same_areas; [| exact MSLN]; reflexivity).
    assert (Esz : size = 16 * size_class sc) by reflexivity.
    assert (NDC' : c = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * c + 16 <= nd /\ nd < 16 * size_class sc * c + 16 + 4096).
    { pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 _]. pose proof (round_up_pg_props (size * c + 16) ltac:(nia)) as [N1 _].
      rewrite <- Esz. destruct NDC as [[Ec En]|[LE En]]; [left; split; [exact Ec| rewrite En; lia] | right; split; [exact LE| rewrite En at 1; lia]]. }
    destruct (sm_slot_ok stT sc c ai ml mm rid r0 SC C32 AIR ML28 RECT HrT Hk0 SHT GNT req nd RQ FIT LEN0 EML NDR ltac:(lia) NDC' MST) as (SO & STR & S16 & SND).
    fold stF in SO, STR, S16, SND.
    pose proof (sm_proj stT sc c ai mm rid) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10).
    fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
    assert (MRF : rmrep stF m9) by (exact (rmrep_st_model stT sc c ai ml mm (rid, 0) SC C32 RECT ltac:(cbn; lia) m9 MR9)).
    assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK9]; reflexivity).
    assert (MSF : meta_slot stF mm) by (apply (proj1 (sm_meta_slot stT sc c ai mm rid mm)); exact MST).
    assert (REGT : s_regions stT = <[rid:=r0]> (s_regions stS)) by reflexivity.
    assert (SHT' : s_shadow stT = s_shadow st2) by (transitivity (s_shadow stS); [reflexivity| exact SHS]).
    assert (GRT : s_groups stT = s_groups st2) by (transitivity (s_groups stS); [reflexivity| exact GRS]).
    assert (ART : s_areas stT = s_areas st2) by (transitivity (s_areas stS); [reflexivity| exact ARS]).
    assert (TKT' : s_tick stT = s_tick st2) by (transitivity (s_tick stS); [reflexivity| exact TKS']).
    assert (NRT : s_next_rid stT = N.succ rid) by reflexivity.
    assert (RST : s_reserved stT = s_reserved st2) by (transitivity (s_reserved stS); [reflexivity| exact RSS]).
    assert (BRKT : c_brk (ctx stT) = c_brk (ctx st2)) by (transitivity (c_brk (ctx stS)); [reflexivity| exact BRKS]).
    assert (ACTT' : forall c', active stT c' = active st2 c') by (intros c'; transitivity (active stS c'); [reflexivity| apply ACTS]).
    assert (GF : conc stF mm = conc st2 mm) by (rewrite (sm_conc stT sc c ai mm rid); exact GT).
    assert (HOLD : forall q rq, (s_regions st2) !! q = Some rq -> (s_regions stF) !! q = Some rq /\ q <> rid).
    { intros q rq Hq. assert (NE : q <> rid) by (intros ->; rewrite FRr in Hq; discriminate).
      split; [| exact NE]. rewrite PF1, REGT, lookup_insert_ne, REGS by congruence. exact Hq. }
    assert (MREL0S : forall q rq, (s_regions st0) !! q = Some rq ->
              exists r', (s_regions stS) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
    { intros q rq Hq. destruct (mrel_regions _ _ (er_mrel _ _ ER) q rq Hq) as (r1 & H1 & K1 & B1 & L1). rewrite <- REG1 in H1.
      destruct (amr_regions _ _ _ REL q r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. rewrite REGS. repeat split; auto; try congruence. lia. }
    assert (FRESH : forall a, xa <= a < xa + nd -> fresh_addr st0 a).
    { intros a Ha. eapply (fresh_addr_anti st0 stS); [| exact MREL0S|].
      - rewrite (rstatics_reserved _ RS6), <- (rstatics_reserved _ RS0). exact (mrel_reserved _ _ (er_mrel _ _ ER)).
      - split; [atop_facts; lia|]. eapply (ranges_free_sub _ xa nd); [exact XRF| lia| lia| lia]. }
    assert (HFP2 : forall a, rmalloc_fp st0 st2 lo (bv_unsigned sp) a -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
    { intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros q rq Hq. exists rq. split; [apply (proj1 (HOLD q rq Hq))|]. repeat split; auto. lia. }
    assert (OLDW : forall q rq off, (s_regions st2) !! q = Some rq -> r_kind rq = RKGroup -> 0 <= off < round_up_pg (r_len rq) ->
              m9 (wa (r_base rq + off)) = m3 (wa (r_base rq + off))).
    { intros q rq off Hq Hk Ho.
      assert (HqS : (s_regions stS) !! q = Some rq) by (rewrite REGS; exact Hq).
      destruct (WR6 _ _ HqS) as (R0 & _ & _ & RC & _). atop_facts.
      destruct (rregion_facts st2 m3 q rq MR3 Hq) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      destruct (rmeta_chunk_facts st2 m3 mm MR3 MSL) as (_ & _ & _ & _ & _ & GRG & _). pose proof (GRG q rq Hq Hk) as GRq.
      pose proof (In_live_ranges stS q rq HqS) as HIq. unfold region_live_range in HIq. rewrite Hk in HIq.
      pose proof (ranges_free_In _ _ _ _ _ XRF HIq) as DJq.
      pose proof (lr_lo_group rq Hk) as LRq.
      transitivity (m8 (wa (r_base rq + off))). { apply MU9. rewrite wa_unsigned by (clear - Ho R0 RC; lia). unfold rtailW. rewrite GT, PT. cbn. unfold RCTX. clear - Ho R0 RC RI2 GRq DJq SC SND S16; lia. }
      transitivity (mz (wa (r_base rq + off))). { apply MU8. rewrite wa_unsigned by (clear - Ho R0 RC; lia). rewrite GCN. cbn. unfold RCTX. clear - Ho R0 RI2 GRq; lia. }
      transitivity (m6 (wa (r_base rq + off))). { apply ZO; [clear - Ho R0 RC; lia | clear - Ho R0 DJq; lia]. }
      transitivity (m4 (wa (r_base rq + off))). { apply MU6. rewrite wa_unsigned by (clear - Ho R0 RC; lia). cbn. clear - Ho R0 RC CLO' LO ASG; lia. }
      apply MU4. rewrite wa_unsigned by (clear - Ho R0 RC; lia). unfold rseqW, RCTX. cbn. clear - Ho R0 RI2; lia. }
    assert (UAF : unk_agree stF o m9).
    { eapply (unk_agree_transfer st2 stF o m3 m9 UA3). intros q rq Hq Hk.
      rewrite PF1, REGT, REGS in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      - right. rewrite lookup_insert_eq in Hq. inversion Hq; subst rq. cbn [r_len r_base]. intros off h Ho Hc.
        rewrite (sm_cell_read stT sc c ai mm rid SHT off ltac:(lia)) in Hc.
        destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T. apply (sm_grp_hdr_cov stT sc c ai mm rid SC). lia.
      - left. rewrite lookup_insert_ne in Hq by congruence.
        split; [exact Hq|].
        split. { rewrite (sm_shadow_other stT sc c ai mm rid q NE). unfold get_shadow. rewrite SHT'. reflexivity. }
        split. { intros off X. apply (sm_grp_hdr_cov_old stT sc c ai mm rid GNT). eapply rgrp_hdr_cov_same; [exact GRT| exact X]. }
        intros off h Ho Hc NG. exact (OLDW q rq off Hq Hk Ho). }
    assert (PE09 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m9).
    { eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE04| exact HFP2]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. left. left. lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. do 4 right. apply FRESH. lia. }
      eapply rpres_except_trans.
      { eapply rpres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. rewrite GCN. cbn. split; [|split; [|exact I]]; intros X; apply NC.
        - left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
          exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
        - left. right. right. left. unfold RCTX in *. atop_facts. lia. }
      eapply rpres_except_of_munch; [exact MU9| exact WM9|]. intros a Ha NC. unfold rtailW. rewrite GT, PT. cbn.
      split; [|split; [|split; [|split; [|exact I]]]]; intros X; apply NC.
      - left. right. right. left. unfold RCTX in *. atop_facts. lia.
      - left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
        exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
      - do 4 right. apply FRESH. lia.
      - left. right. right. left. unfold RCTX in *. atop_facts. lia. }
    assert (ERR9 : rw_cells usegs m9 (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [| exact MU9| exact WM9|].
      - eapply rw_cells_transport; [exact ERRz| exact MU8| exact WM8|]. rewrite EA, GCN. cbn. unfold RCTX. lia.
      - unfold rtailW. rewrite GT, PT, EA. cbn. unfold RCTX. lia. }
    unfold ras_post2.
    do 14 eexists. exists m9, errv'. split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST10|]. split; [exact ERR9|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m9); [exact MRF| exact AUX| exact PE09| exact CLO| lia]|].
    split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE09|].
    split. { split.
      - intros q rq Hq. rewrite <- REG1 in Hq. destruct (amr_regions _ _ _ REL q rq Hq) as (r' & H' & K' & B' & L' & _).
        exists r'. split; [apply (proj1 (HOLD q r' H'))|]. repeat split; auto.
      - rewrite PF6, NRT. pose proof (amr_next_rid _ _ _ REL) as NX1. pose proof (tr_next _ _ _ TR) as NX0. subst rid. rewrite NRS. lia.
      - rewrite PF7, RST, (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
    split. { unfold brk_link_ps in BL2 |- *. rewrite PF8, BRKT. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:EB; auto.
             rewrite (sm_conc stT sc c ai mm rid). rewrite <- (CONCS (brid, boff)) in BL2.
             replace (conc stT (brid, boff)) with (conc stS (brid, boff)); [exact BL2|].
             change (conc stT (brid, boff)) with (conc stN (brid, boff)). rewrite EstN. symmetry. apply nr_conc. cbn [fst].
             destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite BRKS in P7. first [rewrite EB in P7; exact P7 | exact P7]. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite (sm_active stT sc c ai mm rid). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite ACTT', (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ART. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF5, TKT', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros _ rid' S len RS o' v t Ho Hc. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        rewrite (sm_cells_none stT sc c ai mm rid SHT) in Hc. discriminate.
      - intros _ _ rid' S len RS o' Ho. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        split; [apply (sm_cells_none stT sc c ai mm rid SHT)|].
        split; [apply (sm_hav_none stT sc c ai mm rid SHT); lia| apply (sm_havp_none stT sc c ai mm rid SHT)]. }
    split. { rewrite PF9, CTR8. unfold u32. (Z.div_mod_to_equations; lia). }
    right. split; [lia|]. exists mm, (rid, 0), r0.
    split; [rewrite (sm_active stT sc c ai mm rid), Z.eqb_refl; reflexivity|]. split; [exact SO|]. split.
    + intros a Ha. replace (r_base r0) with xa in Ha by reflexivity. cbn [fst snd] in Ha. do 4 right. apply FRESH. rewrite Z.mul_0_r in Ha. lia.
    + intros _. cbn [fst snd]. replace (0 + (16 + get_stride (get_meta_rec stF mm) * 0) + -3) with 13 by lia.
      apply (sm_rdv stT sc c ai mm rid SHT).
Qed.
End LEVEL.
End CANSEC1.
