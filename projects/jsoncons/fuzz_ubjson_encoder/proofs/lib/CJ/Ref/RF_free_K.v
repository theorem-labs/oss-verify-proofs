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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free MallocBlocks MallocFacts_B MallocKit_B MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Export F_free_K.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_free_K () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C35stdpp4base6lookupI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_delete_neC47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8ticks_okC13~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8F_free_K6hdr_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B8rfree_fpC13~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes6option00C47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~K47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8F_free_KAhdr_st_known_backC13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~I47Corelib7Numbers7BinNums1Z00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree7optr_inC13~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_K:rconc_dropC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~I47Corelib4Init5Logic4True00C47Corelib4Init9Datatypes2idC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRepAget_shadow_unfoldC13~~~C35stdpp6option;from_optionC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7shadow0C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_free_meta_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<c_avail_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6a_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6g_metaC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_wordC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_K8rpw_dropC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_head_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;c_init_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>c_mmap_counterC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_meta_alloc_shiftC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7map_extI47Corelib4Init9Datatypes3nat00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_tail_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5zerosC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~C35stdpp8fin_mapsBlookup_delete_SomeC47Corelib4Init5Logic7and_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr6u64arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:unmap_seqsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8bouncessC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rarea_repC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7a_checkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8a_nslotsC13~~~C56Stdlib6ZArith6BinInt1Z3mulC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_K@rmeta_cells_dropC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_K9rrec_dropC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:rgroup_repC13~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<g_active_idxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rshadow_repC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_K@rget_shadow_dropC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8AREA_HDRC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<ref_reservedC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_KDrctx_tail_cells_dropC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_K=ractives_dropC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_KDrctx_head_cells_dropC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9META_SIZEC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres4KINV00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres4ZINVC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B8ci_mptrsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B6ng_ptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree7ptrs_inC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres8ki_linksC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B:ci_links_t00C13~~~C47Corelib4Init5Logic3iffC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B5is_gmC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres>kinv_free_headC13~~~C47Corelib4Init5Logic5proj1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_sizeclassC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres;kinv_activeC13~~~C47Corelib4Init5Logic5proj2K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate03C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres5ki_bkC13~~~C47Corelib4Init5Logic8eq_transC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B5hostsC13~~~C46Stdlib5Lists4List2InK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres7ki_grpsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres9ki_gmetasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B7go_slotC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks5blockC13~~~K47Corelib4Init5Logic4True01K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate02C13~~~". Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
#[using="Type"] Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

#[using="Type"] Lemma rdrop_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
#[using="Type"] Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q.
Proof. reflexivity. Qed.

#[using="PTR"] Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

#[using="PTR"] Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma ractives_drop : actives st' = actives st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
#[using="PTR"] Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

#[using="PTR"] Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof.
  intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

#[using="Type"] Lemma rptrs_in_norid st2 LB c rid r m :
  KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
  ci_mptrs st2 ->
  ptrs_in (fun x => x <> rid) st2.
Proof.
  intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.
End CEIL_WRAP_1.


