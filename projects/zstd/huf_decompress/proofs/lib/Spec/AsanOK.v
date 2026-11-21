(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (15 recorded proofs replaced by written proofs (AI_perm, AI_so, AI_model and 12 more); AI_perm, AI_model and AI_fds destructure this file's AI, whose allocator conjuncts sit in a second group; asan_ok_malloc, aannotate_core, asan_ok_annot and asan_ok_free go through this unit's amalloc_core, poison0_ok and afree_core). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ModelX MmXfer NodesA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree Stdio AsanCtrl AsanCtrlProps SizeHist Gap AsanEmbed AsanProgDeps
  AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree StepB RSim RSimProg EquivPA.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanOK () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_lengthC35stdpp8fin_maps:map_deleteC47Corelib4Init9Datatypes6lengthC35stdpp8fin_maps;map_to_listC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC46Stdlib5Lists4List8map_consC35stdpp4gmap;gmap_finmapC35stdpp4base6LookupC35stdpp4base6DeleteC46Stdlib5Lists4List7map_mapC35stdpp4base?list_elem_of_InI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC35stdpp4gmap:gmap_emptyI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib4Spec6AsanOK2AIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_atopC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec<AsanProgDeps5aps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv3INVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK:live_pairsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec7AsanInv5FAINVC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib4Spec6AsanOK3VCBC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;PermutationAPermutation_transK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC59OSSVerify5KrLib4Spec7AsanInv2VCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv4NOPSC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4Spec<AsanProgDeps7aset_soC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec<AsanProgDeps3APS01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA5minvAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC59OSSVerify5KrLib4Spec7AsanInv4AINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv2CHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv3AMIC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedI47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib4Spec7AsanInv4zlenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC59OSSVerify5KrLib4Spec7AsanInv8entry_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC59OSSVerify5KrLib2AS>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyI59OSSVerify5KrLib4Spec7AsanInv4seps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv7atop_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC59OSSVerify5KrLib4Spec7AsanInv;noacc_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec7AsanInv5STARTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv2PmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra9sum_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv<commit_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec7AsanInv7LIMIT34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv6RES_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv4LEN0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv5RTOT0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv4wentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv6EAGER0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC59OSSVerify5KrLib4Spec7AsanInv<AMI_with_fdsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib4Spec6AsanOK2FRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC59OSSVerify5KrLib3Lib5NodesCvm_only_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes<minv_vm_onlyC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib4Spec4RSim5tglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim4STOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim9STOT_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim8STOT_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim9STOT_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanNodeSem@atotal_STOT_asanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanNodeSem5apostC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK59OSSVerify5KrLib4Spec8AsanCtrl3aev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib4Spec7AsanInv;grant_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv;fixed_modelC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01c59OSSVerify5KrLib4Spec6AsanOKDFR_with_vmmaps_stripC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC59OSSVerify5KrLib4LibA6MmXferAstrip_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6MmXferKstrip_with_mmap_replacementC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyK59OSSVerify5KrLib4Spec8AsanCtrl3aev04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv<munmap_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedK59OSSVerify5KrLib4Spec8AsanCtrl3aev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK7FR_reflC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev07C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeK47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec8AsanCtrl3aev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aundef00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanTotalCore6atotalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanTotalCore;atotal_monoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanNodeSem3aokC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK8apost_FRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK8FR_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv;live_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:AsanBudget5sizesC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8SizeHist6HISTOKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8SizeHist3YWsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib4Spec8SizeHist3BCsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib4Init5Peano2le00C59OSSVerify5KrLib4Spec8SizeHist3N4sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8SizeHist4N24sC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec8SizeHist2HBC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec9AsanTotal;atot34_atotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec<AsanProgDeps6aps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanTotal8INV_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps5aliftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim8STOT_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanTotal;malloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec8AsanCtrl<sec_map_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanTotal4mkchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8class_idC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv8chunk_wfC1?~~~~~~~~~~~~~~~C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib6ZArith:ZArith_dec8Z_lt_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec=AsanCtrlPropsAlarge_not_primaryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib4Spec9AsanTotalAnot_primary_largeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanCtrlPropsCsec_map_size_boundsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3sum00C59OSSVerify5KrLib4Spec9AsanTotal4csigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv7cls_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv:all_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv8qbatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv4bsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec7AsanInv;live_budgetC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib4Spec7AsanInv7qchunksC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K46Stdlib7Sorting;Permutation;Permutation02c59OSSVerify5KrLib4Spec6AsanOK;HISTOK_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK@sizes_live_pairsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:AsanBudgetElive_budget_of_HISTOKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanTotalDlive_budget_list_sigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec9AsanTotal<amalloc_coreC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK9atotal_FRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aset_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim8STOT_updC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp8fin_mapsBmap_to_list_insertC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib4Spec<AsanProgDeps9amalloc_MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03C35stdpp4base6lookupK46Stdlib9micromega7EnvRing5PExpr05C35stdpp4base6insertC46Stdlib9micromega;ZifyClasses5mkappC59OSSVerify5KrLib4LibA6NodesA6nstepAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec7AsanInv8batch_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>K_CHUNKS_BLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg6REQMAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv5ACEILC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv8ATOP_MAXC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec7AsanInv5LS_LOC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec7AsanInv5KHIGHC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib4Spec7AsanInv5VCMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv3VC0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List:in_map_iffI35stdpp4base<list_elem_of00C35stdpp4base7elem_ofC35stdpp8fin_mapsCelem_of_map_to_listC59OSSVerify5KrLib4Spec8AsanCtrl9aannotateC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec8AsanCtrl7aundef_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbK59OSSVerify5KrLib4Spec8AsanCtrl6aundef04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec8AsanCtrl3rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec9AsanTotal5aok34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanTotalCore:atotal_retC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z8min_specC59OSSVerify5KrLib4Spec9AsanTotal6rdn_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanTotal?sec_map_size_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib4Spec7AsanInv8bsum_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv4secsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv8secbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:AsanBudget9CH_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv5zsum2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanTotal:poison0_okC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>chunk_user_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7poison0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aundef05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec8AsanCtrl2PGC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aundef02C1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inc59OSSVerify5KrLib4Spec6AsanOK=live_pairs_InC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK>aannotate_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aannot_MC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanFree9free_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanFree:afree_coreC1?~~~~~~~~~~~~~~~C35stdpp8fin_mapsBmap_to_list_deleteC46Stdlib7Sorting;PermutationDPermutation_cons_invC47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib4Spec<AsanProgDeps7afree_MC1?~~~~~~~~~~~~~~~C35stdpp4base6deleteC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZK59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC59OSSVerify5KrLib3Lib5Nodes4eff0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes6efferrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeK47Corelib4Init5Logic2or02C59OSSVerify5KrLib4LibA6ModelX>strip_with_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX;m_fds_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFC59OSSVerify5KrLib4Spec8RSimProg7io_nodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX>m_halted_stripC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatK4ELinuxProcessSemantics?LinuxProcessSem5State5event02K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA@nstep_open_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>minv_preservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA@nstep_open_shapeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK<mat_with_fdsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA@nstep_read_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA@nstep_read_shapeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOKAnstep_close_stripC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC59OSSVerify5KrLib4LibA6ModelX>strip_with_tidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK<mat_with_tidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK?halted_with_tidC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOTTYK59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB7nf_nodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK3AIWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK7AI_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK5AI_soC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK8AI_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK6AI_fdsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK>asan_ok_mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK4PhiAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK<asan_ok_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6AsanOK=asan_ok_annotC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Notation atot a := (atotal (aok a) (apost a)) (only parsing).
Local Notation STOTA := (STOT (St:=APS) nstepA (fun R0 => texit (R:=R0) nstepA nexit)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition live_pairs (st : astate) : list (AsanCtrl.aptr * Z) :=
  map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (a_live st)).

(* [comment removed for export] *)
Definition VCB (a y : Z) : Z := VC0 + 2^19 * (2 * a + 1 - y).

Definition AI (Y : list (AsanCtrl.aptr * Z)) (s : APS) (mo : Model) : Prop :=
  (INV (aps_resv s) (aps_atop s) [] [] (aps_m s) mo
   /\ Permutation Y (live_pairs (aps_m s))
   /\ a_qloc_bytes (aps_m s) <= Q_CACHE /\ a_qglob_bytes (aps_m s) <= Q_MAX
   /\ minv (strip mo) /\ m_halted mo = None)
  /\ (FAINV (aps_m s) /\ Z.of_N (a_next (aps_m s)) <= NOPS
      /\ VC (aps_m s) <= VCB (Z.of_N (a_next (aps_m s))) (Z.of_nat (length Y))).   (* [comment removed for export] *)

Lemma AI_perm : forall Y Y' s mo, Permutation Y Y' -> AI Y s mo -> AI Y' s mo.
Proof.
  intros Y Y' s mo HP ((H1 & H2 & H3) & (G1 & G2 & G3)). split.
  - split; [exact H1|]. split; [|exact H3].
    eapply Permutation_trans; [apply Permutation_sym; exact HP| exact H2].
  - split; [exact G1|]. split; [exact G2|]. rewrite <- (Permutation_length HP). exact G3.
Qed.

Lemma AI_so : forall Y s mo v, AI Y s mo -> AI Y (aset_so v s) mo.
Proof. intros Y [m so rv atp] mo v H. exact H. Qed.

Lemma AI_model : forall Y s mo, AI Y s mo -> minvA mo /\ m_halted mo = None.
Proof. intros Y s mo ((HI & _ & _ & _ & Hmi & Hh) & _). split; [|exact Hh]. split; [exact Hmi|]. destruct HI as [_ (M1 & _)]. exact M1. Qed.

Lemma AI_fds : forall Y s mo f, AI Y s mo -> minvA (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI Y s (with_fds f mo).
Proof.
  intros Y s mo f ((HI & HP & Hq1 & Hq2 & Hmi & Hh) & HB) [Hmi' _] Hh'. unfold AI.
  split; [|exact HB].
  split; [| repeat (split; [assumption|]); assumption].
  destruct HI as [HA HM]. split; [exact HA|]. apply AMI_with_fds. exact HM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FR (mo mo' : Model) : Prop :=
  (minv (strip mo) -> minv (strip mo')) /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo.

Lemma FR_refl : forall mo, FR mo mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01Hh12mop;1p;2p;3p;4g00MUj16Tg00NKj15Tg00O>j10Tg00Ocj17Tg00PAj1?Tg00DYj2=Tg00E9j1<Tg01EJj1;Tg00R_j31Tg01F>j1:Tg00Pdj18Tg00QFj19Tg00S9j24Tg01G1j23Tg00W;j42Tg01GKj2>Tg00^[f0R0#6#5R1f1#6#5[g00aG#0#0#0#0#0#0#7#?R2g01DR'=#<R3%;0R4;14R5g0048R6%:0R7;17R8%82R2%90R9;19R:'4R;'4P0X01P5P;1334P8P:13671329C2C2C21>00eW1o"). Qed.
Lemma FR_trans : forall m1 m2 m3, FR m1 m2 -> FR m2 m3 -> FR m1 m3.
Proof. intros m1 m2 m3 (A1&A2&A3&A4) (B1&B2&B3&B4). unfold FR. split; [intros H; apply B1, A1, H|]. split; [congruence|]. split; congruence. Qed.

(* [comment removed for export] *)
Lemma FR_with_vmmaps_strip : forall mo mo' h, strip mo' = with_vmmaps h (strip mo) ->
  vm_init_sp h = vm_init_sp (m_vmmaps mo) ->
  m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> m_halted mo' = m_halted mo -> FR mo mo'.
Proof.
  intros mo mo' h Hs Hsp Hf Hfs Hh. unfold FR. split; [| split; [exact Hf| split; [exact Hfs| exact Hh]]].
  intros Hmi. rewrite Hs. eapply minv_vm_only; [apply vm_only_with_vmmaps; exact Hsp| exact Hmi].
Qed.

Lemma apost_FR : forall atop e mo z mo', apost atop e mo z mo' -> FR mo mo'.
Proof.
  intros atop e mo z mo' H. destruct e as [t|b|addr len prot flags|addr len|a l p|addr len|w]; cbn [AsanNodeSem.apost] in H; try contradiction.
  - destruct (addr =? 0).
    + destruct H as (_ & _ & _ & _ & ->). unfold grant_model. eapply FR_with_vmmaps_strip; try reflexivity.
    + destruct H as (_ & ->). unfold fixed_model. eapply (FR_with_vmmaps_strip _ _ (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)))).
      * rewrite strip_with_mmap_replacement. apply strip_with_vmmaps.
      * reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
  - destruct H as (_ & ->). unfold munmap_model. eapply FR_with_vmmaps_strip; try reflexivity.
  - (* [comment removed for export] *) destruct H as (_ & ->). apply FR_refl.
Qed.

Lemma atotal_FR : forall atop {R} (t : AM R) mo (Post : R -> Model -> Prop),
  atot atop t mo Post -> atot atop t mo (fun r mo' => Post r mo' /\ FR mo mo').
Proof.
  intros atop R t. induction t as [r|e k IH]; intros mo Post H; cbn in *.
  - split; [exact H| apply FR_refl].
  - destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp.
    eapply atotal_mono; [| apply IH; exact (Hk _ _ Hp)]. cbv beta. intros r mo'' [HP HF]. split; [exact HP|].
    eapply FR_trans; [apply (apost_FR _ _ _ _ _ Hp)| exact HF].
Qed.

(* [comment removed for export] *)
Lemma atotal_FR_gen : forall atop (ok : aev -> Model -> Prop) {R} (t : AM R) mo (Post : R -> Model -> Prop),
  atotal ok (apost atop) t mo Post -> atotal ok (apost atop) t mo (fun r mo' => Post r mo' /\ FR mo mo').
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h03mo'h11rh21zh34Posth42moh51Hh61th72HFh82HPh92Hkh:3Hokh;2Hph<2IHh=1Rh>4atoph?1eh@1khA4mo''hB2okp;1p;3p;6p;2p;4p;5p;9p;7p201R0g025_R1p4p73110p8P0g026XR2p4p710p8P0g027MR3p4p73110p8P0g028KR4p4p73110p8P2j1>Tg029Nj38Tg01Rmj12j54TP3j60Tg01GKj21Tg00S9R3j23Tg02;>j47Tg01odj1;Tg00W;j45Tg02<5j56Tg02<lj69Tg02=ej5:TP4l9=TP1j7<Tg00]AR1g023lR4g00^[R2p-0[R5[f0R6#>P4P1f1R7A8417f3R8P5[R9f5R:f6R;#2R<f4R=f2R>P7P6E0P;f7R?#2R@P:P8P>P8P7P6O211=6'3X02RAX1:RBE0[]3^42W6P:P<P=P4P1P=P>C7P7P6E0P7P8P>O211>>P6%;>C5P;P@P:P4P1P:P8C7P>PBE0eW5X39X42X17A8418\1P5\:R5P?f8R9#2RBP;P8P>O1P7P6E0P9f9R@#2R<P?P=P8O1P>PAX1?RAE0[]3^42\1P?PBP;P4P1P;P=P8D6P7P6E0P3P9P:P>O2f;RBP?P=P7P6D4PBf<RC#2f:RDP?P>O1P7P=E0[^02^21P@P;P8O2PCP9P:P7P6D4PCf=RE#2PBP9P>O1P7P?P7P6O21196'3X02X1BE0[^02^21'3P6PDP?P=O2f>RFPDP?P7P6D4PFf?RG#2PEPDP>O1P7P?E0[^02^21PCP@P;O2PGPBP9P7P6D4RHPGf@RI#2RJPFPBP>O1RKP7PDP7P6O2RL11B6'3X02X1FRME0[^02^21P7PGPJPFPKP71186,3LRLX02X1FPMP3PBP>P7O2RB11=7PCP8P>O211E>'3P6PEP=P8O211?=PGP;P:O211I:P7PIP9P:fGfCPIP@P9P?E9P6D:C5W7W8P7P6O2n2001000000120000000X5LXA2X1FPCP7P6O211:6'3X02X1IP7P6O211C7,3B[^02^1FePDP>P7P9P8P>P7P6O3O4M9=X;HX02X21C5W9W:P7P6O2n2001000000120000000P9P<P?P4P1P?P:P=D6P>PAE0eW5X35X42W<W@X?4P6F<W6X=0WBW>o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sizes_live_pairs : forall st, map snd (live_pairs st) = sizes (live_chunks st).
Proof. intros. unfold live_pairs, sizes, live_chunks. rewrite !map_map. reflexivity. Qed.

Lemma HISTOK_perm : forall M M', Permutation M M' -> HISTOK M -> HISTOK M'.
Proof.
  intros M M' HP (I & Zl & H1 & H2 & H3 & H4 & H5). exists I, Zl. split; [|auto].
  eapply Permutation_trans; [apply Permutation_sym; exact HP| exact H1].
Qed.

Theorem asan_ok_malloc : forall Y n s mo,
  AI Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  Z.of_N (a_next (aps_m s)) < NOPS ->                                     (* [comment removed for export] *)
  STOTA (amalloc_M n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AI ((q, n) :: Y) s' mo' /\ n < 2^63
                         /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                         /\ a_next (aps_m s') = N.succ (a_next (aps_m s))).
Proof.
  intros Y n [st so RESV ATOP] mo HAI Hn HH HCNT. pose proof HAI as [(HI & HPY & Hq1 & Hq2 & Hmi & Hh) (HFA & HAN & HVC)]. cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  unfold amalloc_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR.
    apply (atot34_atot (SBc:=a_space_beg st) (PAc:=a_ptr_array st)).
    apply (amalloc_core st mo n HI Hq1 Hq2 ltac:(unfold REQMAX in Hn; lia)).
    2:{ exact HFA. }
    2:{ unfold VCB, VCMAX, VC0, NOPS in *. pose proof (Nat2Z.is_nonneg (length Y)). lia. }
    2:{ split; reflexivity. }
    intros mb ms.
    set (dummy := mkch n 70368744177664 (sec_map_size n)).
    assert (Hwf : chunk_wf ATOP dummy).
    { unfold dummy, mkch. destruct (is_primary n) eqn:Hp.
      - cbn. split; [|reflexivity]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia].
      - cbn. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)).
        unfold KHIGH. unfold REQMAX in Hn. repeat split; try lia. }
    apply (live_budget_list_sig dummy). { unfold dummy, mkch. destruct (is_primary n); reflexivity. }
    apply (live_budget_of_HISTOK (ATOP:=ATOP)).
    + constructor; [exact Hwf|]. destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW.
      apply Forall_app in HW as [HWl _]. exact HWl.
    + unfold sizes. cbn [map]. replace (chunk_size dummy) with n by (unfold dummy, mkch; destruct (is_primary n); reflexivity).
      fold (sizes (live_chunks st)). rewrite <- sizes_live_pairs. eapply HISTOK_perm; [|exact HH]. apply perm_skip. apply Permutation_map. exact HPY. }
  cbv beta. intros [st' op] s2 mo2 (-> & (ch & Hop & HI2 & Hlive & Hnone & Hsz & Eq1 & Eq2 & Eq3 & Eq4 & HFA2 & HVC2 & Hnext) & HFR). cbn [fst snd] in *.
  eapply STOT_bind; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  eapply STOT_mono; [apply STOT_ret|]. cbv beta. intros r s4 mo4 (-> & -> & ->).
  exists (a_next st). subst op. split; [reflexivity|]. destruct HFR as (F1 & F2 & F3 & F4).
  split; [| split; [unfold REQMAX in Hn; lia| repeat split; auto; cbn; auto]].
  unfold AI. cbn [aps_m aset_m aps_so aps_atop aps_resv]. split; [| split; [exact HFA2| split]].
  2:{ rewrite Hnext, N2Z.inj_succ. lia. }
  2:{ cbn [length]. rewrite Hnext, N2Z.inj_succ, Nat2Z.inj_succ. unfold VCB in *. lia. }
  split; [exact HI2|]. split.
  - unfold live_pairs. rewrite Hlive.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply map_to_list_insert; exact Hnone].
    cbn [map fst snd]. rewrite Hsz. apply perm_skip. exact HPY.
  - rewrite Eq1, Eq2. split; [exact Hq1|]. split; [exact Hq2|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_pairs_In : forall st p cap, In (p, cap) (live_pairs st) -> exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = cap.
Proof.
  intros st p cap H. unfold live_pairs in H. apply in_map_iff in H as ([k ch] & E & Hin). cbn in E. injection E as -> <-.
  exists ch. split; [|reflexivity]. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin.
Qed.

(* [comment removed for export] *)
Theorem aannotate_core : forall RESV ATOP SBc PAc st mo p cap old new ch,
  INV RESV ATOP [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  (a_live st) !! p = Some ch -> chunk_size ch = cap ->
  0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  atotal (aok34 (ATOP:=ATOP) (SBc:=SBc) (PAc:=PAc)) (apost ATOP) (aannotate st p cap old new) mo (fun st' mo' => st' = st /\ INV RESV ATOP [] [] st mo').
Proof.
  intros RESV ATOP SBc PAc st mo p cap old new ch HI Hq1 Hq2 Hl Hsz Hold Hnew Hmin.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & _).
  assert (Hwf : chunk_wf ATOP ch).
  { unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HWl _]. unfold live_chunks in HWl.
    rewrite Forall_forall in HWl. apply HWl. apply in_map_iff. exists (p, ch). split; [reflexivity|].
    apply list_elem_of_In. apply elem_of_map_to_list. exact Hl. }
  assert (Hcap : 0 <= cap <= 2^30) by (subst cap; destruct ch; cbn in Hwf |- *; lia).
  unfold aannotate. rewrite Hl.
  replace (negb ((0 <=? old) && (old <=? cap) && (0 <=? new) && (new <=? cap))) with false.
  2:{ symmetry. rewrite (proj2 (Z.leb_le 0 old)), (proj2 (Z.leb_le old cap)), (proj2 (Z.leb_le 0 new)), (proj2 (Z.leb_le new cap)) by lia. reflexivity. }
  destruct (Z.ltb_spec (2^40) cap); [lia|].
  destruct (Z.eqb_spec old new) as [|Hne]; [apply atotal_ret; auto|].
  assert (Hrdn : 0 <= rdn cap 8) by (unfold rdn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  replace (rdn cap 8 <? Z.min old new) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
  destruct (Z.ltb_spec old new) as [Hlt|]; [|apply atotal_ret; auto].
  destruct ch as [c n|mb ms n]; [apply atotal_ret; auto|]. cbv zeta. cbn [chunk_user_beg].
  pose proof (rdn_le old 8 ltac:(lia)) as R1. pose proof (rdn_le new 8 ltac:(lia)) as R2.
  assert (R0 : 0 <= rdn old 8) by (unfold rdn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  destruct (Z.ltb_spec (rdn old 8) (rdn new 8)) as [Hab|]; [|apply atotal_ret; auto].
  cbn in Hwf. destruct Hwf as (Hn & -> & Hal & Hmb & Hrange). cbn in Hsz. subst cap.
  pose proof (sec_map_size_ge n ltac:(lia)) as SG.
  assert (Hrz : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity). rewrite Hrz. unfold PG.
  destruct (CH_bounds [] [] st HA) as [_ HCS].
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  { unfold zlen; cbn; lia. } { cbn; lia. }
  apply (@poison0_ok RESV ATOP SBc PAc _ _ [] [] st _ mo); auto; try lia.
  all: try (destruct Hrange as [Hlo|[Hh1 Hh2]]; [left; lia| right; lia]).
  intros mo' HI'. apply atotal_ret. auto.
Qed.

Theorem asan_ok_annot : forall Y q cap old new s mo,
  AI Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  STOTA (aannot_M q cap old new s) mo
        (fun _ s' mo' => AI Y s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                       /\ a_next (aps_m s') = a_next (aps_m s)).
Proof.
  intros Y q cap old new [st so RESV ATOP] mo HAI Hin Hold Hnew Hmin. pose proof HAI as [(HI & HPY & Hq1 & Hq2 & Hmi & Hh) HC]. cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (Hin' : In (q, cap) (live_pairs st)) by (eapply Permutation_in; [exact HPY| exact Hin]).
  destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
  unfold aannot_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR.
    apply (atot34_atot (SBc:=a_space_beg st) (PAc:=a_ptr_array st)).
    apply (aannotate_core RESV ATOP _ _ st mo q cap old new ch HI Hq1 Hq2 Hl Hsz Hold Hnew Hmin). }
  cbv beta. intros st' s2 mo2 (-> & [-> HI2] & (F1 & F2 & F3 & F4)).
  eapply STOT_mono; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  split; [| repeat split; auto; cbn; auto].
  unfold AI. cbn [aps_m aset_m aps_atop aps_resv]. split; [| exact HC].
  split; [exact HI2|]. split; [exact HPY|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem asan_ok_free : forall Y q n s mo,
  AI ((q, n) :: Y) s mo ->
  STOTA (afree_M q s) mo
        (fun _ s' mo' => AI Y s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                       /\ a_next (aps_m s') = a_next (aps_m s)).
Proof.
  intros Y q n [st so RESV ATOP] mo HAI. pose proof HAI as [(HI & HPY & Hq1 & Hq2 & Hmi & Hh) (HFA & HAN & HVC)]. cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
  destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
  unfold afree_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR.
    apply (atot34_atot (SBc:=a_space_beg st) (PAc:=a_ptr_array st)).
    apply (afree_core st mo q ch HI Hq1 Hq2 Hl HFA); [| split; reflexivity].
    unfold VCB, VCMAX, VC0, NOPS in *. pose proof (Nat2Z.is_nonneg (length ((q, n) :: Y))). lia. }
  cbv beta. intros st' s2 mo2 (-> & (HI2 & Hlive & Hnext & Hq1' & Hq2' & HFA2 & HVC2) & (F1 & F2 & F3 & F4)).
  eapply STOT_mono; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  split; [| split; [reflexivity| split; [exact F2| split; [exact F3| cbn [aps_m aset_m]; exact Hnext]]]].
  unfold AI. cbn [aps_m aset_m aps_atop aps_resv].
  split; [| split; [exact HFA2| split; [rewrite Hnext; exact HAN| rewrite Hnext; cbn [length] in HVC; unfold VCB in *; lia]]].
  split; [exact HI2|]. split.
  - unfold live_pairs. rewrite Hlive. eapply (Permutation_cons_inv (a := (q, n))).
    eapply Permutation_trans; [exact HPY|]. unfold live_pairs. rewrite <- Hsz.
    change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
      with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
    apply Permutation_map. apply Permutation_sym. apply map_to_list_delete. exact Hl.
  - split; [exact Hq1'|]. split; [exact Hq2'|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mat_with_fds : forall x m, m_vm_materialized (with_fds x m) = m_vm_materialized m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01mh11xp;1p;2g00O>j10Tg00Ocj16Tg00PAj13Tg00DYj22Tg00E9j11Tg00g1j15Tg01G1j24Tg00aG#0#0#0#0#0#0#6#3R0g01DR'2#1g00^[%10f0#5'4W0W1o"). Qed.
Lemma halted_with_fds : forall x m, m_halted (with_fds x m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01mh11xp;1p;2g00O>j10Tg00Ocj17Tg00PAj12Tg00DYj21Tg00E9j16Tg00Pdj15Tg00QFj13Tg01G1j24Tg00aG#0#0#0#0#0#0#7#2R0g01DR'1#6g00^[%50f0#3'4W0W1o"). Qed.
Lemma mat_with_tid : forall x m, m_vm_materialized (with_tid x m) = m_vm_materialized m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01mh11xp;1p;2g00O>j10Tg00Ocj15Tg00PAj12Tg00E9j11Tg00g1j14Tg01G1j23Tg00aG#0#0#0#0#0#0#5#2R0g00^[%10f0#4'3W0W1o"). Qed.
Lemma halted_with_tid : forall x m, m_halted (with_tid x m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01mh11xp;1p;2g00O>j10Tg00Ocj15Tg00PAj12Tg00Pdj11Tg00QFj14Tg01G1j23Tg00aG#0#0#0#0#0#0#5#2R0g00^[%10f0#4'3W0W1o"). Qed.

Lemma nstep_close_strip : forall fd m eff mo' evs,
  nstep (NClose fd) m eff mo' evs -> nstep (NClose fd) (strip m) eff (strip mo') evs /\ (mo' = m \/ exists x, mo' = with_fds x m).
Proof.
  intros fd m eff mo' evs Hn. cbn [nstep] in Hn |- *. rewrite m_fds_strip. destruct Hn as (He & Hr & H).
  destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)).
  - destruct H as [Heff ->]. rewrite strip_with_fds. split; [| right; eexists; reflexivity]. auto.
  - destruct H as [Heff ->]. split; [| left; reflexivity]. auto.
Qed.

Theorem asan_ok_MI2 : forall n mo rsp mo' evs,
  nstep n mo rsp mo' evs -> io_node n -> minvA mo -> m_halted mo = None -> minvA mo' /\ m_halted mo' = None.
Proof.
  intros n mo rsp mo' evs Hst Hio [Hmi Hmat] Hh.
  assert (Hsh : m_halted (strip mo) = None) by (rewrite m_halted_strip; exact Hh).
  destruct n as [fd bs|fd bufs|path|fd buf count|fd|fd req| |code|req|a l p f|a l|a l p|a l]; cbn [io_node] in Hio; try contradiction.
  - destruct Hst as (k & _ & _ & -> & _). split; [split|]; assumption.
  - destruct Hst as [-> _]. split; [split|]; assumption.
  - pose proof (minv_preserved _ _ _ _ _ Hmi Hsh (nstep_open_strip _ _ _ _ _ Hst)) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct (nstep_open_shape _ _ _ _ _ Hst) as [-> | (x & ->)]; [exact Hmat| rewrite mat_with_fds; exact Hmat].
  - pose proof (minv_preserved _ _ _ _ _ Hmi Hsh (nstep_read_strip _ _ _ _ _ _ _ Hst)) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct (nstep_read_shape _ _ _ _ _ _ _ Hst) as [(E & _) | (x & ->)]; [rewrite E; exact Hmat| rewrite mat_with_fds; exact Hmat].
  - destruct (nstep_close_strip _ _ _ _ _ Hst) as [Hs Hsh2].
    pose proof (minv_preserved _ _ _ _ _ Hmi Hsh Hs) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct Hsh2 as [-> | (x & ->)]; [exact Hmat| rewrite mat_with_fds; exact Hmat].
  - destruct Hst as (_ & _ & ->). split; [split|]; assumption.
  - destruct Hst as (_ & t & _ & H). destruct (m_tid mo); destruct H as [_ ->]; [split; [split|]; assumption|].
    split; [split; [rewrite strip_with_tid; exact Hmi| rewrite mat_with_tid; exact Hmat]| rewrite halted_with_tid; exact Hh].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PhiA : node -> Model -> Prop := fun _ _ => True.

Lemma nstepA_sub : forall n mo r mo' e, ~ nf_node n -> nstepA n mo r mo' e -> nstep n mo r mo' e.
Proof. intros n mo r mo' e Hnf H; destruct n; cbn [nf_node] in Hnf; try (exfalso; exact (Hnf I)); exact H. Qed.
Lemma nstepA_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstepA n mo r mo e.
Proof. intros n mo r e Hnf H; destruct n; cbn [nf_node] in Hnf; try (exfalso; exact (Hnf I)); exact H. Qed.
Lemma nstepA_io : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstepA n mo r mo' e.
Proof. intros n mo r mo' e Hio H; destruct n; cbn [io_node] in Hio; try contradiction; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AIW (Y : list (AsanCtrl.aptr * Z)) (w : Z) (s : APS) (mo : Model) : Prop :=
  AI Y s mo /\ 0 <= w /\ Z.of_N (a_next (aps_m s)) + w <= NOPS.

Lemma AIW_perm : forall Y Y' w s mo, Permutation Y Y' -> AIW Y w s mo -> AIW Y' w s mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01Hh12HAh22HPh32Hwh41Yh52Y'h62moh71sh81wp;2p;1p;3p;4p;6g00DYj2<Tg00E9j1;Tg0064j39Tg05@Hj47Tg00EYj36Tg00X2j20Tg00Hjj13Tg00XNj12Tg00YGj15Tg00mEj21Tg00S9R0j24Tg05A<j68Tg00W;j4:Tg004fg00]AR1'<R2#;R3g00]_g00^[f4R4f3R5592f5R2P5f2R6f1R7C7P0f6R0?656g022NR6/04%35#2#5/14g00\KR8'0'4P0P2P4P5C7f0R5f8R9?624f7R4,06%30#2#5/14/08'4f9R:?6401069%34#2#5/19/08'4f:P:P4P0P2P7E8P5C:W3W1P7P5O2n2001000000120000000W0W2W6W7X81X53W4o"). Qed.
Lemma AIW_so : forall Y w s mo v, AIW Y w s mo -> AIW Y w (aset_so v s) mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "p'0h02moh11vh21Hh32HAh42Hwh51Yh63atph71mh82rvh91sh:2soh;1wi001ai018aps_atopi025aps_mi038aps_resvi046aps_sop;2p;1p;4p;3p;5g00DYj2;Tg00E9j1:Tg05@Hj42Tg00bKj29Tg00cIj41Tg00EYj37Tg00X2j20Tg00Hjj14Tg00XNj15Tg00YGj16Tg00mEj23Tg00S9R0j28Tg05B4j5<Tg00W;j4=Tg004fg00]AR1';#:g00]_R2P2g00^[R2g00dER3f5R4f4R5f2R6f1R7C2f6R8P4f3R9,97P6C2[]1]0f0R:g00e@1;11#:f<R;f;P4P5P9P6C1P7C2P0f=R0P8P4P5P9C1R<;76g022NR=/0;%4<#5#6/3;g00\KR;'0'8f>P0f7R0P8P4P5C1,96P9C2P:f?R<f8R>P0P8P4C1;7510=<f9R5P>P0P8C1#4#5#6/3</0;'8fAR<f:P5P>P0C1R0,94R>;78f@R5,0=%4>#5#6/35/0;'8P<P0P8P4P7D<P:C=W4W3P7P:O2n2001000000120000000W2X13X02X61W8X:3W7P9P6P7P:O4n01100000140102104103101W9X;1W5o"). Qed.
Lemma AIW_model : forall Y w s mo, AIW Y w s mo -> minvA mo /\ m_halted mo = None.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01Hh12HAh21Yh32_Hh42moh51sh61wp;2p;1p;4p;3g00DYj2BTg00E9j1ATg05@Hj49Tg00EYj34Tg00X2j21Tg00Hjj17Tg00XNj16Tg00YGj13Tg00mEj25Tg00S9R0j22Tg00f;j18Tg00O>j10Tg00Ocj1:Tg00PAj1@Tg00Pdj1?Tg00QFj1<Tg00R=j1;Tg00R_j3=Tg05Bjj4>Tg004fg00]AR1'B#Ag00]_g00^[f3R2f2R3f1R4f0R5C9P0f4R0?434g022NR6/12%73#6#3/52g00\KR7'1'2%83g00aG#0#0#0#0#0#0#:#@R8#?%<3%;83='2P5f6R8?4021168f5R6#7#6#3/58/17'2f8P8P6P4C>W3W1P4P5O2n2001000000120000000W0W4W5X61W2o"). Qed.
Lemma AIW_fds : forall Y w s mo f, AIW Y w s mo -> minvA (with_fds f mo) -> m_halted (with_fds f mo) = None -> AIW Y w s (with_fds f mo).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01Hh12HAh22HMh32Hhh42Hwh51Yh61fh72moh81sh91wp;2p;1p;4p;3p;7g00DYj2>Tg00E9j1;Tg00O>j10Tg00Ocj1?Tg00PAj1DTg05@Hj4<Tg00EYj37Tg00X2j21Tg00Hjj14Tg00XNj16Tg00YGj13Tg00mEj25Tg00S9R0j28Tg01B]j22Tg00f;j1=Tg00Pdj1CTg00QFj1:Tg00R=j1BTg00R_j39Tg05Ccj7@Tg00W;j4ATg004fg00]AR1'>#;g00]_g00^[g00aG#0#0#0#0#0#0#?#DR2g01DR'>#;f4R3f3R4f2R5f1R6C<P0f5R0?745g022NR7/13%44#6#3/53g00\KR8'1'81254#=%C2R91243#:%B2R239f8R:f7R;f6R<1230C<[[f0R=A7;03117;%4<#6#3/5;/18'8120<#=12<;#:=992f;R2f9R912;:37f:R<,17%49#6#3/5</18'8P2P9P:P;P4P6P=F@P5CAW3W2W4W1P6P=O2n2001000000120000000W0W6W7W8X91W5o"). Qed.
Lemma AIW_credit : forall Y w w' s mo, 0 <= w' <= w -> AIW Y w s mo -> AIW Y w' s mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01Hh14__x1h24__x2h34__x3h44__x4h52H0h62H1h72HAh82Hwh91Yh:7__arithh;4__ffh<8__varmaph=5__with>4cstrh?2moh@1shA1whB2w'p;2p;1p;4p;3p;7p;8g00DYj2[Tg00E9j1ETg00X2j20Tg00S9R0j23Tg05@Hj4<Tg00EYj3;Tg00Hjj16Tg00XNj15Tg00YGj14Tg00mEj22Tg02e^j1GTg02EOj1:Tg02iOj2=Tg03Ncj3DTg02j8j2VTg00HJj1UTg01\^j3TTg02Unj2CTg02jdj1NTg03OLj4ATg02VLj1MTg02Vjj1KTg00O>j1@Tg02X8j29Tg03LTj3?Tg02LWj1JTg00R=j1ITg02WUj2LTg02X[j2HTg01G1j2OTg02akj2PTg00R_j3QTg02Y=j3FTg02Y\j4RTg00W;j4STg03Jbj4ZTg03KMj7YTg03M7j7XTg03M[j8WTg022NR1f0R2'0p=1g00]AR3f1R4g03T0P2CZp=8P4g03RQR5g03S0R6P6g03SPR7P2g03TWFYp=7f2R8P5P6P6P7P4P2FXp=>f3R9P5P6P6P7P8P4P2GWp=Bg004f/[3#Eg00]_g00^[%18R51089'3f5R:f4R;P8P4C<P0f6R<?;98%1:%69#5#4/2:g00\KR='0'3f7R>P:P;P9C<P2f8R??;:;%1?%6<#5#4/2?/0='3P0f9R0#1%6>#5#4/20/0=f;R<P0P?P>C<P2%1<f:R>#6#5#4f<R?'2/0=f>R0?;<>%1?%6<#5R>#4R@/2?/0='3P:%G>%1@g03[lR@g02JWR>#:R:#:#:,=31=3:1=3>5D35D3g03a6'V%U@3T%E@P3P31C3;P8%N3CAP41C39CA%M3%K3R@g00aGR>#@R:,93R?%@:,93R:5?3%J>,93RA'8,7@%I6R6P@1L31193>R>'8,7@RB18>:,7@5>@P6A?3?>/8A,7@9>@BCBCB1H@7P2P8g022lR@g023LR7'O1P28=Q@7dAF314CRb;b<b=X13X23X33X431249/08%14104;'31298/0;,35[[^13^23^33^43P2f?P=f=#6#5#4P0P8P<O6b:b>CSW6W5P4P2O2n2001000000121000000W0W7P4P2O2n2001000000121000000W0W8W?W@XB3XA3W9o"). Qed.
Lemma AIW_wnn : forall Y w s mo, AIW Y w s mo -> 0 <= w.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "h01Hh12H0h21Yh32_Hh43_H0h52moh61sh71wp;2p;1p;4p;3g00DYj2:Tg00E9j19Tg05@Hj48Tg00EYj36Tg00Hjj15Tg00XNj13Tg00YGj12Tg00mEj24Tg00X2j21Tg00S9R0j27Tg022Nf0R1'1p=0g004fg00]AR2':#9g00]_g00^[f3R3f2R4f1R5P1C8P0f4R6?645%03%54#3#2/43g00\KR4'1'7%06P1f6R7?663%07f5#5#3#2/47/14'7P0f7R0#0%57#3#2/40/14f8#0P1f9R0#0%50#3#2f:'4/14P5W4W1P5P1O2n2001000000120000000W0W3P5P1O2n2001000000120000000W0W5W6X72W2o"). Qed.

Lemma asan_ok_malloc_w : forall Y w n s mo,
  AIW Y w s mo -> 1 <= w -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  tglob nstepA PhiA (amalloc_M n s) mo ->
  STOTA (amalloc_M n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AIW ((q, n) :: Y) (w - 1) s' mo' /\ n < 2^63
                         /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "p'0h01qh11Hh21rh33mo'h42s'h54__x1h64__x2h74__x3h87__arithh94__ffh:8__varmaph;5__with<4cstrh=1nh>1sh?1xi001xh@2H0hA2H1hB3H63hC2HAhD3HA'hE2HHhF3HfdhG3HfshH2HnhI5HnexthJ6Hnext0hK3HsohL2HwhM2R0hN1YhO2_HhP1ahQ5cstr0hR2mohS3mo1hT1whU1yhV1zp%0p&0p;2p;1p;4p;3p;7p;8p;<p;6p;:p;5g00DYj2eTg00E9j1cTg05@Hj4OTg00EYj3@Tg00YGR0j18Tg00mEj2;Tg00S9R1j20Tg01WLj1[Tg00X2j29Tg00lhj2tTg000\j4dTg01\^j3HTg02C`j1aTg00Pdk10LTg05DZk10GTg03Hnj2JTg01R9k40BTg00R_j31j1hTg03>mj2<Tg00O>j1MTg02LWj1QTg02M<k202Tg02MYj13Tg00Ocj1~Tg00PAj1}Tg01EJj15Tg01F>j12Tg01MYR2j7fTg01XJj2>Tg02e^j1bTg02EOj1qTg02iOj2`Tg03Ncj3pTg02j8k20KTg00HJk10JTg02Unj2nTg03OLk40FTg02VLk10ETg02Vjk10DTg02WUj2mTg02X8j2^Tg00R=k10CTg03LTj3XTg03Jbj4kTg02X[k20ATg01G1j2WTg02akk20@Tg02Y=k30>Tg02Y\k40=Tg05ERk80<Tg03C8R3j1PTg03E@k103Tg03E^k200Tg03F?k306Tg03F\m<08Tg03GAk409Tg03>Jk30:Tg03M7j7|Tg03GhR4j1{Tg002cj6\Tg00W;j4NTg02Fdj4zTg01NLl:yTg00Hjj1oTg00XNj1lTg01Lej5xTg02L5j2wTg01\>j4_Tg01=7R5j2vTg03KMk70HTg03M[k80ITg03Q5l<uTg022NR6f0R7'9p=:%o7#lp=4g00\KS00,97p=Fg03QZR8g05FQf2R9f1R:P7Dxp=]g004fR;/w7p=?P;g00]AR<P:P7C_p=if5R=f4R>f3R?3HP9P:P7COp=gg0048R@%2771:p=L%5:91?9/07p=S1>>?g00dERA?19:/07'0p=C10:7,09p=61v;7p=7P;P<P9P:C_=H?7p=EA1A:7p=sA1@:7p>0Ng02BKRB%P771:p>0MP>1<?9P:P7COp=rP<P:g03T0P7Ckp=KP:g03RQS01g03S0RCPCg03SPRDP7g03TWK0Hp=GP?Q01PCPCPDP9P:P7L0Ip=U%3:=1A7p=j%5:=197p>0;%2:=1@7p=I%o7#l#P91B:p=Z%59=1?:/07p==f7REP;P<f6RFP=C_;H>P?P9P:CO/07p=DA1?9:/07p=AA1B:7p=VA1@9:/07p>05%39=1A:/07p=RA1@?9%P791B:'0p=B%3791A:p=Y%57919:p=T1>9:/07p>04A1@:7,09p>01PBPBP<P<P3P0P0P?P4P9P:P7M<up>07A1=>?A1@9:/07'0p>0?1e;<R@#cg00]_R4g00^[R3P>P?P:P7COP1A@=9:%:>%49RA#8/;>#F'0g00aGRG#[RH/9=%:=g03WYRI,9='0P@P<1t;<RJf8RKCd9H<F#a&0L;RL/e4$0GRM1JEF;]=P4P8P2p4p741100g03XRP8g03YGP7H0BWMR2PL1JKEPF%?7RN91L?ROP@f<RP,i7f>RQf=RR/<HP9P:EgPP%MGRS#[%QGRT#Q#Q#Q#Q#[+02RU%39RVf;RW#3%MS#M#M#M#M#~#}g01DR'e#cRX%5:RYf:RZ%2:R[/LZCSDC36X0;#7X33X44X2LFf[[[[P7A@E>?%:E%4=R\#8/;E#F'0P1%:K%4FR]#8/;K#Ff9R^,9H%:^19^I'0P@P<PJPPCd9H<Z#a1JWZ=]M^P4P8P2PL1JPWPZP@f@R_,i7fBR`fARa/<HP9P:EgP_PUPVf?Rb#3PXPYPQ1L[QCSDC56OX0;#7X33X44X2LFf[[[[P7%:Z%4^Rc#8/;W#F19HP%:P19PI'0P@P<PJPbCd9H<R#a1JQR=]MPP4P8P2PL1JbQPRP@P7fCR2fER8CERM?@9:1>2URJ%3`RI,sVRd%5aS0291XYRe%2aS03-0N[Rf%4`S04-0MA363656OX0;#7S05X33X44X2LPMfDRMPHP9P:Dr10ef96Jd56OX0;#7X33X44X2LPaPbPQPRP^P9P:%4QRd#b%8d#:g03[lRJg02JWRf#qRe#q,`<1`<e1`<f5p<5p<g03a6+0K&0JJS063H%cJS07P<1n<9P:1n<?H0FS08&0E<S09&0D<RJ1m<HRf1^<TRT'K,GJ&0CCRePJ1^<GRG=X<T1^<SRS'K,GJPeP<PGg03U7PSCk,GJCUCU20AJDS0:P7P9g022lRgg023LRh'W20@79=1ghdB0><6:H0=S0;b9b:b;X5<X6<X7<19H91;:?/991>9?[[^5<^6<^7<P7P`Q00%4_#8P=PFO5b8b<L0<Q05P5P;A1L>NS0<P@P7PMfFR5CES0=?@?91>MUS0>%32,j?S0?%5`:0;X9Rh%2`,I9R`%4?/Z2363636X0;PLP=PNP@P7P8fGRg1<5HP>P?P8PU%3>%3MRiPXP?%52Rj%22Rk,I?C=DCGDCAX0;#7P7PLPFPNP@P7P5fHRlCERm?@=>1>5URn%38RoPXP>%5MRp%2>%2MRq%48S0@#PRr,V\405C=5R=36CAP1%?:91LEP@P:PgfIR\CE?@F=1>gU%35PXP=%58Rs%2=%28S0AP]%45S0BCBC=5RF36PLP^PNP@P7P\fKRFfJR5/<HPKPEP\PU%3K%3lS0CPXPE%5gR]%2gRt,IEC=DCGDCAX0;#7P7%??91L^PL%?>P@P=PFfMRuCE?@Z^RvPFPU%3Z%35PXP^%5\%2^%2\Rw%4Z%45RxCBC=DCRy'0PLP9PNP@P7PufORzfNR{/<HPPPWPuPU%3PfLR|#3S0DPXPW%5FS0E%2FR},IWC=DCGDR~CAX0;#7[X2LP@P>P5P|CE?@^K1>5U%3\PXPK%5l%2K%2lS0FPc%4\S0GCBC=5R^36P1PvPyPL%?EPNP~CAX0;#7P7P@PEPuPzCE?@PWP{PU%3R%3uPXPP%5|%2P%2|%4R%4uRPCBC=DCP11>zU%3{REPXPR%5uR~%2R%2uRyPd%4{RdCBC=5RQPL%?WPNP@P7fQRWfSRQfRRv/<HP_Pb1>WURcfPRK#3,j_PXPb%5z%2z,IbC=36GDCAX0;#7P7%3WPXP_%5K%2_%2K%4a%4WCBC=5RaP11YIvPXQ02PWQ03%2WQ04%4vCBCSPL%?bPNP@P7fURbfWRvfVRW/<HPMP2fTRM,YiRiATXjQ1LkQ36:04bUGDCAX0;#7P7PXPpPMPq%2MQ0@%4bCBCSP1ATXsbQ0A%2bQ0B%4WCBPL%?2PNP@P7fYR2f[RWfZRb/<HPlPgP2PUQ0CfXRl#3ATX]vR]%2v801tDCGDCAX0;#7P7Q0F%2lQ0G%42CBP11Lw21ZxbPL%?gPNP@P7f]Rgf_Rbf^Rx/<HP|PFPgPUQ0Df\#3PXQ0EPW1L}WRWCSDCGDCAX0;#7P71ZPgP;PL%?5PNP@P7f`RNfbR5faRP/<HR}PzP{PNPU%3z%3bPXP{%5x%2x,I{C=DCGDCAX0;P\%?\RF=1LFP@P\PbPPCERP1<NHR\P{PuCOR@1>bURb1YExREATX~gR~1LygRg'0Ry'0RU'0R|'01WLFP@P|A@P{u%:\%8dRP/;\#F'0PaPB%4xRx#PRa%:}R\%87R{/;}#F'0X=BP<%8xRu$031;7}#F,0\XV<1Vda1;uH91<PR\PBP<%hBP0%h<%8:=1<{1V:7200:7406XUBX?BPdPP1W<PPa1;7HX?<RPPuO1PPPxPu1W<uH07N<08P7H09P\%4zRz#b%8z#:%4NRN#b%8N#:Q06Q07Q08Q09PJ1KfG,GJPePJAX<SG/KT,GJPePJQ01PCPCPD1m<6B0:<GfRG'K,GJAX<Sf=X<G/KT,GJF|CUCUQ0:Q0;b9b:b;X5<X6<X7<19H71;9:/9?1<9HRJ#:1;?H/;J/9>'0[[^5<^6<^7<P7Q00%45#8fdPvPlO5b8bQb<bJ%8a%{xE\PdP7E\CNPbPUPRPEPyP^P~PgP=P:CNCNCNCNCNCzWIXGWP:P7O2n2001000000121000000W1XF]P:P7O2n2001000000121000000W1XKiP:P7O2n2001000000121000000W1XBcP:P7O2n2001000000121000000W1WDP:P7O2n2001000000121000000W1PZP7E\W1P:P7O2n2001000000121000000W1X0;P:P7O2n2001000000121100000W1X33X44X2LA@m9:1sVoPXPYPpP[Pq1VArJ0?56n56OX0;#7X33X44X2LP9P:P7O3Q0<Q0=P8PHP?P9DrQ0>Q0?10h`3636X0;#7[^S3^>4^PLeM:yWOWEWHWLWAW@P:P7O2n2001000000121000000W1WCP:P7O2n2001000000121000000W1WRW>X=<XT<WNo"). Qed.

Lemma asan_ok_free_w : forall Y w q n s mo,
  AIW ((q, n) :: Y) w s mo -> tglob nstepA PhiA (afree_M q s) mo ->
  STOTA (afree_M q s) mo (fun _ s' mo' => AIW Y w s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "p'0h01Hh13mo'h22s'h31sh44__x1h54__x2h64__x3h71ah83mo1h91nh:2H0h;2H1h<2HAh=3HA'h>3Hfdh?3Hfsh@5HnexthA6Hnext0hB3HsohC2R0hD1YhE2_HhF7__arithhG4__ffhH8__varmaphI5__withJ4cstrhK5cstr0hL2mohM1qhN1whO1xhP1yi001up;2p;1p;3p;4p;6p;<p;7p;:p;5p;8g00DYj2KTg00E9j1JTg01\^j3ITg05@Hj4PTg00EYj3=Tg00YGR0j17Tg00mEj2<Tg00S9R1j25Tg05DZj1[Tg04W5j2BTg01R9j4rTg02MYj13Tg00O>j1@Tg00Ocj1iTg00PAj1dTg01EJj10Tg01F>j12Tg05GFj6\Tg00R_j34j1QTg03E^j2ZTg03F?j3YTg01G1j2MTg03F\l<wTg03GAj4vTg02e^j1XTg00HJj1uTg02Unj2WTg03OLj4tTg02VLj1qTg02Vjj1pTg02X8j2LTg03LTj3mTg02LWj1lTg03Jbj4VTg00R=j1kTg02WUj2jTg03M7j7hTg02X[j2eTg02akj2cTg02Y=j3fTg02Y\j4gTg00X2j2GTg002cj6bTg00W;j4HTg01NLl:aTg01\>j4nTg00Hjj1oTg00XNj1`Tg01Lej5_Tg01MYR2j7^Tg03KMj7]Tg03M[j8sTg004fR3g00]AR4f1R5f0R6Cnp=Ng022NR7/G6p=8%o6#`p=1g00\KR8,G6p=Ag03QZR9g05FQf2R:P5P6D_p=Og0048R;?456p=:g00dER<f5R=f4R>34f3R??4:5/56'5p=;P>P?P:P5CP/56p=9g00]_R@P9P?g03S0RAP:P5P6F^p=S%3694<5p=D%0694:5p=Fg02BKRB?456p=C1556,5:p=?A4<56p=RA4B56,5:p=>A4?:5/56p=E%2694;5p=6P5g03RQR;PAPAg03SPR<P6g03TWF]p=UP?P;PAPAP<P:P5P6Gsp=T1K34RC#Jg00^[RD1N?:=IC=P>P5P6CPP11N>?f6RE5IC?=:5%8=%1:RF#7/<=#A'51KA@#[RG1B=?;O:P2p4p741100g03XRP9g03YGP6CrWCR21BE>P?f;RHf:RIP5P6%35RJf7RK#3RLg00aGRM#@RN#@#@#@#@#@#i#dg01DR'K#JRO%06RP%0ERQ%26RR%2ERS':E;D9X1DX2@VACS[P61NE=f8RT5IC?=>?%8T%1=RC#7/<T#A'5P1f9RU#8%1ERV#7/<U#A1BUK=OGEP21BITPKf?RWf>RXP5P6PJ%3HRYPOPP%0IRZ%2IR[,:RE;D9X1DX2@VACS[P6%8H%1UR\#7f<R]'<#A1B]I=OGUP@P9P2PAf=R2/BHPIfBR9?=561DJXRGAFOP2R^%22R_,:RR`%15Ra%1XRb'C3?3?RcX1DX2@VAP9fARdP5P6A?G^`D9X1DX2@VAPWP2P]PHPIPEE\PAfCR`?=56%3WR^,RJPOPP%0XRG%2XRe,:R%1WRf7>aCE3?fDRgP`P:P5%3:Rhf@Ri#3RjPO%05Rk%0WRl%25Rm%2WRn':E;D9[^8D^3@P6P1A=`:51Rh^RhA4OkGRk1:meRm?>Ff3?PgP`P?P:%3?PjPO%0:Pl%2:/:nE;D9P6fERl?=>?%3=%39RjPO%0>%0dRf%2>%2dRF':%19Ro7>CE;P1%3E/D`PO%0=%09%2=/69%1`RC7>VCEfHRVfGRpPKPEPL%3gPOPQ%0`16S`E;D9P6%3T/DlPO%0T%0l%2T/6lfFRT#17>\CEP1%0U=FOT%2U/6T%1I%1p3>fLRTfKR\PHPIPY%3VPOPZ%0p16[pE;D9P6%0H=FOV%2]fIR]'6%12fJRV#13>P116_V%1\,CbfPfORbPWPXP^%3TPOPG%0\16e\E;D9P616nT%1dRTfNRn#1'CfSR\fRReP9PdCP1DjbRjAFOfnRf16FnRn'5RF'5A=\9d%8e%7oRG/<e#A'5P2PB%1bRb%8\%76R2/<\#A'5X9B1Cob%7bRe944GR^PBP4%QBP0%Q4%75=4421C561Z563YXPBXOBPoPG1M4GPbPe1M4eM<wP6CvP^%XC%7C#8fQ#1RC#X%7C#8g03[lRC#u%JCP41W4:P51W4?Ct%q4%p4RCP41L4N1L4MRN5m4g03T0R^%lM,L4CV,UCRM%kARePCP41j47P^PNCV,UCRNPePCP;PAPAP<PNPMFhCTCT1eC<P6P:g022lRCg023LR<'M1c6:=4C<dAf475CgbGbHbIX44X54X641<56/G:%85%8:1<?:/G>'5[[^44^54^64P6P8%1\#7fVP]PVO5bFbKbJbAPoP6EbCHPjPFPUPfPnP=P5CHCHCHW@W?P5P6O2n2001000000121000000W0W>P5P6O2n2001000000121000000W0WBP5P6O2n2001000000121000000W0W=P5P6O2n2001000000121000000X0cX1DX2@n01100000101X7AA=l561DJdPOPP%0i16Ri?>aTCE3?X1DX2@VAP:P5P6O3P`P9P:P5A?hkmD9[^8D^3@^7AeM:aWEW;W:P5P6O2n2001000000121000000W0W<P5P6O2n2001000000121000000W0WLX3@X94XM3XN4WDo"). Qed.

Lemma asan_ok_annot_w : forall Y w q cap old new s mo,
  AIW Y w s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  tglob nstepA PhiA (aannot_M q cap old new s) mo ->
  STOTA (aannot_M q cap old new s) mo (fun _ s' mo' => AIW Y w s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanOK ()) [] "p'0h01Hh13mo'h22s'h31sh44__x1h54__x2h64__x3h71ah83mo1h92H0h:2H1h;2HAh<3HA'h=3Hfdh>3Hfsh?3Hinh@2HnhA5HnexthB6Hnext0hC2HohD3HsohE2HzhF2R0hG1YhH2_HhI7__arithhJ4__ffhK8__varmaphL5__withM3caphN4cstrhO5cstr0hP2mohQ1nhR3newhS3oldhT1qhU1whV1xhW1yi001up;2p;1p;4p;3p;5p;<p;7p;6p;:p;8g00DYj2QTg00E9j1TTg05@Hj4NTg00EYj3;Tg00YGR0j16Tg00mEj2<Tg00S9R1j21Tg03dbj3JTg00X2j28Tg02i5j2PTg05DZj1zTg04Q7j5@Tg01R9j4pTg02MYj14Tg00O>j1CTg00Ocj1gTg00PAj1fTg01EJj10Tg01F>j17Tg00R_j33j1\Tg05HCl<`Tg00Hjj1UTg03E^j2|Tg03F?j3{Tg01G1j2STg03F\l<yTg03GAj4xTg02e^j1[Tg00HJj1tTg02Unj2ZTg03OLj4sTg02VLj1rTg02Vjj1qTg02X8j2OTg03LTj3oTg02LWj1nTg03Jbj4XTg00R=j1iTg02WUj2hTg03M7j7jTg02X[j2kTg02akj2lTg02Y=j3mTg02Y\j4eTg002cj6dTg00W;j4ETg01NLl:cTg00XNj1]Tg01\>j4uTg01Lej5bTg01MYR2j7vTg03KMj7wTg03M[j8aTg022NR3f0R4'8p=5%U4#]p=2g00\KR5,84p=Ag004fR6g00]AR7f1R8P4Cup=KA3743p=Bg03QZR9g05FQf2R:P8P4Dbp=Rg0048R;?384p=Dg00dER<f5R=f4R>33f3R??3:8/14'1p=:P>P?P:P8CN/14p=9g00]_R@P9P?g03S0RAP:P8P4Fvp=VA3<84p=Mg02BKRB?384p=L1184,1:p=?A3B84,1:p==A3?:8/14p=F%78=3;4p=_%78%7453;p=>%4493<8p=G%0493:8p=I%7493;8p=H%]493B8p=^P8g03RQR;PAPAg03SPR<P4g03TWFwp=WP?P;PAPAP<P:P8P4Gap=Y1Q67RC#Tg00^[RDf7REf6RFP8P4CNP1f8RG?;:8%5E%2:RH#6/<E#A'11KEFf9RI5JC%5FRJ18FE'118FG,1J%BG%BE'P1QA@#zRJf;RKf:RLPIPGPED@;RFP2p4p741100g03XRP9g03YGP4CpWFR2f<RMPKPLPIPGD@PEfARNf@ROP8P4%48RP%4KRQg00aGRR#CRS#C#C#C#C#C#g#fg01DR'Q#TRT%04RU%0LRV%74RW%7LRX'DE:D9X1DX2@VACV[[[[[P4A;L>?%5LRY%2=RZ#6/<L#A'1P1%5K%2FR[#6/<K#A1KKLf=R\5JC18LK,1Y18LM,1Y%BM%BK'Pf?RYf>R]P\PMPKD@=RJLP2POPYP]P\PMD@PKfER^fDR_P8P4PP%4YR`PTPU%0]Ra%7]Rb,DWE:D9X1DX2@VACV[[[[[P4%5\Rc%2IRd#6/<]#A1K]\=JCO18\],1c18\Y,1c%BY%B]'PfBRcPNPOPYP]D@=RJ\P@P9P2PAfCR2PcPNPOPYD@P]fHR9?;84%4cRJ,MPRC%0NRe93TURf%7NRg,DWRh%28Ri%2cRj'L3?3?RkX1DX2@VAP9fGRlP8P4A?CfhD9X1DX2@VAP^P2PcPNPOPYP]PLP>P?P:P8M<`PAfIRO?;84%42Rh,MPPTPU%0cRf%7cRC,DW%22Rm7=iCF3?fJRnPOP:P8%4:Ro%4_RpPT%08Rq%02Rr%78Rs%72R2'DE:D9[^8D^3@P4P1A;O:81MohRoA3TqfRq1DsCRs?=Hm3?PnPOP?P:%4?PpPT%0:Pr1_:2E:D9P4fKR2?;>?%4=fFRr#4PT%0>%0^1>>^%2r7=ZE:P1%4F/GlPT%0=%0r1>=r%2l7=[CFfNR[fMRrPEPF%4E%49PT%0F%0l1>FlE:D9P4%4G/GOPT%0G%0O1>GO%2n7=dCFP1%0I=ITn1>In%2L%223=fRRnfQPKPLPQfLRQ#4PTPV%021HX2E:D9P4%0K=ITQ1>Mr%2\%2[3=P11>\[%2]fOR1#U'^fVfURMPYP]P`fPR`#4PTPa%011Hb1E:D9P41>Y`%2N%Un'^fYR`fXRYPcPNCNfSR1,GJRJAITenRe1HgnRn'1Rg'1A;`cN%5Y%6jRc/<Y#A'1P\PB%21R1%5`%64R\/<`#A'1XQB1Lj1%61R`937cRYPBP7%\BP0%\7%68=37\1L841|843{XWBXVBPjPc1S7cP1P`1S7`M<yP4CxPY%[m%6m#5%2MRM#[%6M#5g03[lRM#t%TMP71Z7:P81Z7?Cs%r7%q7RMP71O7S1O7RRS5o7g03T0Rm%nR,O7CX,WMRR%iARYPMP71h73PmPSCX,WMRSPYPMP;PAPAP<PSPRFjCYCY1kM<P4P:g022lRMg023LR<'S1l4:=3M<dAm738CebJbKbLX47X57X671<84/8:%58%5:1<?:/8>'1[[^47^57^67P4P5fW#2#6f\PrP[O5bIbObNbBPjP4EdCEPJPgPIPePnP=P8CECECEWAW>P8P4O2n2001000000121000000W0W=P8P4O2n2001000000121000000W0WDP8P4O2n2001000000121000000W0W<P8P4O2n2001000000121000000X0kX1DX2@n01100000101X7AA;2841GP^PTPU%0_1HW_%2^7=iCF3?X1DX2@VAP:P8P4O3POP9P:P8A?oqsD9[^8D^3@^7AeM:cWHWEW@WCW?W:W9P8P4O2n2001000000121000000W0W;P8P4O2n2001000000121000000W0WPX3@XR7XS7XM7XT6XU7WGo"). Qed.

Definition AAllocAsanOK : AAllocOK AAllocAsan nstepA PhiA minvA :=
  mkAAllocOK AAllocAsan nstepA PhiA minvA nstepA_sub nstepA_same nstepA_io asan_ok_MI2
    aps_get_set aps_set_set aps_set_get aps_addr_so
    AIW AIW_perm AIW_so AIW_model AIW_fds AIW_credit AIW_wnn
    asan_ok_malloc_w asan_ok_free_w asan_ok_annot_w.
