(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (25 recorded proofs replaced by written proofs (sgood_vis, sgood_bind, sgood_mono and 22 more); nstep_progress_mmap, nstep_progress_munmap re-proved; startup_STOT also states that startup keeps m_kernel). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Cfg ITree Nodes Decode Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe MPaths STree Malloc MallocCtrl KInv KStep KLink KEv Relim Prog StepB RSim EKSim ModelInv.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_PTotal () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes4list01C5ELinuxProcessSemantics?LinuxProcessSem6Checks8Progress9receptiveC5ELinuxProcessSemantics?LinuxProcessSem6Checks8ProgressDsyscall_spec_witnessC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specI4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib3CfgBexists_nonspuriousC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap9check_brkK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C59OSSVerify5KrLib3Lib5Nodes=nstep_brk_iffC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallC5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsDcheck_syscall_ok_iffC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys?DispatchComputeAcheck_syscall_brkK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C59OSSVerify5KrLib3Lib5Nodes4eff0C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsPcheck_syscall_complete_unmodeledI47Corelib4Init9Datatypes4prod00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap8brk_r_okC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC47Corelib4Init9Datatypes4andbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=with_brk_nextC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C59OSSVerify5KrLib3Lib5Nodes:pure_inputC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notI47Corelib4Init5Logic3and00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bK47Corelib7Numbers7BinNums1Z03C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC59OSSVerify5KrLib3Lib5Nodes>nstep_mmap_iffC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys?DispatchComputeBcheck_syscall_mmapC59OSSVerify5KrLib3Lib5NodesFmmap_safe_no_unmodeledC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC59OSSVerify5KrLib3Lib5Nodes@nstep_munmap_iffC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys?DispatchComputeDcheck_syscall_munmapC59OSSVerify5KrLib3Lib5NodesHmunmap_safe_no_unmodeledC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm8Mprotect>check_mprotectC59OSSVerify5KrLib3Lib5NodesBnstep_mprotect_iffC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys?DispatchComputeFcheck_syscall_mprotectC59OSSVerify5KrLib3Lib5NodesJmprotect_safe_no_unmodeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidI47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim4STOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim5tglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB3tnfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal4PhiPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB2NFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>minv_preservedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim=tglob_ebind_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim=tglob_ebind_rC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib4Spec6PTotal5sgoodC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim8STOT_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;tpath_enodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;tpath_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal8good_ansC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps6membedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps;MAP_FIXED_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal9sgood_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9am_finishC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<am_after_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal8guard_sgC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal8queue_sgC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal:am_take_sgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbc59OSSVerify5KrLib4Spec6PTotal;am_carve_sgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_meta_alloc_shiftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal<am_finish_sgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>brk0_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDmmap_fixed_answer_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal?am_after_brk_sgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=brk_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<brk_pages_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc;layout_hook00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7lh_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal:ag_tail_sgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4Spec6PTotal=alloc_meta_sgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;log2_nonnegC59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal<ctz32_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal>alloc_group_sgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal<try_avail_sgC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3lorc59OSSVerify5KrLib4Spec6PTotal=alloc_slot_sgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotalDmalloc_small_ctrl_sgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal>malloc_core_sgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal:sgood_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8lay_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<mmap_addr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6DecodeAmmap_addr_ok_trueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode6avoidsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KStep;mmap_len_geC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec5MSafe9twf_tpathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths?tpath_mbind_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths:tpath_mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths:tpath_mupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPathsBtexit_msys_nonexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths;texit_mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths:texit_mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths:texit_mupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths=tpath_msys_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MPaths>tpath_msys_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode7dec_brkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal>tpath_sys_thenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_brk0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7vm_onlyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState:set_brk_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps>dec_mmap_fixedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps9neg_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode=dec_mmap_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode:dec_munmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps?dec_mprotect_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps7ev_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes@nstep_mm_vm_onlyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode7brk_ans00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode8mmap_ans00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ProgDeps9fixed_ans00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode7brk_ans01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode7brk_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K59OSSVerify5KrLib3Lib6Decode8mmap_ans01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5EKSimGdec_mmap_none_err_errnoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode8mmap_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6DecodeBdec_mmap_none_SomeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9efferr_ciC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotalAis_err_of_addr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5EKSimBdec_mmap_err_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode=dec_mmap_SomeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode9range_ans01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<dec_mprotectC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5EKSimFdec_mprotect_err_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal>ev_step_silentC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal>ev_step_noexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv4MAPFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv5MAPFXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ctree_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink8frame_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5KLink2KL00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9brk_quietC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink:KL_atop_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv<ev_step_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink<ev_step_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe4etwfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib4Spec6PTotal<ev_step_goodC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv?event_post_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal=ev_step_nsafeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal>ev_step_existsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal>noreserve_MAPFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal?noreserve_MAPFXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State:fdst_tableC4ELinuxProcessSemantics?LinuxProcessSem5State:fsst_imageC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spI4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib4Spec6PTotal3FRZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal>vm_only_tablesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv3OWNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal<frame_ok_FRZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv9OWN_weakGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv?raw_malloc_specC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv6creach00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_ContractsFcmalloc_contract_proofC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec<MI_Contracts;creach_atopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal:cmalloc_sgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal;membed_stotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5set_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv5OWN_GC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal=membed_silentC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotal=membed_noexitC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List4inclI46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib6Malloc8ProgDeps9fresh_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv=raw_free_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_ContractsDcfree_contract_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5cfreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6DecodeAnstep_dec_set_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode;dec_set_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes=m_fs_with_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>m_fds_with_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesAm_vmmaps_with_tidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6PTotalEnstep_progress_settidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim9STOT_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim9STOT_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog7startupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim8STOT_sysC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation M := Monad.M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PhiP (n : node) (mo : Model) : Prop :=
  minv mo /\ m_halted mo = None /\ nsafe n mo /\ NF n mo.

(* [comment removed for export] *)
Lemma nstep_progress_brk : forall req mo, exists rsp mo' evs, nstep (NBrk req) mo rsp mo' evs.
Proof.
  intros req mo. pose proof (receptive (pure_input 214 [Z_to_bv 64 req]) mo) as Hr.
  destruct (syscall_spec_witness (pure_input 214 [Z_to_bv 64 req]) mo) as [eff mo' evs|] eqn:E.
  - destruct (exists_nonspurious ACFG _ _ _ _ _ Hr) as (eff2 & mo2 & evs2 & Hs2 & Hns2).
    exists eff2, mo2, evs2. apply nstep_brk_iff. split; [|exact Hns2].
    rewrite <- (check_syscall_brk (pure_input 214 [Z_to_bv 64 req])) by reflexivity.
    apply check_syscall_ok_iff. exact Hs2.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr.
    rewrite (check_syscall_brk (pure_input 214 [Z_to_bv 64 req])) in Hr by reflexivity. cbn [in_arg in_args nth pure_input] in Hr.
    revert Hr. destruct (eff0 (Z_to_bv 64 0)) as [r ws zs us cs ci] eqn:Ee. unfold check_brk.
    destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (_ && _); discriminate.
Qed.

Lemma nstep_progress_mmap : forall addr len prot flags mo,
  nsafe (NMmap addr len prot flags) mo -> mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  exists rsp mo' evs, nstep (NMmap addr len prot flags) mo rsp mo' evs.
Proof.
  intros addr len prot flags mo Hsafe Hnr.
  set (i := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]).
  pose proof (receptive i mo) as Hr.
  destruct (syscall_spec_witness i mo) as [eff mo' evs|] eqn:E.
  - destruct (exists_nonspurious ACFG _ _ _ _ _ Hr) as (eff2 & mo2 & evs2 & Hs2 & Hns2).
    exists eff2, mo2, evs2. apply nstep_mmap_iff. split; [exact Hnr|]. split; [|exact Hns2].
    rewrite <- (check_syscall_mmap i) by reflexivity.
    apply check_syscall_ok_iff. exact Hs2.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr.
    rewrite (check_syscall_mmap i) in Hr by reflexivity. cbn [in_arg in_args nth pure_input i] in Hr.
    cbn [nsafe] in Hsafe. exact (mmap_safe_no_unmodeled _ _ _ _ _ _ _ _ (proj2 Hsafe) (proj1 Hsafe) Hr).
Qed.

Lemma nstep_progress_munmap : forall addr len mo,
  nsafe (NMunmap addr len) mo -> exists rsp mo' evs, nstep (NMunmap addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hsafe. set (i := pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]).
  pose proof (receptive i mo) as Hr.
  destruct (syscall_spec_witness i mo) as [eff mo' evs|] eqn:E.
  - destruct (exists_nonspurious ACFG _ _ _ _ _ Hr) as (eff2 & mo2 & evs2 & Hs2 & Hns2).
    exists eff2, mo2, evs2. apply nstep_munmap_iff. split; [|exact Hns2].
    rewrite <- (check_syscall_munmap i) by reflexivity. apply check_syscall_ok_iff. exact Hs2.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr.
    rewrite (check_syscall_munmap i) in Hr by reflexivity. cbn [in_arg in_args nth pure_input i] in Hr.
    exact (munmap_safe_no_unmodeled _ _ _ _ Hsafe Hr).
Qed.

Lemma nstep_progress_mprotect : forall addr len prot mo,
  nsafe (NMprotect addr len prot) mo -> exists rsp mo' evs, nstep (NMprotect addr len prot) mo rsp mo' evs.
Proof.
  intros addr len prot mo Hsafe. set (i := pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]).
  pose proof (receptive i mo) as Hr.
  destruct (syscall_spec_witness i mo) as [eff mo' evs|] eqn:E.
  - destruct (exists_nonspurious ACFG _ _ _ _ _ Hr) as (eff2 & mo2 & evs2 & Hs2 & Hns2).
    exists eff2, mo2, evs2. apply nstep_mprotect_iff. split; [|exact Hns2].
    rewrite <- (check_syscall_mprotect i) by reflexivity. apply check_syscall_ok_iff. exact Hs2.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr.
    rewrite (check_syscall_mprotect i) in Hr by reflexivity. cbn [in_arg in_args nth pure_input i] in Hr.
    exact (mprotect_safe_no_unmodeled _ _ _ _ _ Hsafe Hr).
Qed.

Lemma nstep_progress_settid : forall mo, exists rsp mo' evs, nstep NSetTid mo rsp mo' evs.
Proof.
  intros mo. cbn [nstep]. destruct (m_tid mo) as [t0|] eqn:E.
  - exists (eff0 t0), mo, []. split; [reflexivity|]. exists t0. auto.
  - exists (eff0 (Z_to_bv 64 1)), (with_tid (Z_to_bv 64 1) mo), []. split; [reflexivity|]. exists (Z_to_bv 64 1). split; [reflexivity|].
    rewrite unsigned_lit by lia. unfold Fork.PID_MAX_ENVELOPE. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma tglob_PhiP_intro : forall {R} (t : itree node R) mo,
  minv mo -> m_halted mo = None -> tsafe nstep nsafe t mo -> tnf t mo -> tglob nstep PhiP t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo Hmi Hh Hs Hn; cbn -[NF]; [exact I|].
  cbn -[NF] in Hs, Hn. destruct Hs as [Hsafe Hs]. destruct Hn as [HNF Hn].
  split; [split; [exact Hmi|]; split; [exact Hh|]; split; [exact Hsafe| exact HNF]|].
  intros rsp mo' evs Hst. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi'].
  apply IH; [exact Hmi'| exact Hh'| exact (Hs _ _ _ Hst)| exact (Hn _ _ _ Hst)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition good_ans (e : Malloc.ev) (z : Z) : Prop :=
  match e with
  | EMmap a len prot flags => Z.land flags MAP_FIXED_Z =? 0 = true -> Malloc.is_err z = false
  | EMprotect _ _ _ => z = 0
  | _ => True
  end.

(* [comment removed for export] *)
Fixpoint sgood {R} (P : R -> Prop) (t : stree Malloc.ev Z R) : Prop :=
  match t with
  | SRet r => P r
  | SVis (EUndef _) _ => True
  | SVis (EPeek _ _ _) _ => True
  | SVis e k => forall z, good_ans e z -> sgood P (k z)
  end.

Lemma sgood_vis {R} (P : R -> Prop) e k : (forall z, good_ans e z -> sgood P (k z)) -> sgood P (SVis e k).
Proof. intros H. destruct e; cbn; auto. Qed.

Lemma sgood_bind {A B} (P1 : A -> Prop) (P : B -> Prop) (t : stree Malloc.ev Z A) (f : A -> stree Malloc.ev Z B) :
  sgood P1 t -> (forall a, P1 a -> sgood P (f a)) -> sgood P (sbind t f).
Proof.
  induction t as [r|e k IH]; intros Ht Hf; cbn [sbind].
  - apply Hf. exact Ht.
  - destruct e; cbn in Ht |- *; auto.
Qed.

Lemma sgood_mono {R} (P P' : R -> Prop) (t : stree Malloc.ev Z R) : sgood P t -> (forall r, P r -> P' r) -> sgood P' t.
Proof. induction t as [r|e k IH]; intros Ht HP; cbn in *; [auto|]. destruct e; auto; intros z Hz; apply IH; auto. Qed.

Section Walk.
Context {R : Type}.
Variable P : R -> Prop.
Local Notation sgood := (sgood P).

Ltac sg_leaf := first [ assumption | exact I | apply sgood_vis ].

Lemma guard_sg tag c (k bail : Malloc.M R) : sgood k -> sgood (guard tag c k bail).
Proof. intros Hk. unfold guard. destruct c; [exact Hk| exact I]. Qed.

Lemma bad_answer_sg (bail : Malloc.M R) : sgood (bad_answer bail).
Proof. exact I. Qed.

Lemma queue_sg h m st (k : mstate -> Malloc.M R) bail : (forall st', sgood (k st')) -> sgood (queue h m st k bail).
Proof. intros Hk. unfold queue. apply guard_sg. apply guard_sg. destruct (get_head st h); apply Hk. Qed.

Lemma free_meta_sg m st (k : mstate -> Malloc.M R) bail : (forall st', sgood (k st')) -> sgood (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply queue_sg. exact Hk. Qed.

Lemma activate_group_sg m st (k : mstate -> Z -> Malloc.M R) bail : (forall st' z, sgood (k st' z)) -> sgood (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply guard_sg. apply Hk. Qed.

Lemma am_take_sg st (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_take st k bail).
Proof. intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk| exact I]. Qed.

Lemma am_carve_sg st p (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_carve st p k bail).
Proof. intros Hk. unfold am_carve. apply am_take_sg. exact Hk. Qed.

Lemma am_finish_sg st nu (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu); [|apply am_carve_sg; exact Hk].
  cbn -[am_carve]. intros z ->. cbn -[am_carve]. apply am_carve_sg. exact Hk.
Qed.

Lemma am_after_brk_sg st nu (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0); [|apply am_finish_sg; exact Hk].
  cbn -[am_finish new_region Malloc.mmap_answer_ok Malloc.is_err]. intros z Hz. destruct (negb (Malloc.mmap_answer_ok _ _ _ z)); [exact I|].
  rewrite (Hz eq_refl). destruct (new_region RKMeta z _ st) as [st1 rid]. apply am_finish_sg. exact Hk.
Qed.

(* [comment removed for export] *)
Ltac sgauto Hk :=
  repeat first
    [ exact I
    | apply Hk
    | apply am_after_brk_sg; [exact Hk]
    | apply am_finish_sg; [exact Hk]
    | apply am_take_sg; [exact Hk]
    | apply guard_sg
    | progress (cbv zeta)
    | lazymatch goal with
      | |- sgood (SVis _ _) => apply sgood_vis; intros ? ?
      | |- sgood (if ?c then _ else _) => destruct c
      | |- sgood (match ?x with _ => _ end) => destruct x
      end ].

Lemma alloc_meta_sg st (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (alloc_meta st k bail).
Proof. intros Hk. unfold alloc_meta. sgauto Hk. Qed.

Lemma ta_fin_sg st m mask (k : mstate -> Z -> Malloc.M R) : (forall st' z, sgood (k st' z)) -> sgood (ta_fin st m mask k).
Proof. intros Hk. unfold ta_fin. apply Hk. Qed.

Lemma try_avail_sg sc st (k : mstate -> Z -> Malloc.M R) bail : (forall st' z, sgood (k st' z)) -> sgood (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail.
  repeat first
    [ exact I
    | apply Hk
    | apply ta_fin_sg; [exact Hk]
    | apply guard_sg
    | apply activate_group_sg; intros ? ?
    | progress (cbv zeta)
    | lazymatch goal with
      | |- sgood (if ?c then _ else _) => destruct c
      | |- sgood (match ?x with _ => _ end) => destruct x
      end ].
Qed.

Lemma ag_tail_sg lay st sc m p cnt ai (k : mstate -> optr -> Malloc.M R) : (forall st' g, sgood (k st' (Some g))) -> sgood (ag_tail lay st sc m p cnt ai k).
Proof. intros Hk. unfold ag_tail. apply Hk. Qed.

Lemma alloc_group_sg lay (aslot : mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R) st sc req (k : mstate -> optr -> Malloc.M R) bail :
  (forall st' g, sgood (k st' (Some g))) ->
  (forall st' sc' req' k', (forall st'' idx, 0 <= idx -> sgood (k' st'' idx)) -> sgood (aslot st' sc' req' k' bail)) ->
  sgood (alloc_group R lay aslot st sc req k bail).
Proof.
  intros Hk Has. unfold alloc_group. apply alloc_meta_sg. intros st1 m.
  repeat first
    [ exact I
    | apply ag_tail_sg; [exact Hk]
    | progress (cbv zeta)
    | lazymatch goal with
      | |- sgood (SVis _ _) => apply sgood_vis; intros ? HANS
      | |- sgood (if Malloc.is_err ?r then _ else _) => rewrite (HANS eq_refl)
      | |- sgood (if ?c then _ else _) => destruct c
      | |- sgood (match ?x with _ => _ end) => destruct x
      | |- sgood (aslot _ _ _ _ _) => apply Has; intros ? idx Hidx; replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia)
      end ].
Qed.

Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma alloc_slot_sg lay : forall fuel st sc req (k : mstate -> Z -> Malloc.M R) bail,
  (forall st' idx, 0 <= idx -> sgood (k st' idx)) -> sgood (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [exact I|].
  apply try_avail_sg. intros st1 first. destruct (negb (first =? 0)); [apply Hk; apply ctz32_nonneg|].
  apply alloc_group_sg.
  - intros st2 g. cbn. apply queue_sg. intros st4. apply Hk. lia.
  - intros st' sc' req' k' Hk'. apply IH. exact Hk'.
Qed.

Lemma malloc_small_ctrl_sg lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  (forall st' g i, sgood (k st' (Some (g, i)))) -> sgood (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hk. unfold malloc_small_ctrl. cbn beta iota zeta.
  match goal with |- sgood (match ?g with _ => _ end) => destruct g as [gp|] end;
    [match goal with |- sgood (if ?c then _ else _) => destruct c end; [apply Hk|] |];
    (apply alloc_slot_sg; intros st1 idx Hidx; replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia);
     destruct (active st1 _) as [gp'|]; [apply Hk| exact I]).
Qed.
End Walk.

Lemma malloc_core_sg lay st n : size_overflows n = false ->
  sgood (fun r : mstate * option (aptr * Z) => snd r <> None) (malloc_core lay st n).
Proof.
  intros Hov. unfold malloc_core. rewrite Hov.
  destruct (MMAP_THRESHOLD <=? n).
  - repeat first
      [ exact I
      | progress (cbv zeta)
      | lazymatch goal with
        | |- sgood _ (SRet _) => cbn; discriminate
        | |- sgood _ (Malloc.ret _) => cbn; discriminate
        | |- sgood _ (SVis _ _) => apply sgood_vis; intros ? HANS
        | |- sgood _ (if Malloc.is_err ?r then _ else _) => rewrite (HANS eq_refl)
        | |- sgood _ (if ?c then _ else _) => destruct c
        | |- sgood _ (match ?x with _ => _ end) => destruct x
        | |- sgood _ (alloc_meta _ _ _) => apply alloc_meta_sg; intros ? ?
        end ].
  - apply malloc_small_ctrl_sg. intros st' g i. cbn. discriminate.
Qed.

Lemma cmalloc_sg cs n : size_overflows n = false ->
  sgood (fun r : mstate * option cptr => snd r <> None) (cmalloc cs n).
Proof.
  intros Hov. unfold cmalloc. eapply sgood_bind; [apply malloc_core_sg; exact Hov|].
  intros [st1 [[g idx]|]] H; cbn in H |- *; [discriminate| exfalso; apply H; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma is_err_of_addr_ok : forall atop len avoid a, 0 < len -> atop < 2^63 -> mmap_addr_ok atop len avoid a = true -> Malloc.is_err a = false.
Proof.
  intros atop len avoid a Hlen Hat H. apply mmap_addr_ok_true in H as [(_ & Ha & Hc) _].
  pose proof (mmap_len_ge len Hlen). unfold Malloc.is_err, Malloc.TWO64. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma tpath_sys_then {St A B} (n : node) (dec : resp -> option A) (k : A -> M St B) (s : St) mo tr x mo' :
  tpath nstep (mbind (msys n dec) k s) mo tr x mo' ->
  exists rsp mo1 evs, nstep n mo rsp mo1 evs /\
    ((x = Unr /\ tr = evs /\ dec rsp = None) \/ (exists a tr2, dec rsp = Some a /\ tpath nstep (k a s) mo1 tr2 x mo' /\ tr = evs ++ tr2)).
Proof.
  intros Hp. apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)].
  - apply tpath_msys_any in Hp as (rsp & Hst & E). exists rsp, mo', tr. split; [exact Hst|]. left.
    destruct (dec rsp); [discriminate|]. auto.
  - apply tpath_msys_ok in Hp1 as (rsp & Hst & Hd & ->). exists rsp, mo1, tr1. split; [exact Hst|]. right. exists a, tr2. auto.
Qed.

Ltac pure_tail H :=
  repeat first
    [ apply tpath_mret in H as (? & ? & ?)
    | apply tpath_mupd in H as (? & ? & ?)
    | apply tpath_mbind_any in H as [[H ?]|(? & ? & ? & ? & ? & ? & H & ?)]
    | match type of H with tpath _ (match ?a with _ => _ end _) _ _ _ _ => destruct a end ];
  subst.

(* [comment removed for export] *)
Lemma ev_step_silent : forall atop e s mo tr x mo', tpath nstep (ev_step atop e s) mo tr x mo' -> tr = [].
Proof.
  intros atop e s mo tr x mo' Hp. destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; cbn [ev_step] in Hp.
  - destruct (req =? 0).
    + apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). pose proof (nstep_mm_vm_only (NBrk 0) _ _ _ _ I Hst) as [_ ->].
      destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]. pure_tail Hp; reflexivity.
    + unfold mbind at 1 in Hp. unfold mget in Hp. cbn [ebind ITree.bind fst snd] in Hp.
      apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). pose proof (nstep_mm_vm_only (NBrk req) _ _ _ _ I Hst) as [_ ->].
      destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]. pure_tail Hp; reflexivity.
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)];
      (apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC); pose proof (nstep_mm_vm_only (NMmap addr len prot flags) _ _ _ _ I Hst) as [_ ->];
       destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]; pure_tail Hp; reflexivity).
  - apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). pose proof (nstep_mm_vm_only (NMunmap addr len) _ _ _ _ I Hst) as [_ ->].
    destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]. pure_tail Hp; reflexivity.
  - apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). pose proof (nstep_mm_vm_only (NMprotect addr len prot) _ _ _ _ I Hst) as [_ ->].
    destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]. pure_tail Hp; reflexivity.
  - cbn in Hp. destruct Hp as (_ & _ & ->). reflexivity.
  - cbn in Hp. destruct Hp as (_ & _ & ->). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ev_step_noexit : forall atop e s mo tr, ~ texit nstep nexit (ev_step atop e s) mo tr.
Proof.
  intros atop e s mo tr Hx. destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; cbn [ev_step] in Hx.
  - destruct (req =? 0).
    + apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)|].
      apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & ? & Hx & ?)]; [exact (texit_mupd _ _ _ _ Hx)| exact (texit_mret _ _ _ _ Hx)].
    + unfold mbind at 1 in Hx. unfold mget in Hx. cbn [ebind ITree.bind fst snd] in Hx.
      apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)|].
      destruct a; [apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & ? & Hx & ?)]; [exact (texit_mupd _ _ _ _ Hx)| exact (texit_mret _ _ _ _ Hx)]| exact (texit_mret _ _ _ _ Hx)].
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)];
      (apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)| exact (texit_mret _ _ _ _ Hx)]).
  - apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)| exact (texit_mret _ _ _ _ Hx)].
  - apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)| exact (texit_mret _ _ _ _ Hx)].
  - exact Hx.
  - exact Hx.
Qed.

(* [comment removed for export] *)
Lemma ev_step_good : forall atop e s mo tr z s' mo',
  atop < 2^63 ->
  match e with EMmap _ len _ _ => 0 < len | _ => True end ->
  tglob nstep PhiP (ev_step atop e s) mo -> tpath nstep (ev_step atop e s) mo tr (Ok (z, s')) mo' -> good_ans e z.
Proof.
  intros atop e s mo tr z s' mo' Hat Hlen HG Hp. destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; cbn [good_ans]; auto.
  - cbn [ev_step] in HG, Hp. intros EF. rewrite EF in HG, Hp. cbn [negb] in HG, Hp.
    assert (HNF : NF (NMmap addr len prot flags) mo).
    { destruct (prot =? 0); cbn -[NF PhiP] in HG; (destruct HG as [HP _]; destruct HP as (_ & _ & _ & HNF); exact HNF). }
    destruct (prot =? 0);
      (apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC); destruct HC as [(E & _)|(a & tr2 & Hd & Hp & _)]; [discriminate|];
       apply (proj1 (tpath_mret _ _ _ _ _ _)) in Hp as (E & _ & _)).
    + destruct a as [e|x]; [exfalso; pose proof (dec_mmap_none_err_errno _ _ _ _ _ Hd) as He; rewrite (HNF _ _ _ Hst) in He; discriminate|].
      injection E as -> _. destruct (dec_mmap_none_Some _ _ _ _ _ Hd) as (ci & _ & Hok). eapply is_err_of_addr_ok; [exact Hlen| exact Hat| exact Hok].
    + destruct a as [e|x]; [exfalso; pose proof (dec_mmap_err_errno _ _ _ _ _ Hd) as He; rewrite (HNF _ _ _ Hst) in He; discriminate|].
      injection E as -> _. destruct (dec_mmap_Some _ _ _ _ _ Hd) as (ci & _ & Hok). eapply is_err_of_addr_ok; [exact Hlen| exact Hat| exact Hok].
  - cbn [ev_step] in HG, Hp.
    assert (HNF : NF (NMprotect addr len prot) mo).
    { cbn -[NF PhiP] in HG. destruct HG as [HP _]. destruct HP as (_ & _ & _ & HNF). exact HNF. }
    apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). destruct HC as [(E & _)|(a & tr2 & Hd & Hp & _)]; [discriminate|].
    apply (proj1 (tpath_mret _ _ _ _ _ _)) in Hp as (E & _ & _). injection E as -> _.
    destruct a as [e|b]; [|reflexivity]. exfalso.
    unfold dec_mprotect_rw in Hd. destruct (dec_mprotect addr len rsp) as [[e'|[|]]|] eqn:Hd'; try discriminate.
    pose proof (dec_mprotect_err_errno _ _ _ _ Hd') as He. rewrite (HNF _ _ _ Hst) in He. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ev_step_exists : forall atop e s mo,
  match e with
  | EBrk req => True
  | EMmap addr len prot flags => nsafe (NMmap addr len prot flags) mo /\ mmap_noreserve_b (Z_to_bv 64 flags) = false
  | EMunmap addr len => nsafe (NMunmap addr len) mo
  | EMprotect addr len prot => nsafe (NMprotect addr len prot) mo
  | _ => True
  end ->
  exists tr r mo', tpath nstep (ev_step atop e s) mo tr r mo'.
Proof.
  intros atop e s mo He.
  assert (SYS : forall A B (n : node) (dec : resp -> option A) (k : A -> M PState B) rsp mo1 evs,
            nstep n mo rsp mo1 evs ->
            (forall a, exists tr r mo', tpath nstep (k a s) mo1 tr r mo') ->
            exists tr r mo', tpath nstep (mbind (msys n dec) k s) mo tr r mo').
  { intros A B n dec k rsp mo1 evs Hst Hk. destruct (dec rsp) as [a|] eqn:Hd.
    - destruct (Hk a) as (tr & r & mo' & Hp). exists (evs ++ tr), r, mo'. unfold mbind. apply tpath_ebind. right.
      exists evs, (a, s), mo1, tr. split; [| auto]. unfold msys. apply tpath_enode. exists rsp. rewrite Hd. auto.
    - exists evs, Unr, mo1. unfold mbind. apply tpath_ebind. left. split; [| reflexivity]. unfold msys. apply tpath_enode. exists rsp. rewrite Hd. auto. }
  assert (RET : forall A (a : A) (s1 : PState) mo1, exists tr r mo', tpath nstep (mret a s1) mo1 tr r mo').
  { intros A a s1 mo1. exists [], (Ok (a, s1)), mo1. cbn. auto. }
  assert (UPD : forall (f : PState -> PState) (s1 : PState) mo1 B (k : unit -> M PState B),
            (forall s2, exists tr r mo', tpath nstep (k tt s2) mo1 tr r mo') -> exists tr r mo', tpath nstep (mbind (mupd f) k s1) mo1 tr r mo').
  { intros f s1 mo1 B k Hk. destruct (Hk (f s1)) as (tr & r & mo' & Hp). exists tr, r, mo'. unfold mbind, mupd. cbn [ebind ITree.bind fst snd]. exact Hp. }
  destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; cbn [ev_step].
  - destruct (req =? 0).
    + destruct (nstep_progress_brk 0 mo) as (rsp & mo1 & evs & Hst). eapply SYS; [exact Hst|]. intros a. apply UPD. intros s2. apply RET.
    + unfold mbind at 1. unfold mget. cbn [ebind ITree.bind fst snd].
      destruct (nstep_progress_brk req mo) as (rsp & mo1 & evs & Hst). eapply SYS; [exact Hst|]. intros [|]; [apply UPD; intros; apply RET| apply RET].
  - destruct He as [Hsafe Hnr]. destruct (nstep_progress_mmap addr len prot flags mo Hsafe Hnr) as (rsp & mo1 & evs & Hst).
    destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)]; (eapply SYS; [exact Hst|]; intros; apply RET).
  - destruct (nstep_progress_munmap addr len mo He) as (rsp & mo1 & evs & Hst). eapply SYS; [exact Hst|]. intros; apply RET.
  - destruct (nstep_progress_mprotect addr len prot mo He) as (rsp & mo1 & evs & Hst). eapply SYS; [exact Hst|]. intros; apply RET.
  - exists [], Unr, mo. cbn. auto.
  - exists [], Unr, mo. cbn. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma membed_silent {R} atop (t : stree Malloc.ev Z R) : forall s mo tr x mo', tpath nstep (membed atop t s) mo tr x mo' -> tr = [].
Proof.
  induction t as [r|e k IH]; intros s mo tr x mo' Hp; cbn [membed] in Hp.
  - apply tpath_mret in Hp as (_ & _ & ->). reflexivity.
  - apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & z & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + eapply ev_step_silent. exact Hp.
    + rewrite (ev_step_silent _ _ _ _ _ _ _ Hp1), (IH _ _ _ _ _ _ Hp2). reflexivity.
Qed.

Lemma membed_noexit {R} atop (t : stree Malloc.ev Z R) : forall s mo tr, ~ texit nstep nexit (membed atop t s) mo tr.
Proof.
  induction t as [r|e k IH]; intros s mo tr Hx; cbn [membed] in Hx.
  - exact (texit_mret _ _ _ _ Hx).
  - apply texit_mbind in Hx as [Hx|(tr1 & z & s1 & mo1 & tr2 & _ & Hx & ->)]; [exact (ev_step_noexit _ _ _ _ _ Hx)| exact (IH _ _ _ _ Hx)].
Qed.

Lemma ev_step_nsafe : forall atop e s mo, tglob nstep PhiP (ev_step atop e s) mo ->
  match e with
  | EMmap addr len prot flags => nsafe (NMmap addr len prot flags) mo
  | EMunmap addr len => nsafe (NMunmap addr len) mo
  | EMprotect addr len prot => nsafe (NMprotect addr len prot) mo
  | _ => True
  end.
Proof.
  intros atop e s mo HG. destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; auto; cbn [ev_step] in HG.
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)]; cbn -[NF PhiP nsafe] in HG; destruct HG as [HP _]; destruct HP as (_ & _ & HS & _); exact HS.
  - cbn -[NF PhiP nsafe] in HG. destruct HG as [HP _]. destruct HP as (_ & _ & HS & _). exact HS.
  - cbn -[NF PhiP nsafe] in HG. destruct HG as [HP _]. destruct HP as (_ & _ & HS & _). exact HS.
Qed.

Lemma noreserve_MAPF : mmap_noreserve_b (Z_to_bv 64 MAPF) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "p;2p;1p;3g00:fj25Tg004@j10Tg005Cj12Tg00;Zj21Tg00hEj14Tg00;@j33Tg00d:R0g00neR1'5g00_1#0#0#0#0#0#0#2g05l:'1#4=301do"). Qed.
Lemma noreserve_MAPFX : mmap_noreserve_b (Z_to_bv 64 MAPFX) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "p;2p;1p;3g00:fj25Tg004@j10Tg005Cj12Tg00;Zj21Tg00hEj14Tg00;@j33Tg00d:R0g00neR1'5g00_1#0#0#0#0#0#0#2g05lm'1#4=301do"). Qed.

(* [comment removed for export] *)
Lemma membed_stot {R} (t : stree Malloc.ev Z R) : forall Post (G : PState -> Model -> Prop) L s mo (P : R -> Prop),
  frame_ok G -> ctree_ok L t Post -> KL L (ps_brk s) mo -> G s mo -> sgood P t -> tglob nstep PhiP (membed (ld_atop L) t s) mo ->
  (forall tr x mo', tpath nstep (membed (ld_atop L) t s) mo tr x mo' -> match x with Unr => True | Ok (r, _) => P r end)
  /\ (exists x mo', tpath nstep (membed (ld_atop L) t s) mo [] x mo').
Proof.
  induction t as [r|e k IH]; intros Post G L s mo P HG Hok HK HGs Hsg HT; cbn [membed] in HT |- *.
  - split.
    + intros tr x mo' Hp. apply tpath_mret in Hp as (-> & _ & _). exact Hsg.
    + exists (Ok (r, s)), mo. cbn. auto.
  - cbn [ctree_ok] in Hok. destruct Hok as [Hpre Hk].
    assert (NOTUP : match e with EUndef _ | EPeek _ _ _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
    assert (Hsgk : forall z, good_ans e z -> sgood P (k z)) by (destruct e; cbn in Hsg; auto; destruct NOTUP).
    assert (Hlen : match e with EMmap _ len _ _ => 0 < len | _ => True end).
    { destruct e; auto. cbn in Hpre. destruct Hpre as [(_ & _ & _ & _ & Hl)|(cur & _ & _ & -> & _)]; [lia| unfold PGSZ; lia]. }
    pose proof (tglob_ebind_l nstep PhiP _ _ _ HT) as HTe.
    pose proof (KL_atop_lt _ _ _ HK) as HKat.
    assert (STEP : forall tr1 z s1 mo1, tpath nstep (ev_step (ld_atop L) e s) mo tr1 (Ok (z, s1)) mo1 ->
              tr1 = [] /\ answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s1) mo1 /\ G s1 mo1 /\ good_ans e z
              /\ tglob nstep PhiP (membed (ld_atop L) (k z) s1) mo1).
    { intros tr1 z s1 mo1 Hp1.
      pose proof (ev_step_spec L e G s HG Hpre s mo (conj eq_refl (conj HK HGs))) as W.
      pose proof (twf_tpath _ _ _ _ _ _ W Hp1) as HQ. cbn [fst snd] in HQ. destruct HQ as (Hans & HK1 & HG1 & _).
      split; [exact (ev_step_silent _ _ _ _ _ _ _ Hp1)|]. split; [exact Hans|]. split; [exact HK1|]. split; [exact HG1|].
      split; [exact (ev_step_good _ _ _ _ _ _ _ _ (proj2 HKat) Hlen HTe Hp1)|].
      exact (tglob_ebind_r nstep PhiP _ _ _ _ _ _ HT Hp1). }
    split.
    + intros tr x mo' Hp. apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & z & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)]; [exact I|].
      destruct (STEP _ _ _ _ Hp1) as (-> & Hans & HK1 & HG1 & Hgood & HT1).
      rewrite <- (event_post_atop L e z) in HT1, Hp2.
      exact (proj1 (IH z Post G (event_post L e z) s1 mo1 P HG (Hk z Hans) HK1 HG1 (Hsgk z Hgood) HT1) _ _ _ Hp2).
    + assert (HEX : exists tr x mo', tpath nstep (ev_step (ld_atop L) e s) mo tr x mo').
      { apply ev_step_exists. pose proof (ev_step_nsafe (ld_atop L) e s mo HTe) as HS. destruct e; auto.
        split; [exact HS|]. cbn in Hpre. destruct Hpre as [(_ & _ & -> & _)|(cur & _ & _ & _ & _ & ->)]; [apply noreserve_MAPF| apply noreserve_MAPFX]. }
      destruct HEX as (tr0 & x0 & mo0 & Hp0). pose proof (ev_step_silent _ _ _ _ _ _ _ Hp0) as ->.
      destruct x0 as [|[z s1]].
      * exists Unr, mo0. unfold mbind. apply tpath_ebind. left. auto.
      * destruct (STEP _ _ _ _ Hp0) as (_ & Hans & HK1 & HG1 & Hgood & HT1).
        rewrite <- (event_post_atop L e z) in HT1.
        destruct (proj2 (IH z Post G (event_post L e z) s1 mo0 P HG (Hk z Hans) HK1 HG1 (Hsgk z Hgood) HT1)) as (x & mo' & Hp2).
        rewrite (event_post_atop L e z) in Hp2.
        exists x, mo'. unfold mbind. apply tpath_ebind. destruct x as [|[r s2]].
        -- right. exists [], (z, s1), mo0, []. auto.
        -- right. exists [], (z, s1), mo0, []. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).

Lemma vm_only_tables : forall mo mo', vm_only mo mo' -> m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo.
Proof. intros mo mo' (Hfd & _ & Hfs & _). unfold m_fds, m_fs. rewrite Hfd, Hfs. auto. Qed.

(* [comment removed for export] *)
Definition FRZ (G : PState -> Model -> Prop) (s0 : PState) (mo0 : Model) : PState -> Model -> Prop :=
  fun s mo => G s mo /\ ps_so s = ps_so s0 /\ ps_fa s = ps_fa s0 /\ m_fds mo = m_fds mo0 /\ m_fs mo = m_fs mo0.

Lemma frame_ok_FRZ G s0 mo0 : frame_ok G -> frame_ok (FRZ G s0 mo0).
Proof.
  intros HG s s' mo mo' Hfa Hso Hv (HGs & E1 & E2 & E3 & E4). destruct (vm_only_tables _ _ Hv) as [E5 E6].
  split; [eapply HG; eauto|]. repeat split; congruence.
Qed.

Theorem raw_malloc_STOT : forall X (G : PState -> Model -> Prop) n s mo,
  frame_ok G -> OWN X G s mo -> 0 <= n -> size_overflows n = false ->
  tglob nstep PhiP (raw_malloc n s) mo ->
  STOTP (raw_malloc n s) mo
        (fun r s' mo' => exists p, r = Some p /\ OWN (p :: X) G s' mo' /\ n < 2^63
                         /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros X G n s mo HG HO Hn Hov HT.
  pose proof (raw_malloc_spec X (FRZ G s mo) n (frame_ok_FRZ G s mo HG) Hn s mo ltac:(eapply OWN_weakG; [exact HO|]; intros; repeat split; auto)) as W.
  destruct HO as [(L & Hcr & HK & Hi) [Hnd HGs]].
  pose proof (MI_Contracts.cmalloc_contract_proof _ _ _ Hcr Hn) as Hok.
  unfold raw_malloc in HT, W |- *. unfold mbind at 1 in HT. unfold mbind at 1 in W. unfold mbind at 1. unfold mget in HT, W |- *. cbn [ebind ITree.bind fst snd] in HT, W |- *.
  rewrite (MI_Contracts.creach_atop _ _ Hcr) in HT, W |- *.
  pose proof (tglob_ebind_l nstep PhiP _ _ _ HT) as HTm.
  destruct (membed_stot (cmalloc (ps_m s) n) _ (FRZ G s mo) L s mo (fun r => snd r <> None) (frame_ok_FRZ G s mo HG) Hok HK
              ltac:(repeat split; auto) (cmalloc_sg _ _ Hov) HTm) as [SOUND (x0 & mo0 & EX)].
  split; [| split].
  - intros tr x mo' Hp. pose proof (twf_tpath _ _ _ _ _ _ W Hp) as HQ. cbn [fst snd] in HQ.
    apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & [st' p] & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)]; [destruct HQ|].
    pose proof (SOUND _ _ _ Hp1) as HS. cbn [snd] in HS. rewrite (membed_silent _ _ _ _ _ _ _ Hp1).
    unfold mbind, mupd in Hp2. cbn [ebind ITree.bind fst snd] in Hp2. apply tpath_mret in Hp2 as (-> & -> & ->). split; [reflexivity|].
    destruct p as [c|]; [| exfalso; apply HS; reflexivity]. cbn [fst snd] in HQ. destruct HQ as [HO' Hn63].
    pose proof (OWN_G _ _ _ _ HO') as (HGs' & Hso & Hfa & Hfds & Hfs).
    eexists _, _. split; [reflexivity|]. exists (c, fresh_off st' c n). split; [reflexivity|]. split; [eapply OWN_weakG; [exact HO'|]; intros [? _]; assumption|]. auto.
  - intros tr Hx. apply texit_mbind in Hx as [Hx|(tr1 & sp & s1 & mo1 & tr2 & _ & Hx & ->)]; [exact (membed_noexit _ _ _ _ _ Hx)|].
    destruct sp as [st' p]. unfold mbind, mupd in Hx. cbn [ebind ITree.bind fst snd] in Hx. exact Hx.
  - destruct x0 as [|[[st' p] s1]].
    +
      exfalso. assert (Hp : tpath nstep (mbind (membed (ld_atop L) (cmalloc (ps_m s) n)) (fun x => let '(st', p) := x in mupd (set_m st') ;;; mret match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end) s) mo [] Unr mo0).
      { unfold mbind at 1. apply tpath_ebind. left. auto. }
      exact (twf_tpath _ _ _ _ _ _ W Hp).
    + eexists _, _. unfold mbind at 1. apply tpath_ebind. right. exists [], (st', p, s1), mo0, []. split; [exact EX|]. split; [| reflexivity].
      cbn. auto.
Qed.

Theorem raw_free_STOT : forall X (G : PState -> Model -> Prop) p s mo,
  frame_ok G -> OWN (p :: X) G s mo ->
  tglob nstep PhiP (raw_free p s) mo ->
  STOTP (raw_free p s) mo
        (fun _ s' mo' => OWN X G s' mo' /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros X G p s mo HG HO HT.
  pose proof (raw_free_spec X (FRZ G s mo) p (frame_ok_FRZ G s mo HG) s mo ltac:(eapply OWN_weakG; [exact HO|]; intros; repeat split; auto)) as W.
  destruct HO as [(L & Hcr & HK & Hi) [Hnd HGs]].
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  pose proof (MI_Contracts.cfree_contract_proof _ _ _ Hcr Hin) as Hok.
  unfold raw_free in HT, W |- *. unfold mbind at 1 in HT. unfold mbind at 1 in W. unfold mbind at 1. unfold mget in HT, W |- *. cbn [ebind ITree.bind fst snd] in HT, W |- *.
  rewrite (MI_Contracts.creach_atop _ _ Hcr) in HT, W |- *.
  pose proof (tglob_ebind_l nstep PhiP _ _ _ HT) as HTm.
  destruct (membed_stot (cfree (ps_m s) (Some (fst p))) _ (FRZ G s mo) L s mo (fun _ => True) (frame_ok_FRZ G s mo HG) Hok HK
              ltac:(repeat split; auto) ltac:(clear; induction (cfree (ps_m s) (Some (fst p))) as [|e k IH]; cbn; [exact I| destruct e; auto]) HTm) as [_ (x0 & mo0 & EX)].
  split; [| split].
  - intros tr x mo' Hp. pose proof (twf_tpath _ _ _ _ _ _ W Hp) as HQ. cbn [fst snd] in HQ.
    apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & st' & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)]; [destruct HQ|].
    rewrite (membed_silent _ _ _ _ _ _ _ Hp1). apply tpath_mupd in Hp2 as (-> & -> & ->). split; [reflexivity|].
    rename HQ into HO'. pose proof (OWN_G _ _ _ _ HO') as (HGs' & Hso & Hfa & Hfds & Hfs).
    eexists _, _. split; [reflexivity|]. split; [eapply OWN_weakG; [exact HO'|]; intros [? _]; assumption|]. auto.
  - intros tr Hx. apply texit_mbind in Hx as [Hx|(tr1 & sp & s1 & mo1 & tr2 & _ & Hx & ->)]; [exact (membed_noexit _ _ _ _ _ Hx)| exact (texit_mupd _ _ _ _ Hx)].
  - destruct x0 as [|[st' s1]].
    + exfalso. assert (Hp : tpath nstep (mbind (membed (ld_atop L) (cfree (ps_m s) (Some (fst p)))) (fun st' => mupd (set_m st')) s) mo [] Unr mo0).
      { unfold mbind. apply tpath_ebind. left. auto. }
      exact (twf_tpath _ _ _ _ _ _ W Hp).
    + eexists _, _. unfold mbind. apply tpath_ebind. right. exists [], (st', s1), mo0, []. split; [exact EX|]. split; [| reflexivity]. cbn. auto.
Qed.

(* [comment removed for export] *)
Theorem startup_STOT : forall s mo, minv mo -> m_halted mo = None ->
  STOTP (startup s) mo (fun _ s' mo' => s' = s /\ m_vmmaps mo' = m_vmmaps mo /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ minv mo' /\ m_halted mo' = None
                                       /\ m_kernel mo' = m_kernel mo).
Proof.
  intros s mo Hmi Hh. unfold startup.
  eapply STOT_bind; [| intros a s' mo' H; exact (STOT_mono _ _ _ _ _ _ (STOT_ret _ _ tt s' mo') ltac:(intros ? ? ? (-> & -> & ->); exact H))].
  apply STOT_sys.
  - intros rsp mo' evs Hst. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi'].
    pose proof (nstep_dec_set_tid mo _ _ _ Hmi Hst) as (-> & t & Hd & _ & _). split; [reflexivity|]. exists t. split; [exact Hd|].
    cbn [nstep] in Hst. destruct Hst as (_ & t' & -> & Ht). split; [reflexivity|].
    destruct (m_tid mo); [destruct Ht as [_ ->]; auto 8| destruct Ht as [_ ->]]. rewrite m_vmmaps_with_tid, m_fds_with_tid, m_fs_with_tid. auto 8.
  - intros code mo' Hx. exact Hx.
  - apply nstep_progress_settid.
Qed.
