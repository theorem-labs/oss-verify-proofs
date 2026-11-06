(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
    exact (mmap_safe_no_unmodeled _ _ _ _ _ _ _ _ Hsafe Hr).
Qed.

Lemma nstep_progress_munmap : forall addr len mo,
  nsafe (NMunmap addr len) mo -> exists rsp mo' evs, nstep (NMunmap addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hsafe. set (i := pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]).
  pose proof (receptive i mo) as Hr.
  destruct (syscall_spec_witness i mo) as [eff mo' evs|] eqn:E.
  - exists eff, mo', evs. apply nstep_munmap_iff. rewrite <- (check_syscall_munmap i) by reflexivity. apply check_syscall_ok_iff. exact Hr.
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
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "p'0h01Hh11zh24addri004addrh33leni013lenh41Ph51Rh61ei021eh71kh84proti034proth95caddri045caddrh:5flagsi055flagsh;4hinti064hinth<1pi071ph=3whyi083whyh>1xp;3p;2p;1p;4p;5g01[nR0p4p70R1g01\cR2p4p710p8P1p1000`p4p710R3p8P1p101]Zp4p73110R4p8P1p101N^R5p4p710R6p8P1p101Q6p4p73110R7p8P1p101^Sp4p710R8p8P1p101_1p4p7210R9p8P1p101MiR:p4p7210R;p8P1p1001<p4p710R<p8P1p101_Np4p710R=p8P1p101`BR>p4p73110R?p8P1P>p4p741110R>p8P1p101a>R@p4p73110RAp8P1P@p4p741110R@p8P1p101b:RBp4p710RCp8P1PBp4p7210RBp8P1p101OOp4p710RDp8P1g01bWREp4p710RFp8P1p200RGp8P1p101cMp4p710RHp8P1p101dDp4p73110RIp8P1p101PBp4p741110RJp8P1p101e8p4p73110RKp8P1p101f2RLp4p73110RMp8P1PLp4p741110RLp8p101flp4p70R1P3p8P1P4p8P1P6p8P1P7p8P1P8p8P1P9p8P1P;p8P1P<p8P1P=p8P1P?p8P1P>p8P1PAp8P1P@p8P1PCp8P1PBp8P1PDp8P1PFp8P1PGp8P1PHp8P1PIp8P1PJp8P1PKp8P1PMp8P1PLp8PGPFp8p101gap4p70R1p101hVp4p710p8P1P3p8P1P5p4p7210p8P1p101hmp4p7210p8P1P;p8P1P:p4p73110p8P1P?p8P1PCp8P1PBp8P1PFp8P1PIp8P1PMp8P1PLp8P2j3:Tg01iaj21TPEj30Tg01jZj19Tg01kOj48Tg01lDj27Tg01m9j34Tg01mnj35Tg01ncj16Tg01oXj53Tg020OREg00^SR2f2RLf1R1f0RMD3p=2p-0\MRIf3RF9:E2^>2RB11LMf5RCf4R?PLP1O130[^12PE111Mf7R:f6R;P?P1O130[^12A2;1F90;C]0PL%91R5/1Mf8R3PCP1O170:RC[^12PMA2:5?90:;eW0X22PMO1P?PFPLP1C8R5/1Mf>f=RKf;RJP1O130[^12PMf<RHf:RD92K550KeW0X:2X82X32X22PFPLP1PMO417L1RK/1Mf9R5P:P1O150D[^12PMA25K;9053eW0X32X22P1PMO2A4FL1RK/1MP5P1O190HJRH[^12PMA2JK390JDeW0X82X32X22PLP1PMO3A5FL1RK/1MPH[^12g00f@RHA2JK390JDeW0X;2X92X<0PLP1PMO3g021D%61R0/1MPC[^12PHA2:0?90:;eW0W=PMO1n011020006101004010010110310520100101301001011033010710410610108PMO1W0X7BX6EX4IX5GPFPLP1PMO4W7X6EW4X5Go"). Qed.

Lemma sgood_bind {A B} (P1 : A -> Prop) (P : B -> Prop) (t : stree Malloc.ev Z A) (f : A -> stree Malloc.ev Z B) :
  sgood P1 t -> (forall a, P1 a -> sgood P (f a)) -> sgood P (sbind t f).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "p'0h02Hth11ah21Hh34addri004addrh41zh53leni013lenh61th71Ah81Bh92Hfh:1Ph;2P1h<1fh=4proti024proth>2IHh?5caddri035caddrh@1ei041ehA5flagsi055flagshB4hinti064hinthC1khD1pi071phE1rhF3whyi083whyp;3p;4p;1p;2p;7p;6p;5g01[nR0p4p70R1p1022Cp4p710R2p8P1p200R3p8P1p201R1p8p101flp4p70R4P2p8P4P3p8P4P1p8p1023>p4p70R4p101Q6p4p73110p8P4p1001<p4p710p8P4p101`Bp4p741110p8P4p101b:p4p710p8P4p101OOp4p741110p8P4p101dDp4p73110p8P4p101f2p4p741110p8P3g01]ZR4p4p73110p8P3g0247R5p4p73110p8P3g01bWR6p4p710R7p8P1P5p4p741110p8P1P7p8p101gap4p70R7P2p8P7P1p8P6j31Tg024lj45Tg01jZj1:Tg01kOj47Tg025cj2?Tg026Aj2>Tg00;@j34Tg026^j1=Tg01lDj28Tg01m9j39Tg01mnj3<Tg01ncj1;TP4j7BTg01\cj3ATP5j6@Tg01oXj56Tg020OR5g00^SR4f0R63Ap=3P5P4f3R7f2R2f1R8P6E@p=2f4R9P5P4P2P8P6D6717p=0P5P4P2P8P6D6p=Cp-0\8R:%37R;%39\9R<P5P4f5R=%3=f6R>?196f7R?P>P6O1R@f8RAP9P8O171>[]1RBPAP?P2P7C291?=[[W6P5P4P>P6C591>9P6P2P8O2PAP?P5P4PAP2C5P7C291?=eX9BW0XE=%3?\4P8P6O191A>f9RBPAP6O1f:RCP>P8O171A[]1RDPCPBP7P2O1P=C291B?[[\4PAP>PAP2P8D0P5f;R>PBP>P6P9D0P>PBP>P8f=REf<RFP@PAC2X14D0]0P9PFPCPF%:6P=D0g00edRAP?P8P2P8P6O2R@P=O3W2X44PFPCPF%:8f>RGPEP?P6O1PBC2X14RHD0eW0X34P6O1fBRIf@RJPIP7P2P8P6C7P>D0g00d:RKg027U,?2g00ahRL'>g01Km34%=8g00ne54K[PEP8P@P>O3W2X44PIPJPIP9P7P2P8C7fDfCPEP6O1f?RKC2X14D0eW0XA4X=4X54X34P7P2P8P6O4PGPFPG1886P?D0PBP8P@P?O3X2AX44PGPFPG1828PJPKPBP6O1P>C2X14D0eW0X54X34P8P6O2PJPGPJA9286PBD0A446LP>P8P@PBO3W2X44PJPGPJA9728PIfAP>P6O1PEC2X14RED0eW0X=4X54X34P2P8P6O3PJPGPJA<286PBD0P6PJPGPJA<728PED0eW0XB4X?4XD0P2P8P6O3g021DPFPCPF%;6P=D0P6PFPCPF%;8PHD0eW0WFP6O1n011040006101004010010110210520100101301001011023010710310610108P8O1PCPBACC97P=C291B?eX9DW0W>WCX@5P8FBX<<X6;X::X;:X81X73P=P9P7P2P8P6O6W<W6X::W;X81X73o"). Qed.

Lemma sgood_mono {R} (P P' : R -> Prop) (t : stree Malloc.ev Z R) : sgood P t -> (forall r, P r -> P' r) -> sgood P' t.
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "p'0h01zh12Hth21Hh34addri004addrh43leni013lenh51rh61th72HPh81Ph92P'h:1Rh;4proti024proth<2IHh=5caddri035caddrh>1ei041eh?5flagsi055flagsh@4hinti064hinthA1khB1pi071phC3whyi083whyp;3p;4p;5p;2p;1p;7p200R0g01]ZR1p4p73110p8P0g01bWR2p4p710p8P2j30Tg024lj46Tg01oXj53Tg01iaj21Tg01jZj18Tg01kOj47Tg01lDj24Tg01m9j35TP1j7:Tg01\cj39Tg020OR1g00^SR2f0R339p=2p-0R4\3R5f1R6P4[R7f2R8#2R9P1P2f3R:%2:f4R;?0:3f5R<P<P3O1P<P6O1[]5R=f6R>?0;8[[W6P1P2P;P3C690;:P3P8P6O2P1P2P>P8C690>;eX7=W1X5:%2<\2P6P3O190><f7R=P=P3O1P=P6O1R?[]5R@f8RAP:P8O170>[[\2P1P2P>P8P6D390><P1P1P4P31183f<RBf;RC;0?R?[^0211<3RDf?REf>RFf:P6O1RG30[^0211:3RHf=RIPAP6O1RJ70B[^0211;3RKf9RLP6O1RM90FIRN[^02g00edROPOn011040006101004010010110210520100101301001011023010710310610108P1P4P6A0ICJ\H^0211>3f@RHPCP6O1RJ70F[^02A0FBM\K^02A0EIG\D^02POPOn011040006101004010010110210520100101301001011023010710310610108]1P;%86/13P?[^02%88/13P=P6P8P6P3O2R?P<O3W2X02W1X32P3O1P;P:P8P6C7/13fBfAPIP6O130[^02P<P;P:P8C7/13PIP6P?PCO3W2X02W1X?2X;2X42X32P:P8P6P3O41486/13PN[^0214:8/13PLP6P?P=O3W2X02W1X42X32P6P3O2A5:86/13A0HEJ[^02A5;:8/13PCP6P?PLO3W2X02W1X;2X42X32P8P6P3O3g01[nP3X1OROX@2X=2WBP8P6P3O3g021DPOWCP3O1n011040006101004010010110210520100101301001011023010710310610108P6O1P1P2PAP;P:D390A>eX7@W1W<WAX>1P3F:X69X97X85X:0P:P8P6P3O4W6W9W8X:0o"). Qed.

Section Walk.
Context {R : Type}.
Variable P : R -> Prop.
Local Notation sgood := (sgood P).

Ltac sg_leaf := first [ assumption | exact I | apply sgood_vis ].

Lemma guard_sg tag c (k bail : Malloc.M R) : sgood k -> sgood (guard tag c k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h04bailh11ci001ch21kh33tagh42Hki011bp;1p;3p;5p101[np4p70p,1RR0p4p300R1p8p101flp4p70P1p8P1g028UR2p4p710p8P1g01bWR3p6051002p8P1p1029Gp6051001p8P1p102:Ap4p710p8P1g02;<R4p4p710p8P1p102<2p4p710p8P1p102<hp4p710p8P1p102=bp4p710p8P1p102>ap4p710p8P1p102?Yp4p710p8P1p102@Rp4p710p8P1p102ALp4p710p8P1p102BIp4p710p8P1p102CDp4p710p8P1p102D;p4p710p8P1p102E5p4p710p8P1p102Emp4p710p8P1p102Fip4p710p8P1p102Gdp4p710p8P2j15TP3j30Tg02Hfj12Tg01ncj11Tg01oXj54TP4j53Tg00^SR4g00d:R3%50R2p,1PR1f1R5500P3P3P2f0R6f3R7g020OP4P0f5#2#1P7V4D4n01100000200009001P7P6g00f@n0110100020000P0f4P7f2R8P5D39001eW4X02X22X13X34P7P8P5P6O4X02W2W1W3o"). Qed.

Lemma bad_answer_sg (bail : Malloc.M R) : sgood (bad_answer bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "h04bailp;1g028Uj10Tp,1R#0R0g00f@X00f0O1W0o"). Qed.

Lemma queue_sg h m st (k : mstate -> Malloc.M R) bail : (forall st', sgood (k st')) -> sgood (queue h m st k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h01rh14bailh21hh31kh41mh52sth62Hkh71ai001ah81oi011oh93st'i024headi035hprevi042pvi051xp;1p;3p;2p;5p;6g028Uj1DTg01bWj37Tg004ej19Tg02Iej24Tg02Jbj1CTg01><j1BTg02KYj2<Tg004@j1>Tg02LRj12Tg02MIj2=Tg02NBj18j21Tg02O=j1:j25Tg02P8j30Tg02Q1j36Tg02;<j5ATg02Qjj5;Tg02<2j6?Tg01=Zj2@Tg01[nR0f0R1'@p=3g02RcR2g02S[R3p,1RR4#DR5\3R6p,1PR7f2R8P1O1574^93g00_1R9#9f3R:f4R;'4R<#C%B0R='<P4%>9#9R9%2</<=R=g01;;R<P0P5f5R>,=:R?P:%3>R@#8P<P0P314;1#2f6RA#3RB#:g02TTRC14A8#2%38/51RD'1W0=0A>501f1RE,4>#2%3E/51RF'1X0C=0>;n10110300021010400501O1P8%3;15@1,1@X0C=0;:56>O1n10110500021010200RGPEDAPEP9P=PGPEP?g01flP<P0P<P0P5P1P>f7R?#3RG#8P<P0P314A1#2f8R<#3#:14<8#2/1DX0C=0<?50114?E#2/1FX0C=0?An10110300021010400501RFO1P;15G1,1GX0C=0A>96?BO1n101105000210102009747P1P:PFO1X70P1O1PE15B1,1BX0C=0>;96A@O1n10110100021010000b8D;D;P4P>P;P:P8PEE?9747eW6X15X36X53X40X22P;P:P8PEP1O5X15W3W5X40W2o"). Qed.

Lemma free_meta_sg m st (k : mstate -> Malloc.M R) bail : (forall st', sgood (k st')) -> sgood (free_meta m st k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "h04bailh11kh21mh32sth42Hkh53st'p;1p;3p;6p;5g028Uj14Tg01bWj30Tg02UKj32Tg02VDj61Tg02<hj53Tg01[nR0g02S[R1p,1RR2#4R3\1R4p,1PR5f2R6f0R7O1502^51g02W=f4R8g02X5f3R9528P6f1R:P7E1P2P8P9P6P:D39025eW4X03X14X31X20P9P6P:P7O4X03W1W3W2o"). Qed.

Lemma activate_group_sg m st (k : mstate -> Z -> Malloc.M R) bail : (forall st' z, sgood (k st' z)) -> sgood (activate_group m st k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h04bailh11kh21mh32sth42Hkh51rh63st'h71zi001ai011xp;1p;3p;2p;4p;5g028Uj1FTg01bWj34Tg003[j1>Tg004ej1;Tg02Iej20Tg02Xkj1ETg026Aj2?Tg02Ycj12Tg02Z[j11Tg00Ioj2<Tg02[Qj1:Tg00iJj18Tg02[mj49Tg02\Mj57Tg02\hj26Tg02]ij13Tg025cj25Tg02^cj2DTg02_Bj2CTg02`>j2@Tg02P8j3ATg02Qjj5BTg02=bj5=Tg01[nR0g02S[R1g00^SR2p,1RR3#FR4[\1R5p,1PR6f3R7f1R8f0R9O2543^72^61g00_1R:#>#;f4R;,07R<#Eg00ahR='?f2R>g02TTf5R?,0;R@#2RAg01;;RBP0P2%1@R@g02a:RC/<2RDPD%:DREPCP2g02aX%8:C9R:f6,0?#1D7,6?#3P=n10110100021010000R?'51DA?/C9'@W5=A;7R?%2<PBP0P2%1<PDPDPEP:P@D7,6;#3P=n10110100021010000'5R=O2P8P9P?P=O2DBP3P;P7P>P8D=9436eW4X04X15X31X20P7P>P8P9O4X04W1W3W2o"). Qed.

Lemma am_take_sg st (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_take st k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h04bailh11kh22sth32Hkh41ai001ah51ch61mi011mh71oi021oh81rh93st'i031xp;1p;2p;3p;5p;4g028Uj1BTg01=Zj21Tg01bWj30Tg02b6j12Tg02bjj1ATg01><j1:Tg02O=j24Tg02NBj23Tg02cgj25Tg02d\j16Tg004ej17Tg02e_j28Tg02f<j29Tg02gAj2@Tg02h@j2?Tg02P8j3;Tg01ncj1<Tg01oXj5=Tg02>aj4>Tg02S[R0g01flR1p,1RR2#BR3[\0R4g01[nR5p,1PR6f3R7f1R8f0R9,15R:O2502]6^90%27#AP1g01;;R1P5P1P5P3P9f5g02TT%:5R11419'3W8g02i8g02io,58,15%69g00_1#7'8/99'@W5f6'?5;9R1P:O2g020Og00^SR:P2g02ji#<f4V:D=n101103000210101009026P9P7P1P9O2X45P9O1g00f@n10110200021010000b7P2P7f2R7P8C>9026eW3X03X14X20P7P8P9O3X03W1W2o"). Qed.

Lemma am_carve_sg st p (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_carve st p k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h01ch14bailh21kh31ph42sth52Hkh61mh73st'i001ai012tli021xp;1p;3p;2p;4p;6p;7p;5g028Uj1VTg01bWj37Tg02cgj24Tg02f<j2UTg02gAj2RTg02khj4ITg02lFj6ETg02lgj4CTg02m;j4BTg02m[j4ATg02n7j1?Tg004ej1=Tg02o:j1TTg02e_j2STg030Bj2QTg031Lj2;Tg02h@j22Tg02b6j1:Tg032Qj1HTg033Rj4GTg033kj18Tg034cj69Tg0357j1DTg035oj1FTg036hj33Tg037_j76Tg0383j25Tg038mj1JTg03:0j1KTg02[Qj1@Tg01><j1LTg02\Mj5MTg03:ij1NTg03;`j4OTg02?Yj5PTg01=Zj2>Tg004@j1<Tg01[nR0f0R1'>p=0%<1#<p=1g02S[R2g01flp,1RR3#VR4[\2R5p,1PR6f3R7f1R8%01O2573^60^72g02i8R9f4R:g03<['4#0g03=TR;/U1'RW0P0g03>KR<P0g02a:R=g03?BR>g00^SR?g03?[R@CIRAP=P>g03@4P?P@g03@REER@P<CCR?P0P<P?P0PAP@P<CBCAR>P7%07R=#?g01;;RBP0P2g00_1RC#1#1#1#1#1#1#=RD,4:#0%T1%=C'S/Q1RC';X09/2:RE#:#HP0P<P?P>P1PBP<P<P0P<P?P0PAP@P<CGR@P1f5RA/4D#0/;CX09/2AR9#8RCE9%D1%0A%F133g00ahRA%0:;3An10110200021010000PCF6/59%J=/2En10110200021010100'2RE#:#KP<P<%@<%L0=3AAP0P<P?P@P7%8ER@E9DM#N;3;P@F6/5E'2f2REP8P1COP3P:P7PEP8DP9736eW5X14X25X30X42P7PEP8P1O4X14W2X30W4o"). Qed.

Lemma am_finish_sg st nu (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_finish st nu k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h01rh14bailh21kh32nuh42sth51zh61Hh72Hkh81bi001bh91mh:1oi011oh;1pi021ph<3st'i031ai04>need_unprotecti051xp;1p;2p;3p;5p;6g028Uj1ITg01=Zj2HTg01bWj30Tg02b6j1<Tg03A0j1GTg03B3j3DTg03BPj2BTg026Aj21Tg03C0j17Tg03CNj25Tg01\cj3;Tg03DCj18Tg02:Aj24Tg02e_j2FTg03EFj2:Tg02?Yj52Tg01><j1CTg01ncj1ATg00;@j3@Tg03Ecj59Tg001<j6?Tg02@Rj5>Tg01m9j3ETg01oXj5=Tf0R0g03F_R1g03GT3Ep=6g020OR2g00^SR3f2R4f1R5P0D=p=3g02S[R6g00d:R7g01flR8p,1RR9#IR:[\6R;g01[nR<p,1PR=f3R>P51H<0O2509]9^<6f4R?#<#GP8g01;;R8P<P8P<P:P0P7P:P7P7g02a:?D30/B1g00ahR1'1#7g00nef6R8n0100000020000R@f7RA/50#6P7A;239R2%80#7RBf5RC,49P7P21101g03HLg03IB'FRD,10':REP9f8RFP5P8PCD2P8PF%C<RGO2n0100000020000n0100000020000X03539P9PAP0PCP?D2n0110400020000g02ji#AP?V3539n10110500021010200909=P0P@P7P7P7P:P0f9R@/54#6P7P2PB149ARHP7P2PEP9f:RIP>PFPAD2RJPFPIPGO2RKn0100000020000n0100000020000X03539P9P@P4PAP8D2RLn0110400020000909=P0A@301P3P1P7P2PB149FP7P2PEP9f;RMP?P@PFD2P@PMPGO2n0100000020000n0100000020000909=X53PIP>PFPAP8D9P7P2%81#7PHP7P21111111D':PJPKn0100000020000n0100000020000909=eP5P0E?W6X5315F5#6P7P2PB1498P7P2PEPLPAP@PGO2n0100000020000n0100000020000X03539909=ePFP5P8PCP?D9n0110000020000b8X;<P0O1g00f@n10110100021110300b:P9P?P>P4P5D>909=eW7X1:X2;X37X46P>P4P5P0O4X1:W2W3W4o"). Qed.

Lemma am_after_brk_sg st nu (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_after_brk st nu k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h01ch11bi001bh24bailh31kh42nuh51rh62sth72Hkh82Hzh91mi011mh:1pi021ph;3ridi033ridh<3st'h=3st1i043st1h>1zi051ni061xp;1p;2p;3p;4p;5p;6g028Uj1UTg01=Zj2ITg01bWj31Tg02b6j1=Tg02o:j1TTg026Aj2ETg004@j1STg004ej1@Tg03J9j25Tg03JVj2?Tg01kOj4DTg01\cj3JTg03K3j1HTg03Kjj1FTg03Lfj4<Tg03C0j1;Tg02:Aj2:Tg026^j18Tg01><j1RTg03Mej49Tg03N`j1BTg02e_j26Tg00IoR0j2ATg02[mj4NTg031Lj2MTg030Bj27Tg03Ocj22Tg02h@j24Tg02@Rj53Tg01oXj5>Tg025cj2LTg00;@j3GTg03Phj5CTg00:fj2KTg001<j6OTg02ALj5PTg03Qej2QTf1R1f0R2#=#B'Qp=0g02S[R3g00d:R4g01flp,1RR5#UR6[\3R7g01[nR8p,1PR9f3R:P11I82O2515]9^<3f4R;#=#Tg00ahR<'EP4P4P4P6P2g020OR=g00^SR>P5P<g00_1R?#S#@R@f6RA'0g03F_RB'5RCg03RERDg03S?g03T;'?RECDP4AJ=>5RFf7RG#HRH%FGRI10@G/5BRJP2C<#;1:5;P4PF%82RKf5RLPG%R8R8O2P0P3g02a:RMPFg03U4RNP2PJPGC9P5g02i8RO%B2%@?R?'?RPf:RQ,0@/6?1AM>PMP>P1PBCN'I/M2RR'7'2W0/41f8RSPGPAD3n2001106000120104103n0100000020000n0100000020000X5>D>P5PAPLP;P:D3n01000000200009159P2g027U,LE/E<RTg01Km5G4%81g00neRU5G4[PHPIPJP1C<#;P4P4P4PFP21:5AP4PF%8:PGf9RJP8O2RIP0P3PMPFPNP:10@JRH/5BPJC9P5f<RV,0@/6?/7R,2PX0O/41PQPJPSD3n2001106000120104103RWn0100000020000n01000000200009159P2g00f@P4PUP4PFP2PIPWn01000000200009159X14PNf2RW10@S/5BPSC91A3MP0P3PMP0P3PMPFP2P5f=,0@/6?/7R,2PX0O/41f;RSPQPJD3n20011060001201041039159P2f>,0@/6?/7R,2PX0O/41PVPSPQPJDCX;MX=3P1P2O2n2001102000120101105b:%8WP11K4TO1EOn0110000020000b1W8X>>P=P>P5P<10@L/5BPDPECDP4PF%HA%FAPCP2C<#;1:5:P4PFPKP;PAP8O2P0P3PMPFPNP2PCPAC9P516H?/7R,2PX0O/41PGPAPLD3n2001106000120104103n0100000020000n0100000020000X5>D>9159ePLP;P:PWP1DCn0110000020100b1P5P;P:PWP1DP9159eW7X26X37X44X63P:PWP1P2O4X26W3W4W6o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h01ch12rgh21rh31bi001bh43curh51Hh64bailh71kh82sth91zh:2H0h;2H1h<2Hkh=1ai011ah>1mi021mh?1oi031oh@3offi043offhA3ridi053ridhB3st'hC2z0hD2z1i063st1i072tli081xp%0p&0p;1p;3p;2p;4p;5p;6p;7g028Uk10FTg01bWj38Tg004ej1\Tg02h@j20Tg02b6j1CTg03Ulj1~Tg03Vmj3yTg02d\j1ZTg03C0j11Tg02>aj4qTg02o:j1^Tg03Wej1]Tg00O<j2oTg01jZj1?Tg01\ck30@Tg03X[j1lTg02:Aj2:Tg03YZj1;Tg004@j1VTg03J9k206Tg03JVj2>Tg03ZVj1zj2ITg03[Nj2KTg00IoR0j2rTg01=Zj2BTg03\Sj2JTg031Lj2ATg030Bj2DTg03CNj27Tg03]Nk10ETg03^Ek10DTg03_<j3MTg03;`k40ATg01iaj2WTg03`5j5QTg03a5j1[Tg02cgj2PTg01><k10?Tg02O=k20>Tg02NBk20=Tg02e_j2kTg02f<j2jTg02gAj2iTg02khk40<Tg02lFk60;Tg02lgj4hTg02m;j4gTg02m[j4mTg02n7k108Tg03b0j1fTg03bNj1eTg037_j7TTg03cHj2dTg03dDj2`Tg032Qk105Tg033Rk404Tg033kj1cTg034cj6bTg0357j1}Tg035oj1|Tg036hj3UTg0383j2aTg038mj1{Tg03:0k100Tg02[Qk101Tg02\Mk502Tg03:ij1xTg02P8k303Tg029Gj5XTg02BIj4wTg03eAk107Tg026Aj2YTg03f=j1vTg03g6k209Tg03h1k20:Tg03hoj3uTg02ALj5_Tg03imj3nTg01kOj4tTg03Mej4sTg02[mj4pTg01oXk50BTg03jjk30CTg01[nR1f0R2'Bp=G%C2$07g00ahR3'Yp=4f2R4f1R5#v0092+0:p=51Y23p=SAu452#1p==1Y52#1p=<f3R6P4g01KmR7P5P2D_p=9An452#1p=FP5g03F_R8g03REP2Ctp=Ng03keR9P4P5P2Csp=@g02a:R:g00^SR;P2P8Cpp=RP6P4g00neR<P5P2D_p=3g020OR=P;P4P5P2I0Bp=2P:P;P5P2Cpp=H1>28p=6An528p=LB0C452,06p=E%V2#Vp=Og02S[R>g01flR?p,1RR@$0FRA[\>RBp,1PRCP6P5%G2RDO258@^>1^B>g00d:REP>%46g02i8RFg00_1RG#\RHf4RI;52W0/06P6n0100000020000#C#~P?g01;;R?P1P?P1PAP2f5RJg02W=PEP>f6RK#4f7RL=5H2X0F/0KPKn0100000020000RM7y2RNPDO2PEPAPEP>%4JA5HK2X0F/0JPJn0100000020000RD#CRO#Z#S#1P@PDPIP6CqPEPA%^O#Sg03l]RPPE%]OROP<P7P<n011080003000020105104#1'oRQPPPAPO%?3ROPEB0@=;@R=%l2#1RR1:@I%;2%VGRG#\0068R8'>#?RSPEP=%;5RT/>8RU==52RV1:@JRWPEP=1<2URUP@g03mX#zRXPEP>%4Lf8RY=5H2X0F/0LPLn0100000020000RZ'0PKPJC9PEP=AFZT8PWg03S?g03T;'>g03nS'>R[,NTR\PEP=%;4R]/K2#1R^1:@KR_P0P>P:P=PEP>%4Yf9R`=5H2X0F/0YPYn0100000020000Ra9@]8P@1r:;Rb%R5'B1J58/I2'A,DHX0F/05RcP`PYC3n2001108000120106105n0100000020000X1;52@n0100000020000n0100000020000n0100000020000X2;52@n0100000020000X4;52@P@PDPIP6C9Rd1H52Re,7Z#6#?PEP=1H45Rf,7aRg%6gRh;=2P_PEP=1<2hP@10XaPLPKC9RhPEP=1Lag#1P_P@1H64Rg,Bb%64Ri,J6/I2'A,DHX0FRjP4g03oMRk&0E2Rl&0D2Rm;MiW1RiPaCEPLPKC3n0100000020000n0100000020000n0100000020000X2;52@n011080003010021105104Pdn0100000020100n0100000020001n1011080002101020198@CP2P6PNP2O2X=1P2O1PEP>%4IA5HJ2X0F/0IPIn0100000020000#C#Z#S#1PEPEPEPAP2P@PMPJPICqPEPA%CMRN#^#SPPPE%]NRNP<P7P<n011080003000020105104#1'oPPPAPNPEP=PRPWPEP=PVP_PEP=PUPhPEP=AFaT8P_PEP=P^1:@LRhP0P>P:P=PEP>%4`f:RW=5H2X0F/0`P`n0100000020000Rd9@]8P@PcPWP`C3n2001108000120106105n0100000020000X1;92@\n0100000020000n0100000020000n0100000020000X2;92@Sn0100000020000X4;92@OP@PMPJPIC9Rn17ae#6#?PEP=17dfRo%6oRp;=2PhPEP=1<2pP@10XdPYPLC9RpPEP=1Ldo#1PhP@PjP4PiPdCEPYPLC3n0100000020000n0100000020000n0100000020000X2;52@n011080003010021105104Pnn0100000020100n010000002000198@CP2PDPIP6P4H0APQPEPEPEPAP2PPPA%CZ#]PEP=PRP_PEP=PVPhPEP=PUPpPEP=AFdT8PhPEP=P^1:@YRpP0P>P:P=PEP>%4Wf;R_=5H2X0F/0WPWn0100000020000RQ9@]8P@PcP_PWC3n2001108000120106105n0100000020000X1;92@\n0100000020000n0100000020000n0100000020000X2;92@Sn0100000020000X4;RD92@OP@PZPKPJC9Rn17de#6#?PEP=17QfRd%6dRo;=2PpPEP=1<2oP@10XQP`PYC9RoPEP=1LQd#1PpP@PjP4PiPQCEP`PYC3n0100000020000n0100000020000n0100000020000X2;52@n011080003010021105104Pnn010000002010098@CP2PNPPPPPPPAP2PEP=PRPhPEP=PVPpPEP=PUPoPEP=AFQT8PpPEP=P^1:@`R^P0P>P:P=PEP>%4_f<Rp=5H2X0F/0_P_n0100000020000RT9@]8P@PcPpP_C3n2001108000120106105n0100000020000X1;92@\n0100000020000n0100000020000n0100000020000X2;92@Sn0100000020000X4;92@OP@PaPLPKC917Qe#6#?PEP=17TfRQ%6QRa;=2P^PEP=1<2aP@10XTPWP`C9RaPEP=1LTQ#1P^P@PjP4PiPTCEPWP`C3n0100000020000n0100000020000n0100000020000X2;52@n01108000301002110510498@CP2P@PCPOPD1WO2%l5#1PEPEPEP=P2P^%;6RO/>8RD#?RQPEP=%;IRS/>8R\==I21:@WRoPEP=1<2\P@PEP>%4pf=RU=5H2X0F/0pPpn0100000020000RV,0XP_PWC9S00PEP=AFVS8Po1NS[PEP=%;JRh/K2#11:@_P0P>P:P=PEP>%4Uf>RR=5H2X0F/0UPUn0100000020000RP9@h8P@PcPRPUC3n2001108000120106105n0100000020000X1;52@n0100000020000n0100000020000n0100000020000X2;52@n010000002000098@CP2g00f@RNP@PC1>]8#?PEP=A=6D2P^PEP=1<2DPaPEP=AFTO8P^1NO[PEP=1KS2#1PoP0P>P:P=A@S8VP@PcPUPpC3n2001108000120106105n0100000020000X1;52@n0100000020000n0100000020000n0100000020000X2;1WQ2A=I\5PEPEPEP=P21:@pR\PEP=%;KRQ/>8,<6P@PEP>%4Rf?RS=5H2X0F/0RPRn0100000020000RO,0XR^PUPpC9PEP=AFOQ8RaP\1NQ[PEP=%;LRQ/K2#11:@UR\P0P>P:P=PEP>%4Sf@RD=5H2X0F/0SPSn0100000020000R]9@Q8P@PcPDPSC3n2001108000120106105n0100000020000X1;52@n0100000020000n0100000020000n010000002000098@CP2PN1>h8,<4PEPEPEP=P2P@10X]S01PRPUC9RhPEP=AF]Q8P\1NQ[RQPEP=%;YRn/K2#11:@RRdP0P>P:P=PEP>%4DfARq=5H2X0F/0DPDn0100000020000Rr9@n8P@PcPqPDC3n2001108000120106105n0100000020000X1;Rs52@n0100000020000n010000002000098@CP2P^P7PUPpP_DQPaPEPEPEP=P2Pd1Nn[RnPEP=%;`R`/K2#11:@SS02P0P>P:P=PEP>%4qfBR[=5H2X0F/0qPqn0100000020000S039@`8P@PcP[PqC3n2001108000120106105n0100000020000X1;52@n010000002000098@CP2PNP@PCPQPs1Wn21K`5#1PEPEPEP=P21:@qP0P>P:P=%;_R0PEP>fCRq#4fDR`=5H2X0F/0qPqn0100000020000Rn7@8P@PcP`PqC3n2001108000120106105n010000002000098@CP2PNPSPEP>%4[A5Hq2X0F/0[P[n0100000020000R[#[Rq#RRcg03<[Rs'PRQg02TT&0?1Ra20>a2+0=W2%[nR^#RRt/PsRsg02io'P#G%Z2/kH/j2'iX0F%Gsg03=TRs/j2'iX0FP1g03>KRuP1P:g03?BRvP;g03?[RwH0<RxP:Pvg03@4RyP;Pwg03@RJ0;RwPuChRzP1PuPzP1PxPwPuCgCmR{Pc%GcR|$08P?P1P>%VG#O#O#O#O#O#\RG,Pt#G%^2/kH/D2R}'AX0F1Bbt1J^8/I2'A,DHX0F%fqP:PkP:PvPyPkChR~P:PkP~P:PvPyPkCgCmRyPq%;W=M98%e[FT/d['`'0'0R[#C$05P1PuPzP{P2P?PuPuP1PuPzP1PxPwPuH04RwP2PEP>%4`fE=5H2X0F/0`P`n0100000020000#[R`#RRx/PG#G/A}X0F1Bbx1J`8/I2'A,DHX0F%f^P:PkP~PyP^AM908%enFT/dn'`'0'0Rn#cR0Eb%}2%Gx%|23U%Gt=U33n10110800021010100P0FT/an%{|/0[n10110800021110701'0R[#C$00PuPu&01uAU3a3P1PuPzPwPc%c[RcEbI02#x;UsPcFT/a['0'0403PQO2n0110000020001b3W;XD;DXn0110000020001b3n0110000020001b3n0110000020001b3W:XC;DXn0110001020001b3W5X9;DXPZP7PKPJPIDQP@PC17Te#6#?PEP=17VfRf%6fRT;=2PoPEP=1<2TQ00PEP=1LVf#1PoP@PjP4PiPVCEP_PWC3n0100000020000n0100000020000n0100000020000X2;%?T/W217PgRP%6P;=5PEPEPEP=P2P\PEP=1HJI,7]RP#6,<6PhPEP=1L]P#1RPP\P@1HKJR\,Bb%6JRh,JK/I2'A,DHX0FPJAMlmhX1kP]CEPRPUC3n0100000020000n0100000020000n010000002000098@CP2PN1HI6,7O#6,<4PEPEPEP=P2P@10XrPSPRC9PEP=17r\,Lr#1PdP@1HLK,Bb%6KRd,JL/I2'A,DHX0FPKAMlmdX1kPrCERrPSPRC3n0100000020000n010000002000098@CP2Q01P7PRPUPpDQPPPEPEPEP=P2Q02P@1HYL,Bb%6LRb,JY/I2'A,DHX0FPLAMlmbX1kQ03CEPDPSC3n010000002000098@CP2PNPrP<PSPRPUDQn0110000020000b3n0110000020000b3n0110000020001b3W5X9;DXX@;XA:P5P2O2n011000103010021105104b3PMP7PJPIP6DQn0110001020100b3n0110001020001b3n10110301021010101b?P@P6P4P5Cw98@CeW<X6AX7BX8>P4P5P2O3X6AW7W8o"). Qed.

Lemma ta_fin_sg st m mask (k : mstate -> Z -> Malloc.M R) : (forall st' z, sgood (k st' z)) -> sgood (ta_fin st m mask k).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "h01kh11mh24maskh32sth42Hkh53st'h61zp;1p;3p;2p;5g028Uj16Tg01bWj30Tg040Fj12Tg02e_j21Tg02`>j15Tg02P8j34Tg02CDj53Tg02S[R0g01[nR1g00^SR2p,1RR3#6\2\0R4p,1PR5f2R6f1R7f0R8O2503^62^50P8f3R9%26R:,16#5f4R;34P:O2P3P;P9P6P7D39035eW4X04X22X11X30P9P6P7P8O4W0W2W1W3o"). Qed.

Lemma try_avail_sg sc st (k : mstate -> Z -> Malloc.M R) bail : (forall st' z, sgood (k st' z)) -> sgood (try_avail sc st k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h04maski004maskh13st4h21pi011ph31bi021bh44bailh51kh61oi031oh71rh82sch92sth:1zi041zh;2Hkh<1ai051ah=2a0h>2a1h?2a2h@3acthA1mi061mhB2m0hC2m1i072m1hD3st'hE3st1i083st1i091gi0:2m2i0;2m3i0<2mni0=3st2i0>3st3i0?5step1i0@1xp;1p;3p;2p;5p;4g028Uj1mTg01bWj35Tg041=j2FTg02Iej23Tg02Xkj1JTg03C0j1<Tg02CDj54Tg00IoR0j2LTg01;;R1j1`Tg02Ycj1:Tg0424j1>Tg03Vmj3?Tg01=Zj29Tg01><j1iTg02Jbj1HTg042lj1VTg02]ij1ETg026Aj2YTg043gj1dTg00O<j2cTg02Z[j1MTg02[Qj1bTg00iJj1aTg02[mj4DTg02\Mj5QTg02\hj2PTg025cj2=Tg02KYj2_Tg004ej1BTg03JVj2KTg004@j1ATg044bj1GTg045^j1\Tg03J9j2[Tg046Yj4lTg047Sj2kTg02e_j2OTg0480j3jTg003[j1ZTg0495j2NTg02;<j57Tg02=bj58Tg01ncj1hTg040Fj1XTg02`>j1Wj2STg02P8j3ITg02^cj2TTg02_Bj2RTg02Qjj5UTg02D;j5gTg04:3j3fTg00kkj10Tg01oXj5eTf0R2g00ahR3'Yp=2g02S[R4g01[nR5f1R6P2CDp=@P4P5f3R7f2R8;f6P2CDp=1P8g00^SR9P6P2CDp=;%02#0#0#0p=^%02#0#0#0#0#0#0#0p=]%02#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=6g020OP9P8P6P2Dep=Cp,1RR:#mR;\9\4R<p,1PR=P7P6P2O255:^:9^D4f4R>,F7g01flP1P5P1P5P;P2g00d:R?P;f6R@/32RA#JRB#2#<RCP:P@P2PBf5RBD4P11L45RDP;P?%`DRE%:A#2RFP1P5PEf7RG#>??2@RH/FGf8RI#>??6GRJ/@2,9D%iDRKn10110@00021010700P1P5PE%HAPI1952RAPGP2C1,9DPKn10110@00021010700n0100000020000P0P4P5P;P2P0PDP9P;P?1LD9RL1362RM#:RN%VM#E'Y%dM#2#<'cROP1P5PL%HMRPf;RQPAP8P2C11382#:RR5;D1@62RS=;DNRTn10110@00021010<00PTn0100000020000P0P4P5P;P6P0P4P5P;P?PDP1P5P9%MMRUg02a:RV/L9RWPW%bWRXPVP9g02aXg00_1RV#aCDRY1386RZ#MR[DQ,P8R\P3n10110@00021010500#ER],=8#2R^P?PD1_PA#<R_P1P5PDPPf?R`PAP8P2C1RaPSn10110@00021010<00P1P5PDPUP?P9%VZ%BVRb'KRcg00aI#^#]#6#6#6#6#6#6#6#6#6P1P5P9P[PWPWPXPY1378#MDQ,P7RYP3n10110@00021010500%AVRX#B'KRWg04:nRd%GZ#\/[dRd/[W'KPdClRd'kPcPdn0100000020001/Ob=j28/@6PSn10110@00021110900Rbn0100000020001PSn0100000020100P:P2P6P:%ZX#A#A#A#BRX%22#<RdP:1368#G/N6RcP8P2f@RWD4P`D7X09X14f=ReD8n200110@00012010>10;n200110100012110=10:n200110@000121101100n2001101000121108107P?P;PFPBPHP3O2g02ji#hRHPBV95C:n0100000020000n10110?00021110100n0100000020001P>PBP3O2n10110@0002111060095:=P2PCP?P?P?P;P2P:PIP813I8RC#JPGD4P1PDP;P?PE%:C#2RBP1P5PEf9RF#>??8IRf/FFf:Rg#>??7FRh/@2,9DPKn10110@00021010700P1P5PE%HCPgPAPFP2C1,9DPKn10110@00021010700n0100000020000P0P4P5P;P2P0PDP9P;P?PLPOP1P5PLPPPePAP8P2C1=;DRPTn10110@00021010<00PTn0100000020000P0P4P5P;P6P0P4P5P;P?PDP^P?PDP_P1P5PDPPfARePAP8P2C1PSn10110@00021010<00Pbn0100000020001PSn0100000020100P:P2P6P:PXPdP:PcP8P2fBRCD4PeD7X09X14P`D8n200110@00012010>10;n200110100012110=10:n200110@000121101100n2001101000121108107P?P;PBPGPfP3O2PGV99C:Hn0100000020000n10110?00021110100n010000002000195:=P2P>13G6R`#JRi%XiRi'O#W=I6GPiO2P?PE%:`#2P1P5PE1FJI1@f2,9DPKn10110@00021010700P1P5PE%H`PFPAPIP2C1,9DPKn10110@00021010700n0100000020000PEP1PDP1PDP;P2P0P4P5P;P2P0PDP9P;P?PLPOP1P5PLPPf>PAP8P2C1=;DRPTn10110@00021010<00PTn0100000020000P0P4P5P;P6P0P4P5P;P?PDP^P?PDP_P1P5PDPPPCPAP8P2C1PSn10110@00021010<00Pbn0100000020001PSn0100000020100P:P2P6P:PXPdP:PcP8P2fCRED4PCD7X09X14PWD8n200110@00012010>10;n200110100012110=10:n200110@000121101100n2001101000121108107P?P;13F7#:#2PIPhP3O2PIV99C:Hn0100000020000n10110?0002111010095:=P2P0P4P5P0P4P5P;P2P0PDP9P;P?PLPOP1P5PLPPA;DaRPTn10110@00021010<00PTn0100000020000P0P4P5P;P6P0P4P5P;P?PDP^P?PDP_P1P5PDPPPEPAP8P2C1PSn10110@00021010<00Pbn0100000020001PSn0100000020100P:P2P6P:PXPdP:PcP8P2fDRaD4PED7X09X14PeD8n200110@00012010>10;n200110100012110=10:n200110@000121101100n200110100012110810795:=P2P?PLPOP1P5PLPPPWPAP8P2C1=;DRPTn10110@00021010<00PTn0100000020000PLP0PDP9P0PDP9P;P2P0P4P5P;P6P0P4P5P;P?PDP^P?PDP_P1P5PDPPfFR^PAP8P2C1PSn10110@00021010<00Pbn0100000020001PSn0100000020100P:P2P6P:PXPdP:PcP8P2fGD4P^D7X09X14PaD8n200110@00012010>10;n200110100012110=10:n200110@00012110110095:=P2P0P4P5P0P4P5P;P2P0P4P5P;P?PD1=7]#2P?PDP_P1P5PDPPfHRaPAP8P2C1PSn10110@00021010<00Pbn0100000020001PSn0100000020100P:P2P6P:PXPdP:PcP8P2fIRLD4PaD7X09X14P^D8n200110@00012010>10;n200110100012110=10:95:=P6P?PD1=>]#2P?PDP_P1P5PDPPPLPAP8P2C1PSn10110@00021010<00Pbn0100000020001PSn0100000020100PDP0P4P5P0P4P5P;P2P:P2P6P:PXPdP:PcP8P2fLD4fKRcD7X09X14PLD8n200110@00012010>10;95:=P2%ZV#B%JM#2P1P5P9PU%E\P3n10110@00021010500R\P9%:ZRZP9g02TTRU1=68RM1T68/R2'SW7=I87P4P:PX%2M#<P:1327#G/N2P7PMfND4fMD7bEb0b@fJRMPX1=N\R\#2#<P:P1P5P9P[%EYP3n10110@00021010500RY,=Z1TZY/R2'SX7U=I26RU/32#G/NURUP2P\PcD4PMPL%X\RL,O\#W=I2UPLO2DUDUX?5XC4P6P2O2n2001101000121106105b2X>5XB4P6P2O2n2001101010121106105X:9X2DP6P2O2n2001101010121101104b2X=5XA4P6P2O2n2001101010121106105X2DP2O1PBP?P?P?P;P2PF%>Q??>gP3O2PFV99C:Hn010000002000095:=P2P@PhP3O2g00f@n0110200020000b3n10110301021110100b6n0110201020001b3X<5P2O1P6P>P3O2n10110301021110500b6P:P>P7P8P6Dg95:=eW;X4;X5<X94X89P7P8P6P2O4X4;W5X94X89o"). Qed.

Lemma ag_tail_sg lay st sc m p cnt ai (k : mstate -> optr -> Malloc.M R) : (forall st' g, sgood (k st' (Some g))) -> sgood (ag_tail lay st sc m p cnt ai k).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "h02aih13cnth21kh33layh41mh51ph62sch72sth82Hkh91gh:1rh;3st'p;1p;2p;3p;4p;5p;9g028Uj1ETg01=Zj21Tg01bWj32Tg004ej14Tg02e_j23Tg02]ij10Tg02`>j2;Tg02_Bj25Tg04;cj26Tg04<]j27Tg04=\j28Tg04>[j29Tg04?[j3:Tg04@Rj2DTg03JVj2CTg04AHj3BTg02P8j3<Tg04BBj4=Tg02Iej2>Tg04C<j1?Tg04D7j5@Tg02E5l9ATg04E1R0g02S[R1g00^SR2g01[nR3g01flp,1RR4#E[\1R5p,1PR6f2R7f1R8f0R9,13O2524^93^;1P9f5R:f4R;P;113:R<P7g02TTf7R=g00_1#4R>13;>R>%0>f3R>#0R?'31;?9'5,6<'7'8'9W:f6R<f8R??:=;R@/D</C>;B@5<:C=R@/>:#?P>P@D@P:O2P4P?P=P<P:P;P>P7P8M9A9246eW8X25X02X12X53X43X62X71X30P=P<P:P;P>P7P8P9O8W2X02X12X53W4W6W7W3o"). Qed.

Lemma alloc_group_sg lay (aslot : mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R) st sc req (k : mstate -> optr -> Malloc.M R) bail :
  (forall st' g, sgood (k st' (Some g))) ->
  (forall st' sc' req' k', (forall st'' idx, 0 <= idx -> sgood (k' st'' idx)) -> sgood (aslot st' sc' req' k' bail)) ->
  sgood (alloc_group R lay aslot st sc req k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h03st2i003st2h13idxh21bi011bh31rh43st1h52sth61xi021xh71Hh84__x1h95asloth:4bailh;1kh<3layh=3reqh>2sch?3st'h@4st''hA1yhB4HANShC3HashD4HidxhE2HkhF7__arithhG4__ffhH8__varmaphI5__withJ1ai031ahK1chL1gi041ghM2k'hN1mi051mhO2moi062mohP1oi071ohQ1pi081phR4req'hS3sc'hT2x0hU1zi091zhV2z0hW2z1i0:3cnti0;6neededi0<3ridp%0p&0p;1p;2p;3p;4p;5p;9p;7p;6p;8g028Uk10KTg01=Zk20JTg01bWj38Tg01\cj3sTg01E2j2ZTg004@j1ITg004ej15Tg04Eoj2GTg003[j1VTg047Sj20Tg04@Rj26Tg04FLj2=Tg00kkj1BTg025cj2:Tg03J9j21Tg00IoR0k20FTg04GKj2fTg03C0j1ETg04HGj1dTg03JVj23Tg00O<j2@Tg026Aj2LTg03YZj1TTg04Hej2WTg03EFj2eTg01kOj4aTg03K3j1KTg03Kjj1MTg03Lfj4NTg02:Aj2RTg026^j1`Tg01><j1kTg02<hj5?Tg03Mej4QTg04IBk10ITg04JAk10HTg04K5k20GTg04L6j2jTg04LVj1^Tg02P8j34Tg02h@j2JTg02e_j22Tg02E5l99Tg04MSj1DTg041=j2XTg04NQj7YTg04OIj3[Tg01nck10ETg01iak20DTg03a5k10ATg03b0k10@Tg02lgk40=Tg02m;k40:Tg02m[k409Tg03_<k308Tg03bNk105Tg037_k704Tg03cHk202Tg03dDj2~Tg04PAl9cTg00:fj2bTg001<j6{Tg029Gj5zTg04Q<j2yTg006Dj1|Tg00<@j1}Tg04Q\j2xTg01?Yk100Tg01@7k101Tg01@bj2wTg04R:j2vTg01DGk403Tg01FJj7uTg04R]k806Tg01Ahk207Tg01BJj2tTg00;@j3\Tg01C6k30;Tg01CUj4rTg04SAj4qTg000`k60<Tg04S]j4pTg02Emk80>Tg045^k10?Tg04T[j1oTg04USk30BTg04VNk30CTg04WHj2nTg04XGj1mTg02[mj4iTg01oXj5lTg04:nR1f0R2$0?'1p=7f4R3f3R4f2R5#of1R640B<0C2p=>1L341156/31/W2'@p=;1321p=P%I2#Ip=O1062,@5p=H1n62#mp=<1L56/@2p=U1W62,@5p=hg00^SR7P7P6P2Cip=S1162/31p=_g02a:R8P7P2g00ahR9Cip=g1029p=Cg020OR:P7P5P6P2Dlp=F1162,31g04Y@R;'2p=Ag00d:R<g00neR=7\2p=]g04E1R>g02S[R?p,1RR@$0KRA\7\?PA\A[\7\7[RBg01flRCPA[\?RDg01[nREp,1PRFP4P620JE2O258@]L^??As:7@R:^T7^6?1Z92RGP4P5P6O298@F[^17^@?f;RHP3P4P5P6f6RIO598@F[]M^R7^S7^??PIg01;;RJPEPAP2P<PAg03F_RKg00_1RL#IRM#5RN'GROf8RP#7RQP<P7P<P7%IMRR#V#5RS,0P165PRT,=Pg00aI#B#B#B#B#B#B#B#BRUPU%VLRV#5RW,:PRXPTPQD>n0100000020000RY%5LRZPQPYPOD;PNPYn0100000020000RY'1R[#P'0P0P7P7PAP<20F77R\1fP5#ER]P<P7P<P7%dP%IRR^#OR_#5R`7HP1<P513PZ'6,3TPTn0100000020000RT%5RRR/1Y'0/@]P<P7%5^/1KR^/0[R]9UXZPNP<P711RKRa/0[9UXNPWP<P71LX9RX/@]PWP<P711NKRK=HX[%VM#5RMPYn0100000020000n0100000020001n0100000020001n0100000020001PYn0100000020100RX%VV#5R[3hP<P\f7R]/3;#P#TRb%PQ'01Wab11NX7HT'e1SZb1_QX#T,SXRXn0100000020001PXn0100000020101RXP9P2g03GTRbg03S?g03T;'3RTCaRcP<P:f5Rd,<HRe#K%MeP6P2CN#E1R@PP<P:%`2RfP@P4Pef:RgP2%kERhO2X0?RiPPD?P0P?P8P:g04Z3RjP2P6PeCQP@f@Reg02i8&0I2/3Z$0H00G2WKRk%OV#5RV,j4#^Rl=4d6'Jf=RmPd%g2RnP3P<P7P<P7123ZRo%I_#O#O#O#5/21R1%7mR_'G/2ZRp'0PoPpn0100000020000Rp#CP9Ppn0100000020000PHM99n200110200012010010<n0100000020000n0100000020001X375F@n200110200012110:10;PgP51AYQRY#DS00PYP<PA%C2RQP@P5P6f9RpP2PhO2X0?S01P]D?PJPEPAP<P7P<P710gS163gRq,=gPUPU1:gWPq%7gRqD>n0100000020000RrPZPqPrPOD;PNPrn0100000020000/Aq#D,X6RqP@f>Rr%^9RsPrP5P2P6P<P7P<P710HS16dHRt,=HPUPU1:HWPt%7HRtD>n0100000020000RuPZPtPuPOD;PNPun0100000020000Ru/At#DRvPtPuFYRt544PHP4A[526RwPu12uZRxPpM99g02ji$0ERyPPV75F@Rzn10110200021110400n0100000020001X17X4?PdO5n0100000020101PdP6PhO2n10110600021110500XOCX5?P5%7]R{P<P7P<P710]S166]R|,=]PUPU1:]WP|P{D>n0100000020000R|PZP{P|POD;PNP|n0100000020000'_,0OP<P<P<PAP2P0P7P7PAP<P\1fp4#ER|P<P7P<P7%dp?Hp`164pR`1<p413pZ'6'3P`n0100000020000R{P<P7P<P710pS1=p`PUPU1:pWR}P`%7pR`D>n0100000020000R~PZP`P~POD;PNP~n0100000020000R~,1R'0/@|P<P711`~R|,0^R^9U}ZPNP<P710a|9U}NPWP<P71L}9R}/@^PWP<P7AH}K|PMP~n0100000020000n0100000020001n0100000020001n0100000020001P~n0100000020100RM;h[P<P\13P;#P#TR;%P`'01Wa;11NM7H{'e1SZ;1_`M#T,SMRMn0100000020001PMn0100000020101P<P:f<RM/<IR;#K%M;P6P2CN#E1R@pP<P:PfP@PdP;PHP2PhO2X0?PpD?P0P?P8P:PjP2P6P;CQP@fAR;A4]l6,JkPrP]PnP3P<P7P<P7%7rR{,G1/2ZRa,0oPoPan0100000020000Ra#CP9Pan0100000020000PMM99n200110200012010010<n0100000020000n0100000020001X379F@cn200110200012110:10;PHP41A~`R~#DP~P<PAPQP@P3P6PiPPD?PJPEPA1X6vP@f?RvPvP5P2P6P<P7P<P710MS16IMRi,=MPUPU1:MWPi%7MRiD>n0100000020000R~PZPiP~POD;PNP~n0100000020000R~/Ai#DR`PiP~FY94dsPMPdPwP~12~ZPgM99PpV79F@yn10110200021110400n0100000020001X17X4?PIO5n010000002010198@FP2PXP\P0P7P7P0P7P7PAP2P<P:1<m]R\#K%M\P6P2CN#E1R@gP<P:PfP@PIP\PMP2PhO2X0?RXPgD?P0P?P8P:PjP2P6P\CQP@fBR\A4Pl6,JkPvPPPnP3P<P7P<P7%7vR~,G1/2ZRi,0oPoPin0100000020000Ri#CP9Pin0100000020000PmM99n200110200012010010<n0100000020000n0100000020001X379F@cn200110200012110:10;98@FP2P@PFPcP<P:1<rPRc#K%McP6P2CN#E1R@HP<P:PfP@P]PcPmP2PhO2X0?PHD?P0P?P8P:PjP2P6PcCQP@fCRcA4pl6,JkPePpPnP3P<P7P<P7%7e,G1/2ZRf,0oPoPfn0100000020000Rf#CP9Pfn0100000020000RfPrM99n200110200012010010<n0100000020000n0100000020001X37P9P6PbPTCa00D21<vpRb#K%MbP5P6CN#EP<P<P<P:P21R@rP<P:%`4P@Pg1<;HRbPeP2PhO2X0?PrD?RhP0P?P8P:PjP4P3PbCQP@fF1jIV#^=4M6,JkPcPMPnP]P<P7P<P712]ZRn%7c,G1/2ZR1'0PnP1n0100000020000R1#CP9P1n0100000020000P;M99n200110200012010010<R1n0100000020000n010000002000198@FP2g00f@RnP<P=P<P:P2PhP1n010000002000098@FX2<Pc1<egRc$0AR1$0@P8g03oMRhP8g03?BR:g03@4RVPhH0=RbP8PhPbP8P:PVPhH0:H09P1B08j54&05cK04002c'~94pl,JkPePp%g1P3PfPrPMM9c%`5P6g027U,:T/L9,b<O1E{n0110101020001b2WBXW7DzXV7XU7P6P2O2n2001108010121109109bQP4P5Q00PYP<PAPQP@P4P6Q01P]D?PJPEPAPqP@PrA43stPHP3PwPuPxPpM99Pzn10110200021110400n0100000020001X17X4?P<%C6RzP=g00XL1062#]1Z65Rx[1Z261056#][Ru1045#]\x1y62P2n2001000000120000000XA7X67Pu^A7^67P2P5P9g01KARu#|%}u1x76&007&017Rug01H9Rxg01HXRwPwg01I8RtPuPxPwPwPtP71w79g01LM1v7LH03g01IXFuRL%kwPLL06207utP2P5g01KmRt,b<1t25=\<tdB0;796CrbGbHbIX871Z96\G^87P2P4P5O2bFO3b7CqA\<=zP<P=P<PAP2P@PIP3PXPgD?PJPEPAP<P7P<P710mS16]mRg,=mPUPU1:mWPgP_D>n0100000020000RgPZP_PgPOD;PNPgn0100000020000/A_#D,X3P@P;P;PdP2P3P<P7P<P710rS16PrR;,=rPUPU1:rWP;P{D>n0100000020000R;PZP{P;POD;PNP;n0100000020000R;/A{#DP{P;FY94]sPrP]A[d23P;12;ZPMM99PHV79F@yn10110200021110400n010000002000198@FX2<1X4`PCPJPEPJPEPAP2P@P\P\PIP2PdP<P7P<P710vS16pvRp,=vPUPU1:vWPpP~D>n0100000020000RpPZP~PpPOD;PNPpn0100000020000Rp/A~#DP~PpFY94PsRsPvPPA[I2dR~Pp12pZRZPmM99PMV79F@yn1011020002111040098@FP2P\PsPvPPP~PpPZPmPHM9cXJEP2O1Pnn10110701021110300bP%C5P2J0<b7XDGX17X@?O5n0110101020101b2XNEX4?CpP@PPP]PIPdP3P4P5L0>98@FeWCWEX:AX;DX=7X>7X5?X9BX<>PIPdP3P4P5P6P2O7X:AW;X=7X>7X5?W9W<o"). Qed.

Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "h01mp;1p;2g040Fj13Tg04Zkj12Tg04[Pj10Tg01E2j21Tg00^SR0f0R1#3#2g00ah%01'1eX00P1O1W0o"). Qed.

Lemma alloc_slot_sg lay : forall fuel st sc req (k : mstate -> Z -> Malloc.M R) bail,
  (forall st' idx, 0 <= idx -> sgood (k st' idx)) -> sgood (alloc_slot lay fuel st sc req k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h03st2h13st4h24bailh32goi002goh41kh53reqh62sch72sth82Hkh95firsth:4fuelh;3idxh<3layh=3st'h>3st1h?3Hk'h@2IHhA7__arithhB4__ffhC8__varmaphD5__withE1bi011bhF1fhG1gi021ghH2k'hI1rhJ4req'hK3sc'hL4st''hM1xhN2x0p;1p;2p;3p;8p;6p;4p;7p;9p;5g028Uj1UTg01E2j27Tg01bWj30Tg02Fij82j35Tg026Aj2TTg03C0j1LTg04[Pj14Tg0424j13Tg02Xkj1=Tg004ej1<Tg02e_j2:Tg02`>j29Tg02P8j38Tg02<2j61Tg00iJj1STg02Emj86Tg04\Fj1KTg006Dj1ETg00<@j1CTg01?;j1BTg01?Yj1ATg01@7j1@Tg01@bj2?Tg01DGj4DTg01FJj7>Tg01Ahj2FTg00:fj2GTg01BJj2HTg00;@j3ITg01C6j3JTg01CUj4;Tg02VDj6MTg01\cj3NTg04]Cl9OTg04^Bj5PTg00kkj1QTg04_?j4RTg04E1R0g00c[R1g02S[R2g00^SR3p,1RR4#UR5\3\2R6g00ahR7f0R8'7R9p,1PR:f4R;f2R<f1R=O2504[^;3^=2R>P4f8R?f6R@f5RAP;f3RBP<P=G2904:[^25]4^53]6]7RCX:1g00f@P4f7RDg00aIPAP;PBP<P=G2904:eX8>X25X46X53X63X72P;PAg00d:REP51T87#LRFP;P=%48O2P4f;RGf9RH954GP=P@PAg01flRIg01;;RJg01[nRKP5P8P4%3HRLP8g02TT%=8g00_1RM#<':/98WIRN=88<ROP?P8P7O2X12RPP@E1P@P=%SMRMO2n10110000021010200W3X02PBG6n0100000020000X93X>2P=PFPEPEPEP5P8P@PB%4<O2P4f=RFA54FGPBP?PDPJPKP5P8P4%3GP8POf:RGP8P7O2X12P?E1P?P=PMO2n10110000021010200X3IX02PAG6n0100000020000904:P8PBP<%4=%K=O3f<R?A54?GP<PDP@PJPKP5P8P4%3GP8POPHP8P7O2X12PDE1PDP=PMO2n10110000021010200X3IX02P;PLP8A88N=RNPPP@P@P8P7g01KARI#E%CI%B3%A3%@3RIg01H9g01HXRMPMg01I8RMP31?37ROg01LMPOCDg01IXF>1FIMP8P<g01KmRM,GE1H8<=IEMdAJ37=C;bBbCbD1777P8bAO3X12EMP4PLP8PNPPP@E1904:eXGKX02g020O?N34^N3^M2PBP<P=O2904:\9^;3^L2f>P;PBP<P=PHP8O6W?WHXJ3XK3X=2M9On0110100020000bEX93X>2DPP4PH%QDPAP;PBP<P=G2904:eX8>X25X46X53X63X72X@CXF1P8CRW:X<0P8O1W<o"). Qed.

Lemma malloc_small_ctrl_sg lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  (forall st' g i, sgood (k st' (Some (g, i)))) -> sgood (malloc_small_ctrl lay st n k bail).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) ["Walk"] "p'0h03idxh13st1h21Hh31bi001bh41oi011oh54Hidxh64__x1h74bailh83gp'h91kh:3layh;1nh<2sth=1xi021xh>1yh?2Hkh@7__arithhA4__ffhB8__varmaphC5__withD1gi031ghE2gpi042gphF1ihG3st'i051ap;2p;1p;3p;4p;8p;7p;6p;5g00Ioj2TTg01;;R0j1pTg028Uj1YTg01=Zj2?Tg01bWj3:Tg04MSj14Tg041=j20Tg004@j1=Tg004ej1@Tg003[j1XTg04_`j25Tg02[Qj1lTg00iJj1fTg02[mj4RTg04@Rj21Tg03JVj22Tg04Hej23Tg02Iej2ATg02Xkj1BTg040Fj1CTg03C0j1LTg02e_j2KTg02`>j1ITg02P8j3JTg04[Pj1GTg047Sj2>Tg01><j1PTg01ncj1WTg02Fij8ETg01E2j2HTg04Q<j2VTg006Dj1UTg00<@j1oTg04Q\j2nTg01?Yj1mTg01@7j1kTg01@bj2hTg04R:j2gTg01DGj4eTg01FJj7dTg04R]j8cTg01Ahj2aTg00:fj2`Tg01BJj2_Tg00;@j3OTg01C6j3^Tg01CUj4bTg04SAj4]Tg000`j6QTg04`=j8STg02Gdj6\Tg026Aj2DTg00O<j2FTg04HGj1[Tg02\Mj5iTg02Ycj1jTg01oXj5ZTg01[nR1g00^SR2f1R3f0R4CRp=<1134g00ahR5'Dp=9f7R6f6R7'3f5R8f4R9'>'Ff3R:f2R;'D#L'F%[3'F/F4p=7P9P:P;P3P4Di,A8p=8%B3/D5%j4/D5'Fp=61D45p=Ng020OP2P;P3P4DZp=;g00d:R<g00neR=7O4p=Mg04E1R>g02S[R?1T12R@#pp,1RRA#YRB[\?RCp,1PRDP9P;1<34,?@O25:A^F2^D1^G?P0P1P2%4:RE,09%49RFP<P2g00_1RG#=#=RH#@RIPEPE%=H#=#=#@RHPE%XGRJ#=RK#@RLPE199EG7P<P2P0P1P2%@GRM,5ERN,09P<P2P8g02a:RO/T2RPPP%lPRQPOP2g02aX%fGCRRO15FMRR,08RSE8RT/6T118RRT%@JRJ'2RUPTn0100000020000119N/2Jn10110200021010500%=K#@RK'3PNPEn0100000020000PEn0100000020000n10110300021010500RE,09RNg01flRTP0P1P0P1PBP4P<PBP0P1P2P3f8RV/A4#BP5n10110300021010400RW#CRX#N#LP81KWX#I=J46%GX,<4,?@O2PAPVg04a;RXP6P0P1P2%47RW,06%46RYP<P2PIPWPWPHPWPLPW196WG7P<P2P0P1P215WMRZ,06R[P<P2PVPPPPPQPO15YMR\,0VR]E8R^/6^11V\R^/2JR_P^n0100000020000116ZR^/2JR`n10110200021010500/3KPZPWn0100000020000PWn0100000020000n10110300021010500RZP7P<PB1>45RaP6P3%P@RbO2P0P1PBP0P1P2f9Rc%4VRd'0%4cReP<P2PIPdPdPHPdPLPd19cdG7P<P2P0P1P215dMRf,0cRgP<P2f:RhPPPPPQPO15eMRi,0hRjE8Rk/6k11hiRk/2JRlPkn010000002000011cfRk/2JRmn10110200021010500/3KPfPdn0100000020000Pdn0100000020000n10110300021010500Rf,03PVP;1<43,?@RnO2g02ji#WRoP6V25;An10110200021010400n0100000020000X02X1?P9GEn0110200020001PAP6PXP7P0P1P2%48Rp,07PWP<P2PIPpPpPHPpPLPp197pG7P<P2P0P1P215pMRW,07RqP<P2P6PPPPPQPOP[E8R[/6[P`P^n0100000020000117WR^/2JR`n10110200021010500/3KPWPpn0100000020000Ppn0100000020000n10110300021010500RWP8P<PBPaP7P3PbO2P0P1PBP0P1P210VYPdP<P2PIPYPYPHPYPLPY19VYG7P<P2P0P1P2P]P<P2PcPPPPPQPOPgE8Rg/6gPmPkn0100000020000P_n10110200021010500/3KP\PYn0100000020000PYn0100000020000n10110300021010500RY,03P6P;PnO2P7V29;Aon10110200021010400n0100000020000X02X1?P:GEn101103000211104019:ADP41A64#B#C#N#LP<P<P<PBP4P61Ac;#BR\%C\R\'K#I=J;c%G\,<;,?@O2PAPhPXPcPfPVP<PBPaPcP3PbO2P0P1PBP0P1P2f;R\%4hR_'0%4\RkP<P2PIP_P_PHP_PLP_19\_G7P<P2P0P1P215_MRm,0\RgP<P2f<R]PPPPPQPO15kMRd,0]R[E8Rr/6r11]dRr/2JRsPrn010000002000011\mRr/2JRtn10110200021010500/3KPmP_n0100000020000P_n0100000020000n10110300021010500,03PhP;PnO2PcV29;AoRmn10110200021010400n0100000020000X02X1?P7GEn01102000200019:ADP4P91AV3#BRu%CuRu'K#I=J3VP3%GuO3PcPXPVPYP6P<PBPaPVP3PbO2P0P1PBP0P1P210heP_P<P2PIPePePHPePLPe19heG7P<P2P0P1P2PjP<P2P\PPPPPQPOPgE8Rg/6gPtPrn0100000020000Pln10110200021010500/3KPiPen0100000020000Pen0100000020000n10110300021010500Re,03PcP;PnO2PVV29;AoRin10110200021010400n0100000020000X02X1?P81H54RlP<1>35RrP=g00XL1>34#M1H3;Rt[1H431>;3#M[Rg1>:;#M\t1V34P4n2001000000120000000X>2X=2Pg^>2^=2P4P;P5g01KARg#U%og1n23%m2%k2Rgg01H9Rtg01HXRjPjg01I8R_PgPtPjPjP_P21h25g01LM1g2GCeg01IXFdRG%PjPGGc1ag_P4P;g01KmR_,`<1_4;=O<_dA^253CbbAbBbCX621H53\l^62P4P:P;O2b@O3b2C]R_AO<=rRrP<P=P<PBP4P\P9PbO2P0P1PBP0P1P2f=Rg%4]RG'0%4gRjP<P2PIPGPGPHPGPLPG19gGG7P<P2P0P1P215GMRt,0gR6P<P2f>RYPPPPPQPO15jMRj,0YE8RM/6M11YjRj/2JPjn010000002000011gtRj/2JRJn10110200021010500/3KPtPGn0100000020000PGn0100000020000n10110300021010500,09P]P81<49,?@RtO2P\V29;Aon10110200021010400n01000000200009:ADX3<P0P1P210]kPGP<P2PIPkPkPHPkPLPk19]kG7P<P2P0P1P2P[P<P2PgPPPPPQPOP6E8R6/66PJPjn0100000020000Psn10110200021010500/3KPdPkn0100000020000Pkn0100000020000n10110300021010500,0:PTP0P1P0P1PBP4PgP71<48,?@RgO2P]V29;Aon101102000210104009:ADP4P\P7P4P8O3X81P4O1g00f@R\n10110100021010500b41>;5R]P4EQb2W5X02X1?GSn0110001020001b3XE1P4O1P7PXP8P0P1P2108FPpP<P2PIPFPFPHPFPLPF198FG7P<P2P0P1P2PSP<P2P7PPPPPQPOPqE8Rq/6qP`P^n0100000020000PUn10110200021010500/3KPRPFn0100000020000PFn0100000020000n10110300021010500RFP9P<PBPaP8P3PbO2P0P1PB103ZP7P;PnO2P8V29;Aon10110200021010400n0100000020000X02X1?RZP;P_PrP<P=P<PBP4PVP9PbO2P0P1PB109ePcP8PtO2Pin10110200021010400n01000000200009:ADX3<10:fPTP0P1P0P1PBP4PhP7PgO2Pmn101102000210104009:ADP4PVP7P4P8O3X81P4O1P\n10110100021010500b4P]P4EQb2X5lX02X1?GSn10110101021110501b4P0P1PBPNP<PBP0P1P2108F1A74#BP5n10110300021010400R5#CRN#N#LP:1K5N#I=J48%GN,<4,?@O2PAP7PXP8PFP9PZP;GEn0110200020101PAP8PXP9PEP:P<PBPaP9P3PbO2P0P1PB103WP8P;PnO2P9V29;Aon10110200021010400n0100000020000X02X1?P3GEn101103000211104019:ADePAP8P9P:P;P3E\9:ADeW?X7BX9CX;2X<?X:>P9P:P;P3P4O5X7BW9X;2W<W:o"). Qed.
End Walk.

Lemma malloc_core_sg lay st n : size_overflows n = false ->
  sgood (fun r : mstate * option (aptr * Z) => snd r <> None) (malloc_core lay st n).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "p'0h02mrh12goi002goh22ruh33st3h41bi011bh51rh61Hh72H0h83layh91ni021nh:2sth;3st'h<4HANSh=3Hovh>1ch?1eh@1gi031ghA1ihB1mi041mhC2m0hD2n0hE1pi051phF3st1i063st1hG1zi071oi083ridi091xp;1p;3p;2p;4p;5p;6p;8g04b0j1_Tg00;@j3KTg00IoR0j2JTg01;;R1j1`Tg03B3j3wTg01><j1uTg00X3j1PTg028Uj1fTg04Hej2WTg03JVj22Tg01kOj4RTg01\cj3vTg03K3j1^Tg03Kjj1]Tg03Lfj4LTg03C0j1OTg02:Aj23Tg026^j1QTg03Mej4ITg04XGj1gTg04IBj1eTg004ej1GTg04JAj1bTg04K5j2aTg01=Zj26Tg003[j1MTg04Eoj2DTg04;cj2VTg04<]j2UTg04=\j2TTg04>[j2STg04LVj29Tg02P8j3ATg02\hj2BTg04?[j3<Tg04BBj4?Tg02Iej2>Tg04C<j1=Tg04D7j5@Tg02h@j2;Tg01lDj2ETg04boj1tTg04d0j2sTg02BIj4HTg02Gdj6YTg01bWj34Tg01iaj2pTg000`j6XTg00Q[j2oTg04S]j6kTg025cj2jTg026Aj2iTg00:fj2hTg001<j6ZTg029Gj5lTg02[mj4FTg04dlj8mTg04f1j3nTg01_Nj2dTg004@j1[Tg02`>j2qTg02_Bj2cTg01oXj5rTf3R2g02S[R3f2R4f1R5f0R6CF'dp=0g04Y@,26g04:n'2p=1g02a:R7g00^SR8P6g00ahR9CFp=N%M6#Mp=C%[6#[p=:1q96p=71c96p=8g01[nR:P8P6P9CFp=\g020OR;P8P4P5P6Drp=5g04E1R<g00d:R=%_6g00neR>3KP=P>1J:8R?#`R@,J3RAAw3@6%u?RB5K@#PX5ARCP=%fARDP6PAP@P2PBC0REP=PDg04fmRF/W4P9%14g03GTRGg03S?g03T;'2RHCRRIP=Av;8AR;f4RJ#^%]J%12RKP6CL#OPAP@PJPBC0RL,3AP=P;%Q6RMPLP0P3P7P;g04Z3RNP6PKPJCIPA%g5ROg01flRPP1P:PDP6PAP@g02i8%e6g00_1RQ#GRR'2#b/a6W>RSP6%N2RTPT16:6RUg02TTRVf9RW#1%MQ#C#CRX#C#C#C#GRY'2%:Q#:#:#:#:#:#GRQ'D%GXRX1J78RZ%NJ'6/V6,U9,TR'SR['9#7#8W0=A64R\/BTf:R]?<\TC?R\/>6#=PRP\D@';%\6,6?R\C0f7R^#1,EJP=P;%t6R_PAP@1s24PBC0R`PAP@PWPBC0Ra,3An0100000020000X2855An10110000021110300W1X33PAP@f6RbPBC0CHn2001109000121106108n0100000020001n0100000020001X58Rc55APAPJP2P4PAP@P5P6C0X5@XF3RdPEEYn0100000020100n010000002000134X4=1WF5P=P=P=PDP6P9PKPGPHCRRGP=P;f5RK#^RF%]KRe%1JRfP6CL#OPAP@PKPBC0Rg,3AP=P;PMPgP0P3P7P;PNP6PfPKCIPAPOP1P:PDP6PAP@P6PTPTPU%1]Rg/2Y/DQ/9[#7#8X0V=A64RM/BTf;Rh?<MTC?RM/>6#=PRPMD@,;SP\C0f8RM#1,EJP=P;P_P`PAP@P]PBC0R],3An0100000020000X2855An10110000021110300X1PX33PAP@P^PBC0RiCHn2001109000121106108n0100000020001n0100000020001X5855APAPKPJP2PdPLEYn010000002010094ACP6PAPCPIPc1pG6PFPePfP5CL#OP=P=P=P;P613AiP=P;%Q2PiP0P3P7P;PNP2%1bP^CIPAPOP1P:PDP6PAP@P6PTPTPUf<Rf#1Re/2Y/DQ/9[#7#8X0V=A64RF/BTf=RG?<FTC?RF/>6#=PRPFD@,;SP\C01E^gP=P;P_P`PAP@PfPBC0,3An0100000020000X2855An10110000021110300X1PX33PaCHn2001109000121106108Ran0100000020001n010000002000194ACP6g00f@RfP=P>P=P;P6PiPan010000002000194ACX4=PNP4%1KPbCI1J37P0P3P7P0P3P7P;P6PAPOP1P:PDP6PAP@P6PTPTPU%1G/2Y/DQR0/9[#7#8X0V=A64Rb/BTf>RK?<bTC?Rb/>6#=PRPbD@,;SP\C0%1h,EMP=P;P_P`PAP@PGPBC0,3An0100000020000X2855An10110000021110300X1PX33P]CHn200110900012110610894ACP6PAPCPOP1P:PDP6PAP@P6PTPTPU%1K/2Y/DQ/9[#7#8X0V=A64R[/BTf??<[TC?R[/>6#=PRP[D@,;SP\C01EWeP=P;P_P`PAP@PKPBC0,3An0100000020000X2855An10110000021110300X1PX33PAP@PhPBC0AK@\BRhP@%\5,6?P1P?p-0P6g00edg00bFR1n10110700021000000X?@RPPfPBP6EXP11o16R`b7W6%PhePAP@P6%N4RhPhPU16ZT/V6,U9,TR,SX,90#7#8X0V=A65RV/BhA<KVhC?RV/>6#=PRPVD@,;SP\C094ACeXC:X;3EkXD7XB3P5P6O2n2001105010121104102bE%Q4P5g027U,jH/i9,h=O1EZn0110101020001b4W<XG8DlPAPCPJP2P4PdPEP:P8P5P6CF,6?RE=K@BRdP@P:P8P4P5CF,6?PPPfPBP6EXP1P`b7W6%PdePAP@P4PEC094ACeXA8X@:X;3Gmn0110101020101b4%_5P6EZAn24594ACeW=X98X:3X8<P4P5P6O3X98X:3W8o"). Qed.

Lemma cmalloc_sg cs n : size_overflows n = false ->
  sgood (fun r : mstate * option cptr => snd r <> None) (cmalloc cs n).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "p'0h01Hh12csh21nh31ri001rh42H0h52H1h63Hovh71ai011ah81eh91gi021gh:3idxi033idxh;1oi041oh<1pi051ph=3st1i063st1h>3x__i071mi084x__0i091zp;1p;3p;2p;4p;6p;8g04b0j1FTg00;@j31Tg00IoR0j29Tg01;;R1j1:Tg01><j1;Tg00X3j12Tg04f1j3@Tg01\cj3>Tg04glj17Tg04OIj36Tg01=Zj23Tg01_Nj28Tg04hbj4ETg01bWj34Tg02[mj4=Tg000`j6DTg00Q[j2<Tg00:fj2CTg04iaj8BTg04j\j2ATg03B3j3?Tg02S[R2f1R3f0R43?p=5P2f2R5P3P4C=p=0g00^SR6g00d:%F4g00ne31g01[nR7/96R8#:R9,92R:g01gaR;#:R<,92R=1594%;8R>519#2R?X3:15<4%;;R@51<#2X3=RAg04kTRB?@53P0P2P9g020O%:7RC,92RD7>6REP4%73P1P8PCP4P0P7P6PCP4f4RF?634,37n2001105000120102103%;7RGn1011000002101050050C,8DRHn2001108000120106100X>:PBP5P3P4CEP0P2P9P0P2P9PEP3PHn200110800012010610094=A\?P4P1P8A0954,59=19>#2f3R?#7P1P8PCP3P0P7P6PCP4f6?634,37n2001105000120102103PGn1011000002101050050C,8D94=A[P4P0P7P61384909F,59=19>#2f5#7P0P7P6PCP3f7R0?634,37n200110500012010210350C,8D94=A[P4P7P6P3P4C=,389090,59=19>#2f8R0?653,37RF=1<@RHP<f9?6?5,37P1P;p-0P4g00edg00bFR;n10110400021000000X8<g00f@P@P4EDP;1<;4b5W4%2He%70=0CF,8D94=AeW0X:6X97P3P4O2n2001105000120101109X<8P4O1A093>,59=19>#2A1<G@#2P41C9>O1'<%75=0CG,8D94=AeW0n10110400021110500X;9X=2P3P4O2n2001105000121107104X7:GB1A5394=AeW6X26X12P3P4O2W2X12o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma is_err_of_addr_ok : forall atop len avoid a, 0 < len -> atop < 2^63 -> mmap_addr_ok atop len avoid a = true -> Malloc.is_err a = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "h01Hh14__p1h24__x1h34__x2h44__x3h54__x4h61xh71yh82H0h92Hah:3Hath;2Hch<4Hlenh=2_Hh>3_H0h?7__arithh@4__ffhA8__varmaphB5__withC1ahD4atophE5avoidhF3lenp;2p;1p;4p;5p;3p;6p;7p;8g00Ioj2iTg00<@j1QTg004@j1>Tg004ej1ETg003[j1;Tg01>^j2NTg01<Gj2ATg04lMj4ZTg04mIj5VTg03BPj2=Tg04nJj10Tg00XLR0j21Tg04oBj39Tg026^j1BTg0508j2\Tg01E2j26Tg03JVj2ITg047Sj2HTg04Q<j2[Tg02e_j2YTg00kkj1@Tg0513j27Tg051\j3?Tg052Ej2XTg006Dj1WTg00R:j3UTg04Q\j2MTg01?;j1TTg0531j4LTg01?Yj1STg01@7j1RTg04R:j2DTg053Oj6hTg01Fnj7gTg01><j1fTg0543j3dTg01@bj2KTg005Cj1PTg01AEj3OTg01DGj4JTg054Vj3cTg01Ahj2`Tg00:fj2_Tg01BJj2^Tg01C6j3aTg01CUj4bTg00;@j3GTg01FJj7]Tg04R]j8eTg00ahR1f0R2'Ap=3g00d:R3g01KmR47G2p=4g00^SR5?G21p=:f2R6f1R7'I/62p=2g00ne9G32p=5%>2#>p=8P5P7g01LMP2CJp=FP7g01H9R8g01HXR9P9g01I8R:P2g01IXF]p=<f3R;P8P9P9P:P6P7P2Gep=C1i55#Q%36f4R<g00_1R=#>R>#ER?%;=R@#;#;#;#;RA#E'N'ARBf5RCP<P;P6CZ#4f6RDPCP<P;P2DVg0559RE,=;#:%3;%0CRF=2;D'1'1A9;F<#4'1P01=<E#:%3<RF%0DRGf7RH52<'1'1A9<GC#4%BC#5P21=DE#:%3Df8RC#0f9RG52D'1'1P01=HE#:%3H%0Gf:RI52H'1%0I=9CG#4%BG#5[P21=GE#:%3If<RG#0f=RE52I'1P0f;RI#3%0Ef>RC52I%0C=9GE#4%BE#5[P2%3Ef@RE#0fARG52Cf?RC%0G;9E#4fBRE/\C%0ERC,6E%>>RI#8#8RH#8#8#8#ERJ,IE,AC'1P01H72#51676R0[16271H67#5[RC1H;6#5\01[72P2n2001000000120000000X75X65PC^75^65P2%EH,N?/YJRCPEp-0R0g01KARKg00aIRL#@RM#@RN#@RO#@,75175O175N175M175L5?55?55?55?5g0561'X%WK3U%QKP5P51M5<P6%T5CLP71M5;CL%S5%R5RKPKP8P9P9P:1D5>R>1D5IRI'F,<KPKP8P9P9P:PDEhFg%f9R9PK1D5=R==d5I1D5@R@'F,<KP9PKP5P@g01GRR@1K5?R?%PA5O5CJ,<KP9PKP51K51P@P>CJ,<KP9%PH9O5?1K5J5c5,F=,<KCCCCCCCC1`K:P2P61_341^26#4dAa517Cbb@bAbBX25X35X45X55W1167;/1<A27<;16<C\F\B[[^25^35^45^55^10P2fER0#0RB1I0J'APBfFP0fCP6P<PGPEO9b?O3b8%BG#5eb0W>W;W9P7P2O2n2001000000121000000W0W=P7P2O2n2001000000121000000W0P7P2O2n2001000000121000000b0W0W:W<XC5WEXF5XD5o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "h01Hh11fh23Hfdh33Hfsh42_Hh53_H0h62moh73mo'p;2p;1p;3p;4p;6g05IAj2RTg06G4j1<Tg00;@j30Tg06Ggj1;Tg06HZj12Tg06IOj16Tg06JDj15Tg06K8j14Tg004@j1=Tg005Cj1QTg005aj1PTg00Ioj2LTg00<@j1HTg006Dj1KTg06Kmj1ATg06Lmj1ETg06Mej19Tg06NYj18Tg00XLR0j2DTg06OLj1FTg06PEj1GTg00:fj2JTg00Eoj4OTg001<j6ITg00KLj1NTg06Q>j1MTg06R7R1f1R2f0R330p=Bg06Ro?023p=?g06Si?023p=>g06Tb?023p=C%N3#Mp=7f2R4%E2;03p=@f3R5?042/D3p=11D23,D4p=3g001ZR6?023p=:g00XgR71R23P0g06U\R8%<2%<430g06VTR9%;2%;4%22%24'B%62%64'?%52%54'>%42%44'Cg00_1#=#=#=#=#=#=#Q#PR:%72%741L::R;#HR<%K;R;7@4%H:R=%A5%K:R>30R?P<%E5P;P?C1[[C13333C1g06WL,L:#HR?%94%95%84%85':C1P3%<5f4R5#<508P9%;5f5R4#;R@%25%24RA'B%65%64RB'?%55%54RC'>%45%44RD'CP:%75%74R5A@<4;f6R4#A=0=>REA@<4;RF/DE[[C13333C1P0%;4909@%24,BA%64,?B%54,>C%44,CDP:P5%74f7R5#A=0=>RDP<%E5P;PDC1[\FC13333P?%94%95%84%85':C1P3%;5f8R5#;509%25f9R9#2R4'B%65%69RF'?%55%59RD'>%45%49RC'CP:%75%79R5A@<9;f:RB#A=0=>RAA@<B;R@/DA[[C13333P0%2B,B4%6B,?F%5B,>D%4B,CC%7B90:5f;R5#A=0=>RCP<%E5P;PCC1[\@3333P?%9B%95%8B%85':C1P3%25f<R5#2'B%65f=RB#6'?%55%5B'>%45%4B'C%75%7B50:A@<B;f>R:#A=0=>R>P<%E:P;P>C1[[3333P8%<:R>P?%F3f?R;#<#FR<%2:R=#GR5%2;#GR;':C1X18P1P=P?P<P<%G3/:;C1X11%F>R>=0?>1:551J?>1J65CO%2BP2EI%<BP9EIP?%9B%9:%8B%8:':C1eW5W3P2P3O2n2011000000121000000W0W4P2P3O2n2011000000121000000W0W2P2P3O2n2011000000121000000W0X77W6o"). Qed.

(* [comment removed for export] *)
Definition FRZ (G : PState -> Model -> Prop) (s0 : PState) (mo0 : Model) : PState -> Model -> Prop :=
  fun s mo => G s mo /\ ps_so s = ps_so s0 /\ ps_fa s = ps_fa s0 /\ m_fds mo = m_fds mo0 /\ m_fs mo = m_fs mo0.

Lemma frame_ok_FRZ G s0 mo0 : frame_ok G -> frame_ok (FRZ G s0 mo0).
Proof.
ltac2:(KReplay.run1 (kr_t_PTotal ()) [] "h01Hh11Gh23mo0h32s0h42E1h52E2h62E3h72E4h82E5h92E6h:2HGh;3HGsh<3Hfah=3Hsoh>2Hvh?1ah@2mohA3mo'hB1shC2s'p;1p;2p;5p;3p;6p;4g05nXj1=Tg068=j13Tg0693j16Tg05IAj2DTg06XDj58j3BTg004@j19Tg005Cj1ATg005aj1@Tg00Ioj2?Tg00<@j1>Tg06Mej11Tg00;@j32Tg06NYj14Tg00XLR0j20Tg06Y8j3CTg01^Sj6<Tg00Eoj4;Tg01HXR1f1R2f0R332p=7g06CER4?223p=:g001ZR5?223p=5g05SUR6g00XgR7p-0[[R8f2R9#=%39f3R:#3'7%6:f4R;#6':1D:9f:R<f9R=f8R>f6R?P;D8P0f;R;f7R@f5RAO2%6@%6<RB':%3@%3<RC'7g00_1#9#9#9#9#9#9#A#@g06WL'?#>RD%1A%1=RE32%4A%4=RF'5'0'0'0f<RGP;P<P@PAD8P3f=RHP=P@O2%6HR@,:B%3H,7C%1>%1GRC52D%4>%4GRG'5'0'0'0P0%6;f>R>#6':%3;%3>RB'7%1HRI92DE%4HRE,5F'0'0f@RFf?RJP>P;P=D8P3%6F,:@fAR@#3R=,7B%1FRB92DC%4FRF,5G'0'0P0%3JfBRG#3'7%1@RC92DI%4@RI,5E'0fDREfCR;PGPJPHD8P3%3E,7=%1ER=92DB%4ERB,5F'0P0fERF#1RH92DC%4FRC,5IfHRIfGRJfFRKP;P@D8P3%1;%1JR;52D%4IRL,5BACFE@A2D=H15BC'0P0%1K92DH%4K,5CfMRCfLRHfKR0PIPKD8P3%1I92D;fIR;#4RB,5LfPP0P;O2%60RLfOR=#6RF':RE%30R@%3=R='7RM%1;RNfNRO#1RP52DRQ%4ORO,5BRR'0RS'0RT'0PCPHP0fJR0P;PIPJPKPGO8PEPTP4PL%6HPFPJP>E<PMPSP1P@%3HP=PIP<E<PQPRPDPN%10PPP2P?E<P5PB%40POP3PAE<C;C;C;C;W9W8P2P3O2n2001000000121000000b?W7W6P2P3O2n2001000000121000000W0W5P2P3O2n2001000000121000000W0W4P2P3O2n2001000000121000000W0W;P2P3O2n2001000000121000000W0W>W=W<XA7X@7XC6XB6AB:92#=eW:X27X36X18P9P2P3O3X27X36W1o"). Qed.

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
  STOTP (startup s) mo (fun _ s' mo' => s' = s /\ m_vmmaps mo' = m_vmmaps mo /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ minv mo' /\ m_halted mo' = None).
Proof.
  intros s mo Hmi Hh. unfold startup.
  eapply STOT_bind; [| intros a s' mo' H; exact (STOT_mono _ _ _ _ _ _ (STOT_ret _ _ tt s' mo') ltac:(intros ? ? ? (-> & -> & ->); exact H))].
  apply STOT_sys.
  - intros rsp mo' evs Hst. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi'].
    pose proof (nstep_dec_set_tid mo _ _ _ Hmi Hst) as (-> & t & Hd & _ & _). split; [reflexivity|]. exists t. split; [exact Hd|].
    cbn [nstep] in Hst. destruct Hst as (_ & t' & -> & Ht). split; [reflexivity|].
    destruct (m_tid mo); [destruct Ht as [_ ->]; auto 6| destruct Ht as [_ ->]]. rewrite m_vmmaps_with_tid, m_fds_with_tid, m_fs_with_tid. auto 6.
  - intros code mo' Hx. exact Hx.
  - apply nstep_progress_settid.
Qed.
