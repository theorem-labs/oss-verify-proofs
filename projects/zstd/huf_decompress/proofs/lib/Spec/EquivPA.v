(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (54 recorded proofs replaced by written proofs (m_fds_mo0, m_fs_mo0, OWN_minv and 51 more); OWN_vm takes an unchanged kernel build (m_kernel), passed from startup_STOT in startup_pair and startup_startup, and OWN_fds re-proved for KL_fds' same new premise; RX_init, equiv_PP_L and equiv_PP give GI_init the launch's channel reader, the entry's mmap-base fact and resv_plain; tglob_prog gives minv_init the channel reader; GI_init's state is moved to the run's initial model (init_model with the vDSO draw installed) by GI_with_vdso; malloc_pair through P_annot, whose recorded terms no longer typecheck (a universe of the recorded rsim_silent application), are zstd_frame_info's proofs restated for this unit's RX X w, AI Y w and AIP Y w (one unit of budget per malloc; AIP carries 0 <= w); equiv_PA is equiv_PA_L at source_alloc_limit (zstd_frame_info's proof); equiv_PP_L also proves AIP's 0 <= MAIN_OPS). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe MPaths STree Malloc Stdio Harness Adapter Driver
  PState Prog StepB KLink KEv ModelInv ImgFacts ModelOK EquivShared EquivProg RSim RSimProg SizeHist PTotal ProgA LB_StmtA LB_Main EquivK_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_EquivPA () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List7map_mapI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C49OSSVerify5KrLib8TopLevel3mo0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib4Spec7EquivPA8init_fdsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree6ttraceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;tpath_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7vm_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA2GTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink8frame_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib4Init9Datatypes4unit00I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K59OSSVerify5KrLib4Spec5ProgA6AAlloc01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver7IOStyle00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init9Datatypes6lengthC46Stdlib7Sorting;Permutation?Permutation_mapC46Stdlib5Lists4List7map_appC59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec7EquivPA2aXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv3OWNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv6creach00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink7kl_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink7kl_haltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec5KLink2KL00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC59OSSVerify5KrLib4Spec8ModelInvAm_vmmaps_with_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ModelInv6KL_fdsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec5ProgA3AStC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA2RXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA2pXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA2AIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA4a_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv8OWN_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA:ok_AI_permC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2lec59OSSVerify5KrLib4Spec7EquivPA<ok_AI_creditC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib4Spec7EquivPA9ok_AI_wnnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState9set_so_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA8a_set_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv9OWN_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA8ok_AI_soC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6PState6PState01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA:ok_get_setC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA8OWN_minvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA;ok_AI_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA7OWN_fdsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9ok_AI_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes=m_fs_with_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim5tglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg6rsimeqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim4STOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim8STOT_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim3relC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim=tglob_ebind_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim=tglob_ebind_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim4rsimC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg2QmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim;rsim_silentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg6rd_relC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim9STOT_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec8RSimProg6REQMAXC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec8SizeHist6HISTOKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA7amallocC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib4Spec7EquivPAEsize_overflows_REQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PTotal?raw_malloc_STOTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA8sizes_aXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9ok_mallocC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PTotal4PhiPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA;frame_ok_GTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PTotal=raw_free_STOTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA7ok_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c59OSSVerify5KrLib4Spec7EquivPA8ok_annotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim9STOT_pathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim9STOT_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA6aannotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib4Spec5StepB7nf_nodeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg7io_nodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>minv_preservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared:diag_shortC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA7ok_sub2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA8ok_same2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg:s_diag_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA3ioAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA4sub1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA5same1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog2ioC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA6ok_io2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA6RX_getC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA6RX_setC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg:s_emit_simC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA3io1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProgEstdout_exit_flush_simC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9RX_modelsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg=exit_node_simC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes9Empty_set00C59OSSVerify5KrLib4Spec5ProgA<new_handlerAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim9rsim_munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog;new_handlerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA6ok_MI2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9RX_tablesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg8open_simC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA8MI1_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg9close_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg8read_simC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog3runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA4runAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg>target_run_simC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA;malloc_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9free_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA7RX_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9RX_creditC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA7nh_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9emit_pairC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg7RUN_OPSC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib4Spec5ProgA;alloc_initAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA<alloc_countAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg:rsimeq_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:exit_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA:progA_mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg=main_exit_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:main_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog:alloc_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog;alloc_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9diag_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA8run_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9open_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA:close_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9read_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA;ioexit_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA=exitnode_pairC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;EquivShared9PIECE_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8RSimProg8MAIN_OPSC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c59OSSVerify5KrLib4Spec7EquivPA>main_exit_pairC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog9prog_withC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim8rsim_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog7startupC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem:entry_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC49OSSVerify5KrLib8TopLevelBvalid_entry_eitherC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelK46Stdlib9micromega6VarMap1t01C4ELinuxProcessSemantics?LinuxProcessSem5State<reserved_topC59OSSVerify5KrLib4Spec8ModelInv7GI_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ModelInv3GsoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv9OWN_weakGC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_basec59OSSVerify5KrLib4Spec7EquivPA9m_fds_mo0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA8m_fs_mo0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg9p_init_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg7p_phdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC59OSSVerify5KrLib5Plain4PImgBreserved_top_plainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts:ceil_plainC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC59OSSVerify5KrLib4Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ModelInv<argv_Z_shortC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implC59OSSVerify5KrLib4Spec8ModelInv;ARG_MAX_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog4progC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes9minv_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7ModelOKEprog_model_ok_plain_LC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec7LB_Main@never_forced_p_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PTotal@tglob_PhiP_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree<ttrace_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;texit_ebindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop?or_iff_morphismK69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib4Spec4RSim;tglob_ebindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA5treeAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsC4ELinuxProcessSemantics?LinuxProcessSem5State;in_image_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs@fs_keys_relativeC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_credsC4ELinuxProcessSemantics?LinuxProcessSem5State9in_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run<valid_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_hwcapC4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_urandomc59OSSVerify5KrLib4Spec7EquivPA>argv_Z_pieces'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9prog_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA7RX_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPAAtglob_after_emptyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA:tglob_progC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPABttrace_after_emptyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPAAtpath_after_emptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim;rsim_ttraceC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6PTotal<startup_STOTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA6OWN_vmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA5AHANDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA>equiv_core_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA:progA_treeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA<startup_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA3toPC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_sp_vaC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_mmap_base_vaC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunCentry_stack_fits_vaI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00C4ELinuxProcessSemantics?LinuxProcessSem5State<brk_aslr_maxC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizei59OSSVerify5KrLib4Spec7EquivPA8AAllocOK00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA:equiv_coreC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel;tree_tracesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA7ptracesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixI59OSSVerify5KrLib4Spec5ProgA6AAlloc00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA:equiv_PA_LC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC59OSSVerify5KrLib4Spec8ImgFacts5lim_pC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA9toP_validC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA>equiv_PA_toP_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8ptr_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA3AIPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA4PasAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA2KPC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevelEtrees_equiv_of_ttraceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA?startup_startupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EquivPA:equiv_PP_LC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Definition init_fds : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Lemma m_fds_mo0 : forall segs lim en inp, m_fds (mo0 segs lim en inp) = init_fds.
Proof. intros segs lim [? ? ?] inp. reflexivity. Qed.
Lemma m_fs_mo0 : forall segs lim en inp, m_fs (mo0 segs lim en inp) = in_fs inp.
Proof. intros segs lim [? ? ?] inp. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ASide.
Variable A : AAlloc.
Variable step2 : node -> Model -> resp -> Model -> list event -> Prop.
Variable Phi2 : node -> Model -> Prop.
Variable MI2 : Model -> Prop.
(* [comment removed for export] *)
Variables (rsP rsA : Z).

Local Notation STOT2 := (STOT (St:=ASt A) step2 (fun R0 => texit (R:=R0) step2 nexit)).

Record AAllocOK : Type := mkAAllocOK {
  (* [comment removed for export] *)
  ok_sub2 : forall n mo r mo' e, ~ nf_node n -> step2 n mo r mo' e -> nstep n mo r mo' e;
  ok_same2 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> step2 n mo r mo e;
  ok_io2 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> step2 n mo r mo' e;
  (* [comment removed for export] *)
  ok_MI2 : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> MI2 mo -> m_halted mo = None -> MI2 mo' /\ m_halted mo' = None;
  (* [comment removed for export] *)
  ok_get_set : forall v s, a_so A (a_set_so A v s) = v;
  ok_set_set : forall v w s, a_set_so A v (a_set_so A w s) = a_set_so A v s;
  ok_set_get : forall s, a_set_so A (a_so A s) s = s;
  ok_addr_so : forall v s p, aptr_addr A (a_set_so A v s) p = aptr_addr A s p;
  (* [comment removed for export] *)
  AI : list (aptr A * Z) -> Z -> ASt A -> Model -> Prop;
  ok_AI_perm : forall Y Y' w s mo, Permutation Y Y' -> AI Y w s mo -> AI Y' w s mo;
  ok_AI_so : forall Y w s mo v, AI Y w s mo -> AI Y w (a_set_so A v s) mo;
  ok_AI_model : forall Y w s mo, AI Y w s mo -> MI2 mo /\ m_halted mo = None;
  ok_AI_fds : forall Y w s mo f, AI Y w s mo -> MI2 (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI Y w s (with_fds f mo);
  ok_AI_credit : forall Y w w' s mo, 0 <= w' <= w -> AI Y w s mo -> AI Y w' s mo;
  ok_AI_wnn : forall Y w s mo, AI Y w s mo -> 0 <= w;
  (* [comment removed for export] *)
  ok_malloc : forall Y w n s mo, AI Y w s mo -> 1 <= w -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
      tglob step2 Phi2 (amalloc A n s) mo ->
      STOT2 (amalloc A n s) mo
            (fun r s' mo' => exists q, r = Some q /\ AI ((q, n) :: Y) (w - 1) s' mo' /\ n < 2^63
                             /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo);
  ok_free : forall Y w q n s mo, AI ((q, n) :: Y) w s mo ->
      tglob step2 Phi2 (afree A q s) mo ->
      STOT2 (afree A q s) mo
            (fun _ s' mo' => AI Y w s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo);
  ok_annot : forall Y w q cap old new s mo, AI Y w s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap ->
      (old = 0 \/ new = 0) ->   (* [comment removed for export] *)
      tglob step2 Phi2 (aannot A q cap old new s) mo ->
      STOT2 (aannot A q cap old new s) mo
            (fun _ s' mo' => AI Y w s' mo' /\ a_so A s' = a_so A s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo)
}.

Variable K : AAllocOK.

(* [comment removed for export] *)
Variable LS : Z.
Hypothesis HLS : 2^31 <= LS.

(* [comment removed for export] *)
Definition AHAND (inp : ProcInput) (sA0 : ASt A) (moA0 : Model) : Prop :=
  AI K [] MAIN_OPS sA0 moA0 /\ a_so A sA0 = stdout_init /\ m_fds moA0 = init_fds /\ m_fs moA0 = in_fs inp
  /\ tglob step2 Phi2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation rel := (rel PState (ASt A)).
Local Notation rsim := (rsim nstep step2 nexit nexit PhiP Phi2).
Local Notation triple := (bptr * aptr A * Z)%type.

Definition pX (X : list triple) : list bptr := map (fun b => fst (fst b)) X.
Definition aX (X : list triple) : list (aptr A * Z) := map (fun b => (snd (fst b), snd b)) X.
Definition GT : PState -> Model -> Prop := fun _ _ => True.
Lemma frame_ok_GT : frame_ok GT.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h02_Hh13_H0h23_H1h33_H2h42moh53mo'h61sh72s'p;1p;3p;2p100Dcp4p70R0p100EXp4p710R1p8P0p10056p4p710R2p8P0p10031p4p7210R3p8P0p100FIp4p741110R4p8P0p100G>p4p7210R5p8P0p100H2p4p73110R0p8p100Hlp4p70R6P1p8P6P2p8P6P3p8P6P4p8P6P5p8P6P0p8g00Iaj11Tg004>j32Tg00JWj10Tg00KMj23Tg00LCR0j25Tg00M7j14Tg00MoR6g00NhR5g00O^f2R4#1f3R3#132g00P>%03f4R2#0321334f6/52g00Q9W3W2W1W0X55W4X76W6%40eo"). Qed.

Definition RX (X : list triple) (w : Z) : rel := fun s1 mo1 s2 mo2 =>
  OWN (pX X) GT s1 mo1 /\ AI K (aX X) w s2 mo2 /\ ps_so s1 = a_so A s2 /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.

Lemma pX_app X Y : pX (X ++ Y) = pX X ++ pX Y.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h01Xh11Yh21bp;1p;2p;3p;5p100Dcp4p70R0p100QUp4p710R1p8P0p100RMp4p710R2p8P0p100SGp4p710R0p8P1p100EXp4p710R3p8P1P2p8P1p10056p4p710R4p8P1g0031R5p4p7210R6p8P1p100FIp4p741110p8P1p100G>p4p7210p8g00TFR7p4p711R8p100U:p4p710R9p8P8p1002UR:p4p710R;p8P8p100UQp4p710R<p8P8P:p4p7210R:p8P8P4p8P8P5p4p710R=p8P8P6p8P8p100V<p4p710R6p8P8p1006Bp4p710R>p8P8p100V\R?p4p710R@p8P8P?p4p7210R?p8P8g00WIRAp4p710RBp8P8PAp4p7210RCp8P8p1007URDp4p710REp8P8PDp4p7210p8p100Hlp4p70RDP1p8PDP2p8PDP0p8P2P3p8g00WeR3p4p70R2P9p8P2P;p8P2P<p8P2P:p8P2P8p8P2p100X^p4p710p8P2P4p8P2P=p8P2P6p8P2P>p8P2P@p8P2P?p8P2PBp8P2PCp8P2PEp8P7j14Tg00:7j21Tg0081j12TP5j30TPAj53Tp,1A#4RA,13R5g00=UR7'1RE#2R2PEP3f0RC9057903AX2Ef1REPCD3X12X02PEPCO2X12W0o"). Qed.
Lemma aX_app X Y : aX (X ++ Y) = aX X ++ aX Y.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h01Xh11Yh21bp;1p;2p;3p;4p;5g00TFj16Tg00:7j20Tg0081j13Tg0031j32Tg00YZj31Tg00Z7j45Tg00WIj54Tg00WeR0p,1A#6R1'0R2g00=UR3'0R4#3R5P41013P1P3f0R692239101A1236C5X24f1R4P6D4X15X05P4P6O2X15W0o"). Qed.
Lemma sizes_aX X : map snd (aX X) = map snd X.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h01Xh11bh21lh31xp;1p;2p;3p;4p;6g00TFj1<Tg00:7j21Tg0081j15Tg0031j36Tg00YZj32j24Tg00Z7j4;Tg002Uj40Tg004>j33Tg00<<j27Tg007Uj68Tg0056j69Tg00ZWj1:Tg00WeR0p,1A#<R1'1R2g00=UR3'1R4#5R5%53R6P4P3P1P3f0R796239201A2237C;R09213X34P7C0P4P31423R2f1C09367X26P4P3P2P7C0R2,761113R8P31413R1P4P8P0X14R0P7C0C0P4P8P3P0P1P7E8E9P8P3P1%:7C0=362eX05P7O1W0o"). Qed.

Lemma OWN_minv X s mo : OWN X GT s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(L & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

Lemma OWN_fds X s mo f : OWN X GT s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> OWN X GT s (with_fds f mo).
Proof.
  intros [(L & Hc & HK & Hi) [Hnd _]] Hmi Hh. split; [|split; [exact Hnd| exact I]].
  exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| apply m_vmmaps_with_fds| reflexivity| exact Hmi| exact Hh].
Qed.

Lemma RX_perm : forall X Y w s1 mo1 s2 mo2, Permutation X Y -> RX X w s1 mo1 s2 mo2 -> RX Y w s1 mo1 s2 mo2.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h01Hh11bh22HAh32HOh42HPh53Hfdh63Hfsh73Hsoh81Xh91Yh:3mo1h;3mo2h<2s1h=2s2h>1wp;1p;2p;3p;6p;4p;5p;7p;8g00TFj1KTg00:7j2<Tg0081j1@Tg00kbj1ETg00UQj3?Tg00lUj6:Tg00mIj1;Tg00[Kj4>Tg00ZWj17Tg00n=j59Tg00JWj14Tg00o1j26Tg008Qj18Tg0096j1JTg009Tj1ITg00;Hj10Tg004>j32Tg00^^R0j21Tg0031j3CTg00V\j6BTg00oej7HTg00YZj3ATg00Z7j4GTg010[j8FTg00eBj4=Tg00C<j1DTg00P>f1R1f0R232p=5g005T%D1%D232p=3g00WeR3p,1AR4#KR5'<R6g00=UR7'<R8#@R9g00Mog00NhR:%E4f6R;f5R<5?8f7R=P<f4R>f3R?f2R@P1E:P0f8RA#;g00LCRBP<P>C>p,1KRC%7AP;P?P@D9%4<164?'5g00?e#8#8#8#8#8#8#J#Ig00@J'<#@RD%0>%0@3213>@'1'1'1PAP=P;P<P>P?E:P2f:R?#;PBP=P;C>PCf;R>#7f9R@P;P<D9%4A164;'5%0=%0<52D13=<'1'1'1P0PCf<RE#7P?P=P;D9%4@164='5%0A%0;52D13A;'1'1PEP>P?P@PAP=E:P2PCf>R=#7PEP@PAD9%4E164?'5%0>%0@52D13>@'1'1P0f=RA#4164>'5%0E%0?52D13E?'1f@R?f?R;P=PAPEP>E:P2%4;164A'5%0;%0A52D13;A'1P0%0?R0%0=52D13?=fDR=fCR>fBREfARFP?P;E:P2%0ER;=2D013>FfGR0#;R?PBfERGP=C>PC%70RHfFRIP>PED9RJ%4G164>'5R4%0==2D;R;13=ERD'1RK'1RL'1fHRM#;RNP?PBPGP=P8P3AC672R=9C35X18PMP0PFEBA?3N?ePAFHPJPLPC%7MRCPHPIP>PEP81<57REP5P7AA35=AA672CGX18PMP0PFEBA?ECHeP@GFP4PKP<P;PDP1P2C=C=C=C=W6W5P1P2O2n2001000000121000000W0W7P1P2O2n2001000000121000000W0W2P1P2O2n2001000000121000000W0W3P1P2O2n2001000000121000000W0W4X;:W=W:W<X>7X99W8o"). Qed.

Lemma RX_get : forall X w s1 mo1 s2 mo2, RX X w s1 mo1 s2 mo2 -> ps_so s1 = a_so A s2.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h02H0h11Hh21Xh32_Hh43_H0h53_H1h63mo1h73mo2h82s1h92s2h:1wp;1p;2p;6p;4p;5p;3g00TFj1CTg00:7j29Tg0081j1:Tg00kbj1?Tg00lUj6BTg00mIj1<Tg00[Kj4;Tg00ZWj18Tg00n=j57Tg008Qj15Tg0096j1>Tg009Tj1=Tg00;Hj11Tg004>j34Tg00C<j12Tg00^^R0j20Tg00JWj1ATg00o1j2@Tg00P>f2R1#Af1R2f0R3'@34p=3g005T?423p=6g00Wep,1AR4#C'9g00=UR5'9#:g00Mog00NhR6%?4f5R7f4R8f3R9P1P2P3EBP0f6R:#<g00LCR;P8P9C;p,1KR<%8:P7P1P2D7A3841g00?e#5#5#5#5#5#5#>#=g00@J'9#:R1%19%1234%29%22'6'0'0'0A3749P3f8R9#<P;P:P7C;P<f9R;#8P9P7P8D7f7R=?347%1:%18541%2:%28'6'0'0'0P0P<f:R8#8P;P:P7D7A394:%1=%17541%2=%27'6'0'0A3;4=P3P<f<R<#8f;R7P9P=D7A374;%18%19541%28%29'6'0'0P0A3<48%17%1;541%27%2;'6'0f=?347P3f>R7?34<%17%1<541%27%2<'6'0P2W5W1P2P3O2n2001000000120000000W0W4P2P3O2n2001000000120000000W0W3P2P3O2n2001000000121000000W0X76W9W6W8X:5W2o"). Qed.

(* [comment removed for export] *)
Lemma RX_credit : forall X w w' s1 mo1 s2 mo2, 0 <= w' <= w -> RX X w s1 mo1 s2 mo2 -> RX X w' s1 mo1 s2 mo2.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h01Hh12HAh22HOh32Hrh42Hwh51Xh63mo1h73mo2h82s1h92s2h:1wh;2w'p;1p;2p;6p;4p;5p;3p;8g00TFj1ETg00:7j2=Tg0081j1>Tg00kbj1ATg011Wj2@Tg00^^R0j29Tg00lUj6<Tg00mIj1;Tg00[Kj4:Tg00ZWj16Tg00n=j55Tg00JWj17Tg00o1j28Tg008Qj14Tg0096j1DTg009Tj1CTg00;Hj12Tg00C<j10Tg004>j33Tg0123j8BTg00eBj4?Tf3R1f2R2f1R333f0R4'9p=1g00Wep,1AR5#E'=g00=UR6'=#>g00Mog00NhR7%A5g0131f4R8'@f5R9,@8'9f7R:f6R;P8P1P2P3E<P0f8R<#;g00LCR=P9P8C:p,1KR>%6<P:P1P2D5g00P>R?%791851g00?e#4#4#4#4#4#4#D#Cg00@J'=#>R@%28%22g005TRA%08%0233C1C1'9f9R2P:P;P9P8P1E<P4f:R1#;P=P:P;C:P>f;R8#6P1P;P9D5P?%7<185;P@%2:%29%0:%0953AC1C1'9P0P>f<R0#6P8P:P;D5P?%72185:P@%2<%2;%0<%0;53AC1C1f=R;P8P1P2P<P:E<P4P>f>R:#6P;P2P<D5P?%701851P@%28%22%08%0253AC1C1f@R<#;P=P;P0C:P>%6<R<P:P8P1D5R=P?%7;1858P@%20%21%00%0153AC1C1RA'9P9P=PAP>P<f?P:P8P1P2P3GBP4C?C?W3W1P3P4O2n2001000000120000000W0W2P3P4O2n2001000000121000000W0W4X77W9W6W8X;6X:6W5o"). Qed.
Lemma RX_wnn : forall X w s1 mo1 s2 mo2, RX X w s1 mo1 s2 mo2 -> 0 <= w.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h01Hh12HAh21Xh32_Hh43_H0h53mo1h63mo2h72s1h82s2h91wp;1p;2p;6p;4p;5p;3g00TFj1DTg00:7j2:Tg0081j1;Tg00kbj1@Tg00lUj6CTg00mIj1=Tg00[Kj4>Tg00ZWj14Tg00n=j58Tg00JWj17Tg00o1j26Tg008Qj13Tg0096j1?Tg009Tj1BTg00;Hj12Tg00C<j10Tg004>j35Tg00^^R0j29Tg011Wj2<Tg013Oj6ATf3R1f2R2f1R335f0R4'9p=1g00Wep,1AR5#D':g00=UR6':#;g00Mog00NhR7%@5f5R8f4R9P1P2P3P4ECP0f6R:#=g00LCR;P9P1C>p,1KR<%4:P8P2P3D8g00P>R=%791652g00?e#3#3#3#3#3#3#?#Bg00@J':#;R2%21%23g005TR>%01%0335C1C1'9g0131R1/<:P4f8R?#=P;P:P8C>P<f9R;#4P?P8P9D8P=f7R@#71658P2%2:%29%0:%0955>C1C1'9P0P<f:R0#4P;P:P8D8P=%7?165:P2%2@%28%0@%0855>C1C11<10P4P<f<#4f;R1P?P@D8P=%71165;P2%20%2?%00%0?55>C1C1P<f>#4f=P0P;P3EAW4W1P3P4O2n2001000000120000000W0W3P3P4O2n2001000000120000000W0X67W8W5W7X96W2o"). Qed.

Lemma RX_set : forall X w s1 mo1 s2 mo2 v, RX X w s1 mo1 s2 mo2 -> RX X w (set_so_ps v s1) mo1 (a_set_so A v s2) mo2.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "p'0h01Hh12HOh23Hsoh32HAh43Hfdh53Hfsh61Xh73mo1h83mo2h96ps_brki006ps_brkh:5ps_fai015ps_fah;4ps_mi024ps_mh<5ps_soi035ps_soh=1sh>2s1h?2s2h@1vhA1wi041pp;1p;2p;6p;4p;5p;3p;9p;7g00TFj1OTg00:7j2@Tg0081j1DTg00kbj1HTg00lUj6<Tg00mIj1;Tg00[Kj4:Tg00ZWj17Tg00n=j59Tg008Qj16Tg0096j1GTg009Tj1FTg00;Hj10Tg004>j32Tg00^^R0j21Tg014Jj25Tg015Dj38Tg00o1j2ETg00\<j1NTg00<<j2>Tg00b]j1MTg016<l9LTg0173j7KTg017mj4BTg018fj3JTg0056j6ITg00eBj4=Tg00JWj1CTg00C<j1ATg00P>R1f2R2#Cf1R3f0R4'E32p=4g005T%A3%A432p=3%C3=214p=?g00Wep,1AR5#O'@g00=UR6'@#Dg00MoR7g00NhR8%H5f6R9f5R:f4R;f3R<P2P3E<P0f7R=#;g00LCR>P:P;C:p,1KR?%7=P9P<P2D9A4:5<g00?e#6#6#6#6#6#6#G#Fg00@J'@#DR@%0;%023213;2'1'1'1f8RAP=1529P:A852;P<E<P4f9RB#;P>P=P9C:P?f:RC#7PBP9P:D9A4A59%0=%0:52@13=:'1'1'1P0P?f;RD#7PCP=P9D9A4B5=%0A%0952@13A9'1'1f<REPD159CPBA859AP=E<P4P?f=R=#7PEPBPAD9A4E5C%0D%0B52@13DB'1'1P0A4=5D%0E%0C52@13EC'1f@RAf?R9f>RF,5CP=A85CEPDE<P4A495=%09%0=52@139='1P0%0AR0%0F52@13AFfDRDfCREfBRC,5FfARGA85FAP9E<P4%0CR9=2@013EGfGR0#;RFP>fERA,5GRHPDC:P?%70R0fFRIA85GERJPCD9RK1E5JRJ,?HRL%0D=2@9R913DCR@'1RM'1RN'1PFP>PAPHPDP=g019bRH%NA'>%MA,>6g00Q9M9LPKPNP?P0PIPEPCPGPBFKPLPMP1PG15CI/?4X=1P7fH#;P>P4PAC:A435A15D2/?D]2]1PAg00O^fO#;P>P<P2P3P4CBfLR>C:P;P<P2P3CB?45>fK,>1W2W1X<1W:X96X;HP<P2P3P4O4n01104000140102100101103P=P:O2PJAJ?GEEIP9P@P3P4C=C=C=C=W5W4P3P4O2n2001000000121000000W0W2P3P4O2n2001000000121000000W0W3P3P4O2n2001000000121000000W0W1P3P4O2n2001000000121000000W0X@1X88W?W7W>XA6W6o"). Qed.

Lemma RX_models : forall X w s1 mo1 s2 mo2, RX X w s1 mo1 s2 mo2 ->
  minv mo1 /\ MI2 mo2 /\ m_halted mo1 = None /\ m_halted mo2 = None /\ m_fds mo1 = m_fds mo2 /\ m_fs mo1 = m_fs mo2.
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h01Hh11ah22H1h32H2h42HAh52HOh63Hfdh73Hfsh83Hsoh92M1h:2M2h;1Xh<3mo1h=3mo2h>2s1h?2s2h@1wp;1p;2p;6p;4p;5p;3g00TFj1STg00:7j2FTg0081j1GTg00kbj1KTg00lUj6RTg00mIj1ETg00[Kj4HTg00ZWj1?Tg00n=j5CTg00JWj1;Tg00o1j2=Tg008Qj19Tg0096j1QTg009Tj1PTg00;Hj10Tg00C<j11Tg00_oj14Tg00`bj1OTg00aDj18Tg00b;j1NTg004>j33Tg01:[j4JTg00^^R0j22Tg01;Uj6ITg00eBj4@Tg00P>f1R1f0R233p=>g005TR3%11;32p=6f5R4f4R5f3R6f2R7;31/22'2'2p=5%129331p=MA3671/22p=<%87=361/22p=DA3312p=:%01=372p=A1212,27p=B%029371p=L%81=372p=7g00Wep,1AR3#S'Fg00=UR8'F#Gg00Mog00NhR9%K3P4P5P6P7P1P2ERP0f6R:#Eg00LCR;P5P6CHp,1KR<%?:P4P7P1DC%;51=37'>g00?e#9#9#9#9#9#9#Q#PR=g00@J'F#GR>%06%01%11,66E5%45p,3MI2R6P7O1%O=R?%85%N=R=P?P7P=P>%05R@%07%15RA/M7C<CDE5P2f8R7#EP;P:P4CHP<f9R;#?P7P4P5DCf7R5#;1=34'>P>%0:RBP@%1:R@/:AE5P0P<f:RA#?P;P:P4DC%;71=3:'>%049A>5%14,653B%47P6P:O1P?%87P=P?P:P=P>%07RCPB%17RB/:@C<CDE5P2P<f<R@#?f;RDP7P5DC%;D1=3;'>%0AR5=3>C%1ARC/:B3BP0%;@1=3A'>P>%0D%0;%1;,6DC<%4@P6PAO1P?%8@P=P?PAP=P>%0@R;P5%1@R5/:CC<CDE5P2f>RC#;1=3@'>P>%0CR@P;%1CR;/:5C<P0f?R5#0R3f=RB5L>%1B,65f@R5#4P6PCO1P?%85P=P?PCP=P>%05P@%15R5/:;C<CDE5P2fA=A>3fB/65fFR5#EfDR3fCR;PBCJ%4;A7?;=RB'2P0%43A7?3=fER3#4P6P;O1P?%83P=%0;9A>3%1;,635BBE5P2%45fGRB=7?=R3P<fKR<#?fJR;PBP5PCEIP6P5O1A7?5='2P0P6PBO1P3%4;P6fHR3O1A7?;=RBA7?3=P>%0;%03%13,6;E53BP2P6fIO1fMR;#4P6P<O1R6A7?;=R3A7?<=R=%0<9A>;R>%1<,6;R;'2R<'2R?'2R0'2P:P6P0P1P3P?P4P=P<P2P>P;PDPAC@C@C@C@C@X3BW:P1P2O2n2001000000121000000b1W2W9P1P2O2n2001000000121000000b1W7W6P1P2O2n2001000000121000000W0W8P1P2O2n2001000000121000000W0W4P1P2O2n2001000000121000000W0W5P1P2O2n2001000000121000000W0X=9W?W<W>X@8W;o"). Qed.

Lemma RX_tables : forall X w s1 mo1 s2 mo2 f, RX X w s1 mo1 s2 mo2 ->
  minv (with_fds f mo1) -> MI2 (with_fds f mo2) -> m_halted (with_fds f mo1) = None -> m_halted (with_fds f mo2) = None ->
  RX X w s1 (with_fds f mo1) s2 (with_fds f mo2).
Proof.
ltac2:(KReplay.run1 (kr_t_EquivPA ()) ["ASide"] "h01Hh11fh22H1h32H2h42HAh52HOh63Hfdh73Hfsh83Hsoh92M1h:2M2h;1Xh<3mo1h=3mo2h>2s1h?2s2h@1wp;1p;2p;6p;4p;5p;3p;7p;9g00TFj1STg00:7j2CTg0081j1ETg00kbj1ITg008Qj1;Tg0096j1RTg009Tj1QTg00lUj6>Tg00mIj1ATg00[Kj4BTg00ZWj1=Tg00n=j5<Tg00JWj18Tg00o1j2:Tg00;Hj13Tg00^^R0j21Tg00hTj20Tg00_oj1?Tg00`bj1PTg00b;j1OTg004>j34Tg00C<j16Tg01<Rj7MTg01=Kl9LTg00<<j2KTg01>Fj2DTg0056j6FTg00eBj4@Tg00aDj1GTg00P>f1R1f0R234p=9f2R3%31;42p=7g005TR4%61%6234p=5f3R51031#G;42p=2A4412p=N%629441p=J%61=442p=Hg00Wep,1AR6#S'Cg00=UR7'C#Eg00Mog00NhR8%I6g00?e#;#;#;#;#;#;#R#QR9g00@J'C#ER:f6R;f5R<f4R=P5P3P1E>P0f7R>#Ag00LCR?P<P=CBp,1KR@%=>P;P5P3D<%8<1:65'9%3397:=15=3'1'1'1103<#?p,3MI2RA105=O1%P9RBP=P>%O9R9C2PBP<P;P9C2f<RCf;RDf:REf9RF,0;RGf8RH10;>E>[[[[P2%AFP?P>P;CBP@%=EPFP;P<D<%8H1:6;'9%3<97:>15><'1'1'1P0P@%=DPEP>P;D<%8F1:6>'9%3;97:H15H;'1'1%?GPA10>HO1PBPHPDP9C2PBPFPEP9C2f@R>f?RGf>R;f=R<,0ERIPC10EDE>[[[[P2P@%=<PCPFPHD<%8C1:6E'9%3F97:D15DF'1'1P0%8<1:6D'9%3E97:C15CE'1%?IPA10DCO1PBPCPGP9C2PBP<P;P9C2fDRCfCRDfBRIfARE,0;RHP>10;GE>[[[[P2%8G1:6<'9%3<97:G15G<'1P0%3>R0%3;54:15>;%?HPA10G>O1PBP>PDP9C2PBPEPIP9C2fHR>fGRGfFRHfER;,0IPC10IDRJE>[[[[P2A7:I015DE10EC#?PAPJO1PBPDPHP9C2PBPCP;P9C2fKR9#ARCP?fIR?10;>RBCBP@%=9R9fJRDPG10;HRJD<RA%8?1:6G'9R6%3JR097:BRI%6BRB%6JRJ'NRK'1RL'1RM'1PCP?P>P;PEP5P1FMPAPMP@P9PDPGPHP;P<P3P2M9LP6PLPFPIPK1K:0P4%6>10HG,J2X14P4%6H1H?2X14P=PJ1D;HEFPB1D;>EFC@C@C@C@W3W2W:W9W7W6P1P2O2n2001000000121000000W0W8P1P2O2n2001000000121000000W0W4P1P2O2n2001000000121000000W0W5P1P2O2n2001000000121000000W0W1X=8W?W<W>X@7W;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma size_overflows_REQMAX n : 0 <= n <= REQMAX -> size_overflows n = false.
Proof. intros Hn. unfold size_overflows, REQMAX in *. apply Z.leb_gt. lia. Qed.

Lemma malloc_pair : forall X w n, 0 <= n <= REQMAX -> HISTOK (n :: map snd X) -> 1 <= w ->
  rsim (RX X w) (raw_malloc n) (amalloc A n) (Qm RX X w n).
Proof.
  intros X w n Hn HH Hw. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs) G1 G2.
  eexists _, _. split; [| split].
  - apply (raw_malloc_STOT (pX X) GT n s1 mo1 frame_ok_GT HO ltac:(lia) (size_overflows_REQMAX n Hn) G1).
  - apply (ok_malloc K (aX X) w n s2 mo2 HA Hw Hn ltac:(rewrite sizes_aX; exact HH) G2).
  - intros a s1' mo1' b s2' mo2' (p & -> & HO' & Hn63 & Hso1 & Hfa1 & Hfd1 & Hfs1) (q & -> & HA' & _ & Hso2 & Hfd2 & Hfs2). cbn [Qm].
    split; [| exact Hn63]. split; [exact HO'|]. split; [exact HA'|]. split; [congruence|]. split; congruence.
Qed.

Lemma free_pair : forall X w p q n, rsim (RX ((p, q, n) :: X) w) (raw_free p) (afree A q) (fun _ _ => RX X w).
Proof.
  intros X w p q n. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs) G1 G2.
  eexists _, _. split; [| split].
  - apply (raw_free_STOT (pX X) GT p s1 mo1 frame_ok_GT HO G1).
  - apply (ok_free K (aX X) w q n s2 mo2 HA G2).
  - intros a s1' mo1' b s2' mo2' (HO' & Hso1 & Hfa1 & Hfd1 & Hfs1) (HA' & Hso2 & Hfd2 & Hfs2).
    split; [exact HO'|]. split; [exact HA'|]. split; [congruence|]. split; congruence.
Qed.

(* [comment removed for export] *)
Lemma annot2_pair : forall X w p q c, 0 < c ->
  rsim (RX ((p, q, c) :: X) w) ((fun (_ : bptr) (_ : Z) => mret tt) p c) (aannot A q c c 0 ;;; aannot A q c 0 c) (fun _ _ => RX ((p, q, c) :: X) w).
Proof.
  intros X w p q c Hc. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs) G1 G2.
  eexists _, _. split; [apply STOT_ret| split].
  - eapply STOT_bind.
    + apply STOT_path.
      apply (ok_annot K (aX ((p, q, c) :: X)) w q c c 0 s2 mo2 HA ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(right; reflexivity) (tglob_ebind_l _ _ _ _ _ G2)).
    + intros [] s2' mo2' ((HA' & Hso2 & Hfd2 & Hfs2) & Hp). cbn beta.
      assert (G2' : tglob step2 Phi2 (aannot A q c 0 c s2') mo2').
      { unfold mbind in G2. exact (tglob_ebind_r _ _ _ _ _ _ _ _ G2 Hp). }
      eapply STOT_mono; [apply (ok_annot K (aX ((p, q, c) :: X)) w q c 0 c s2' mo2' HA' ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(left; reflexivity) G2')|].
      intros [] s2'' mo2'' (HA'' & Hso3 & Hfd3 & Hfs3). cbn beta.
      instantiate (1 := fun _ s' mo' => AI K (aX ((p, q, c) :: X)) w s' mo' /\ a_so A s' = a_so A s2 /\ m_fds mo' = m_fds mo2 /\ m_fs mo' = m_fs mo2). cbn beta.
      split; [exact HA''|]. split; [congruence|]. split; congruence.
  - intros [] s1' mo1' [] s2' mo2' (_ & -> & ->) (HA' & Hso2 & Hfd2 & Hfs2).
    split; [exact HO|]. split; [exact HA'|]. split; [congruence|]. split; congruence.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sub1 : forall n mo r mo' e, ~ nf_node n -> nstep n mo r mo' e -> nstep n mo r mo' e.
Proof. auto. Qed.
Lemma same1 : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstep n mo r mo e.
Proof. auto. Qed.
Lemma io1 : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstep n mo r mo' e.
Proof. auto. Qed.
Lemma MI1_pres : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> io_node n -> minv mo -> m_halted mo = None -> minv mo' /\ m_halted mo' = None.
Proof. intros n mo rsp mo' evs Hst _ Hmi Hh. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi']. auto. Qed.

Local Notation rsimeq := (rsimeq nstep step2 PhiP Phi2).

Lemma diag_pair : forall X w d, diag_short d -> rsimeq (RX X w) (io_diag io d) (io_diag (ioA A) d) (fun _ => RX X w).
Proof. intros X w d _. cbn [io ioA io_diag io_S]. apply (s_diag_sim nstep step2 PhiP Phi2 sub1 same1 (ok_sub2 K) (ok_same2 K)). Qed.

Lemma emit_pair : forall X w v, rsimeq (RX X w) (io_emit io v) (io_emit (ioA A) v) (fun _ => RX X w).
Proof.
  intros X w v. cbn [io ioA io_emit io_S].
  apply (s_emit_sim nstep step2 PhiP Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) ps_so set_so_ps (a_so A) (a_set_so A) (RX X w) (RX_get X w) (RX_set X w)).
Qed.

Lemma ioexit_pair : forall X w, rsimeq (RX X w) (io_exit io) (io_exit (ioA A)) (fun _ => RX X w).
Proof.
  intros X w. cbn [io ioA io_exit io_S].
  apply (stdout_exit_flush_sim nstep step2 PhiP Phi2 sub1 same1 io1 (ok_sub2 K) (ok_same2 K) (ok_io2 K) ps_so set_so_ps (a_so A) (a_set_so A) (RX X w) (RX_get X w) (RX_set X w)).
Qed.

Lemma exitnode_pair : forall X w c (Q : Empty_set -> Empty_set -> rel), rsim (RX X w) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof. intros X w c Q. apply (exit_node_sim nstep step2 PhiP Phi2 sub1 (ok_sub2 K) minv MI2 (RX X w) (RX_models X w)). Qed.

(* [comment removed for export] *)
Lemma nh_pair : forall X w (Q : Empty_set -> Empty_set -> rel), rsim (RX X w) new_handler (new_handlerA A) Q.
Proof. intros X w Q. unfold new_handler, new_handlerA. apply rsim_munr. Qed.

Lemma open_pair : forall X w path, rsimeq (RX X w) (msys (NOpen path) dec_open) (msys (NOpen path) dec_open) (fun _ => RX X w).
Proof. intros X w path. apply (open_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX X w) (RX_models X w) (RX_tables X w)). Qed.
Lemma close_pair : forall X w fd, rsimeq (RX X w) (msys (NClose fd) dec_close) (msys (NClose fd) dec_close) (fun _ => RX X w).
Proof. intros X w fd. apply (close_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX X w) (RX_models X w) (RX_tables X w)). Qed.
Lemma read_pair : forall X w fd buf1 buf2 cnt, 0 <= cnt < 2^64 ->
  rsimeq (RX X w) (msys (NRead fd buf1 cnt) (dec_read buf1 cnt)) (msys (NRead fd buf2 cnt) (dec_read buf2 cnt))
         (fun a => match a with RdData bs => fun s1 mo1 s2 mo2 => RX X w s1 mo1 s2 mo2 /\ zlength bs <= cnt | RdErr _ => RX X w end).
Proof. intros X w fd buf1 buf2 cnt Hcnt. apply (read_sim nstep step2 PhiP Phi2 sub1 io1 (ok_sub2 K) (ok_io2 K) minv MI2 MI1_pres (ok_MI2 K) (RX X w) (RX_models X w) (RX_tables X w)). exact Hcnt. Qed.

(* [comment removed for export] *)
Lemma run_pair : forall X w cfg payload, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_OPS <= w ->
  rsimeq (RX X w) (run cfg payload) (runA A cfg payload) (fun _ => RX X (w - RUN_OPS)).
Proof.
  intros X w cfg payload HL Hp Hw. unfold run, runA, Prog.fuzz_one, fuzz_oneA.
  apply (target_run_sim nstep step2 PhiP Phi2 RX raw_malloc (amalloc A) raw_free (afree A) new_handler (new_handlerA A)
           (io_emit io) (io_emit (ioA A))
           malloc_pair free_pair RX_perm RX_credit nh_pair emit_pair X w cfg payload HL Hp Hw).
Qed.

(* [comment removed for export] *)
Lemma main_exit_pair : forall argv w (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv -> MAIN_OPS <= w ->
  rsim (RX [] w) (code <- main_model io raw_malloc raw_free rsP alloc_init run alloc_count argv ;; exit_model io code)
                 (progA_main A rsA argv) Q.
Proof.
  intros argv w Q Hargv Hw. unfold progA_main.
  apply (main_exit_sim nstep step2 PhiP Phi2 io (ioA A) raw_malloc (amalloc A) raw_free (afree A) rsP rsA
           alloc_init (alloc_initA A) run (runA A) alloc_count (alloc_countA A) RX
           malloc_pair free_pair RX_perm RX_credit diag_pair).
  - intros X w0 bm. apply rsimeq_ret. intros ? ? ? ? H; exact H.
  - intros X w0. apply rsimeq_ret. intros ? ? ? ? H; exact H.
  - apply run_pair.
  - apply open_pair.
  - apply close_pair.
  - apply read_pair.
  - apply ioexit_pair.
  - apply exitnode_pair.
  - exact Hargv.
  - exact Hw.
Qed.

(* [comment removed for export] *)
Lemma OWN_vm X s mo mo' : OWN X GT s mo -> m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> minv mo' -> m_halted mo' = None -> OWN X GT s mo'.
Proof.
  intros [(L & Hc & HK & Hi) [Hnd _]] Hvm Hkb Hmi Hh. split; [|split; [exact Hnd| exact I]].
  exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_fds; [exact HK| exact Hvm| exact Hkb| exact Hmi| exact Hh].
Qed.

Section Pre.
Variable pre : Monad.M (ASt A) unit.
Hypothesis pre_pair : forall X w, rsim (RX X w) startup pre (fun _ _ => RX X w).

Lemma prog_pair : forall argv w (Q : Empty_set -> Empty_set -> rel), Forall (fun a => zlength a <= PIECE_MAX) argv -> MAIN_OPS <= w ->
  rsim (RX [] w) (prog_with rsP argv) (pre ;;; progA_main A rsA argv) Q.
Proof.
  intros argv w Q Hargv Hw. unfold prog_with. eapply rsim_seq; [apply pre_pair|]. intros [] []. apply main_exit_pair; [exact Hargv| exact Hw].
Qed.

(* [comment removed for export] *)
Definition treeA (sA0 : ASt A) (argv : list (list Z)) : itree node (exc unit) :=
  ebind ((pre ;;; progA_main A rsA argv) sA0) (fun p => match fst p : Empty_set with end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma RX_init : forall en inp w sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  AI K [] w sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp ->
  RX [] w (ps_init (reservedZ psegs) (entry_atop en)) (mo0 psegs LS en inp) sA0 moA0.
Proof.
  intros [sp brk0 mbase rnd] inp w sA0 moA0 Hve Hvi HA Hso Hfd Hfs.
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hvi) in Hve. destruct Hve as ((Hsp1 & Hsp2 & _) & Hbrk & Hmb & _).
  split; [| split; [exact HA| split; [cbn; symmetry; exact Hso| split; [rewrite m_fds_mo0; symmetry; exact Hfd| rewrite m_fs_mo0; symmetry; exact Hfs]]]].
  unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp].
  eapply OWN_weakG; [apply GI_with_vdso; apply (GI_init psegs brk0 mbase sp LS inp _ Hbrk ltac:(rewrite reserved_top_plain; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_plain (valid_input_either_reader _ Hvi) Hmb resv_plain)|]. intros _; exact I.
Qed.

Lemma argv_Z_pieces' : forall argv, valid_argv argv -> Forall (fun a => zlength a <= PIECE_MAX) (argv_Z argv).
Proof.
  intros argv Hv. eapply Forall_impl; [|apply (argv_Z_short argv Hv)]. intros a Ha. unfold ARG_MAX_LEN, PIECE_MAX in *. lia.
Qed.

Lemma tglob_prog : forall en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tglob nstep PhiP (prog psegs rsP inp en) (mo0 psegs LS en inp).
Proof.
  intros en inp He Hi. apply tglob_PhiP_intro.
  - unfold mo0. apply minv_init; [| exact (valid_input_either_reader _ Hi)].
    destruct en as [sp ? ? ?]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He.
    destruct He as ((Hsp1 & Hsp2 & _) & _). cbn [en_sp]. split; [exact Hsp1| exact Hsp2].
  - destruct en; reflexivity.
  - exact (proj2 (prog_model_ok_plain_L LS rsP en inp HLS He Hi)).
  - exact (never_forced_p_L LS rsP en inp HLS He Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ttrace_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop)
      (t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo tr :
  ttrace step nexit (ebind t f) mo tr <-> ttrace step nexit t mo tr.
Proof.
  rewrite !ttrace_split, texit_ebind. split.
  - intros [[Hx|(tr1 & [[] ?] & _)]|(r & mo' & Hp)]; [left; exact Hx|].
    apply tpath_ebind in Hp as [[Hp ->]|(tr1 & [[] ?] & _)]. right. exists Unr, mo'. exact Hp.
  - intros [Hx|(r & mo' & Hp)]; [left; left; exact Hx|]. right. destruct r as [|[[] ?]]. exists Unr, mo'. apply tpath_ebind. left. auto.
Qed.

Lemma tpath_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop)
      (t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo tr r mo' :
  tpath step (ebind t f) mo tr r mo' -> exists r', tpath step t mo tr r' mo'.
Proof. intros Hp. apply tpath_ebind in Hp as [[Hp ->]|(tr1 & [[] ?] & _)]. exists Unr. exact Hp. Qed.

Lemma tglob_after_empty {S} (step : node -> Model -> resp -> Model -> list event -> Prop) Phi
      (t : itree node (exc (Empty_set * S))) (f : Empty_set * S -> itree node (exc unit)) mo :
  tglob step Phi (ebind t f) mo <-> tglob step Phi t mo.
Proof.
  split; [apply tglob_ebind_l|]. intros H. apply tglob_ebind; [exact H|]. intros tr [[] ?] mo' _.
Qed.

Theorem equiv_core_pre : forall en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  AI K [] MAIN_OPS sA0 moA0 -> a_so A sA0 = stdout_init -> m_fds moA0 = init_fds -> m_fs moA0 = in_fs inp ->
  tglob step2 Phi2 (treeA sA0 (argv_Z (in_argv inp))) moA0 ->
  (forall tr, ttrace nstep nexit (prog psegs rsP inp en) (mo0 psegs LS en inp) tr
              <-> ttrace step2 nexit (treeA sA0 (argv_Z (in_argv inp))) moA0 tr)
  /\ (forall tr r mo', ~ tpath step2 (treeA sA0 (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros en inp sA0 moA0 He Hi HA Hso Hfd Hfs GA. pose proof Hi as (Hargv & _).
  pose proof (prog_model_ok_plain_L LS rsP en inp HLS He Hi) as [NL _].
  destruct (rsim_ttrace nstep step2 nexit nexit PhiP Phi2 (RX [] MAIN_OPS) (prog_with rsP (argv_Z (in_argv inp))) (pre ;;; progA_main A rsA (argv_Z (in_argv inp)))
              (fun _ _ _ _ _ _ => False) (ps_init (reservedZ psegs) (entry_atop en)) (mo0 psegs LS en inp) sA0 moA0
              (prog_pair _ _ _ (argv_Z_pieces' _ Hargv) (Z.le_refl _)) (RX_init en inp MAIN_OPS sA0 moA0 He Hi HA Hso Hfd Hfs)) as [EQ NL2].
  - apply (tglob_after_empty nstep PhiP _ (fun p => match fst p : Empty_set with end)). exact (tglob_prog en inp He Hi).
  - apply (tglob_after_empty step2 Phi2 _ (fun p => match fst p : Empty_set with end)). exact GA.
  - intros tr r mo' Hp. destruct r as [|[[] ?]]. apply (NL tr Unr mo'). unfold prog, prog_itree. apply tpath_ebind. left. auto.
  - split.
    + intros tr. unfold prog, prog_itree, treeA. rewrite !ttrace_after_empty. apply EQ.
    + intros tr r mo' Hp. unfold treeA in Hp. apply tpath_after_empty in Hp as [r' Hp]. exact (NL2 tr r' mo' Hp).
Qed.
End Pre.

(* [comment removed for export] *)
Lemma startup_pair : forall X w, rsim (RX X w) startup (mret tt) (fun _ _ => RX X w).
Proof.
  intros X w. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & HA & Hso & Hfd & Hfs) G1 G2.
  destruct (OWN_minv _ _ _ HO) as [Hmi Hh].
  eexists _, _. split; [apply (startup_STOT s1 mo1 Hmi Hh)| split; [apply STOT_ret|]].
  intros [] s1' mo1' [] s2' mo2' (-> & Hvm & Hfd1 & Hfs1 & Hmi' & Hh' & Hkb) (_ & -> & ->).
  split; [exact (OWN_vm _ _ _ _ HO Hvm Hkb Hmi' Hh')|]. split; [exact HA|]. split; [exact Hso|]. split; congruence.
Qed.

Theorem equiv_core : forall en inp sA0 moA0,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp -> AHAND inp sA0 moA0 ->
  (forall tr, ttrace nstep nexit (prog psegs rsP inp en) (mo0 psegs LS en inp) tr
              <-> ttrace step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr)
  /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros en inp sA0 moA0 He Hi (HA & Hso & Hfd & Hfs & GA).
  change (progA_tree A sA0 rsA (argv_Z (in_argv inp))) with (treeA (mret tt) sA0 (argv_Z (in_argv inp))) in GA |- *.
  exact (equiv_core_pre (mret tt) startup_pair en inp sA0 moA0 He Hi HA Hso Hfd Hfs GA).
Qed.

End ASide.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition toP (en : ExecEntry) : ExecEntry :=
  mkEntry (en_sp en) (Z_to_bv 64 (reserved_top (segments_reserved psegs))) (en_mmap_base en) (en_draw en).

Lemma toP_valid : forall segsX pcX phX en inp,
  valid_entry (mkImage segsX pcX phX) en inp -> valid_entry (mkImage psegs p_init_pc p_phdrs) (toP en) inp.
Proof.
  intros segsX pcX phX [sp brk0 mbase] inp H. cbn [valid_entry valid_entry_va toP en_sp en_mmap_base] in H |- *. destruct H as (Hsp & _ & Hmb & Hst).
  split; [exact Hsp|]. split; [| split; [exact Hmb| exact Hst]].
  unfold valid_brk. rewrite reserved_top_plain. rewrite unsigned_lit by lia. unfold brk_aslr_max, page_size. split; [lia|]. split; [lia| reflexivity].
Qed.

From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require ITreeA.

Theorem equiv_PA_L (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
        (rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) (LS : Z) (HLS : 2^31 <= LS) :
  forall enP inp sA0 moA0,
    valid_entry (mkImage psegs p_init_pc p_phdrs) enP inp -> valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
    trace_equiv (tree_traces (prog psegs rsP inp enP) (mo0 psegs LS enP inp))
                (ITreeA.ptraces step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0)
    /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof.
  intros enP inp sA0 moA0 HeP Hi HH.
  destruct (equiv_core A step2 Phi2 MI2 rsP rsA K LS HLS enP inp sA0 moA0 HeP Hi HH) as [EQ NL2].
  split; [| exact NL2]. intros tr. unfold tree_traces, ITreeA.ptraces. split; intros (full & Hf & Hp); exists full; split; auto; apply EQ; exact Hf.
Qed.

(* [comment removed for export] *)
Theorem equiv_PA (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
        (rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) :
  forall enP inp sA0 moA0,
    valid_entry (mkImage psegs p_init_pc p_phdrs) enP inp -> valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
    trace_equiv (tree_traces (prog psegs rsP inp enP) (mo0 psegs source_alloc_limit enP inp))
                (ITreeA.ptraces step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0)
    /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof. exact (equiv_PA_L A step2 Phi2 MI2 rsP rsA K source_alloc_limit lim_p). Qed.

(* [comment removed for export] *)
Corollary equiv_PA_toP_L (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
        (rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) (LS : Z) (HLS : 2^31 <= LS) :
  forall segsX pcX phX enX inp sA0 moA0,
    valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
    trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs LS (toP enX) inp))
                (ITreeA.ptraces step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0)
    /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof. intros segsX pcX phX enX inp sA0 moA0 HeX Hi HH. exact (equiv_PA_L A step2 Phi2 MI2 rsP rsA K LS HLS (toP enX) inp sA0 moA0 (toP_valid _ _ _ _ _ HeX) Hi HH). Qed.

Corollary equiv_PA_toP (A : AAlloc) (step2 : node -> Model -> resp -> Model -> list event -> Prop) (Phi2 : node -> Model -> Prop) (MI2 : Model -> Prop)
        (rsP rsA : Z) (K : AAllocOK A step2 Phi2 MI2) :
  forall segsX pcX phX enX inp sA0 moA0,
    valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp -> AHAND A step2 Phi2 MI2 rsA K inp sA0 moA0 ->
    trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs source_alloc_limit (toP enX) inp))
                (ITreeA.ptraces step2 nexit (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0)
    /\ (forall tr r mo', ~ tpath step2 (progA_tree A sA0 rsA (argv_Z (in_argv inp))) moA0 tr r mo').
Proof. intros segsX pcX phX enX inp sA0 moA0 HeX Hi HH. exact (equiv_PA A step2 Phi2 MI2 rsP rsA K (toP enX) inp sA0 moA0 (toP_valid _ _ _ _ _ HeX) Hi HH). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PasA : AAlloc := mkAAlloc PState bptr raw_malloc raw_free (fun _ _ _ _ => mret tt) ptr_addr ps_so set_so_ps.
Definition AIP (Y : list (bptr * Z)) (w : Z) (s : PState) (mo : Model) : Prop := OWN (map fst Y) GT s mo /\ 0 <= w.

Lemma p_get_set : forall v s, ps_so (set_so_ps v s) = v.
Proof. intros v [? ? ? ?]; reflexivity. Qed.
Lemma p_set_set : forall v w s, set_so_ps v (set_so_ps w s) = set_so_ps v s.
Proof. intros v w [? ? ? ?]; reflexivity. Qed.
Lemma p_set_get : forall s, set_so_ps (ps_so s) s = s.
Proof. intros [? ? ? ?]; reflexivity. Qed.
Lemma p_addr_so : forall v s p, ptr_addr (set_so_ps v s) p = ptr_addr s p.
Proof. intros v [? ? ? ?] p; reflexivity. Qed.

Lemma AIP_perm : forall Y Y' w s mo, Permutation Y Y' -> AIP Y w s mo -> AIP Y' w s mo.
Proof. intros Y Y' w s mo HP [H Hw]. split; [| exact Hw]. eapply OWN_perm; [apply Permutation_map; exact HP| exact H]. Qed.
Lemma AIP_so : forall Y w s mo v, AIP Y w s mo -> AIP Y w (set_so_ps v s) mo.
Proof. intros Y w s mo v [H Hw]. split; [| exact Hw]. eapply OWN_other; [exact H| reflexivity| reflexivity| exact I]. Qed.
Lemma AIP_model : forall Y w s mo, AIP Y w s mo -> minv mo /\ m_halted mo = None.
Proof. intros Y w s mo [H _]. exact (OWN_minv _ _ _ H). Qed.
Lemma AIP_fds : forall Y w s mo f, AIP Y w s mo -> minv (with_fds f mo) -> m_halted (with_fds f mo) = None -> AIP Y w s (with_fds f mo).
Proof. intros Y w s mo f [H Hw] M Hh. split; [exact (OWN_fds _ _ _ _ H M Hh)| exact Hw]. Qed.
Lemma AIP_credit : forall Y w w' s mo, 0 <= w' <= w -> AIP Y w s mo -> AIP Y w' s mo.
Proof. intros Y w w' s mo Hw' [H _]. split; [exact H| lia]. Qed.
Lemma AIP_wnn : forall Y w s mo, AIP Y w s mo -> 0 <= w.
Proof. intros Y w s mo [_ Hw]. exact Hw. Qed.

Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).

Lemma P_malloc : forall Y w n s mo, AIP Y w s mo -> 1 <= w -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  tglob nstep PhiP (raw_malloc n s) mo ->
  STOTP (raw_malloc n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AIP ((q, n) :: Y) (w - 1) s' mo' /\ n < 2^63
                         /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y w n s mo [HA Hw0] Hw Hn _ G.
  eapply STOT_mono; [apply (raw_malloc_STOT (map fst Y) GT n s mo frame_ok_GT HA ltac:(lia) (size_overflows_REQMAX n Hn) G)|].
  intros r s' mo' (p & -> & HO & H63 & Hso & _ & Hfd & Hfs). exists p.
  split; [reflexivity|]. split; [unfold AIP; cbn [map fst]; split; [exact HO| lia]|].
  split; [exact H63|]. split; [exact Hso|]. split; [exact Hfd| exact Hfs].
Qed.

Lemma P_free : forall Y w q n s mo, AIP ((q, n) :: Y) w s mo -> tglob nstep PhiP (raw_free q s) mo ->
  STOTP (raw_free q s) mo (fun _ s' mo' => AIP Y w s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y w q n s mo [HA Hw] G. eapply STOT_mono; [apply (raw_free_STOT (map fst Y) GT q s mo frame_ok_GT HA G)|].
  intros [] s' mo' (HO & Hso & _ & Hfd & Hfs). unfold AIP.
  split; [split; [exact HO| exact Hw]|]. split; [exact Hso|]. split; [exact Hfd| exact Hfs].
Qed.

Lemma P_annot : forall Y w (q : bptr) (cap old new : Z) s mo, AIP Y w s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap ->
  (old = 0 \/ new = 0) ->
  tglob nstep PhiP (mret tt s) mo ->
  STOTP (mret tt s) mo (fun _ s' mo' => AIP Y w s' mo' /\ ps_so s' = ps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y w q cap old new s mo HA _ _ _ _ _. eapply STOT_mono; [apply STOT_ret|]. intros [] s' mo' (_ & -> & ->). auto.
Qed.

Definition KP : AAllocOK PasA nstep PhiP minv :=
  mkAAllocOK PasA nstep PhiP minv sub1 same1 io1 MI1_pres p_get_set p_set_set p_set_get p_addr_so
             AIP AIP_perm AIP_so AIP_model AIP_fds AIP_credit AIP_wnn P_malloc P_free P_annot.

Local Notation RXP := (RX PasA nstep PhiP minv KP).

(* [comment removed for export] *)
Lemma startup_startup : forall X w, rsim nstep nstep nexit nexit PhiP PhiP (RXP X w) startup startup (fun _ _ => RXP X w).
Proof.
  intros X w. apply rsim_silent. intros s1 mo1 s2 mo2 (HO & [HA Hw] & Hso & Hfd & Hfs) G1 G2.
  destruct (OWN_minv _ _ _ HO) as [Hmi1 Hh1]. destruct (OWN_minv _ _ _ HA) as [Hmi2 Hh2].
  eexists _, _. split; [apply (startup_STOT s1 mo1 Hmi1 Hh1)| split; [apply (startup_STOT s2 mo2 Hmi2 Hh2)|]].
  intros [] s1' mo1' [] s2' mo2' (-> & Hvm1 & Hfd1 & Hfs1 & Hmi1' & Hh1' & Hkb1) (-> & Hvm2 & Hfd2 & Hfs2 & Hmi2' & Hh2' & Hkb2).
  split; [exact (OWN_vm _ _ _ _ HO Hvm1 Hkb1 Hmi1' Hh1')|].
  split; [split; [exact (OWN_vm _ _ _ _ HA Hvm2 Hkb2 Hmi2' Hh2')| exact Hw]|]. split; [exact Hso|]. split; congruence.
Qed.

(* [comment removed for export] *)
Theorem equiv_PP_L : forall LS, 2^31 <= LS -> forall rs rs' en en' inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_entry (mkImage psegs p_init_pc p_phdrs) en' inp -> valid_input_either inp ->
  trace_equiv (tree_traces (prog psegs rs inp en) (mo0 psegs LS en inp))
              (tree_traces (prog psegs rs' inp en') (mo0 psegs LS en' inp)).
Proof.
  intros LS HLS rs rs' en en' inp He He' Hi. apply trees_equiv_of_ttrace.
  change (prog psegs rs' inp en') with (treeA PasA rs' startup (ps_init (reservedZ psegs) (entry_atop en')) (argv_Z (in_argv inp))).
  apply (equiv_core_pre PasA nstep PhiP minv rs rs' KP LS HLS startup startup_startup en inp _ _ He Hi).
  - destruct en' as [sp brk0 mbase rnd]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He'. destruct He' as ((Hsp1 & Hsp2 & _) & Hbrk & Hmb & _). unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp AI KP]. unfold AIP. cbn [map].
    split; [| unfold MAIN_OPS, READ_OPS, RUN_OPS, FUZZ_OPS; lia].
    eapply OWN_weakG; [apply GI_with_vdso; apply (GI_init psegs brk0 mbase sp LS inp _ Hbrk ltac:(rewrite reserved_top_plain; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_plain (valid_input_either_reader _ Hi) Hmb resv_plain)|]. intros _; exact I.
  - reflexivity.
  - apply m_fds_mo0.
  - apply m_fs_mo0.
  - change (treeA PasA rs' startup (ps_init (reservedZ psegs) (entry_atop en')) (argv_Z (in_argv inp))) with (prog psegs rs' inp en'). apply (tglob_prog rs' LS HLS); assumption.
Qed.

(* [comment removed for export] *)
Theorem equiv_PP : forall rs rs' en en' inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_entry (mkImage psegs p_init_pc p_phdrs) en' inp -> valid_input_either inp ->
  trace_equiv (tree_traces (prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp))
              (tree_traces (prog psegs rs' inp en') (mo0 psegs source_alloc_limit en' inp)).
Proof. exact (equiv_PP_L source_alloc_limit lim_p). Qed.
