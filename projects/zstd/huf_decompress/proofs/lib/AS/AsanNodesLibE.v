(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanCeil.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanNodesLibE () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsDcheck_syscall_ok_iffC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC59OSSVerify5KrLib2AS8AsanAcctNmaterialize_model_accesses_nilC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00I47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg04C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanAcct7node_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib2AS=AsanNodesLibEHsstep_cfg_of_check_noaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5NodesEsstep_cfg_svc_inv_chkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS5Nodes7halt_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01K47Corelib4Init9Datatypes4list02K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib2AS=AsanNodesLibEEnode_chk_ev_gen_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibEAnode_chk_ev_noaccC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bC59OSSVerify5KrLib2AS5NodesDuniform_not_spuriousC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE>node_det_noaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg:rz_silent1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlg;srz_silent1C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS7SpinAlg9srealizes01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg5t_altC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgBsrealizes_nonemptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS7SpinAlg9srealizes03C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC59OSSVerify5KrLib2AS8RefNodes5tid_IC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE>node_chk_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE9srz_casesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC59OSSVerify5KrLib2AS8RefNodesFvm_forget_range_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibEHwith_mmap_backing_haltedC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC59OSSVerify5KrLib2AS8AllocSimBwith_vmmaps_haltedC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@forget_vm_rangesK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_model_nextC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsc59OSSVerify5KrLib2AS=AsanNodesLibEGforget_vm_ranges_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim9brk_modelC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes5ependC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC45stdpp9bitvector;definitions4BvWfK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib2AS=AsanNodesLibE>asanreflect_fxC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepC59OSSVerify5KrLib3Lib3CfgAtransparent_instrC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C59OSSVerify5KrLib2AS8ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibECstepacc_ecall_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE@node_instr_noaccC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib2AS8AgentLib7u64_litC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim6unfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib2AS8AllocSimFpage_round_up_Z_boundsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib2AS7MmapSim=page_round_upC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim>munmap_args_okC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C59OSSVerify5KrLib2AS8RefNodes<munmap_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSimDmunmap_check_modeledC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC47Corelib4Init9Datatypes4andbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC46Stdlib5Lists4List6filterK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC59OSSVerify5KrLib2AS8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSimCmunmap_model_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodesAadv_unmaps1_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE=srz_det_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE<srz_sys_lazyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEK46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2AS8RefNodes>asanreflect_fxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodes7brk_admC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00C47Corelib4Init6Specif9proj1_sigC59OSSVerify5KrLib2AS8AllocSimAbrk_resolution_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=brk_refusal_bK47Corelib4Init6Specif3sig01C59OSSVerify5KrLib2AS8AllocSim<brk_ok_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodesCbrk_adm_nonspuriousC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC59OSSVerify5KrLib2AS8AllocSim:brk_ok_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodesCbrk_nonspurious_admC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsEcheck_syscall_err_iffC59OSSVerify5KrLib2AS8AllocSim@brk_no_unmodeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE@brk_model_haltedC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap7min_brkC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;brk_grow_okC59OSSVerify5KrLib2AS8RefNodesAbrk_adm_of_uniqueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE=node_brk_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodes=adv_ret_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodes?with_vmmaps_etaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodes:vmmaps_etaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim?brk_model_queryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim?brk_unmaps_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim?brk_zeros_queryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim5zfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodesCbrk_r_ok_grow_casesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib2AS8RefNodesBbrk_refusal_b_moveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_page_rangeC59OSSVerify5KrLib2AS8RefNodes=Z_to_bv_u_eq'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib2AS8RefNodes@adv_zeros1_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodesAbrk_model_grow_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7add_modC59OSSVerify5KrLib2AS8AllocSimGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib2AS8AllocSim?brk_unmaps_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim>brk_zeros_growC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibEAsrz_brk_grow_lazyC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib4Init5Logic2or01C59OSSVerify5KrLib2AS8RefNodes>brk_model_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim>brk_zeros_keepC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys6Kernel4ForkEcheck_set_tid_addressC59OSSVerify5KrLib2AS8RefNodes@check_syscall_96C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC46Stdlib4Bool4Bool=andb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State7m_credsC4ELinuxProcessSemantics?LinuxProcessSem5StateBm_setsid_succeededC4ELinuxProcessSemantics?LinuxProcessSem5State9m_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem5State?procst_childrenC4ELinuxProcessSemantics?LinuxProcessSem5State9m_utsnameC4ELinuxProcessSemantics?LinuxProcessSem5StateGm_sigaltstack_installedC4ELinuxProcessSemantics?LinuxProcessSem5State=procst_killedC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_sigabrt_pendingC4ELinuxProcessSemantics?LinuxProcessSem5State@m_abort_terminalC4ELinuxProcessSemantics?LinuxProcessSem5State:m_statpinsK4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState01C59OSSVerify5KrLib2AS8RefNodes?with_tid_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgCacfg_nonspurious_noC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEc59OSSVerify5KrLib2AS=AsanNodesLibEAnode_set_tid_lazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib2AS:AgentNodes=adv_set_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodes:one_tid_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes>asanreflect_fxC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib2AS8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlg8srz_exitC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC56Stdlib6ZArith6BinInt1Z3eqbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;MAP_PRIVATEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_NONEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9MAP_FIXEDC59OSSVerify5KrLib2AS8RefNodes6t_alt3C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS8RefNodes5three00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8RefNodes5three01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8RefNodes5three02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8RefNodes5three03C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC47Corelib4Init9Datatypes4negbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC56Stdlib6ZArith6BinInt1Z3lebC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bc59OSSVerify5KrLib2AS=AsanNodesLibEAmmap_gates_core50C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6leb_gtC46Stdlib4Bool4Bool;andb_true_rC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib2AS8AsanCeilCmmap_anon_b_of_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodes:mmap_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibEGfixedin_destroyed_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibE@fixedin_ok_modelC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTC59OSSVerify5KrLib2AS8AsanCeilDmmap_off_aligned_b_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibEBmmap_fixedin_checkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_belowc59OSSVerify5KrLib2AS=AsanNodesLibE>fixedin_ok_effC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodesBrefusal_b_mmap_sysC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunLspurious_refusal_not_refusalC59OSSVerify5KrLib2AS8RefNodesCmm_refusal_spuriousC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos4succI4ELinuxProcessSemantics5Riscv7Prelude4tree00C57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC57Corelib7BinNums6PosDef3Pos3eqbc59OSSVerify5KrLib2AS=AsanNodesLibEAfixedin_ok_vmmapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibEHfixedin_destroyed_vmmapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibEKwith_mmap_destroyed_halted'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS=AsanNodesLibEMwith_mmap_replacement_halted'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeI47Corelib7Numbers7BinNums8positive00C4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics5Riscv3Sem2w0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=MAP_NORESERVEC69OSSVerify5KrLib2AS8AsanPlan2AP;is_ecall_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP2pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC69OSSVerify5KrLib2AS:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I69OSSVerify5KrLib2AS8AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions?bv_and_unsignedI47Corelib7Numbers7BinNums1N00C35stdpp7tactics<f_equal_helpI69OSSVerify5KrLib2AS=AsanPlanSound3APS5cs_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS2MrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6refuseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS6allowAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS6fds_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP8a_tidsetC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC69OSSVerify5KrLib2AS8AsanPlan2AP6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS:maps_matchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS7hole_okC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS=AsanPlanSound3APS4seps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib2AS=AsanPlanSound3APS:hull_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS4atopC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib2AS=AsanPlanSound3APS2uEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS6in_ivsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7am_kindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS8amap_denC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2AS8AsanPlan2AP7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6am_lenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC69OSSVerify5KrLib2AS=AsanPlanSound3APS9sum_sizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP5a_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7a_eagerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP8a_abytesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS8AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS3hidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS8in_ghostC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S:edenot_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS=regs_ok_set_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7a_ghostC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP3acs01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS=AsanPlanSound3APS5cs_ok01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI69OSSVerify5KrLib2AS8AsanPlan2AP4amap00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI69OSSVerify5KrLib2AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP:ENOMEM_RETC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX26sentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP5e_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4CEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6TOPMAXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS8AsanPlan2AP5mkind00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind02C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP3nxtC1?~~~~~~~~~~~~~~~".  (* [comment removed for export] *)
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Noacc.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma sstep_of_check_noacc : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "h03effh13evsh22m'h31ih41mh51Hh64Hacch72Hch82Hhh93Hh'h:4Hsvch;1lh<5modelh=2msh>2x8p;1p;3p;2p;4p;5p;6p;=p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9p1001ip4p70R0p1002Yp4p710R1p8P0p10035p4p710R2p8P0p1003Sp4p7210R3p8P0g0040R0p4p710R4p8p1004Np4p70R5P1p8P5P2p8P5P3p8P5P4p8P5p1005<p4p710p8p1005Yp4p7210R5P1p8P5P2p8P5P3p8P5P4p8p1006Ep4p70R5P1p8P5P2p8P5P3p8P5P4p8g007;j11Tg007`j1FTg008>j1=Tg008aj16Tg009Aj1:Tg009cj1CTg00:Zj1>Tg00;<j30Tg00;Vj1;Tg00<\j27Tg00=>j38Tg00>4j35Tg00?Aj24Tg00@Kj2ETg00@kj19Tg00B1j1DTg00BQj42Tg00CIj33Tg00DDj5BTg00EXj2?Tg00Faj1@TP0j6ATg00H0l=<Tg00Hdg00IkR0g00Ja#1#1#1#1#1#1#F#=R4g00KFR5g00LD#6R3%:4R2f4R1#C%>430R6f6R7#;1741502g00M:R2p,4segsR8f7R9f5R:38?517f3R;f2R<'430g00ND,E4R4#6R=%97%D4R430P8f:R>f9R?f8R@P9P7P7P:P1P;g00NcRAg00O`A51;<f1RBf0RC'4502P5P1P<PBC293:;[RDP5P;PBPCC2931<A5:1;14<B502R2[P5P:P;P<C29371\2P1P;P<PBPCDBPBn2001000000120000000X13X20X40X05W3PD^13^20^40^05^3APCf;=88?P@P>P9P7P;O6b5PBP=P4%:01?9C170930X;=%@7%99PCEAM=<W6X96W7W:W8W1X20W0W>W<W=o"). Qed.

Lemma sstep_cfg_of_check_noacc : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff ->
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep_cfg segs ACFG (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hacc.
  apply (sstep_cfg_syscall segs ACFG ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hns.
  - exact Hh'.
  - rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

Lemma node_chk_ev_gen_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hnf Hinv Hnu Hnh Hacc. split.
  - intros i. apply (sstep_cfg_of_check_noacc ms model x8); auto. exact (Hnh _ _ _ (Hok i)).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv_chk segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hmat. injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hmat. discriminate.
    + rewrite (Hnh _ _ _ Hc) in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hacc Hns.
  apply (node_chk_ev_gen_noacc ms model x8 I effs ms' evs Hh Hsvc Hok Hns); auto.
  intros eff m' ev Hc. destruct (Hinv _ _ _ Hc) as (i & _ & -> & _). apply Hh'.
Qed.

Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hacc Hns.
  apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hacc.
  assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
            exists i : unit, eff = (fun _ => eff0) i /\ m' = (fun _ => m0) i /\ ev = (fun _ => evs0) i).
  { intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto. }
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - exact Hinv.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hacc.
  - apply (uniform_not_spurious segs ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
             (refusal_b (sys_input segs ms x8) model (eff_ret eff0)) Hinv).
    intros []. reflexivity.
Qed.

Lemma rz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply rz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes segs (nx i) (T i)) ->
  srealizes segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (srz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (srz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma with_vm_backing_halted : forall l p m, m_halted (with_vm_backing l p m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "h01lh11mh21pp;1p;2g007;j10Tg007`j17Tg008>j13Tg00@Kj22Tg008aj11Tg009Aj16Tg009cj15Tg00W;j24Tg00Ja#0#0#0#0#0#0#7#3R0/20#1%10g00Ik%60f0#5'4W1W2W0o"). Qed.

Lemma vm_add_lazy_halted : forall a n m, m_halted (vm_add_lazy a n m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "h01ah11mh21np;1p;2g007;j10Tg007`j15Tg008>j12Tg009Aj11Tg009cj14Tg00W;j23Tg00Ja#0#0#0#0#0#0#5#2R0g00Ik%10f0#4'3W1X20W0o"). Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "p'0h01ah11bi001bh25flagsh31mh41np;1p;3p;2p;4g007;j10Tg007`j19Tg008>j14Tg017Cj13Tg009Aj18Tg018Hj37Tg009cj11Tg00;<j32Tg00W;j25Tg019Bj46Tg00Ja#0#0#0#0#0#0#9#4R0g00IkR1f3R2#3g00iVR3P3%80R4P3P1f0R1f4f2R3772P3n0100000020000#1%1332P1f1R5#1,54R6P6n0110000020000b1P2P3P5P1C6#1%11524eW3X40X00W2o"). Qed.

Lemma with_mmap_replacement_halted : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement. rewrite with_mmap_backing_halted.
  apply vm_forget_range_halted.
Qed.

Lemma with_mmap_destroyed_halted : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "h01ah11hh21mh31nh41op;1p;2p;3p;6p;4g007;j10Tg007`j1=Tg008>j16Tg009Aj14Tg01Bej2<Tg009cj11Tg00;<j33Tg01C_j25Tg01=Aj22Tg01=kj27Tg01>Hj38Tg01?Fj39Tg0040j6:Tg01Dbj4;Tg00Ja#0#0#0#0#0#0#=R0#6R1g01Ejg00Ik%41R2f1R3f0R4'<R5#1%139324X421534f3R6,20R7f2R8,20,77R0;85#1A9705E:P6P8P3P4C;#1%14532eW2W1X31W0o"). Qed.

Lemma forget_vm_ranges_halted : forall ranges m,
  m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "p'0h01mh16rangesh22IHh31ah42a0h51lh61nh71oh81ri001bi011pp;1p;2p;3p;6p;4p;5g007;j11Tg007`j1ATg008>j18Tg00@KR0j26Tg008aj1@Tg009Aj1:Tg01Faj23Tg009cj10Tg00;<j32Tg00W;j27Tg00^7j34Tg01=Aj25Tg01=kj29Tg01>Hj3?Tg01?Fj3>Tg0040j6;Tg01Gfj4<Tg01HFj5=Tg00Ja#1#1#1#1#1#1#AR1#8R2/62R3#@R4P3g00IkR5%:2R6f1R7f0R8'3#0%08R932]0R:X141769X05P0P2P2f3R0f2R;543/38#0=269^05\:^54P8P6f4R<,51R=1510,9=R1;?8R>#0%079268X76A>=1813;>#0P7P>O1E;P2P2P<P0C<=43;/38#0=269eX05X2:X84X62X32P7P8O2n2001101000121100100X43P8D=W1o"). Qed.

Lemma brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "h01mh11oh21rh33reqp;1p;3p;2p;6g007;j10Tg007`j1?Tg008>j14Tg009Aj13Tg01Hhj1>Tg01I_j3:Tg01Bej25Tg009cj11Tg00;<j32Tg01C_j26Tg01Jbj17Tg01KWj28Tg01Faj29Tg01LVj2=Tg0040j6<Tg01Mcj3;Tg00Ja#0#0#0#0#0#0#?#4R0g00Ik%30R1f0R2#>R3f2R4f1R53:R6/52R7#1%159212X111662%73,85R3/97#1R61=37E<%12R39216eA;452#1=213eW0X20W3o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "p'0h06Hecallh16Hfetchh21bh33memh41oh52pch64regsh73romh81wi001wi011ci021ii033iszi042m'i051pi066reporti073st'i081xp;1p;2p;3p;5p;8p;6g007;j13Tg01N]j1NTg007`j15Tg008>j1<Tg005Yj2gTg009AR0j1HTg01OBj2=Tg00<\j26Tg00;<j30Tg01PDj1ETg01QDj1DTg01RKR1j1QTg01SSj54Tg01THj38Tg01UTj1>Tg01VRj3KTg01WWj3ITg01X]j3MTg00B1j1WTg01Ybj21Tg01Zjj1VTg01\2j1STg01]:j1RTg01]Xj3GTg01^;j2;Tg01_0j5?Tg01_hj1@Tg01`gj1BTg01agj1ATg01bhj2JTg01cfj17Tg01dej1CTg01edj1:Tg01fbj89Tg00@KR2j2FTg01gij1PTg01hZj2OTg01i@j5TTg01iij3UTg01jPj3fTg01k[j2eTg01l_j1dTg01mHj1`Tg01n2j1_Tg00:Zj1^Tg01nYj1]Tg01oBj1\Tg01okj2[Tg0212j1ZTg00W;j2YTg0040j6LTg021kj1XTg022hj2aTg023mj2bTg024Pj3cTg00HdR3f1R4f0R53cp=2g00Ja#3R6#N#5R7%36#3R6#3#3R8#3#5R9#<R:'g%56#<#H\:R;%58#<R8%H8R<p,4segsR=f3R>'=168530g00iVR?%E4g025WR@30P<f2RA,68%D3RB#QRCP0P8PCP5g0267RDf8REf7RFf6RGf5RHD4=8=5RIP0P8PCPDPFPGPHf4RJD4RK#>RL=K=GPIP0P8PCAI=LGPIP1P3PCAM=LGg027;#WRI,25,1BRM%VBRN%SBROn1011080003101070000n10110800021010000n10110800021010000n10110800021010000PFPGPHPJ%N6#RR6g00bFRP5G7RQ,;FD?/2I,1BRR30X4<P?P@P?PCP5%@K%BK%AK1JKQ,6:%7K%CKPL%:KG9/2I,1BP0g028@RLg028lR@'FPC%P>P2PLP@PCP5P1g029JR@/F;RL#DPC1O95PDf:R9f9PEPFD4RF#@%BF%AF%CF%7FDT7U4%>F5f=P2P@P;PC1eL5%d4%`4%_4%^:%]4%\4P5PDf=f<f;P9D4#:G91[LA'2,1Bn2001108000120101104PNPOn1011080003101060000n2001105000120102103P?PC%Z>PNPOn0100000020000n10110800021110500n0100000020001=0CRX2?PGPHPJP>1;GQD?/2I,1BR?,YCPDPGPHPJP>D4RD#@%BD%AD1JDQ,6:%7D%CD%>DRQ%:DG9/2I,1B=0C?e%EAP5ELA8=DA=0C?RAePAe1==HP4ELP0P8PC%XDR4,==A8=K5RKP0P8PCAK=Q4PKP0P8PCAI=Q4PKP1P3PCAM=Q4PMPNPOn1011080003101070000n10110800021010000n10110800021010000n10110800021010000=0C?e1a=DPGPHPJP>PP1b76d9G76,;GD?/2I,1B50CeW0W1W8X7;W3X5:W6o"). Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  apply node_ok_of_pnode; [apply transparent_instr; exact Hsvc |].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

Lemma rz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply rz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma epend_len : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "h04__x1h12Hch27__arithh37__sat12h47__sat13h52Hah64__ffh74__p1h84__p2h98__varmaph:5__with;3H11h<4Hlenh=1bh>3lenh?3memh@2pchA4regshB3romhC1zp;1p;2p;3p;4p;6p;5p;7p;8g007;j12Tg01N]j1>Tg007`j1=Tg008>j1CTg005Yj2dTg009Aj1XTg01]:j18Tg023mj2OTg01]Xj3;Tg01^;j2<Tg01hZj23Tg00;<j30Tg02E3j21Tg02EOj2cTg00O`j24Tg01=Aj25j1STg00Q<j1DTg02Elj2VTg02FTj29Tg02G0j3UTg00B1j1TTg008aj1RTg02GTj2NTg02H2j1MTg02HPj1LTg02I;j2@Tg02I^j2KTg02JAj46Tg02Jlj3JTg00:Zj1ITg02KOj2HTg00W;j2GTg02L1j2PTg02L]j3QTg02M<j4FTg02Mnj2ATg003Sj6bTg002Yj6aTg00WUj4]Tg0040j6BTg01_0j5\Tg02Nfj1YTg02OEj2ZTg02PCj5[Tg02QCj7WTg02Qgj7^Tg02RKj8_Tg02Roj6`Tf1R0g02SSR1g00hVR2P2g02T2R3f0R4g00i6FWp=7f2R5P1P2P2P3P0P4F^p=?f3R6P1P2P2P3P5P0P4G_p=:P0P1P2P2P3P4E`p=Eg00JaR1#2R7#>R8#=R9%27#2R:#2#2#2R;#=R<#CR='d%=:#C#X\=R>g028lR?f4R@%>8#8R8g00bFRA1O98d5;9'<13<450=g02TRRB/10RC%87R7%8;R;'cRD,10RE'4P=f6RFA;98A'<R815<4=0?613<BRG90=4#D'4X==RHP=13<5RIPH15<I=0?5A0=IGRI#DRH1V7;RJ11B719B;11BD[[RK19B7RLg00aMRMAU7;0UW5R;19BD\M^5LRLg02U0RM#TRN%RMRM1N?0RO%M?RP%L?RQP?1@?BRRg02U\RS1K?1R1C6,7QRTP?P1PS1@?7=J?<C6,7QR75?Q%I2R2P?PRg02VCP1C6,7Q=?Q7C:1HQ3R3P4P5g00iVR7g025WRS'G1P45=07SdAQ?B0CFRSb6b9b:X0?R711B4114D'419B0/4E[^0?REP4f5RUP6O2b2b3b4,A5P=P?%S<13<6RVPGP4Eb15<V15<GRG50?P?13<@,5<A0?4GXC?P4P@PJPKP;PLP7PEP4f7PUO2b2b3b4,A@EaA0?@GPJPKP;PLp-0RLPNPMPOPPPQP?P1g02VjPRC6,7QP2PQ1EQ69?QTP21EQ@C:C:P3PSb6b9b:X0?X7LW8A0?4B14C5P@[[^0?^7L^8LP4g00aif8R4/1DP4P6PFO5b2b3b4b1b1X1IPHeC]P8P0EBPFPUP@P6%>:#8=;9A,<FRAD\g02WQ#Y'ZPFPUP@P6PAD[EBW<W;W>XB>W?X@=WAo"). Qed.

(* [comment removed for export] *)

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->  (* [comment removed for export] *)
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  pose proof (fun eff => eq_trans (munmap_check segs ms (getr regs 17) model eff Hno) (munmap_check_modeled ms model eff Hargs)) as Hchk.
  rewrite H0, Hpr in Hchk.
  eapply (srz_det_noacc ms model (getr regs 17)
            (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
            (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model));
    [exact Hh | reflexivity | | | | reflexivity |].
  - intros eff m' evs. split.
    + intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb us [(a, Z_to_bv 64 (page_round_up_Z len))]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck. injection Hck as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
    + intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
  - rewrite munmap_model_halted. exact Hh.
  - unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma node_brk_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs (mkCfg ms model)
    {r : word | brk_adm model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno.
  apply (node_chk_ev_gen_noacc ms model x8 {r : word | brk_adm model (ms_gpr ms 0) r}
           (fun i => mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) (fun _ => []) Hh Hsvc).
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply check_syscall_ok_iff.
    exact (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros [r Hr]. cbn [proj1_sig]. apply (brk_adm_nonspurious segs ms x8 model _ Hno). exact Hr.
  - intros eff m' evs Hc Hns. apply check_syscall_ok_iff in Hc.
    pose proof (brk_nonspurious_adm segs ms x8 model eff Hno
                  (proj1 (proj2 (proj2 (proj1 (brk_ok_iff segs ms x8 model eff m' evs Hno) Hc)))) Hns) as Hadm.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & _ & ->).
    exists (exist _ (eff_ret eff) Hadm). cbn [proj1_sig]. rewrite <- Heff. repeat split; reflexivity.
  - intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
    exact (proj1 (check_syscall_err_iff _ _ _) Hc).
  - intros eff m' evs Hc. apply check_syscall_ok_iff in Hc.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (_ & _ & _ & ->).
    rewrite brk_model_halted. exact Hh.
  - intros [r Hr]. reflexivity.
Qed.

Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_adm model (ms_gpr ms 0) (vm_brk (m_vmmaps model))).
  { apply brk_adm_of_unique; [apply Hcases; reflexivity | intros r' Hr'; apply Hcases; exact Hr']. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_adm model (ms_gpr ms 0) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
  eapply srz_cases; [exact (exist _ _ Hq) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig].
  pose proof (proj1 (Hcases r) (proj1 Hr)) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  assert (Href : forall r, brk_refusal_b model (ms_gpr ms 0) r = bv_eqb r b).
  { intros r. rewrite H0. apply brk_refusal_b_move; [exact Hreq0 | rewrite Hureq; exact Hs | exact Hneq]. }
  assert (Hadmc : forall r, brk_adm model (ms_gpr ms 0) r <-> r = req).
  { intros r. split.
    - intros [Hr Hf]. destruct (proj1 (Hcases r) Hr) as [-> | [-> _]]; [|reflexivity].
      exfalso. pose proof (Hf ltac:(rewrite Href; apply bv_eqb_refl) req Hgrow) as E.
      rewrite Href, (bv_eqb_neq _ _ Hneq) in E. discriminate.
    - intros ->. split; [exact Hgrow|]. intros E. rewrite Href, (bv_eqb_neq _ _ Hneq) in E. discriminate. }
  assert (Hr0 : brk_adm model (ms_gpr ms 0) req) by (apply Hadmc; reflexivity).
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_adm model (ms_gpr ms 0) r} => KB)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hr0); exact Ht]].
  eapply srz_cases; [exact (exist _ req Hr0) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hadmc r) Hr) as Er. subst r.
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Lemma srz_brk_grow_lazy_same : forall regs (pc : word) mem rom model w (d : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w d K HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HA HB.
  exact (srz_brk_grow_lazy regs pc mem rom model w d K HF HE Hh H17 Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB).
Qed.

Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_adm model (ms_gpr ms 0) b).
  { apply brk_adm_of_unique; [apply Hcases; reflexivity | intros r' Hr'; apply Hcases; exact Hr']. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_adm model (ms_gpr ms 0) r} => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
  eapply srz_cases; [exact (exist _ b Hkeep) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) (proj1 Hr)) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma node_set_tid_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
                    (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 segs ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  apply (node_chk_noacc ms model x8 tid_I
           (fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
           (fun i => with_tid (proj1_sig i) model) Hh Hsvc).
  - intros [t [Ht1 Ht2]]. cbn [proj1_sig]. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool eqn:Eb; [|discriminate].
    apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
  - intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool; discriminate.
  - intros [t Ht]. cbn [proj1_sig]. rewrite with_tid_halted. exact Hh.
  - intros [t Ht]. reflexivity.
  - intros i. apply (acfg_nonspurious_no segs ms x8 96 model _ Hno). reflexivity.
Qed.

Lemma srz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig].
  change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
  rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma srz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "p'0h01bi001bh12Hch25flagsh34proth41zp;1p;3p;2p;4p;6g007;j12Tg007`j1HTg008>j1DTg04XRj1<Tg01N]j1ATg01]:j1?Tg00;<j35Tg01=Aj26Tg01=kj2:Tg04YVj21Tg01hZj2=Tg02hij1BTg00O`j20Tg00W;j2>Tg00WUj48Tg0040j6GTg04Z3j3FTg04[6j3ETg04\:j3@Tg04]Dj3CTg02mhj27Tg00iVR0f2R1f1R2'7f0R3'7g03MoR435p=31712/73p=9g025WR59503p=4A5034p=;g00JaR6#2#2#2#2#2#2#HR7#DR8g028lR9%<2%A6R6#2#2#A#2#?R:35P9P:1671R;g04^Hg04_C':R<'1g04`?g04a<':R=,13R>g02TR,=7R?#BR@33g04b;RA,1;?3>@167?/1AR>g04c6,:=R;,13RB;9@#4%?6,=7R6,67RC/1ARD?3B@11C<RC?9B@#4'0'0'0'0X491672R7/1<R<11:=R=;3@117AR7?3=@RA11:;R;=9>@#4R>A3D;@RDA9C;@#4R;'0RC'0R:'0P<P0P0A33=@P31>04R<A35=@dP<A34=@dn0110000020000R=b0PAP:P7P0P=b0P>PC1>05R5PDP;P<P5C8C8C8C8%<1P3EGAF21?#;AE21?#;A@?1?#4A@61?#;AC61?#4'0'0'0'0eW1X38W2o"). Qed.

Lemma srz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs c three (fun _ => []) nx ->
  srealizes segs (nx T1) A -> srealizes segs (nx T2) B -> srealizes segs (nx T3) C ->
  srealizes segs c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (srz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (srz_cases c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
  if Z.eqb prot 0
  then mkVmMapsFull (vm_reserved h) (vm_maps h)
         ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  else mmap_fixed_rw_next h addr n.

Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    (maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.

(* [comment removed for export] *)
Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
  if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "p'0h01ah11bi001bh25flagsh31mh41np;1p;2p;3p;4g007;j10Tg007`j1ATg008>j1;Tg017Cj14Tg009Aj1@Tg038Hj1<Tg01=Aj22Tg01=kj2:Tg032<j35Tg039@j26Tg03:Aj17Tg03;Aj38Tg04hHj39Tg018Hj3?Tg009cj11Tg00;<j33Tg00W;j2=Tg01A[j4>Tg00Ja#0#0#0#0#0#0#AR0#;R1g00IkR2f3R3#4g00iVR4P4%@1R5P4P2f0R2f4R4f2R6#<1204R41203,:4R0351640%76581;96R07?3P0n0100000020000#1%1633P2f1R0#1,=5R4P4n0110001020000b1P3P6P0P2C>#1%12535eW3X41X01W2o"). Qed.
Lemma with_mmap_destroyed_halted' : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["Noacc"] "h01ah11hh21mh31np;1p;2g007;j10Tg007`j15Tg008>j12Tg009Aj11Tg009cj14Tg00W;j23Tg00Ja#0#0#0#0#0#0#5#2R0g01Ejg00Ik%10f0#4'3W2W1X30W0o"). Qed.

(* [comment removed for export] *)
Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs us [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs, us with
             | [], [] => CheckOk model []
             | [], _ => if listNN_eqb us [(addr, n)]
                        then CheckOk (fixedin_destroyed_model addr n model) []
                        else CheckReject
             | _, _ => CheckReject
             end
        else if (Z.eqb prot 0)
             then match zs with
                  | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
             else match us with
                  | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc Hbud.
  pose proof (alloc_top_lt (m_vmmaps model)) as Hcv. unfold two_pow_64 in Hcv.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
  pose proof (u64_range addr) as Har.
  destruct Hprot as [-> | ->].
  -
    rewrite G3. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct zs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
    reflexivity.
  -
    rewrite G4, G5. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    rewrite (Hbud eq_refl).
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (alloc_top_lt (m_vmmaps model)) as Hcv. unfold two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Htop Hrf Hmc Hbud) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof (alloc_top_room (m_vmmaps model)) as Hroom.
    unfold two_pow_64, stack_max_size in *. pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  pose (effs := fun _ : unit => fixedin_ok_eff prot addr n).
  pose (ms' := fun _ : unit => fixedin_ok_model prot flags addr n model).
  assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (fixedin_ok_eff prot addr n) model
                 = CheckOk (fixedin_ok_model prot flags addr n model) []).
  { unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk, Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity. }
  assert (HretS : eff_ret (fixedin_ok_eff prot addr n) = addr) by (unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity).
  assert (Hrb : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = errno_ret_in mmap_errnos r).
  { intros r. apply refusal_b_mmap_sys. exact Hno. }
  assert (HB0 : KB []) by (eapply srealizes_nonempty; exact HB).
  apply (srz_conseq segs (mkCfg ms model) (t_alt (fun i : unit => t_emit [] KB))).
  2:{ intro tr. split; [intros [i Hi]; exact (proj1 (t_emit_nil_eq KB HB0 tr) Hi) | intros H; exists tt; exact (proj2 (t_emit_nil_eq KB HB0 tr) H)]. }
  apply (srz_node segs (mkCfg ms model) unit (fun _ => []) (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))
           (fun _ => KB) tt).
  - apply (node_chk_ev_gen_noacc ms model (getr regs 17) unit effs ms' (fun _ => []) Hh eq_refl).
    + intros []. exact HokS.
    + intros []. apply spurious_refusal_not_refusal. cbv delta [effs] beta. rewrite HretS, Hrb. exact Haddr_ne.
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (mm_refusal_spurious segs ms (getr regs 17) model _ _ _ _ (or_introl Hno) HokS).
        -- rewrite HretS, Hrb. exact Haddr_ne.
        -- cbn [eff_ret]. rewrite Hrb. exact Er.
      * rewrite Hchk in Hc. rewrite Er in Hc.
        destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (Z.eqb prot 0) eqn:Ep.
        -- destruct zs; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists tt. cbv delta [effs ms'] beta. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
        -- destruct us; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists tt. cbv delta [effs ms'] beta. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r).
      * destruct zs; [|discriminate]. destruct us.
        -- injection Hc as <- <-. exact Hh.
        -- destruct (listNN_eqb _ _); [|discriminate]. injection Hc as <- <-.
           unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. cbn. exact Hh.
      * destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
          (destruct (bv_eqb r addr && listNN_eqb _ _)%bool; [|discriminate]); injection Hc as <- <-;
          unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh.
    + intros []; cbv delta [effs] beta; unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity.
  - intros []. cbv delta [effs ms'] beta. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.

End Noacc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Import AX2 AX2S AP APS.

(* [comment removed for export] *)
Lemma is_ecall_at_sound : forall SEGS cs,
  is_ecall_at SEGS cs = true ->
  0 <= pc cs /\ pc cs + 4 < two64 /\
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) [] "p'0h01Hh11wi001wh22Hfh32Hwh41mh51nh62H0h72H4h84SEGSh92csh:1eh;1oi011oi021bi031xp;1p;2p;3p;4p;6g008aj1QTg05gfj2PTg05hej11Tg007;j19Tg01]:j1MTg01=kj24Tg02mhj2@Tg007`j1CTg008>j1ETg01PDj1ATg05i[j3DTg00O`R0j22Tg02FTj27Tg02E3j26Tg009AR1j1OTg00<\j2?Tg00;<j33Tg00T6j2;Tg0569j2>Tg05;`j2JTg03]0j2<Tg040<j2ITg00W;j2BTg00WUj4=Tg00X0j4HTg00:Zj1KTg002Yj6LTg00Z7j2GTg01hZj2FTg01OBj2NTg00iVR2f0R3g025WR433p=0g02TRR5/>3p=:g05j>R6,<3p=8f2R7f1R8/F3'Np=5g05k:#Qg05l91P83#0%18R9#:g00Ja#9#9R:#MR;,49#8'@R<P1%9:#9#9R:#C#ER=P2%9:#CR:=579%A3R9g03MoR>n10110300021010000R?;D3%0<%0?'2P0%17R?#:14?;#8'@#0P1P=P2f3R<?5:?P9P>n10110300021010000#0%1<R?,7514?;/66%O=R?f5R@f4#1RA75:1?=3RB33%09RC'2X1=,;='2'2P3%:A14A;#8'@#0P1P=P2f6RA%1@75:P9P>n10110300021010000#0%1AR@#:RD14@;#8R@;D8%0D%0@'2P0f7#1R@#:#014@;#8#0f8R@#1RD,7514D;/66f:RDf9#1RE75:=3?B/2CX1=,;='2'2P3%:E#0%1D/4;#8#0g028lRDP01>83#01778[RE17831>78#0RF[17<7\F1J83P8n2001000000120000000X4DW5PE^4D^5DP3P5f<#1REP7O3175EP01<83#01678[R016831<78#0RE[16<7\E1I83P8n2001000000120000000X4DX5DP0^4D^5DP3f>#1/4;RDP6P<O316D6f@RDf?#175:P?1B?3fAR0%1D75:=3?3P1P=fCRDfBRE#175:=3?3P1P=P2P8P9P>n10110300021010000#0fDR9#1R1,75RF141;/66R1A3?<B/2CX1=,;='2'2]2]3P8%1D959:=3?B%A8#0fE#1R9,75149;/66R61?=<=3?B/2CX1=R<,;=R9'2P@P6P9PAP=P<P71?=7R<=3?<%A7#01B?<P3C=CHC=C=W2W3X1=P3O1%1095E:%K=RE53?A32>4P2P>P2p-0P3g00aiR>g00aMn0110200020000X:2g00bFP4P3ELP>A3?EB/2CX1=,;=,21,2F/G3b0W2W3n10110100021110200P3f;O2b3b;b7b0b6b0W7W6P8P3O2n2001000000121000000b0W2W0P8P3O2n2001000000121000000b0W0W9W8o"). Qed.

Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
  bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) [] "h07__arithh14__ffh28__varmaph35__with42Hah56__sat1h66__sat2h74__x1h81zh91Hh:6__sat3h;6__sat4h<2b1h=2b2h>1nh?2Hch@6__sat5hA2c0p;1p;3p;2p;4p;6p;7p;8g008>j19Tg00;<j3:Tg01=Aj21Tg05m2j3[Tg007;j16Tg007`j1ETg01hZj25Tg01N]j14Tg01]:j1;Tg04UDj3KTg05mVj28Tg02EOj2HTg03H8j2BTg02Elj2GTg02E3j2>Tg02G0j3FTg00B1j1ZTg008aj1YTg02cGj1XTg02H2j1WTg02HPj1VTg02I;j2<Tg02Jlj3DTg02KOj2UTg00W;j2TTg02L1j2RTg02L]j3NTg02M<j4MTg05n4j3OTg02^:j2LTg02GTj2PTg02I^j2QTg00:Zj1STg02Mnj2CTg03m:j4dTg05n[j1cTg05o9j3bTg0040j6=Tg05o\j3aTg02FTj2`Tg00O`R0j2_Tg02JAj4ITg02QCj7^Tg02Qgj7]Tg02RKj8\Tg02TRR1f0R2'`p=0f2R3f1R4/>2'_p=2g028lR5?:42p=7P5P4g02U\P2CIp=?P4g02SSR6g00hVR7P7g02T2R8P2g00i6F^p=3P5P4g02VCP2CIp=@P3P6P7P7P8P4P2F]p=Af3R9P6P7P7P8P3P4P2G\p=J%02R6g05j>722g060JR:%92R;%94R<P0%93?:4211931194'7R0[11341132'7%99?:34[R=f4R>#9?:93\0A[342P2n2001000000120000000W=W<W>P=^=<^<;^>:P2g00JaR:#6R;#6#6R<#6#6#6R=#ER01503R?%4:#4#4#4#4#4#4#;R@,50RA5K0RB183@,50P5110?RC110ARD'8189@,50,10RE,72X85P5P3182D/7EX85P5P@1892/7EX85P5%;;R;%;<RE'HR9,B3RF1502,10,72X85P5150F,10PF1G;ERG1>1;RH%0ERI1>19RJ[[RK%0;RLg00aMRMAF;E4UW4RN%09RO\M^4LRP%;=R=,G;RQ%0=1H;=RR,>1[\HRHAF;=4VMX4LR=%0R\M^4LRLg02U0RM#ZRS%YMRM%X5RT%W5RU%V5RV1<51RW1<5;R;%E<5D5R<'?'31UV8R8P2P3g00iVRXg025WRY'T1R23=:XYdAN514CMR1b1b2b3PJP2b0b5b6b:b;9O39%0FRJ?2F9PGPKPNPPf5RP/L9%0Pf7/B9#0\O[PQPHP=PLPSPM1P54ROPUPV1Q5:R:,@W,3VRN1?:<,3V5AV%S7R7AD5;0R;,?:,3V9AVNRNCJP8P1b1b2b3X75A2629%04?24RR4[^75P2f9/B9f6O2b0b5b6b:b;b@b9A2JFRe,CFCd%cE,83PSPMPTPU1<5E,@W,3VP8P1b1b2b3PIP2b09b3EE=PDPQPHP=PLPSPMPTPU1<5@RT,@W,3V1?T;,3V5AVP8P1b1b2b3%0@?2@RRTP2b0b5b6PTe,C@E=PCPQPHP=PLPSPMPOPUPVPNP7PNCJP8P1b1b2b3X75A262RP4[^75P2PPP>O2b0b5b6%03?23Re,C3E=110BAa0?AE=O4b9W?XA5o"). Qed.

Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) [] "p'0h01Hh11Th21ah31bh41ti001op;1p;2p;3p;6p200R0g003SR1p4p710p8P0P1p4p7210p8g009AR2j11Tg00<\j20Tg00;<j33TP1j62Tf0R1f1R3f2R4#11043104133f3R5#1R6P5P2f4f5P1P1P5n10110000021000000X4610541053P1E2W0W3W2X10o"). Qed.

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < two64 ->
  v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) [] "h02Hah14__x1h22H0h32H4h47__arithh54__ffh66__sat5h76__sat6h88__varmaph95__with:1ph;1zp;1p;2p;3p;4p;7p;6p;8g007;j10Tg01]:j15Tg01=kj22Tg02E3j23Tg007`j1OTg008>j1GTg01hZj1Cj2:Tg01=Aj2@Tg00W;j27Tg00;<j34Tg02Elj2<Tg02EOj2XTg02G0j3VTg00B1j1UTg008aj1NTg02GTj2LTg02H2j1KTg02HPj1FTg02I^j2ETg02I;j26Tg02dCj3BTg02Jlj3DTg02JAj48Tg00:Zj1ATg02Qgj7HTg02KOj2ITg02L1j2JTg02L]j3?Tg02M<j4>Tg00O`j2MTg02Mnj2=Tg0040j6PTg060hj8QTg02[Qj2RTg02FTj2STg02QCj7TTg02RKj8WTg02TRR0f0R1'Sp=1f1R2g02SSR3g00hVR4P4g02T2R5P1g00i6FTp=9f3R6P3P4P4P5f2R7P2P1GWp=;g028lR8%11g00JaR9#0R:#0R;#5R<,22g05j>'3P8%0;#0#0#0R;#OR=#GR>%C=R?P?1:=7R@,@=RA/2<RB127<RCP>\8/7?P8P7121<R?126<548X;8178CPA%5:R:%5;R;'<130:%1;1X:;RA,30[[%1:RDg00aMREAV:;2UW0%1A\E^0Dg02U0RD#U%ND1L82%K8%F8RDP81E89R9168<5B8g02U\RE168:=D8=R:C8,9D%A4R;PDP81680g02VCP9C8,9DRFP;PDP3P4P4P5PFP8P9PEP:C8,9DFHC;C;1ID5P1P7g00iVRDg025WR5'71J17=4D5dA?802C>b5b8b9X1813?A%12%17137A'M[[^18P1f5P6f4O3b4b6b7,=7EPA48BCeGQ1R@<1:=C54>eW3W2W:o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CsOk.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Lemma cs_ok_refuse : forall E cs R FULL model,
  cs_ok E cs R FULL model ->
  cs_ok E (refuse cs) (regupd R 10 (Z_to_bv 64 ENOMEM_RET)) FULL model.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["CsOk"] "p'0h01ah12ivh21mh31zh41Eh54FULLh62HAh72HCh83HMrh91Rh:7__arithh;4__ffh<8__varmaph=5__with>1bh?:co_abytes0h@:co_bounds0hA7co_brk0hB9co_eager0hC7co_fds0hD6co_fs0hE8co_halt0hF9co_holes0hG9co_kinds0hH8co_know0hI9co_lazyb0hJ9co_limit0hK7co_log0hL8co_maps0hM8co_minv0hN9co_napos0hO9co_nasub0hP8co_none0hQ8co_regs0hR7co_res0hS8co_sbrk0hT8co_seps0hU8co_sinv0hV6co_sp1hW7co_tid0hX7co_top0hY9co_totsz0hZ6co_wf0h[8co_zero0h\2csh]5modeli009co_abytesi019co_boundsi026co_brki038co_eageri046co_fdsi055co_fsi067co_halti078co_holesi088co_kindsi097co_knowi0:8co_lazybi0;8co_limiti0<6co_logi0=7co_mapsi0>7co_minvi0?8co_naposi0@8co_nasubi0A7co_nonei0B7co_regsi0C6co_resi0D7co_sbrki0E7co_sepsi0F7co_sinvi0G6co_sp0i0H6co_tidi0I6co_topi0J8co_totszi0K5co_wfi0L7co_zerop%0p&0p;1p;2p;;p;6p;3p;4p;7p;9p;Xp;<g007;j1ETg01N]k10YTg007`j1cTg008>k10:Tg005Yk20WTg009Ak103Tg061ER0m;01Tg062Fj6VTg00W;j2ITg063Bj1MTg00;<j30Tg00@Kj2pTg008aj1[Tg064<j3STg01]:j1XTg01]Xk30VTg01hZk206Tg02ZZk305Tg065<j17Tg0664j1;Tg0671j3eTg0685j1dTg00B1j1~Tg0691j1aTg069gj4`Tg009cj1yTg00:Zj1xTg06:kj1?Tg06;cj3hTg02>Lj1uTg06<cj1BTg04<Fj1rTg01Hhj13Tg02oOj1ZTg06=_k10>Tg0343j1qTg06>]j16Tg02Xnj1FTg06?Wj3oTg06@[j1>Tg005<j3nTg06ATj3kTg06BUk10;Tg06CUk109Tg06DXk30XTg01=Aj24Tg02E3R1j2QTg06E5k30UTg03H8k208Tg06ERk20TTg01=kj2GTg06FVj1iTg02FTj21Tg00O`j22Tg06GTj3KTg038Hj1WTg035ek104Tg06H5j2gTg031Bj1HTg06I1j28Tg06J1k10STg00Vak20RTg06Jlk202Tg06Knk300Tg06LEk10QTg06M@j2DTg06N=k10PTg06O7j1}Tg06Ooj2YTg06Plj1|Tg06Qoj1ATg01Jbj1_Tg06Rjj1@Tg0338j1{Tg06Scj1zTg06T^j1:Tg06UYj1bTg06VQj1=Tg06WMj2mTg06XDj6fTg06YAj3lTg00<\k20OTg06ZCk10NTg06[@R2j2vTg06[Xk60KTg02cGk10JTg02H2k10GTg02HPk10FTg02I;j2^Tg02JAj4tTg02Qgk70ETg02KOk20DTg02L1k20CTg02L]k30BTg02M<k40ATg06\Ak40@Tg06\lk20HTg0040k60?Tg06^3m90ITg05hej1jTg06_:j1\Tg06`5j3]Tg06a2j1OTg06aoj1UTg06blj6LTg06cnj1RTg06dgj1TTg06ebl;NTg06f[mX0=Tg02Nfj1PTg06g\m<07Tg02QCk70<Tf0R3#E#Ep=Cg00iVR4g03Mo703p=9g06hAR5f1R6;K3p=<g025WR79043p=5%P3#Pp=w%P3#P#P#Pp=Jg00NDR8g028lR9P2g06i;R:P1g06i[R;g02WQR<g02TRR=f3R>f2R?P6P3N<07p>0MP8P9P2P:P1P;f5R;f4R1P>P?P6P3N<07p>0LP6g02SSS00g00hVR:P:g02T2R2P3g00i6K0<p=sg06j=g05l9g00Ja#ER8$0YR@#cRA%E8R8#ERB#CRC#ERD#cRE$0:RF+0W%cBRB$0:RG$03RH\FRIg00Ikp,4SEGSRJp,1ARKp,5LIMITRLp,4SINVRMp,4argHRNp,3FS0ROP1P>P?P6P3N;01PKPNP;P1P6P?EVRP,IIPKPNP;%M1P6P?EV=0IP1p99#[RPf6RI=SK;RQ'I%M;9SKI=0PQP0PJPKPLPMPNPOf7R0PIP;P1P>PJPKPLPMPNPOf8RQ%M0%E@#XR@g00bF60VARAg06k9RP-06ERR605IP;P1N;01P?fTRSfSRT#7#;fRRU3eg06l7RV#[RW%7S#d%~VRV30PJfVRXPKPNPXfURXPUPTEV%aXC`&03FRU%yT%xFRT30fXRYfWRZ#?;hSg004NRS%uX;0OfYRX#B#9%rZ=0UT[1pFFR[#[R\%3Z#Z&0>JRZ30%3Y#q=09Lf]RYf\R]#6%3X#F3of^RX%>YfZ#3R^#Z%F^5n[3k%6Y'<f[#3#F$0;&09]B0XFF3,4ER],Q=R^B0UFF3,4ER_%CD#C#CRD#XR`+08=09=Ra208]`=09=R`1Q=_Rb20TK3Rc1G_]R_%iX'1'2'2'2'2'2X1[%3Y#F5K[f_RY#i,1_,2cX1[%WX5K[%3Y$04,4EfcRYg06m6RX'g509g06mo%ED#C#C#C#C#C#XRD'GR]fd/gXRd'1g06ng/GDRD,1d'2fb#3#HRd,83#5%3Y#F,86#5[^39P^X1[RY=K[dg06oaRd&0S3Reg070\30g071W90de+0RRffiRg0026fe#3Rh#H600[[X25ffRi#6'<g072R90deRefkRd&0Q?Rj'D,4ERk14E3Rl'1&0P?Rm,Dd,4E,Gk,Ql'214E6RkfhRn#3#H'8#9%}6Ro%Wn'Y#5'2[^0F[X25fgRp#6'<%Zh%Fh5n[#|%An'1%3i#_fjRi%@g'D50F%3pRp#{,4E%_p,4E'1%zn%:d'1fmRdflRn5SK#b%=n'1fnRp=SKd/miPKPNfpRifoRgPnP3Ef#5%3dRn#FRh,8k#514E?Rq%3p#HRr'8#9%}>Rs%Wg'Y#5ftRtfsRu14E1Rv3l#9frRwP;O1206B=-0OGRG50H[[[[[^0FPMPiPdO2PJPKPLPMPNPOfqRB%MiRxB05gARRAPpPdPB%7iRy#;RzPg%w<#J#JR{&0NPR|PRfLS011v<{S02%w{#J#J#J#J#JS03,v{R<'21Q=@R}%XCRC,Q@R~'2S04Q02P<P}P~1I9=P{P@1I9@R~H0MP{P@P~Q03PC1I9CJ0LJ0Kg02U0R~#~%[~&0J9&0G9&0F9R~Q00P:P:P2P91^9=g02U\R:1^9@R@Ct,s~P9P@P:1^9CCt,s~K0E20D~2P3P?1I4720C3?#5dB0B9=6H0Ab;b<b=Q04P3b:H0@PFPRA0F3RX>F1IFR1DB|20HBPJ0?N90I%ji%X8R8'G%\yA]z{|PV%Oy%Uyg073M#xRyEL%6i%Ai%>i%:i%Ri%Ti%=i%@i%?i%BiM;NRz#7RP#;PV%OP%UPPyEL%6z%Az%>z%:z%Rz%Tz%=z%@z%?z%BzM;NRz#7RP#;=eBAe%7xRR#;=eBAe1IWV%dP=0WVe%dR=0WVefJRWPJPBPKPNPBPzPdPpEV%azC`ePJPBPKPNPBPxPdPpEV%axC`efIRJ%yd=0UTRRePRefHRR%?z=hBde%?x=hBdefGRP%ud=0SORSePSefFRS%Bz#9%rp=0UTRT[e%Bx#9PT[efERT%ZnRU=0\ZRZePZefDRZ%qn=09LRLePLefCRL%6zR\=oBhe%6xRO=oBhefBRA%>zAn[UhRU5kB/<\e%>x=kBU/<OefAR=&0;hR7eP7ef@R7&09dR4eP4ef?R4%ip,1_,2cRc,2b,2`,2a,2^X1[=K[hRhePhef>RhPcX1[%Wd5K[RcePcef=Rc&04n,4E1gBXRX509R^eP^ef<R^11]X11XD'2RXePXef;RX183r#5%3gRg#FRr,86#5[^39R9eP9ef:R9%Hn9K[YRYePYef9RY202u6%Hg600[\fX25Rf/<\e1<fOePQ1Dtj,4ERj/1l1Dtm,4E,Gj,Ql'2%3B#H,8k#9%WBRl,Yo#5'2[^0F\eX25R5/<\e1<5OeP0%|URU%Az'1e%Ax,1UePI%_nRU%@z,DB50Fe%@x,DB90FUeP;%{n,4E14EU'1RUePUeP1%zdRU%:z'1e%:x,1UeP>ASKBzRU#b%=z'1eASKBxRz#b%=x'1eP?1mUde1mzdeP6PKPNPw%jB/G8%7BRz#\%;z?]{|PV%Oz%UzPyEL%6B%AB%>B%:B%RB%TB%=B%@B%?B%BBM;NRz#7Rd#;PV%Od%UdPyEL%6z%Az%>z%:z%Rz%Tz%=z%@z%?z%BzM;NPpP3Ef#518kr#5Rr%3i#H,8q#9Rq1Ysl#5RlfvRsfuRi#j/G8%7iR8#\%;8?]{|PV%O8%U8PyEL%6i%Ai%>i%:i%Ri%Ti%=i%@i%?i%BiM;NR8#7R|#;PV%O|%U|PyEL%68%A8%>8%:8%R8%T8%=8%@8%?8%B8M;N;lv#9PtP;O1=0HGRG[[[[[^0FePKPNPw%MBPpP3Ef#5%Mi=lsv#9PG[\l\q\r[^0FeP3PMPBPpO2RpePpeNX0=WUW[WMW?WBWSWAWYWGWPWNWOWVWXWIW@WZWTWFWLWJWRWWWDWCWEWHWKWQQ01fKPWPJPRPPPSPTPZPLPAP=P7P4PhPcP^PXP9PYPQP0PIP;P1P>P?P6P3OMn;0000000000010000001M110B10<10910610410510H10C10;10=10710E10K10110:10I10G10@10?10A10810J10210D10310010>10L10Fb6b8W7W]W5W9W\W4o"). Qed.

Lemma pc_refuse : forall cs, pc (refuse cs) = pc cs + 4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["CsOk"] "h02csp;1p;2g05hej14Tg007;j10Tg01]:j12Tg01=kj21Tg00W;j23Tg05l9g028lf0#4g00Ja#0#0#2'1'3W0o"). Qed.
Lemma nxt_refuse : forall cs, nxt (refuse cs) = nxt cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesLibE ()) ["CsOk"] "h02csp;1p;2g074Kj11Tg00W;j20Tg05l9g00NDf0#1'0W0o"). Qed.
End CsOk.
