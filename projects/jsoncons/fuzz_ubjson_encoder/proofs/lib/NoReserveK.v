(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the place_declined_b premise of the mmap decline; the read-only-backing form of the system-call steps; the Linux placement of mmap grants; munmap answering -ENOMEM; the model's access_ok checks; addresses and numbers; imports; new lemmas. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  SimInv ExitSim PropExec CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_NoReserveK () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSimNmaterialize_model_accesses_nilC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LazyFrameEaccesses_outside_lazyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LazyFrameSmaterialize_model_accesses_disjointC13~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Peano2le00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LazyFrameDaccess_outside_rangeC13~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List2InC46Stdlib5Lists4List9in_or_appc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKJaccesses_outside_lazy_inclC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKIaccess_outside_range_monoC13~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim7fd1chanC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=lazy_interiorc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKFmmap_args_ok_noreserveC13~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes4negbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec:bv_eqb_neqC13~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC47Corelib4Init9Datatypes4andbK47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;MAP_PRIVATEc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveK;grant_ok_nrC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses=iff_Reflexivec79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKBgrant_ok_nr_unpackC13~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_belowC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C4ELinuxProcessSemantics?LinuxProcessSem5StateBstack_max_size_valK46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKLmmap_args_ok_noreserve_gatesC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9mmap_specC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSimAsyscall_spec_mmapC13~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC47Corelib4Init9Datatypes3orbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_introC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapCcheck_mmap_sound_okC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementI6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim=page_round_upC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKDmmap_model_noreserveC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;bv_eqb_reflC13~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9u64_rangeC13~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFpage_round_up_Z_nonnegc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKBgrant_nr_not_errnoC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKFmmap_noreserve_b_flagsC13~~~C47Corelib4Init5Logic5proj1C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFcheck_mmap_complete_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedI47Corelib4Init5Logic2ex00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAerrno_ret_in_trueK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool;andb_true_rC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C46Stdlib4Bool4Bool<andb_false_rC46Stdlib4Bool4Bool<andb_false_lK47Corelib4Init5Logic4True01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapMcheck_mmap_complete_unmodeledK47Corelib4Init9Datatypes6option01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim>munmap_args_okC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim:munmap_effC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim=munmap_ok_invC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim<munmap_modelC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKJmaterialize_munmap_eff_nilC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemantics?LinuxProcessSem5State5event03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSimCmunmap_model_haltedC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_noneC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSimCmunmap_no_unmodeledC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8wr_indexC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7node_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgFnode_ok_of_pnode_sysnoC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim9munmap_okC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKEsstep_munmap_inv_lazyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg@injected_arm_215C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_nodeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveK@node_munmap_lazyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg;srz_silent1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim=write1_ok_invC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKLaccesses_outside_lazy_shrinkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKZmaterialize_syscall_effect_copyin_disjointC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSimMapply_effect_copyins_no_writeC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim;buf_modeledC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKMsstep_write_next_inv_disjointC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSimCwrite1_no_unmodeledC13~~~K47Corelib4Init6Specif3sig01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim;write1_ok_nC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKHsstep_write_inv_disjointC13~~~C47Corelib4Init6Specif9proj1_sigC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg?injected_arm_64C13~~~I47Corelib4Init6Specif3sig00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7wr_fullC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKDnode_write1_disjointC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_write_chC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveK:msteps_acc00C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveK:msteps_acc01C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveK:msteps_acc02C13~~~C46Stdlib5Lists4List9app_nil_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib5Lists4List9app_assocc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveK>msteps_acc_indC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKKaccesses_outside_lazy_app_lC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:NoReserveKKaccesses_outside_lazy_app_rC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgAsrz_step_disjointC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8realizes00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg@rz_step_disjointC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSim7to_spin00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LazyFrame@ts_step_disjointC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr08C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem5is_x0C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7fp_regsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6fp_csrC13~~~C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6b_npc4C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec=bv_eqb0_is_x0C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcI4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5instr09C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr0;C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0BC4ELinuxProcessSemantics5Riscv3Sem7mul_divI4ELinuxProcessSemantics5Riscv5Instr5mulop00K4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4btgtC13~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00K4ELinuxProcessSemantics5Riscv5Instr5instr01C56Stdlib6ZArith6BinInt1Z6shiftlC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_luiC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5b_luiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_auipcC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7b_auipcC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7is_x0_0C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8jalr_tgtC13~~~C45stdpp9bitvector;definitions6bv_notC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6b_jalrC13~~~C45stdpp9bitvector;definitions6bv_andK4ELinuxProcessSemantics5Riscv5Instr5instr06C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8u8_rangeC13~~~K46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions>bv_zero_extendC56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitionsGbv_zero_extend_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec=b_extract8_idC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9le_word_1C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6ov_rdnC13~~~C45stdpp9bitvector;definitions:bv_extractK47Corelib7Numbers7BinNums1N01I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5msize01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_lbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8b_lb_valC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_lhC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8b_lh_valC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9le_word_vC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec:rdn_lengthC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecCbytes_le_to_Z_boundC13~~~C56Stdlib6ZArith6BinInt1Z3mulC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecDbytes_le_to_Z_nonnegC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_lwC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8b_lw_valC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03C45stdpp9bitvector;definitionsCbv_wrap_bv_unsignedK4ELinuxProcessSemantics5Riscv5Instr5msize04".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Common.Cfg Require RomBase RomWrite RomWritev.
Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.

Lemma materialize_syscall_effect_nil :
  forall (m : Model) (r : word) (zs us : list (word * word)),
  materialize_model_accesses m
    (syscall_effect_accesses (mkEffectU r [] zs us [] []))
  = Some m.
Proof. intros m r zs us. exact (materialize_model_accesses_nil m). Qed.

Lemma materialize_syscall_effect_copyin_disjoint :
  forall (m : Model) (r : word) (a : word) (n : nat),
  accesses_outside_lazy [(a, n)] (m_vm_lazy m) ->
  materialize_model_accesses m
    (syscall_effect_accesses (with_copyins [(a, n)] (mkEffect r [] [])))
  = Some m.
Proof.
  intros m r a n Hout.
  exact (materialize_model_accesses_disjoint m [(a, n)] Hout).
Qed.

Lemma materialize_munmap_eff_nil : forall (m : Model) (ms : machine_state),
  materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms))
  = Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.

Lemma access_outside_range_mono : forall (a : word) (n n' : nat) (lo sz : word),
  (n' <= n)%nat ->
  access_outside_range a n lo sz ->
  access_outside_range a n' lo sz.
Proof.
  intros a n n' lo sz Hle [Hnw Hd].
  split; [lia | destruct Hd as [Hd | Hd]; [left; lia | right; exact Hd]].
Qed.

Lemma accesses_outside_lazy_incl :
  forall (accs accs' : list (word * nat)) (lazy : list (word * word)),
  (forall x, In x accs' -> In x accs) ->
  accesses_outside_lazy accs lazy ->
  accesses_outside_lazy accs' lazy.
Proof.
  intros accs accs' lazy Hincl Hout a n lo sz Hin Hlz.
  exact (Hout a n lo sz (Hincl _ Hin) Hlz).
Qed.

Lemma accesses_outside_lazy_app_l :
  forall accs1 accs2 lazy,
  accesses_outside_lazy (accs1 ++ accs2) lazy ->
  accesses_outside_lazy accs1 lazy.
Proof.
  intros accs1 accs2 lazy Hout.
  apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
  intros x Hx. apply in_or_app. left. exact Hx.
Qed.

Lemma accesses_outside_lazy_app_r :
  forall accs1 accs2 lazy,
  accesses_outside_lazy (accs1 ++ accs2) lazy ->
  accesses_outside_lazy accs2 lazy.
Proof.
  intros accs1 accs2 lazy Hout.
  apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
  intros x Hx. apply in_or_app. right. exact Hx.
Qed.

Lemma accesses_outside_lazy_shrink :
  forall (a : word) (len n : nat) (lazy : list (word * word)),
  (n <= len)%nat ->
  accesses_outside_lazy [(a, len)] lazy ->
  accesses_outside_lazy [(a, n)] lazy.
Proof.
  intros a len n lazy Hle Hout a' n' lo sz Hin Hlz.
  destruct Hin as [Hin | []]. injection Hin as Ha Hn. subst a' n'.
  apply (access_outside_range_mono a len n lo sz Hle).
  apply (Hout a len lo sz); [left; reflexivity | exact Hlz].
Qed.

Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
  vm_add_lazy a n (mmap_model a n m).

Lemma mmap_model_noreserve_halted : forall a n m,
  m_halted (mmap_model_noreserve a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fs : forall a n m,
  m_fs (mmap_model_noreserve a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fd1chan : forall a n m,
  fd1chan m -> fd1chan (mmap_model_noreserve a n m).
Proof. intros a n m H. exact H. Qed.
Lemma mmap_model_noreserve_lazy : forall a n m,
  m_vm_lazy (mmap_model_noreserve a n m) = lazy_interior a n ++ m_vm_lazy m.
Proof. reflexivity. Qed.

Definition mmap_args_ok_noreserve (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 16418 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Lemma mmap_args_ok_noreserve_gates : forall ms,
  mmap_args_ok_noreserve ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\
  mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
  = true.
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5).
  split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
  split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

Lemma mmap_noreserve_b_flags : mmap_noreserve_b (Z_to_bv 64 16418) = true.
Proof. reflexivity. Qed.

Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

(** Building one: the placement test is all a caller has to show. *)

Lemma grant_ok_nr_intro : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  grant_ok_nr hint m a n = true.
Proof.
  intros hint m a n Hn Hnal Hpl.
  destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal Hpl)
    as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok_nr. rewrite Hpl, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    (proj2 (Z.leb_le _ _) Htop).
  reflexivity.
Qed.

Lemma grant_ok_nr_place : forall hint m a n,
  grant_ok_nr hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok_nr in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

Lemma grant_ok_nr_unpack : forall hint m a n,
  grant_ok_nr hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_nr in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[_ H1] H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  auto 6.
Qed.

(** A budget-free grant is a fortiori not an errno encoding. *)

Lemma grant_nr_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_nr hint model a n = true ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg.
  destruct (grant_ok_nr_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Lemma mmap_fail_ok_noreserve : forall segs ms x8 model e,
  bv_unsigned x8 = 222%Z -> mmap_args_ok_noreserve ms -> In e mmap_errnos ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn Hdecl.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

Lemma mmap_succ_ok_noreserve : forall segs ms x8 model a,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model a Hno Ha Hdecl Hg.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
  rewrite (grant_nr_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  pose proof (grant_ok_nr_place _ _ _ _ Hg) as Hp.
  rewrite Hflags.
  unfold mmap_noreserve_backed_ok, with_mmap_backing.
  rewrite mmap_noreserve_b_flags.
  rewrite Hp. cbn [andb].
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.

(** Inversion: the admissible outcomes of the NORESERVE call are
    EXACTLY the errnos plus the [grant_ok_nr] grants. *)

Lemma mmap_ok_inv_noreserve : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
      /\ model' = model) \/
   (exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
      /\ model' = mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  destruct (place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
              (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Hdecl;
    [discriminate|].
  rewrite Hflags in Hspec.
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite mmap_noreserve_b_flags in Hspec.
  destruct eff as [r ws zs us cs copyins].
  cbv beta iota zeta in Hspec.
  destruct ws as [|w ws]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Herr; rewrite ?Herr in Hspec;
    cbv beta iota in Hspec.
  - destruct zs as [|z zs]; [|discriminate].
    inversion Hspec; subst.
    split; [reflexivity|]. left.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    exists e. auto.
  - rewrite andb_true_r in Hspec.
    destruct (linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                (ms_gpr ms 0) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) r)
      eqn:Hcond; rewrite ?Hcond in Hspec.
    2:{ rewrite andb_false_l in Hspec. discriminate. }
    destruct (listNN_eqb zs
                [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
      rewrite ?Hzs in Hspec.
    2:{ rewrite andb_false_r in Hspec. discriminate. }
    cbn [andb] in Hspec.
    apply listNN_eqb_eq in Hzs. subst zs.
    inversion Hspec; subst.
    split; [reflexivity|]. right.
    exists r. split; [|split].
    + exact (grant_ok_nr_intro _ _ _ _ (proj1 (mmap_grant_len_ok _ Hl))
               (proj2 (mmap_grant_len_ok _ Hl)) Hcond).
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.

Lemma mmap_no_unmodeled_noreserve : forall segs ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hdecl Hspec.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hspec.
  unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hdecl in Hspec.
  cbv beta iota zeta in Hspec.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  rewrite E in Hspec. cbv beta iota in Hspec.
  match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    discriminate.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma sstep_munmap_inv_lazy : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + right.
      match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite materialize_munmap_eff_nil in Hmat;
        inversion Hmat; subst
      end.
      reflexivity.
  - (* sstep_syscall_materialization_fault *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
      [ rewrite materialize_syscall_effect_nil in Hmat
      | rewrite materialize_munmap_eff_nil in Hmat ];
      discriminate
    end.
  - (* sstep_exit *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite Hh in H6 | rewrite munmap_model_halted, Hh in H6 ];
      discriminate
    end.
  - (* sstep_killed *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6
      | rewrite m_killed_of_m_halted_none in H6;
        [| rewrite munmap_model_halted; exact Hh] ];
      discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

Lemma node_munmap_lazy : forall ms model x8,
  sc_alloc scfg = false ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                  model)).
Proof.
  intros ms model x8 Halloc Hh Hsvc Hno Hargs.

  assert (Hin : bv_unsigned (in_sysno (sys_input segs ms x8)) = 215%Z)
    by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hok : syscall_spec (sys_input segs ms x8) model
                  (Ok (munmap_eff ms)
                      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []))
    by (apply munmap_ok; assumption).
  assert (Hnr : refusal_b (sys_input segs ms x8) model (eff_ret (munmap_eff ms)) = false).
  { rewrite (refusal_b_munmap _ model _ Hin). apply munmap_eff_ret_not_ENOMEM. }
  split.
  - intros []. apply (sstep_cfg_syscall segs scfg ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + exact Hok.
    + apply not_spurious_nonrefusal. exact Hnr.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_munmap_eff_nil.
  - (* At 08b1429 munmap of an exact mapping may also answer the injected
       -ENOMEM (Sys/Mm/Mmap.v munmap_spec, injected_table 215).  With
       [sc_alloc scfg = false] that answer is a spurious refusal: the family
       is off, -ENOMEM is a refusal, and the unmap is a non-refusal outcome
       of the same input, so [sstep_cfg] does not take it. *)
    intros e st Hss.
    assert (Hoff : injected_family_off scfg (sys_input segs ms x8) = true).
    { rewrite (injected_family_off_some scfg _ (mkInjectedArm 215 FamAlloc [ENOMEM]));
        [cbn [ia_family family_may_fail]; rewrite Halloc; reflexivity
        | rewrite Hin; exact injected_arm_215]. }
    pose proof (sstep_munmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs
                  (sstep_cfg_sub segs scfg _ _ _ Hss)) as Hinv.
    inversion Hss; subst; try congruence;
      try (exfalso; destruct Hinv as [_ [(? & ? & Hx) | Hx]]; discriminate Hx);
      (* the exit and killed arms end in [SNext] too; their trace is not [] *)
      try (exfalso; destruct Hinv as [Hev _]; apply app_eq_nil in Hev;
           destruct Hev as [_ Hev]; discriminate Hev).
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    destruct Hcase as [(er & Her & -> & ->) | (-> & ->)].
    + exfalso.
      match goal with Hns : ~ spurious_refusal_cfg _ _ _ _ |- _ => apply Hns end.
      apply (spurious_intro scfg _ model _ (munmap_eff ms)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) [] Hoff);
        [| exact Hok | exact Hnr].
      rewrite (refusal_b_munmap _ model _ Hin).
      destruct Her as [<- | []]. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite materialize_munmap_eff_nil in Hmat;
        inversion Hmat; subst
      end.
      exists tt. split; reflexivity.
Qed.

Lemma srz_munmap_lazy : forall ms model x8 T,
  sc_alloc scfg = false ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 T Halloc Hh Hsvc Hno Hargs Hc.
  eapply srz_silent1; [apply (node_munmap_lazy ms model x8); assumption
                     | exact (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_215)) | exact Hc].
Qed.

Lemma sstep_write_next_inv_disjoint : forall ms model x8 buf evs c',
  m_halted model = None ->
  accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs (SNext c') ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
  intros ms model x8 buf evs c' Hh Hout Hfd Hsvc Hno Hg Hr Hok Hnb Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
                   (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - (* sstep_exit : write leaves the model unchanged, so it cannot halt *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* sstep_killed: same — an unchanged model is not killed *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
    end.
Qed.

Lemma sstep_write_inv_disjoint : forall ms model x8 buf evs st,
  m_halted model = None ->
  accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hout Hfd Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
  destruct st as [c'|].
  - destruct (sstep_write_next_inv_disjoint ms model x8 buf evs c'
                Hh Hout Hfd Hsvc Hno Hg Hr Hok Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
    exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
  - (* SError: the write is modeled, and its one access is disjoint,
       so neither error transition applies *)
    exfalso. inversion Hss; subst; try congruence.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
        Hmat : materialize_model_accesses ?model' _ = None |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
                    Hfd Hno Hg Hr Hok Hnb H3)
          as (n & _ & Hn2 & Heff & Hm & _);
        subst eff model';
        rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
                   (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
        discriminate
      end.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
      end.
Qed.

Lemma node_write1_disjoint : forall ms model x8 buf,
  m_halted model = None ->
  accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* 08b1429: [vfs_write]'s access_ok check, as in the model's NoReserve.node_write1_disjoint *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok segs scfg (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb.

  assert (Hin : bv_unsigned (in_sysno (sys_input segs ms x8)) = 64%Z)
    by (rewrite in_sysno_sys_input; exact Hno).
  split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_cfg_syscall segs scfg ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + apply not_spurious_nonrefusal. rewrite (refusal_b_write _ model _ Hin).
      change (eff_ret (with_copyins [(ms_gpr ms 1, n)]
                         (mkEffect (len_word (firstn n buf)) [] [])))
        with (len_word (firstn n buf)).
      apply write_ret_not_ENOMEM. exact Hbm.
    + exact Hh.
    + apply materialize_syscall_effect_copyin_disjoint.
      exact (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout).
  - intros e st Hss.
    destruct (sstep_write_inv_disjoint ms model x8 buf e st
                Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb
                (sstep_cfg_sub segs scfg _ _ _ Hss))
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma srz_write1_disjoint : forall ms model x8 buf T,
  m_halted model = None ->
  accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes segs scfg (mkCfg (advance_past_svc
                         (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes segs scfg (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node segs scfg (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1_disjoint ms model x8 buf); assumption.
  - eapply RomWrite.write1_rob; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Inductive msteps_acc
    : machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step_accesses segs ms
      = MachineOk (@mkAccessReport machine_state ms1 ranges) ->
    msteps_acc ms1 ms2 accs ->
    msteps_acc ms ms2 (ranges ++ accs).

Lemma msteps_acc_one : forall ms ms' ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  msteps_acc ms ms' ranges.
Proof.
  intros ms ms' ranges Hsvc Hstep.
  rewrite <- (app_nil_r ranges).
  eapply msta_step; [exact Hsvc | exact Hstep | apply msta_refl].
Qed.

Lemma msteps_acc_trans : forall ms ms' ms'' accs1 accs2,
  msteps_acc ms ms' accs1 -> msteps_acc ms' ms'' accs2 ->
  msteps_acc ms ms'' (accs1 ++ accs2).
Proof.
  intros ms ms' ms'' accs1 accs2 H; revert accs2 ms''.
  induction H as [ms | ms ms1 ms2 ranges accs Hsvc Hstep H IH];
    intros accs2 ms'' H2; [exact H2|].
  rewrite <- app_assoc. eapply msta_step; eauto.
Qed.

Lemma srz_msteps_disjoint : forall ms ms' model accs T,
  m_halted model = None ->
  msteps_acc ms ms' accs ->
  accesses_outside_lazy accs (m_vm_lazy model) ->
  srealizes segs scfg (mkCfg ms' model) T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms ms' model accs T Hh Hms; revert T;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros T Hout Hc; [exact Hc|].
  eapply srz_step_disjoint;
    [ exact Hh | exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.

Lemma rz_msteps_disjoint : forall ms ms' model accs T,
  m_halted model = None ->
  msteps_acc ms ms' accs ->
  accesses_outside_lazy accs (m_vm_lazy model) ->
  realizes segs scfg (mkCfg ms' model) T ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms ms' model accs T Hh Hms; revert T;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros T Hout Hc; [exact Hc|].
  eapply rz_step_disjoint;
    [ exact Hh | exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.

Lemma ts_msteps_disjoint : forall ms ms' model accs,
  msteps_acc ms ms' accs ->
  accesses_outside_lazy accs (m_vm_lazy model) ->
  to_spin segs ms' model ->
  to_spin segs ms model.
Proof.
  intros ms ms' model accs Hms;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros Hout Hspin; [exact Hspin|].
  eapply ts_step_disjoint;
    [ exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hspin] ].
Qed.

End WithSegs.

End WithFP1.
Ltac stepacc_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.
Section WithFP2.
Context {fx : FPState}.

Lemma stepacc_opimm_gen : forall segs regs pc mem rom w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_shiftimm_gen : forall segs regs pc mem rom w op rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_op_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_opimm32_gen : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_shiftimm32_gen : forall segs regs pc mem rom w op rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_op32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_mul_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_mul32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepacc_branch_tk_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst regs (btgt pc (bv_signed imm)) mem rom) []).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma stepacc_branch_ft_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst regs (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

Lemma stepacc_lui : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma stepacc_auipc : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma stepacc_jal_x0 : forall segs regs pc mem rom w (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal 0 imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst regs (btgt pc (bv_signed imm)) mem rom) []).
Proof.
  intros segs regs pc mem rom w imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  rewrite is_x0_0; cbv beta iota.
  rewrite b_addsext. reflexivity.
Qed.

Lemma stepacc_jalr_gen : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
          (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.

Lemma stepacc_ecall : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
       ms_svc_pending := Some (getr regs 17);
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    []).
Proof.
  intros segs regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses.
  cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

Lemma stepacc_lbu : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b)))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
  { rewrite le_word_1, b_extract8_id. apply bv_eq.
    unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lb : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite b_lb_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lh : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lhu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 16 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 16) with 65536%Z.
    change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_lwu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 32 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 32) with 4294967296%Z.
    change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma stepacc_ld : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 8%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

End WithFP2.
