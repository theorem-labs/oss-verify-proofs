(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import Gap04.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From Stdlib Require Import Zify.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RefNodes () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2or00C47Corelib4Init5Logic6or_indK47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib2AS8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib2AS8RefNodes6t_alt3C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsI47Corelib4Init5Logic2eq00K4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01I47Corelib7Numbers7BinNums1Z00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch9lookup_caC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch8ca_checkC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib4Init9Datatypes3nat02C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib2AS7ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch:CheckedArm00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch=checked_tableK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03K47Corelib4Init9Datatypes3nat01C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC59OSSVerify5KrLib2AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg5t_altC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Nodes8rz_casesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib2AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00i59OSSVerify5KrLib2AS8RefNodes5three00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS8RefNodes5three01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS8RefNodes5three02C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS8RefNodes5three03C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00C59OSSVerify5KrLib2AS7FileSim;adv_eff_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes5ependC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes>asanreflect_fxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib2AS8RefNodes>asanreflect_fxC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib2AS8AllocSim?apply_zeros_oneC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC59OSSVerify5KrLib2AS7MmapSim5zfillC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC59OSSVerify5KrLib2AS8PropExec7fp_regsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib2AS8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib2AS8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib2AS8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib2AS7MmapSim6unfillC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:StreamExec?adv_apply_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removec59OSSVerify5KrLib2AS8RefNodesAwith_vmmaps_lazy'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodesBvm_forget_range_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSimAbrk_resolution_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=brk_refusal_bK47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bC59OSSVerify5KrLib3Lib3Cfg=refusal_b_214C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=ret_in_errnosC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC59OSSVerify5KrLib3Lib3Cfg=refusal_b_222C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC59OSSVerify5KrLib3Lib3Cfg=refusal_b_226C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offC59OSSVerify5KrLib3Lib3CfgCacfg_family_off_222C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgCacfg_family_off_226C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsDcheck_syscall_ok_iffC59OSSVerify5KrLib3Lib3CfgIrefusal_spurious_of_grantC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00C56Stdlib6ZArith6BinInt1Z2leC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2c59OSSVerify5KrLib2AS8RefNodes7brk_admC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgc59OSSVerify5KrLib2AS8RefNodes@refusal_b_brk_msC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsC59OSSVerify5KrLib2AS8AllocSim:brk_ok_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim9brk_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgCacfg_family_off_214C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim<brk_ok_introC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00C47Corelib4Init6Specif9proj1_sigK47Corelib4Init6Specif3sig01c59OSSVerify5KrLib2AS8RefNodesCbrk_adm_nonspuriousC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib2AS8RefNodesCbrk_nonspurious_admC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsEcheck_syscall_err_iffC59OSSVerify5KrLib2AS8AllocSim@brk_no_unmodeledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim>brk_step_shapeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC59OSSVerify5KrLib2AS5Nodes?node_chk_ev_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap7min_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;brk_grow_okC47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC45stdpp9bitvector;definitions6bv_subC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z:ltb_irreflK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes9MorphismsFreflexive_proper_proxyC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C47Corelib7Classes?RelationClasses>iff_TransitiveI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C47Corelib7Classes?RelationClasses=iff_ReflexiveC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK46Stdlib9micromega=RingMicromega3Op203C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_model_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@forget_vm_rangesC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_grantsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapDmaps_subtract_rangesc59OSSVerify5KrLib2AS8RefNodes?with_vmmaps_etaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodes:vmmaps_etaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim?brk_unmaps_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim?brk_grants_keepC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS8AgentLib7u64_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions?bv_sub_unsignedC59OSSVerify5KrLib2AS8AllocSim?brk_unmaps_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim?brk_grants_growC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2AS7MmapSim8grant_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodes;grant_ok_naC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Program6Basics4implc59OSSVerify5KrLib2AS8RefNodesEmmap_noaccess_args_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC46Stdlib4Bool4Bool:andb_assocc59OSSVerify5KrLib2AS8RefNodes:mmap_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodes>noaccess_modelC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTC4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_belowC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizec59OSSVerify5KrLib2AS8RefNodes>mprotect_modelC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm8Mprotect>check_mprotectC59OSSVerify5KrLib2AS7FileSim;in_sysno_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSimFpage_round_up_Z_boundsC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectImprotect_grows_conflict_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_modeled_bC56Stdlib6ZArith6BinInt1Z6leb_gtc59OSSVerify5KrLib2AS8RefNodesAcheck_syscall_226C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextC46Stdlib5Lists4List2Inc59OSSVerify5KrLib2AS8RefNodesDfixed_noaccess_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodesEfixed_destroyed_modelC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys6Kernel4ForkEcheck_set_tid_addressc59OSSVerify5KrLib2AS8RefNodes5tid_IC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidc59OSSVerify5KrLib2AS8RefNodes@check_syscall_96C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib2AS6CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib3Lib3CfgGtransparent_nonalloc_noC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00c59OSSVerify5KrLib2AS8RefNodes?with_tid_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodes=with_tid_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Nodes>sstep_of_checkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State7m_credsC4ELinuxProcessSemantics?LinuxProcessSem5StateBm_setsid_succeededC4ELinuxProcessSemantics?LinuxProcessSem5State9m_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem5State?procst_childrenC4ELinuxProcessSemantics?LinuxProcessSem5State9m_utsnameC4ELinuxProcessSemantics?LinuxProcessSem5StateGm_sigaltstack_installedC4ELinuxProcessSemantics?LinuxProcessSem5State=procst_killedC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_sigabrt_pendingC4ELinuxProcessSemantics?LinuxProcessSem5State@m_abort_terminalC4ELinuxProcessSemantics?LinuxProcessSem5State:m_statpinsK4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState01C59OSSVerify5KrLib2AS5Nodes=sstep_svc_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyC59OSSVerify5KrLib2AS5Nodes7halt_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib2AS8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes6rz_sysC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodes:rz_exit_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:AgentNodes@bv_and_255_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backed_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC59OSSVerify5KrLib2AS5Gap04Aalloc_top_lt_2_64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodes=Z_to_bv_u_eq'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modC59OSSVerify5KrLib2AS8AllocSimGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib2AS7MmapSim@region_free_consC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool>andb_false_iffC46Stdlib4Bool4Bool;andb_true_rC59OSSVerify5KrLib2AS8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC46Stdlib4Bool4Bool:orb_true_rc59OSSVerify5KrLib2AS8RefNodes?map_remove_skipC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractC46Stdlib5Lists4List9app_assocC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z3maxc59OSSVerify5KrLib2AS8RefNodesCiv_subtract_coveredC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodes=u64_roundtripC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5max_lC56Stdlib6ZArith6BinInt1Z5min_lC56Stdlib6ZArith6BinInt1Z5min_rC56Stdlib6ZArith6BinInt1Z5max_rI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC56Stdlib6ZArith6BinInt1Z8min_specK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z8max_specI46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib2AS8RefNodesAiv_subtract_sizesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;incl_filterC46Stdlib5Lists4List;incl_ForallC47Corelib4Init3Nat3mulI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulc59OSSVerify5KrLib2AS8RefNodesIlive_bytes_iv_subtract_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodes>live_bytes_appC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesCPreOrder_Transitivec59OSSVerify5KrLib2AS8RefNodesKlive_bytes_maps_subtract_leC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<transitivityc59OSSVerify5KrLib2AS8RefNodesFmaps_subtract_all_consC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorderc59OSSVerify5KrLib2AS8RefNodesOlive_bytes_maps_subtract_all_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodesGvm_backed_bytes_le_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodesFvm_backing_used_simpleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodesGvm_backing_used_le_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AllocSim>with_vmmaps_vmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodesFmprotect_model_next_eqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3minC4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC59OSSVerify5KrLib2AS7FileSim@length_file_readC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8RefNodesCfile_read_length_eqC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_min".
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

Lemma t_alt2_idem : forall A, t_eq (t_alt2 A A) A.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01Hh11Ah22H0h32trp;1p;2p;6p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9p1003<p4p70R0p1003lp4p710R1p8P0p1004Hp4p710R2p8P0p1004fp4p7210R3p8P0p1005Cp4p710R0p8p1005ap4p710P0p8p1006>p4p70R4P1p8P4P2p8P4P3p8P4P0p8P4p1006lp4p710p8p1007Ip4p7210R4P1p8P4P0p8p10085p4p70R4P1p8P4P2p8P4P3p8P4P0p8g008kj18Tg009Kj20Tg009ej62Tg00:Aj31Tg00:[j47Tg00;6j36j24Tg00;mj23Tg00<Fj25Tg00=;g00>0#8f1R0f0R4O1R3/03R2f2P0O1R1[1011\3P1P1P1P4X21R5P5P4E2X02A1114X03C7A6004/33eW31444/54eW1o"). Qed.

Lemma t_alt3_idem : forall A, t_eq (t_alt3 A A A) A.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01Hh12H0h21Ah32trp;1p;2p;6p;3p;4g008kj18Tg009Kj20Tg009ej61Tg00:Aj32Tg00:[j47Tg00>fj46j33Tg00;mj24Tg00<Fj25Tg00=;g00>0#8f1R0f0R1O1R21022'0R3f2R4P0O1R5[1055R6,05\2P5P6P5P1X15f3P4O1R4P4P4P1X04R4P4P1E1X16P1E1X03A2561X02C7P0P0P0P1C6/42eW3A3111/51eW2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h03fdsh11mp;1p;2g00?]j10Tg00@Bj17Tg00@`j12Tg00ACj21Tg008kj16Tg00Acj15Tg00BEj13Tg00C<j24Tg00CV#0#0#0#0#0#0#7#2R0g00D;'1#6g00E3%50f0#3'4W1W0o"). Qed.

Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h03fdsh11mp;1p;2g00?]j10Tg00@Bj16Tg00@`j13Tg00ACj21Tg008kj12Tg00Eij15Tg00C<j24Tg00CV#0#0#0#0#0#0#6#3R0g00D;'1#2g00E31100#2f0#5'4W1W0o"). Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01mh11tp;1p;2g00?]j10Tg00@Bj15Tg00@`j12Tg00Acj11Tg00BEj14Tg00C<j23Tg00CV#0#0#0#0#0#0#5#2R0g00E3%10f0#4'3W0W1o"). Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01mh11tp;1p;2g00?]j10Tg00@Bj16Tg00@`j12Tg00ACj21Tg008kj15Tg00Eij14Tg00C<j23Tg00CV#0#0#0#0#0#0#6#2R0g00E31100#5f0#4'3W0W1o"). Qed.

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01hh11mp;1p;2g00?]j10Tg00@Bj16Tg00@`j12Tg00ACj21Tg008kj15Tg00Eij14Tg00C<j23Tg00Fag00E3g00CV#0#0#0#0#0#0#6#2R0/10#5f0#4'3W1W0o"). Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h06m_fsysi006m_fsysh14m_ioi014m_ioh25m_limi025m_limh36m_proci036m_proch46m_timei046m_timeh51mi051mh64m_fdi064m_fdh74m_vmi074m_vmh89vmst_lazyi089vmst_lazyh99vmst_mapsi099vmst_mapsh:Avmst_materializedi0:Avmst_materializedi0;1vp;1p;2p;3p;7g00GXj13Tg00HOj25Tg00IIj32Tg00Icj74Tg00?]j10Tg00@Bj1:Tg00@`j19Tg00ACj28Tg008kj11Tg00JYj37Tg00C<j26Tg00E3R0P0f0R1#3/51=201P1g00KQg00LIR2P2g00MAR2g00N9R3g00O1R4g00OkR5g00PdR6f7R7f5R8f4R9f3R:f2R;f1R<P1F4R=#3/5==20=]4]2]3]0]1P1g00Fag00CV#0#0#0#0#0#0#:#9R=/8=#1%1=f<f6R==778P9P:P;P<P1F4,60X46X25X34X03X12W:W8W9P;P<P1O3n0110;00013010910810:W7W6P=P8P9P:P;P<P1O7n01105000170106107101100103102104W5o"). Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h01hh16vm_brki006vm_brkh2:vm_init_spi01:vm_init_sph38vm_limiti028vm_limith47vm_mapsi037vm_mapsh5<vm_mmap_basei04<vm_mmap_baseh6;vm_noaccessi05;vm_noaccessh7;vm_reservedi06;vm_reservedh8<vm_start_brki07<vm_start_brki081vp;1p;8p;3p;2g00Q^j1?Tg00RXj1>Tg00SNj13Tg00THj12Tg00UCj1=Tg00V8j17Tg00Voj15Tg00Wjj14Tg00Xcj81Tg00IIj36Tg00?]j10Tg00@Bj18Tg00@`j19Tg00ACj2<Tg008kj1:Tg00C<j2;Tg00FaR0P0f0R1#?%>1%31%21%=1%71%51%41G1=601P1g00CV#0#0#0#0#0#0#8#9R2/<2#:R3g00YZf7R4f6R5f5R6f4R7f3R8f2R9f1R:P1G1,;0X22X52W3X12X82X63X43W7P4P5P6P7P8P9P:P1O8n01108000180106103105107100102104101W0o"). Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01zh11Hh22b1h32b2h41nh51ap;1p;2p;3p;6g00?]j13Tg00@Bj1;Tg00@`j12Tg00Z8j20Tg00IIj31Tg00Zbj25Tg00[Hj3:Tg00[lj29Tg00\Rj28Tg00]Ej37Tg00^1j26Tg005Cj64Tg00CV#3#3#3#3#3#3#;R0#2R1g00YZR2f0R3f1R4,00512P2f2R5,001503f3R6511X02g00^`R1%23R7%24R8g00_>%25?14310651064512R9[10541053512%26?154[R:f4R;#2?165\9A:543P3n2001000000120000000W3W2W4P:^38^27^41P3P01006R1,50R7P6P21901100;9123X021806970110071601E4O4b1P4P3E4W1W0W5o"). Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_forget_range lo hi m = m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h02Hlh12Hmh21lh36m_fsysi006m_fsysh44m_ioi014m_ioh55m_limi025m_limh66m_proci036m_proch76m_timei046m_timeh82mth92hih:2loh;1mi051mh<4m_fdi064m_fdh=4m_vmi074m_vmh>9vmst_mapsi089vmst_mapsi091vi0:9vmst_lazyi0;Avmst_materializedp;1p;2p;3p;7p;6g00?]j14Tg00@Bj1HTg00@`j1GTg00ACj2DTg008kj1CTg00Eij1>Tg00_Yj1BTg00IIj33Tg00`9j16Tg00a9j17Tg00GXj15Tg00alj3?Tg00bhj2ATg00cij3@Tg00JYj31Tg00dDj1<Tg00e7j1;Tg00elj18Tg00faj19Tg00gUj1:Tg00Icj70Tg00C<j2FTg005Cj6=Tg00hJj3ETg00E3R0f1R1f0R233p=2g00YZR3g00CV#4#4#4#4#4#4#H#GR4/D4R5#CR6%>2%B5R533R7%C4R8%61%B4R933R:P6P5f3R;#7R<%5;R=f5R>f4R?5?21A>?R@%6;5@431%<;RA%;;RB%8;RC%9;RD%:;REF0/2;X26P8P9P<A?5>?A@4@251=PAPBPCPDPEF0/2;X28P0f2RE#7RD%5ERC?159%<ERB%;ERA%8ER=%9ER@%:ER<F0/2E^1:^07PEg00KQg00LIR7P7g00MAR7g00N9R:g00O1RFg00OkRGg00PdRHf7RIP>P?P;PEP1P2F0#>=365f8RJf6RKP>P?P;PEP1F0#6=389f9RLPIPKP>P?P;PEF0RM#7%5M?159%<M%;M%8M%9M%:MF0/2M]1]0]7]5]6]3]4P2g00Faf<A1IK>P?P;PEP1P2F0#>=365f=A1JIKP>P?P;PEP1F0#6=389P6P5f?RMf:RN?12JPIPKP>P?P;F0RO#7%5O?159%<O%;O%8O%9O%:OF0/2OX26P8P9PMA1N52PIPKP>P?P;F0RN#7%5N?159%<N%;N%8N%9N%:NF0/2NX88f>A1L59PKP>P?P;PEF0,F0PIP2E=PJP1E=W1W0X7HX5GX6FX3:X47X88X26W>PEP1P2O3n0110901013110810:10;W=W<PKP>P?P;PEP1P2O7n01105000171106107101100103102104P1P2O2PDA?5?;1A?;=@4951CPBPAP=P@P<F0/2Ee%6EP2E=%>EP1E=AE?;E/2EeW1W0X;0X93W:o"). Qed.

Lemma vm_forget_range_lazy_nil : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h02Hlh12hih21lh32loh41mp;1p;2p;3p;7p;6g00?]j10Tg00@Bj1GTg00@`j1BTg00ACj2@Tg008kj1FTg00Eij11Tg00_Yj1ETg00IIj32Tg00a9j14Tg00GXj16Tg00alj33Tg00bhj28Tg00`9j19Tg00cij3?Tg00JYj3>Tg00dDj1<Tg00e7j1;Tg00elj17Tg00faj15Tg00gUj1:Tg00Icj7=Tg00C<j2DTg005Cj6ATg00hJj3CTg00YZR0g00E3g00CV#0#0#0#0#0#0#G#BR1/@1R2#FR3f0R4#1%E2R232P3P2f2R5#4%65f4R6f3R75341867%955?13>%<5%;5%75%55%:5F=#1=232X231D32f1R6#1R8P4EA%46%66A38751875%965?13>%<6%;6%76%56%:6F=#1=232eAC756#1=232eW0W4X10W3o"). Qed.

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h02hih12loh21mp;1p;2g00?]j10Tg00@Bj15Tg00@`j12Tg00Acj11Tg00BEj14Tg00C<j23Tg00YZR0g00E3g00CV#0#0#0#0#0#0#5#2#1f0#4'3W2X00W1o"). Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma mmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z ->
  check_syscall (sys_input segs ms x8) eff model
  = check_mmap (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma munmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 215%Z ->
  check_syscall (sys_input segs ms x8) eff model = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "p'0h03Hnoh11bh23effh35modelh42msh52x8h61zi001ci011xp;1p;2p;3p;4p;6g00?]j10Tg00@Bj1ATg00@`j1;Tg00Z8j24Tg00iHj11Tg00imj1<Tg00IIj33Tg00jKj25Tg00kQj36Tg00lGj4:Tg00mLj22Tg00nJj19Tg01:@j47Tg00C<j2@Tg005Cj68Tg00ooj1?Tg010fj3=Tg011hj3>Tg0135g00CVR0#0#0#0#0#0#0#AR1#;R2g00E3g014<g00YZR3f2R4,41%10#0#1#0#1#1#1#<R033P2f3R5g015:R6g00AcR7g016DR8P6g017MR9f0R:,41'5P:p,4segsR;f6f5R<36P5f4R=C:R>g018WR?n10110100021010000g019aR@,2<%9@RA,2<P4P5C7R<33X12P3P0P7P8P6159:P>P?n10110100021010000=36<X6312=@12=Af1RAP4C7R@,@61415P:E8A6;=5R:#?A=;=5E8A>:A4=36@eW0W2W3W5W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

Lemma rz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs c three (fun _ => []) nx ->
  realizes segs (nx T1) A -> realizes segs (nx T2) B -> realizes segs (nx T3) C ->
  realizes segs c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (rz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (rz_cases segs c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
Lemma node_of_iff : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  (forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i))) ->
  (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
  node_ok segs c I evs nx.
Proof. intros; split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h03memh12pch21rh34regsh43romh52x8p;1p;2p;7p;5p;6p;3g00?]j10Tg00iHj1DTg00@Bj13Tg00@`j14Tg007Ij2CTg00Acj1;Tg01HZj7:Tg01IUj58Tg008kj17Tg00ACj22Tg00_Yj11Tg01JMj66Tg01KKj29Tg01LDj1BTg00imj15Tg01MAj2ATg01Mdj3<Tg01NGj3=Tg01O>j2>Tg01P5j5?Tg00IIj3@Tg00CV#0R0#DR1#3R2%00R0#0R3#0#0#0#3#4R4'C%33#4R3#;\4R5g01Pjf5R6f4R7f1R8f3R9f2R:f0R;F:g0135P6P7P9P:P8D8P;%73,24#11244#1R3P3g01Qk#1g01Rc,24#1E6'9#Bg01SB%01#5R1g01TA1A21d5<2==6;%50,>7P9P:D?3@eX24X54X45W0X14W3o"). Qed.

Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "p'0h01nh11Hh22Hch31bh42b1h52b2h62Hmh71ah81eh93memh:1oh;2pch<1rh=4regsh>3romh?2x8i001zp;1p;2p;3p;4p;8p;6p;5g00?]j16Tg00iHj1lTg00@Bj1ETg00@`j14Tg007Ij2kTg00Acj1gTg01T]j3^Tg00ACj2HTg01U]j4DTg00_Yj1?Tg01V=j3CTg01V]j27Tg01WUj3LTg00IIj31Tg01XJj2=Tg01YCj1[Tg01Z;j2YTg01Z]j1cTg01[?j1XTg01\6j80Tg00imj1VTg01Mdj3ITg008kj1\Tg01JMj6FTg01]=j1STg01^3j19Tg01_2j5ATg01_bj1@Tg01`bj18Tg01acj1BTg01bij1;Tg01chj1>Tg01dgj1<Tg01eej1:Tg01fcj1QTg01g\j1PTg01hTj1RTg01iMj3OTg01jFj1TTg01k?j2UTg00Zbj2jTg01l8j3NTg01NGj3KTg01O>j2MTg01P5j5GTg00C<j2iTg005Cj6JTg01l]j1fTg01mTj3eTg00Z8j22Tg00[Hj3bTg003lj6`Tg01nAj2aTg01n`j1_Tg01o9j4dTg01KKj2WTg01LDj1ZTg01IUj5]Tg01MAj2hTf7R0f6R1#@f5R2f4R3f3R4f2R5#>f1R6f0R7G0p=3g0135R8?167p=5g00CV#6R9#lR:#ER;%69R9#6R<#6#6#6#ER=#4R>'k%E<#4R<#g\>R?A^2671H>>R@P>P>P6P7CD%?@RA3CRB,72AL672RC51?e1=2A/7B=1?CRDePDg0204RDg020TPDP8P7f9REg01PjRF#[RGf8RH1Y>2RI%c>RJ%XFRFP0P1G0RKP;P>%6:#VR:g01TARL5I;RMP3%\<,H>#?R<P>P>P4P5CD=C@ARNPAg01Qk#?ROg01Rc,H>#?RPEFRQ#S%9KDA%@KRR%8K%BK%;K%>KRS%<K%:KG0n0100000020001RK#9PK%8K%BK%;KPK%<KRT%QQ,=T%PQ'7%RQ3O%TQ'U%:KG3RK#9PK%8K%V9R9,j=RQ5N=PJ%;KPK%<K%:KG3g01SBRKAKEM31MH9RTAL450RUP1DG'5X3DP>1M09RDP;P>PMP3PEDAREPEPEPRPHPIPJPSP0P1G0RS#@RRPHPIPJ%>SRS1=0A/7NRNP1G0RVP7PJPJPVPNP1G3PE%[KRNPTPJPJ%XKRVPUP1G0RU'5X3>P?AL561RWPEPEPRPHPIPJPSP7P1G0RSPTPJPJPSP7P1G3/5UX:?P;P>PMP4PHDARUPNPDPJPJPVPWP2G0,i81=1AP>P>P5P6CD=C@AR@'7R8P7EJAN=0QRV%f0EJPUPUPUPHPGP01Y>3RGPJPFP1P2G0RF#@RUP0PGPJ%>FRNP1P2G0RSP0PGPJPSP8P2G3RSPVPJPJPSP8P2G3PKAKHM4PDPWP2DGRW'5eP;P>PMP4P<P@PAPOPPEFR@#S%9FDAPU%8F%BF%;FPN%<F%:FG0RN#9PN%8N%BN%;NPN%<NRU%Q@,=U%P@'7%R@3O%T@'U%:NG3RN#9PN%8N=N=QPJ%;NPN%<N%:NG3/5WRNePNeg0214RN=I;LRJ9e;MP;PMPJ%4;?1MJRQg00^`R=%47RU%46RDg00_>%45?167g00YZRH1245124631[R81256125751H%44?156RS[1234123551H\SAb567P6n2001000000120000000W5W4W0P8^5D^4U^0=P7P;PMPJP6O412;M12;J51HPHP:PHp-0P7g021RRJg021oPJn011000003001000010000X8HPLPNP7E`PJ1aJ7b1b2b1W2%_QeCdEJ1WF@#Z/5Web6P0P1P2P3P4D]P5P<PBPAPOPPEF'W#ZPKPL1h;:d9I;:=K051M19PCP3DG'5eX0>X7>X<>X?>X>?W9X;>W=o"). Qed.

Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "p'0h01bh11nh21Hh32Hch42b1h52b2h62Hmh71ah81eh93memh:1oh;2pch<1rh=4regsh>3romh?1xh@2x8hA1zi001zp;1p;2p;4p;3p;6p;5p;8g00?]j16Tg00iHj1wTg00@Bj1ITg00@`j14Tg007Ij2vTg00Acj1uTg00ACj2MTg01U]j4LTg00_Yj1?Tg01V=j3HTg01XJj2=j3eTg022Kj3Gj4dTg00Z8j20Tg023Aj2STg023^j2RTg024;j2QTg024Xj2PTg01Z]j1^Tg00IIj31Tg00C<j2]Tg0256j2rTg025Sj1kTg005Cj6@Tg0262j3iTg026Oj3gTg026lj3fTg027Hj5cTg01V]j2>Tg008kj1bTg01k?j2<Tg01YCj1XTg01Z;j2WTg01[?j1VTg01\6j82Tg00imj1UTg01Mdj3ETg01JMj6FTg01]=j1TTg01^3j1;Tg01_2j5DTg01_bj1ATg01`bj19Tg01acj1CTg01bij17Tg01chj1BTg01dgj18Tg01eej1:Tg01fcj1aTg01g\j1`Tg01hTj1[Tg01iMj3YTg01jFj1ZTg00Zbj2tTg01l8j3OTg01NGj3KTg01O>j2NTg01P5j5JTg01l]j1qTg01mTj3pTg00[Hj3oTg003lj6lTg01nAj2mTg01n`j1nTg01o9j4jTg01KKj2\Tg01LDj1_Tg01IUj5hTg01MAj2sTf7R0f6R1#Af5R2f4R3f3R4f2R5#Bf1R6f0R7G2p=3g0135R8?167p=5g00CV#6R9#wR:#IR;%69R9#6R<#6#6#6#IR=#4R>'v%I<#4R<#uR?\>R@P>P?1M>>RAP>P>P6P7CL%?ARB3HRC,=2RDAG672REg0204RF10=5RG10=7RH'S10=6RI,RG,QH'PRHPFP?P7%^<RJP0P6O1RKn0100000020000PFP?10=4RL/SI1RLG,QI'PPJPKn010000002000051?X0FPFP?PHPJP1P7O1RKn0100000020000RL,]?g020TRG,rH%kHE@PFP?Ai>>7,0=RH/SIAg>>7,0=,RH,QI'PXAAP>P>P5P6CL=HABRI5fAPJPKn0100000020000=1?LeAe1I7P5P6P1P7Cd51?eX?>Dc1>DB%b<,M>#?R<'<=1@ERDePDPFPGPFP8P7f9RGg01PjRD#XR?f8RL1W>2RK%^>RJ%VDRDP0P1G2RHP;P>%6:#UR:g01TARM5E;RNP3P<PBP>P>P4P5CL=HABRAg01Qk#?ROg01Rc,M>#?RPEFRQ#T%;HDD%AHRR%9H%CH%7H%BHRS%8H%:HG2n0100000020001RH#;PH%9H%CH%7HPH%8HRT%aQ,=T%`Q'>%[Q3Y%ZQ'<%:HG3RH#;PH%9H%U9R9,t=RQ5O=PJ%7HPH%8H%:HG3g01SBRHAKGN31NL9RTAG450RUP1DJ'5X0FP>1N09RFP;P>PNP3PGDDRGPGPGPRPLPKPJPSP0P1G2RS#ARRPLPKPJ%BSRS1=0A/>B/<<RAP1G2RVP7PJPJPVPAP1G3PG%XHRAPTPJPJ%VHRVPUP1G2RU'5X0>P@AG561RWPGPGPRPLPKPJPSP7P1G2RSPTPJPJPSP7P1G3/5UX:@P;P>PNP4PLDDRUPAPFPJPJPVPWP2G2,]81=1I/>B/<<R8P7E@AO=0QRV%q0E@PUPUPUPLP?P01W>3R?PJPDP1P2G2RD#ARUP0P?PJ%BDRAP1P2G2RSP0P?PJPSP8P2G3RSPVPJPJPSP8P2G3PHAKLN4PFPWP2DJRW'5eP;P>PNP4P<PBPIPOPPEFRI#T%;DDDPU%9D%CD%7DPA%8D%:DG2RA#;PA%9A%CA%7APA%8ARU%aI,=U%`I'>%[I3Y%ZI'<%:AG3RA#;PA%9A=O=QPJ%7APA%8A%:AG3/5WRAePAeg0214RA=E;MRJ9p;NP;PNPJ%4;?1NJRQg00^`R=%47RU%46RFg00_>%45?167g00YZRL1045104631[R81056105751L%44?156RS[1034103551L\SAo567P6n2001000000120000000W5W4W1P8^5F^4U^1=P7P;PNPJP6O410;N10;J51LPLP:PLp-0P7g021RRJg021oPJn011000003001000010000X8LPMPAP7ElPJ1mJ7b2b3b2W3%nQeCjE@1\DI#_/5Web6P0P1P2P3P4DhP5P<PBPCPOPPEF'\#_PHPM1s;:d9E;:=K051N19PEP3DJ'5eX1>X7>X<>X@>X>@W9X;>W=o"). Qed.

Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h03bufh14datah21mh33memh41oh52pch61rh74regsh83romh92x8p;1p;2p;3p;5p;6p;8p;4p;9g00?]j10Tg00iHj1PTg00@Bj13Tg00@`j1=Tg007Ij2OTg00Acj1MTg008kj1JTg00imj1:Tg01Mdj39Tg01NGj34Tg01O>j2<Tg028Jj3?Tg01P5j51Tg029Nj3>Tg00IIj35Tg00C<j2NTg02:Dj3LTg005Cj67Tg01YCj1KTg01Z;j2ITg01Z]j1HTg01[?j1FTg01\6j8ETg00ACj26Tg01U]j4DTg00_Yj12Tg01V=j3CTg01JMj6GTg01KKj2;Tg01LDj18Tg02;Gl9BTg01IUj5ATg01MAj2@Tg00CV#0R0#PR1#3R2%00R0#0R3#0#0#0#3#=R4'O%33#=R3#M\4R5%J3R3g0135R6g01PjR7f7R8%01#:R1g01TAR9592R:f2R;34R<f6R=%:0R0'<R>f5R?f1R@f0RA3?RBf4RCD1g01SBRDf8f3RE74:R:1<80R0A>=;@P?D1RF956AX26P5A>?@ARGP7P:P0PAP?D1=56FX45PDP<P>PGPCD1,N6PBALA?@E7P8%K7P=1I4ERB%H4%F7P?PCGEP;1643R<P4P3P@PACD%2<3C1644#2R<P<g01Qk#2g01Rc,64#2EGR<';#8P7P8P=PBP?PCP;P@PAM9BE7P8P=P?PCPEDA/;<#8PDP91@21d9921=48;P>PGPCD1556eW1X04X64X94X85W3X54W7o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma munmap_model_simple : forall (a n : word) m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  munmap_model a n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) a)
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h02Hlh12Hmh21ah31lh41mh51np;1p;2p;3p;8p;6p;5g00?]j10Tg00@Bj1KTg00@`j1<Tg00ACj26Tg008kj15Tg00Eij12Tg00_Yj14Tg00IIj31Tg00`9j1:Tg00Z8j23Tg023^j27Tg00GXj18Tg00Q^j19Tg00RXj1JTg02<Ij2ITg00SNj1HTg00alj3@Tg00THj1?Tg00UCj1>Tg00V8j1=Tg00Voj1ATg00Wjj1BTg00Xcj8;Tg00HOj2CTg02=Bj2DTg005Cj6ETg02>Dj5FTg02?Gj3GTg00CV#0#0#0#0#0#0#KR0#<R1g00E3R21611R3#5R4f0R5#2%43R331%51f1R6#:%4131f4R7,30R8f3R9,30,78R0f2R:#8R;#9%J;/I7%H;?@80%?;%>;%=;%A;%B;G;R;/C:R0P4%2:A1453X34P6%201D;:EEP5DFAG79:=120eW1W0W4X51W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition brk_adm (model : Model) (req r : word) : Prop :=
  brk_resolution_ok model req r
  /\ (brk_refusal_b model req r = true ->
      forall r', brk_resolution_ok model req r' -> brk_refusal_b model req r' = true).

Lemma brk_adm_of_unique : forall model req r,
  brk_resolution_ok model req r ->
  (forall r', brk_resolution_ok model req r' -> r' = r) ->
  brk_adm model req r.
Proof. intros model req r Hr Hu. split; [exact Hr|]. intros E r' Hr'. rewrite (Hu r' Hr'). exact E. Qed.

Lemma refusal_b_brk_ms : forall ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof. intros ms x8 model r Hno. rewrite (refusal_b_214 (sys_input segs ms x8) model r Hno). reflexivity. Qed.

Lemma refusal_b_mmap_sys : forall ms x8 model r,
  bv_unsigned x8 = 222%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof. intros ms x8 model r Hno. rewrite (refusal_b_222 (sys_input segs ms x8) model r Hno). reflexivity. Qed.

Lemma refusal_b_mprotect_sys : forall ms x8 model r,
  bv_unsigned x8 = 226%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mprotect_errnos r.
Proof. intros ms x8 model r Hno. rewrite (refusal_b_226 (sys_input segs ms x8) model r Hno). reflexivity. Qed.

Lemma mm_refusal_spurious : forall ms x8 model eff effS mS evS,
  (bv_unsigned x8 = 222%Z \/ bv_unsigned x8 = 226%Z) ->
  check_syscall (sys_input segs ms x8) effS model = CheckOk mS evS ->
  refusal_b (sys_input segs ms x8) model (eff_ret effS) = false ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = true ->
  spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff.
Proof.
  intros ms x8 model eff effS mS evS Hno HcS HnS Hr.
  apply (refusal_spurious_of_grant ACFG _ model eff effS mS evS); [| exact Hr | apply check_syscall_ok_iff; exact HcS | exact HnS].
  destruct Hno as [E | E]; [apply (acfg_family_off_222 (sys_input segs ms x8) E) | apply (acfg_family_off_226 (sys_input segs ms x8) E)].
Qed.

Lemma brk_refusal_b_move : forall m req r,
  req <> Z_to_bv 64 0 ->
  (bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned req)%Z ->
  req <> vm_brk (m_vmmaps m) ->
  brk_refusal_b m req r = bv_eqb r (vm_brk (m_vmmaps m)).
Proof.
  intros m req r H0 Hs Hb. unfold brk_refusal_b, min_brk. cbv zeta.
  assert (E0 : w_is0 req = false) by (unfold w_is0; apply bv_eqb_neq; exact H0).
  rewrite E0, (proj2 (Z.ltb_ge _ _) Hs), (bv_eqb_neq _ _ Hb). reflexivity.
Qed.

Lemma brk_adm_nonspurious : forall ms x8 model eff,
  bv_unsigned x8 = 214%Z -> brk_adm model (ms_gpr ms 0) (eff_ret eff) ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff.
Proof.
  intros ms x8 model eff Hno [Hok Hf] (_ & Hr & eff' & m' & evs' & Hspec & Hnr).
  rewrite (refusal_b_brk_ms ms x8 model _ Hno) in Hr. rewrite (refusal_b_brk_ms ms x8 model _ Hno) in Hnr.
  apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hspec as (_ & _ & Hok' & _).
  rewrite (Hf Hr _ Hok') in Hnr. discriminate.
Qed.

Lemma brk_nonspurious_adm : forall ms x8 model eff,
  bv_unsigned x8 = 214%Z -> brk_resolution_ok model (ms_gpr ms 0) (eff_ret eff) ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff ->
  brk_adm model (ms_gpr ms 0) (eff_ret eff).
Proof.
  intros ms x8 model eff Hno Hok Hns. split; [exact Hok|]. intros Hr r' Hr'.
  destruct (brk_refusal_b model (ms_gpr ms 0) r') eqn:E; [reflexivity|]. exfalso. apply Hns.
  eapply (refusal_spurious_of_grant ACFG (sys_input segs ms x8) model eff).
  - exact (acfg_family_off_214 (sys_input segs ms x8) Hno).
  - rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact Hr.
  - exact (brk_ok_intro segs ms x8 model r' Hno Hr').
  - cbn [eff_ret]. rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact E.
Qed.

(* [comment removed for export] *)
Lemma node_brk : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
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
  intros ms model x8 Hh Hlazy Hsvc Hno.
  apply (node_chk_ev_gen segs ms model x8 {r : word | brk_adm model (ms_gpr ms 0) r}
           (fun i => mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) (fun _ => []) Hh Hsvc).
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply check_syscall_ok_iff.
    exact (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros [r Hr]. cbn [proj1_sig]. apply (brk_adm_nonspurious ms x8 model _ Hno). exact Hr.
  - intros eff m' evs Hc Hns. apply check_syscall_ok_iff in Hc.
    pose proof (brk_nonspurious_adm ms x8 model eff Hno
                  (proj1 (proj2 (proj2 (proj1 (brk_ok_iff segs ms x8 model eff m' evs Hno) Hc)))) Hns) as Hadm.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & _ & ->).
    exists (exist _ (eff_ret eff) Hadm). cbn [proj1_sig]. rewrite <- Heff. repeat split; reflexivity.
  - intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
    exact (proj1 (check_syscall_err_iff _ _ _) Hc).
  - intros eff m' evs Hc. apply check_syscall_ok_iff in Hc.
    exact (proj1 (proj2 (brk_step_shape segs ms x8 model eff m' evs Hh Hlazy Hno Hc))).
  - intros [r [Hr Hf]]. cbn [proj1_sig].
    destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno (brk_ok_intro segs ms x8 model r Hno Hr))
      as (_ & _ & _ & _ & Hlazy'). rewrite Hlazy'. exact Hlazy.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_r_ok_grow_cases : forall m req r,
  let h := m_vmmaps m in
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
  brk_resolution_ok m req r <->
  (r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h01Hh11bh24__x1h35lemmah41rh52Hgh67__arithh74__ffh88__varmaph95__with:4__x2h;1xh<1yh=1Bh>2E0h?2Hbh@4HposhA2HshB1hhC1mhD3reqp&0p;1p;2p;3p;4p;6p;;p;7p;8p;9g00?]j1?Tg00@Bk105Tg00@`j1oTg00GXj1JTg00Z8j21Tg02jZj2^Tg00THj1KTg02TVj2:Tg00UCj15Tg02k6j2LTg00IIj30Tg01n`j1RTg02kSk204Tg00_Yk103Tg008kj1{Tg02l4j2_Tg02lRj1vTg02m0j1rTg02m[j2qTg02n>j2YTg02naj4NTg01Z]j1nTg02oLj6mTg0300j2jTg00C<j2FTg030Rj2hTg031>j3gTg031]j4fTg02U2j1STg032Oj1ITg024;j24Tg0256j2;Tg01mTj3>Tg033Kj3ATg024Xj27Tg009KR0j23Tg00;mR1j26Tg00_>R2j28Tg034Kk202Tg0357k201Tg035Xj3zTg036Nj6PTg037@j2yTg037`R3j6xTg038Qj3`Tg039Fj4uTg039ml;sTg00:[j4GTg01?Aj3\Tg005Cj6@Tg00:Aj3[Tg03:hj1MTg03;fj1ZTg023Aj2DTg00ACj2pTg00Q^j1VTg00RXj1XTg006lj3cTg00Zbj2CTg023^j2ETg03<^j2WTg03=;j3UTg03>5j1TTg03?3j3aTg00V8j1]Tg03?Xj1tTg03@8j1wTg02VJj2dTg03@\j1lTg03A:j4kTg02Vjj4eTg02@Cj3|Tg03AXj7}Tg03B<j8iTg03B`l9~Tg03CZk400Tg0204R4f0R5g020TR630p=<f1R7g03DMR8g03DlR9P9g03ELR:P5g03ElF}p=Of3R;P8P9P9P:f2R<P7P5Gip=bg02B?R=9045p=2AA<75=04=,8;p=9p-0R>P1g03FLf5R?f4R@P;P<P7P5M9~p=HP>P1P7P5H00p=QAA<75=04=p==P4P6P;P<P7P5E@p=Bg00E3g00CVRA#?RB#?#?#?#?#?$05RC#oRD%J<g00Fag0214RE11C<'^%K7,1C11C;':%5<,1C11C@':g00YZRFP21L75#<A0F<7#RRG[A0F75#R1L<7#<[RH1L;<#<\G20475P5n2001000000120000000X<FW;PH^<F^;FP5f6RH,1CRGPEg03G=RI$03RJ%{IRI1_F7%vFRK%rFRLPF1qFERMg03Gi1YFARACN,OL%n9RNPLP8P9P9P:PFPAg03HPPMCN,OLEmCb1jL:R:P5P<1F4=RM1h5<#2dAgFE7CfR9b7b8b9X2F1^E5A0F7Eg021R[[^2FP5f7R8,1CROP@O2b6O3b0%S?RP#<RQePQP4P4%I?,1C,4O,;5%5?RQ9>CHRRP4P411CQRS,4ORTA>CH8RU/;RRVf8RW?A8HRX,7VRYn0100000020000RZn0100000020000#2A0DHQRQA0DH8R[PWP8P8C9R\'3R]'6X14P4P41;65PRPZn0100000020000#2/6]X14P4P4P5PVPYn0100000020000#2/6]X14A>C?HRZ%5@R^9>C?R_';R`AA8H?Ra'7Rb#2%2`Rc%2aRd'8'6%2Y%2VRV%2XRX'8RYP5P]P]202>]ReEHW3201`a%2ZRa%2_Rf'3,6cPY%2URU%2RRR'3RY/8XRcPVPYP5PXPXg03I79z>1RV/QXRgEPP]P]PeEHW31yZ_A0D?HRZ,6aPc13[RRc/8XRaPYPcPUP[P5PRPR1QVRExPXPXPgEPP]P]PeEHW3A`C?HA0D?^RU,6fPa13[QRa/8XRfPcPaP>P>^=>P1P>P>P1P1CuP0P3P[1QV[PRPQP5M;sPXPXPgEPP]P]PeEHW3A`C?^13ZU/8dRdP][PZP8PHPHC9,3URUPf[P2PaPX%5H90D8RXA0D8WRaf9RfPWPWC9RZ'3P5A0DWfR]%58Re90DW'3P0f:Rg90DfRR%5WRV90DfR[f<R3f;R1;=g%5gR>90D1A0D13f=Rc?=33RY'8'3[P5A0Dg1RhPDP3f>Ri?=c5%5390D7RjA0D7iRkf?RlPiPiC9'3[X4DRm%51Rn90DcRoA0DccRpA=iccRq'8PpPq1FDcRrP5CG3\X5YP1P5E@W0P5O1%5f90DgPDP>PmA=c3>A0DnnA0Dnc/8q1FDn3[W5P1P5E@W0P5O1n200100000021000010000W0P7P5O2n2001000000121000000X0dP0PQP\13aXPfPWP8C9P5PDPeA0D5gA0D5V'3P1PgP5C9X4DA0DefR8A0DeeRa'3A=gfeR\1FDe9\8aP4P411CVRa,4E/75P4P4%MaRa/4a%ZW,Da1pDDR8%VW%XW3c1CCag03IgRQ,Ea/Wa,CC3U'7P=n0100000020000%T1AaCVV,1C'E%]W'D'7RVP=n0100000020000#2X14P4P4P5PVP=n0100000020000#2X14PM11CeRM,4ERV/76%tVCB14MM%wMCBP4P4%JgRV#5Ra,1CR0,4E140M'7P4P4%M0R0%MMRM'4%ZV,DM%VV%XV5c81CC01EMQ/W0,CC3U'7P=n0100000020000%TgAaCea,1C'E%]V'D'7P=n0100000020000#2eP\eCGPWP5E@X0XP5O1P2P]A=gff13R[P1PgPfC9P5PDP313kjPlPiP7C9\qX4D13poPqA[porP5CGX5YP1P5E@X0hP7P5O2n2001000000120000000X0ZP5O1n200100000021100011000X0UCGO2O2O2O211C^R^,4GRZ%<Z1:SO[1:^G%<T[1dG^PJPIPF1_F<P7%lFCkPKPLPFPAg03J_1YFBCN,OLRLPNPLCbP:P9b7b8b9X2FX:FR91:571:7<[^2F^:FRFP5POPSP<O3b6CeCBP4P41;66P_P4P4PZP`Pbn0100000020000Rbn0100000020000#2/6Ue%K@,1CR`,4GRZ%<Z%K?,1CRZ/:O[1:`G14OZ#<[1dG`P9PFP5POPZP;O3b6CeCBP4P4%I@,1C,4G,;6P_Pbn0100000020000#2/6Ue%SHP5CBb>P4P411C?R5%JHRU#I,1C'4,;P%5URU9>C@RPP4P411CU,45A>C@?/;PRPAAH?@,7Pn0100000020000n0100000020000#2%5;90D@A0D@?PHP?P?C9'3R;'6RPePPeA|H?@/6;eW?WAW@bBX4DWDWCo"). Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h01lh11bh21mh33reqh41vp;1p;2p;3p;8p;6g00?]j14Tg00@Bj1TTg00@`j1LTg00ACj2ITg008kj1STg00_Yj1RTg00GXj1@Tg00UCj1?Tg03KFj3=Tg00HOj21Tg03LIj27Tg00Q^j19Tg00Z8j2FTg024;j28Tg024Xj2ETg00RXj1DTg00alj3QTg03MNj3CTg006lj35Tg00SNj1ATg02[=j2BTg03NMj26Tg00THj1>Tg00V8j1;Tg00Voj1:Tg00Wjj1<Tg00Xcj83Tg03OVj1KTg03PVj1JTg005Cj62Tg03QQj1HTg03RQj2MTg03?Xj1NTg03@8j1GTg02]7j3OTg00IIj3PTg00E3R0f1R1f0R23Pp=0g00CV#4#4#4#4#4#4#TR3#LR41I44R4#SR5%R4R6f2R7#@R8%?8R97=1/17,72/07X05g0204R:g020TR;%98R<P:P5g0214R=1F39R>'8/E2%D8R??Q>>R>AC199=54?R@n0100000020000%A8RA1B99'6RB%>8RCP9%;8RD%:8RE%<8R8G3/17/07X1:P:P;P<P:P5P2P>P@n0100000020000PBPCP9PDPEP8G3/17/07X1:P5P6P<A542?PBPCP9PDPEP8G3/17/07X05P5P6P<A546?16A2PCP9PDPEP8G3/17/07X05g00FaR5%@1R81127/07X45%K1%98R5%D8R7%A8RE%>8RD%?8R9%;8RC%:8RA%<8R?G3%J8E2P5A546716E6PDP9PCPAP?G3/11/01e1B99R?%H9RAE2AC2991M29E21F39R3,8=R=/E;%N=E21833%G3E2A=829/11R8/01e1768/01eP?PAE217?8/01eAO291/01eW3X20o"). Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_eq : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
  brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
  = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                   (vm_noaccess h) (vm_start_brk h)
                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h04__x1h14__x2h27__arithh34__ffh46__sat1h56__sat2h66__sat3h76__sat4h88__varmaph95__with:1zh;1bh<1Eh=1lh>1nh?1xh@1HhA2HahB4__p1hC2b1hD2b2hE1mhF3Hb0hG4HbalhH3HbrhI2HdhJ4HdalhK3HlthL3HnwhM5Hreq0hN5HureqhO1dhP1hhQ3reqhR1yp%0p&0p;1p;2p;3p;4p;6p;8p;<p;7p;Bg00GXj1tTg00UCj1aTg00?]j1DTg00@Bk100Tg00@`j1CTg00Z8j20k10ITg023^j2:Tg00imj1eTg03SQR0j2`Tg02jZS00j22Tg03Snk10OTg00_>S01j2?Tg00Zbj2JTg02TVj2ATg03Thk20DTg03UPk30;Tg00nJj1ZTg03V4j2LTg03V]j3KTg03WFj2iTg00_Yj1fTg01V=j3<Tg008kj1jTg02l4k202Tg03@\k101Tg03A:j4~Tg02lRj1|Tg02m0j1{Tg02n>j2lTg03X2j3pTg02m[j2sTg03XUj3vTg01Z]j1uTg0300k20NTg00C<j2>Tg030Rk20MTg00IIj35Tg031>k30KTg031]k40JTg03Y8j2rTg005Cj68Tg004fk60HTg003lj6oTg02naj4OTg03Z0k60GTg01n`k10FTg00ACk20ETg03KFj3[Tg00HOj23Tg03LIj2PTg00Q^j1_Tg01U]j4GTg00RXj1\Tg00SNj1YTg00THj1]Tg00V8j1bTg00Voj1XTg00Wjj1STg00Xcj8;Tg024;j2ETg024Xj2WTg00alj3hTg03MNj3UTg006lj3ITg02[=j2NTg03NMj2MTg03?3j3gTg00[Hk304Tg03<^j2@Tg00[lj2VTg03ZTj3dTg03[7R1j1kTg03[Uk303Tg03\;k105Tg03\Yk406Tg03]<m<09Tg03]ak60:Tg03^Jj4}Tg03_5k10<Tg00]Ek30=Tg03_^k30>Tg03`Lk30?Tg03aLk60@Tg03?Xk10ATg02VJk20BTg02Vjk40CTg02]7j3zTg03bLj2mTg03blj2yTg03AXj7nTg03c]j7xTg03B<j8^Tg03dAl<wTg03dfmB0LTg0214R2f0R3'2p=Fg03IgR4,m3p=qg00YZR5?532p=T1A23p=11y34p=61m34,A2p=9f2R6g03DMR7g03DlR8P8g03ELR9P5f1R:g03GiP3COg03ElR;Fnp==P5P:g03J_P3COp=RP:P7P8P8P9P3P;Fnp=BP6P7P8P8P9P:P3Fxp=cf3R;P7P8P8P9P6P:P3G^p=Hf6R<P7P8P8P9f5R=f4R>P;P7P8P8P9P6P:P3G^G^p=QA55:3p=7g00E3R??5:3p=4g00^`R@P5P5P5P1P1P=P>P;P6P:P3M<wp>07P5P5P5P5P5P5P0P3P:P6P0P;P>P=P<f7R0f8R1f9RANB0Lp>08%t:g00Fa%a3g00CVRB#DRC#D#D#D#D#DRD$00RE#CRF%F6RG10E:RH#F10E6/:>%eCRI%eDRD'`RJ'210E;RK#q#T%q<#T&0O=10E=RL#112LJ'?10E</:1,JEPF10E0/:AR0%6A%1A1A24R4f;RL#9[[10E1RM#6%1Mf:RN,0ERO#9\4[20DIDRP%FI%1D%FJ[[RQ%1IRRg021oRSB0;ID:UWART%1J\S^ARRRg03G=RSg019aRU#ZRV#ZS02,L5S031L5V1L5URU5K55K5g03eLRV'i%fSRW3<RX%jSRYP520256P:&015C~RZ%|5R[%{5R\1l5BRB1l5CRC5p5R]1s5I=v5ER^5=\R_%u8R`P\1s52Ra==\BRbP`P\A=\aCRcP`1Ra],B\=c\_CHFQ20N\9RdP3P6g0204Reg02B?Rf'>20M36=5efdB0K52:H0JRfb3b8b9X05X151:3:/2JS04%F:Rg%F;S051:;>Rh#112hJ'?[[[^05^15P3f>Rif<Rj,0ERkPAPNPLO5b2b4b5b6b7'r10E3/70R0eP0P51:MN10EARA/23X:5%6N%1N%9j\4[%6A%1A10ELRA#9\4[PPPQPTPRPWPYPZP[P\PcP`A=\B]CHPdPfb3b8b9X05X151::6,2:\g^05^15P3f?R0f=Rl,0ERmPjO3b2b4b5b6b7PHP3E812MH1JE2RH95F6RnPFP5&0IEP;PHP3J0H10EHRH,7KP510E>Ro173HX:5P31:AlRpP;Eo17pH%6i%1if@RH#9\4[%6m%1m10E0S06#9\4[PPPQPTPRp-0RqPXPYPZP[P\P5Ap5CBRXg03HPS07PaCO,B\P`P\PcP`P\PbP`P\P7P8P8P9P>J0GCHFQPdPfb3b8b9X05X15WB1::3R9#TP=\G\G[^05^15^BqP3g021RfA,0EfCP=P0PHO6b2b4b5b6b7b<b<W<&0FnRnePn20EFFRn#jR8%fnR7A[j>>/3i,P3%_jRrPFPFPL1JElRsCG%\jRt5<n%YjRu%]jRvP>%bjRw%XjRx%SjRyG;/3iRz'4X=8Peg020TR{PrPeP81E2A/W3AhtoAR|AU>>L=IntR}n01000000200001N>L,MuR~PvP>PwPxPyG;/3i/4zX;ePeP{PrPeP8P3P|P}n0100000020000P~PvP>PwPxPyG;/3i/4zX;eP8PFPFPNAgE;NR}CG=<n7R|PrAIn3tP~PvP>PwPxPyG;/3i/4zX=8P8P7PrPFPFPLAgE>LRrCG=<n7=Int1Mu3PvP>PwPxPyG;/3i/4zX=8%C3Ry%C:RxQ01%C6?5:310;610;:'7Rw[106:1063'7%C;?56:[Rv%C>?5;6\wB046:3P3n2001000000120000000WDWCX>@Pv^Dx^Cy^>@P3PEPsPrP51@oA,VE1JEiRy,0ERx/73X:5RvP5Pp1@3k,VE,7xX:5P51@pARpPvP5Pl1:ki/@k,73X:5%6lRv%1l%90\4[Rx%6kRw%1k10Ei#9\4[RkPPPQPTPRPWPYPZP[P5PBQ07Ad5XCCO,B\PdPfb3b8b9X05X151@9:,73^05^15P310EHRHfBRuO2b2b4b5b6b710EsPvPxPwPkPPPQPTPRQ02#Z,L5Q03=K5U5K5/iV=<SWRSPYPZP[P\A=\X^P`P\PcP`P\PbP`1RaB,B\A=\B^5c\CHFQPdPfb3b8b9X05X15129J%1;12;J'?\G\G[^05^15P3PHPuPlPiP0O5b2b4b5b6b7,rlE81VEp%1pRG%kER9,`IRX,2pRV'?12pJRU,?GPGPVPGPU1>qG:03GGP5P5Q00P3X?5RqQ0012:3$05XR5X?5PpPp1>5pPXPJPqPqPqP5P5g03f81`:3H06,>5XE5X>5PIPI1>5IP9PDPqPq%k3,>5X?@PEPD1>5DJ07N:08N<09J0:PvPxPwPkPPPQPTPRPSPYPZP[P\P_P`P\PbP`P\PcP`Ad5]BR],Ra,B\A=\]^5c\CHFQPdPfb3b8b9X05X15Q04Q051@h;Rh#112hJ'?[\g[^05^15P3PuPHPlPiP0O5b2b4b5b6b7C}&0<E,2p,?Ge:0=EpE8PoP;E810ErB0>E>LE8O4b@1JEjR>=5F}PFPs%_lRsPFPFPjP3CG%\lR}5<n%YlRp%]lRGP=%blRH%XlRu%SlRgG;/30PsPFPFPjPyCG=<n}PpPGP=PHPuPgG;/30'4X;F1>?zPrP3Eob@%_LRr%\LRz9In|%YLR|/M7%]LR0P;%bLRg%XLRu%SLRHG;/3lPrPFPFPNP>CG=<nzP|P0P;PgPuPHG;/3lR>'4e1N;NRF%6j%1j%9i\4[%6A%1A%9m\4[PPPQPTPRPWPYPZP[P\A=\BCP`1RBC,B\CHPdPfb3b8b9X05X15123:1A:6[^05^15P3PMQ06P<O3b2b4b5b6b7R<:0?;NRME8AU;;NP;P;PNP3P1P:J0@E81E2OR:/W{&0A:E81EKOR:A5e:{1AAo[1AOK1EoA=5e{[20BKOP<H0CE8PrPeP8%aLR8,0ERE,E21EKE'WAhzKEAU;;8=Inzn01000000200001N;8R8,M|P0P;PgPuPHG;/3l/4>eA[L;;/3lRL/4>e1P7L/4>ePFPME81P8L/4>e%tlRL#a,N;A[L;;/3l'P/4>RLePLeAz;;l/4>ebMbKbNbQbHWJWGWLWFWIb;bPXO5XE?o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

Lemma grant_ok_grant_ok_na : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na hint m a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h01Hh12b1h22b2h32H0h42_Hh51ah64hinth71mh81np;1p;4p;2p;3g00?]j14Tg00@Bj1JTg00@`j1GTg03f\j4DTg024Xj21Tg00_>R0j2=Tg0357j2FTg00Z8j2@Tg03bLj29Tg02k6j26Tg024;j28Tg023^j22Tg00GXj15Tg03;fj1ATg023Aj23Tg00ACj2ITg00Q^j1>Tg00RXj1?Tg006lj3;Tg00Zbj2:Tg03=;j37Tg03>5j1CTg00V8j1BTg03gTj4ETg00IIj3HTg0204R1f0R2g02B?3Hp=0f2R3f1R4'1/12p=<g00CV#4#4#4#4#4#4#JR5#GR6g00E3g00YZf3R7P3P4P2CD#0P01142#0%03R8%04R9'=[R:%02,=91134#0R9[%07/=8\91F42P4n2001000000120000000X21X11P:^21^11P21@57R1g03IgR:'9g0214R9'61891'11213f4R1#5R8#A'31I66R;%>8%?83;1:537773<R<%C1/23%B8'3R8P4O3%0<%08'=P01@51R0/9:/691890'11207f5R0#5R8#A'3%>8%?85;;1:577713<#0%C0/27%B8'3#01@50R8/9:/691898'11281f6R8#5R<#A'3%><%?<5;;1:517703<#0P21@58R</9:/69189<'112<0f7#5R<#A'3%><%?<5;;1:507783<#0f8R0#C/28%50#B'3#0P4W4W0P4P2O2n2001000000120000000b0b3P1P7P3P4CE#0eW0W8X56W7W6o"). Qed.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\ True.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h01Hh11mh21nh35lemmah42H1h52H2h62H3h71Ah81Bh92H4h:1ah;4hintp;1p;4p;2p;3p;8p;6p;=g00?]j1>Tg00@Bj1cTg00@`j1\Tg03gTj4WTg00Z8j21Tg024Xj24Tg00GXj12Tg00ACj2VTg00Q^j1FTg00RXj1MTg00Zbj2LTg00;mR0j2KTg00_>R1j23Tg03hPR2j3]Tg0357j2JTg039Fj4DTg03iAj2[Tg03inj8OTg035Xj3YTg036NR3j6XTg02jZj2;Tg023^j2?Tg03;fj1=Tg02TVj29Tg02k6j2CTg00IIj3:Tg03jaj2bTg024;j2GTg03kAj2aTg023Aj2ITg03kaj2`Tg00:[j4ETg03bLj2RTg006lj3PTg03=;j3QTg03CZj4_Tg03lAl=^Tg0204R4f0R5g02B?R63:p=0g03IgR7,R5g0214R8'Cp=71G85p=6f2R9f1R:'?%=5'Ip=8f4R;f3R<;P9?Q:5p=SA:4:6/35p=<p-0R=P=P0P0P5P0g03m0R>P2GOp=Zf5R2%F;%M<3P1L:57Q9=:46p=5P=P0P:P5C_p=HP5P:P1P3P9g03ElP<P;P2f6R3f7R?f8R@f9RAM=^p=N1R57p=Bg00YZR7?:58p=A13:5,39p=@A:456,3:p=U1C58p=Tg00CV#>#>#>#>#>#>#cR6#\R4g00E3P<P9P:P5CW#01169RB#7%6B'4%2<RC98B:'4RB1V44RD%FC%MCP91L6:DSRC'4#0%0C,<BRE'K116<RF#7%6F'4RG%2;RH98F9RF'4RIPD%FH%MHP<1L69DSRH'4#0%0IRI%0HRH'3;]5W31JBCP5O2PE%0F,<GRE,KIP=^8=RI^7=RCP=P=\=P0P=P=P0P0CDRBCDRJP=PIP0P=P=P0P>CDR>CDRKP=PIP0P01[=0RIPBP>%ZIGORI116;R>#7RB%6>RL'4RM%22RN98><R>'4#0%0MRM%0>R>'3P5PDPNPNP;P6P<E5RNPNg03I79Y=0R=/HNM:NW31JGFP5O213EH%0L,<BRE,KMPCPJPKPI1162RI#7RK%6IRJ'4#0RC%23RM98I;#0RI'3%0J,<KRK/3IRJPCPKP5PIPI1H=IEXPDPMPMP2P6P;E5RMPM1H=MM:NW31JBLP5O213E>/3NP1PJPM1163RM#B#A1;8M1?M2%2?RM#='9PDPMPMP3P6P2E5g021oRM3@3@P5116?RJ#7%6J#0'<%2@98J3'UP1116@RJ#7%6J#0'<%2A98J?#0PDf:RJ#2R?P?PAP6P@E5116JR@#BR?#A1;8@1?@Af;RN#2RE#='9PDPEPEPJP6PAE5;@M3@[P5%T?%6@#0'<P1116NR@#7#0%6@#0f<R@,16f=R?#278N#0PDf>RN#2RAPAP?P6P@E5116NR@#B#A1;8@1?@?f?RA#2RJ#='9PDPJPJPNP6P?E5;@M3@[[P5116?#7#0%6@#0116Af@R@#278N#0PDfA#2RNPNP@P6PAE5P11C:5#0A:79:[RAA:7:51C9:#0R@[A:7<9\@1b:5P:n2001000000120000000X17X27PA^17^27P5fB,16#BRAP8P;O3%AAP11G:5#01;9:[RA1;:51G9:#0R@[1;<9\@1a:5P:n2001000000120000000X17X27PA^17^27P5P8fD,16RAP2O31;8AP11I:5#0199:[R119:51I9:#0RA[19<9\A1`:5P:n2001000000120000000X17X27P1^17^27P5fFR1,16fE'?RAfGR<#2#=R2P3O319A2116<R2#B#A1;82R81?21fH#2R2#='9RAPDP2P2P<P6P1E5R1/3MR6'3R<'3P;P8P<P9PAP6P5P1PMP3g01TACECECECEb6b0b5b0b4b0W9W6W5W4P:P5O2n2001000000121000000W0P:P5O2n2001000000121000000W0P:P5O2n2001000000121000000b0b0b0W0X27X:4W1W;o"). Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Lemma mmap_noaccess_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  check_syscall (sys_input segs ms x8) eff model
  = let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
    match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r   (* [comment removed for export] *)
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)]
             then CheckOk (noaccess_model r (Z_to_bv 64 n) model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff Hno (H1 & H2 & H3 & H4 & H5).
  rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 34)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na, noaccess_model, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  rewrite <- !andb_assoc. reflexivity.
Qed.

Lemma grant_na_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_na hint model a n = true -> errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg. unfold grant_ok_na in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Hce]. apply Z.leb_le in Hce.
  apply errno_ret_in_below; [reflexivity|].
  pose proof (alloc_top_room (m_vmmaps model)). unfold two_pow_64, stack_max_size in *. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h04addrh11mh21np;1p;3p;2g00?]j10Tg00@Bj14Tg00@`j12Tg04Vgj31Tg00C<j23Tg00E3R0g00CV#0#0#0#0#0#0#4#2R1f1f0f231,30X21W0W1o"). Qed.

Lemma check_syscall_226 : forall ms x8 eff m,
  bv_unsigned x8 = 226%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_mprotect (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Lemma mprotect_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mprotect_errnos r   (* [comment removed for export] *)
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
             then CheckOk (mprotect_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (check_syscall_226 ms x8 eff model Hno). unfold check_mprotect.
  rewrite H0, H2, Hu1.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  cbv beta iota zeta. fold n. rewrite Hna, Hma. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct cs; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct ci; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  reflexivity.
Qed.

Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "p;3p;1p;2g00IIj34Tg00_Yj13Tg04aLj30Tg00C<j21Tg00:Aj32Tg00YZR0g04Q5R1;41%309001110132o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

(* [comment removed for export] *)
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Lemma fixed_noaccess_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_noaccess_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h04addrh11lh21mh31np;1p;2p;3p;4p;8p;6p;5g00?]j10Tg00@Bj1LTg00@`j1=Tg00ACj26Tg008kj15Tg00Eij12Tg00_Yj13Tg00IIj31Tg00`9j1;Tg00Z8j24Tg023^j27Tg00GXj18Tg00Q^j19Tg00RXj1KTg01U]j4JTg00SNj1ITg00alj3CTg01V=j3BTg00THj1?Tg00UCj1>Tg00V8j1@Tg00Voj1ATg00Wjj1<Tg00Xcj8DTg00HOj2ETg02=Bj2FTg005Cj6GTg02>Dj5HTg04acj3:Tg00CV#0#0#0#0#0#0#LR0#=R1g00E3R21611R3#5R4f0R5#2%33R631%51f1R7#;%3131f4R8,40R9f3R:,40,79R0f2R;#8R<#9%K<P1P1P8P:CJ%I<?C905B3%?<%><%@<%A<%<<GDR</E;R3P4%2;A1456X14P7%231F<;EGP5DHA:8:;=123eUUW2X31W0o"). Qed.

Lemma fixed_destroyed_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_destroyed_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h04addrh11lh21mh31np;1p;2p;3p;8p;6p;5g00?]j10Tg00@Bj1JTg00@`j1=Tg00ACj27Tg008kj16Tg00Eij12Tg00_Yj14Tg00IIj31Tg00`9j1;Tg00Z8j23Tg023^j28Tg00GXj19Tg00Q^j1:Tg00RXj1ITg00alj35Tg00SNj1HTg00THj1CTg00UCj1BTg00V8j1?Tg00Voj1>Tg00Wjj1@Tg00Xcj8ATg00HOj2<Tg02=Bj2DTg005Cj6ETg02>Dj5FTg04bhj3GTg00CV#0#0#0#0#0#0#JR0#=R1g00E3R21711R3#6R4f0R5#2%43R331%61f1R6#;%4131f4R7,30R8f3R9,30,88R0f2R:#9R;#:%I;?580%H;?580%C;%B;%?;%>;%@;GAR;/<:R0P4%2:A1453X14P6%201D;:EEP5DFAG79:=120eUUW2X31W0o"). Qed.

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_syscall_96 : forall ms x8 eff m,
  bv_unsigned x8 = 96%Z ->
  check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "p'0h03Hnoh11bh23effh31mh42msh52x8h61zi001ci011xp;1p;2p;3p;4p;6g00@Bj1@Tg00@`j19Tg00Z8j23Tg00iHj1?Tg00?]j12Tg00imj1;Tg00IIj31Tg00jKj25Tg00kQj34Tg00lGj48Tg04cnj26Tg00C<j2:Tg005Cj67Tg00ooj1>Tg04Y4j3=Tg011hj3<Tf0R0#2#2p=0g0135g00CVR1#0#0#0#@R2#9R3g014<g00E3g00YZR4f2R5,32%?1#2#0#0#;R131P3f3R6g015:R7g00AcR8g016DR9P7g017MR:1320'5P0p,4segsR;f6f534f4R<P6C8R=g018WR>n101101000210100001665R?31X13P4P1P8P9P715:0P=P>n10110100021010000=17?X64f1R4,65R?,:71326P0E7A4;<6R0#>A=;<6E7A<054=17?eW0W3W2W5W4o"). Qed.

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if (0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
  assert (Enx : forall i : tid_I,
    mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
  { intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
  apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 96 Hsvc Hno); reflexivity |].
  split.
  - intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | rewrite with_tid_halted; exact Hh | rewrite with_tid_lazy; exact Hlazy].
    destruct i as [t [Ht1 Ht2]]. subst effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : tid_I, eff = effs i /\ m' = with_tid (proj1_sig i) model /\ ev = []).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb; [|discriminate].
      apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
      injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (with_tid_lazy _ model) Hlazy)) in Hmat.
      injection Hmat as <-. exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (with_tid_lazy _ model) Hlazy)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite with_tid_halted in Hh2. congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z); discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_exit_at_lit : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_backing_used_simple : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h01mh11xh24__x1h34__x2h41lh51nh62Hlh72Hmh87__arithh94__ffh:8__varmaph;5__with<1yp;1p;2p;3p;<p;4p;7p;6p;Bg00?]j14Tg00@Bj1_Tg00@`j1VTg00ACj2HTg008kj1;Tg00Eij1BTg00_Yj1:Tg00IIj37j1XTg00`9j18Tg00GXj1>Tg05NDj1=Tg05OAj29Tg05PAj16Tg05Q:j2<Tg05QZR0j15Tg04T?R1j23Tg023^R2j22Tg05R:j1ATg03\;j1WTg00C<j21Tg03]<l<NTg02l4j2LTg03@\j1ITg03A:j4JTg02lRj1KTg02m0j1GTg02n>j2?Tg02m[j2MTg04S\j3FTg03X2j3PTg02naj4QTg03AXj7ETg0300j2RTg030Rj2STg031>j3^Tg031]j4]Tg03^Jj4\Tg005Cj6CTg03>5j1[Tg03\Yj4ZTg03dAl<YTg03dflBDTg00YZR3f1R4f0R537p=0P3P3g03f8P5CZp=@g01RcR6P3P3P3P0P0f3R0f2R7P4g019aR8g0214R9P5M<Yp=UP3P3P3P3P3P3P1f6R:f5R;f4R<P1P0P7P9P4g03IgR1P1P5MBDp=TP3P3P3P3P3P3P2P5P4P7P2P0P<P;P:f7f8f9MBDp=Og00E3g00CVR:#4R;#4#4#4#4#4#_#VR</H<R2#;R=%B5%:2R237%;<R>%84%:<R?37P=P2%>0R@#=RA/95#6%80,<<#5/31'2%A@R@'0X4=P>P?19A2#61<<5#5/31'2/0@X4>%>7R>#=R@#6R=%58R8/31R0'2RB/0=1391RC,2=RD/0=P3P3%X3REP5X13RFPE1045#WX<3X13PBPDPFPFPF1245#@,13X03X53P=P=113=RDP0PCPFPFPF1345#@,13X03X53P8PFPF%55,13X161139CU1131FTM:OP=P=PDM<Ng03G=RD#:%;DP31L37P4%I3CJ%K3%G3RDg03DMg03DlR=P=g03ELR=P31?3:R:1M391?3;5F35P3g03HPP:CQg03ElFE1RD=P5P7g0204R=g02B?RD'11S57=7=DdA^394C]b9b:b;X23X331394,25/05^23^33P5P1%6AO2b8C\%A>R>,0Be19@2#61<<?#5/31'2/0>e%87P5EC%B7P4EC%[7/0>eW7W6W0o"). Qed.

Lemma vm_backed_bytes_no_noaccess : forall h,
  vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h01Hh11hh21lp;1p;2p;3p;6g00?]j10Tg00@Bj1>Tg00@`j15Tg00ACj24Tg008kj1=Tg00SNj13Tg00_Yj1:Tg00IIj31Tg00RXj16Tg05OAj27Tg05PAj18Tg05S8j12Tg00C<j29Tg005Cj6<Tg05R:j1;Tg00Fag00CV#0#0#0#0#0#0#>#5R0/40R0#=R1f0R2#3%:0R031P1P0g00YZR0f2R3#6/72#8%2331X21f1R1#2R3,90%31P2E<%;1=103eW0W1o"). Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_intro : forall m d,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z ->
  (bv_unsigned b + d <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
  (vm_backing_used m + d <= vm_limit h)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) ["WithSegs"] "h04__x1h14__x2h27__arithh34__ffh46__sat1h56__sat2h66__sat3h76__sat4h88__varmaph95__with:4__x3h;1zh<1bh=1Hh>1xh?2Hah@1mhA3Hb0hB4HbalhC3HbrhD3HcehE2HdhF4HdalhG5HlivehH3HrfhI4HtophJ5HureqhK1dhL1hhM1nhN1yp%0p&0p;1p;2p;3p;4p;<p;6p;7p;8p;Bg00GXj1vTg00UCj1nTg00?]j1^Tg00@Bk10UTg00@`k10MTg00Z8j22Tg023^j20Tg03;fj1BTg02TVj2<Tg00ACk20TTg00Q^j1QTg00RXj1RTg006lj3PTg03>5j1NTg00V8j1ITg03Snk10ATg00imj1hTg03SQR0j2fTg02jZS00j2:Tg00_>j2KTg05T4k106Tg03Thk201Tg03UPk300Tg00nJj1_Tg03V4j2UTg03WFj2]Tg00_Yj1yTg01V=j3XTg008kj1wTg02l4j2cTg03@\k10STg03A:j4YTg02lRk10RTg02m0k10OTg00iHj1uTg02n>j2WTg02m[j2kTg03XUk30NTg01Z]k10LTg03X2j3aTg0300k20ITg00C<j2`Tg030Rk20HTg031>k30ETg031]k40DTg03Y8k20CTg00Zbj29Tg024;j28Tg024Xj26Tg03:hj1DTg023Aj24Tg03<^j27Tg03?3j3MTg05U3k30@Tg05C6k40?Tg00IIj3JTg03ZTj3gTg00[lj2dTg03[7R1j1rTg03[Uk30=Tg03\;k10<Tg03\Yk40;Tg03]<m<05Tg03]ak604Tg03^Jk403Tg03_5k102Tg00]Ek307Tg03_^k308Tg03kaj2qTg02Vjj4\Tg003lj6eTg03kAj2pTg005Cj6bTg02oLj6~Tg01n`j1}Tg05V1k40BTg05VRj3sTg03nTj1|Tg05WZj2{Tg05X;k30FTg033Kj3zTg03bLk20GTg03=;j3jTg03blk20JTg03V]k30KTg02naj4mTg03AXj7oTg03c]j7xTg03B<j8lTg03dAm<0PTg03dfmB0QTf0R2#^#^p=Tg03IgR3-0G2p=5g00YZR4g0214R57J2p=E1:52p==1023p=;f3R6f2R7f1R8/923jp=ig0204R9g02B?R:7J2p=31<52p=120J23p=AB0K482p=@P7g03DMR;g03DlR<P<g03ELR=P4P8g03GiP2Cmg03ElR>Fop=CP4P8g03J_P2Cmp=VP8P;P<P<P=P2P>Fop=?P7P;P<P<P=P8P2Fxp=tf6R>P;P<P<P=f5R?f4R@P6P;P<P<P=P7P8P2GlGlp=OAJ482p=H19829j67,6@p=F1682=J9:p=>1`42p=SP4P8g03HPP2Cmp=ZAj782,66p>0>g00^`S01P4P4P4P1P1P?P@P6P7P8P2N<0Pp>0:P4P4P4P4P4P4P0P2P8P7P0P6P@P?P>f7R0f8R1f9RANB0Qp>09P4P@P6P7P8P2Ebp=GP9P:P6P7P8P2Ebp=LP6P;P<P<P=P7P8P2Glp=[g00E3%v8g00Fa%n2g00CVRB#^RC#^S02#T#TRD$0URE$0MRF12E2#5#E%56#E%=@RG12E6#=12E@/0>%B?'<20TFFRH%Q>%R>3PP?PE%;0Ci#3%NA/01%I0'<&0A012E0R0#1%hCRI%hDRJ'fRK,:0'K&06A%BA/:K12EAf;R0'0RL%A0%101<53RMf=RN#5S03#1[[f:RO,2ERP#A%1Pf<RQ,2ERR#5#1\M[201IJRS%=I%1J%=K[[RT%1IRUg021oRVB00IJ8UW?RW%1K\V^?URUg03G=RVg019aRX#_RY#_RZ,U4S041U4YS051U4XRX'@'@g03eLRY']S06%_ZRZ#_,U4S071U4ZRZ/@X'@/]Y%yVR[5XV3X%wVR\P41c47R]P8P41c46R^P6&0S4S08CYS09CYS0:&0R4R_&0O4R`%uC,W4Ra1k4I>0N4ERb5C`S0;&0L<RcP`1W4BRd1W4CRC5a4Re/Va,?`S0<PcP`1k45Ra=C`dRfPcP`AC`aCRgPc1Vae,?`S0=AC`eb5t`FOFO20I`=RhP2P71`9:S0>20H27#3dB0E458H0DRib3b8b9X04X14X:41:7KRj1087S0?/<6Rk%=7Rl10@?Rm#11:mK'K\G[[[^04^14^:4P2f?Rn#Bf@Rof>Rp,2ERqP?PAPOP0O7b2b4b5b6b7+0C19EL,2E/HL10PQRLP9P912E0R?,85S0@18?2Rr'6P9P9%D?Rs%D2Rt'8%BQRu,4t%QQ%RQ5PHRv19EsRwPE%;t/7sDFP:n0100000020000%Np10?NRt,9E=ME0,2E'0%IQ'4Rx'6P:n0100000020000#3X;4P9P918?tS0A,62P9P9%DtRy,8s14yuRzPvPwPE%;yRw/7sDFP:n0100000020000/6xRsP:n0100000020100#3X<9P9P916:2R{PsP:n0100000020100#3X<9PPP9P9182yPzPv19E2RzPE17w2DFP:n0100000020000/>xX;4PLP9P9Pr142uPv19E?RrPE%;2/7?DFP:n0100000020000/>xX;4P9P9P214tuRwPvPrPE%;t/7?RvCiRy'6P:n0100000020000/>xX<9162y/>xX<9PF19EPRxPO%SP:0@OPH0?AJFOxPFP0P:%QN%RN5PHS0BP2PE10RpRx#;/7RS0CDF%Nn19ExRy=MEQ,2ERs'0%IN'4'>X<F%AN%1N%5n#1\M[%AR%1R%5q#1\M[PSPTPWPUP[P\P4P]P8P^CYS0DP_%uB,W4R^=a4d=a4C=g4^,Ze,?`PhPib3b8b9X04X14X:41028Rq1072/08/77'H^04^14^:4P212EoP3fBRFO3b2b4b5b6b7%;N/HvP4%;pS0EP:%Qp%Rp5PHPNPzH0>%NoRz12ENRv/0n,9E=MEN,2ES0F'0%IpR|'4R}'>X;41>{}X<912EyS0G/7R,dE1Hn2X;4R}Px172v,dE,HnX;417xRRxP}%ApS0H%1p%5o#1\M[S0I%AvS0J%1v12EnR}#5S0K#1\M[S0LPSPTPWPUP[P\P4P]P8Q08CYRRP_Aa4Cd=g4C,Zd,?`PhPib3b8b9X04X141082/78,H2^04^14P2fARC,2ES0MfCS0NO2b2b4b5b6b71dEx%1xR{%rES0O,fIS0P,:xS0Q'K1:xKR~,K{P{Q0QP{P~p-0/`{:0={{P4P4Q00P2X>4R~Q001:82$0<XN4X>4PxPx%SxQ0PPKP~P~P~P4P4g03f81f82H0;#SX@4XM4PIPI%SIQ0OPJP~P~Q01%r2#SW>PEPJ%SJJ0:N:09N<05J04Q0HQ0IQ0JQ0LPSPTPWPUQ07Q04/@X,@Z'@/]Y=XV[P\Q0:P_P`Q0;PcP`Q0<PcP`PfPcP`PgPcAg4edRZ,Va,?`AC`Zb5t`FOFOPhPib3b8b9X04X14X:417m@Rm#11:mK'K\G\l\k\j^04^14^:4P2%BFQ0NQ0MP1PQPNPpO7b2b4b5b6b7H03&02E,:x,K{e:07ExDGQ0GP7DGPsB08EyQDG1HpsP4Pn16::Rs%NCRy/02%InRx'4'>X;41>s2X<9Q0>10znRz/4|Rn%3n10yoRy/<x[1<z|14yx#3[1qz|P>C\CLQ0FP2Eeb=Q0BPQPEQ0ECiP>CLQ0CP2Eeb=PrP2Eeb=%B0Rr,4LRz%3z1<tu[1<Lr%3w[1qLr%AQRw%1Q%5p#1\M[Ru%A?Rz%1?%5v#1\M[RMPSPTPWPUP[P\Q0DP_P`1Ve^,?`RvPcPvC[PhPib3b8b9X04X14X:41<q7Pk[^04^14^:4P2%BoPCP}POO4b2b4b5b6b7C\CL18PLRo%3o1:?t[1:PLQ0A#3[1pPLPwPuPzPMPSPTPWPUP[P\PRP_P`PgPcAC`deC[PhPib3b8b9X04X14%=8Q0?,:8[^04^14P2PCP}PQO3b2b4b5b6b7C\ReCL%DLRtPwPuPzPMPSPTPWPUQ06=XV[P\PRP_P`PfPcP`PgPcQ0=FOPhPib3b8b9X04X14%=2Rg1076#1\l[^04^14P2PCP}P0PQO4b2b4b5b6b7%5PRR%5QRk'0#5%E2X;4P4P5Q03,02#5#EX;4P4P51052#5#EX;41`45PkP1EbPRPAEb%5LPPPQP3PwPuPzPMPSPTPWPUP[P\Q08P_P`P;P<P<P=%TD#T#T#hRD,k4/Za,?`E~PhPib3b8b9%EDg021R[P2b2b4b5b6b7AJ435#}eH0BDG5sLDG%DPR3PwPuPzPMPSPTPWPUP[P\1c48P_P`PfPc1Vad,?`C[PhPib3b8b9X04%18\g^04P2P}P0O2b2b4b5b6b7PwPuPzPMPSPTPWPU%|B,{4Q0560F4/@X/]Y=XV[P\P4Q09P8P]CYP_P`Q02,W49C`aPcP`AC`a^PcP`1Zda,?`R`PcP`C[FOPhPib3b8b9X04X14X:4%E7%E6[\l\l^04^14^:4P2P}PCQ0KP0PQPpO6b2b4b5b6b75sPDGP9P9PsP9P9183t14tr%Q0%R05PHRs19E3PE%;t/73DFP:n0100000020000%NNR319ELRL=MEO,2E'0%I0RO'4'6P:n0100000020100#3ePoPeCL185PRe%3e%=?[%=PQ0@#3[1p5PP>C\CL12ELR>P2DGP9P9%n0R0,2ER2,85182>'6P9P9%D2R2%D>RP'814PrPs19E2PE%;PRs/72DFP:n0100000020000AMEL0,2E,03/4O'6P:n0100000020100#3eP9P9%vNRO#nR0,2ER2,85182>'6P9P9%D2R2/8P%BO,4P%QO%RO5PH19E2PE17s2DFP:n0100000020000AMEL0,2E,03%IO'4'6P:n0100000020100#3eAzNLL#3ebJbIbCWGWHWDWAWEWFWBb<bLXK4W@o"). Qed.

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h02b1h12b2h21nh31Hh41xh51zp;1p;3p;2p;6g00?]j13Tg00@Bj1;Tg00@`j11Tg00IIj32Tg00Z8j20Tg00[Hj3:Tg00Zbj29Tg00[lj25Tg00\Rj26Tg00]Ej37Tg00^1j24Tg005Cj68Tg00CV#3#3#3#3#3#3#;R0#1g00^`R1f0R2#1R3f1R4#1R5g00_>f2R6#1?242g00YZR7f3R8/06108432R9[10641062527%18?264[R:f4#1?286\9A:642P2n2001000000120000000W1W0W2P:^15^03^21P2P01004R1,90R3P4P7150110069272X571604970110031401E8O4b3W4o"). Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h02l2h12loh21nh31bi001bh42l1h52IHh61ah71lh81si011pp;1p;2p;3p;4p;6p;5g00?]j12Tg00@Bj1ATg00@`j1<Tg00ACR0j2:Tg008kj1@Tg006lj34Tg03=;j30Tg024Xj21Tg00IIj33Tg00_Yj1;Tg00C<j25Tg01V=j37Tg05Xdj46Tg02Ulj19Tg04IUj3?Tg005Cj68Tg01U]j4=Tg05Y]j5>Tg00CV#2#2#2#2#2#2#A#<R1/:1R2#@R3P2g0204R4f3R5f2R6542f1R7f0R830A0578A0678R9'133^21^11^03R:X43%;2?078/19,54X21X11X03P0P1P1f5R0f4R;572R<=426?078A0<78/19534^21^11^03\:^73P8P4A0;78R</19R=P6P7f7f6R>C6#9R?/18A0067,1?A0567'1R?534X34P4P7P8P>P0C6#9R@/1</19RAA348?X34154A11@=A?@<9E8A42;6?078P5P6P7P8O3E8P1P1P>P0C==72;R;=426?078A0;78/19534eX21X11X03X5:X43X81X31P7P8O2n2001101010121100100X62P8D>W4o"). Qed.

(* [comment removed for export] *)
Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h02Hdh11Hh23Hrfh31bi001bh41lh52loh61nh71sh83Hinh92b'h:1eh;2s'h<1Eh=2IHh>1ai011pp;1p;2p;3p;4p;6p;7p;5g00?]j1:Tg00@Bj1GTg00@`j1BTg00ACR0j2@Tg008kj1FTg03=;j38Tg01U]j43Tg04aLj39Tg00Z8j20Tg023^j21Tg00_Yj1ETg01V=j3;Tg05Z?j6DTg02TVj25Tg00_>R1j2CTg00IIj34Tg004fj6<Tg005Cj7=Tg05Y]j5ATg009KR2j2?Tg0204f0R3g02B?34p=7f2R4f1R5'1/53p=61545/?3p=21553,?4p=>g00CV#:#:#:#:#:#:#GR6#BR7/@7R8#FR9P8f4R:f3R;;84#7P7P7P4P5C3R<f5R=598106=R>106:R?'1R@106;RA1064=6A>32RB[[^77^37^67^57RCX49%E8RD?8;4#7A98<Dg021Rf6RD,06RE/1>RFA6?AE72?P3n010000000W8W2X77X37X67X57P0P7P7A;8D=?8;4#7f7R?=;8D998<PB[[^77^37^67^57\C^49P3P7P7P?PDC3=;8=?8;4#7P7P7f8R;P?C3RB=;8D998<f9R<P;P?P=P:P5ED106<RA106;RG,1ARH/5>52@A8?=:#7'CP1f:R1,06R:A6:AE52FA8;D=#7106?R?/1E15@?72>P311G?f<R?,06R>f;R@,06RE=6>G32A8@<;#7P2P7P7f>R2f=R>C3=48BA98B?11E:15HE72AP=P7P7f?R=P2C3P7P7P<P;C3R;548P8P7P0P7P7P7P3P3n2001101000120100100X:8P7P7f@RAP=C3P7P7P1P<C3P3E<A47=<P8P7P0P7P7P7P3P5n2001101000120100100X:8P7P7fAR0PAC3P7P7P@P1C3P5E<A470@fBRE=47?P7P>106ARA106=R='1RH1063R:fCRB,06RG=6:A32fDRF=472106ERE1060R0;6ARI?>HE[]0X971062,1=RH106>R6A66E=32A47B>P7P211A:=>IE11GE110ARA/5G720]0X;715H092A=P3W0PFP3P5F=W1W0PBP3PDF=W1P3O1b1P3O1b1W<P3O1A98;>P>P?P@P1P<P4P3O6W8P3O1n200100000021100010000W2W0P5P3O2n2001000000121000000b2W8W2X77X37X67X57X=CX49X;7X97P5P3O2n2001101010121100100X>8P3DAW4o"). Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l ->
     bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h01bi001bh11li011lh21sh32H0h42loh51nh61ah71Hh87__arithh94__x1h:4__x2h;4__x3h<2b1h=2b2h>1xh?1yh@3HinhA2HlhB2HrhC2IHhD4__ffhE8__varmaphF5__withG2b'hH1ohI2s'i022Ini032l'i041pp;1p;2p;4p;3p;7p;8p;6p;5g00?]j19Tg00@Bj1\Tg00@`j1VTg00ACR0j2KTg008kR1j1CTg01U]j46Tg04aLj37Tg00Z8j21Tg023^j22Tg02TVj23Tg009KR2j28Tg03=;j3=Tg00_Yj1GTg00C<j2BTg01V=j3>Tg05Xdj4DTg02Ulj1<Tg024Xj2:Tg05[?j1XTg05[`j2WTg024;j25Tg00IIj3;Tg00:Aj3ATg02VJj2UTg02l4j2@Tg03A:j4TTg02lRj1OTg02m0j1NTg02n>j2?Tg03X2j3JTg00iHj1LTg02naj4MTg03AXj7ITg01Z]j1PTg03B<j8QTg0300j2HTg030Rj2RTg031>j3STg031]j4[Tg01?Aj3FTg05\Bj1ZTg005Cj6ETg05Y]j5YTg0204R3f0R4g02B?R53;p=4g020T9;34p=0g00CVR6#9R7#9#9#9#9#9#\R8#VR9/K9R:#CR;P:P9P9f1R<P4C6R=f4R>57:118>R?f3R@,18'2RAf2RB,18RC'3118<,2C/3?'8RC[^29^09A=@B<#4[^59^49RDX1;%G:97:=PC[^29^091B35REW7X59X49P0P9P9f6R0f5RF5>:97:=PC[^29^09A>:F>?=B<#4[^59^49\D^1;P4P9P9f7RGP0C6=>:F97:=PC[^29^09P3P5P@PBPGP0CDRC#</:4#4X03P3PBP<P0PFCD#<RH%44X03g00_>RI%<4#4%0<RJ[%04RK%<<#4[RL%<B#4\J%X4P4n2001000000120000000X03PL^03P4PCPI1:<4#0%0B/8JRL[18JK1:B<#0[RK1:@B#0\L1W<4P4n2001000000120000000X=3X<3PK^=3^<3P4f8R3,18RK118GRL'2RJ,5?15KAPBP3PGP9P9P3PGC6RM=;:Mp-0RN^1;^6:P1P:PNP4g021RA;:<@P>P@P4O2'8n10110100020020100103X1;X6:p?1001102PMP0O21B:M3AO313AK13J?'8P2118FR2/2?f9R?,18RA'312AK/321180RMf:,18RN/2AR1'5#012M2R2,5N#0'8P4132Nf;,18R2/2N,5L#0RN12LM,52#0RLg00YZROPI15<4#013<BRI[134<15B<#0[RP15@B#0\I1U<4P4n2001000000120000000X?OW>RIPP^?O^>ORPP4f<,18RQPJg03G=RJ#G%CJPO1@OBP<1@O@CT%OO%NORJg03DMRRg03DlRSPSg03ELRTPJPRPSPSPTPO1?O61?O75JOg03J_%L6,?OCMg03ElFIR6%PSP6GQ1HJTP4PBPE1R4B#4dg0214=SO<C[bDbEbFX9OX:OX;ORE124</3B12<B/3@[^9O^:O^;OROP4f=,18R8PKPAPBO4b8O3b33FWAP4O1131MPIPPP4PK12Q2PEPOP4PAPQP8PBO4b8O3b39ANLWBP4O1n200100000021100011000bHO3b3%0CeO2b31:H5%ZHEEA=>B<P@PBP<A7:=0P@PBP<P9P9P?P3C6P9P9PBP<C6R35;:A7:3G;F4O3W@XI9XG9O3EEP9P9P0PFC6=>:>?=B<#4eW7X59X49XCDX1;X29X09P<P4O2n2001104010121100100X6:P4DYW1o"). Qed.

(* [comment removed for export] *)
Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01bh11ph21ah31lh41np;1p;2p;3p;6p;4g00?]j10Tg00@Bj1BTg00@`j1<Tg00ACj28Tg008kj1ATg01mTj31Tg024Xj22Tg0262j3;Tg026Oj3:Tg026lj35Tg0256j24Tg00C<j29Tg05\aj27Tg005Cj66Tg01U]j4@Tg01V=j3=Tg05]]j3>Tg00IIj3?Tg0204R0f0R1g02B?R23?p=3g00CV#0#0#0#0#0#0#BR3#<R41844R5#AP0P2f2R6=136R7,21A;441R8f4513A:441R9f3R:513'2X15f1R;555R<'4#3X00P0P21221/4<#3X001902A13;;173;E6P71736E6A138:A1396'2X15P4P4P6P;C@==51R1555#3eA>16;#3eW3X44W2o"). Qed.

Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01ph11Hh21ah31bh41lh51np;1p;2p;3p;6g00?]j10Tg00@Bj1@Tg00@`j1;Tg00ACj28Tg008kj1?Tg05]]j36Tg0262j34Tg01mTj31Tg026Oj33Tg024Xj25Tg0256j29Tg05^Sj1:Tg026lj37Tg005Cj6>Tg01V=j3=Tg00IIj3<Tg0204R0f0R1g02B?R23<p=2g00CV#0#0#0#0#0#0#@R3#;R4/84R5%?5f2R6f1R7561#2P0P2f5R29444f4R8513A3442f3R2513'5/91#2X30A4448=132A3448=136'5#:A4441=138A3441=132'5X05R3=757P1E>A=587R89753#2eA6826#2eW1W4X54X24W0o"). Qed.

Lemma map_contains_head : forall (a sz lo n : word) l,
  bv_unsigned a <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains ((a, sz) :: l) lo n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01bh11ph22H1h32H2h41ah51lh62loh71nh82szp;1p;2p;3p;4p;6g00?]j14Tg00@Bj1FTg00@`j1@Tg00ACj2>Tg008kj1ETg00Z8j20Tg02TVj23Tg023^j25Tg023Aj21Tg024Xj26Tg0262j3=Tg026Oj3<Tg026lj37Tg0256j2;Tg00C<j2DTg03kaj29Tg02Vjj48Tg005Cj6:Tg01U]j4CTg01V=j3BTg04:ij3ATg00IIj3?Tg0204R0f0R1g02B?R23?p=2g00CV#4#4#4#4#4#4#FR3#@R41>44R5#Ef4R6,03R7f2R8,03R9'3f3R:,03R;/59f5R9,03R</57R='3P0P2f7,03R>f6R?,03R@'5RA,1=RB,61A=441,03RC/1@15@<RDA<441,03,5CR3'1'6X15=75:RE';#2X00P0P21621/;E#2X001D02157;R;/1DR2%2213=A[13;D%2B[19;DP1C8E:11@7R1%2113><[13@711><#2[19@7f1C8E:11C<11=3'6X15P4P4P?P9CC=B58R8575#2eAA86:#2eW3W2W5X74X64X84W4o"). Qed.

Lemma map_contains_cons : forall p (lo n : word) l,
  map_contains l lo n = true -> map_contains (p :: l) lo n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01ph11Hh21bh31lh42loh51np;1p;2p;3p;6g00?]j12Tg00@Bj1BTg00@`j1;Tg00ACj2:Tg008kj1ATg04:ij39Tg0262j37Tg00Z8j20Tg023Aj21Tg023^j23Tg026Oj35Tg024Xj26Tg0256j2@Tg05^Sj1?Tg026lj38Tg005Cj6<Tg01V=j3=Tg00IIj3>Tg0204R0f0R1g02B?R23>p=4g00CV#2#2#2#2#2#2#BR3#;R4/:4R5%A5f2R6f1R7591#4P0P2f5R29744,03R8f4R9,03R:'1f3R;,03R<,3:R=A5442,03,38'1'6/@1#4X20A7449,03R0/1<1036,3<A5449,03,30'1'6#?A7441,03R0/1:A5441,03,30,1='6X05R==857P1E<A=597R9985=#4eA99;6#4eW1W3X54X44W0o"). Qed.

(* [comment removed for export] *)
Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01ap;1p;2g00?]j10Tg00@Bj16Tg00@`j12Tg00ACj21Tg008kj15Tg00_Yj14Tg00C<j23Tg00CV#0#0#0#0#0#0#6#2R01100R0#5%40'3W0o"). Qed.

Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01ph11ah21bh31lh41np;1p;2p;4p;3p;6g00?]j10Tg00@Bj1?Tg00@`j1;Tg00ACj28Tg008kj1>Tg02Ulj14Tg01U]j46Tg0262j3:Tg01mTj32Tg00cij31Tg01V=j35Tg00IIj33Tg00C<j29Tg05\aj2=Tg005Cj6<Tg02<Ij27Tg00CV#0#0#0#0#0#0#?R0#;R11811R2#>R3g0204R4g02B?P4P3f0R5#4P1P1f3R6f2R7C6A:115R8f4520#4X02f1R9512R:552P:n0100000020000=33:X24A2086#4X02R8=125R6,93A20771=07E<P1P1P7P9C6=525R99128=336e17971757533eW3X41W1o"). Qed.

Lemma map_remove_skip : forall (b s a : word) l,
  b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01bh11ph21Hh31ah41lh51sp;1p;2p;3p;4p;6g00?]j10Tg00@Bj1@Tg00@`j1:Tg00ACj28Tg008kj1?Tg00IIj32Tg01n`j1;Tg02Ulj14Tg01U]j46Tg0262j39Tg01mTj35Tg00cij33Tg01V=j31Tg00C<j2>Tg01o9j4=Tg005Cj6<Tg02<Ij27Tg00CV#0#0#0#0#0#0#@R0#:R11811R2#?R3f3R4f1R5521#;g0204R6g020TP6P3f0R7#4P1P1f5f4R8C6A9117R9=508#4X12f2R:532R;512R<P;n0100000020000=23<X06P1P1P8P4C6R6A5094#4X12R9=325512R4,>3A508:P0P8P:P7C=E<A1265R79329=234e177:175:9126523eW2W4X31X51W0o"). Qed.

Lemma map_remove_notin : forall l (a : word),
  (forall b s, In (b, s) l -> b <> a) -> map_remove l a = l.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h01lh11ah21bi001bh31sh41Hh53Hinh62IHh72b'h82s'i011pp;1p;2p;4p;3p;6p;5g00?]j13Tg00@Bj1ATg00@`j1;Tg00ACR0j29Tg008kj1@Tg01U]j44Tg04aLj31Tg00IIj30Tg01n`j1:Tg02<Ij25Tg00_Yj18Tg00C<j26Tg01V=j32Tg01?Aj3?Tg005Cj67Tg00:Aj3>Tg05_1j5<Tg05Y]j5=Tg00CV#3#3#3#3#3#3#A#;R1/91R2#@R3P2P1P1f1R4f0R5C4R6f3R7512f2R8=017#:R9[^31^211584=038[^11R:X03%82R;9126P9[^31^21163;W4X11P0P1P1f5R0f4R;5229126P9[^31^21A22;7R</54=03<[^11\:^03P5P1P1f6R<P0C4R==22;R>9126P9[^31^21P3P1P1P0P;C4R91574R?522A035>X03P3P7A22=5=03>X03A2297R>,63P?P8P4A1260P7P8P4P1P1f8f7C4P1P1P8P4C4R8502A128<;?5O3W5X81X71O2E715>4P0P;P4P7P5P0P;A0299A129716293>O3D<E7W4X11X6:X03X31X21P4P5O2n2001101010121100100X12P5D=W0o"). Qed.

(* [comment removed for export] *)
Lemma disjoint_base_ne : forall (lo n b s : word),
  0 < bv_unsigned n -> 0 < bv_unsigned s ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  b <> lo.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h02Hdh14__p1h24__x1h34__x2h44__x3h51bh61Hh72Hnh82Hsh97__arithh:4__ffh;8__varmaph<5__with=2loh>1nh?1sp;1p;2p;3p;4p;7p;6p;8g00?]j12Tg00@Bj1RTg00@`j1CTg00Z8j20Tg02jZj28Tg009Kj24Tg00IIj39Tg00_Yj1ATg008kj1@Tg02l4j2:Tg03A:j4=Tg02lRj1<Tg02m0j1QTg00iHj1PTg02n>j26Tg03X2j3;Tg02naj43Tg05`1j7MTg01Z]j1LTg02m[j2KTg03Z0j6BTg0300j2DTg00C<j2ETg030Rj2FTg031>j3GTg031]j4HTg005Cj7ITg01n`j1JTg023^j2?Tg02TVj2>Tg03AXj7NTg03B<j8OTf2R0f1R1'?f0R2'>p=1P1g03DMR3g03DlR4P4g03ELR5P2g03ElFNp=5f3R6P3P4P4P5P0P1P2GOp=7g00CVR7#2R8#2#2#2#2#2#RR9#CR:g0214R;1090R<'81091,8;f5R=,09R>f4R?,09R@1096RA31A1A<>'4f6RA99:?R<P:f7RBf8,09RC109BRB1092RD31A1D>C'4g021RRD]0X5:109AR>=1BBA1B@B'4p-0RBg00YZR@g03G=RE#A%@EP@1:@0P11:@6C=%<@%Q@R6P6P3P4P4P5P@%P7,6@RE16@7R75;@g03J_RFPEC3,56P@16@8R89;@EPFPEC3,56FM%L4REP6P@1K@;RFg03GiRGP8C3,56PEP6P@PFPGP7C3,56PEP6P3P4P4P5P=EBC7C7C71D65P2P0g0204R6g02B?R5'E1F20=965dAG@;1CHb:b;b<X2@X3@W4W1A1020A1010'418;0R;PA\;[[^2@^3@^4@^1BP2PDf9,09P>PCP1P?P=O7b9W0P=P2P1FIW6%J<eW0W8W7X?:X5:X>:W=o"). Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01ah11lh21np;1p;2g00?]j10Tg00@Bj18Tg00@`j12Tg00ACj21Tg008kj17Tg00Z8j26Tg05PAj13Tg023^j24Tg00C<j25Tg00CV#0#0#0#0#0#0#8R0#2R11111#7g00YZf1,60f0#3'4'5W1X21W0o"). Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h02l2h12l1h24__x1h34__x2h44__x3h52IHh67__arithh74__ffh88__varmaph95__with:1ah;2a0h<1lh=1nh>1zi001bi011pp;1p;2p;3p;4p;7p;6p;5g00?]j13Tg00@Bj1LTg00@`j1ATg00ACR0j2=Tg008kj19Tg006lj34Tg05PAj11Tg023^j20Tg00IIj32Tg00_Yj1:Tg00C<j27Tg01V=j38Tg00Z8j2<Tg02l4j2;Tg03A:j4KTg02lRj1JTg02m0j1ITg02n>j26Tg00iHj1HTg03X2j35Tg02naj4CTg03AXj7BTg0300j2@Tg030Rj2DTg031>j3ETg031]j4?Tg005Cj6FTg01U]j4GTg05Y]j5>Tg00CVR1#3R2#3#3#3#3#3#LR3#AR4/=4R5#9R6P5g00YZR7f1R8f0R9545#1%18R:%19R;'032^06R<X16%:5#1/0;,77X06P0P4P4f3R0f2R=585R>=459#1%1>/0;527^06\<^<6P9P7%1=/0;f4R>,<3R3/09%10R?,03/0:527X>7g03G=R@#:%9@P71;7=P81;70CK%J7%I7R@g03DMg03DlRAPAg03ELRAP71671RB1672R2%H1,67R1557557g03HPA57B2=571CCg03ElFB1@@AP9P=g0204RAg02B?R@'71D9==2A@dg0214=E78C?b7b8b9X27X37X47108=,091098/0=527^27^37^47P9P:P?P3O3b6A45=9#1P8P9O1EFP4P4P>P0CG=85=R==459#1%1=/0;527eX06X5<X16X=4X:4P8P9O2n2001101010121100100X;5P9D>W1o"). Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h01lh12Hah27__arithh34__ffh44__p1h58__varmaph65__with74__x1h84__x2h91Hh:2IHh;6__sat0h<6__sat1h=1ah>2a0h?1ni001bi011pp;1p;2p;3p;4p;6p;7p;5p;8g00?]j11Tg00@Bj1_Tg00@`j1LTg00ACR0j2ETg008kj1@Tg05PAj12Tg00_Yj1;Tg03@\j1HTg02lRj1FTg02m0j1DTg02m[j2CTg0300j2\Tg00C<j2VTg030Rj2UTg00IIj3TTg031>j3QTg031]j4MTg02TVj2<Tg01V=j36Tg03Snj1KTg00Z8j28Tg00imj19Tg03SQj2GTg02jZj23Tg00_>j2:Tg03Thj2ITg03UPj3JTg00nJj1?Tg03V4j27Tg03V]j3>Tg03WFj2NTg02l4j2OTg03A:j4PTg02n>j2=Tg03Z0j6BTg03c]j7RTg01Z]j1STg03X2j3^Tg023^j2]Tg01U]j4[Tg05Y]j5WTg02naj4XTg03AXj7YTg03B<j8ZTg0214R1f0R2'<p=0g00YZR3f1R4g03J_P2CXp=4P4g03DMR5g03DlR6P6g03ELR7P2g03ElFYp=5f3R8P5P6P6P7f2R9P4P2GZp=Ag00CVR:#1R;#1#1#1#1#1R<#_R=#LR>/E>R?#@R@P?%22#0RAX0@g03G=RB#;RC%@BRD%H3RE%F3RF%D3RG1C31RH/4H'51\G7RIP2P9g0204RJg02B?RK'V1U29=TJKdAQ314CMRKb3b5b61<11P2b2%;?#2#0eP0P>P>A6?94#2#0\A^0@P2%K918=9R0#0%9;RJ%9<R<'GRL,30':1IJ<131J%0<131L[[%0JR1g021oR0AJJ<4UW1%0L\0^11p-0R1g019aR0#?R<#?,73173<17305>35>3g03eL'N=6BCPDP31O39P4PECPPFPGPGP5P6P6P71=3:R:,4H,5GPGP5P6P6P7f4R7EBFR%S6R6PG1=3;R;,4H,5GP6A^3:;,4H,5GCACAPIPKb3b5b6X73X83W4%02/:9%091]98#0[[^73^83^41P2f6,8=R=/3Lf5#2P=P8P7O5b2b;b<b9P>P>P8P9C[=6?4#2#0eX:AX0@X?>X=>P4P2O2n2001101000121100100X>?P2DWW0o"). Qed.

Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h01ah14__x1h24__x2h34__x3h41lh57__arithh64__ffh78__varmaph85__with91pi001ph:1Hh;2H0h<2Hah=4__p1h>6__sat1h?6__sat2h@2IHhA1bi011bhB2b0hC1sp;1p;2p;3p;4p;6p;7p;5p;8g00?]j14Tg00@Bj1eTg00@`j1VTg00ACR0j2NTg008kj1ITg02<Ij25Tg05PAj11Tg00_Yj1FTg03@\j1STg02lRj1MTg02m0j1KTg02m[j2JTg0300j2cTg00C<j2\Tg030Rj2ZTg00IIj3YTg031>j3XTg031]j4WTg02TVj20Tg01V=j33Tg01mTj39Tg02Ulj1:Tg01U]j4>Tg0262j3UTg00cij3=Tg03Snj1RTg00Z8j2<Tg00imj1DTg03SQj2LTg02jZj2;Tg00_>j2CTg03Thj2OTg03UPj3PTg02l4j2ETg03A:j4QTg02n>j2ATg00iHj1TTg01Z]j1dTg03X2j3BTg023^j28Tg00nJj1HTg03V4j2@Tg03V]j3GTg03WFj2bTg03Z0j6aTg03c]j7[Tg05Y]j5]Tg02naj4^Tg03AXj7_Tg03B<j8`Tf1R1#1f0R2'0p=2g00YZR3P1g03J_P2C^p=7P1g03DMR4g03DlR5P5g03ELR6P2g03ElF_p=6f3R7P4P5P5P6f2R8P1P2G`p=?g00CVR9#4R:#4#4#4#4#4R;#eR<#VR=/N=R>#IR?P>1512%11'2^0=R@X4?g03G=RA#FRB%IARC%S3%M3RD%K3REg0214RF,J3RG/7G'61cE6RHP2P8g0204RIg02B?RJ'\1Z28=YIJdAX3F1CWRJb6b7b810FFP2b5%F>RK/52%1K'2eX0=P0P=P=A3>78R0/52%10'2^0=\@^4?P2f4R0=9<2#:PIPIPIP?P2P=P=f6RIf5RKC>RLAU==2RM=9<7#:X9>==>0RN53>PNn0100000020000A3>L0#1'2P2P8P1O1RL1571%17RN'2RO%RKRP1<<KRQ,0F%D:RR%D;R;'LRS,;Q'CRQ1OR;RT1;FR10F;1;FS[[RU10FRRVg021oRWAPR;1UW<R;10FS\W^<VRVPBPCP31E38P11E37CQRWPDPE1A3:R:%T9,A3RR'7,6E%d5RX1A39R9=B3:AB39R'7,6EC?PHPJb6b7b8X13X23X33101818181817'0[^13^23^33P2f8RY#1RZ15YI#1RYf9,<<RIP0O4b5b>b?b;b:1<<0R[A9<M8#:X9>==>7R\#1R]'818[NR['0eP=P=PKP0C>RN=3>\A3>N7#1RN'2ePLPOPPPQPTPUP;PVp-0RVg019aR;#HRU#H,@31@3U1@3;5G35G3g03eL'b=3ABPCPWPDPEPEP4P5P5P617G:,6EPEP4P5P5P6PKEaF[PXPE179R,6EPXAB3:R,79,6EC?C?PHPJb6b7b8X13X23X33W=10F1/C710171870,08[[^13^23^33^=VP21;ISPZPIPYP7P0O6b5b>b?b;b:10][e10]Nen0110101020101bBA9<M1#:X9>P=P=P0P7C>=3>8R85=>%18R7'2e1582/27eX0=X@@X4?XC=XA=P1P2O2n2001100000121101101X0>P2D]W4o"). Qed.

(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h02hih12lop;1p;2g00?]j10Tg00@Bj16Tg00@`j12Tg00ACj21Tg008kj15Tg00_Yj14Tg00C<j23Tg00YZR0g00CV#0#0#0#0#0#0#6#2R1/11R1#5%41'3X00W1o"). Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01ah12hih21lh32loh42szp;1p;2p;4p;3g00?]j10Tg00@Bj18Tg00@`j12Tg00ACj21Tg008kj17Tg05`Uj46Tg00alj33Tg006lj34Tg00C<j25Tg00CV#0#0#0#0#0#0#8#2R0g00YZR11100R2#7R3f4f3f2R4f1R5C6f0?345542,53W2X11W3X40W0o"). Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h02hih12l2h22loh31lh42l1h52IHh61ah72a0h82szi001bi011pp;1p;2p;3p;4p;6p;5g00?]j12Tg00@Bj1?Tg00@`j1;Tg00ACR0j28Tg008kj1>Tg006lj30Tg00alj31Tg00IIj33Tg00_Yj1:Tg00C<j24Tg01V=j36Tg05`Uj45Tg05aOj49Tg005Cj67Tg01U]j4=Tg05Y]j5<Tg00CV#2#2#2#2#2#2#?#;R1/81R2#>R3P2g00YZR4f3R5f2R6502f1R7f0R831A1578A1678R9502533^04]2^13R:X43%:2?178=029,43X04X24X13P0P1P1f5R0f4R;562R<=026?178A1<78=029533^04^24^13\:^33P8P3A1;78R<=029R=f7f6R>P6P7C5R?=028A1067902?A1567502R?533X33P3P>P0P7P8C5R@=02<=029RAA338?X33143AA02@=P2P@P<P9C9E7A02;6?178P5P6P7P8O3E7P1P1P>P0C==62;R;=026?178A1;78=029533eX04X24X13X5:X43X81X61P7P8O2n2001101010121100100X72P8D<W4o"). Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01bh12H1h22H2h31ah42hih52loh62szp;1p;2p;4p;3p;6g00?]j11Tg00@Bj1GTg00@`j1BTg00Z8j24Tg02TVj20Tg023^j27Tg00ACj2CTg008kj1ATg03<^j2:Tg05amj2@Tg00Zbj26Tg01U]j48Tg00_Yj1?Tg01V=j3>Tg024;j25Tg05bJj2FTg006lj3<Tg00IIj32Tg00C<j2ETg02VJj2;Tg02Vjj4=Tg005Cj69Tg05`Uj4DTg0204R0f0R1g020TR232p=3g00CV#1#1#1#1#1#1#GR3#BR4g00YZR5f1R6f3R7,43R8'0f4R9,43R:/78/06P0P21C44R8#AR;P0P;P1P4P4f6R<f5R=,43R>143<R<,:9'@,63C8%?8R?5>8P?n0100000020000P0P;17<>R@,57RAP4P41F<7RB,631:@B,63C8=>8?R3P?n01000000200005<8;2?X00P0P2P0P;P1P3P?n01000000200009<8?=2;?X001E;?f2R017>:R:'5R8%3810@7[10:0%3A[1;0:P1C=E915>7R1%31109<[107>15<9#3[1;>7P6C=E9P=P9P7P0CD=2;?eW2W1X45W5X64W3o"). Qed.

(* [comment removed for export] *)
Lemma iv_subtract_self : forall (a sz : word),
  iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h61ah72szp;1p;2p;4p;3p;6p;7g00?]j10Tg00@Bj1HTg00@`j1;Tg00Z8j21Tg023^j27Tg00_Yj1@Tg008kj1<Tg02l4j24Tg02lRj19Tg02m0j18Tg02n>j22Tg02naj45Tg0300j2GTg00C<j2FTg030Rj2ETg00IIj3?Tg031>j3=Tg031]j4>Tg02TVj26Tg03@\j1ATg03A:j4BTg03X2j3:Tg05bgj6CTg03AXj7DTf1R0g03DMg03DlR1P1g03ELR1f0R2g03ElFDp=3g00CVR3#0R4#0#0#0#0#0#HR5#;R6P0P21150R71152,77g00YZR8g03G=R9#@R:%<9R91480%98R;%88R<P81283R3g03J_R=P3C5'31G<1R1P2f2R>g0204R?g02B?R@'F1E2>=??@dg0214==80C>R@b2b3b4W01622^08P2115>R5O1b1P:P9P8148>P0%A8CBP;P812849:83R3P=P3C5,3<P1P@b2b3b4X08X581720R0/60^08^58P2P7P5O2b1ECX76W6o"). Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with71bh82Hdh91zh:4__x4h;1Hh<3Hlhh=3Hszh>1ah?2hih@2lohA2szp;1p;2p;3p;4p;6p;7p;8g00?]j1?Tg00@Bj1lTg00@`j1aTg00Z8j2;Tg02jZj29Tg02TVj20Tg023^j23Tg009KR0j2`Tg00ACj2]Tg008kj1PTg024;j2<Tg03<^j22Tg05amj2FTg00_Yj1WTg05bJj2JTg00Zbj2:Tg006lj3=Tg00IIj31Tg02l4j2LTg03@\j1bTg02lRj1_Tg02m0j1^Tg02n>j2BTg03X2j3@Tg03ZTj3QTg02naj4HTg0300j2\Tg00C<j2GTg030Rj2[Tg031>j3ZTg031]j4YTg05ckj1NTg005Cj65Tg003lj6XTg01Z]j1kTg05dij3jTg03kAj2UTg00nJj1OTg03V4j2ITg03V]j3TTg03WFj2iTg01V=j3KTg02m[j2hTg00iHj1gTg02Vjj4ETg02VJj2STg05eHj3fTg05`Uj4eTg01U]j4RTg03A:j4dTg03AXj7VTg03B<j8cTf6R1f5R2f4R3f3R4f2R5f1R6':CRf0R73Kp=8P3P4P5P6CR=K27p=7g00YZR8P5P6P7Cdp=>P6g03DMR9g03DlR:P:g03ELR;P7g03ElR<FVp=Dg0204R=g02B?R>717p=AP5P9P:P:P;P8P6g03J_P7CHP<FVp=6P4P9P:P:P;P5P6P7Gcp=4P8P6g03GiP7CHp=Mg020TR991=7p=Cg00CVR<#?R?#?R@#?#?#?#?#lRA#aRBg0214RC1;A5'91056RD1;A2RE,051;A3,3E/04'`P01;A1R0,04130E/031]BBRE#PRFP=PFf7RG,;ARH/<2PEPBPBPGPA122H,F0%WERIF8PIn0100000020000P=PF13H0R0,<3PEPBPB1JH3RJ,:APA120JPIF8PIn01000000200005=EPEPBPBPGP1PIE731P7103HP=P9P=PFP7PEPBPBf9RJPAf8RK,;ARL1;AJRM,2G'FPIF8RNPIn0100000020000P=PF13MLRO,<1RPPEPBPB1JM1RQ,:APA12OQPIF8RQPIn01000000200005=EPEPBPBPJPKPIE7RR51FX7=RSP=P>P=PFP7PQPIn0100000020000RQ9=EI=1FRX7=P8PLPEPBPB1:A7RTPA12O7PIF8=1FRX98PBPKPEPBPBP7PA12OMRUPIF8=1FRX7Bg03G=RV#WRW%PVRX1L85RY%b8RZ7>6R[%_8R\%^8R]P81B8<R^g03HP1B8?R?=@8^=Q8?CH'D1\];R;P7P51G=>1[75#AdAZ8C6CYR_b4b5b6X08X181367/269187^08^18P7PMPLO2b313LHR`/2L918HP8PLPEPBPBf:RaPTPIE7PEPBPBPaPJPIE7Rb51FX98PBPKPEPBPBPaP7PIE7=1FbX7B1GFR1:ALRb%NKRaE5PUP7EXb;PbPaE51JL2RaPWPXP[P\P]A6]^?R[%k:R:P[C4P;P_b4b5b6X08X181076Rb1065[^08^18P7PMP1P6O3b39jL2E5PEPBPB1:AaPA12`aPIF89=EIPEPBPBPKPGPIE7Ra51Fe1<2`RU%AU191O[192`%AP[1U2`g019aRc#ORd#O,I81I8d1I8c5T85T8g03eL'i=KVWRVPX1L84Rc9>Y6RYP\P]P[P:P]1h8C%g<,B8R<'M,D]RdP:A@8?<,M^,D]C4C4P;P_b4b5b6X08X18X2819C4RC1343,95[\b^08^18^28P7PLPMP1P6P2O5b3CEE51<L1Rb%Cb10GM[101L1<MGRe#C[1SL1PVPXA>c5Z?>6ZP\P]1B8@R@=6]?P:P]A6]^@P:P[C4C4P;P_b4b5b6X08X18X2810641054[\D^08^18^28P7P1PMPGP6P3O5b3CEE5W8P7O11002P=P>PSP=P9A=ENQ=1FRX7=P8PHPEPBPBPJPTPIE7=1FRX98PBPGPEPBPBPJP7PIE7=1FRX7B1GFa1:AH%NGE5121LRR,FHRJPWPXPYP\P]A@8<^=6]?P:AQ8?<96]^C4P;P_b4b5b6X08X18X281357/061254,06[^08^18^28P7PMPGPLP6O4b39fHRE5PEPBPBPKPAPJPIF8==EI=1FaePU%CU10O1[10`2%CP[1S2`PVPX1L83?>5Z?>6cP\P]A@8^?Rc=6]@P:P]A6]@<P:A6]c<C4C4P;P_b4b5b6X08X18X28X:81376/0410341354/03[[^08^18^28^:8P7PGP1PLPMP6P3O6b3CEE5Pb%Ab19MG[19L1%Ae[1UL1PVPXPYP\P]A@8^<=6]?P:P]PdP:1M^?,D]C4C4P;P_b4b5b6X08X18X281375/061954\C[^08^18^28P7PLPGPMP6P2O5b3CEE5W8P7O1n200100001021100011000P1P2P3P4CePEPBPBP1P2PIE751FeW8W<W=X?8X@8XABW>o"). Qed.

(* [comment removed for export] *)
Lemma iv_subtract_suffix : forall (a sz : word) (lo hi : Z),
  bv_unsigned a < lo -> lo <= bv_unsigned a + bv_unsigned sz ->
  bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [(a, Z_to_bv 64 (lo - bv_unsigned a))].
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h04__x1h14__x2h24__x3h31bh42H1h52H2h62H3h77__arithh84__ffh98__varmaph:5__with;1ah<2hih=2loh>2szh?1zp;1p;2p;4p;3p;8p;6p;7g00?]j13Tg00@Bj1[Tg00@`j1TTg00Z8j27Tg02jZj2;Tg023^j26Tg02TVj22Tg00ACj2STg008kj1BTg03<^j28Tg05amj2ATg00Zbj21Tg01U]j44Tg00_Yj1ETg01V=j35Tg024;j29Tg05bJj2WTg006lj3=Tg00IIj30Tg00C<j2DTg02l4j2CTg03A:j4VTg02lRj1RTg02m0j1QTg02n>j2<Tg00iHj1OTg03X2j3NTg02naj4?Tg01Z]j1LTg03ZTj3KTg03B<j8JTg0300j2ITg030Rj2MTg031>j3HTg031]j4PTg05egj3GTg005Cj6>Tg02VJj2UTg02Vjj4FTg03kAj2ZTg05`Uj4YTg03AXj7XTf1R0g03DMR1g03DlR2P2g03ELR3f0R4g03ElFXp=@g0204R5g02B?R6704p=:g00CVR7#3R8#3#3#3#3#3#[R9#TR:g00YZR;f3R<,79R=/;0f2R>f4R?,79R@/6='2f5R=,79RA/6@/2>P5P61S::R@#BRBP5PBP4P:P:f7RCf6RD,79RE179CRF,8=RG'A,19C4%E@RH55@RIPHn0100000020000P5PB16FERJ,9?RKP:P:1WF?RL,1918JL,19C4=5@HRLPHn01000000200005=@P:P:PC119GC4=5@HRG30X35P5g020TRMP5PBP4PLPHn01000000200009=@I=0BGX35P;18?ERIP:P:PC1194C4=5@H=0BGX?;P:P:PD119IC4=5@HRG,DB1AAIRCg03G=RL#E%BLP;1C;>P01C;<CV%R;%Q;RLP1P2P2P3P;1<;7R1g03J_RN1<;8R8%O7,<;R75N;C?,@L%L2P;AK;18PNP7C?,@LGJ1IL3P4P>1D561M4>#:dg0214=H;0CPb8b9b:X0;X1;X2;160>,24180>/2<[^0;^1;^2;P4PEPFP=P>O4b79GAIE>P:P:PD119CC4=5@H==@H=0BGe16EARA,9<RHA05HM12J?[12A<A05KM[1U<AP4CFE>19E?R4%:41;F=[1;E?19F=#:[1ZE?P>CFE>PDP=P?P<CY=0BGeW6W5W4X<;W=X>:W;o"). Qed.

(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h04__x1h14__x2h21bh32H1h42H2h52H3h67__arithh74__ffh88__varmaph95__with:1ah;2hih<2loh=2szh>1zp;1p;2p;4p;3p;7p;8p;6g00?]j16Tg00@Bj1XTg00@`j1STg00Z8j27Tg02TVj22Tg023^j2=Tg02jZj2<Tg00ACj2RTg008kj1>Tg03<^j24Tg05amj2GTg00Zbj20Tg01U]j43Tg00_Yj1CTg01V=j35Tg024;j28Tg05bJj2BTg006lj3:Tg00IIj31Tg00C<j2ATg02l4j2VTg03@\j1UTg03A:j4QTg02lRj1PTg02m0j1NTg02n>j2?Tg02naj4LTg03AXj7KTg01Z]j1HTg03B<j8ITg0300j2JTg030Rj2FTg031>j3MTg031]j4ETg05fFj3OTg005Cj6;Tg03kAj2DTg02Vjj4@Tg02VJj2TTg05`Uj4WTg0204R0f0R1g02B?R231p=9g00CVR3#6R4#6#6#6#6#6#XR5#SR6g00YZR7f1R8f3R9,75'2f4R:,75R;/28f2R<f5R=,75R>/=;'<P0g020TR;1R66R?#>R@P0P@P1P6P6f7RAf6RB,75RC175ARA,4='G,05C3%C?RD55?PDn0100000020000P0P@1=ACRE,8:RFP6P61BA:RG,0514EG,05C3=5?DRGPDn01000000200005:?P6P6105:14E:,05C3=5?DRH31X20P0P2P0P@P1PGPDn01000000200009:?D=1@HX20P7P9P6P6105114E1,05C3=5?D=1@HX>7P6P610591=C>R>/49,05C3=5?DRH,A@1BC9RGg03G=RI#C%>IP71V7<P8%U7CQ%P7%N7RIg03DMRJg03DlRKPKg03ELRLPIPJPKPKPLP71?73g03J_1?74CLg03ElFKR4%HKP4GI1JILP1P<1A021F1<#9dg0214=M78CEb7b8b9X07X171218128<[^07^17P1P:PAP<O3b69OC9E;P6P6105G14>G,05C3=5?D9:?D=1@He189>RD%9D1<:E[1<9>%9F[1D9>P1C@E;18C:R1A101;12=A[12:C18A==10;[1TC:P<C@E;PBP=P:P9CW=1@HeW5W4W3X;7W<X=6W:o"). Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sizes : forall (a sz : word) (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  bv_unsigned sz <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (iv_subtract a sz lo hi).
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h01Eh14__p1h24__x1h34__x2h44__x3h54__x4h62H1h71ph87__arithh94__ffh:6__sat2h;6__sat3h<8__varmaph=5__with>4__x5h?2z1h@1AhA2HahB1PhC1bi001bhD2l1hE2l2hF1mhG1nhH1HhI2H0hJ3HhihK3HlohL2HshM1NhN1ahO2hihP2lohQ2szhR1zp%0p&0p;1p;2p;3p;4p;6p;7p;8g00?]j1BTg00@Bk109Tg00@`j1wTg00imj1iTg03SQk202Tg02jZj20Tg00Z8j22Tg02TVj21Tg03Snj1pTg00_>R0j29Tg008kj1OTg006lj3VTg05fej33Tg05gFk407Tg00ACk203Tg026Oj3YTg024;j27Tg03<^j24Tg05amj2TTg00Zbj2;Tg01U]j4FTg00_Yj1`Tg01V=j3>Tg023^j2<Tg05bJj2PTg00C<j2dTg00IIj3:Tg03kAj2nTg05gej2mTg009Kj2CTg03Thj2lTg03UPj3kTg00nJj1JTg03V4j2GTg03@\k108Tg02l4j2UTg02lRk106Tg02m0k105Tg02n>j2ETg00iHj1gTg03ZTj3XTg01Z]k101Tg0300j2~Tg030Rj2}Tg031>j3|Tg031]j4{Tg03nTj1zTg05WZj2xTg05X;j3bTg02m[j2aTg03XUj3vTg03Y8j2]Tg005Cj6_Tg05hGj2\Tg05hhj6^Tg05iIj2uTg03X2j3tTg00:[j4yTg05`Uj4rTg03V]j3eTg03WFj2QTg03A:j4qTg03Z0k600Tg02naj4NTg03AXj7KTg03c]j7ZTg05`1j7oTg03B<k804Tg0214R1f0R2'1p==g0204R3g02B?R47:2p=Mf2R5g00YZR6f1R7;:2'9p=6Ae672p=5g03G=R8g03eLR9,Q7;>2p=jAe657/Q9=>82p=IP6P5P7P2Cqp=@P7g03DMR:g03DlR;P;g03ELR<P2J00p=hP6P7g03HPP2CNp=Af3R=P:P;P;P<P5P7P:P;P;P<P2g03ElR>FKFZp=fP6P7g03J_R?P2CNp=HP7P:P;P;P<P2P>FKp=LP=P:P;P;P<P5P:P;P;P<P7P>FKP2FZp=?P5P:P;P;P<P7P2Fop=SP5P:P;P;P<P6P7P?P2CNP>FKp=RP=P:P;P;P<P5P7P2L04p=81Q591Q79=>825>8p=WP5P:P;P;P<P6P7g03GiR9P2CNP>FKp=DP6P7P9P2CNp=[P5P:P;P;P<P7P2FZp=cA:672p=sg00CVR:#BR9#BR>#B#B#B#BR?$09R@#wRA%=5%i9RB%i?R?+02RC,05f5RD,2@/15f7RE#pRF12@ERG#=10GC'9RGPFPGg05ikp4p710RGp-0RF\2RH%O7RI%O5RJP0AV=7293=5f4RK?3=5A3K=7'9RL[A3=57A3=52'9AVK5793K=[RMAVD=593DK\LP=P5P7P2H07P2n2001000000120000000WEWDWBW@PM^EJ^DI^BH^@GP2203AARGAYAA2,2@RH/1EX7GRIP3%OGRJf:RM,2@RLf8RN'7ROPAPAPMf9RP,2@RQ14NL'T,;@CF%`GRR5>GPRn0100000020000RSP3PJ1<LQRQ,7ES00PAPA1PLERT,;@14QT,;@CF=>GRPRn0100000020000RTA3GISA3GITPOP31d32S01f;RO,2@RT/7P=:32P3f=RI,2@RS/7O=:3211HOX7GRQP3PJP7PAPAf>RUf<RV12@URW'4,TS,;@CF=>GRPRn010000002000053G]0P712@VRX/7MRY#MP01772#M1057[R010721757#MRZ[10=5\Z1n72P7n2001000000120000000XF6XG6RZP0^F6^G6R0P2PWPVP7O310WVPG11HVX7GR[PAPAf?R\12@\R\,4IR],TWR^,;@R_CFR`PRP6P^112VXR6Ra1mW]Rb10W]?6^W11]W?6^]'CR]f@Rc,2@Rd,4U,T\RUP61lB?Re101B%=?101C[[Rf%=BRgg021oRhAkB?7UWAR?%=C\h^AgRgg019aRh#JRi#JRj#JRk,G6Rl1G6jRj1G6i1G6hRh'5Ri'5Rm%`8Rn,jm3I%O8R8&086Rm1U6DRo7@51U6KRp?@=mRq7@7&066Rr&056RsPs1hsERtPs1E6:Ru%g9,E6Rv'ACfPsPs%g:Rw,E6Rx%Bw,E6Rw5X6Ry/Hv1Auy,LsC?5Ss&01;R;Ps1E69R99RsvP;ARsu9C8C81~s<R<P2P51d341}25#MdA|617C{R4b9b<b=X26X36X46X56X>6X1FA6D2=145KRy/1=?62y'C11K5115=[[^26^36^46^56^>6^1FP2fC,2@RyfBRzfD,2@R{'4'0R|P{PyPzPcP=PKPIO8b8b:b;b?b612@_PbP]PUP6PePfP?Pg%z:,x6R:%JkRk,G6RU5b6R]15lhRb%Jk,G6Rk15UiR_15jhRh,5]=W_n3I3IP81U6=R_?@5p?@7mPrPsPsf6Rm,hsR}Ps1E6>R>,AuCfPsPsAX69wR~/H>1Au~,LsC?5SsP;PsADsw9P;PsPsPs1a61R1/H>1a6B=v6@RB9Ds>C?P;PsPs1H1uADsuBC?C8C8C8P<P4b9b<b=X26X36X46X56X1FA6K25147=R~/15?62~'C10K5%=K10KC'9%==10=C'9R~[[[^26^36^46^56^1FP2P|P{PyPzP=PKPDPOO8b8b:b;b?b6,]^E_AYAA`,2@/1Oe1\G[R`E^b0b6W0g020TR^9:3Y11HMX7G,\GRYW0n0110001020100P2O1b0bCQ00P3Q011<TL,7N=:32P31<SX,7M=:32P3PJP7PAPA1PWORJ,;@1<WSRS/4J,;@CF=>GRPRn010000002000093GQ]0P71<XT,7PRX#MPZP0P2POPSP7O310OSPGP[PAPA1P\VR[,;@1<\W/4[RW,;@RSCFR0PRP6PWPa1u\VRa10\V?6[V11V\?6[\'CR[1PdIRdP6PePfP?PgAb6:j/5iR:15l:;WnP8A@p5o?@7_PrPsPsPs1[uw1Axw,LsC?1Axu,LsRw9cst5SsP;PsARs9>P;At6u9Rt=X6xR_=Rs>C8C8P<P4b9b<b=X26X36X46X56X>6X1F102K?65K1s52R>,9D'C115K1<5=/4K/1D[[^26^36^46^56^>6^1FP2fARp/1{RoPpPcP=PyP{PKPIO8b8b:b;b?b612@SPaP[PdP6PePfP?Pg15]iR]15k]AIUbn3W9IUhP81U65?@7qPrPsPsPs1[uv1Axv,LsC?Acs}w5SsP;PsADsvtP;PsPsPs1H19ADs9BC?P;PsPs1H1_ADs_BC?C8C8C8P<P4b9b<b=X26X36X46X56X1F102=?65=19K>'C1<75,0K1<=K/4DR7#=107C'9\~[[^26^36^46^56^1FP2PoPpP=PyP{PKPDPOO8b8b:b;b?b6,]WE_AYAA0,2@/1OeP`E^b0b6W0A:3X^PYW0n0110001020100P2O1b0bCCyO5b611HmX7GPPPNPEPmCr53GebIbHWLWJWKXM6XO6XP6XQAWNo"). Qed.

Lemma maps_subtract_sizes : forall l (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (maps_subtract l lo hi).
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h01pi001ph12H0h21li011lh32H1h42Hlh52Hph61Nh72hih82loh91eh:1Ah;1Hh<3Hhih=3Hloh>1Ph?2l1h@2l2hA2H2hB2IHhC1ahD2a0hE2l'hF2szi021bi031xp;1p;2p;3p;6p;4p;8p;5g00?]j17Tg00@Bj1NTg00@`j1DTg00ACR0j2@Tg008kR1j1;Tg02TVj21Tg00imj1>Tg03SQj2CTg02jZj2BTg026Oj39Tg00Z8j28Tg05feR2j30Tg00alj36Tg00_Yj1MTg05hGj2LTg01V=j34Tg00IIj32Tg003lj6JTg01nAj2ITg004fj6=Tg01U]j45Tg006lj3:Tg00_>R3j2<Tg05gFj4ETg05`Uj4FTg05jHj8GTg00:[j4HTg005Cj6?Tg00C<j2ATg05Y]j5KTf5R4f4R5f3R6f2R7f1R8C5f0R934p=3g00CV#7R:#7#7#7#7#7R;#NR<#DR=/@=R>#;R?P>g00YZR@g0214/17RA%>:%>;'C,B7R;A9==9,8<R:/16X0>RB=0>411:5X0>RCf6RD?64550>[[[^6@^7@]8REX2?%M>RF90>B1L>CW;X<;X=AX6@X7@X8@P0P=P=f7R0=4>D90>Bf8RG=4>0?64590>C[\;\A^6@^7@^8@\E^2?P9P>P=P=PGP0PDE390>BP2P>PCP>P=P=f;RCf:R2f9RBE3RH92?811:0X0>P>P=P=f<PCP2E3?6G050>RI[P9P>P=P=PBPGP0E3RJ92?FP>P=P=P2PBPGE3RK92?FP?PFP1P>p-0RFP9g021og021RRLn10110100020020000000X9?g01TAPHP9EJPL1II9b3W1P9O1W1A9==8,8<RI/1B11:CX0>=0>8A4>67P>P=P=fARLf@RMf?E352?A4>56P>P=P=fBRNPLPME352?P?P?P1P>P?P9P4P9n10110100020020100101X9?A4>45P>P=P=fCRMPNPLE3P9E=A2?5LP?P>P1P>P>P9P0P8n10110100020020100101X9?A4>D4P=P=fDR1PMC5RL=4>NP8E=A2>DLP=P=fERLP1C592>0P9P=P=fFRNPLC592>GP>P=P=fGROPNC5A2?BNRP11IM11:LX0>RI=0>C11:NX0>RCP>P=P=fKRQfJRRfIRSE3?6ON50>RT]4]5[X0>A2?GLP9PPP?POP=P=PRPSC599==,8</11A0>C811:OX0>RCP>P=P=fLRPPQPRE3fHRG;6O50>]4]5X2?P=P=PSPGC599==,8</1MA0>IGg05ikp4p710RIPF\9RF%;8RM%;7R<P3A:6899067A0567A0568'<R3[A0678A0679'<A:5789056[RUA:4679045\3P6P7P8P9CEP9n2001000000120000000W@W?W>W:PU^@<^?M^>F^:IP9P>PCPPPQPGPOCFRIA6RGORRA0>CIA0>CRPPPQPGPOPNPLP1P7GGPSPGPOPNPLP1P8O6CHO5b1PTeW4W5P2P9E?bAW3PBP9E?b3W1P9O1b3P9O1b3W1P9P7P8O3W1W4W5XE?X0>P6P7P8P9O4n200210100001020141103101000000A2?9K11:DX0>A6H0D50>[X2?PJO1P91A?KO1b1W;X<;X=AX6@X7@X8@XBEX2?XF=XC=P8P9O2n2001100010121102102XD>P9DKW2o"). Qed.

Lemma map_remove_sizes : forall l (a : word) N,
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (map_remove l a).
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01ph11Hh21Nh31ah41lp;1p;2p;3p;6g00?]j10Tg00@Bj1?Tg00@`j14Tg00ACj23Tg008kj1>Tg026Oj3:Tg00Z8j25Tg02TVj21Tg05fej32Tg0262j36Tg01mTj37Tg02Ulj18Tg00cij39Tg05kJj3=Tg05kjj6<Tg02<Ij2;Tg00CV#0#0#0#0#0#0#?R0#4R1/31R2#>g00YZf0R39:11,50R4f1'1X02f2R5522P21145X02R4f3R6A6113=706#8X02R0=926A=206P3E<1;659224eW1W2X31W4o"). Qed.

Lemma maps_subtract_length : forall l (lo hi : Z),
  (length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h07__arithh14__ffh28__varmaph35__with42hih51lh62loh71bi001bh82IHh94__x1h:4__x2h;4__x3h<1nh=1Hh>2H0h?3IH0h@1ahA2a0hB4cstrhC5cstr0hD5cstr1hE2szhF1xi011pp;1p;2p;3p;4p;6p;5p;<p;7p;Bp;8g00?]j1>Tg00@Bj1vTg00@`j1dTg00ACR0j2_Tg008kj1]Tg00nJR1j1KTg05Q:j20Tg05lJj28Tg05laR2j21Tg02TVR3j22Tg00C<j2FTg00_Yj1\Tg03@\j1tTg02lRj1sTg02m0j1kTg02m[j2NTg0300j2fTg030Rj2eTg00IIj3cTg031>j3aTg031]j4`Tg03^Jj4?Tg01V=j3HTg05`Uj4CTg00alj3PTg05m;j24Tg00Z8j2@Tg024;j2BTg03<^j2=Tg05amj2GTg00Zbj26Tg023^R4j27Tg05bJj2ETg00imj1OTg006lj3ZTg05mRj3YTg005Cj6XTg05QZR5j13Tg04T?R6j2DTg05n1j4UTg05nXj1ITg03V4j2JTg03V]j3TTg03WFj2jTg02l4j2STg03A:j4iTg02n>j2LTg00iHj1hTg04S\j3QTg01Z]j1gTg03X2j3RTg05Y]j5lTg03]<l<MTg02naj4mTg03AXj7nTg01U]j4bTg03dflBWTg03dAl<pTg03B<j8qTf3R7f2R8f1R9f0R:3P'0p=5g01RcR;g00YZR<P2P5P3g05o=R=g019aR>g0214R?P9P>P?P:M<Mp=^P<P9g03J_P:Cmp=<P9g03DMR@g03DlRAPAg03ELRBP:g03ElFnp=:f5RCf4RDP7P8P9Cb;H:p=91F<:p=;P;P<P2P5P3P=PCPDP7P8P9P:M<Mp=AP;P<P2P5P3P=P>P?P7P8P9P:M<Mp=uP;P;P;P<P<P<g05o_P5P5P5P4g060?PCPDP7P8P9P:MBWp=rP;P;P<P<P1P5P5P7g060bP8P9P:M<pp=oP;P;P;P<P<P<g061FP5P5P5P6g061fPCPDP7P8P9P:MBWp=VP7P@PAPAPBP8P9P:Gqp=[g00CVR@#>R6#>#>#>#>#>#vR5#dR1/_1R4#]R=P4P4P8P9P:C5%K>R3#KR21048'8'1^4<^6<REX5=11>>12??RF1F<?RG/^Gg03G=RH#\RI%]HRJ%t<RK%s<RL%k<RM1N<?RN/<N':1fMBRBP:P8g0204ROg02B?RP'F1e:8=cOPdAa<?9C`RPb1b2b3PFP:b0C?P4%\4RFP9P:C5104FRQ,82'1eX4<X6<P0P1P1P4AH4D7R0P9P:C51040,82'1^4<^6<\E^5=P:P;PCPDP9P:CCR0,04RRAP79:RS,04'4RTP4P1P1f6RUPCPDE9,04,82,1:X<;P;POP=1@5CRV/B9RWP4P1P1PC1@5DRX1=9V'G,65PFE9PFn0100000020000RY,04POP=17VXRX,B:P4P1P11EV:RZ,651=XZ,65PFE9PFn0100000020000RZ,04'411:2X<;PWPOPOPOP=P:P4P1P1f7RW1@5UR;1@5WRX,=7'G,65PFE9R[PFn0100000020000,04POP=17X;R\,B8P4P1P11EX8R],651=\],65PFE9R]PFn0100000020000,04'4/12P:17;V,B9R;POPOP4P1P1f8RV1@5VR\,=D,GX,65PFE9,04POP=P:P4P1P11E\7R^,6517\X/=^,65PFE9PFn0100000020000,04RF'4/12P:1122%O6R5/25R^P2P5%;5R\P2P5P\EAPIPJPKPL1N<5RX/<X,:MPBPPb1b2b3P^P:b0C?104[R[104]R]'4/12e1132%O@R^/25R_P3P^%;^P2P5P\EAPIPJPKPL1N<^R`/<X,:MPBPPb1b2b3P_P:b0C?R_14[Q/12en0110001020101b7P;POPO14QF/12P:P_14Q]/12e11>212?5R]PGP2P5P\CuPIPJPKPL1<NX,:MPBPPb1b2b3P]P:b0C?14QQ/12en0110001020100b7n0110001020101b7AZ4YZ,04AY4YZEX11R2RRePRP7P8P9O2P4PDP8P9C5104D,82'1PWPUP7P8CC,04RRP4PCP7P8C5RZ'4RY104CRQ#KR],82RN'1%3RRK%3ZRG'7R_%3QRF/7^RO,D5R;'2PYP_PRPK%;KR_PZPG%;GErPNP;P2P5P\P]PO17:^XF<PQPF%;FCoEVEA11R212K5RFPRPKP_P2P5P\EAP9CUPFP4PUPDP7C5RF104UR_,82RK'1%3FRR%3_RQ,D5RO'2R]PFPR%;RPKPOP2P5P\P_PQ%;QEVEAP9CUP]104WR]#I%3],2?P4PVPUPCC5R]#I%3],2?f;R]f:PWPUCC,04RU#I%3U,2?1J<21J<31J<>5T<5T<g03eL'j=HHIPJP<1S<8P91S<7CiPLPM1L<6R6%h@,L<RL9Q<X'<,:M%gARAPM1L<@R@/<X,:MPAAR<@6AR<L`9Q<X'<,:MC[C[PBPPb1b2b3X9<X:<X;<1D58,291295178717D^,D5'2[[^9<^:<^;<P:104]#3P4P]f9R]PVC5#3f=f<P]PVCC,04#3PDPCO5b0bDbCbBb?b>C?b8b=P4P1P1PCPDP7E9R7,04,82R2,1TeAZ40S,04AY40SEXP4P7P9P:C5/12eX4<X6<X8EX5=XE1X@1P9P:O2n2001101010121100100XA4P:DlW5o"). Qed.

Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h01ah14__x1h24__x2h31lh42IHh57__arithh64__ffh78__varmaph85__with91pi001ph:3IH0h;4cstrh<5cstr0h=1bi011bh>2b0h?1sh@1xp;1p;2p;3p;4p;5p;<p;7p;8g00?]j16Tg00@Bj1cTg00@`j1TTg00ACR0j2OTg008kj1LTg02<Ij24Tg05Q:j20Tg05laR1j23Tg02TVR2j21Tg00C<j2:Tg00_Yj1JTg03@\j1bTg02lRj1^Tg02m0j1[Tg02m[j2ITg0300j2WTg030Rj2VTg00IIj3UTg031>j3STg031]j4RTg03^Jj4CTg01V=j35Tg01mTj3<Tg02Ulj1>Tg01U]j4ATg0262j3QTg00cij3?Tg00nJR3j19Tg05QZR4j17Tg00imj1PTg023^j28Tg05n1j4MTg05nXj1ETg02l4j2aTg03A:j4`Tg02n>j2KTg01Z]j1]Tg03X2j3FTg05Y]j5ZTg03]<l<GTg02naj4\Tg03AXj7YTg03dAl<XTg03B<j8_Tf2R5f1R6'0f0R7'3p=2g01RcR8g00YZR9P1P4P2g05o=R:g019aR;g0214R<P6P;P<P7M<Gp=NP9P6g03J_P7C\p==P6g03DMR=g03DlR>P>g03ELR?P7g03ElFYp=;1467,05p=@P8P8P9P9P3P4P4f3R3g060bP5P6P7M<Xp=DP8P9P1P4P2P:f5R:f4R2P3P5P6P7M<Gp=BP3P=P>P>P?P5P6P7G_p=Hg00CVR=#6R4#6#6#6#6#6#cR1#TR8/O8R@#LRAP@146710@652@^08RBX3A13;;11<<R;1:9<RC/NCg03G=RC#JRD%LCRC%b9RE%^9RF%[9RG1I9<RH/=H';1WG?R?P7P5g0204RHg02B?RI':1V75=UHIdAS9<6CRRIb6b7b8P;P7b5CC%J@R;/4710@;52@eX08P0P8P8A5@35R0/4710@052@^08\B^3AP7A<127#>PHPHPHPAP7P8P8f6RHP:CAR0AQ887R;=<13#>X9@=?@2RJ55@PJn0100000020000A5@02,0@52@P7P5P6O1R0143610@3RJ52@RKA@@25RL#9RM10@2RN#9RO'3%7LRP%P=RQ'8RR%7NRS/8QRT'1PMPR187QX@9RRPLPP1:9PRMCDPOPTPRPNPS1:9SRRCDRUEB13LN11PSRVPLPPPMPNPSPREBP7CMRRPV10@:RS#ERN%7S,1<RSA@@H2RW#ERX%7W,1<R<PDPCP91a95P6PEC`REPFPG1K9=R=1K94R4'=,;GRW%]>R>1I9QRY9F9=AF94YRY'=,;GCHP?PIb6b7b8X19X291176R4186Q185QRQ'1[^19^29P7f8RZ,0@#7A@@ZH#7P3O3RZb5b<b;b:CCb4A<1;5#>X9@=?@3RH,0@R[#9%9JRJ'3eP8P8P:P2CAR:=5@HA5@:3,0@R:52@eP0PK13LO11PTPLPPPMPOPTPUEBPRPVPNPSPXP<PDPCPEPFPGPWP>1==Y,;GCHP?PIb6b7b8X19X29116Q\4^19^29PZb5b<b;b:CCb413[Je13[:en0110101020101b>A<1;6#>X9@P8P8P2P3CA=5@5R55?@10@5R352@e1457=2@3eX08X4BX3AX?8X=8P6P7O2n2001100010121101101X0@P7DZW3o"). Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h04__p1h14__x1h24__x2h34__x3h44__x4h52E2h62E1h72H1h87__arithh94__ffh:8__varmaph;5__with<2H3h=6__sat4h>6__sat5h?2z3h@4__p2hA4__x5hB1bi001bhC1zhD2HahE4__p3hF4__p4hG4__x6hH1mhI1nhJ1xhK1yhL1HhM2H0hN2H4hO3HlhhP6__sat3hQ6__sat6hR1ahS2hihT2lohU2szhV2z4p%0p&0p;1p;2p;3p;4p;6p;7p;8g00?]j1MTg00@Bk10>Tg00@`k104Tg02TVj21Tg03Snk10=Tg00Z8j22Tg00imj1hTg03SQj2{Tg02jZj20Tg00_>S00j26Tg024;j2=Tg00C<j2dTg00IIj3?Tg00ACk20;Tg008kj1mTg03<^j23Tg05amj2GTg00Zbj28Tg01U]j4QTg00_Yj1jTg01V=j37Tg023^j24Tg05bJj2UTg006lj3HTg03kAj2xTg05iIj2wTg05gej2eTg03Thj2sTg03UPj3rTg00nJj1OTg03nTj1qTg05WZj2pTg05X;j3cTg03V4j2oTg03@\k10:Tg02lRk109Tg02m0k107Tg00iHj1kTg02n>j2RTg03ZTj3XTg01Z]k106Tg02m[j2iTg0300k203Tg030Rk202Tg031>k301Tg031]k400Tg03XUj3|Tg03Y8j2YTg005Cj6[Tg02VJj2zTg05`Uj4yTg05PAj1}Tg009Kj2gTg03V]j3`Tg03WFj2VTg02l4j2vTg03A:k405Tg02naj4WTg03Z0j6uTg03AXj7\Tg03c]j7lTg05`1j7tTg03X2k308Tg03B<j8bTg0214R0f0R1'1p=9f1R2#}/11p=Cg0204R3g02B?R47?1p=Tf2R5g00YZR6??21'6p=Jf3R7A?652'6/g1p=A1o61p=NA`621p=5A`621g03eLR8'Vp=]g03G=R9?721p>0<A`652/V8=791p=;A79219795p=n1v61p=SP6P5P2P1H05p=<P6P2g03GiR:P1CWp=aP2g03DMR;g03DlR<P<g03ELR=P1Eup=FP7P;P<P<P=P5P;P<P<P=P2g03ElR>F\P1Flp=@P5P;P<P<P=P6P2g03HPP1CWP>F\p=EP5P;P<P<P=P2P1Flp=:P5P;P<P<P=P2P1Ftp=LP6P2g03J_R?P1CWp=PB08621p=IP5P;P<P<P=P6P2P:P1CWP>F\p=>P5P;P<P<P=P6P2P?P1CWP>F\p=KP7P;P<P<P=P5P2P1Gbp=Bf6R>P;P<P<P=f5R?f4R:P7P;P<P<P=P5P2P1GbGbp=D1652/g1p=~A?621p=^1V581V28=791579p=_g020T9?31p=Z1V28=791p=fg00CVR8#MR;#MR@#M#M#M#MRA$0>RB$04RC1121&0=:RD12B:RE#9%h;RF%hARA'{RG,0E'6REPDPE12B>/=:P31d31S01f7RE,2B/=?=?31P3f9RD,2BRH/=E=?3120;CCRIP3%mIRJP2PCPCf:RKf8RL12BKRM'3,GH,8BCQ%jIRN57IPNn0100000020000P3PJ14MHRO,=ERPPCPC1UMERQ,8B13OQ,8BCQ=7INPNn01000000200003H/CH]6P212BLRQ/=>S02#T14HQ,=>S03P3Q01A?3P1S04P3f<RP,2BRQf;RH,2BRO'4S05,=D=?31S06PCPCf=RR12BRRS,3H,GQ,8BCQ=7INP3PJP2PCPC1USKRJ,8B14SQ/3J,8BCQ=7INPNn0100000020000S075HI/CQ]5P214OM,=LS08#TS09Q001=21S0:#T1052[RM10211=52S0;#TRJ[1075S0<\J1x21P2n2001000000120000000XH6XI6RJPM^H6^I6RMP1PSPHP:O3S0=10SHS0>PJPMP1PPf?RT,2BRUf>RV,2B'4RWP7O3S0?10PWS0@P6f@RX,2BRY,3VRZ,GUR[fAR\,2BR]/4Y1U]VRV'3,8B,2B/40,41/1YXC6P614YU1UYRR^'3R_13T],GYR`1410S0A'4/1YXC61wYRRa10YRP^PR11RY?J^YCAR^PVP6fBRb,2BRc,3XRX,e]10]X1G]XRdP]11X]?JdXCAfCRd,2B,3\,GcP61sFARX100F%9A100G[[R]%9FReg021oRfArFA2UWDRA%9G\f^DeRep-0Rfg019aRg#ORh#ORi#ORj#ORk#NRl%NiRi%NhRh'5']Rm%OkS0B#NRk%q8,p6Rn=c6lRo1o6gRg,5hRp'5S0C']S0D%NjRj/5h%j9Rq-0<m5;k3n%m9R9%S:Rm%S>7<5%S?&0:6Rr7<7Rs7<2&096Rt&076RuPuPu%k8Rv,R6Rw%k;,R6Rx1R6;R;5X6Ry'a1FuLRzC@1FuD1R68R8=Euy5:u5Lu&06<R<Pu1FuK1R6@R@%Mv,R6Rv5Eu5:uPuPu1Pv;1FuHC@5LuP<Pu1I;wRy9>uvP<PuA>u;xP<PuAKuxvP<AX6y@1i60Ry'I,I8=KuwCBFDFD203u=R=P1P51d3420215#TdB01602H00R4b9b:b;X16X26X36X46XA6XG6X0fX@fXEfWF13:2Rv,05AJE1v7~>PDP:P>11>5/6KCA147:S0E,0E10:E11LD14>E/3L/40,4?/1E[[[[[^16^26^36^46^A6^G6^0f^@f^Ef^FfP1fG,2BRv,^?fDR{,0vfER|/3vfF,2BR}'11^7}P{P|P?P}PvP7P:P>PEPDPdO?b8b>bQbVbNb?b<18B_,2BS0FPaP^PVP6PXP]PAPe15jp,5lS0GAc6nkRv15igR}'5R~Q0B#O#NS0B/5~15lg=;kq3_5;kP9A<m5r?<2sS0HPtPuPuPu1a8xAEuwxC@S0I1FuES0JAEuw8S0K5:u5LuP<Pu1I8;Rs9>uxS0LP<PuA>u8@P<Pu1i6F=|6BRF9>u;S0M9:uzP<PuAKu@xP<PuPuAX6swRs,PyA>usFC@S0NCBFDFDP=P4b9b:b;X16X26X36X46XA6X0fX@f101:P5P:1^51S0O,6?CA1425R~,0?105?10:G,6D11EL14?>/3ERL#910LG'6[[[[[^16^26^36^46^A6^0f^@fP112B{R{#9S0P12B|R|,1bS0QPbPdP7P{P|P:P?PEPTP\O<b8b=b>b?b<,Y_E[18B[,2BS0R1eUZS0S10UZP[PU11ZU?J[ZCARZP`P6PXP]PAPe15jgRj15ipRU,5lQ0B15lhQ0G=;vq3;5;k5;vP9Q0HPtPuPuPuAX6;@Rv,axAEu8xRLC@Q0JAEu8vS0H5:u5LuP<Pu1I@x9>uwP<PuA>u@;S0JP<PuA>uxFS0B9:uzP<PuAKu;wP<AKuy8RzA>u8F5:uS0GCBFDFDP=P4b9b:b;X16X26X36X46XA6X0fX@f1327RF,0:P1P:AJ?1FCA14:?,0710?710EG,6D11?>%9?10?G'6RF[[[[[^16^26^36^46^A6^0f^@fP1Q0P13d|R@/1{P{P|PbPdP7P:P?PEPTP\O<b8b=b>b?b<,Y[E[b5b7b6b7PCPCPP13KQ,GO,8BCQ=7INRKPCPC1UQDRD,8BQ05/3D,8BCQ=7INS055HI/COeW5Q08#ZS08PJPMQ0=Q0>Q00Q0:#Z1125[RD1112Q0;#ZR\[1157\\1z21P2n2001000000120000000XK6XJ6R\PD^K6^J6RDQ0?11WPRWP6P[Q0A/1YXC6RYQ0SPZP`P6PXP]PAPe1fUqP9%S5A<m7r7<2RUPtPu1Fu>RPAEu8;5:uPuPuAX6wxRw/P;AEu8wC@5LuP<1I8y=Ku;CBP=P4b9b:b;X16X26X36X46X0fP:P1P21357R8/12?J18CA1420/15[^16^26^36^46^0fP110{@R@P|PdP{P7P:O6b8b=b>b?b<Q0RQ0SPZP`P6PXP]PAPe15lpRp15o}=_pq5;k9;ojP9%S7?<5rA<m:r7<2PtPuA:uPLPuPu1PvxQ0HC@5LuP<PuQ0JP<PuPuPu1PyxQ0BC@P<Q0GCBFDP=P4b9b:b;X16X26X36X46X0fP:P1P71325Rx/17?J1xCAQ0<%97107G'6Rx\F[[^16^26^36^46^0fP1P@P{P|PdP7P:PEPTO8b8b=b>b?b<,Y[E[b5b7b6b7AHIKN/COeW5n0110001020101P1O1b5bBW6Q02#ZQ03P3Q01Q04P3Q06Q079HIN/CQ]5P2Q09P\PDQ0=11HSRSPJPMQ0?Q0@P6P_PYPaP^PVP6PXP]PAPeAc6nh/5gRg15ig;_qP9PUPtPuQ0IQ0K9:uP5LuRPP<1Isy=Ku;CBP=P4b9b:b;X16X26X36X46X0f1017P5P7Q0O,6:CARs13~7/40/15[^16^26^36^46^0fP1Q0QPbP7P{P|P:O6b8b=b>b?b<Q0FPaP^PVP6PXP]PAPeQ0CQ0D1]lj;nq'f9;l}P9PUPtPuPPP<PuQ0LP<PuPuPu1Py;Q0MC@P<Q0NCBFDP=P4b9b:b;X16X26X36X46X0f10:~Q0E/3?R~#910~G'6\x[\s^16^26^36^46^0fP1Q0QPbP7P{P|P:P?PTO8b8b=b>b?b<,Y_E[b5b7b6b7Q059HIN/COeW5Q08P\PDQ0=PSP\PDQ0?PWPXP]PAPePqP9%S2PtPu1Fu79:uzP<PzCBP=P4b9b:b;X16X0f%91/62%92[^16^0fP110cGPcPRO3b8bPb=b5b7b6b7AHINN/COeW5n0110001020101P1O1b5bBW6n0110001020101P1O1b6bBP>P?P:P7Cy12B?'CebMbLWOXS6XT6XUCWRo"). Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h02hih11lh22loh33Hlhh42IHh57__arithh64__ffh78__varmaph85__with94__x1h:4__x2h;4__x3h<4__x4h=1Hh>1ah?2a0h@2szhA1zi001bi011pp;1p;2p;3p;4p;5p;6p;7p;8g00?]j13Tg00@Bj1\Tg00@`j1JTg00ACR0j2GTg008kj1CTg02TVj21Tg00alj32Tg05PAj10Tg00_Yj1<Tg03@\j1HTg02lRj1FTg02m0j1ETg02m[j2DTg0300j2VTg00C<j2UTg030Rj2TTg00IIj3PTg031>j3MTg031]j4LTg01V=j38Tg05`Uj4=Tg023^j24Tg00Z8j2:Tg062Ij5ITg00nJj1;Tg03V4j29Tg03V]j3BTg03WFj2KTg02l4j2ATg03A:j4>Tg02n>j25Tg00iHj1NTg01Z]j1OTg03X2j3?Tg006lj3QTg063Sj2RTg005Cj6STg01U]j4[Tg05Y]j5ZTg02naj4YTg03AXj7WTg03B<j8XTg00YZR1f1R2g03J_f0R3CYp=7P2g03DMR4g03DlR5P5g03ELR6P3g03ElFWp=6f3R7P4P5P5P6f2R4P2P3GXp=@g00CVR8#3R9#3R:#3#3#3#3#\R;#JR</G<R=#CR>P=1123R?A2742#0%07'1[^01^21R@X1>g03G=RA#<RB%CARC%H1RD%F1RE%E1RFg0214RG,D1RH/7H'61VF6R6P3P4g0204RHg02B?RI'U1T34=PHIdAM1G2CLRIb6b7b811GGP3b5%<=RG?242#0%0G'1eX3?X01X21P0P<P<f5R0f4RG58=RH?242#0%0H'1\?^01^21\@^1>P3P1f6RHP0P4P2C=RJ#0RKA2G42RL#0'41:;H%00RM'4,13XA1PHP0P4P2P3DI1:;0,1KPGP7P4P2O3A2074#0/1Mg019aRM#;RK#;,91191K191M5B15B1g03eL'K=8ABPCP1P11A1GP4PDC>P21A17C>PEPF1518RE%N8,51R8'7,6F%O5R5PF1519R9151:R:'7,6FP5A?1E9A?18:'7,6FC@C@P6PIb6b7b8X91X:1X;1X<11134114G144714G0'1[[^91^:1^;1^<1P3f7R7#0f8RI,:;A270G#0f9PIP0PGC=#0P4P2O6b5b4b=AQ=JL#01RJLESP<P<PHP0C[=8=GRG?242#0%0G'1eX3?X01X21X4@X1>X@<X><P2P3O2n2001101000121100100X?=P3DZW1o"). Qed.

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h04mapsp;1p;2g00?]j10Tg00@Bj15Tg00@`j12Tg00ACj21Tg008kj14Tg00C<j23Tg00CV#0#0#0#0#0#0#5#2R0/10#4R0f0,30W0o"). Qed.

Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01ah14cutsh24mapsh31np;1p;2p;3g00?]j10Tg00@Bj19Tg00@`j13Tg00ACj22Tg008kj18Tg00Z8j21Tg023^j27Tg00alj34Tg05OAj25Tg00C<j26Tg00CV#0#0#0#0#0#0#9R0#3R1/21#8R2f3f2,10R3f1,10,7334f0'5,62X12X31X01W2o"). Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "p'0h04__x1h14mapsh24cutsh32Hah47__arithh54__ffh64__p1h78__varmaph85__with94__x2h:1lh;1Hh<2IHh=6__sat0h>6__sat1h?1ah@2a0hA1ni001bi011pp;1p;2p;3p;4p;6p;7p;8p;5g00?]j12Tg00@Bj1`Tg00@`j1GTg00ACR0j2CTg008kj1?Tg05OAj23Tg05PAj11Tg02TVR1j20Tg00_Yj1>Tg02l4j2<Tg02lRj1BTg02m0j1ATg02n>j2=Tg0300j2VTg00C<j2UTg030Rj2TTg00IIj3QTg031>j3JTg031]j4ITg01V=j3:Tg00Z8j25Tg023^j2;Tg00alj3FTg064Rj3ETg03Snj1HTg00imj18Tg03SQj2DTg02jZj24Tg00_>j29Tg03Thj2KTg03UPj3LTg03@\j1MTg03A:j4NTg02m[j2OTg03Z0j6PTg03c]j7@Tg01Z]j1RTg03X2j3STg03B<j8_Tg065Hj4^Tg066Tj8]Tg01U]j4WTg067Cj4XTg005Cj6YTg05Y]j5ZTg02naj4[Tg03AXj7\Tg00YZR2f1R3g03J_f0R4C[p=7P3g03DMR5g03DlR6P6g03ELR7P4g03ElF\p=6g00CVR8#2R9#2#2#2#2#2R:#`R;#GR</C<R=#?R>P=1343#1%14R?'0^1>R@X2>g03G=RA#>RB%?ARA1<23%B2RC%A2RD1=28R8/78'61VD7REP4f2RFg0204RGg02B?RH'U1T4F=QGHdg0214RH=J23CIRGb5b7b8X021044^02P4%13RIO1b4%>=,34#1/0?eX1>P0P<P<f3R0=:=F,34#1/0?^1>\@^:>P4P>f4RJ,5;RK15;0RL,;KRM5F4RN/3FRO10?IX:>P2P1g068J9E21%1O%1NP?P3PNO1P4PKPM%H010HL%89RM%8:R:'DRK,4L'91KM:14HM10H:14HK[[10HMRLg021oRNALM:3UW310HK\N^3Lp-0RLPBPAP21<2FP3%M2CNPCPDP5P6P6P7PDP5P6P6P71O2H1=29R9'7,6DPDP5P6P6P7PJEPF@%R6AS289,78,6DG_PEPGb5b7b8X02X92W610H3/9F1;3F,03[^02^92^6LP4f7,5;RL/4KPLf8,5;P0O4b4b=b>b;C^G]P<P<PJP0CW=:=F,34P4PJP0PFCXEYX1>X<@X2>XA<X?<P3P4O2n2001101000121100100X@=P4DZW2o"). Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01hp;1p;2g00SNj15Tg00RXj14Tg068oj20Tg05R:j11Tg05S8j13Tg02TVj22Tg00Faf0R0#5%40'0%10%30'2eW0o"). Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h02Hlh12Hmh21mh31zp;1p;2p;3p;6g00?]j10Tg00@Bj1@Tg00@`j17Tg00ACj25Tg008kj14Tg00Eij1;Tg00_Yj11Tg00IIj32Tg00`9j16Tg00GXj13Tg05R:j18Tg05S8j19Tg02TVj2:Tg06:?j1?Tg03>5j1>Tg06;Gj3=Tg005Cj6<Tg00E3g00CV#0#0#0#0#0#0#@#7R0/50R1#4f0R2#;%1132%40f1R1#6%1032g00YZR0f2R3#3R4#8f3#3#9,:2X30%?4%>3A=312E<W1W0W2o"). Qed.

Lemma grant_budget_intro : forall m n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h04__x1h14__x2h24__x3h34__x4h41Hh52H0h62Hlh72Hmh87__arithh94__ffh:8__varmaph;5__with<1mh=1np;1p;2p;3p;4p;7p;8g00?]j10Tg00@Bj1XTg00@`j1MTg00ACj2GTg008kj1;Tg00Eij1UTg00_Yj17Tg00IIj39Tg00`9j1JTg00GXj18Tg05S8j1:Tg023^j26Tg00V8j1ATg02TVj21Tg06<Nj3VTg03>5j1CTg00nJj1BTg03V4j25Tg03V]j3@Tg03WFj2RTg01V=j3QTg02l4j2?Tg03@\j1LTg03A:j4>Tg02lRj1KTg02m0j1ITg02n>j22Tg01Z]j1HTg03X2j3=Tg00iHj1FTg0300j2NTg00C<j2ETg030Rj2OTg031>j3PTg031]j4DTg02naj4STg03AXj7TTg03B<j8WTg00YZR0f1R1g03J_f0R2CSp=3P1g03DMR3g03DlR4P4g03ELR5P2g03ElFTp=4f3R6P3P4P4P5f2R3P1P2GWp=<g00E3g00CVR7#0R8#0R9#0#0#0#0#X#MR:/G:R;#;%U1%7;39%;:%J3%7:39%86R:#:/63%A:'1f4R:?V31%C:%8:#:'1g03G=R;g019aR<#BR=#B,50150=150<5@05@0g03eL'R%7;3Q%;;P0P01?0:P3%L0C>P11?06C>%K0%I0R;1207R<1209R9'3,4;%H4R4P;1208R89=09%F7,20R7'3,4;P4A=0<8/37,4;C<C<1N;5P2P3g0204R;g02B?R5'E1O23=9;5dg0214=P01CDb9b:b;X00X10X20X30112616:3/161636/1:[[^00^10^20^30P2f6R2#8R:#:%A:f5%C2P1P3O6b8b5W4W7W6X=0W<o"). Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h01mh11nh21Hh32Hlh45Hliveh52Hmh64addrh71lh81vp;1p;2p;3p;8p;6g00?]j10Tg00@Bj1VTg00@`j1JTg00ACj2BTg008kj1>Tg00Eij17Tg00_Yj1;Tg00IIj33Tg00`9j1DTg00GXj15Tg05S8j16Tg00V8j11Tg02TVR0j22Tg04Vgj3=Tg03>5j1<Tg023Aj28Tg03kaj2UTg064Rj3TTg00Q^j1RTg00RXj1QTg00SNj1NTg00Z8j2:Tg023^j2ITg00alj3HTg00THj1ETg00UCj1FTg00Voj1GTg00Wjj1CTg00Xcj8KTg00HOj2LTg02=Bj2ATg005Cj69Tg06<Nj3MTg06=Vj2@Tg066Tj8OTg04`@j3PTg06>Uj3?Tg04_5j3STg0204f0R1g02B?33p=4g00E3R2g00CV#0#0#0#0#0#0#VR3#JR41B44R5#>R6f2R7#7%;5R533%>4f3R8#D%;433f4R9#5R:#6%1:'2P2f5R:9=98%<1%51#1'8#4X02g00YZR2g00_>f1R;/81#4127;R<[12;1187;#4[R=1887#4\<1U;1P1n2001000000120000000X02W1P=^02^12P1f6R=9=:9R<#<R>%5<R?#1R@P2P0g068J9T20P>%6?R?P@P6%7=A3615X76P8%5=R>#R%Q>%N>1:3:R21:39,I23H%E>%F>%1>%G>%C>GKR>/L=R2#71A>=E9%7<=365e=M<7g00FaR<P>%61%11'2X8<P;%6>%1>'2e%521@>=E912?@eGOO3b2AP:98A?:98E9AS:98#4eW4W5W3X14W6W0o"). Qed.

(* [comment removed for export] *)
Lemma file_read_length_eq : forall data (off count : word),
  length (file_read data off count) = Nat.min (word_to_nat count) (length data - word_to_nat off).
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h05counth14datah21nh33offp;1p;2p;3p;6g00?]j10Tg00@Bj16Tg00@`j13Tg008kj17Tg06?\j12Tg05Q:j21Tg06@Wj25Tg06@nj24Tg00IIj3<Tg00C<j2;Tg06ANj38Tg06BCj39Tg005Cj6:Tg00CV#0#0#0R0#6#3R1#7%00#0#0#6#3R0g01RcR2f0R3#2f2R4,11f1R5#2R6'5'4R7f3,11%24'5,469<23X221;27A8453,11A9453E:X00W3W1o"). Qed.

Lemma file_read_length_le : forall data (off count : word),
  (length (file_read data off count) <= word_to_nat count)%nat
  /\ (length (file_read data off count) <= length data - word_to_nat off)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefNodes ()) [] "h04__p1h14__x1h24__x2h34__x3h42H2h52H3h67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<5cstr1h=1nh>2z2h?2z3h@5counthA4datahB1mhC3offp;1p;2p;3p;4p;6p;Bp;<p;7p;8g00?]j17Tg00@Bj1TTg00@`j1NTg008kj1KTg06?\j14Tg05Q:j26Tg06@Wj2RTg06@nR0j2\Tg05laR1j2=Tg00_>j22Tg05QZR2j11Tg03<^j29Tg05bJj2@Tg05amR3j2HTg02TVR4j20Tg00C<j2:Tg05nXj1GTg05iIj2]Tg02jZj2<Tg00IIj35Tg009Kj2;Tg05gej2[Tg00nJj1CTg03V4j2?Tg03V]j38Tg03WFj2MTg00_Yj1ZTg01V=j3LTg02l4j2JTg03@\j1YTg03A:j4FTg02lRj1XTg02m0j1WTg03Z0j6VTg02n>j2>Tg00iHj1UTg01Z]j1nTg02m[j2mTg0300j2lTg030Rj2kTg031>j3fTg031]j4eTg03^Jj4OTg02naj4ETg00:[j4bTg06ANj3aTg06CCj3`Tg005Cj6dTg03dflBQTg03]<l<_Tg03AXj7^Tg03c]j7hTg05`1j7iTg03B<j8jTg01RcR5P5P5g00YZR6P6P6g06DGP2P2P2f6R7g06Dgf5R8f4R9f3R:f2R;f1R<f0R=MBQp=gP5P5P5P6P6P6P0P2P2P2P3g06ENP8P9P:P;P<P=MBQp=cP5P6P1P2P4g05o=P8P9P:P;P<P=M<_p=PP6P<g03HPP=CEp=AP<g03DMR4g03DlR2P2g03ELR1P=g03ElF^p=3P;P4P2P2P1P<P=Fhp=IP6P<g03J_P=CEp=BP;P4P2P2P1P<P=Fip=SP:P4P2P2P1P;P<P=Gjp=Dg00CVR3#7R0#7#7R>#T#NR?#K%7>#7#7#T#NR>P5%4=R@16?;RA%4<RB'RRC'\RD1==B16?:%4;RE'R,=='2X=51=D@R51=DCRFP5%1@R5g0214RG%1ARH%1BRI'9'@RJ'HRK/05PDPKP@P51:65RLPCPJ19<=,@GXB6X=6PAPH1:6HPBPI1:6IFgRIEcRBP@P5PLEP%G@R@10G5R5%GERL%1E,0GRE16?9RH#GRA%1H,0GRH16?8#1%49#1'9R9,]GRM1<G91@G9RN=569'2109GA56NG'2';RN16?7#1%48#1R9'9,@GROP61[9=RP1<9=1H9=RQ=569'210=9A56Q='2';RQ%47#1/H<R7P6p-0R9g03G=RRg019aRS#CRT#CRU#C,?61?6URU1?6SRS586586g03eLRV'M%ZRRW3L%KRRXP61J6;RYP<P61J6:RZP:%Y6CFCF%X6R[%W6R\P\P4P2P2P1P8EV1>63R81>60R4'A,3\5I\R]%U0,>6R0/B4,3\1A80,3\5I\5S\%n2R2P\1m6G/B4,3\P21B84,3\R0CDCD1l\1R1P=P;g0204R^g02B?R_':1k=;=5^_dAf6G<CeR_b7b8b9X16X26X36W0A56=<,2:R^10;<A56=;R`'2';10G;10;:[[^16^26^36^09P=f8#4#1RG/<:P:PGP<P;f7O6b6b?b5b>b4b<b;b:COPF10KJPDPKPBPCPJPIEPP@P5PLPEPAPHPMPNPOP6PPPQP7P61?6T=86S986U/MV=LRWPXP6PYP<PZCFP[P\P6%U3,>6R3g03GiP4CE,3\1A83,3\5I\=S\]P2P0CDP1P_b7b8b9X16X26X36X091<;</2`/;^10<;[^16^26^36^09P=10:GPGP:P<P;O5b6b?b5b>b4b<b;b:COCbAa;<=,6?A`;<=EdX@>WCWAo"). Qed.

