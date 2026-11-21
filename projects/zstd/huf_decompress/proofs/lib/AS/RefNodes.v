(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (AllocSim's page_round_up_Z_aligned by qualified name; 72 recorded proofs replaced by written proofs (t_alt2_idem, t_alt3_idem, with_fds_halted' and 69 more); munmap_model_simple, mmap_noaccess_check, mprotect_check and 1 more restated for the revision's model; adds grant_ok_na_pin_unpack, grant_ok_na_of_pin, grant_ok_na_pin_of_grant_ok and 3 more; drops grant_ok_grant_ok_na; grant_ok_na redefined for the revision's model; defines grant_ok_na_pin; imports; rz_alt3 takes RomBase.sys_rob; imports RomBase). *)
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
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import RomBase.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From Stdlib Require Import Zify.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanCeil.
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
Proof. intros A tr. unfold t_alt2. tauto. Qed.

Lemma t_alt3_idem : forall A, t_eq (t_alt3 A A A) A.
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h m. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

Lemma vm_forget_range_lazy_nil : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof.
  intros lo hi m Hl. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. rewrite Hl. reflexivity.
Qed.

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

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
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

Lemma rz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs c three (fun _ => []) nx -> sys_rob segs c ->
  realizes segs (nx T1) A -> realizes segs (nx T2) B -> realizes segs (nx T3) C ->
  realizes segs c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode Hrob HA HB HC.
  apply (rz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (rz_cases segs c three nx _ T1 Hnode Hrob). intros [| |]; assumption.
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
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

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
  munmap_model a n m = with_vmmaps (mmap_fixed_destroyed_next (m_vmmaps m) a n) m.
Proof.
  intros a n m Hl Hm. unfold munmap_model, with_mmap_destroyed.
  apply vm_forget_range_id; [rewrite with_vmmaps_lazy'; exact Hl | exact Hm].
Qed.

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
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

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
  intros m d h b Hd Hb0 Hnw Hbal Hdal.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
  rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next. fold b.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  (* AllocSim's [page_round_up_Z_aligned] by qualified name: LPS 727298f3's Checks.Placement has its own *)
  rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite Hureq.
  rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Zplus_mod, Hbal, Hdal; reflexivity]).
  unfold brk_page_range. rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned b + d))) by lia.
  cbn [app maps_subtract_ranges fold_left].
  replace (Z_to_bv 64 (bv_unsigned b)) with b
    by (apply bv_eq; rewrite u64_lit by lia; reflexivity).
  replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
  reflexivity.
Qed.

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
linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
&& (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
&& hint_placement_ok_b hint (m_vmmaps m) (bv_unsigned a) n.

Definition grant_ok_na_pin (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a.

Lemma grant_ok_na_pin_unpack : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  grant_ok_na_pin hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n Hn Hnal H.
  exact (linux_place_is_admissible _ _ _ _ _ Hn Hnal H).
Qed.

Lemma grant_ok_na_of_pin : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  grant_ok_na_pin hint m a n = true -> grant_ok_na hint m a n = true.
Proof.
  intros hint m a n Hn Hnal H.
  unfold grant_ok_na_pin in H.
  destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal H)
    as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok_na. rewrite H, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    (proj2 (Z.leb_le _ _) Htop). cbn [andb].
  unfold hint_placement_ok_b. destruct (w_is0 hint) eqn:H0; [|reflexivity].
  unfold w_is0 in H0. apply bv_eqb_eq in H0. subst hint.
  exact (placement_policy_holds (m_vmmaps m) (kb_thp (m_kernel m)) a n Hn Hnal
           (proj1 (linux_place_is_iff _ _ _ _ _ Hn Hnal) H)).
Qed.

Lemma grant_ok_na_pin_of_grant_ok : forall hint m a n,
  grant_ok hint m a n = true -> grant_ok_na_pin hint m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok_na_pin.
  exact (grant_ok_place _ _ _ _ H).
Qed.

Lemma grant_ok_na_pin_of_gate : forall hint m a n,
  grant_ok_na hint m a n = true -> grant_ok_na_pin hint m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok_na in H. unfold grant_ok_na_pin.
  rewrite !andb_true_iff in H. tauto.
Qed.

Lemma grant_ok_na_place : forall hint m a n,
  grant_ok_na hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok_na in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

Lemma grant_na_pin_not_errno : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z -> grant_ok_na_pin hint m a n = true ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros hint m a n Hn Hnal Hg.
  destruct (grant_ok_na_pin_unpack _ _ _ _ Hn Hnal Hg) as (_ & _ & Htop & _).
  apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\ True.
Proof.
  intros hint m a n H. unfold grant_ok_na in H.
  rewrite !andb_true_iff in H. destruct H as [[[[[_ H1] H2] H3] H4] _].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. repeat split; assumption.
Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* LPS 727298f3: the model's own statement and proof (theories/Common/RefNodes.v): the
   decline premise, and the grant test is the placement alone. *)
Lemma mmap_noaccess_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  check_syscall (sys_input segs ms x8) eff model
  = let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
    match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)]
             then CheckOk (noaccess_model r (Z_to_bv 64 n) model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff Hno (H1 & H2 & H3 & H4 & H5) Hdecl.
  rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 34)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, noaccess_model, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma grant_na_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_na hint model a n = true -> errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg. unfold grant_ok_na in Hg.
  (* LPS 727298f3: grant_ok_na ends with the hint gate, after region_free (the model's Common/RefNodes.v) *)
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Hce]. apply Z.leb_le in Hce.
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
Proof. reflexivity. Qed.

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
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) addr n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mprotect_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
             then CheckOk (mprotect_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hvd Hna Hma.
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
  cbv beta iota zeta. fold n. rewrite Hvd. cbn [negb]. rewrite Hna, Hma. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct cs; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct ci; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  reflexivity.
Qed.

Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

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
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Lemma fixed_destroyed_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_destroyed_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

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
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

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
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

Lemma vm_backed_bytes_no_noaccess : forall h,
  vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_intro : forall m d,
let h := m_vmmaps m in
let b := vm_brk h in
(bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
(0 < bv_unsigned b)%Z ->
(bv_unsigned b + d <= alloc_ceiling)%Z -> init_sp_ok h ->
region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
(vm_backing_used m + d <= vm_limit h)%Z ->
Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true.
Proof.
intros m d h b Hbal Hdal Hd Hb0 Hce Hisp Hrf Hlive.
pose proof alloc_ceiling_val as Hcv. pose proof (u64_range b) as Hbr.
pose proof (alloc_ceiling_le_alloc_top h Hisp) as Htop.
assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok, Mmap.brk_grow_bytes.
fold h. fold b. rewrite Hureq.
rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned b + d))
by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia. rewrite Hrf.
replace (Z.max 0 (bv_unsigned b + d - bv_unsigned b))%Z with d by lia.
rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l ->
     bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof. intros. unfold map_has. cbn [existsb fst snd]. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof. intros p a n l H. unfold map_has in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma map_contains_head : forall (a sz lo n : word) l,
  bv_unsigned a <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains ((a, sz) :: l) lo n = true.
Proof.
  intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma map_contains_cons : forall p (lo n : word) l,
  map_contains l lo n = true -> map_contains (p :: l) lo n = true.
Proof. intros p lo n l H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

(* [comment removed for export] *)
Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof. reflexivity. Qed.

Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof. intros. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma map_remove_skip : forall (b s a : word) l,
  b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof. intros b s a l H. unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq _ _ H). reflexivity. Qed.

Lemma map_remove_notin : forall l (a : word),
  (forall b s, In (b, s) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b s] l IH]; intros a H; [reflexivity|].
  rewrite map_remove_skip by (apply (H b s); left; reflexivity).
  rewrite IH by (intros b' s' Hin; apply (H b' s'); right; exact Hin). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disjoint_base_ne : forall (lo n b s : word),
  0 < bv_unsigned n -> 0 < bv_unsigned s ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  b <> lo.
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.

Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
    fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_self : forall (a sz : word),
  iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_suffix : forall (a sz : word) (lo hi : Z),
  bv_unsigned a < lo -> lo <= bv_unsigned a + bv_unsigned sz ->
  bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [(a, Z_to_bv 64 (lo - bv_unsigned a))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
  rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sizes : forall (a sz : word) (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  bv_unsigned sz <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract. apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
Qed.

Lemma maps_subtract_sizes : forall l (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
  inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
  - apply iv_subtract_sizes; assumption.
  - apply IH; assumption.
Qed.

Lemma map_remove_sizes : forall l (a : word) N,
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (map_remove l a).
Proof.
  intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
  apply List.incl_filter.
Qed.

Lemma maps_subtract_length : forall l (lo hi : Z),
  (length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
  cbn [maps_subtract]. rewrite length_app. cbn [length].
  assert (length (iv_subtract a sz lo hi) <= 2)%nat.
  { unfold iv_subtract. rewrite length_app.
    destruct (_ <? _); destruct (_ <? _); cbn; lia. }
  specialize (IH lo hi). lia.
Qed.

Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
    fold (map_remove l a); specialize (IH a); lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

Lemma grant_budget_intro : forall m n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

(* [comment removed for export] *)
Lemma file_read_length_eq : forall data (off count : word),
  length (file_read data off count) = Nat.min (word_to_nat count) (length data - word_to_nat off).
Proof. intros. rewrite length_file_read. reflexivity. Qed.

Lemma file_read_length_le : forall data (off count : word),
  (length (file_read data off count) <= word_to_nat count)%nat
  /\ (length (file_read data off count) <= length data - word_to_nat off)%nat.
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.

