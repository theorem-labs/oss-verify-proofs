(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamSim AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MmapSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7div_posK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib2AS8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib2AS8PropExec6v_srliC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr07K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C59OSSVerify5KrLib2AS7SeqExec7step_sbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExecEN_to_le_bytes_1_smallC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib2AS7MmapSim;step_sb_anyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib2AS8PropExec:word_add_0C1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC47Corelib4Init3Nat3addC59OSSVerify5KrLib2AS8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indK47Corelib4Init5Logic4True01C59OSSVerify5KrLib2AS8PropExec9word1_natC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib2AS8AllocSim8zmem_outC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib2AS8AllocSim<rdn_zmem_outC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib2AS6CatSim7fd1chanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterc59OSSVerify5KrLib2AS7MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim8grant_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsBsubrelation_properC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses=iff_ReflexiveC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprc59OSSVerify5KrLib2AS7MmapSim<mmap_args_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib2AS8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;MAP_PRIVATEI4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00C5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch:lookup_armC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7sa_specC4ELinuxProcessSemantics?LinuxProcessSem5Monad9unmodeledC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;munmap_specC47Corelib7Classes?RelationClasses;reflexivityC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib2AS7ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specI4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7SpecArm00C5ELinuxProcessSemantics?LinuxProcessSem3Sys<SyscallTable:spec_tablec59OSSVerify5KrLib2AS7MmapSim>munmap_args_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim=page_round_upC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEI6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03c59OSSVerify5KrLib2AS7MmapSim:munmap_effC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01c59OSSVerify5KrLib2AS7MmapSimCsyscall_spec_munmapC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC59OSSVerify5KrLib2AS8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSimDmunmap_check_modeledC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapEcheck_munmap_sound_okC47Corelib4Init5Logic5proj1C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapHcheck_munmap_complete_okC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapOcheck_munmap_complete_unmodeledC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9mmap_specC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude9errnos_okC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude?errnos_ok_rangeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosc59OSSVerify5KrLib2AS7MmapSimBmmap_args_ok_gatesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSimAsyscall_spec_mmapC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_introC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapCcheck_mmap_sound_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTc59OSSVerify5KrLib2AS7MmapSim?grant_ok_unpackC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_belowC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC4ELinuxProcessSemantics?LinuxProcessSem5StateBstack_max_size_valK46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib2AS7MmapSim:mmap_modelC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFpage_round_up_Z_nonnegc59OSSVerify5KrLib2AS7MmapSim?grant_not_errnoC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFcheck_mmap_complete_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextI47Corelib4Init5Logic2ex00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAerrno_ret_in_trueK47Corelib4Init5Logic2ex01C46Stdlib4Bool4Bool<andb_false_rC46Stdlib4Bool4Bool<andb_false_lC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapMcheck_mmap_complete_unmodeledI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib2AS8AllocSim?apply_zeros_oneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosc59OSSVerify5KrLib2AS7MmapSim5zfillC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC59OSSVerify5KrLib2AS8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC45stdpp9bitvector;definitions4BvWfI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z6leb_gtc59OSSVerify5KrLib2AS7MmapSim6unfillC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib2AS7MmapSim:unfill_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib4Bool4Bool;orb_false_rC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib2AS7MmapSim3twm00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7MmapSim3twm04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim:msteps_indC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib2AS7MmapSim3twm20C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7MmapSim3twm23C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesI47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC47Corelib5Lists7ListDef5skipnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib2AS7CatExec7adv_setC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7MmapSim3twm11C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7MmapSim3twm02C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7MmapSim3twm22C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim:adv_munmapC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7MmapSim3twm03C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib2AS7SeqExec>land_255_smallC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7MmapSim3twm01C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03c59OSSVerify5KrLib2AS7MmapSim=munmap_ok_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc59OSSVerify5KrLib2AS7MmapSimDmunmap_model_no_lazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemantics?LinuxProcessSem5State5event03c59OSSVerify5KrLib2AS7MmapSimCmunmap_model_haltedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_nonec59OSSVerify5KrLib2AS7MmapSimCmunmap_no_unmodeledC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C59OSSVerify5KrLib2AS6CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim8twm_postC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec00C59OSSVerify5KrLib2AS6CatSim;buf_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim=twm_rest_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedC59OSSVerify5KrLib2AS7ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06C59OSSVerify5KrLib2AS7ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_halted_with_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC59OSSVerify5KrLib2AS6CatSim7weventsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exits_withC46Stdlib5Lists4List9app_nil_rK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>exec_step_onlyi59OSSVerify5KrLib2AS7MmapSim3twm10C1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_cons_iffK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List9app_assocC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_conseqc59OSSVerify5KrLib2AS7MmapSimDmunmap_model_fd1chanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim9munmap_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04c59OSSVerify5KrLib2AS7MmapSim@sstep_munmap_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim?munmap_model_fsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C59OSSVerify5KrLib2AS7ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC56Stdlib5Arith8PeanoNat3Nat7le_reflC59OSSVerify5KrLib2AS6CatSim;write1_ok_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim?sstep_write_invC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome02C59OSSVerify5KrLib2AS6CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC46Stdlib5Lists4List<firstn_skipnC46Stdlib5Lists4List7map_appK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec02c59OSSVerify5KrLib2AS7MmapSim:twm_mutindC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome00I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib2AS7MmapSim<twm_exec_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim8twm_execC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_realizesI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun5mexec00I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun?mexec_halt_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun9exec_starc59OSSVerify5KrLib2AS7MmapSim;mmap_ok_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSim?mmap_model_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSimAmmap_model_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7MmapSimAmmap_no_unmodeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exec_soundC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunGexits_with_never_errors".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_srli_div : forall (x : word) (sh : Z), (0 <= sh < 64)%Z ->
  bv_unsigned (v_srli x sh) = (bv_unsigned x / 2 ^ sh)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h02H0h12H1h21Hh32H2h42Hah57__arithh66__sat0h76__sat1h84__x1h96__sat3h:4__ffh;6__sat2h<6__sat4h=8__varmaph>5__with?1ah@4__x2hA2H3hB2H4hC2H5hD2H6hE2H7hF1qhG1rhH6__sat5hI4__x3hJ1zhK2H8hL3HlehM2HphN3HshhO2HxhP2shhQ1xp%0p&0p;1p;2p;3p;4p;5p;7p;6p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p8p1002dp4p70R0p1003Tp4p710R3p8P0p10040p4p710R4p8P0p1004Np4p7210R5p8P0g004kR0p4p710R6p8p1005Ip4p710R7P3p8P7P6p8p1005fp4p70R8P1p8P8P2p8P8p1006Tp4p7210p8P8P3p8P8p10070p4p710p8P8p1007fp4p7210p8P8P7p8P8P4p8P8P5p8P8p1008UR7p4p7210p8P8P7p4p710p8P8p1009Ip4p710p8P8p100:Cp4p710p8P8P6p8P8p100;3p4p7210p8P8p100;gp4p710p8P8p100<_p4p710p8P8p100=<p4p7210R7p8P8p100=Yp4p7210p8p100>8p4p7210R8P3p8P8P4p8P8P5p8P8P6p8p100>dp4p70R8P3p8P8P4p8P8P5p8P8P6p8P7P6p8g00?Zj15Tg00@?j1mTg00@]j1aTg00A@j1ITg00A^j23Tg00BHj2hTg00Bhj2dTg00CNj21Tg00Ckj29Tg00DHj2;Tg00Dhk101Tg00Ebj2Gj4]Tg00FJj3HTg00Fnj22Tg00GJj1pTg00Gjj1oTg00HJj1nTg00Hhj1lTg00IFj1jTg00J1j2UTg00JTj2eTg00K6j2cTg00KPj2bTg00L<j3LTg00LVj3`Tg00M5j4_Tg00Mgj2KTg00NEj2FTg00Nhj1^Tg00OJj2DTg00Ogj2<Tg00PCj2\Tg00Plj2[Tg00QMk400Tg00Qnj2{Tg00RWj1ETg00S6j2CTg00S_j2XTg00TKj3VTg00Tkj4MTg00UIj5yTg00Umj3xTg00VPj3wTg00W3j5uTg00W_j2TTg00XPj2STg00Y1j1RTg00YJj2PTg00Ygj2ZTg00ZNj2QTg00[5R6j2JTg00[Pj2OTg00\6j2WTg00\\j4kTg00]=j1qTg00]bj7rTg00^Fj3sTg00^ij3tTP0j6NTg00_Rj1iTg00`Pj2vTg00a6j2gTg00aej2zTg00b\j4YTg00cGj7fTg00ckj8|Tg00dOj3}Tg00e8j3~Tf0R0#5#5#5#5p>03g00eaR7/<0p=0f2R8f1R5/20'Jp=:g00f?R4?L50p=?1270p=4P4P5g00f]P0CYp=AP5g00gDR3g00gcR2P2g00hCR1P0g00hcFfp=7P4P5g00iCP0CYp=Bf3R9P3P2P2P1P8P5P0G|p=6%50#5p>02%50#5#5#5#5#5#5#5p=@A}450p=8A~450p==AL407p=>g00ijR:#5R;#5S00$03R<#mR=#a%00R>%I<R?7:0P413=8R@/h5RA,d=S0113=9%I;RB/18RC'9RD,?0XJ4REP411B?RF,;APEP411B5,9@S021;0F/?DXJ4&018%0@?:@FPBP81GB?RD%4BRE%0?%4F[[RG%0BRHg00jORIAHB?5UW4RJ%0F\IRK^4HRLP6f5RM,3=RN#0RO12NFRPPEP8f7RQ,3=#0RRf8RS,3=RT/2FRUP6%0SRV12S?RWPEPQf:RX#0RYf;RZ/2?R[g00jkR\#pR]%o\R^%n4S03%l4R_%j4R`1U47Ra1U4BRb'A'7Rc1e`1RdP0P8g00kWReg00l7Rf'c1b08=LefdA`475C_Rfb:b=b>PEP0b5W3W1P5P0O2n2001000000120000000W0W2P5P0O2n2001000000120000000b6b7PDPGPJPLP6POPP%0MRPP8P6PVPWf9RW#0PQP]P^1K45ROP_P`1F4:Re,Ba,7`Rg%^2RhPgC6PdPfb:b=b>X84S04%05S05\>^84S06P0f=RiP8O2b5X3[X1YP5P0O2n2001000000120000000X0UX2RP5P0O2n2001000000120000000b6b7C]%4Cf4RC,3=RR11B9RYPR1GB9Rj%0CS0711BMS08#4[\ERkf6Rl=HB5VIX4HRm11BlRn#0\I^4HRoPDPGPJPLP6%0TRTPU11BSRp#4PM13=XRq#0Rr13=ZRs/2FRtP6%0ZRuP[f<Rv,1BRw#4PX%0iRxf>Ry/2?RzPvP0P8O2X?ER{f@R|,1BS09#4^?ER}P]P^POP_P`1Aae,7`ROPhPOC6PdPfb:b=b>X84S0:%40%45[^84S0;P0fARO,1BR~PyO2b5b9W3W1P5P0O2n2001000000120000000W0W2P5P0O2n2001000000120000000b6b7b;b9PjPkPmPoPDPGPJPLP6PTPU13=WRU1DpU'<PMP6PuP[13=iR[1Dw['<PXP{P}&02<#@#@#@#@#@#@#@#I,\4R<P4%I:,[4P:1[47H00,{4g00lWR}#ER{#ERT,C4Ro'8'8%ETS0<#E,C4RT1C4{R{,8o/={Ro'81\4B1C4}R},8T'818}o,8<18}},8<'='='='=g00m6S0='X=V\]P^P41K48S0>P5Q03CMP_P`P`1Bab,7`PhP`P`P3P2P2P1DyPhAx4b=Rb,Ba,7`C6C6PhP`P`PcPh1F4;R;,Aa,7`RcC6PhP`PcPhP`PgPhAw4;e,Be,7`C6C6C6C6PdPfb:b=b>X84X@4PK\H%49RK\E%09S0?1DMC,<C[\K[[^84^@4P0P~fB,3=RKPXP5PyPQO6b5b9X3zX1xP5P0O2n2001000000121000000X0tX2rP5P0O2n2001000000121000000b6b7b;b9Du19RY/<RPN11BCS0@1GBCS0A%4n\P\ES0BAHBQ5VIX4HS0C11BQS0D#0\I^4HS0EPDPGPJPL1TUpS0F%0U11BWRW#011BXRX,9sRU#0[[S0G1SqWS0H%>W#R1DXU1;sX'P,?s[S0I1ZsXS0J%4X13=vRU11BZRQ';RP#0?:PQ[S0K1QUQS0L12Q71;[wRn,2w1<n7'J[S0M1O[wS0N%>w13=yRR11BiRY'9#>[S0O1WRYS0P%>YS0Qf?Rt,3=Rz11ByR;';/?z[S0R19z;RcP413=|R<11BtS0S';RoP4P613=ORT#0S0T12TFS0U%0KS0VPyfCS0W,3=#0S0XfDRm,3=S0Y/2FS0ZP6%0mS0[12m?S0\fFRk,3=#0Q0W%0kS0]fGS0^/2?S0_PifERjO1S0`fHS0a,1B9:VSS0bP|PlO1S0cfI,1BS0d#0Pu[S0ePkP0PCO2X?ES0ffK,1BR|#4^?ES0gP6Pu12Z|S0hfMS0i,3=#0P8fNS0j,1B,2yR|Q04Q06P0fQS0k,3=PiO2b5W1X0xP5P0O2n2001000000120000000b<b6b0WEWDP5P0O2n2001000000120000000WCWBP5P0O2n2001000000121000000bGbFbAb3b1b0b2b6b7b;b9b<Q0AQ0BQ0CQ0EPDPGPJPLQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0RPcP4PoP4P6Q0TQ0U%4~PyQ0XQ0ZP6Q0[Q0\11Bj#4Q0WQ0]Q0_Q0`Q0bQ0cQ0eQ0fQ0gP6PuQ0hfLS0h,1BR~#4S0gP8Q0:Q0;P0fP,1BQ0iO2b5X1|X0xP5P0O2n2001000000120000000b<b6b0WEWDP5P0O2n2001000000120000000WCWBP5P0O2n2001000000121000000bGbFbAb3b1b0b2b6b7b;b9b<CkQ0@,9N#013=lQ08'91GBM%0lRMQ0D#4[\EAHBS5VIX4H%0p\I^4HPDPGPJPL1TqW%0X19UQRW#0[\r1SsX%>X#R1DQW/PP,?U[1ZUQ%4Q%0n?:nw[1Q[w12w71;RYRw,2Y1<w7'J[1ORYQ0Q%>c[1Wz;%>;1?o<[Q0S,9<P4Q09,;TP4P6Q0V12KF%08RK?:8FPtQ0Y#013=j/2FP6%0j12j?A:MlFPmQ0^#0Q0a/2?PiPkO1Q0d9:VSQ0cfJ,1B#0Pu[Q0fQ0g^?EP6Pu12Z~A:xiFP8fO,1B,2yQ0<,C41={}'=Q0='X=V\]P^P4P41K49P9Q03CMP5Q0>CMP_P`PgPhP`%q:,F4R:,Be,7`PhP`Q00,F4,Aa,7`PhP`1A:b,7`PhP`P3P2P2P1Pg1Aeb,7`FrC6C6C6C6PdPfb:b=b>X84X@4XI41<58%4C12CFRfQ07/Jf[[[\>^84^@4^I4P0Q0k,1BfR,3=POQ0hQ0iQ0jPvO7b5W3X1xP5P0O2n2001000000121000000bHb7b1WKWEP5P0O2n2001000000121000000WDWCP5P0O2n2001000000121000000bGbFbBbAb3b1b2b7b;b9b<bH7sFb0bLbMbOPAP6Q05125?PKP0Q0?12C?Q04Q06P0PlP8O2b5W0W2P5P0O2n20010000001200000009t@5ENQ01%iAEN1v=A,3=1g=AEN1z85,3=Q02'?eWNXP4WQo"). Qed.

(* [comment removed for export] *)
Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            [Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h07Hdecodeh16Hecallh26Hfetchh33Hokh43immh51lh63memh72pch84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;5p;>p;6g00Gjj1;Tg00?Zj10Tg00]=j17Tg00@?j13Tg00@]j12Tg00>8j2LTg00mbj15Tg00nDj2CTg00oFj28Tg00L<j31Tg00ohj1?Tg010hj2=Tg011Hj1<Tg0129j4QTg00A@j1PTg012ej4OTg013Ej24Tg014:j29Tg014bj26Tg00RWj1ITg015Yj4HTg016Yj2ETg017aj1BTg018ij5:Tg019^j2DTg01:Zj3ATg01;Pj2FTg01<Xl>GTg00A^j2@Tg00`Pj2JTg00GJj1KTg00TKj3>Tg01=Oj1MTg003Tj6NTg01>T#;g00ijR0#0R1#7#3R2%01R1#0R3#0#0R4#0#3R5#2R6'L%33R3#2R7#5\6R8%34#2R4%22R2%70#0#0#3R0#2%54f8R9f6R:'Cf3R;,8431g00kWR4f4R<#?g01?S31g01@3R=g00f?R>'=R?#5f5R@#<P=P>g01@_P<P;f2R>CQ%P1R1CO,8?31f;R?P9f:R=/4@190;'6g00lW#IRACHg00l7514%;7R414?@RB,EAg01AKRA#Bf=p,2fxRCf<RDP?P=f9RED:'DPCPD16?1f7R1,4D190@'6f0R05A=PED:,FA31X54PCPDP?P=PEP9P1P:P@P<P;P>f1P0M>G1@5B,J3%K75>7%MBENW3W0W1W2W4X;2W:W=X98W6X76W8W<o"). Qed.

(* [comment removed for export] *)
Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
                          (a v : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01bh12Hah22Hbh32Hdh42Heh52Hfh63Hokh72Hvh81ah93immh:1mh;3memh<2pch=4regsh>3romh?3rs1h@3rs2hA4segshB1vhC1wp;1p;2p;3p;4p;5p;6p;=g00Gjj1QTg00?Zj11Tg00]=j1?Tg00@?j17Tg00@]j1;Tg00>8j2KTg00mbj1=Tg00nDj2ITg00oFj2>Tg00L<j30Tg00ohj1ETg010hj2CTg011Hj1BTg0129j4PTg00A@j1OTg012ej4NTg013Ej28Tg014:j2ATg014bj2<Tg00A^j29Tg00`Pj26Tg00RWj1JTg015Yj4@Tg017aj1HTg00GJj1GTg00TKj34Tg01:Zj33Tg018ij52Tg00K6j2FTg004kj6:Tg019^j2DTg01BRl=LTg01;Pj2MTg01AKR0f0R1'Mp=5g01>T#Qg00ijR2#1R3#?#7R4%13R3#1R5#1#1R6#1#7R7#;R8'K%75R5#;R9#=\8R:%76#;R6%;4R4%?2#1#1#7R2#;%=6f;R;f9R<'If6R=,>630g00kWR6f7R>#Eg01?S30g01@3R?g00f?R@'CRA#=f8RB#BP?P@g01@_P>P=f5R@CP%O3R3CN,>A30f=RA/8B1A2='<=08@f>R?/8B=08@197=,65=09@fARCP?PBg00lW#JRDC@g00l7RE506%H0R0p,2fxRFPCf@RG/<3RHf?RIf<RJ,8Cf:RK,A2'<R218C;RL,97,65%G9RM54933P?D2#5PFfBRN1<C3R3A49BM93GKPID2#5RO9001X:0P8P<PFPNP318NJ,97,65=49M93G1PID2#5=00OX08P8PBPFPNP31971,65=49M93GKPID2#5=00OX08P9P>PFPNP3A491M93GKPID2#5=00OX09PFPCPHA49>M93I<P?D2#5,F0197B,65f1E:PLf2E:P2f3RLE:PFPCPGPIP?D2,DNPNPCPGPIP?PAPJP;PKP=P@f4P8P<fCPGP1PDC@=06EX08P1P2PLE:M=LE:W6W2W7W1W3W4W5X09XB8X88W9X@4W?WCX>:W;X<8W=WAo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_snoc : forall (bs : list byte) (m : word -> option byte)
                           (a : word) (b : byte),
  wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word (length bs)) [b].
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01ah11bh22bsh31mh42IHh51oh61xp;1p;3p;2p;6p;4p;5g00?Zj15Tg00@?j1?Tg00@]j1>Tg00Gjj1ATg00mbj1ITg00GJj1GTg00TKj3=Tg00<_j38Tg01:Zj30j4:Tg002Dj24Tg00L<j33Tg01CMj36Tg00oFj27Tg00K6j2@Tg01D:j1HTg004kj69Tg00A@j1FTg01E5j3ETg01EXj31Tg01F=j1;Tg00RWj1<Tg01G8j2DTg01GOj3CTg01HUj5BTf2R0f1R1f0R2#;31p=2g00ijR3#5#5#5R4#?#>R5#AR6P5%54#5#5#?R4#>R7%I5R8[R9f3R:%G5R;9=52R<5859001A001:145:9241;0<539^15^07]3R=X26P7P1g00kWR>P8A642:R?1750R@f4RAP2O1RBn0100000020000X07P>P8A6421P@PBn0100000020000X07539X17P>P8A6420RC1751RDP:P2O1REn0100000020000X07,@9g00lWRF9241%H1E9A85;<9001A001;145;9241;0<539eX15X07X39P9P>P8PCf6RC,75PEn0100000020000X07RE%F3g01I75E4R39141RG;0A145ARH#;RI914G;0<P>P8145C#<924:9642RJP@P>P8A642Af8,75f5RKP2O1n0100000020000X07RLA14:3PCP2C:n0100000020000X079392X59P7%<FRF#;RMP>P8P?f7,75PBn0100000020000X07RBA1402R?;0K145KRN924?A=51;R;30P>P8PJP@PLA14:1PCP2C:n0100000020000X07539X17P71DFH9241A140MR?=0BK?02;P>P8PJP@PLA14:MPCP2C:n0100000020000X07539X17P>P8%<N92409642PDPBP?PKP2C:n0100000020000X07,@9A141M=14IAC1FHE9P3g01ISE9A85A<90EGP:PEPGP2O3E9A=5KARK=85<9001A001K145K9241;0<539eX15X07X39X4=X26X65P2DBW2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
  zmem m a n.

Lemma zfill_out : forall a n m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  zfill a n m x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h02Hxh11ah21mh31nh41xp;1p;2p;5g00?Zj10Tg00@?j13Tg00@]j12Tg00mbj14Tg00A^j21Tg00Fnj29Tg00YJj28Tg00Ogj25Tg01JMj26Tg01Jgj57Tg00ij#0#0#0R0#0#0#0#3R1#2R2%30#2#4\2f0R0,11R3f3R4,11R5'9f2R6,11,85/53'6P6f4P4f1P0D7W0X42W2X32W1o"). Qed.

(* [comment removed for export] *)
Lemma rdn_zfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (zfill a n m) x k = rdn segs m x k.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h02Hdh13Hnwh21ah31kh41mh51nh64segsh71xp;1p;2p;8g00Gjj1<Tg00?Zj10Tg00@?j14Tg00@]j16Tg00mbj1;Tg00A^j21Tg01K`j17Tg00YJj22Tg00A@j15Tg00CNj29Tg00Ogj23Tg01JMj28Tg01L@j8:Tg01>T#<g00ij#0R0#0#0R1#0#0#0R2#4R3#6R4%41#6#;\4g01M=f1R1,13f0R5#7'2%50%52'9'3f2R2,13R0%71'2f5R6,13R7'3f4R8,13,27/30'8f7P8f6P6f3P2P1P5G:W0W1W3X74W4X54W2W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n
    (mkVmMapsFull (vm_reserved (m_vmmaps m))
               (map_remove (vm_maps (m_vmmaps m)) addr)
               (maps_subtract (vm_noaccess (m_vmmaps m))
                  (bv_unsigned addr)
                  (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m))
               (vm_init_sp (m_vmmaps m))) m.

Definition mmap_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
               ((a, n) :: vm_maps (m_vmmaps m))
               (vm_noaccess (m_vmmaps m))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m))
               (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition page_round_up (len : word) : word :=
  Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).

(* [comment removed for export] *)
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h04addrh11mh21np;1p;2g00?Zj10Tg00@?j15Tg00@]j12Tg00mbj11Tg01M\j14Tg00K6j23Tg00ij#0#0#0#0#0#0#5#2R0g01NS%10f0#4'3W1X20W0o"). Qed.
Lemma munmap_model_fs : forall addr n m, m_fs (munmap_model addr n m) = m_fs m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h04addrh11mh21np;1p;2g00?Zj10Tg00@?j14Tg00@]j12Tg01OIj11Tg00K6j23Tg00ij#0#0#0#0#0#0#4#2R0g01NSg005ff0#1'3W1X20W0o"). Qed.
Lemma munmap_model_fd1chan : forall addr n m, fd1chan m -> fd1chan (munmap_model addr n m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01Hh14addrh21mh31np;1g00?Zj10Tg00@?j13Tg00@]j12Tg01P<j11Tg00ij#0#0#0#0#0#0#3#2R0g01NSf0R1#1P1W0W2X30W1o"). Qed.
Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h05Hlazyh14addrh21lh31mh41np;1p;2p;3p;8p;7p;6g00?Zj11Tg00@?j1STg00@]j1OTg010hj2NTg00Gjj1RTg01Q2j10Tg00GJj1QTg00L<j33Tg01Qjj15Tg01R]j16Tg01STj1ITg01TNj1ETg01UDj2?Tg01V=j1KTg00A^j2>Tg00YJj2JTg01W7j3:Tg01X3j1HTg01Xnj1GTg01Ycj1FTg01ZZj1DTg01[Uj1CTg01\Nj8BTg01]Ej1<Tg01^Ej39Tg01_=j17Tg01`0j14Tg01`ej1=Tg01aZj1;Tg01bNj12Tg01cCj78Tg01d9j2@Tg01e:j3ATg00K6j2MTg004kj6LTg01eUj3PTg00ij#1#1#1#1#1#1#SR0#OR1g01NS1N11R2#RR3f0R4#0%Q2R233P3P2f2R5#5%65R6#I%E6f4R7'?%K61>07R7f3R8,>0R9,J7R:3:%H6%G6%F6%D6%C6GB%<5794%75%45%=5%;5%25F8R6#5%66%06?:7:1@7:%<65A139%76%46%=6%;6%26F8#0=332X231M32f1R6#0R:P4EL%56%66R4#I%E4/?8%K41>05,J9R07:9%H4%G4%F4%D4%C4GB%<679:%76%46%=6%;6%26F8R:#5%6:%0:?:901@90%<:5A139%7:%4:%=:%;:%2:F8#0=332eAP856#0=332eW0W3X41W1o"). Qed.
Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01ah11mh21np;1p;2g00?Zj10Tg00@?j15Tg00@]j12Tg00mbj11Tg01M\j14Tg00K6j23Tg00ij#0#0#0#0#0#0#5#2R0g01NS%10f0#4'3W1X20W0o"). Qed.
Lemma mmap_model_fs : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01ah11mh21np;1p;2g00?Zj10Tg00@?j14Tg00@]j12Tg01OIj11Tg00K6j23Tg00ij#0#0#0#0#0#0#4#2R0g01NSg005ff0#1'3W1X20W0o"). Qed.
Lemma mmap_model_fd1chan : forall a n m, fd1chan m -> fd1chan (mmap_model a n m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01Hh11ah21mh31np;1g00?Zj10Tg00@?j13Tg00@]j12Tg01P<j11Tg00ij#0#0#0#0#0#0#3#2R0g01NSf0R1#1P1W0W2X30W1o"). Qed.
Lemma mmap_model_lazy : forall a n m,
  m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01ah11mh21np;1p;2g00?Zj10Tg00@?j16Tg00@]j12Tg010hj21Tg00Gjj15Tg01Q2j14Tg00K6j23Tg00ij#0#0#0#0#0#0#6#2R0g01NS1100#5f0#4'3W1X20W0o"). Qed.

(* [comment removed for export] *)
Lemma grant_ok_unpack : forall hint m a n,
  grant_ok hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01Hh11mh21nh35lemmah42H1h52H2h62H3h72H5h81Ah91Bh:2H4h;1ah<4hintp;1p;4p;2p;3p;8p;6p;=g00?Zj1GTg00@?j1iTg00@]j1cTg01fQj4^Tg00A^j23Tg01gIj26Tg01R]j10Tg01ggj14Tg010hj2]Tg01STj1JTg01TNj1KTg00`Pj2ITg01h_j1@Tg01Ycj15Tg01i]R0j2PTg00[5R1j21Tg01j6R2j3bTg01jgj2OTg01kHj4MTg01koj2aTg01l\j8XTg01mOj3_Tg01nER3j6TTg00YJj2=Tg00Ogj2ATg01o7j2WTg01oTj2RTg00L<j3;Tg0201j2hTg020Qj2VTg00Fnj2QTg020nj2gTg021Nj2fTg021nj4NTg00DHj2[Tg00<_j3ZTg022Ij3YTg023Cj4dTg0246l=eTg00kWR4f0R5g00l7R63;p=2g024eR7,[5g00eaR8'Rp=<1V85p=8f2R9f1R:'=/W5p=?f4R;f3R<;Z9?Y:5p=LA;4:6A;456'1p=:p-0R=P=P0P0P5P0g025]R>P2GXp=`%@:/=5p=>1W:5=;46p=7P=P0P:P5Cdp=FP5P:P1P3P9g00hcP<P;f5R3f6R2f7R?f8R@f9RAM=ep=U%J;%K<5Z31I:57Y9=;46p=91[57p=Eg00f?R7?;58p=D1Q85p=H1=9:/A5p=B11:5,19p=CA;456,1:p=S1R58p=\g00ij#G#G#G#G#G#G#iR6#cR4g01NSP<P9P:P5C^#21369RB#<%8B'6%0<RC#49?B:'61]44RB%JC%KCP91I6:DL'6RD%@<%5C7?:RC'6#21:DCRE'P136<RF#<%8F'6%0;RG#49?F9'6RFPB%JG%KGP<1I69DLRH'6RI%@;%5G7?9RG'6#2%2IRI%2GRG'1;b5W31ODCP5O2PE1:FHRE,PIP=^9=RI^8=RCP=P=\=P0P=P=P0P0CMRDCMRJP=PIP0P=P=P0P>CMR>CMRKP=PIP0P01a=0RIPDP>%`IGXRI136;R>#<%8>'6RD%03RL#49?><R>'6RMPB%JL%KLP;1I6<DLRN'6#2%2MRM%2NRN'1P51>3<%5L'7RLPLg026;9_=0R=/FLM:UW31OFHP5O211EG1:D>RE,PMPCPJPKPI1363RM#<RG%8MRH'6RF%02R0#49?M;RM'6#2ROPBP0P0P3P6P;E9RP'1%2FRF%2MRM'1RQ/1PPOPQP5PPPP1F=PET1>2;%50'7R0P01F=0M:UW31OD>P5O211EN/1L1:GHRL,PFPCPJPKPI1362RI#<RK%8IRJ'6#2RC1=I3%0?RI#4'7RF'1REPBPIPIP2P6P3E9RN'11:KJRJ/1FRK/1NR>PEPKPCPJP5PFPF1F=FETPNPN1F=NET1>?3%5I'7RIPI1F=IM:UW31OGHP5O211LM/1P/10P1P>PI136?RI#E#D%HI%0@R>#49BI2PBP>P>P?P6P2E9%@@%5>7B23C3CP5136@R>#<%8>':%0ARI#49?>?'SPB%JI%KIP@1I6?DL'SP1136ARI#<%8I':f:R>#0R0#49?I@'SPBP0P0PAP6P@E9f;R@/>A%0@#5'7136@R0#ERI#D%H01=0>RPf<RL#0RM#4RH'APBPMPMP@P6P>E9%@L%5M7B>3C3C[P5%\I%80':1WPH'SP1136LRH#<%8H':1=H@f=RH#0#4'7PBf>R@#0RPPPPHP6PLE9f?RL/>H%0L#5'7136LRH#ERP#D%HHf@R0#0RI#49BH@PBPIPIPLP6P@E9%@0%5I7B@3C3C[[P5136@R@#<%8@':P1%\P#2%8H#21360/=LfARL#0#4'7PBfBRH#0RPPPPLP6P0E9fCR0/>L%00#5'71360RP#E#D%HP1=PHRPfDR@#0RI#4R>'APBPIPIP0P6PHE9%@@%5I7BH3C3C[[[P5136L#<#2136H#8#217P>PBfE#0R>P>P@P6P0E9fFR0/>@%00#5'7P11R:5#2A;79:[R0A;7:51R9:#2R@[A;7<9\@1h:5P:n2001000000120000000X17X27P0^17^27P5fG,36#ER0P8P3O3%D0P11V:5#21Q9:[R01Q:51V9:#2R3[1Q<9\31g:5P:n2001000000120000000X17X27P0^17^27P5P8fI,36R8P2O3%H8P117:51A9:[R11A:5179:R8[1A<9\81f:5P:n2001000000120000000X17X27R8P1^17^27R1P5fK,36fJ'=R<fLR0#0#4R3P?O31A<3P8P1P5fNR1/>0R0%01#5R8P?O31A081361R8#E#D%H8R0fMR?fOR3#0R<#45B8R8PBP<P<P1P6P?E9R6%@3%5<7B?R?'1R<'1R3'1P2P0P3P;P8P<P9P6P?PAP5CNCNCNCNb7b0b6b0b5b0b4b0W7W:W6W5W4P:P5O2n2001000000121000000W0P:P5O2n2001000000121000000W0P:P5O2n2001000000121000000W0P:P5O2n2001000000121000000b0b0b0b0W0X27X;4W1W<o"). Qed.

Lemma region_free_cons : forall (b s : word) r (lo n : word),
  region_free ((b, s) :: r) lo n = true ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo)%Z
  /\ region_free r lo n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h02H1h11Hh22b1h32b2h41bh57__arithh64__x1h74__x2h84__x3h91xh:1yh;2H0h<2H2h=4__ffh>8__varmaph?5__with@2lohA1nhB1rhC1sp;1p;2p;4p;3p;7p;8g00?Zj18Tg00@?j1[Tg00@]j1KTg010hj2DTg00Gjj1@Tg012ej4WTg00TKj3VTg022Ij37Tg01gIj2>Tg00[5R0j29Tg01jgj2BTg026kj4;Tg027dj1:Tg00A^j22Tg00YJj24Tg00Ogj21Tg01JMR1j26Tg028Bj1UTg028cj2TTg020Qj25Tg029Ej2JTg00GJj1ITg00Mgj2=Tg00Tkj4FTg00Hhj1GTg00IFj1HTg00NEj2<Tg029ej3ETg00]=j1LTg00b\j4CTg00cGj7MTg00Nhj1NTg00ckj8OTg00JTj2PTg00K6j2QTg00KPj2ATg00LVj3RTg00M5j4STg02:Hj3ZTg02:bj3YTg021nj4XTg00L<j3?Tg00kWR2f0R3g00l7R43?p=0g01?S9?23p=3g00ijR5#8R6#8#8#8#8#8#[R7#KR81D88R9#@P8P8f4R:f3R;CWf2R<5V9f1R9;73#0P01>93R=#0%0<R>%09R?'9[R@%03,9?1><9R?#0RA[%0;/9>\A1B93P9n2001000000120000000X32X22P@^32^22P3P;P<f6R@f5RAC;#:R>A7:;<RBP9O3%0>%0B'9P0P:P;f7RBP@C;#:#0A7A:;#0127AR>127:'4f8RC,27RD'1127B,4DRE/1>'6A7@A:#0'9P3P@PAf9RAPCC;#:#0A7CB@#0f;R@,27R:,1Ef:,27,4:RE/1D'6A7ACB#0P0%:3#0%39RB[RD%33R>%:9#0RF[%3<RG\F%U3P9n2001000000120000000X42PD^42P3PAPCf<RCP@C;R@P<O2%3@P0%3=16GB[R=16B>%3?R?[%3;/6G\?1T93P9n2001000000120000000X32X22P=^32^22P3f>,27R=f=,27R?'4RG,5:R>15=EREP9O3%3>%3E'6P1127CRCf?,27R1/4=RE'5#314C:,51#314?CRCf@,27R:'114:1R>/1?'6P315?>#3fA,27R>,1GRG14>:/1=R=g00f?R?P01593#3119<[R0113915<9#3RB[11<;\B1J93P9n2001000000120000000X:?W9RBP0^:?^9?R0P3P1fB,27R@/4>RAP9O311A1g00jkRA#I%@AP?1=?<P91=?;CF%G?%H?RAg00gDR1g00gcRDPDg00hCRFPAP1PDPDPFP?1<?51<?65E?g00iC%L5,<?CCg00hcFMR5%NDP5GO1PAFP3P<1Q241A3<#0dg00ea=R?9CSb=b>b?X6?X7?X8?R41439/1<149</1;[^6?^7?^8?R?P3P>fC,27fD,27R7P9O4b5b0b13ZW0P3O115:C#3PBP0P3P@PEP9O311E@P4P?P3P7P:P>P9O4b5b0b19YG=W0P3O1n200100000021100011000b0b1b0b1P3CXW<W0P9P3O2n2001000000121000000b1b;W1XA8X@8WBXC8W4o"). Qed.

(* [comment removed for export] *)
Lemma source_alloc_limit_val : source_alloc_limit = 0x400000000%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p;1p;2p;3g00A@j13Tg00K6j22Tg00L<j34Tg00?Zj11Tf0R0#1#1p=5%10#1#1#1p=0g00f?R0g00ij#5#0#0#0#0#0#0#0#0#3R1'2g02;<=401do"). Qed.
Lemma target_alloc_limit_val : target_alloc_limit = 0x8000000000%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p;1p;2p;3g00?Zj10Tg00A@j15Tg00K6j24Tg00L<j33Tf0R0#0#0p=6%00#0#0#0p=2%00#0#0#0#0#0#0#0p=1g00f?R0g00ij#0#6#2#1#1#1#1#5R1'4g02<==301do"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_arg3_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h02msh14segsh22x8p;1p;2g00Gjj16Tg00?Zj10Tg00@?j13Tg00@]j12Tg00RWj11Tg02=>j25Tg00K6j24Tg01>T#6g01AKg00ij#0#0#0#0#0#0#3#2R0f1g00lW#1#1#1'5,40W2W0W1o"). Qed.

Lemma in_arg4_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h02msh14segsh22x8p;1p;2g00Gjj16Tg00?Zj10Tg00@?j13Tg00@]j12Tg00RWj11Tg02=>j25Tg00K6j24Tg01>T#6g01AKg00ij#0#0#0#0#0#0#3#2R0f1g00lW#1#1#1#1'5,40W2W0W1o"). Qed.

Lemma in_arg5_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h02msh14segsh22x8p;1p;2g00Gjj16Tg00?Zj10Tg00@?j13Tg00@]j12Tg00RWj11Tg02=>j25Tg00K6j24Tg01>T#6g01AKg00ij#0#0#0#0#0#0#3#2R0f1g00lW#1#1#1#1#1'5,40W2W0W1o"). Qed.

(* [comment removed for export] *)
Definition mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
Lemma mmap_args_ok_gates : forall ms,
  mmap_args_ok ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\
  mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
  = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h01bh11Hh22H1h32H2h42H3h52H4h62H5h72msp;1p;2p;3p;6p;4g02><j1QTg00?Zj17Tg00@?j1PTg00@]j1JTg00RWj1@Tg00`Pj2ATg00Y1j1GTg00]=j1ETg00A@j1DTg02?8j1ITg02=>j20Tg02?Vj1?Tg02@]j1>Tg02A]j18Tg02BWj3=Tg00[5R0j24Tg00A^j2HTg00DHj2OTg01oTj26Tg00K6j2NTg004kj6<Tg02CZj2MTg027dj1LTg02D8j4KTg00YJj2FTg02E3j1BTg01gIj29Tg021nj4CTg00L<j3:Tf3R1f2R2f1R3'0f0R43:p=1f4R51012;:3/44p=2g00kWR6g01?S7:4p=;g00l7R79:64p=3A:637/44p=5g01AK%Q4P0g00ijR8#7#7#7R9#7#7#7#PR:#JR;P3g00lW#@R<g00eaR=,A:R>C1#GP;P3%@<R?%E8#D,A:R@P;P3%@?RA%E9#7#D,A:R9P;P3%@ARB%I8,A:R8P;P3%@BRCP>C1D2D2D2102CRD#?102ARE#>102<#8#;102??=ED#3'4'5'5P4P;P1P<P>C1#GP;P5P?P@P;P5PAP9P;P5PBP8P;P5PCP>C1D2D2D2P0P;f5R5P?P@C1P;P5PAP9P;P5PBP8P;P5PCP>C1D2D2f6R1/0CRE#?101ARD#>101<#8#;101??=DE#3'4'5'5P4P;f7P?P@C1P;f8RDPAP9P;PDPBP8P;PDPCP>C1D2D2P0P;f9RDPAP9C1P;PDPBP8P;PDPCP>C1D2f:RE/0CR1#?10EAR2#>10E<#8#;10E??=21#3'4'5'5P4P;f;PAP9C1P;f<R2PBP8P;P2PCP>C1D2P0P;f=R0PBP8C1P;P0PCP>C1f>R2/0CR1#?102ARE#>102<#8#;102??=E1#3'4'5'5P4P;f?PBP8C1P;f@PCP>C1fAR8/0CRB#?#3RE108AR1#>#3R2108<R<#8#;RF108?R8?=1B#3R?'4RG'4P;P>1H:4RHg024e'O/6=#3X0;1N67R7PBP4E<PEeP2PGP;P9g02F7RG,MH/6=#L#3X0;P7P1P5E<P2ePFP?P:P<P>P0CKPFeP;P@g02G6g02H1'FRF,6HfBRH/0A#Bg02Hm/FGRG'6'910HC#8RH'9#3X0;P;P91H:@/6FRF%B4/6G'9/9H#3X0;P;P>%B9/6G,9F%84'9#3X0;P7PBP4E<P1P5E<P8PDE<P?eCCCCCCW6W5P3P4O2n2001000000121000000W1W4P3P4O2n2001000000121000000W1W3P3P4O2n2001000000121000000W1W2P3P4O2n2001000000121000000W1W7o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
  (bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
  ms_gpr ms 1 <> Z_to_bv 64 0 /\
  (bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
  map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (page_round_up (ms_gpr ms 1)) = true.

(* [comment removed for export] *)
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].

(* [comment removed for export] *)
Lemma syscall_spec_munmap : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p'0h03Hnoh11bh25modelh32msh41oh54segsh62x8h71zi001ai011xp;1p;2p;3p;4p;5p;6g00Gjj1ETg00?Zj10Tg00@?j1>Tg00@]j1;Tg02Ijj1DTg00A^j24Tg00]=j11Tg00A@j1=Tg00L<j3<Tg02Jbj26Tg02Kbj33Tg02LXj4:Tg02MUj49Tg02=>j22Tg00RWj1CTg02NMj58Tg01i]R0j25Tg02OMj4@Tg004kj67Tg02P;j1?Tg02Q2j3ATg02R4j3BTg01>T#Eg01AKg00ijR1#0#0#0#0#0#0#>R2#;R3g01NSg02RoR4#Dg00f?R5f2R6,42%11#0#1#0#1#1#1#=R13<P3f3R7g00mbR8g02SmR9p-0R:g02TlR;f0R<,42'6P<f7f6R=f5R>33f4R?P7C:R@P4A3=>?R=P7P6C9R4n10110100021010000g00lWRA,2>%CARB,2>P=P7P6D8R='5X13P5P1P8P9P:16;<P@P4n10110100021010000/5=X75P:P0g026;12?A12?BA3>?7RBP6f1RAD8R0C@1427P<E7%?BAA>?7E7ABB6A/50eW0W4W2W6W3W5o"). Qed.

(* [comment removed for export] *)
Lemma munmap_check_modeled : forall ms model eff,
  munmap_args_ok ms model ->
  check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if w_is0 r
           && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p'0h01bh11Hh23Halh34Hhash44Hlenh53Hnwh63effi003effh75modelh82msi01:eff_copiesi02;eff_copyinsi03:eff_writesi049eff_zerosi051li061mi072m0i081pi091ri0:2usp;2p;1p;3p;4p;8p;6g02V0j2mTg00?Zj1BTg00@?j1STg00A^j22Tg00DHj2KTg00@]j1RTg00RWj1cTg02=>j20Tg00`Pj2CTg00L<j38Tg00Y1j1JTg00YJj24Tg01R]j16Tg02Vnj17Tg00[5R0j2ATg02Wkj4HTg00GjR1j1dTg010hj2MTg02A]j1LTg012ej4<Tg00GJj1QTg00TKj3=Tg02Y3j2?Tg01gIj2>Tg01eUj3DTg02Z9j2@Tg027dj1PTg02[Cj2ETg02[`j1bTg02\Xj4FTg020Qj2OTg01STj1TTg01TNj1NTg01UDj2aTg01V=j1`Tg01W7j3_Tg01X3j1^Tg01Xnj1]Tg01Ycj1\Tg01ZZj1YTg01[Uj1ZTg01\Nj8[Tg02]bj4XTg02^jj3WTg00K6j2lTg004kj6GTg029Ej2kTg02_mj4VTg01CMj3jTg02D8j4iTg01oTj2UTg0201j2gTg02`Hj1fTg00Ogj2hTg02aFj3eTf0R2g00lWR3'0p=1g00f?g00eaR4782p=If1R5/22#fp=5g02b<R6,h2p=;f2R7#N?e52p=9g00kWR8g00l7R9782p=:g02c4R:?852p=3g01AKg01NSg02RoR;1m75P0g00ij#B#B#BR<#B#B#B#SR=f3R>#1R?'2R@g024eRA'K#I%R=RB%c3R3,0>RC1C=4RD38#J15=C,4@#;%67%7C79?#:'A'Af4R?#110?3P7P>CHP;P:P7P1%S<#R#d,MBR<P:P?P11MBBRCP:P>P1g02d>R@P:P5P1g01M=,MBREP:P2P8P:f5RF#LRGPBPBf:RH#1RI10H3RJ#7RKC<%QCRL5=C,?7'>f9RM9DIKg02e6#QRN'@g02elROn0100000020000POn10110200020020108105POn10110100020020106105POn10110400020020108105POn10110300020020108105n0110000016010910310410:101102'3P2%1F,2=/KA#If6RP/03RQ=8BD#J%1PRR,2=15=Q'4#;%6F%7Q79R#:'A'AP0f7RR/03RQ=8BD#J%1RRS,2=15=Q'4#;%6P%7Q79S#:'Af8RS#110S3PPPRCHP;P:PPP1P<P:P?P1PCP:P>P1P@P:P5P1PEP:P2P8P:PBPBf>RP#1RR10P3#7RSC<==CL,?7,>Gf=RQ9DRS/@NPOn0100000020000POn10110200020020108105POn10110100020020106105POn10110400020020108105POn10110300020020108105n0110000016010910310410:101102'3P210M3=8BD#J12=I15=J'4#;%6M?9IK#:'AP0f;R0#1RK,2=1003RI,5='4#;%6H%7I79K#:f<RK#110K3PHP0CHP;P:PHP1P<P:P?P1PCP:P>P1P@P:P5P1PEP:P2P8P:PBPBfBRH#1R010H3#7RHC<==CL,?7,>GfA9D0H/@NPOn0100000020000POn10110200020020108105POn10110100020020106105POn10110400020020108105POn10110300020020108105n0110000016010910310410:101102'3P2%1Q,2=10Q3,5='4#;%6Q?9RS#:P8P9P8P:%P2f@RS/03RR#L'EPPg02g6#bRHf?R0PNCFRKP8P:%1SRS,2=RI15=RRR'4RJ,O6RTPKP8P:%60RU1C=R79SP;P:PPP1P<P:P?P1PCP:P>P1P@P:P5P1PEP:P2P8P:PBPBfFRV#1RW10V3RV,5=,C=RXC<==CL,?7,>GPWPXfERY#6RZ#T%NZ/aW%`Z12=WR[12=X,4[3_%^Z%]Z%\Z%YZ%ZZG[PYCX/@NPOn0100000020000POn10110200020120108105POn10110100020120107105POn10110400020120108105POn10110300020120108105n0110000016110910310410:101102RZP8P:AWUSRPPPDP0PNCFg02gkRUn0100000020000RRn0100000020100RSn0100000020001R[n0100000020001P;P:PPP1P<P:P?P1PCP:P>P1P@P:P5P1PEP:P2P8P:PBPBPW%7VRVC<==CL,?7,>GADWVY/@NPOn0100000020000POn10110200020020108105POn10110100020020106105POn10110400020020108105POn10110300020020108105n0110000016010910310410:101102RV'3X08P8g01?SRWP8P:%P9RX/E2PKP[n0100000020001/3VX08P8PWP8P:P2PKPSn0100000020001/3VX08P8P9P8P:P2PZPRn0100000020100/3VX08P;P:PQP1P<P:P?P1PCP:P>P1P@P:P5P1PEP:P2P8P:PBPB%1YRV10Y3RY#7RRC<==CL,?7,>GfDRZ9DVR/@NPOn0100000020000POn10110200020020108105POn10110100020020106105POn10110400020020108105POn10110300020020108105n0110000016010910310410:101102RR,l:%6PR9%10RS1003R0,5=R3,C=39RKP2EGP8P:PKP;P:PQP1P<P:P?P1PCP:P>P1P@P:P5P1PEP:P2P8P:PBPBPV15=Y,C=RYC<==CL,?7,>GPVPY%6ZRG#T%NG/aV%`G12=VRV12=Y,4V3_%^G%]G%\G%YG%ZGG[PZCX/@NPOn0100000020000POn10110200020120108105POn10110100020120107105POn10110400020120108105POn10110300020120108105n0110000016110910310410:101102P8P:AW9S3PQPDPPPNCFPUn0100000020000n0100000020100RU/3Re12=SR9/43R3,O6ROA88OW%;J[%;3A88TW[1k63P5CVEGP8P:POPQPHPPPNCFRNPUn0100000020001RU/3ReP8P:1EXWPNPUn0100000020001/3ReAj=0DP=P0PDPFCiEGP8P:%L0,EXPNPUn0100000020001/3Re1K9AR9/U4RU%:U1KIARI#I[%I91UI4#:[1g94PMCVEGPSP0PQPPCH/3ReW3W5P5P2O2n2001000000121000000W1W4P5P2O2n2001000000121000000W1W2P5P2O2n2001000000121000000W1W6W7W8o"). Qed.

Lemma munmap_ok : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p'0h01bh12Hah23Hnoh31ch45modelh52msh64segsh72x8i003effi01:eff_copiesi02;eff_copyinsi03:eff_writesi049eff_zerosi051li061mi071pi081ri092usp;1p;2p;3p;4p;5p;6p;8g00GjR0j16Tg00?Zj11Tg00@?j1ATg00@]j1BTg00A^j2TTg00]=j13Tg00A@j1STg00L<j30Tg02V0j2MTg02Kbj3?Tg02i5j1FTg02=>j22Tg00RWj1HTg02Vnj1=Tg01eUj3:Tg00GJj1GTg02ioj4ETg02R4j3DTg02NMj5CTg02jgj6RTg010hj2;Tg02A]j1QTg012ej45Tg00TKj37Tg02Y3j2<Tg01gIj28Tg02Z9j29Tg00K6j2@Tg02kjj2LTg02_mj4>Tg004kj64Tg00`Pj2KTg01CMj3JTg02m3j2NTg02Wkj4ITg02moj4OTg02o3j8PTg01>T#6g01AKg00ijR1#1#1#1R2#1#1#1#AR3#BR4g01NSg00f?f1R5,T3%31#1#3#1#3#3#3#S30f3R1/M5f5R6f4R7;?1R8f2R9g02RoR:%F7R;g00lWR<,27R=%H<R>,27R?#=R@;:9RAg02e6#GRBCERC3D126<RD126>REf6??67RFP1P:%F6%=ERE=:D1RGPBCERHDC[P=P?P8P9PCDCADF1H[P6P7P1P9PCP5ERP=P?P;P9PAPBP8g02c4R8P:P8P;P0%A2#B#6,;4P8P7P01;44R2P8P1P0g02d>P8P5P0g01M=,;4P8f0R0g00kWR5P8%Q6P4P4f:R6/2<R<126>#=R6C5%G2R>572,<9'8f89:<6/9Bg02elR6n0100000020000P6n10110200020020107105P6n10110100020020106105P6n10110400020020107105P6n10110300020020107105n01100000160108103104109101102R<19GBRG9080X38P5g00l7R1P5P8P4P4PDPEC5=72>RE/<ERD,80PGP6n0100000020000=08GX05P5P1P5P81810PGP6n0100000020000=08GX0519ABRB,@8P4P4P=P@C5=72>R>/<>R@A05@1%62R2?0EE[A02>>A05D1[1L>>1@2>C>E4g00ea,K3R2=J321N32E4A08<BeP=P?P;P9CIP7P9P;P0COE4GPC>W1W2W4W7W5W6o"). Qed.

Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  eff = munmap_eff ms /\
  model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model
  /\ evs = [].
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p'0h05Hspech11Hh22HCh32H0h41bi001bh51eh61pi011ph72H1h82Hrh93Hush:1ah;2b1h<2b2h=1ci021ch>7copyinsh?2csh@2l1hA2l2hB1mi031mhC1ri041rhD2usi052ushE2wshF2zshG2H2hH2HahI3HnohJ3effi063effhK3evsi073evshL1li081lhM5modelhN6model'hO2mshP4segshQ2x8i09:eff_copiesi0:;eff_copyinsi0;7eff_reti0<:eff_unmapsi0=:eff_writesi0>9eff_zerosi0?1sp&0p;1p;2p;3p;4p;5p;6p;8p;7g00GjR0j1=Tg00?Zj1;Tg00@?j1]Tg00@]j1YTg00A^j2VTg00]=j1ETg00A@j1tTg00L<R1j31Tg02V0j2gTg02Kbj3OTg02ioj4NTg02R4j3MTg00RWk108Tg02=>j2?Tg02NMj5aTg02jgk601Tg030Dj4|Tg030_j8xTg02Wkj4\Tg02Z9j20Tg010hj2STg02A]j1CTg00GJj1@Tg01eUj36Tg02moj4dTg003Tj6GTg00K6j2BTg02i5j1LTg004Nj6cTg01R]j1bTg01STk107Tg01TNk106Tg01UDk205Tg01V=k104Tg00YJk203Tg01W7j3`Tg01X3k102Tg01Xnk100Tg01Ycj1~Tg01ZZj1}Tg01[Uj1{Tg01\Nj8zTg0323j2yTg01Qjj1wTg01Q2j1vTg01d9j2uTg01]Ej1sTg01e:j3rTg01^Ej3qTg01_=j1pTg01`0j1oTg01`ej1nTg01aZj1kTg01bNj1lTg01cCj7mTg01gIj2ITg00[5R2j29Tg01jgj2jTg01CMj3[Tg032mj3iTg00`Pj2hTg02Y3j2ATg02kjj2fTg033bj6TTg021nj4^Tg004kj6_Tg034`j2FTg00TKj3>Tg02Vnj1ZTg012ej4UTf0R3g00lWR4'?p=2g02c4R5f1R6;13p=31?63#Zp=4f5R7f4R8f3R9f2R:P6CU;>3p=D1A63,I:p=P1?941?:6#Z;63p=:g01NSR;?189A1:63'9p=8g02RoR<%L671:/93p=Xf7R=#Cf6R>P8P9P:P6CU=>73'A'Ip=<P=P>P7P8P9P:ET%L651</93p=7P=P>P7P8P9P:ET=1<6/93p=Wg00kWR?g00l7713p=5A1;63p=HP8P9P:P6CU=>73,A>p=RA1;:6/93p=QA1<63p=eg02elR@=153p=JP5P@P:g01I7P6P3EGp=Kg01>T#=g01AKg00ijRA#;#;#;RB#;#;#;#]RC#YRDg02e6RE#=RFg00f?1VC8%EA#;#E#;#E#E#E#t311g>8f8RA?O=>P<P8P9P:CN7M7f9RG?OA=RHP<P7P8P9CNRI7M>%2GRJ&084R4,?GRKf:RL?OGARMP=P<P>P7P8CNRNDa[%2A1?A4PHP>PIDaRHAMM=N[PGPAP=P>PIP:J01P3C|PHPJPKP>P=P7P8PMP3GxPJPKP>P=C\1078'3P5%2L1?L4P=PAC\10=>,33X=5P3P<P5P=P0%]B#Y#=,SDRBP5P8P01SDDRKP5P9P0g02d>RJP5P6P0g01M=,SDRMP5P3P?P5%C7RHPKPDPDf@RI#2RN14I4RO%@KRPED7P:f>RQ96NO%@ERE'0P@n0100000020000P@n10110:00020020101108P@n10110900020020103108P@n10110>00020020101108P@n10110=00020020101108n0110600016010410=10>10510910:ROPLPAP=P9CdEG10>7,3OP<P<P5P3P0PBP5P8P0PKP5P9P0PJP5P6P0PMP5P3P?P5PKPDPDfBRO#2RN14O4RRPPED9PH:A6NRI/0EP@n0100000020000P@n10110:00020020101108P@n10110900020020103108P@n10110>00020020101108P@n10110=00020020101108n0110600016010410=10>10510910:10A='3f=RRPGPRPRP4f;RNC:PFPAPED85X6]0PA%=BRS%=KRT%=JRU%=MRVP0PBP5P8P0PKP5P9P0PJP5P6P0PMP5P3P?P5PKPDPDfGRW#2RX14W4RYPPED9PH:fERH96XY/0EP@n0100000020000P@n10110:00020020101108P@n10110900020020103108P@n10110>00020020101108P@n10110=00020020101108fCRY/0O'3P0PBP0PBP5P3P0PKP5P7P0PJP5P9P0PMP5P:P?P5P=P8PKPDPDfIRO#2RX14O4RZPPG<A6XZW/0EP@n0100000020000P@n10110:00020020101108P@n10110900020020103108RZP@n10110>00020020101108P@n10110=00020020101108fDRX,0HR['3PAP6P>P7P8P9fJR\fFR]%2\R^14\4R_fHR`36RaPFPHPED8G7]0P7P0PKP5P8P0PJP5P:P0PMP5P6P?P5P>P9PKPDPD%2`Rb14`4RcPPG<A6bc]/0EP@n0100000020000P@n10110:00020020101108P@n10110900020020103108P@n10110>0002002010110810XY'3P0PKP0PKP5P3P0PJP5P8P0PMP5P9P?P5PAP7PKPDPDP^P_PPG<10aEP@n0100000020000P@n10110:00020020101108RaP@n10110900020020103108P@n10110>0002002010110810]HR_'3PG%@BR^P6P>P7P8fKRcPW%2cRb14c4Rd;6ORePFP]PED8G7]0P713Z[P0PJP0PJP5P3P0PMP5P8P?P5PGP>PKPDPDPbPdPPG<10eEP@n0100000020000ReP@n10110:00020020101108P@n1011090002002010310810W]Rd'3PLP^PPP=P6P7fLRbP`%2bR>14b4R[;6\RZPFPWPED8G7]0P813a_P0PMP0PMP5P3P?P5PLP=PKPDPDP>P[PPG<R[10ZEP@n0100000020000P@n10110:0002002010110810`WRZ'3PNP^PPPA%@JR>P6fMR0PO%20R_1404Ra;6cPFP`PED8G7]0P813edP[P?1B?3PNPAPKPDPDP_PaPPG<=1?3P?PRPLPKPDPDfORa#2R_14a4R[PPG<=1?3P?P5P6fPRdPdP4fNReC:Rf/0ERgP@n010000002000010bcR@'3f?RhP^PPf<RiP>%@MRjfQRk#LRlP0PkPkP4PaC:RmPFPbPED8RnGWRo]0]2P6PiPGPKPDPD%2eRp14e4RqPPG<Rr#5A6_[0R[/0E10c\R_'3P1P5Pg10e0R1,36fAP^PPPQP>PjfSRsPaPsPsP4PkC:RtPFPePED8G7[P313g@10mE100bRm'3P5PFP5PFP3P3PEPEn011020003201031070000X55fRRgPgP4PdC:Ru/0EP1P3EcA1FE0P5P;P5P;P3P6%bgR1$07&061fTRv#2Rw+05&0411VCwRx14v4Ry,VC-03xRz3`&021&001%~1%}1%{1Gz/ygR1#w%b1%v1?`xz1uxz%s15rD3q%p1%o1%n1%k1%l1FmR1P1n011020003201031070101X5510tE10aeP6Ec1HtaA6wyg/HdP3fURyPyP4PsC:/HkP;fVRyPyP4PvC:A1FEgRvP]P^PPPYP>PjfXRYP6PYPYP4PyC:PFPsPED8G7[XB;A1FEkP3PvPFPEPWP^PPPXP>PjfYRv%2vRk14v4RyfW36RYPYPFP3PED8G7XLFP21I63#5%5:RY%56Rw'9[Rt%53,9w1I:6#5Rw[%59/9Y\w1j63P6n2001000000120000000X<?X;?Pt^<?^;?P3%CWRWPXPKPDPDPkPyPPFRRyPLO3%5W%5y'9P2%C`#5PHPKPDPDfZRH#214H4PPFR#5POP^PPP]P>Pjf[R]P]P]P4PvC:RvA1FEER]7QvG7P3%C\#5P`PKPDPDf]Rv#214v4PPFR#5P2A[C63#5A1D:6[RvA1D63A[C:6#5RH[A1D9:\HAiC63P6n2001000000120000000X4DX:DPv^4D^:DP3P0g00ea,hCRCP:O3A1D0CPDPCP3P^PPPbP>PjfaRv%2vRH14v4Ryf_36RW?QW]G7XCDP21A63#5A1T:6[R2A1T631A:6#5RW[A1T9:\W1f63P6n2001000000120000000XATX@TP2^AT^@TP3PbPKPDPDPHPyPPEDRyP9O3A1TbyPTPKPDPDfbRy#2RH14y4R2PPEDRWPCP^PPP3P>PjfcRkPkPkP4PvC:Rv?Qv]G7XDTPCP^PPPWP>PjETRW/eWf`96H2R2/H2RH/9]RC1B<WPHP]1B;21BFEC^C^AXWyCeP0P3E_b9b1PeP3E_b8b1W9W8P6P3O2n2001000000121000000b2b1PsP3EGbGW7PgP3EGb7W3P3O1b3P3O1b3W1P3O1W1n2002102000000101133mPIP^PPPRP>PjPgPePuPFP0PED8G7[X=5P@O1P31B5mO1b1W0W2g01?S91?r%J_RrP5p-0P3g035?R?g00jOP?n011020003201031070000X55R5?K@3R@P?1Fo3b1W0W2n0110001020101P3P:O2b2b4W0P@P?PhP^PPPiP>A>M9:PlPnGW/F3b1X0rX>VX6MP6P3O2n10110801020120101108P3O1W010\ORM#JAK5_3P?PQP^PPPNA>J9:PGPdPbPfPFPcPED8G7/F3b1W0X?UXBJP6P3O2n10110801020120103108P3O1W010O`R`#JAK5M3P?PRP^A>K9:PLPGPAPaPcP[PFP\PED8G7/F3b1W0XFTX6KP6P3O2n10110801020120101108P3O1W0%JZAK5`3P?PiA>B9:PLPGPAP=PeP\A6pqbPFPOPED8G7/F3b1W0XESX6BP6P3O2n10110801020120101108P3O1W0W>W?XDTWFWEXCDP7P8P9P:P6P3O6n0110?01016110;10=10>10<10910:P3O1b0b0b0W0WHWIWKXN;XJ<XM;WQWOWPo"). Qed.

Lemma munmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p'0h05Hspech11Hh21eh32Hah43Hnoh51bi001bh61ci011ch75modelh82msh94segsh:2x8i023evsi031mp;1p;2p;3p;5p;6p;4g00Gjj1FTg00?Zj10Tg00@?j1ATg00@]j1BTg00A^j2TTg00]=j14Tg00A@j1NTg00L<j3=Tg02V0j2KTg02Kbj37Tg035\j1ITg02R4j3;Tg00RWj1STg02=>j21Tg02NMj5ETg02jgj6RTg030Dj4QTg00`Pj2OTg010hj2:Tg00GJj13Tg033bj6MTg036Tj6LTg02Wkj4@Tg02A]j1JTg02Vnj16Tg012ej4CTg00TKj3>Tg02Y3j2?Tg01gIj2DTg01eUj38Tg02Z9j2<Tg02moj4HTg003Tj69Tg034`j2GTg00Y1j1PTf0R0g00lWR1'1p=2g02c4R2g02gkR37=0p=5g01>T#Fg01AKg00ijR4#0#0#0R5#0#0#0#AR6#BR7g01NSg00f?f1R8,T6%44#0#4#0#4#4#4#N3=f3R4/K8f5R9f4R:;74f2R;g02Ro#IR<3;R=f6R>?79:R??;4<%2>R@%S1R1,1>RAf7RB?7>9RCP:P<DE[%291191P?P4P<DER?A;C:<[P>P9P:P4P<P;ERP0CQP?P@PAP:PCg00ea,O6R6%A5#B#F,:7#31:77R5#3RCPCg02d>#3g01M=,:7#3EMR?P0ELP@PAP?P:C@#5P2%2BR:11B1RAP?P9C@%50X62P0g00kWR@P2%J6R6P7P7P:%6ARACC=>5C,?C'DA8:A9g02e6#3RA'<g02elR:n0100000020000R;PBP9P?P4CHE9%5;P7P7f8R7#21171#6CC=>5C,?C,D6P@P@P@P2P0f:R@#211@1#6;87/<AR7P:n0100000020000#5g035?R@]0P0f9R6#21161#6;8B/<A#5P2P7P2p-0R7P0g00jORAP@P@n011010003201031020000X22g01I7RBP3P0E9P@1G@0R6b1W0A=2:3P2P:P2P7P0P@PAP@n011010003201031020000X22PBP3P0E9P@P6b1W0n0110000020000P8O1b5b0b0b0W0%P=eW3W4W7W:W8W9o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma syscall_spec_mmap : forall segs ms x8 model o,
  bv_unsigned x8 = 222%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
         (ms_gpr ms 4) (ms_gpr ms 5) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p;3p;1p;2g00L<j34Tg00GJj13Tg038mj30Tg00K6j21Tg02:bj32Tg00f?R0g039DR1;41%309001110132o"). Qed.

Lemma mmap_errno_range : forall e,
  In e mmap_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h03HInh11ep;3p;1p;2p;4g038mj33Tg03:9j12Tg00K6j20Tg03;>j41Tg00f?R0f0R1g03<IR2530P2f1g00kW%22'0P1C1W0W1o"). Qed.

(* [comment removed for export] *)
Lemma mmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms -> In e mmap_errnos ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok hint model a n = true ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Lemma mmap_succ_ok : forall segs ms x8 model a,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model a Hno Ha Hg.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite (grant_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
  destruct Hg as [[[[H1 H2] H3] H4] H5].
  rewrite Hflags.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
  rewrite H1, H2, H3, H4, H5.
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.

Lemma mmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
      /\ model' = model) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
      /\ model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)).
Proof.
(* [comment removed for export] *)
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hflags in Hspec.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite Hnr in Hspec.
  destruct eff as [r ws zs us cs copyins].
  cbv beta iota zeta in Hspec.
  destruct ws as [|w ws]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  match type of Hspec with
  | (if errno_ret_in ?es r then _ else _) = _ =>
      destruct (errno_ret_in es r) eqn:Herr; rewrite ?Herr in Hspec; cbv beta iota in Hspec
  end.
  - destruct zs as [|z zs]; [|discriminate].
    inversion Hspec; subst.
    split; [reflexivity|]. left.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    exists e. split; [exact HIn|auto].
  - destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
              && (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
              && region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
              && (vm_backing_used model
                  + page_round_up_Z (bv_unsigned (ms_gpr ms 1))
                  <=? vm_limit (m_vmmaps model))%Z) eqn:Hcond;
      rewrite ?Hcond in Hspec.
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
    + unfold grant_ok. exact Hcond.
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.

Lemma mmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  cbv beta iota zeta in Hspec.
  match type of Hspec with
  | (if errno_ret_in ?es ?r then _ else _) = _ =>
      assert (E : errno_ret_in es r = false)
        by (apply errno_ret_in_below; [reflexivity | vm_compute; discriminate]);
      rewrite E in Hspec; cbv beta iota in Hspec
  end.
  match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_mmap_grant : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffect a [] [(a, n)]))
  = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p'0h01nh11Hh22Hch31bh42b1h52b2h62Hmh71ah81eh93memh:1oh;2pch<4regsh=3romh>2svi001zp;1p;2p;3p;4p;8p;6p;5g00?Zj15Tg00]=j1jTg00@?j1ETg00@]j14Tg00>8j2iTg00mbj1VTg03m?j3ZTg010hj2FTg012ej4DTg00GJj1@Tg00TKj3CTg03n?j28Tg03o7j3KTg00L<j31Tg03olj2=Tg040ej1gTg00Nhj1^Tg041]j1\Tg042Tj80Tg00A@j1UTg01E5j3GTg00Gjj1XTg033bj6STg043[j1RTg044Qj17Tg045Pj5>Tg046@j1ATg047@j1:Tg048Aj1BTg049Gj1<Tg04:Fj1?Tg04;Ej19Tg04<Cj16Tg04=Aj1OTg04>:j1NTg04?2j1PTg04?kj3QTg04@dj1MTg04A]j2TTg00`Pj2hTg01EXj3LTg04BVj3HTg014bj2WTg018ij5ITg00K6j2fTg004kj6JTg04CMj1eTg01CMj3]Tg00A^j22Tg04DDj3_Tg003Tj6`Tg034`j2aTg00Y1j1bTg02D8j4[Tg04Dhj2cTg04Eaj1dTg04F^j2YTf7R0f6R1#Af5R2f4R3f3R4f2R5#?f1R6f0R7G0p=3g01AKR8?167p=;g00ij#5R9#jR:#ER;%59R9#5R<#5#5#5#ER=#4R>'i%V>%E<#4R<#V\>R?AZ4671F>>R@P>P>P6P7CD%@@RA3CRB,84AK674RC51?e1=4A/8B=1?CRCePCg00kWRCg01?SPCP8P7f8RBp,2fxRD#gREP0P1%^>RF%\DRGP2P3G0RHP;P>%5:#UR:g01I7RI5G;RJP4%X<,F>#@R<P>P>P4P5CD=C@ARKPAg02d>#@RLg01M=,F>#@RMESRN#R%7HD>%AHRO%:H%BH%<H%?HRP%9H%6HG0n0100000020001RH#7PH%:H%BH%<HPH%9HRQ%ON,=Q%NN'8%PN3Q%MN'T%6HG3RH#7PH%:H%U9R9,h=RN5L=PF%<HPH%9H%6HG3PDAHBJ41W09RHAK452RQP3DI';X3CP>1W19R9P;P>PJP4PBD>RBPBPBPOP0P1PFPPP2P3G0RP#AROP0P1PF%?PRP1=2A/8KRKP3G0RCP7PFPFPCPKP3G3PBPEPHPFPFPGPQP3G0RQ';X3>P?AK563RKPBPBPOP0P1PFPPP7P3G0RPPHPFPFPPP7P3G3/;QX:?P;P>PJP5P0D>RQPEP9PFPFPGPKP4G0,f81=3AP>P>P5P6CD=C@AR@'8R8P7EJAL=1NRP%e1EJPQPQPQP0PEP1P2PFPGP3P4G0RG#AREP1P2PF%?GRQP3P4G0RHP1P2PFPHP8P4G3RHPPPFPFPHP8P4G3PDAH0J5P9PKP4DIR8';eP;P>PJP5P<P@PAPLPMESRM#R%7GD>PE%:G%BG%<GPQ%9G%6GG0RQ#7PQ%:Q%BQ%<QPQ%9QRE%OM,=E%NM'8%PM3Q%MM'T%6QG3RQ#7PQ%:Q=L=NPF%<QPQ%9Q%6QG3/;8R8eP8eg00eaR8=G;IRQ9];JP;PJPQ%4;?1JQRFg04GARN%47R=%46REg00[5%45?167g00f?RL1245124631[RA1256125751L%44?156R@[1234123551L\@A_567P6n2001000000120000000W5W4W0PA^5E^4=^0NP7P;PJPQP6O412;J12;Q51LPLP:PLp-0P7g035?RQg00jOPQn011000003001000010000X8LPIP8P7E`PQ1aQ7b1b2b1W2%bFeC[EJ1cGM#dPDPI1Y;:d9G;:=H05P9PKP4DI';eb6X0>X7>X=?W9W>X;>W<o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
  fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
              && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
           then None else m x.

Lemma unfill_out : forall a n m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  unfill a n m x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h04__x1h14__x2h22Hxh31bh41mh57__arithh64__ffh78__varmaph85__with94__x3h:1ah;1nh<1xp;1p;2p;3p;4p;7p;8p;6g00?Zj15Tg00@?j1ETg00@]j1@Tg00mbj1ITg00A^j20Tg00Fnj24Tg00YJj22Tg00Ogj23Tg01JMR0j2MTg01o7j29Tg020Qj28Tg01gIj26Tg00Nhj1CTg00L<j31Tg00K6j2DTg04G_j2WTg00GJj1VTg00Gjj1UTg00Mgj2ATg00HJj1RTg00Tkj4BTg00Hhj1OTg00IFj1NTg00NEj2:Tg00b\j4>Tg00JTj2LTg00KPj2KTg00LVj3JTg00M5j4HTg02_mj4?Tg03i4j1GTg029Ej2PTg029ej3QTg00]=j1FTg04H?j4STg00cGj7TTg00ckj8YTg004kj6XTg00kWR1f0R2g01?SR331p=7f1R4g00gDR5g00gcR6P6g00hCR7P2g00hcFTp==f3R8P5P6P6P7f2R5P4P2GYp=<P1P3P8P5P4P2EXp=;g00ijR9#5R:#5#5R;#5#5#5#ER<#@R=%E;#@R;#IR>\=10<2R?10<8R@'410<5RA,2@/3?'MP010<4R0f4R?,0<RB'412B@/30P1P>f5R0,0<RC/9A12CBRD,8A'6%C;R;P8P5O1REn0100000020000=1>EP214ACP1P>f7,0<REf6,0<RF'2RG,8BRH,62P;P0P?O1R0n0100000020000=1>0X31P?P8O1RI,D>RJ19F@RK%7K14BE[14@F19EBRL#7[1WF@PIP>g00f?RMg00jkRN#VRO%UNRNPM1AM5RPP4%RMCB%OMRQ%NMRRPM1:M9RSg00f]1:M:R:C>,=RRT%C6R6PTC<1LR7R7P2P5g00l7RT,D11K25=11Tdg00ea=JM4CHRTb6b7b8X0MW114241445[^0M^1MP2f8,0<R<PCP5O3b5b4C?C;W2P2O113DAP1P>16L2P;P0n0100000020000=1>0X31P1P>P2P;P0n0100000020000=1>0X31PJ16K3%GKC;12FCRF,8@RK%7K13GB[13F@%7H[1P@FPIP>POPNPMPPP41AM8CBPQPRPMAQMS:g00iC%F9,:MC>,=RRRP6PRC<P7PTb6b7b8X0MX1MX9M1224/351245/38[^0M^1M^9MP2PCPEP<P5O4b5b4C?C;W2P2O1n200100000021100011000P?P8P5P4CSP5P4O151>eW2X<=W4X;=W:o"). Qed.

Lemma rdn_unfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (unfill a n m) x k = rdn segs m x k.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "h02Hah14__x1h24__x2h34__x3h44__x4h54__x5h61mh72Hdh83Hnwh92Hyh:7__arithh;4__ffh<6__sat0h=6__sat1h>8__varmaph?5__with@1ahA4cstrhB1khC1nhD4segshE1xhF1yp;1p;2p;3p;4p;7p;5p;8g00Gjj1JTg00?Zj13Tg00@?j1CTg00@]j1HTg00mbj1aTg00A^j21Tg01K`j16Tg00YJj22Tg00A@j1ATg00CNj2OTg00Ogj20Tg01JMj2>Tg04H?j3KTg00Fnj28Tg00[5j2ITg04I5j1WTg00Ebj2VTg00FJj3TTg00RWj1:Tg00S6j25Tg00e8j3;Tg00S_j2DTg00GJj1RTg00TKj3BTg00Mgj2ETg00HJj1QTg00Tkj4=Tg00Hhj1PTg00IFj1NTg00NEj27Tg00]=j1?Tg029ej3@Tg00b\j4<Tg00]bj7MTg00Nhj1LTg00JTj2STg00K6j2`Tg00KPj2_Tg00L<j3^Tg00LVj3]Tg00M5j4\Tg04IZj5XTg04JTj7YTg00cGj7ZTg04KLj7[Tg00ckj8UTg00f?R0f1R1g00iCf0R2C<p=9P1g00gDR3g00gcR4P4g00hCR5P2g00hcFZp=4f2R6P3P4P4P5P1P2F[p=Ff3R7P3P4P4P5P6P1P2GUp=Gg01>T#Jg00ijR8#3R9#3R:#3R;#3#3#3R<#CR=#HR>%C;#H#aR;\>g01M=11=1%62'2%A9R?%A<R<'OR@'011=6RA%61'2f5RB,1=RC'0f4RD,1=RE,2C/0A'>f7RAP6f6RC?KBDPDP7P111=2RF,0E%67,2E,8F'If8PAPCP1%WDg00eaRF%6D'01V?<18F?10F<18F@[[10F?REg00jORGAT?<1UW010F@\G^0Ef9REPDO1P;g00jkR;g00lWRG#:R@#:R<#:R?,50150<R<150@5;05;0g00m6R@'D%:?,50150G9;0<5;0/D@%R;5B;3B%J;P0P01E0DP6%Q0R;C=P1P01E0BP7P;C=C=%P0%N0R;P;P3P4P4P5170:R:1708R3'9,4;P0P3g00f]R@%?9,709@0:R<C<,4;FM%L4R4P;1709R9,9<,4;%?8,709@09R8/9:,4;5F;P4P0P3P@P9C<,4;1983,4;5F;CGCG1S;5P2P6g00kWR;g00l7R5'`1_26=^;5dA]0F1C\b;b>b?X10X20X30X40X501072127DRF,82'I12DB/061267/0D'>186710F6'>[[^10^20^30^40^50P2%6Ef:,1=f<,1=f=,1=11=CPBPAO7b:b6b<b=bADXW9XF>FYW7W8WBXE>W6XC>W@WDo"). Qed.

(* [comment removed for export] *)
Lemma adv_munmap : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"] "p'0h01bh11nh21Hh32Hch42b1h52b2h62Hmh71ah81eh93memh:1oh;2pch<4regsh=3romh>2svh?1xh@1zi001zp;1p;2p;4p;3p;6p;5p;8g00?Zj15Tg00]=j1uTg00@?j1MTg00@]j14Tg00>8j2tTg00mbj1^Tg010hj2ITg012ej4LTg00GJj1?Tg00TKj3HTg03olj2=j3dTg04H?j3Fj4cTg00A^j20Tg01o7j2QTg00YJj2PTg020Qj2OTg01gIj2GTg00Nhj1[Tg00L<j31Tg00K6j2YTg02[Cj2rTg04L0j1kTg004kj6@Tg04LOj3gTg04Llj3fTg04MIj3eTg04Mej5bTg03n?j2>Tg00Gjj1aTg04A]j2<Tg040ej1`Tg041]j1_Tg042Tj82Tg00A@j1STg01E5j3ETg00`Pj2RTg033bj6TTg043[j1UTg044Qj16Tg045Pj5DTg046@j1CTg047@j17Tg048Aj1ATg049Gj1:Tg04:Fj1BTg04;Ej19Tg04<Cj1;Tg04=Aj1]Tg04>:j1\Tg04?2j1VTg04?kj3WTg04@dj1XTg01EXj3JTg04BVj3KTg014bj2ZTg018ij5NTg04CMj1sTg01CMj3qTg04DDj3pTg003Tj6oTg034`j2lTg00Y1j1mTg02D8j4nTg04Dhj2jTg04Eaj1iTg04F^j2hTf7R0f6R1#Cf5R2f4R3f3R4f2R5#Bf1R6f0R7G2p=3g01AKR8?167p=8g00ij#5R9#uR:#MR;%59R9#5R<#5#5#5#MR=#4R>'t%^>%M<#4R<#^R?\>R@P>P?1I>>RAP>P>P6P7CL%?ARB3H,=4RCAF674RDg00kWRE10=5RF10=7RG'Q10=6RH,PF,OG'GRGPEP?P7%[<RIP2P6O1RJn0100000020000PEP?10=4RK/QH1PKF,OH'GPIPJn010000002000051?X0EPEP?PGPIP3P7O1RJn0100000020000RK,Y?g01?SRF,rG%kGE@PEP?Ag>>7,0=RG/QHAf>>7,0=,PG,OH'GX@AP>P>P5P6CL=HABRH5eAPIPJn0100000020000=1?KeAd3H7P5P6P3P7Cc51?eX?>Db1>CB%a<,I>#?R<'<=1@DRDePDPEPFPEP8P7f8RFp,2fxRD#`RCP0P1%[>R?%_DRKP2P3G2RJP;P>%5:#SR:g01I7RI5E;RGg00eaRL,R=RMP<PBP>P>P4P5CL=HABRAg02d>#?RNg01M=,I>#?ROETRP#U%6JDD%CJRQ%7J%AJ%:J%BJRR%9J%;JG2n0100000020001RJ#6PJ%7J%AJ%:JPJ%9JRS%]P,=S%\P'>%VP3W%XP'<%;JG3RJ#6PJ%7J%S9R9,R=RP5J=P?%:JPJ%9J%;JG3PDAKFGM1Z09RJAF452RSP3DN'8X0EP>1Z19R9P;P>PGPMPFDDRFPFPFPQP0P1P?PRP2P3G2RR#CRQP0P1P?%BRRR1=2A/>B/<<RAP3G2REP7P?P?PEPAP3G3PFPCPJP?P?PKPSP3G2RS'8X0>P@AF563RAPFPFPQP0P1P?PRP7P3G2RRPJP?P?PRP7P3G3/8SX:@P;P>PGPMP0DDRSPCP9P?P?PKPAP4G2,Y81=3H/>B/<<R8P7E@AJ=1PRR%s1E@PSPSPSP0PCP1P2P?PKP3P4G2RK#CRCP1P2P?%BKRSP3P4G2RJP1P2P?PJP8P4G3RJPRP?P?PJP8P4G3PDAK0GMP9PAP4DNR8'8eP;P>PGPMP<PBPHPNPOETRO#U%6KDDPC%7K%AK%:KPS%9K%;KG2RS#6PS%7S%AS%:SPS%9SRC%]O,=C%\O'>%VO3W%XO'<%;SG3RS#6PS%7S=J=PP?%:SPS%9S%;SG3/88R8eP8eAE;LIR89q;GP;PGP8%4;?1G8RSg04GAR?%47RP%46R=g00[5%45?167g00f?RC1045104631[RN1056105751C%44?156RH[1034103551C\HAp567P6n2001000000120000000W5W4W1PN^5=^4P^1?P7P;PGP8P6O410;G10;851CPCP:PCp-0P7g035?R8g00jOP8n011000003001000010000X8CPIPLP7EoP81l87b2b3b2W3%mSeCnE@1jKO#iPDPI1h;:d9E;:=K0MP9PAP4DN'8eb6X1>X7>X=@W9W>X;>W<o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
    (1 <= length buf)%nat ->
    twm_pend ms model buf bufs code ->
    twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(* [comment removed for export] *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
         (skipn n rest) bufs code) ->
    twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
    twm ms model bufs code ->
    twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
    (1 <= length rest)%nat ->
    twm_pend ms model rest bufs code ->
    twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm_tail ms' model rest bufs code ->
    twm_tail ms model rest bufs code.

Scheme twm_min := Minimality for twm Sort Prop
  with twm_pend_min := Minimality for twm_pend Sort Prop
  with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.

Lemma msteps_twm : forall ms ms' model bufs code,
  msteps segs ms ms' -> twm ms' model bufs code -> twm ms model bufs code.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "h02msh11Hh23ms'h32H0h42H1h52Hwh68IHmstepsh74bufsh84codeh95modelh:4ms''p;1p;3p;4p;2p;8p;7g00?Zj11Tg00@?j15Tg00@]j13Tg00Gjj12Tg04Ngj36Tg04O^j40Tg00mbj1<Tg048Aj1;Tg00Nhj1:Tg00L<j34Tg017aj17Tg019^j28Tg01;Pj29Tg04PSj8>Tg04QHj7=Tg01AKR0g01NSg00ij#1#1#1R1#5#3#2#2%11#1#1#5#3R1p,4segsR2f4R3f3R436P2f0R5f5R6P3P4C0f2R7f6R8P6P3C0[X20X00P5P3P4P7C0P5W1X00%<1%;7%:134%701824190734A6247P4f9R7f8R2f7R1C0P6f:R9P7P2C0[P3P9P7P2C0P1P8f;P9P7P3P4f1P5O1G>W5W6W4W3W1X:0X20X00P6P3P5F=W1W8W7W9X20W0o"). Qed.

Lemma msteps_twm_tail : forall ms ms' model rest bufs code,
  msteps segs ms ms' -> twm_tail ms' model rest bufs code ->
  twm_tail ms model rest bufs code.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "h02msh11Hh23ms'h32H0h42H1h52Hwh68IHmstepsh74bufsh84codeh95modelh:4ms''h;4restp;1p;3p;5p;2p;9p;7g00?Zj11Tg00@?j15Tg00@]j13Tg00Gjj12Tg04Ngj36Tg04RAj50Tg00mbj1<Tg048Aj1;Tg00Nhj1:Tg00L<j34Tg017aj17Tg019^j28Tg01;Pj29Tg04S6l9>Tg04QHj7=Tg01AKR0g01NSg00ij#1#1#1R1#5#3#2R2%22%11#1#1#5#3R1p,4segsR2f5R3f4R436P2f0R5f6R6P3P4f3R7D0f2R8f7R9P6P3P4D0[X20X00P5P3P4P7P8D0P5W1X00%<1%;8%:134%701827190834A6278P7f:R8f9R2f8R1P9D0P3f;R:P8P2P1D0[P4P:P8P2P1D0P9P6f<P:P8P2P4P7f1P5O1M9>W5W6W4W3W1X:0X20X00P6P3P5F=W1W8W7W;W9X20W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma twm_write_ret : forall regs pc mem rom model buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n buf))) (v_addi pc 4) mem rom)
       model (skipn n buf) bufs code) ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model (buf :: bufs) code.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "h01nh11Hh21bh32b1h42b2h53E10h63E11h73E12h83H10h93H17h:5Hconth;3Hn1h<3Hn2h=3Hnbh>2Hrh?3bufh@4bufshA4codehB1mhC3memhD5modelhE2pchF4regshG3romp;1p;2p;3p;8p;5p;6p;7p;<g00?Zj11Tg00]=j1@Tg00@?j1DTg00@]j15Tg00>8j2[Tg00mbj1FTg00Gjj1OTg00A@j17Tg04F^j2;Tg01E5j33Tg013Ej28Tg00A^j24Tg00L<j30Tg04Skj22Tg00`Pj2?Tg040ej1VTg00oFj26Tg00Nhj1UTg041]j1TTg042Tj8=Tg04TUj39Tg00RWj1NTg002Dj2CTg04UZj2>Tg04V4j3MTg04VSj2LTg04BVj3KTg014bj2HTg018ij5GTg04WKj3ITg04RAj5JTg04DDj3RTg01K`j1BTg00YJj2ATg00K6j2:Tg048Aj1QTg004kj6<Tg044Qj1PTg02=>j2ETg04Wij2STg04Eaj1ZTg04Xij7YTg04Y`l<XTg04ZUj7WTg00ijR0#1R1#@R2#DR3%11R1#1R4#1#1#1R5#DR6#5R7'[%D4#5R8#F\7R9g01NS%O8R:%O:g00f?R;f7R<%@4#7R4g01I7R=1;34d533R>'8,46%7530f8R5%12#7R?P=1;3?d533R@'2%70,?6R6507%F:RAf9RBp,2fxRC#VRDP518B>,67%U7R>%TCREP<f6RFG=%@2#7R2P=1;32d533RG,2B%@0#1#1#7R0P=1;30d533RH,2B39f4RI,6:30g00lWRJ#NRKf5RL,C8'>g01M=RMf0RN,>KROf1RP1C85'>PCf>RQf2RR=M8B,L87K@f=RS%71R1'Hf<RTf;RUDGf:RVAI8RBP5P<DJ[[]0g04GARW%5NRX%5PRYg00[5%5R?0PNf3RZ/4R14ZP50;R[[14RP14RN50;%5Z?0RP[R\%5I?0ZR\[ARRPNPNn2001000000120000000W4W3W0R[P\^4Y^3X^0WRWPNP3%BJ,A?,?3RXA33?=RY143Y,:;O4b1%53R\P@P\e70XP[PWPNP3%BK,A?,?3R@A332=R21432,:;O4b1PGP\e90\@P[PWPNP3%NKRW#B,A?,?3R?A330=R01430,:;O4b1PHP\e90\?f?RHPDPQA334=R=,8HR4,67R3P>PEPSPTG=R;PUPVPBP5PIP;PUP4PVPBP5%F7R5/:3%Q;=053eP<P\PYf@R</2NR5=076X2\PFPXPRE<%P;R3/2X=076e1E;J=076eP\P2P<PDPH18<=,67P>PEPQPSG=R612<?79516:URU50AX2\P\P012<2=965=0AUX2\PLP?PNE<P@PPE<123@123?59;16:VRV50Ae1E;K1E;W59;=0AVePI1C8T,>Pg01AKRIPCfBRVAM8RS,L8RA7KYfARY/H1P<PHDGPNPHAI8ZQPSPTDJXBIPFPRPPPNO3PVPDPY18V=,67R=P>PEP<PHG=/SA#ZPCPVPYP=P<PHPAFYE<W<X;OX0MM<XFWb7b6b5W:W=W>W8W9XA7W@W?WDXG9WCXE7WFo"). Qed.

(* [comment removed for export] *)
Lemma twm_tail_write_rec : forall regs pc mem rom model rest bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n rest))) (v_addi pc 4) mem rom)
       model (skipn n rest) bufs code) ->
  twm_tail {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
              ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
              ms_mem := mem; ms_rom := rom |}
    model rest bufs code.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "h01nh11Hh21bh32b1h42b2h53E10h63E11h73E12h83H10h93H17h:5Hconth;3Hn1h<3Hn2h=3Hnbh>2Hrh?4bufsh@4codehA1mhB3memhC5modelhD2pchE4regshF4resthG3romp;1p;2p;3p;8p;5p;6p;7p;<g00?Zj11Tg00]=j1@Tg00@?j1DTg00@]j15Tg00>8j2[Tg00mbj1FTg00Gjj1OTg00A@j17Tg04F^j2;Tg01E5j33Tg013Ej28Tg00A^j24Tg00L<j30Tg04Skj22Tg00`Pj2?Tg040ej1VTg00oFj26Tg00Nhj1UTg041]j1TTg042Tj8=Tg04TUj39Tg00RWj1NTg002Dj2CTg04UZj2>Tg04V4j3MTg04VSj2LTg04BVj3KTg014bj2HTg018ij5GTg04WKj3ITg04RAj5JTg04DDj3RTg01K`j1BTg00YJj2ATg00K6j2:Tg048Aj1QTg004kj6<Tg044Qj1PTg02=>j2ETg04Wij2STg04Eaj1ZTg04Xij7YTg04Y`l<XTg04[Jj7WTg00ijR0#1R1#@R2#DR3%11R1#1R4#1#1#1R5#DR6#5R7'[%D4#5R8#F\7R9g01NS%O8R:%O:g00f?R;f7R<%@4#7R4g01I7R=1;34d533R>'8,46%7530f8R5%12#7R?P=1;3?d533R@'2%70,?6R6507%F:RAf9RBp,2fxRC#VRDP518B>,67%U7R>%TCREP<f6RFG=%@2#7R2P=1;32d533RG,2B%@0#1#1#7R0P=1;30d533RH,2B39f4RI,6:30g00lWRJ#NRKf5RL,C8'>g01M=RMf0RN,>KROf1RP1C85'>PCf>RQf2RR=M8B,L87K@f=RS%71R1'Hf<RTf;RUDGf:RVAI8RBP5P<DJ[[]0g04GARW%5NRX%5PRYg00[5%5R?0PNf3RZ/4R14ZP50;R[[14RP14RN50;%5Z?0RP[R\%5I?0ZR\[ARRPNPNn2001000000120000000W4W3W0R[P\^4Y^3X^0WRWPNP3%BJ,A?,?3RXA33?=RY143Y,:;O4b1%53R\P@P\e70XP[PWPNP3%BK,A?,?3R@A332=R21432,:;O4b1PGP\e90\@P[PWPNP3%NKRW#B,A?,?3R?A330=R01430,:;O4b1PHP\e90\?f?RHPDPQA334=R=,8HR4,67R3P>PEPSPTG=R;PUPVPBP5PIP;PUP4PVPBP5%F7R5/:3%Q;=053eP<P\PYf@R</2NR5=076X2\PFPXPRE<%P;R3/2X=076e1E;J=076eP\P2P<PDPH18<=,67P>PEPQPSG=R612<?79516:URU50AX2\P\P012<2=965=0AUX2\PLP?PNE<P@PPE<123@123?59;16:VRV50Ae1E;K1E;W59;=0AVePI1C8T,>Pg01AKRIPCfBRVAM8RS,L8RA7KYfARY/H1P<PHDGPNPHAI8ZQPSPTDJXAIPFPRPPPNO3PVPDPY18V=,67R=P>PEP<PHG=/SA#ZPCPVPYP=P<PHPAFYE<W<X;OX0MM<XFWb7b6b5W:W=W>W8W9X@7W?WFWCXG9WBXD7WEo"). Qed.

(* [comment removed for export] *)
Lemma twm_munmap_rec : forall regs pc mem rom model bufs code (a nlen : word),
  bv_unsigned (getr regs 17) = 215%Z ->
  reg_get regs 10 = a ->
  reg_get regs 11 = nlen ->
  (bv_unsigned a mod page_size = 0)%Z ->
  nlen <> Z_to_bv 64 0 ->
  (bv_unsigned a + page_round_up_Z (bv_unsigned nlen) <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (page_round_up nlen) = true ->
  twm (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
            (unfill a (page_round_up nlen) mem) rom)
      (munmap_model a (page_round_up nlen) model) bufs code ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model bufs code.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "h01bh11Hh22b1h32b2h41nh53E10h63E11h73H17h82Hah93Halh:5Hconth;4Hhash<4Hlenh=2Hnh>3Hnwh?1ah@4bufshA4codehB1mhC3memhD5modelhE4nlenhF2pchG4regshH3romp;1p;2p;3p;5p;8p;4p;6p;7p;9g00?Zj17Tg00]=j19Tg00@?j1MTg00@]j18Tg00>8j2mTg00mbj1\Tg00Gjj1]Tg00A@j1HTg04F^j2NTg01E5j3ETg013Ej2LTg00A^j20Tg00L<j31Tg04Skj23Tg00`Pj2QTg00Y1j1@Tg02`Hj1?Tg00YJj25Tg01R]j1PTg01TNj1OTg02Vnj12Tg02aFj3>Tg04BVj3ZTg014bj2YTg04H?j3XTg018ij5WTg04DDj3bTg01K`j1VTg00K6j2KTg00RWj1aTg040ej1`Tg00oFj2UTg00Nhj1_Tg041]j1^Tg042Tj8TTg048Aj1lTg00[5R0j26Tg021nj4STg004kj64Tg044Qj1kTg02V0j2jTg010hj2RTg00GJj1JTg012ej4DTg00TKj3GTg033bj6FTg04Dhj2BTg04Eaj1;Tg04\?j7hTg02i5j1gTg02=>j2[Tg04]9l9fTg00DHj2eTg00Ogj2dTg01eUj3iTg04O^j4cTf0R1g024e'ep=Cg00f?R2g00eaR3711p=Ag02b<,d1p=<g00kWg00l7711p==f5R4f4R5f3R6f2R73if1R8P1Ccp=:1681,67p=Ig00ijR9#7R:#9R;#MR<%7:R:#7R=#7#7#7#MR>#8R?'m%M=#8R@#\\?RAg01NS%]@R@#]f8RB%9=#HR=g01I7RC1N<=d5E<'L,0>%99#7#9#7#9#9#9#H512f9R9%7;#HRDPC1N<Dd5E<RE'3=1?7f:RF%9;#HR;PC1N<;d5E<RG'3=1?710>5#C#A1Q>3R391?5#@f6RH,0>10>4#?'5#<%PF#Of7RI%2H3>#=p,2fxRJf?RK?ZE3f>RL%H:R:'Y%2IRMf=RN5XBf<RODWPBPMf;RMPFP9E:g04GARP%81RQ%88RRP0%87?18110671068512R0[10781071512%86?178[RS%85?167\0Ab781P1n2001000000120000000W3W2W4R0PS^3R^2Q^4PRPP1P<g00lWRQ#V,5D,Q<RRAE<DCRS10<S,K2O4b1%8<RTPEPTe71RP0PPP1P<%aQRP#V,5D,Q<RDAE<;CR;10<;,K2O4b1PGPTe91TDfBRG%`JR2fAR0AE<=CRC,LGR=,U?R<%_?RE%^JRUf@RVPKGTRWPLP=PNPO%\?R=/K<%lW=1=<eP9PTPSfCR9/31R=,0>RX#C#A139DRY=1?3#@10>Y#?,5X#<%PK#ORZ%2YRY7>=#='63IX0TPTP;139SR[,0>R\#C#AA1?=3#@%?X,5\#<%2=R\9>Z[#='63IX0TP?PM10>1RX#C#A139;R]=1?3#@10>]#?,5X#<%2]R]9>Z1#='63IX0?P?PF10>OR^#C#AA1?13#@%?X,5^#<%21R^9>ZO#='63IX0?10>MRZ#C#AA1?F3#@RX10>F#?,5Z#<RZ%PL#OR_%2FR`7>M#=Ra'6Rb'6PHPXPbP4PZPaP5P6CSCSCS13G;R6PIE413GSR5PBE4PDP1E4PRP8E4%kWRa/3RRZ,0>R4#C#A13aDRa=1?3#@10>a#?,54#<%2aRa9>_Z#='63Ie1jWLePTPSP9P2PG1L9C,U?PEPUP0PVGTRUP31R?@#JR@1R??RE#JR9P?P?P=PYCD=GE9g02d>#JRCg01M=,R?#JR2EF'B#;P=PYPKPLPNE:X0TPTP;P3P@P9P?P?P[P\CD=GE9PCP2EF,BU#;P[P\PKPLPNE:X0TP?PMP3P@P9P?P?P1P]CD=GE9PCP2EF,BU#;P1P]PKPLPNE:X0?P?PFP3P@P9P?P?POP^CD=GE9PCP2EF,BU#;POP^PKPLPNE:X0?g01AKR^PJAZGS31Y0:AXM`VPKDWP1PO%2MPKPLPNE:XB^P7P3P@P9P?P?PMP`CD=GE9PCP2EF,BW#;PGP0P<PVPKPMP`FhE4P6PIE4P5PBE4PDP1E4PRP8E4P3P@P9P?P?PZPaCD=GE9PCP2EF,BW#;PZPaPLPNPOE:e%gW,BW#;1[WQ1[WP#2PLPNPOE:eM9fb6b5W:W;W>W<W9W=W8W7XE?X??XA?W@WDXHAWCXF?WGo"). Qed.

(* [comment removed for export] *)
Lemma twm_exit_coden : forall regs pc mem rom model (c : word),
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model [] c.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "h01bh12b1h22b2h31ch41nh53E10h61Hh73H10h83H17h92Hch:2Hgh;3memh<5modelh=2pch>4regsh?3romp;1p;2p;3p;6p;8p;4p;5g00?Zj12Tg00]=j11Tg00@?j1<Tg00@]j14Tg00>8j2STg00mbj1BTg00A@j15Tg04F^j2>Tg01E5j3:Tg013Ej27Tg00A^j23Tg00L<j30Tg04Skj29Tg00Fnj2RTg04DDj3QTg01K`j1PTg00YJj2MTg00`Pj2ATg00K6j2@Tg04]nj36Tg04^Sj2LTg004kj6?Tg040ej1JTg00oFj28Tg00Nhj1ITg041]j1GTg042Tj8;Tg044Qj1HTg02=>j2=Tg00Gjj1FTg00GJj1KTg04O^j4ETg048Aj1DTg02:bj3NTg04_Qj5CTg003Tj6OTg00ijR0#2R1#1R2#<R3%21#2R1#2#2#2R4#<R5#4R6'S%<1#4R7#B\6R8g01NSg00f?R9f5R:%11#5R1g01I7R;1>31d5:3R<'7,35%12#1R=#2#1#5R>30f6R?%22#5R2P;1>32d5:3R@'9f1RA506f2RB,35%24#2#5'Rg04GAR4f0RC#4RD%4AREg00[5%4B?0ACf3RF/3B13FA509RG[13BA13BC509%4F?0BA[RHf4RI#4?0FB\GAQBACPCn2001000000120000000W2W1W4PH^2E^1D^44PCP3g00lWR4#P,M2,A3RDA:32;R21332,@9O4b6%43REP@PEe70DPEP2f:R@/9C%10#1#1#1#1#1#1#5,A5R0565=06:X0EP6PIA65C0=06:X061LIAf9RA/92PBE?PDPCE?PAp,2fxRB#JR2f8REA:31;R;,7A,86%I6R1%GBRBf7R3P?G;RH#H/9D=650=06Ie1=H4=650=06IePAP2PE17A<,86P1PBP3P?G;/=4=650=06IP6P@P2PA17@;R<,86RHP1PBPEP3G;RD/=4=650f;R0P2P@170;,86P1PBPAPEG;P3%F7#KPCCEX36PDP?P<%B6R?/@H%DD=0?He135<R<=09>%1=#2#5909<;NIDCP:PCEOb:b5W9W7W8X36W<X?8W;X=6W>o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_munmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "p'0h01Hh12H1h22H3h32H0h42H2h52H4h63Hssh72H5h82H6h92H7h:1mi001mh;2x0h<1li011lh=6model'i026model'h>1si031sh?3evsi043evsh@6model0hA3ms0hB2sthC1oi051ohD3effi063effhE2HxhF1ehG4evs0hH2HmhI1ahJ1thK4HeffhL3HeqhM4HevshN2_HhO3_H0hP7model''i077model''hQ5HargshR2HhhS3HhnhT5HlazyhU3HnohV4HsvchW1ci081chX4codei094codehY5modeli0:5modelhZ2msi0;2msh[3ms'i0<3ms'h\3sigi0=3sigh]2x8i0>2x8i0?9cfg_modeli0@6cfg_msp%0p%1p%2p&0p;1p;2p;3p;4p;6p;7p;:p;8p;9g00?Zj1ZTg00@?k10nTg00@]k10dTg00Gjk10:Tg00mbS00k10GTg00Nhk10DTg010hk20CTg01Q2k10ATg00GJk10<Tg00L<S01j30Tg00oFj25Tg00A^k200Tg00]=j1rTg00A@k10hTg02V0k20gTg04`Fj21Tg04a;R0j46Tg00RWk10cTg01M\j1ATg048Aj1HTg017ak10`Tg04aoj3QTg01;Pj2pTg00[5S02j24Tg04bkj1>Tg04caj4STg0040j6@Tg003Tj67j7Kk80ITg034`j2dTg04d=k10fTg04eEk10eTg02Kbj3GTg04Dhj2LTg02i5j18Tg004Nj6^Tg04fMl:zTg01eUj3hTg04gJj1vTg04hPj2wTg04iYk40?Tg04j]k30>Tg01R]k10=Tg01STk10bTg01TNk10aTg01UDk20_Tg01V=k10^Tg00YJk20]Tg01W7k30;Tg01X3k10\Tg01Xnk10[Tg01Yck10ZTg01ZZk10YTg01[Uk10XTg01\Nk80WTg0323k20VTg01Qjk10UTg01d9k20TTg01]Ek10STg01e:k30RTg01^Ek30QTg01_=k10PTg01`0k10OTg01`ek10NTg01aZk10MTg01bNk10LTg01cCk70JTg00K6j2eTg021nk40KTg004kj8bl9uj6tk70Hm:0mTg01OIj1?Tg02R4j3fTg04knj1}Tg04lej2\Tg04m[k30FTg04n^j2]Tg04oTk20lTg035\k10kTg050\k70jTg02=>j2kTg02Vnk105Tg04Eaj1[Tg012ek40iTg02iok406Tg00TKk304Tg00<_k30ETf2R1f1R2#Af0R330p=:%H2=013p=Bg051_S03?023p=Ig052TR4?023p=V%83,L2p=jf3R5g00lWR6'k1k12$05;h3p=2%[2/13p=g%>39042p=cA0512/43p=Eg01AKR7g01NSR8P2P3H0ip=q%>2=043p=~Q03P8P5P1P2P3E^p=nA0823p=3Q03P7P5P1P2P3E^p=mA0723p==f5R9f4R:#8'L#[1k561k12$05;h3'1#>p=PA0423,41p=a1112#>=043p=X1123#>p=F%83,L2#[p=Y1123#>9041,45p=WP:1151P2P3C6p=MP8P:P5P1P2P3Etp=`P7P:P5P1P2P3Etp=_g053JS04=043p=<P4Q04P:P5P1P2P3FKp>03P4Q04P5P1P2P3E7p=|g02RoR;P1P2P3H069f:5p=91583p=;%v2,w1=053p=J%[1/12#>=043p={%v3,w2p>0215839012p=i1L12#[/13#>p=U1L12#[/13p=sA0:51%>2=043'4p=Rf6R<?G9:P;P1P2P3H067f5p=T1L23#[p>0BA0;23p=N%82,L1#[/13#>p>01P5P1P2%>3C6p>0@1k36p=y1k23$05p=xP;P1P2P3H06p=oAG:51?f23p=D%}2=013p=Og02e6R=1\12<043p>09B0E=12=053p=lB04=23:0E=1p=C15239051p>081]12>04=3p>07g00ijR>#Z#Z#Z#Z#Z#Z$0nS05$0dR?&0:=R@&0G?RA&0D?RB7:520C??RC$0:&0A:&0<C3015?:9BA<S06g00f?Q050009%r>#Z#r#Z#r#r#r$0h30f8R>f7RC+0gp,4segsRDf9RE/1>S07P<P9C6P0PDf>R0f=RF'1S08,I5f<RG90@51V5GP@P0&0<=R=fARH/jHPHPH&0c6R6f@RIC2'g,cFCE[[[P3%A1S09=0ABRJ%H:S0:=0ABRK20C78RL$0`RMAQD9:1q51,pL3011<9RNfHROfGRP'1RQ'IfFRR90@=1~NRQ07fKRNfJRS'1S0;'IQ03Q03P8P3P3n0110800012010@10?WFS0<f:RT/1ES0=fLRU/1NP3Cn13ENQ03Q03P7P3P2n0110800012010@10?WFS0>f;RV/1TS0?fMRW/1UP2Cm1=VWfNRX,=GP3fORY,=FfPRZ130ZR[A0@=YR\f?R]/10S0@/~YA:AHBfCR^9QD9fBR_/qH,pL50MfTR`=0@=S0AfSRafWRbPbPbPbP6fVRcEPS0B'VS0C'4]1^3K]0]5]2[X:713FYP3P[fQR[A0@=ZRd11I]S0D/~ZRe%HcS0E=0ABAQDb:1q^_,pL50MfURf=0@=S0FfXRgPgPgPgP6PbEPS0G7a`]1]3^0J]5]2X:8P3PdP@P=AXHI[RdA:AfBRh%HbRi=0ABRjAQDgbfDRk/q^,pL50MRlA0@:=S0HfYRmPmPmPmP6PgEPS0I7af]1]3]0]5X<@P3PdP41F_H%AcRd=0ABABAgBAQDmgfERn/qk,pL50MA0@==RofZRpPpPpPpP6PmEPS0J7a5]1]3]0X>4P@P=PD11pmRqP3PcC6Po11PRRr#>f[Rs/YsPsPsP6PpC2CW]6X?@PD11mgS0KP=PfC6P411RnS0L#>RtPDPsPpP=P3DMPo%>Qf\Ru/YuPuPuP6PsC2CW]6XB4PDPqP=PtC6PAPB%HsS0M15?mS0NPAQ0MPBP5CSRtPAQ0MPBQ0NP5PAPB%ApRqQ0NPAPqPBP:CSPAPqPBQ0NP:PAPBQ0MQ0NPtP`E@E@E@E@E@Q0N90ABPAPBQ00P?p-0S0OP3g035?Rtg00jOS0Pn10110500021000000XFAS0Qg01I7S0R15?pS0SP3E7PtPofIRq/1OS0T#>f]Rv/YvPvPvP6PuC2CW/d3b0bLW6PcP9P3FKW6PcP<PYFKX7lX4jX1hfRRhP3E7b1X5eP[P3E7b1X2\P]P3D`b1W3P0P3D_b3W0P3O1b0P3O1b0W4P1P2P3P9P:P5O6W5W2W4W1W3W0X=8X[7X@8XA7P<P9P:P5P1P2P3O7A:A3BS0UABA1BS0VAQD51S0W&0fLR\50M11:511k^'IS0XA0@=_S0Y%<_S0Z11C</IrS0[Q0<11>CS0\PQP3CnS0]13CPS0^Q0>Q07Q0TP2CmS0_1=EqS0`1=TSS0aP31=VNS0bPU13GURQA0@=NRr%<NS0cA:A]BS0dAQD9HS0e=0M\A0@Z=S0fPY1YaaPaPaP6PhC2CWS0g]1^3K]0]5]2[X:713VNS0hP3PQPWA0@=URe%<URjABAhBRlAQDa:Rw=0M\A0@[=S0iPZ1Y``P`P`P6PaC2CWS0j]1]3^0J]5]2X:8P3PeP@P=%<WS0kA:A[BRxABAaBRyAQD`aRz=0M\R{Q0H1jffPfPfP6P`C2'g,c[S0l'4S0m]1]3]0]5X<@P3Q0kA:AhBR|%H`S0n=0ABR}AQDf`R~=0M\PcPcPcPcP6PfEPS0o9ao5S0p]1]3]0X>4P@P=PD11cfS0qP3PhC6Q0B#<,4o]6X?@PD11f`S0BP=P[C6PD11bcS0rP=P3C6Q0G#<,4o]6XB4PDQ0qP=Q04C6PAPBPi15?fR\PAPiPBP5CSS0sPAPiPBP\P5PAPBPdP\PAPdPBP:CSPAPdPBP\P:PAPBPiP\Q0sPZE@E@E@E@E@A0AB\PAPBQ0QQ0R15?cS0sP3E7PtQ0I#<,4oS0I/d3b0bLW6PhP9P3I03W6PhP<PNFKR\X7{X4yX1xPXP3C|b1X5jPWP3E7b1X2rPFP3D`b1W3PGP3D_b3W0P3O1b0P3O1b0W4P1P2P3P9P:P5O6W5W2W4W1W3W0X@8XA7P:P5P1P2P3O5Q0UQ0VQ0W&0eLRL50MQ0XQ0YQ0ZQ0[Q0]Q0^Q0_Q0`Q0aP3Q0bPUQ0cQ0dQ0e=0MLQ0g]1^3K]0]5^2r\QX:7Q0hP3PQPWA0MwLQ0j]1^3l^0J^5j^2eX:8P3PeP@P=Q0kA0MzLRzQ0m]1^3y^0x]5X<@P3Q0kA0M~LQ0p]1^3}^0|X>4P\X7zX4yX1xPXP3C|b1X5jPWP3E7b1X2rPFP3D`b1W3PGP3D_b3W0P3O1b0P3O1b0W4P1P2P3P9P:P5O6W5W2W4W1W3W0X@8XA7P:P5P1P2P3O5%A9S0U=0ABS0V15?99BACS0XAGD><S0YPCP9P:P1D9Q0V&0G8RrP<PC%;9CJQ0?11h['IS0ZA0@<Z1LFT?{>ZQ08Q0B'IS0[Q0<Q0@Q0qP3CnS0q130fS0aQ0>Q0DQ0rP2CmS0D1=IbS0h1=HgS0pP31=_mS0mPp13^pS0jA0@]mS0c1L1^?{Hm%ARS0d=0ABS0gQ0:15?RS0e50AS0bAGD9PS0`POPRPnP^D9Q0g202POS0_=irRP@f`RjP=f_RxfcRyPyPyPyP6fbRzEPS0^'VS0]CES0W]2]4]1]3]0]8]7[X:713_mS0tP3Q0jPsA0@IpR\f^R|/Lk?{_pS0u%HjS0v15?PS0w50AS0xfaR}=GDOS0yP:PPPRPkD9%APS0z=0ABS0{202OqS0|=irPP@P}P=fdRLPLPLPLP6PyEPS0},VjCES0~]2]4]1]3^0J]8]7X:8Q0cP3P\P@Ps1Lxn?{^sR\A:AxBS1015?OS119BA}S12AGDzqS13P}POPPP5D9%AOS14=0ABS15202qSS16=irOS17P@PzP=feR~P~P~P~P6PLEPS18,V}S19CE]2]4]1]3]0]8X<@Q0uP3P\P4AUjRkA:AjBS1:15?q9BAzS1;AGDySS1<PzPqPOPjD9%AqS1==0ABPrPSPN%;qCJP@PyP=ffR\P\P\P\P6P~EPS1>,V9S1?CE]2]4]1]3]0X>4Q10Q12Q13P}POPPPxD9Q15Q17P4AU~NqRMPD11\~S1@PyP3C6P@PLP=fgRe?sWN%8eS1APePeP6P\C2S1B5UeS1CDR]6XB4PD11~LS1DPzPMC6PAP?Q00P?P?P3P3PXn10110500021000000XJAS1E15?WS1F15?LS1GPAQ1F%H\S1HQ1GPAQ1HQ1FP:CSPxE@E^A0?WLP?P~fhRM#HS1I15?3S1J50APDfiS1KP2PMPYPXP\FTA0@e=RlfjS1L?UZXQ1LQ1L#8S1M+0BQ1LQ1LP6Q1KC2RwCW]2]4X;?%HeS1N15?~S1O50APDPMP\PePXPWP~FTPDQ1KPePMPYPXP\P}PjP3M:zQ1K#8S1P,NYQ1KQ1KP6PMC2S1Q,3XA0@\='4'4Q02Q1M,NZS1R13YwS1S/4lP@PMP=fkS1T?s[YQ1TQ1T#8S1UQ1TQ1TP6Q1LC2S1V3UDRP3flS1W#8,NhfmS1XQ1XP6Q1WC2S1Y,3hQ1L=0@='4Q02fnS1ZQ1ZP6Q1XC2S1[,3aS1\Q1T=0@=P@Q1WP=foS1]?sfaQ1]Q1]Q1]Q1]P6Q1ZC2S1^401DRP3fpRlPlP6Q1]C2S1_,3fQ1Z=0@=P;frRw#8S1`PDfsRQ/1wS1aPlAsQ3bH0@ftRK=GDwS1bPQP2PmfqR{D9PrPpP1%;mCJP@PQP=fvRi?s5p%8iS1cPiPiP6fuS1dC2S1e5UiDR]9]2]6XD;PDPwP{Q1]Q1`=UwcDMAGDQ{S1fPw%8QS1gPgPlD9PrPm%8KS1h%;gCJP8Q1dQ1dP6PKC2S1iAGDiKS1jQ1dQ1cP3PQD9A:A2BS1kPrP1fxS1l#8S1m%;uCJP@PiP=fyRd%8dS1n+0BS1o/FvS1pQ1oPdPdP6Q1lC2S1q'1'cCE]9]5]2X=8Q1d=GDQS1oPKQ1d#8S1rQ1iPwD9Q1e=:ABfwS1s#yS1tQ1s/x6S1u;hiS1vQ1s#8S1w#vS1x'wS1y=irsP@P=PDPdQ1lP3Q1pDMPDfzS1pQ1lPdQ1p#8S1zQ1p#yS1{Q1p/x6S1|;hdS1}P2FTP@P1P=f{S1~Q1~'YS20/1xQ20Q1~Q1~P6Q1pC2S1p'FDR]2]6X?@PDQ1lQ1sP=Q1lQ1m;UuDMPDPdQ1sQ1lQ1nQ1qP=FTPrQ1}Q1z#vS1z'w%;xS1q90r3XCrP1Q1}#;S1nQ1}Q1zQ1{Q1|PdPKH0?40>E7Q1n=ir|Q01PrQ1p#;Rd%;}S1p90r2Pof~S01Q01'YS1n/FzQ1nQ01#yS1nQ01/x6S1zf}S1}3hS1|CW[P3Q1q90rdf|S1{Q1{P6Q1~C2#;%;jS1~50rPrP8Q00P8P8P3P3Q1}$0=Rd$0b&0adQ1n+0_&0^dQ05Q1n+00S1nQ1nQ05Q1z+00+0]S1z40;&0\d&0[d&0Zd&0Yd&0XdL0WQ1}+0VRd$0U&0=d&0AdQ1nQ1z40;Q1nQ1z+0T&0Sd60R?40Q&0Pd&0Od&0Nd&0Md&0LdK0Jn10110500021010001XFrQ1}Q1}P6Q1{C2S1{#;Q1pP3E^Q1{/3}Q1|/3zP3p+01@S1|Q1|P6Q01C2/3yP8p+01ARdPdP6Q1|C2S01Pop+01BS1pQ1p'YS1z/F3S1nQ1zQ1pQ1pP6PdC2S1zCWX:8P8Q01PDQ1pPdP=Q1nDMp+01CS1nQ1nP6Q1pC2S1p#;=ir2p+01DS05Q05Q05Q05P6Q1nEPS05Q055ao]9]6XP8PDPdQ1|P=Q01:01ddDMQ1z#;Rd=0rdPoQ1nQ1nQ1p401Rd/Vd1e@=1e4dH0KW9W6PLP2PCP9L0IPLP3E7b7W3P3O1b3W0P3O1W0n2002105000000101Q1~90r3PoQ1}Q1}'YRd/F}PdQ1{CW[XCrQ1qO1P3Q1~,erO1b0b9W2W6Q1dP<P9P1GbW9W5W2PpP:P2PHP3M9uW9W2W6PgP9PGPEPFM9uWMWHP2P3O2n2001000000121000000W0WKP2P3O2n2001000000121000000bIW2W4PXP3P9P:GbbEW6P}P<PsFKW9W5W2W4W1PuP3E7b1W8PHP3Etb1W7PkP3D`b1W3P^P3D_b3W0P3O1b0P3O1b0W5P1P2P3PCP<P9P:P5O8W8W7W5W2W4W1W3W0XG@XP8X=8XD;X;?X@8XA7PVPTPEP>PCP<P9P:P5P1P2P3O<A:A:BS0cQ06PDPCP9P<P:P5P1FTQ0cPrP9P<&0D8RdCJQ0=11ZY'IS0uA0@=XS17%<XS1~11FGS1q11ah'IS1{Q0<Q0811`aP3CnS0813FaS1}Q0>Q0@Q0BP2CmS0B1=]fS0@1=IcS1pP31=HbS1nPg13_gS1zA0@=bS01%<bA:AnBS1|Q0:15?nS0550AS1mPDP9PRPPPnPkP^FTS20Q1|PrPRPPPdCJP@P|P=1j}}P}P}P6PjC2'g,cvCES21]2]4]1]3]0]8]7[X:713HbS22P3Q1zPmA0@=gS23%<gS24Q0e9BA|S25PDPxPPP:AoRnkS26DDS27Q0gQ0_=0rdP@PxP=1jzzPzPzP6P}C2'g,c|S0_CE]2]4]1]3^0J]8]7X:8Q01P3Q23P@P=%<mS23A:AvBS28Q0w9BAxS29PDPjPOPxAoPRnS2:DDS2;Q0{Q0|=0rdS0|A0@<=S2<Q0]'4]2]4]1]3]0]8X<@Q24P3Q23A:A|BS23Q0vQ1150AS11PDP}PqPjAoOPRS0vDDS0]Q15Q16=0rdQ0}9ao9]2]4]1]3]0X>4Q28Q29Q2;Q0{Q0|P@P=PD11LyS15P3PjC6Q18#<,4oS16]6X?@PD11yzS2=P=PxC6PDQ1DP=P3C6Q1>#<,4o]6XB4PDQ15P=Q04C6Q16PAP?Q1EQ1F15?yS1EPAQ1F%H~S1>Q1EPAQ1>Q1FP9CSP|E@E^A0?WyP?PLQ1NQ1J50APDPMP2PeAoYXWS1FDDPt]2]4X;?Q1HQ1G50APDPeP~P\AoXWUS1GDDPDPMP\PePYPXPWPjPxP3M:z%8MS2>,NYS2?PMPMP6PeC2S2@,3XA0@W='4S2A'4Q02Q1P,NZQ1Q,3YA0@X=S1Q'4PtP3Q1U,NhQ1WQ1WP6Q1TC2,3hS1TQ0i'4Q02Q1Y,3aA0@h=S1YPtP3Q1^,3fQ0FP;%8{S1WAGDwlS1PP{P3PgPbD9PrPmP2PdCJPt]9]2XD;Q1]9GD{S2BPlQ1WPbPcD9PrPgQ1`PdCJP8%yQS1`1xQ6S1W;hwS2CQ1bPQQ1hP3PmD9Q1kPrP1Q1cPdCJPt]9]5]2X=8Q1fPwQ1gQ2CPgD9PKPKP6PQC2S1g=:ABPrQ1iQ1rPdCJP@P=PDQ1sQ1dPiQ1wQ1vP3FTPt]2XG@Q1jQ1dQ1cQ1eP=D9PrQ1yA0r3dXCrP2Q1v#;S1yQ1vQ1xQ1tQ1uPiP{H0?40>E7Q1y=0rdPrQ1lQ1lP6Q1sC2#;Q00P8Q0OP3Q0PPtn10110500021000000XFrQ0RPdP3E7Pt1dt3S0Pb0b9W2PsP9P1K0HW9W5W2PmP5P2PHP3M9uW9W2PgP9PEP0GbWMWHP2P3O2n2001000000121000000W0WKP2P3O2n2001000000121000000bIW2W4PXP3P<P9GbbE'dW6PjPCP3I03W6PjP>PmFKW9W5W2W4W1PpP3C|b1W8PmP3E7b1W7P^P3D`b1W3P_P3D_b3W0P3O1b0P3O1b0W5P1P2P3PCP<P9P:P5O8W8W7W5W2W4W1W3W0XG@X=8XD;X;?X@8XA7PTPEP>PCP<P9P:P5P1P2P3O;Q0VQ0XQ0YPCP9P:P5D9S0YQ0U15?5S0650AAOA<BQ0ZP@PC%?>>09<=PZClAXFEZQ0[Q0qQ0aQ0DQ0hQ0pP3Q0mPpQ0jP@PI%?HS0m>09]=PmClS0hAX1_mQ0gQ0bQ0`Q267fOQ0d15?kS2650A%}PS0d=0ABQ0W]2]4]1]3]0]8]7[X:7Q0tP3Q0jPsP@PH%?_S0j>09I=PpClRdAX|^pS0gQ0xQ0yQ2:7f:Q0zQ0550A%}OS0z=0ABQ0~]2]4]1]3^0J]8]7X:8Q0hP3PdP@%?^,\H=C_=AXxksRdQ10Q12Q13Q0v7f}S0vQ14Q0e50AS14AOAqBS13Q2<Q19'4]2]4]1]3]0]8X<@Q0gP3PdP41FjnQ1:Q1;Q1<PzPqPOPPD9Q1=Q0w50AAOASBP@%?NS1=,\q=CS=S0wP=Q1?CE]2]4]1]3]0X>4Q10Q12Q0vQ14Q13P@%?SS1:,\O=Cq=S1;PDQ1@P3PzC6P@%?U,\S=CN=RdP=11eUQ1CDRRr]6X?@PDQ1DQ1;P}C6P41F\NS1;PDPeP\PdP3DMP@%?W,\N=CU=P=11MWQ2>Q2@5UMDR]6XB4PDQ1@Q0wQ1;C6PAP?Q00P?P?P3P3PYn10110500021000000XJA15?XRdQ1OPAPdQ1NQ1OPAQ1NPdP9CSPjE@E^A0?X~P?P\Q1KQ1J5BAPDQ1LP2Q1KPZPYPXFTPt]2]4X;?PAQ1IP?P\H08PDQ1KPePMQ1FDDPDQ1LPMQ1KPZPYPXPzP}P3M:zQ1RQ1SQ1Q'4'4Q02Q1U,N[Q1V,3ZA0@Y='4PtP3Q1X#8,NaQ1\Q1Y'4Q02Q1^,3`A0@a=S1^PtP3P{P{P6PlC2S1\,3cA0@c=P8Q2CPDPKPQ%?3S1X,\b=Cg=1FK3DMQ1oPKPsP2PmD9Q09Q0N50AAOA5BPt]9]5]2]6X=8PDQ1aQ2C#?,\c=Cb=Q2C,1QH0@Q1bPQPpQ1gPgD9Q1i15?gRK5:AQ1e=OABPAQ1v#A15?sRM90A3XCAP2%AiRdQ1tQ1u<0FiE7Q0S90AdPAQ1s#A15?uRd90A3XCAP3PBPQE7A0ABMPAPBQ0QQ0RPdP3E7PtQ0Pb0b5b5W9W5W2W6PgP2PGPEP]P0N:0mWOWHP2P3O2n2001000000121000000W0WNP2P3O2n2001000000121000000bIW2W4PYP3P<P9GbbE,drW6PzPCP3FKW6PzP>PsFKW9W5W2W4W1PuP3E7b1W8PsP3E7b1W7PkP3D`b1W3P^P3D_b3W0P3O1b0P3O1b0W5P1P2P3PCP<P9P:P5O8W8W7W5W2W4W1W3W0XX?XG@X=8XD;X;?X@8XA7PVPTPEP>PCP<P9P:P5P1P2P3O<Q0VQ0XQ0YQ069OA9Q0uP@P<%?C>079=PXClAXG>XQ1{Q08Q1}Q0BQ0@Q1pP3Q1nPgQ1zP@P]%?I>070=PbClRrAX1HbQ1|Q1mQ2015?^Rd9OAnP@PvP=1jjjPjPjP6PxC2'g,cuCE]4]1]3]0]7]5[X:7Q22P3Q1zPmP@PIQ0m>07]=PgClRjAXu_gRnQ25Q27Q269OARQ21]4]1]3^0J]7]5X:8P3PjP@Q0j,]I=CH=AXv^mRjQ28Q29Q2;Q0dQ0550ARMP@P9P=Q0_CE]4]1]3]0]7X<@P3PjP41F|kQ23Q11Q0]Q0zQ0e50AP@%?q,]P=CO=RjP=Q0^,V:CE]4]1]3]0X>4Q28Q29Q2;P@%?O,]R=CP=RQPDQ2=P3PxC6P@Q1:,]O=Cq=ROP=11LSQ0}DRRi]6X?@PDPzP}PQP|DMP41FyqRQPDQ15POP3C6P@Q1=,]q=CS=P=11~NQ18DR]6XB4PDQ2=PjPQC6PAP?Q00P?P?P3P3PWn10110500021000000XJA15?URQ15?zRjPAPQ%HLROPjPAPOPQP:CSPvE@E^A0?UzP?PyQ1HQ1J50APDPeP2P\Q1GDDPt]2]4X;?Q1>Q1E50APDP\PLP~PWPUPNFTPDPeP~P\PXPWPUPxP|P3M:zQ1A,NXQ1B,3WA0@U='4'4Q02Q2?Q2APtP3Q1M,N[Q1V,3[Q0f'4Q02Q1TQ0iPtP3Q1[,3`Q0AP8Q1_PDP{PlQ1X,]f=Cc=1F{3DMQ1PP{PmP2PbD915?bR[9OA1Pt]8]2]6X=8PDPlQ1]Q1_#?,]`=Cf=Q1_,FlDMQ2BPlPgQ1\PcD9PwPwP6P{C2Q0s5OAPA%AwA0A3BXCAQ1ZQ2C#AR{Q1`Q1W<0FwEtA0A{BPAQ1g#}Q0N90A3XCAP2PBQ1g00l3E7A0ABKPAPBQ0QQ0RQ0NP3E7PtQ0Pb0b8bSW8W2W6PcP2PGPEP0M9uWOWHP2P3O2n2001000000121000000W0WNP2P3O2n2001000000121000000bIW2W4PWP3P9P:GbbE,diW6PxP<P3FKW6PxPCPgFKX8MW2W4W1PpP3E7b1X7nPmP3E7b1X5rP^P3D`b1W3P_P3D_b3W0P3O1b0P3O1b0W2P1P2P3P<P9P:P5O7W7W5W2W4W1W3W0X\?XG@X=8XD;X;?X@8XA7PTPEP>PCP<P9P:P5P1P2P3O;Q1k15?29BA5PDP:P1P5&0k;R;DD119:Q0L'IA0@=k%<kQ0\Q0T'IQ0<Q0711SqP3Cn13>qQ0>Q0=Q0;P2Cm1=TN1=VUP31=GWPX13FXRXA0@=WRUQ0kA:AIBPAQ0:P?PIH08PDP9PHP_P;DDQ1YQ0l'4]1]3]0]5]2[X:713GWP3PXPYQ17Q1~PAQ0nP?PHH08PDPfP_P:P;DDQ1^Q0o7ah]1]3^0J]5]2X:8P3Q17P@P=%<YRJA:AaBRH15?_9BAfR_PDPcP^PfP;DDRfQ0HQ0C'4]1]3]0]5X<@Q1~P3PJA:A`BQ0E=0AdPDPbPkPcP;DDQ0G9ao5]1]3]0X>4P@P=PD11gbRcP3P`C6Q0I]6X?@PDQ0rP=PaC6PDQ0KP=P3C6Q0J#<,4o]6XB4PDPcP=Q04C6Q0IPAP?Q00P?P?P3P3PPn10110500021000000XJAQ0eP[PAQ0e%HmRcP[PAPcQ0eP5CSPhE@E^A0?RbP?PgQ0MQ1J50APDPuP2PsP;DDPt]7]4X;?ABApKPDPsPmPpP;DDPDPuPpPsP`PaP3K0jW7W4PPP3P:P5GbbE'dW6P`P9P3I03W6P`P<PWFKX7fX4_X1HPZP3C|b1W5PYP3E7b1X2UP0P3D`b1W3PFP3D_b3W0P3O1b0P3O1b0W4P1P2P3P9P:P5O6W5W2W4W1W3W0X;?X@8XA7P9P:P5P1P2P3O6n10410810110300000087110;10:10<1020000000005110;10:0000000005110;10:000000000<110;10:10>106102107104000000000000000;110;10:10>106102104000000000000000<110;10:10>106102104109000000000000000;110;10:10>10610210410=0000000000006110;10:10>000000000Q03Q1q,I1A0@1V1V1VP@PFP=1jIIPIPIP6P]C2'g,cGCE[[[X>4X<@WWQ0=PCP<O3P3Q03Q0?'e1e@>1e4CO3b0W6WQWUWVWTWRXB4W?W]XY8XZ7o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.

Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
    (fs : Fs.Fs) : post :=
  fun tr o => tr = map (WriteEv (Z_to_bv 64 1)) rest ++ wevents bufs ++ [ExitEv code fs]
              /\ exits_with code tr o.

Lemma twm_exec_mut :
  (forall ms model bufs code, twm ms model bufs code ->
     bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
  /\ (forall ms model rest bufs code, twm_pend ms model rest bufs code ->
     buf_modeled rest -> bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
  /\ (forall ms model rest bufs code, twm_tail ms model rest bufs code ->
     buf_modeled rest -> bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "p'0h01oi001oh12trh21Hh33Hssh45modelh52msh63Hbmh74bufsh84codeh93Hfdh:2Hhh;5Hlazyh<3evsh=1lh>1nh?2IHh@2sthA4HsvchB1ehC3HbrhD3HeqhE2HxhF1mhG4resthH3HnbhI3HtehJ2x8hK1AhL3HnohM2HphN5HstephO1PhP1ahQ2c'hR3ms'i013ms'hS2H0hT4HabshU5HargshV2HbhW3HbshX3Hc'hY5HconthZ4Hfd'h[2Hgh\3Hh'h]3Hn1h^3Hn2h_2Hrh`2Htha3Hx8hb2_Hhc3_H0hd3_H1he1bhf3bufhg1fhh5lemmai021ci031si041xp%0p&0p&1p;1p;2p;3p;4p;6p;=p;:p;5p;8p;;p;Ap;7g00?Zj1VTg00@?k10RTg00@]k10CTg00Gjj1fTg054@j1KTg00mbR0k10KTg00Nhk10iTg010hj2qTg00GJj1ZTg01P<j1DTg04`Fj22Tg01OIj13Tg055;j3Fj5HTg0563j37Tg056jR1j1JTg057dj4Nj6MTg048Ak104Tg00oFj2aTg00L<j30k102Tg058ak10DTg00]=j1ETg00A@j1rTg00`Pj2}Tg04]nj3{Tg059[j2yTg00K6j2RTg04a;j49Tg033bk609Tg02Kbk30[Tg02P;k10YTg02Q2k30WTg004kj68k70ITg05:Uk30UTg05;Uk20QTg05<Xm=19Tg003Tj6iTg05=Lm:17Tg00Y1k100Tg034`k20MTg01M\j1uTg05>Jk20xTg05?Mk10qTg05@Cj1ITg05A9k10NTg05B3j36Tg04knk10kTg021nj4bTg05Bnk20jTg05CLk50hTg05DCj8tTg00RWk10ETg05EBk50gTg00TKj3ATg05F7j3UTg00[5R2j2BTg05FXk40fTg05G<k10eTg04lej2`Tg05H2k40BTg05HPj6_Tg00A^k20ATg02V0k20dTg02i5j1|Tg04Dhj2pTg04Eaj1\Tg02=>j2@Tg04O^j4zTg01eUj3eTg04m[k30cTg05ILk40bTg05JPk60aTg04gJk10?Tg04iYk40`Tg04j]k30>Tg05KIm=0=Tg05L=m;0_Tg05M=k30^Tg017aR3k10<Tg019^j2lTg01;Pj2jTg04d=k10]Tg04eEk10\Tg04aok30:Tg05N<k408Tg05O@k80FTg05P4m:0GTg04TUk30ZTg04UZj2[Tg04V4j31Tg04WKj3OTg04RAk507Tg03g3S00j2xTg002Dj2]Tg012ek406Tg04VSj2gTg05Q3k20VTg05Qnk10TTg05RRm=0STg03hZk405Tg05SLmA0PTg05TJj1hTg04bkj1<Tg004Nk614Tg05UDk313Tg00<_j3Sk10}Tg05VDk10OTg05W5k311Tg01kHk401Tg05Wgk110Tg05XVk40JTg01mOk30LTg007fk30|Tg006Tk20wj4sTg00=Yk20vTg00;3k40uTg05YMk30rTg023Ck40sTg05ZEk10tTg05[4k60pTg05[_m;0yTg05\Zk20zTg05]Fm:0oTg05^3k70nTg05^nk30{Tg05_Ok50mTg05_kk70~Tg05`bm;0lTg01Q2k112Tg02Vnk10HTg04Wij2oTf2R4f1R5#uf0R630p=>&125=046p=Gg00lWR7,@6p=;g02e6R81`45;A6p=:%36,`5p=mAA8569S84p=P1256#<p>0;AS856p=4f3R9?045/B6p>031]56,[4p=CP4P8P5P6Csp=5AS8569094p=?%I5=S86p=dP9P8P4P5Cs=S86p=~&0H5=e46p=W%\5/26p>0@1@56$0Hp=ng01AKR:g01NSR;P5P6H06,j4p=T1g56,o4#\p>0X1g45,o9#\/26p=cg052TR<g053JR=1g45,o9#\/26#<30p=Yf5R>f4R?P9P8P4P5Cs30/B6p==1B56,B4p=^P4P8P5P6Cs90?9p=k1g45,o9#\/26#<p=LA0<=6p>181[45/B6p=wP>P?P9%34P5P6EMp=X%<5=0<6p=Qf6R@P>P?P9AS845P6EMp=vA0<56p>16%<690<5p>15g00ijRA#V#V#VRB$0R$0CRC#fRD#fRE%VB#V#VRB$0RRF$0CRG%K5&0KGRH&0iGRI7>91qGGRJ#fRK%ZJRJ7G?%D>p,4segsRLf7RM/2@%3@9F>?37[[[[W8W7X4;X5:%J4%K4S01A>H>IAGK@J%DMf9RNf8RO'2PMP@P>%3ORPCN57L[[[[[X8GX7EXGDX4;X5:RQPQ&0441aG650H&0D5%ZDRQ#KA>H?IS02AGK>JS03%D@S04PL12OMS05%;O%EARR#E#E#E#E#E#E#r,}FRS5{FRT%3MRU5FQ%Z8RV9:TURW1yTMRX,2ORY%f8RZ/RWR[1mTX=PVV=0ZWR\eP\PZ%;NR\={FSR]1y]OR^'m=PVVPLf:R_/2NR`P6%;_Ra={FSRS/yN-0;_C9X=ZPLPNPOPMg00ea,}F1qGD#ZS06PJPJg02d>#ZS07g01M=Rb,qGRc#ZRdJ09P^PVP]P9P@B0[LNMRePGPM&0D6XeGP>&0YeB0WLNME880UO1aG]Re,RHA>H^ee20Q]ON=19A:]PVRPP6Eib2PLP`P5P6C9PLf;RfP_PNP4P5P>POPMP6N:17W3X@<X<ZPLPYg05a\RgPQPS%3NRhA:ShV/45P6DHW0X1ZPH1aGTRSA0H6IRi$00X0HA0HSIRjPHPeP0PGp-0R0P6g00jOS08g035?Rkn10110000021000000XBHg01I7S09PIP6EiPk20Mk6bSW2&00je%uXRj20xTMRlE8&0qY=>HI$00ePZPWPZP6%IQRm/4P12N^$0N96]6H03X=ZA0ZWW&0NYRY96TWR]P[A0HjS&0kX=0HIPHPSA0H6eX0H1RHSPjPlE820QTMCbP]eCbPZPW14mWRmP]H03e14WVR]20j8WE8PZP]PmA6T]YH03ePQPTPUP]PYDHeI0hGtW9W;W:W6WaWAXJGX4;X5:&0E7R7?CC4S0:P>P?P9P4P5I0gS0;%J?%K?RYA>HMIR]AGKOJRT%DNRQ12f_RmPNPOPM%3_RWCN57L[[[[[S0<AAD>?#Kg05bVp4p710RlP0\6Rj%f4RSP2AA9569U94P9P4O1AU?95'B[ReP4P5O1AU946'BAA?459U?9RX[P?P9O1AU>?4'B\XP9P4P5P6H0fP5n2001000000120000000W=XP5WOWKPe^=S^P5^Oj^KlP6PDP1P_PNP?O5%J_AUD1N'BP2%JfAUD1_f>Rlf=Rj'2f<RS=ADf%3jS0=7F_57LP6%JjAUD1jPLfAR1f@Re'2RXf?R[PlPj%3eR^CNAAD[l?Fj^P_P5P6POPMP@O5P1PeP[fBRP#3RnP5P6EMP2PZP4%rA,}FRA$0eRo=5CP%I1RpfCRq,me;PVC?A6e45AADqPP1fDRr#3S0>P9P4DHP6PZP?A5Cor%IqRsfERt#3S0?,`P;PVRuC?A6q>?fFRv=ADtfGRw#3S0@=:rVRx'dRy90Z@A6r@>PZA5CovRz%ItR{/4x'4R|PZP6AADwv#IfHR}#3S0A=:tVR~C?X1ZPZP|PCPoPw1dv~C~=0Z6X=Z1RZ|14z{/4xP8PzP{PxH0BEiA0Z|yeP@P5E8P6CbWEWDP5P6O2n2001000000121000000W2X0gX1ZE_WWWVP5P6O2n2001000000121000000b6b2X9QX;TX:]W6W?WMWHX8GX7EXfDX4;X5:&04?R|1aG450Hg00f?Ry20AF9%VR#E#V#E#E#E#r3020d@>%|M,pM#\%;MRR1@M7;W@P?P9Cz%K>Rx1@N7=W\O=>HI1@_7=WaN=GKJ%;f1@f7;W_#D%|S,pS%;S1@S7;WfRa+0@%3a9FNO57L[[[[%K@S0BA>HNIS0CAGK_JS0D%DfS0EPH%uSPiX0HP4%;jRi1nj7Ra;eS#uR\B0ciaSE8A0H\I%;lR\1nl7RaPjP5H0bAe\aj#DPL12[l%3lRa9FSfPV%|[R\,p[%;[Ri1n[7R{;elRz+0@R~PLP[PlPjP\PzPzPVP?P_PLP[PjPlPNPOJ0aP5&0?\PiP{PlP9H0`R{60>zN=0=PLPXP5P6C9PPP1PeP4P5PMP@PjPSPfP6N;0_W3X@<X<ZPLP~%3z9FSfPlPjP^14V5S0FP6DHX0gX1ZP@P>P5P{P6O4PlPj%;11@17S0G;We#3P5P6DHP2PZP4%I[S0H%;P1@P7;W1#3=:lVC?A6l45PeP[Pn14V9P4DHP6PZP?Pp%;r1@r7;Wq#3=:eVC?A61>?14V@Rp=0ZuR{A6Pp>PZ%;vRp1nv7Rz;et#3R~,`P=PsV%IrRs1mqv;PVRi90Z6X1Zg005fR\Q0?1`q6=PsV=0ZiXg\1RZuP~B0^pztE8P@P5E8P{eP6CbWEWDP5P6O2n2001000000120000000W2X0gX1ZE_GtbZb\W9W;W:W6W?WIWUWLWAX8GX7EXJGX4;X5:A0H|I&0<:R|1lL>1j:?30P>P?P9P4CzA>H@IS0?AGKMJS0I%DOS0JAFOMhS0K97L`[[[\YPL12S_AFNOWRWPVPmPLPSP_PfP_P4PM1q:;R{$0<RzP3P:Pz1lLSRpAT{6f&0]{R~&0\{Run1011040003101010000AT{SfR\90z6XFzP|1j:fP3P:PzP6AT{6SP~Pun1011040003101010000=0z\XF|AT{f_,RzPpP@E8B0:LS_PLPSP_P5H08E8L0FPL12lSS0LP5P6C9PLP[PjPlP4P5P?P_PNP6N:0GW3X@<X<ZPLPmPWPfP_%3SRWQ0FP6DHX0gX1ZP?P9P4P5P6O4PfP_PWP5P6DHP6PSPfQ0=14V4S0MP5DHeW2X0gX1ZE_GtX9QX;TX:]X6xW?WIWNWAX8GX7EX4;XR:X5:&04>S0N1aG950H20AF?%rB50yA0GRA&0KD1@O7&0E7,@O60ZO1aD>30AC7C@1[76RRAC5CNA1C4_:0XjCPSAOC4_PNPOI07[[^>bAC5C_AOC4f#J%KfA>H[IAGKeJ%D1PqPCA1CMePPCcAOCMeP[PlPnCN57L[[[[[[\R^>b%JN%KNA>HjIAGKlJ%D[PLPXPlPjPSP^CNP4PZPL12qPS0OP5P6C9X@<,x<X<Z1]ClRX=1ClRn95CoRAP<PL12P1Ry1]C[=1C[95CoP6C9X@<PGPbQ0GPXH06=Acd1gCnQ06PJPJQ07PdJ09+0VRd,p1#\00;ePLP1PeP[PdPePePAP4PfPLP1P[PePlPXP6P_PNPOP?PM&0TXN=0SP4&0?d>0>e5N=0=H05H05PLPyP6P=C9PLPqPPP1PeP5P=P?P9P4PjPSPfP_P@PNP6NA0PAC6C1PZP4PCPoA1C61RyPrPCPyPqCYE=5^RX>b,xbQ00PbAC6CPRyPZP9PCPoA1C6PRdDkRXPtPCPdPrCLRd$18'B5^RX>bPPP1PeQ0>P912tr#hEMP6AC6CrPZP>PCPoA1C6rRAPwPCPAPvCYE=5^RP21[75S0>1]CtRAPZP@PCPoA1C5tRnP}PCPnPwCYE=5w5PvPtPrQ0APMfIRn/2}#hEMP61[79R71]C}PZPNPCPoA1C?}RcfKRBPCPcfJRcCYE=5w?P21]CnRF,[>PZP_PCPoA1C>nR]fLRTPCP]PBCYE=PcPnP}PTPffMR]/2T#hEXP6ACMCBPZPjPCPoA1COTRQfORmPCPQfNRQCYE=P2PZPlPCPoA1CN]RpDkfPR\PCPpPmCYPQP]PTP\P[fQRp/2\#hEXP6PZPePCPoA1CfmDkfSRiPCA1CS\fRRsCYP<P=P<P0P6PkQ08n0110300021010200XB<Q09fTR0PCA1CjpPiCLP6EiPkPsPpP\P0PqfURk/20S09#hEX00M6b2WTWdP5P6O2n2001000000120000000W2WcP5P6O2n2001000000121000000W2WbP5P6O2n2001000000121000000W2X>bP5P6O2n2001000000121104000bBW3X<Zg051_R=PLQ0OP5%<6S0OC9PLPrPqPPP1P4%<5P>P?P9PlPjPSPfPMP_P6NA0P1Q4d,BX9^RyX>b,xbQ00PbAC6CqPZP?PCPoA1C6qRyPvPCPyPtCL,Q9E=5^RX>bPtPrPqQ0@P@P5P6FvX0gX1Z97L9P61[6APZP@PCPoA1C6tRAP}PCPAPwCL,Q>E=5^RP2Q0>1]CvPZPMPCPoA1C5vRRPnPCPRP}CL,Q@E=5w5PnP}PwPB14_5P6EXX0gX1Z97LMP6PZP_PCPoA1C?nRwPTPCPwPBCL,QNE=9w?FP2AC>CcPZPfPCPoA1C>cRFP]PCPFPTCL,Q_E=P]PTPBPm14l5P6EXX0gX1Z97LfP6ACMCTPZPlPCPoA1CO]RFP\PCPFPmCL,QjE=P2PZP[PCPoA1CNQRQDkPpPCPQP\CL,QlPpP\PmPi14P5P6EXX0gX1Z97L[P6PZP1PCPoA1Cf\DkPZA1CSp95CoRpPLQ09P6%<PR\C9%<qRmfVRQPCA1CliPkCcRF#<Rw+16PQPkP0fXRR#3RAP?P5P6FvX0gX1Z97Lr[]3X<ZPL120iPp%<1C9PkPCA1CjsP0Cc-15\P<P=P<P=P6P6Prn0110300021010200XB<PmPwP6J14A0=qFfWRFPCA1C[0PQCc90=rP=PRPCA1CekRwPFCcRmPLfYR\/2RA1C1QRs95CoQ0OC9P\PRPFf[Rp#3RiA1Cr\95CoP5P6FvX0gX1Z97L5]3XQ=PL12RFA5Cow%<mC9PLP\PCPsPRCcAOC1QPkP0PACNPRPFPQfZRA#3R0A1CqR95CoP5P6FvX0gX1ZP]P1PjPNB131QTPBPcPnP}O8AOCqRPFPQP0P5P6EMP2PZP4AOCr\95CoA:FiV,dRC?A6F45PAP\PRf\RRPCPoA1CtAP9C~P4EXP6PZP?AOCvp95Cof]Rv#3=:\V,dAC?A6A>?PZA1C}vRA95CoR\/4@RFA5Covf_#3=:pV,dRRiC?A6pF>PZAOC}vRF95CoRp/4iRrf^R091CnRQ95CoRq/46A5Co0Rcf`#3=:RV,dvRR'4RB50ZX1ZASCAFRT=0DvPZ&02ZR]&0OZ:11Z]PCPoAOCn0RnPRC~,4qRqPBASCQnRn95CoRQ/4RPZ\ZRB\ZRkPZPBP]PZPZP]P]H01RsH01RmPZPBPsPZPZP]&10ZH0JH0J:0Lkm&0}8PcPQP8\CRQPZ^=D&028Rc:0|C8RmPDPZ&02DRkP]H0120wC820vC8PoPQPmPCP8Pc&0O8H0u:0rQm:0LQmPoH0sP0PnPDPk&0tDPnP0P6J0pN;0yPRPR20zZRN:0oK0nWhB0{C}vPZ14\pRvPZPqP6PRC?X=ZPZ14\rRrA0Zq6X=Z1RZr14viP8P\PpPiH0BEiA5CoTPCP8PoPAPFI0mE8O2P@P5E8P6CbWEWDP5P6O2n2001000000121000000W2X0gX1ZE_W3PtP6P9K0IW2P6O1b2WXW3PPP6PeK0IW2P5P6O2n2001000000121000000W2W^P5P6O2n2001000000121000000W2X]7P5P6O2n2001000000121000000W2X>bP5P6O2n2001000000121104000bBW3WQX<ZK0~W9W;W:W6WCW?WYWHW_W[WLWAX8GX7EXGDXJGX4;X5:P9P4P5P6CzQ01Q02Q03Q04Q05AF@>U57L[[[[%ZCRU#JQ0?Q0IQ0JPLP`Q0KPUPOPMPhCNP>P9P4P5P6O4P_PN%3fRhP5P6DHP2PZP4%IfA:_WVC?A6_45PUPSPfQ0=P9P4EMP6PZP?%IjA:SaVC?A6j>?PZP@A5CoUQ0H1`l^;PVC?R^A6l@>P5P^eP6CbWEWDP5P6O2n2001000000120000000W2X0gX1ZE_W9W;W:X6YWCW?WIX8GX7EX4;X5:Q0:Q0;Q0<%J>RYA>HOIR^AGKNJRJ%D_RKP>P?P9P4P5P6O5RUW9W;W:X6xWCW?WMWHX8GX7EXGDX4;X5:Q0N=0HI1lL@1j:>50|P@P>P?P9P4I0712SfP_PNPOPhCN57L\K\J\^\x\Y%J@Q0BQ0CQ0DQ0EPLQ0LPfP_PNPWCNRWPV12jSRVPLPlPSPjPSP4POPzP3P:Pz1lLlROAT{6jP~Pun1011040003101010000AT{ljRN90z6XFzP|1j:jP3P:PzP6AT{6lP~Pun1011040003101010000=0zNXF|AT{jS,RzPOPME8B0:LlSPLPlPSP5H08E8L0FPL12elP5P6C9PLP1P[PeP4P5P?PfP_P6N:0GW3X@<X<ZPLPVPWPjPSPfPaQ0FP6EMX0gX1ZPUPjPSPfPaP5P6EMP6PlPjPSP[Q0MP5EXeW2X0gX1ZE_GtW9W;W:W6WCW?W`WNWAX8GX7EXGDX4;XR:X5:N;0lo"). Qed.

Lemma twm_exec : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "h04bufsh14codeh25modelh32msh44resth53Htep;1p;4p;3p;2p;5p;8g00?Zj10Tg00@?j1;Tg00@]j16Tg00Gjj12Tg04O^j4GTg054@j18Tg00mbj1DTg01M\j17Tg00Nhj1>Tg00L<j31Tg010hj2=Tg01Q2j13Tg00GJj1<Tg01P<j1:Tg04`Fj29Tg01OIj15Tg055;j3FTg0563j34Tg05EBj5ETg056jj1CTg057dj4BTg04RAj5ATg00[5j2@Tg030Dj8?Tg01AKR0g01NSR1g00ij#0#0#0R2#;#6#2R3#2R4%02#0#0#;#6R2f3R5f2R6f1R7f0R8CGR9%86%D2R:f4R;#7%>2R<311=22R=#2R>f5R?#3%<=R=31f6R@#:p,4segsRAf8RBf7RC'9%5C9F@?34[[[[\9^12^04^21^30P;P5P6P7P8DE%C5%85%7@=1:<%3C=1>=%:Bf:f9R='9PBPCP@%5=CB54A[[[[[RA[^12^04^43^21^30P;P5P6P7P8DAPA[^12^04^43^21^30'@g05c3P;P5P6P7P8G?W5W1W0W2W3o"). Qed.

Lemma twm_star_admits : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  exists c, star segs (mkCfg ms model) (wevents bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "p'0h01ci001ch11Hh22Hmh32Hxh41oi011oh52trh63Heqh72c'h83Hbmh93Hfdh:2Hhh;5Hlazyh<5Hstarh=3Hteh>2_Hh?1ah@4bufshA4codehB1ehC5modelhD2mshE1xi021xp;1p;4p;3p;2p;9p;5p;7p;8g00?Zj1<Tg00@?j1ITg00@]j1CTg00Gjj1?Tg04O^j4WTg054@j1UTg00mbj1QTg01M\j1>Tg00Nhj1OTg00L<j39Tg010hj2LTg01Q2j1JTg00GJj1BTg01P<j1VTg04`Fj20Tg01OIj15Tg055;j3Tj53Tg05col9STg05dgj4RTg05eej41Tg00[5R0j28Tg03g3R1j2=Tg05f]j42Tg05A9j16Tg05B3j3:Tg00K6j2NTg05gPj7MTg05?Mj1ATg00Y1j1@Tg03hZj4KTg004kj8PTg05TJj1;Tg05@Cj1GTg04lej2ETg00TKj3FTg00<_j3HTg02e6R2f3R3#Gf2R4f1R5'Ef0R65F23Hp=Dg051_R7/=6p=7%G3%55,E4=F265H2p=4g01AKg01NSg00ij#<#<#<R8#I#C#?#?%<8#<#<#I#CR8P3P4P5P6CW%U4%Q8R9f4R:#>%O8R;391L88R8#?f5R<#J%B839f6R8#Vp,4segsR=f8R>f7R?'0%5?9T8<P>P?P8P<P:P3P4P5P6M9SCR%?2R@g05a\RAP=f:RBf9RC'0P5P6C1P>P?%5CP5P6D3'8X4A'=X5@'=P1P@P=f;RD/0BREP5P6C1PCP>%5BRFP5P6D3'8X4A,=AX5@P=PEPCP>PF%B2R2CDP6C2X07#7P6P=f=RFf<RE'0P5P6C1PDPB%5EP5P6D3'8X4A,=AP1PAP=f>R1/0FP4P6C1PEPD%5FP4P6D3'8X4AP=f?R4/01PFPEP1P2C4P6C2X07#7P6PAP=fARGf@RH'0P<P6C1P4P1%5HP<P6D3'8P=fCRIfBRJ'0RKPGPH%5JRLP2CDP6C2X07#7[P6P=10JGRMP8%66RNC1PHP4%5GROP8PND3'8P0P=PKP?%65RNC1PGPHPLP?PND3P=fERNfDRP'0RQPIPJPPP2C4P6C2X07#7RJP6P=PQPC%63C1PPPI%5NRRPB%6:D3P0PNPPfFRNP2C499@DRS%6<9:PDP=fIRTfHRU'0fGRVPNPUP2C4RNP6C2X07#7RWP6A9@FNRN%6>9:V1P@PTPUfJRUP2C4RFP=fLRXfKRY'0P6%6BRZC1%6DR[9:U5P=fOR\fNR]'0fMR^PXP]P2C4P6C2X07#7]3]2X5@P=10YUPF%6CC1PUPTPYP2C4=:TZP=10^XRZPYPUPXP2C4RUP[P5PD1NA[FMP=PZPUPDC2%AD#>=99;#@'8P0P=10]^PXPYP^P2C4PEC2%AE#>=99;#@P=fPRE/0\RYP]P^P\P2C4R\P6C2X07#7P6P=PYP\P1C2%A4#>=99;#@P7P=fSfRR;'0fQPEP;P2C4P6C2X07PHP5CKW>W<P5P6O2n2001000000120000000b?W3W2P4P5P<P6GPW3W6P5P6O2n2001000000121000000W1W2P5P6O2n2001000000121000000W1X77P6O1P=PMP8%;6RMC1PHP4POP8PMD3'8P0P=PKP?%;5RKC1PGPHPLP?PKD3PJP6P=PQPC%;3C1PPPIPRPB%;:D3P0PS%;<9:PDPWP6%;>9:V1g035?P=PZPUP6C2X07#7P6n010000000W3X6NP5P6O2n2001000000120000000W1W2P5P6O2n2001000000120000000W1X77P6O1n0110100021110010100XEAP5P6O2n2001000000121102000W1X5@P5P6O2n2001000000121102000bBW9W;W:W8W=WAW@WCWDo"). Qed.

Lemma twm_star_only : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    is_prefix tr (wevents bufs ++ [ExitEv code (m_fs model)]).
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "p'0h01oh11Hh22trh33tr'h43Hbmh53Heqh63Hfdh72Hhh85Hlazyh95Hstarh:3Hteh;2_Hh<3_H0h=4bufsh>1ch?4codeh@1ehA1lhB5modelhC2msi001xp;1p;4p;3p;2p;9p;7p;6p;5g00?Zj17Tg00@?j1BTg00@]j1?Tg00Gjj1;Tg04O^j4STg054@j1NTg00mbj1KTg01M\j1GTg00Nhj1FTg00L<j3<Tg010hj2ETg01Q2j1CTg00GJj1=Tg01P<j1RTg04`Fj2@Tg05f]j4QTg01OIj10Tg055;j3Mj5OTg05col9JTg05hPj7ITg05dgj4HTg05eej43Tg00[5R0j28Tg03g3R1j2:Tg05@Cj15Tg04lej26Tg0070j39Tg05B3j3>Tg009Ij3DTg003Tj6LTg00<_j3ATg00TKj3PTf5R2f4R3f3R4g02e6R5f2R6f1R73Af0R8DOp=2AP578p=4AA578p=1g01AKg01NSg00ij#7#7#7R9#B#?#;#;%79#7#7#B#?R9P4P6P7P8CS%N6%K9%G3%F93<1E99R9#;%C2%=93<f6R9#R%;5R:g051_p,4segsR;f:R<f9R='@P7P8CQP;P7g05a\R>f;R?P<f<R@#0RAP3P7P8E2W0X3:P;1@?<f8RB%0<5M=P6P7P?P<P=PBf7RCP9P2P3P4M9JP8FICHP;P4P7P8C3f=RDP@f>RE#0P9P7P8E2X0>X3:P7P8O2'8X0>,:>X2:,::P1P:P;P3P7P8C3P@P?%0DP2P7P8E2'8X0>,:>X2:%5?16<A%=5RA'4'19953P8P;P9P7P8C3PEPDf?R9#0PCP7P8E2'8X0>,:>P1P>P;PCP6P8C3P9PEf@R1#0RFPBP6P8E2'8X0>%5916EF/4A'1995BP8P;P=P3P8C3fARFP1fBR6#0P<P3P8E2'8P0P;P<P2P7C3P6PFfCR<#0P?P2P7E2%5<fDRG#0,66/4A'1995@P8P;P@PCP4C3fER4PGfFRC#0PEPBP3E2P0119=R9%5CfGR=#0,64/4A'15<:A>492%5=fHR9#0,6C/4A'19951P811F?%59fIRF#0,6=/4A'15<:116@=>9BP:11<DA95G8XA:AD5<DfJ#5fK#0,6F/4A'1P7ELW<W5P7P8O2n2001000000120000000W1W;P7P8O2n2001000000120000000W1X0>P7P8O2n2001000000120100000W1X3:P7P8O2n2001000000121100000b@W9W>W2W6W8W7W4W:W?W=WBWCo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_mmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      right. exists a. auto.
  -
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
      discriminate
    end.
  -
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite Hh in H6; discriminate
      | rewrite mmap_model_halted, Hh in H6; discriminate ]
    end.
  -
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | assert (Hhn : m_halted
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
          by (rewrite mmap_model_halted; exact Hh);
        rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
    end.
  -
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma twm_exec_not_errors : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ OmniRun.exec segs (mkCfg ms model) OmniRun.errors.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "p'0h01oh12trh21Hh33Hbmh44Herrh53Hexh63Hfdh72Hhh85Hlazyh92Hmh:3Hteh;2Hxh<2_Hh=4bufsh>4codeh?1eh@5modelhA2mshB1ti001xp;1p;4p;3p;2p;9p;7p;5g00?Zj12Tg00@?j1@Tg00@]j1?Tg00Gjj17Tg04O^j4OTg054@j1LTg00mbj1JTg01M\j1ITg00Nhj1ETg00L<j34Tg010hj2CTg01Q2j1ATg00GJj1>Tg01P<j1NTg04`Fj20Tg0563j3MTg05dgj4KTg05eej41Tg05nJR0j25Tg00[5R1j23Tg03g3R2j26Tg01OIj1;Tg055;j3HTg05col9GTg05oAj7FTg05@Cj18Tg04lej29Tg00TKj3=Tg00<_j3:Tg05B3j3<Tg060<j5DTg00Y1j1BTg01AKg01NSg00ij#2#2#2R3#@#?#7#7%23#2#2#@#?R3f3R4f2R5f1R6f0R7CO%L5%J3f4R8#I%E3341C33R3#7f5R9#A%>334f6R3#Np,4segsR:f8R;f7R<'0;M0R=P:f9R>/0;P0P7CKg02e6R0#7R?g05a\R@P:f;RAf:RB'0P6P7C11567RC'3X0@'6X1?'6P2P?P:f<RD/0AP6P7C1/3CX0@,6@X1?g035?RAP7P:f>REf=RF'0P6P7C1/3CX0@,6@P2P@P:f?R2/0EP5P7C11557'3X0@PAP7P:fAR5f@RC'0P8P7C11587'3P1P:fBRG/05P9P6C11596PAP7P:fDRHfCRI'0P<P4C115;8P:fFR:fER;'0%;;R89HHIP:P;PHPIPGP5PCP2PEM9GP>P9P6FF%8H19I8%>0R85=05:094?>A<I>9'3P1%8;%;:,9H==085:094?BA<HB3PAP7fGRA#8fHRH#;,9:==085:094?DA<AF>PHPEPBP7P9DDW;W<P6P7O2n2001000000120000000bBW4W9P6P7O2n2001000000120000000W2X0@P6P7O2n2001000000120100000W2X1?P6P7O2n2001000000120100000b?W5%B=eW6W8W7W3W:W>W=W@WAo"). Qed.

Lemma twm_exec_code_unique : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall code', OmniRun.exec segs (mkCfg ms model) (exits_with code') -> code' = code.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["WithFP1"; "WithSegs"] "p'0h01Hh12Hxh21oi001oh32_Hh43Hteh53Hx'h62trh72Hmh82c'h94codeh:1eh;3Hbmh<3Hexh=3Hfdh>2Hhh?5Hlazyh@4bufshA5code'hB5modelhC2mshD1xi011xi021bi031cp;1p;4p;3p;2p;9p;5p;7p;6p;8g00?Zj1;Tg00@?j1HTg00@]j1ETg00Gjj1?Tg04O^j4@Tg054@j1VTg00mbR0j1RTg01M\j17Tg00Nhj1MTg00L<j30Tg010hj2LTg01Q2j1JTg00GJj1FTg01P<j1WTg04`Fj22Tg05B3j1Gj3<Tg0563j3UTg01OIj11Tg055;j3Tj54Tg05col9QTg05dgj4NTg05eej43Tg00[5R1j28Tg03g3R2j2=Tg05A9j19Tg05@Cj1DTg04lej2ATg00TKj3CTg00<_j3BTg05oAj7KTg05?Mj15Tg00oFj26Tg04knj1>Tg003Tj6OTg004Nj6PTg00K6j2ITg004kj8STg05TJj1:Tg01AKg01NSg00ij#;#;#;R3#H#E#?#?%;3#;#;#H#ER3f3R4f2R5f1R6f0R7C@%V5%R3R8f4R9#7%M3R:301L33R;#?f5R<#J%F;30f6R;#Wp,4segsR=f9R>f8R?'2%G73UP=f:R@/2>f7RA%1>5T?P@P>P?PAP;P<P9P4P5M9QCNg02e6RB#?RCg05a\RDP=f<REf;RF'2P6P7C3P@P>%1FP6P7D4'8X2D'=X6C'=P2PCP=f=RG/2EP6P7C3PFP@%1EP6P7D4'8X2D,=DX6CA034>P7P=f?RHf>RI'2P6P7C3PGPE%1IP6P7D4'8X2D,=DP2PDP=f@R2/2HP5P7C3PIPG%1HP5P7D4'8X2DA03AGP7PDP=fCRJfBRK'2P<P7C3fARLP2%1KP<P7D4'8A03FL[P7g051_RMP=fDRN/2JROP;%97RPC3PKPL%1JRQP;PPD4'8P1P=fERP/2NRRPA%96RSC3PJPK%1NRTPAPSD4A03GJRSP7P=fGRUfFRV'2RWP>%94C3PVPP%1URXP@%99D4P1%DUfHRY#1,AV%FBRZ5CB5BB90CFR[%9<9<VFA03LUR\P7fIR]#DfJR^#1,AY=CBZ5BB90CGRB%9?9<]IP=fMRZfLRY'2%GNPJPH%9>R_P<FKA<NH_P1%5@R_#7fKRN,63RH508%>_=08:A03VYP6%5E#7163ZRZ508%5G#>=08:P1%5IRG#7163]508%>G=08:fPRG903^P9%52#7=08H%5L#>=08:P8%5K#7fNR:,63RH9087X28P6fSR2,63R^P<EOA08^ZP8P3P0P3P3P7P7fUR0n10110000021010200X:8fTR^,63PHP7EPA03^:fO9030P3PGfZfYR^fXR:P7C@%5U#71636508A0325]1]4X93P^P:fWPGC@%5V#7fQ,63508fR,I3W1W4fVP7P0P?GSW0P7O1b0b5W3W5P6P7O2n2001000000121000000W3W1P6P7O2n2001000000121000000b5W1W3P6P7O2n2001000000121000000W0W7P6P7O2n2001000000121000000W0W8P7O1P=POP;%:7ROC3PKPLPQP;POD4'8P1P=PRPA%:6RRC3PJPKPTPAPRD4PSP7P=PWP>%:4C3PVPPPXP@%:9D4P1P[%:<9<VFP\P7%:?9<]Ig035?A03PNP7n010000000W1X3BP6P7O2n2001000000120000000W0W7P6P7O2n2001000000120000000W0X8MP7O1n0110000021110310103XDDP6P7O2n2001000000121101000W0X6CP6P7O2n2001000000121101000b:W<XA3W=W?W>W;W4W9W@WBWCo"). Qed.

End WithSegs.
End WithFP1.
