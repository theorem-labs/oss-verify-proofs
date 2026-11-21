(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (46 recorded proofs replaced by written proofs (v_srli_div, step_sb_any, step_sb_at and 43 more); munmap_model, grant_ok, munmap_check_modeled and 10 more restated for the revision's model; mmap_ok_inv re-proved; adds iv_subtract_outside, maps_subtract_exact, grant_ok_intro and 4 more; imports). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamSim AllocSim.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
(* check_syscall is used at :480 and :482 and lives in Checks/ExecutableSpecs.v.
   This file required Checks.Sys.Mm.Mmap and Checks.Placement but never
   ExecutableSpecs, and Require Import is not transitive for names, so the one
   it gets through Lib/Cfg does not reach this scope.  NOT a #38 cause: that
   definition is at Checks/ExecutableSpecs.v:61 at BOTH f1006fe8 and 75d69e00,
   identical file and line.  23 files in this tree carry this import already. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
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
  intros x sh Hsh. unfold v_srli.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (u64_range x) as Hx.
  assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hle : (bv_unsigned x / 2 ^ sh <= bv_unsigned x)%Z)
    by (apply Z.div_le_upper_bound; nia).
  assert (H0 : (0 <= bv_unsigned x / 2 ^ sh)%Z) by (apply Z.div_pos; lia).
  apply Z.mod_small. lia.
Qed.

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
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  rewrite <- N_to_le_bytes_1_small.
  apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.

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
  intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
  rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv, Hb. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_snoc : forall (bs : list byte) (m : word -> option byte)
                           (a : word) (b : byte),
  wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word (length bs)) [b].
Proof.
  induction bs as [|x bs IH]; intros m a b.
  - cbn [app wbytes length]. rewrite word_add_0. reflexivity.
  - cbn [app wbytes length].
    rewrite IH. f_equal.
    rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
  zmem m a n.

Lemma zfill_out : forall a n m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  zfill a n m x = m x.
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.

(* [comment removed for export] *)
Lemma rdn_zfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (zfill a n m) x k = rdn segs m x k.
Proof.
  intros segs a n m x k Hnw Hd. exact (rdn_zmem_out segs m a n x k Hnw Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.

Lemma iv_subtract_outside : forall (b s : word) lo hi,
  (0 < bv_unsigned s)%Z -> (lo < hi)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  iv_subtract b s lo hi = [(b, s)].
Proof.
  intros b s lo hi Hs Hlh Hd. unfold iv_subtract. cbv zeta.
  destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.max_l by lia.
    replace (bv_unsigned b + bv_unsigned s - bv_unsigned b)%Z
      with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_exact : forall l (a n : word),
  (0 < bv_unsigned n)%Z ->
  (forall b s, In (b, s) l -> (0 < bv_unsigned s)%Z) ->
  (forall b s, In (b, s) l -> b = a -> s = n) ->
  (forall b s, In (b, s) l -> b <> a ->
     (bv_unsigned b + bv_unsigned s <= bv_unsigned a
      \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b)%Z) ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  = map_remove l a.
Proof.
  induction l as [|[b s] r IH]; intros a n Hn Hpos Hu Hd; [reflexivity|].
  assert (IHr : maps_subtract r (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
                = map_remove r a).
  { apply IH; [exact Hn
              | intros b' s' H; apply (Hpos b' s'); right; exact H
              | intros b' s' H; apply (Hu b' s'); right; exact H
              | intros b' s' H; apply (Hd b' s'); right; exact H]. }
  cbn [maps_subtract]. rewrite IHr.
  unfold map_remove. cbn [List.filter fst]. fold (map_remove r a).
  destruct (bv_eqb b a) eqn:E; cbn [negb].
  - apply bv_eqb_eq in E. subst b.
    rewrite (Hu a s (or_introl eq_refl) eq_refl).
    unfold iv_subtract. cbv zeta.
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a))).
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a + bv_unsigned n))).
    reflexivity.
  - assert (Hne : b <> a) by (intros ->; rewrite bv_eqb_refl in E; discriminate).
    rewrite (iv_subtract_outside b s); [reflexivity | | lia |].
    + exact (Hpos b s (or_introl eq_refl)).
    + exact (Hd b s (or_introl eq_refl) Hne).
Qed.

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
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

Lemma grant_ok_intro : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  grant_ok hint m a n = true.
Proof.
  intros hint m a n Hn Hnal Hpl Hbud.
  destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal Hpl)
    as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok. rewrite Hpl, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    (proj2 (Z.leb_le _ _) Htop), (proj2 (Z.leb_le _ _) Hbud).
  reflexivity.
Qed.

Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma munmap_model_fs : forall addr n m, m_fs (munmap_model addr n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma munmap_model_fd1chan : forall addr n m, fd1chan m -> fd1chan (munmap_model addr n m).
Proof. intros addr n m H. exact H. Qed.
Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
  intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
    vm_forget_range, with_vm_backing, with_vmmaps.
  cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_model_fs : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_model_fd1chan : forall a n m, fd1chan m -> fd1chan (mmap_model a n m).
Proof. intros a n m H. exact H. Qed.
Lemma mmap_model_lazy : forall a n m,
  m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma grant_ok_unpack : forall hint m a n,
  grant_ok hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[[_ H1] H2] H3] H4] H5].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  apply Z.leb_le in H5.
  auto 7.
Qed.

Lemma grant_ok_place : forall hint m a n,
  grant_ok hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

Lemma region_free_cons : forall (b s : word) r (lo n : word),
  region_free ((b, s) :: r) lo n = true ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo)%Z
  /\ region_free r lo n = true.
Proof.
  intros b s r lo n H. cbn [region_free] in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  split; [|exact H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1.
  apply andb_false_iff in H1.
  destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.

(* [comment removed for export] *)
Lemma source_alloc_limit_val : source_alloc_limit = 0x400000000%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma target_alloc_limit_val : target_alloc_limit = 0x8000000000%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_arg3_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. reflexivity. Qed.

Lemma in_arg4_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. reflexivity. Qed.

Lemma in_arg5_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. reflexivity. Qed.

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
  intros ms (H1 & H2 & H3 & H4 & H5).
  split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
  split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

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
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma munmap_check_modeled : forall ms model eff,
  munmap_args_ok ms model ->
  check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in munmap_errnos r
        then match us with
             | [] => CheckOk model []
             | _ => CheckReject
             end
        else if w_is0 r
                && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms model eff (Hal & Hlen & Hnw & Hhas).
  unfold check_munmap.
  rewrite (proj2 (Z.eqb_eq _ _) Hal).
  unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
  cbn [negb orb]. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
  unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.

Lemma munmap_ok : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model Hno Ha.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  unfold munmap_eff, w_is0.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by reflexivity.
  cbv beta iota. rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma munmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  In e munmap_errnos ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

Lemma ENOMEM_in_munmap_errnos : In ENOMEM munmap_errnos.
Proof. left. reflexivity. Qed.

Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
     eff = mkEffect (errno_ret e) [] [] /\ model' = model)
   \/ (eff = munmap_eff ms /\
       model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply check_munmap_complete_ok in Hspec.
  rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct zs as [|? ?]|]; try discriminate.
  destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
  destruct (errno_ret_in munmap_errnos r) eqn:He.
  - destruct us as [|? ?]; [|discriminate].
    inversion Hspec; clear Hspec; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    split; [reflexivity|]. left. exists e. auto.
  - destruct (w_is0 r
              && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
      eqn:HC; [|discriminate].
    inversion Hspec; clear Hspec; subst.
    apply andb_true_iff in HC as [Hr Hus].
    unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
    apply listNN_eqb_eq in Hus; subst us.
    split; [reflexivity|]. right. unfold munmap_eff. auto.
Qed.

Lemma munmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false in Hspec
    by reflexivity.
  cbv beta iota in Hspec.
  destruct (w_is0 (Z_to_bv 64 0)
            && listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
    discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma munmap_node_cfg : forall segs ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  (forall i : unit, sstep_cfg segs ACFG (mkCfg ms model) ((fun _ => []) i)
       (SNext ((fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                                (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) i)))
  /\ (forall e st, sstep_cfg segs ACFG (mkCfg ms model) e st ->
        exists i : unit, e = (fun _ => []) i
          /\ st = SNext ((fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) i)).
Proof.
  intros segs ms model x8 Hh Hlazy Hsvc Hno Hargs.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 215%Z) by exact Hno.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model
                             = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model).
  { intros eff. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. }
  pose proof (fun eff => eq_trans (Hchk eff) (munmap_check_modeled ms model eff Hargs)) as Hck0.
  clear Hchk.
  assert (Hne : errno_ret_in munmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  assert (HR : forall r, refusal_b (sys_input segs ms x8) model r = errno_ret_in munmap_errnos r)
    by (intros r; unfold refusal_b; rewrite Hno'; reflexivity).
  assert (Hoff : injected_family_off ACFG (sys_input segs ms x8) = true)
    by (unfold injected_family_off; rewrite Hno'; reflexivity).
  apply (node_chk_grant_cfg segs ms model x8 unit
           (fun _ => munmap_eff ms)
           (fun _ => munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
           (fun _ => []) tt Hh Hsvc Hoff).
  - intros []. rewrite Hck0. unfold munmap_eff. cbv beta iota. rewrite Hne. unfold w_is0. rewrite bv_eqb_refl.
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros []. rewrite HR. exact Hne.
  - intros [r ws zs us cs ci] m' evs Hck Hr. rewrite HR in Hr. cbn [eff_ret] in Hr. rewrite Hck0 in Hck.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    cbv beta iota in Hck. rewrite Hr in Hck. cbv beta iota in Hck.
    destruct (w_is0 r) eqn:E0; [|discriminate].
    destruct (listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]) eqn:Hl; [|discriminate].
    apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck.
    injection Hck as <- <-.
    unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
    exists tt. unfold munmap_eff. repeat split; reflexivity.
  - intros [r ws zs us cs ci] m' evs Hck Hr. rewrite HR in Hr. cbn [eff_ret] in Hr. rewrite Hck0 in Hck.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    cbv beta iota in Hck. rewrite Hr in Hck. cbv beta iota in Hck.
    destruct us; [|discriminate]. injection Hck as <- _. exact Hh.
  - intros [r ws zs us cs ci] Hck. rewrite Hck0 in Hck.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (errno_ret_in munmap_errnos r); [destruct us; discriminate|].
    destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
  - intros []. cbv beta. rewrite munmap_model_halted. exact Hh.
  - intros []; reflexivity.
Qed.

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
Proof. left. reflexivity. Qed.

Lemma mmap_errno_range : forall e,
  In e mmap_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range mmap_errnos e eq_refl HIn). Qed.

(* [comment removed for export] *)
Lemma mmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms -> In e mmap_errnos ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn Hdecl.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
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
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
(mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
intros segs ms x8 model a Hno Ha Hdecl Hg.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite Hdecl.
rewrite (grant_not_errno (ms_gpr ms 0) model a
(page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
[ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
| exact Hg ].
unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
destruct Hg as [[[[[Hp H1] H2] H3] H4] H5].
rewrite Hflags.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
rewrite Hp, H5.
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
intros segs ms x8 model eff model' evs Hno Ha Hspec.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply check_mmap_complete_ok in Hspec.
unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
destruct (place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
(page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Hdecl; [discriminate|].
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
- destruct (linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
(ms_gpr ms 0) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) r
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
+ apply andb_true_iff in Hcond as [Hpl Hbud].
apply (grant_ok_intro _ _ _ _ (proj1 (mmap_grant_len_ok _ Hl))
(proj2 (mmap_grant_len_ok _ Hl)) Hpl).
now apply Z.leb_le.
+ unfold page_round_up. reflexivity.
+ reflexivity.
Qed.

Lemma mmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hdecl Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hdecl in Hspec.
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
  intros regs pc sv mem rom a n.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_writes apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

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
  intros a n m x Hx. unfold unfill.
  destruct Hx as [Hx | Hx].
  - rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
    rewrite andb_false_r. reflexivity.
Qed.

Lemma rdn_unfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (unfill a n m) x k = rdn segs m x k.
Proof.
  intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros y Hy. apply unfill_out. lia.
Qed.

(* [comment removed for export] *)
Lemma adv_munmap : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) []
               = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

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
    (forall e, In e munmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bufs code) ->
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(** The put-style retry loop realizing one buffer: a write-pending state
    offering the remainder [rest]; the environment delivers any nonempty
    prefix, the loop reissues on the rest.  The trace contribution of the
    whole node is exactly the FULL buffer (WallSim's [to_wall] shape,
    inlined here because the continuation is the mutual [twm]). *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
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
  intros ms ms' model bufs code H; induction H; [auto|].
  intro Hw. eapply twm_step; eauto.
Qed.

Lemma msteps_twm_tail : forall ms ms' model rest bufs code,
  msteps segs ms ms' -> twm_tail ms' model rest bufs code ->
  twm_tail ms model rest bufs code.
Proof.
  intros ms ms' model rest bufs code H; induction H; [auto|].
  intro Hw. eapply twmt_step; eauto.
Qed.

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
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n buf))) (v_addi pc 4) mem rom)
       model (skipn n buf) bufs code) ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model (buf :: bufs) code.
Proof.
  intros regs pc mem rom model buf bufs code H17 H10 Hr Hok Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twm_write; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
Lemma twm_tail_write_rec : forall regs pc mem rom model rest bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n rest))) (v_addi pc 4) mem rom)
       model (skipn n rest) bufs code) ->
  twm_tail {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
              ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
              ms_mem := mem; ms_rom := rom |}
    model rest bufs code.
Proof.
  intros regs pc mem rom model rest bufs code H17 H10 Hr Hok Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twmt_more; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
Lemma twm_munmap_rec : forall regs pc mem rom model bufs code (a nlen : word),
  bv_unsigned (getr regs 17) = 215%Z ->
  reg_get regs 10 = a ->
  reg_get regs 11 = nlen ->
  (bv_unsigned a mod page_size = 0)%Z ->
  nlen <> Z_to_bv 64 0 ->
  (bv_unsigned a + page_round_up_Z (bv_unsigned nlen) <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (page_round_up nlen) = true ->
  (forall e, In e munmap_errnos ->
     twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom)
         model bufs code) ->
  twm (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
            (unfill a (page_round_up nlen) mem) rom)
      (munmap_model a (page_round_up nlen) model) bufs code ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model bufs code.
Proof.
  intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hfail Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  eapply twm_munmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn. auto.
  - intros e He. rewrite adv_set. exact (Hfail e He).
  - unfold munmap_eff, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn.
    rewrite adv_munmap. exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma twm_exit_coden : forall regs pc mem rom model (c : word),
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model [] c.
Proof.
  intros regs pc mem rom model c H17 H10 Hc.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                                 ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                                 ms_mem := mem; ms_rom := rom |} 0)
                      (Z_to_bv 64 255) = c).
  { unfold ms_gpr. cbn [ms_regs]. rewrite E10, H10.
    apply land_255_small. exact Hc. }
  rewrite <- Hg.
  eapply twm_exit.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
Qed.

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
  ((exists e, In e munmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
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
        rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + right.
      match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      reflexivity.
  - (* sstep_syscall_materialization_fault: no lazy range can fault *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat ];
      discriminate
    end.
  - (* sstep_exit : munmap leaves haltedness unchanged *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite Hh in H6
      | rewrite munmap_model_halted, Hh in H6 ];
      discriminate
    end.
  - (* sstep_killed : munmap leaves it unkilled for the same reason *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
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
  apply (twm_mutind
    (fun ms model bufs code =>
       bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
    (fun ms model rest bufs code =>
       buf_modeled rest -> bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
    (fun ms model rest bufs code =>
       buf_modeled rest -> bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))).
  - (* twm_exit *)
    intros ms model x8 Hsvc Hx8 Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold twm_post. cbn beta. rewrite app_nil_r. cbn [wevents app]. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* twm_write: the wall node contributes the full buffer *)
    intros ms model buf bufs code Hnb Hp IH Hbm Hh Hlazy Hfd.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq; [exact (IH Hb Hbs Hh Hlazy Hfd) |].
    intros tr o (Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents]. rewrite <- app_assoc. reflexivity.
  - (* twm_munmap: the refusal and the cut *)
    intros ms model x8 bufs code Hsvc Hno Hargs Hfail IHfail Hcut IH Hbm Hh Hlazy Hfd.
    assert (Hh' : m_halted
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = None)
      by (rewrite munmap_model_halted; exact Hh).
    assert (Hfd' : fd1chan
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
      by (apply munmap_model_fd1chan; exact Hfd).
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8 (munmap_eff ms)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      * exact Hh.
      * exact Hsvc.
      * apply munmap_ok; [exact Hno | exact Hargs].
      * exact Hh'.
      * apply materialize_model_accesses_no_lazy.
        exact (munmap_model_no_lazy _ _ _ Hlazy).
    + intros evs Hss.
      destruct (sstep_munmap_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hargs Hss)
        as (_ & [(e & _ & Habs) | Habs]); discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_munmap_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hargs Hss)
        as (-> & [(e & He & Hc) | Hc]); injection Hc as ->.
      * eapply exec_conseq; [exact (IHfail e He Hbm Hh Hlazy Hfd) |].
        intros tr o (Heq & Hx). split; [| exact Hx].
        cbn [app]. exact Heq.
      * eapply exec_conseq;
          [exact (IH Hbm Hh' (munmap_model_no_lazy _ _ _ Hlazy) Hfd') |].
        intros tr o (Heq & Hx). split; [| exact Hx].
        cbn [app]. rewrite Heq, munmap_model_fs. reflexivity.
  - (* twm_step *)
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
  - (* twmp_write: every delivered length is a successor *)
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbr Hbm Hh Hlazy Hfd.
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv (Z_to_bv 64 1)) (firstn (length rest) rest))).
      * exact Hh.
      * exact Hsvc.
      * apply write1_ok_n; try assumption. apply Nat.le_refl.
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + intros evs Hss.
      destruct (sstep_write_inv segs ms model x8 rest evs SError
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbr Hnb Hss) as (n & _ & _ & _ & Habs).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_write_inv segs ms model x8 rest evs (SNext c')
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbr Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) |].
      intros tr o (Heq & Hx). split; [| exact Hx].
      rewrite Heq. rewrite <- (firstn_skipn n rest) at 3.
      rewrite map_app, <- !app_assoc. reflexivity.
  - (* twmt_done *)
    intros ms model bufs code Hte IH Hbr Hbm Hh Hlazy Hfd.
    eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |].
    intros tr o (Heq & Hx). split; [| exact Hx]. cbn [map app]. exact Heq.
  - (* twmt_more *)
    intros ms model rest bufs code Hnb Hp IH Hbr Hbm Hh Hlazy Hfd.
    exact (IH Hbr Hbm Hh Hlazy Hfd).
  - (* twmt_step *)
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hbr Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbr Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.

Lemma twm_exec : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)).
Proof. intros ms model bufs code Hte. exact (proj1 twm_exec_mut ms model bufs code Hte). Qed.

Lemma twm_star_admits : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  exists c, star segs (mkCfg ms model) (wevents bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd.
  destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

Lemma twm_star_only : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    is_prefix tr (wevents bufs ++ [ExitEv code (m_fs model)]).
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar))
    as (tr' & o & _ & Heq & _).
  rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_mmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hdecl Hss.
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
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs Hdecl H3)
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
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  destruct (exec_sound _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) _ _ Hm)
    as (_ & Hx).
  exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.

Lemma twm_exec_code_unique : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall code', OmniRun.exec segs (mkCfg ms model) (exits_with code') -> code' = code.
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd code' Hex.
  destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as ->. reflexivity.
Qed.

End WithSegs.
End WithFP1.
