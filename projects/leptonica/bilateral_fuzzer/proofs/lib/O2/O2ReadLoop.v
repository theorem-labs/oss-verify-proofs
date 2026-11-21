(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (proofs and definitions restated for the model's changed definitions; recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy; buf_facts and side_frame re-proved by tactics for the allocator's changed live-block bound and the ledger's vDSO reservations). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibKnowXfer LibTail SymCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Room.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2ExitBase O2Startup O2StartupDefs O2StartupFacts O2MainEntry O2LibStdioCall O2OpenFail_defs O2OpenFail_tail2 O2Open_defs O2Open O2Oom_defs O2MemPreds O2Malloc65536 O2DirRead_defs O2MemcpyBase O2Memcpy O2ReadLoop_defs O2FuzzIface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2ReadLoop () := "C47Corelib7Program6Basics4flipC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7add_modC59OSSVerify5KrLib6Common8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3mulC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9u_mul_eqmC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_modC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8u_lit64aC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib6Common:AllocIface7round16C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnK47Corelib4Init5Logic3and01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem2FsCfile_read_unguardedC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib2O2:O2MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init5Peano2ltC46Stdlib5Lists4List8app_nth1K47Corelib4Init5Logic2or01C59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC35stdpp7tactics<f_equal_helpC47Corelib4Init5Peano2geC46Stdlib5Lists4List8app_nth2C59OSSVerify5KrLib6Common8MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_geK46Stdlib9micromega=RingMicromega3Op204C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_nthC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib6Common9CliDriver6SymRun;regs_ok_setC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib6Common8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec:getr_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib2O2:O2ReadLoop6modelkC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c59OSSVerify5KrLib2O2:O2ReadLoop6model2C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C59OSSVerify5KrLib2O26O2Open4fds0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop4sideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop5al_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop5vm_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc655366env_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC69OSSVerify5KrLib6Common8Mallocng9AllocBase<ai_live_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop:round16_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib2O2=O2Malloc65536;live_big_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop6in_winC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop9buf_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open9above_sp0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2O2=O2Malloc65536<ownedA_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase9grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase8ai_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_winC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S?mem_denot_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop:side_frameC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall8log_wd_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall@mem_denot_out_wdC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_wdlC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib2O2:O2ReadLoop7DATA_RSC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC4ELinuxProcessSemantics5Riscv3Sem5alu64C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC69OSSVerify5KrLib6Common9CliDriver<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5aluop00C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX@kwr_store_ok_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_knAC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00c59OSSVerify5KrLib2O2:O2ReadLoop5slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib6Common7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c59OSSVerify5KrLib2O2:O2ReadLoop9at_headerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop7at_fullC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop7at_loopC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver<LibKnowFrame8kn_frameC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop>stage_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AgentLibJread_bytes_map_of_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC56Stdlib6ZArith4Znat5Z2Nat2idc59OSSVerify5KrLib2O2:O2ReadLoop;modelk_pureC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop<fdsk_lookup3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes?andb_true_introC4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsc59OSSVerify5KrLib2O2:O2ReadLoop@length_file_readC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop4fdskC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive;regs_set_a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver<LibKnowFrame=know_ok_frameC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_srRC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes?pair_equal_specc59OSSVerify5KrLib2O2:O2ReadLoop:side_blockC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeC46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib2O2:O2ReadLoop;vals_ev_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer2rvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer<regs_ok_xferC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXferDknow_ok_xfer_entailsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC46Stdlib5Lists4List:firstn_allC69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop;fdsk_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb7m_fds_CC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb:with_fds_CC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive:v_addi_pc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesFS;rz_close_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop9slots_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_regsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop:alu_add_wZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAfirstn_min_lengthc59OSSVerify5KrLib2O2:O2ReadLoop@firstn_app_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop?bytes_at_extendC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C46Stdlib5Lists4List2InC59OSSVerify5KrLib2O2:O2ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib9micromega;ZifyClasses9not_morphc59OSSVerify5KrLib2O2:O2ReadLoop7kwr_bufC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop;fdsk_insertC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop8bv_add_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesFS?rz_read_file_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4emapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srAnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_knRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6STOPSLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5kn_MLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5h_rvlC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_srBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_knD0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5f_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs4sr_FC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2O2?O2ReadLoop_defs5d_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs4sr_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs7l_itinAC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rAnC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C59OSSVerify5KrLib2O2?O2ReadLoop_defs6want_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rAtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srAtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2O2?O2ReadLoop_defs7l_itinCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs4l_rCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_srCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rC2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srC2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs4sr_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_knC2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_knRBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs7l_itinBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs4l_rBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_knBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srD0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs7l_itinDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rDnC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rDtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_knDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srDnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srDtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop8md_mul_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop:want_x_valC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib2O2:O2ReadLoop<regs_ok_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2ReadLoop?iter_from_ecallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib2O26O2Open3ENVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open5fds1gC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib2O26O2Open3vm0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open7model1gC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc655366at_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5e_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2DirRead_defs5ok_srC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2DirRead_defs5ok_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc655365ok_srC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc655365ok_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs6e_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs3e_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs4e_srC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs4e_knC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPSL scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSL scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_add_Z : forall a b, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) [] "h01zh12Hah22b1h32b2h41nh51Hh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1ah=1bp;1p;3p;2p;4p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8p1000np4p70g001^R0p4p710R1p8p1002<p4p70P1p8p1002jp4p710P1p8p1003Ep4p70P1p8p1004;p4p710R2g004ZR3p4p710p8P2P1p8g0056j18Tg005Yj37Tg0063j24Tg006]j3WTg007Aj16Tg007fj1RTg008Dj2:Tg008jj3ITg009Oj21Tg009lj22Tg00:Rj1>Tg00;0j2ATg00;Mj23Tg00;mj2@Tg00<Gj2VTg00<oj2?Tg00=Kj2;Tg00=gj3UTg00>Kj1QTg00>kj1PTg00?Kj1OTg00?ij1MTg00@Gj1LTg00A2j2=Tg00AUj3HTg00B8j4FTg00Bcj7GTg00CGj6ETg00Ckj2JTg00DMj2KTg00E9j3DTg00EXj4CTg00FJj4NTP3j6BTg00Fkj19Tg00Gmj2<Tg00H\j3STP0j6TTg00IJR0f1R3f0R137p=0P0f4R2f3R4f2R5P3P1ETp=5g00IhR6%81R7%83R8g00JF%85?73114451443'0R9[14531451'0%84?753[R:%82?745\9AW531P1n2001000000120000000W3W2W4P:^38^27^46P1g00Ja#6R6#6#6#6#6#6R7#RR81:85R:1:83R95I8R21153R;,:8R<148:R=1489R>'1,281145R?,:8,48R@,01X001285RA111=,28/0@X001283RB1284RC/11,28/0@X00128;R@11CA,28/01X0011ABRC%>6R6%>7R7'ARD'3128?RE,01X00135DRF111A/3D/0EX00133DRG134DR4/11/3D/0EX0013;DRE114F/3D/01X00P0PE13?D,01X001@0E11FG/3DP5P3PD1V67g00KFRG/?61;G71?GD[[1;G6RFg00KdREAU673UW11;GD\E^1Fg00L@RF#Q%PF%O0%M0%L0RFg00LlREg00MKR7P7g00MkR?PFPEP7P7P?P01=06=H08g00NK1=0GCFg00O2FGEE1JF?P1P5g00ORR?g00P2RF'@1K15=7?FdAD0G3CCb7b:b;A70DGg00PR[P1b6b8b9CNEBP@%9;D5PB%93D5PA%95D5128C%9CD5148<1<8;D5P>1<83D5P=1<85D51482AS8:9D5O4b5X=0X<0o"). Qed.

Lemma md_mul_Z : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) [] "p'0h01zh11qh22Hah32b1h42b2h51nh61Hh72Hqh82Hrh97__arithh:4__ffh;6__sat0h<6__sat1h=8__varmaph>5__with?1ah@1bhA1ei001xp;1p;3p;2p;4p;7p;6g0056j19Tg005Yj38Tg0063j20Tg006]j3[Tg007Aj17Tg007fj1UTg008Dj22Tg00Poj21Tg00QLj2ETg00:Rj1@Tg00;0j2BTg009Oj25Tg00R^R0j2YTg00S8j1WTg00=Kj2;Tg00<oj2<Tg00JFR1j2VTg00;Mj24Tg00;mj2ATg00<Gj2TTg00=gj3MTg00>Kj1LTg00>kj1KTg00?Kj1ITg00?ij1HTg00@Gj1GTg00A2j2?Tg00AUj3FTg00B8j4JTg00Bcj7DTg00CGj6NTg00Ckj2OTg00DMj2CTg00E9j3PTg00EXj4QTg00T6j4RTg004Zj6>Tg00TWj3STg001^j6:Tg00U<j1=Tg00VMj3ZTg00W0j4XTg00IJR2f1R3f0R438p=3f2R5g00WZP3P4CXp=6g00IhR6%94R7%93R8P1%95?834f3R1/051013'3R9[10531054'3%91?853[R:f4R;#9?815\9A[534P4n2001000000120000000W4W3W5P:^48^37^56P4g00Ja#7R6#7#7#7#7#7R7#UR81285R:1283R95681153,281E:91281R9=68:,081089R<108:'1%@6R6%@7R7'BR:,14R='5'3X12,Y2P0P2128;R0=689,08R91080/1</5='3X1211;1,28,08,39P4f6,28R9f5,28R;568,081089108;'1/5='3f7R=,28R;=689R9#Wg00KFR<1089R9';1<9:'VP2f8R9,28R0=68;,08R>/4:f9R?/19R@,28,08RA,34X02P21080R0108;R;'1115:RB'5144:/3AX02P2149:RC1140111:R1'5/4:/3AX02P214=:RD14?:R?/14/51/4:/3AX02P2119=RA/4:RE11?C/51/4:/34X02P211CDRD/4:RC14@:,34X02R@P2PEP@1A2EPCP9P=P:1T671<<61;<71<<:[[1;<6RCg00KdREAM673UW21;<:\E^2Cg00L@RC#L%KC%I2%H2%G2RCg00LlREg00MKR7P7g00MkR@PCPEP7P7P@P21?26=F28g00NK1?2<CJg00O2FDEN1OC@P4P5g00ORR@g00P2RC'A1C45=8@CdAP2<3CQb:b=b>A82:<g00PR[P4b9b;b<CRE>15DB/4:ASD5:E:128A,08%=AE:P;%==E:P0%=9E:P>P3E:P>AZ>:4E>b8W7X12P3P4O2n2001000000121100000bAO4b6X@2X?2o"). Qed.

Lemma round16_ge : forall n, (n <= round16 n)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) [] "h07__arithh14__ffh28__varmaph35__with44__p1h56__sat1h64__x1h74__x2h84__x3h91Hh:2H0h;6__sat0h<6__sat2h=1np;1p;2p;4p;6p;3p;7p;8g00XFj1<Tg00:Rj1FTg009Oj21Tg007Aj15Tg00>Kj1^Tg00>kj1VTg00?Kj1PTg00?ij1NTg00@Gj1MTg00A2j27Tg00B8j44Tg00CGj6HTg00Ckj2]Tg00;mj2[Tg00DMj2WTg005Yj36Tg00E9j3UTg00EXj4TTg00Xkj3OTg00YLj2;Tg00Poj2=Tg00;Mj23Tg00Yij2CTg00ZZj2ATg00<oj2:Tg00[Kj3LTg00JFj2@Tg00\2j1BTg00\Qj29Tg00]:j3?Tg00]cj2KTg00^Oj3JTg00^oj2DTg00_Mj4ITg00_kj6QTg00`Oj28Tg00a2j7RTg00aVj1STg00b8j3GTg00b[j3\Tg00=Kj2>Tg00c>j1ZTg00Bcj7XTg00d<j8YTf1R0g00LlR1g00MKR2P2g00MkR3f0R4g00O2FXp=2g00KFR5/>4p=0f3R6P1P2P2P3f2R7P0P4GYp=Eg00IJR8g00JaR9#<R:#<#<#FR;,14R<%59R=#5#5#5#FR>g00L@R?#^R@%V?RA%P8RB%N8RC%M8RDP1P2P2P3P8178>REg00NKRF1785RGC4,2DEH1]D3RHP4P7g00ORRIg00P2RJ'[1W47=6IJdAU850CTRJb1b2b3A68>5g00PR[P4b03O1;<>,=>13<>'1968<110;R<1C<>%0<%0>RI116;RK/3>#0[[117;RL/A>%0LRMf4RN/1;RO/;>#0\I[P@PAPBPCP8PGg00d`RGPEC4,2DPHPJb1b2b31:5>P4b0b;b57L>13<>R5#01:5>'@1CL>13O>#0\I\M1AK>%0Kf5RK/1;RM/;>RO#0\I[p-0RIg00eGRL#BR5#B,981985198L5?85?8g00ef'K=J?@PAP81D87P01D86CIPCPDPDP1P2P2P3PDP1P2P2P3PKEQP8188:R:PGPEC4,2DFR%S2R2PDP81889R9178;5G8PF188=9\8ERE=G8:C4,2DP2P8P9g00fRPEC4,2DCECEPHPJb1b2b3X68X78X88W41:7>,@61=>7/16968<1=>6,>7[[^68^78^88^4IP413M>RM#0PMPOPKP6PNO6b0b5b<b:b9%Z4,>4eW=o"). Qed.

Lemma length_file_read : forall data len want,
  (0 <= len < 2 ^ 64)%Z -> (0 <= want < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 len) (Z_to_bv 64 want) = firstn (Z.to_nat want) (skipn (Z.to_nat len) data)
  /\ Z.of_nat (length (file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)))
     = Z.min want (Z.max 0 (Z.of_nat (length data) - len)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) [] "h04__x1h11xh27__arithh31nh42Hah54__ffh64__p1h74__p2h84__p3h96__sat0h:6__sat1h;8__varmaph<5__with=4__x2h>4__x3h?4__x4h@4__x5hA4__x6hB4__x7hC4__x8hD4__x9hE1zhF2H0hG2H1hH2H2hI2H3hJ2H4hK2H5hL2HlhM2HwhN6__sat6hO6__sat7hP4cstrhQ4datahR1lhS3lenhT1mhU4wanthV1yhW2z0hX2z1hY2z2hZ2z3h[2z4h\2z5p%0p&0p;1p;2p;3p;<p;4p;6p;Bp;7p;8g007Aj1LTg007fj1vTg0056k10BTg00>kj1oTg00:Rj1sTg00;0k20GTg00<oj2>Tg00JFj2ETg008Dj2cTg00g9j1kTg00h4j3UTg00hRj3TTg00i1R0j1]Tg005Yj38k10<Tg00iQj2=Tg00inR1j2KTg0063j2fTg000Nj2_Tg00jKR2j1QTg00;mj2HTg00jkj2dTg00kBk20@Tg00kYk103Tg00l7l<zTg00l\j1yTg00mAj2aTg00mcj2hTg00=Kj2STg00<Gk20NTg00=gk30MTg00nEk10LTg00nck20KTg00\2j13Tg00\Qj2tTg00>Kk10HTg00^oj2WTg00?Kk10FTg00_Mj4YTg00?ik10ETg00@Gk10DTg00XFj1^Tg00`Oj2qTg00aVk10ATg00A2j2nTg00oDj3mTg00Ckk20;Tg00DMk20:Tg00E9k309Tg00EXk402Tg00ogk404Tg010Rk305Tg001^j6VTg0113k301Tg011Uk406Tg00AUk307Tg0120j2iTg013@j3}Tg0145j3|Tg0154k20=Tg015Ql<lTg0166lBpTg016\j2uTg0176k30CTg00]:j39Tg00]cj2<Tg00^Oj36Tg00B8j4XTg00Bcj7RTg00a2j7gTg017_j7xTg00_kk60JTg00d<j8wTg00KFR3f0R4'Sp=Mf1R5/_4#Qp=A20=34p=4f2R6g00IJR7?854'Ep=FA8754p=JP7g018CR8P7P7P0f4R0P2f3R9g018bP6P5P4M<lp=jP8P8P8P7P7P7g019OP2P2P2f6R:g019of5R;P0P9P6P5P4MBpp>00P8P8P8P7P7P7g01:VP2P2P2P1g01;6P;P0P9P6P5P4MBpp=~P8P7P7P7P2P2P;P0P9P6P5P4M<lp={1>34p=:A8743p=NA8796,E01S53/E4'up=DA8765,E9/u4p=b1t74p=5B0C754p=CA97549976p=2A9754p=1A9754g00efR2'<p=[A97549976/<2p=;A975499769979/<2p=B1<42p>0Ig00L@R1A97659979/<2;64p=7A6154961696199610p=01<92A61549616561p=`1<621<52=614561p=r1<52=61496169619p=Z1q74p=GP7P5g00d`P4CXp=PP;g00LlR2g00MKR<P<g00MkR=P0P2P<P<P=P9g00O2R>FRP6P2P<P<P=P7P5g00NKR?P4CXP>FRFgp=\P6P2P<P<P=P7P5P?P4CXP>FRp=IP0P2P<P<P=P9P2P<P<P=P7P6g00fRP5CXP>FRP4Fgp=?P6P2P<P<P=P5P4Fxp=OP5P2P<P<P=P4J0Jp=eP7P5P?P4CXp>0?P9P2P<P<P=P6P5P2P<P<P=P4P>FRFgp>0>P9P2P<P<P=P6P5P4Gwp=@P5P2P<P<P=P4P>FRp>08g00JaR>#LR2#LR?#LR@#v$0BRA#oRB%M5%s2RC%L@#L#LRD#sRE+0GRF,>5'ERGPB%vDRD/c6RH#k1cD9RI#k=UA05TARJ%]9RK%]0=UA;5TARL98B41AA41AA;/=0RM#4RN,K9RO3FXRBP7P6%]4RP1cD0,fD#]=UA;5TARQ=8BL1AAQ;FOXE7P7P9AUAP;9TAKRP=8BL1AAP;FOXE7%]6RPAUAK0RL5TARQ=8BQ1_AQS00#Q1_A0RR#QRS/=9#4,K6RT'J1HBQP81_ALS01,dP%Q4RU/JOX38P820@RKRV1dK4#Q/JOX381dPVRO#QRW/JT%46RX%49RY,=S#4RZ'KR[/JTP7P7&0<7R\P4X17R]P\1J54$03XV7X17PWP[P]P]1H7UX18POP[PPPXP]%44X17RXP6P61H76DjPVPZ1=54#4XT7X37PRPS1H7SPKPYP]PXP9P91H79DjK00E~E{PTPT1H7TM<z%yR%MS1a3M%:MPNPMPM%NNDD1AA:/=;#4P71h;41>;41K;4RNP;1S4;?FN4Cb1K:5P7f8RN,a3%:N%4NRMPNPN%NMDDf9RM#4P7f;RS,AA/=4RR,a3%:R%4RRXPRPR%NXDDf<RX,AA/=5#4P71a3S%:S%4SRRPSPS%NRDD%4XP71h461>461K46RRP41S64?FR6Cb1K59P720NCERR%:C%ME%:F[[R]%MCRYg00KdRZB0MCE5UW4RE%MF\Z^4YRYp-0RZ&0L>-0K7RVg00eGR[#3RO#3R8#3RU#3RW#3R\#3R^#3R_#3R`#3Ra#3Rb#3Rc#3Rd#3Re#5Rf'CRg%5aRa,CVRh%5\R\%5URU1t7[R[32Ri'1Rj'[S021CV\Rk1CVURl/1[Rm'1Rn9;faS03%5dRd%5^R^%5WRW;2lRo'[RpPpPgPdPh11\[RqCBRr%58R8=2k[Rs9;faRtPtPr1CVdRr%5cRc%5`R`,CVRuPqCBRvA;d`sRwPwPv1[coRoPoA;d`nRv11uiRx,[rRyPf%5bRbPaPuCBRzPzPoPoPzPzA;^U8R8P8P8P8%3e#5RePcPbPhCBRzPzPpPpPzPzPgPbPj%5_R_,CVRj/1WRz9;b`R{A2`jnR|92faR}$0I%5ORO/1[92\UR\,1_92ghPgPhA2_^\11k[R[92fcS04,1eP8P8P8P8A2db[R[,1f11^iR\92u_R~,1r11_i92ru11d|1[azRzA;raxPyPvA2kWmRm92d`A;a_WRkA;ra~PwPwPrPuP\PgPhP\PtPtPdPbP_A2^UOCBRUPbP_PWPOCBROPfPaPmQ03Q02PePd1CVcRmPaCBRaPaPOPOPUPUP8P8P8P8PkPkPkPkPfPc1CVbRVP`CBRUPUPzPzPfPVP`A2j^lCBRjPj11VqRj,1rP[P8P8P8P8Q0411mqR[,1g11^q92gm11e}P{P{P{P{PpPpPgPdP[PfPcPsP8P8P8P8PdPbPsPrPcPjPoPoPzPzPrPVPiPdPbPnPoPoPkPkP8P8P8P8POPOPpPpPfPcPnPgPmPi&0H1RiC7C7D0D0D0C7C7D0C7C7D0C7C7D0C`3rCZC`CZD0D0D0D0D0C7D0C7C7D0CZC`3rCZC`C7CZC7D0D0D0D0D0D0D0D0%o1R1P7P7P71W7NP0&0F7RmCYP61W7:CYP5P7P71W7MP;PmCYP9f7Rm,W7CYCY&0E7Rg&0D7RnPnPn%^?#GRc%G@R@'PPn1q7>RfPcE\PnPnP@PcAInf@D?5On&0A<R<PnPnPn1n73Rp%G?R?'PPnPcP?E\PnPnP?PpAIncpD?5OnP<PnPnPn%^2#GRc%^>R>#^#GRO5m7R8,PpPnP@P8E\PnPnP8PpAIn@pD?5OnP<PnPn1enSPn%G>R@-0?OH0>PnPnP@PpAInOpD?5OnP<PnPnPn%L>#GR>,P?Pn%G2R2P?E\PnPnP>P?AIn2>D?5OnP<PnPnPnAm7c@Rc,PpPnP>PcE\PnPnPcPpAIn>pD?5OnP<PnPnPnPpP?1enXD?P<PnPnPnPpP@f=R@,enD?P<AInf2C@C@C@C@C@C@C@C@20;n=R=P4P6g00ORR2g00P2R?'H20:46=82?dB09735H02R3b5b;b<X07X=7X>7X?7X@7XA7XB7XC7XD7X6ZX7ZW81>NmP4PN1SmN?F4mCb%:0PMP0P0%NMR?DD1=:NR2#:PMP2P2P?DDPXPMP;P;P?DD1>mMP;Pm1SMm?F;MCb1=MmR?#:f:R2P?P?%N2DD%MMR?f@R>'EfBRc,E?1JNM[[[[[[[[^07^=7^>7^?7^@7^A7^B7^C7^D7^6Z^7Z^8ZP4fCRZ/>F1>cF%:ZP;PmPMP@fD,AAPcPZPSP9P0P:PNP2PXf>P>fAODb2bNbOb\bKb[bJbZbIbYbHbXbGbWbFbPH04Q01B05AK0EVQ00B01APLEVH061fDIPRP]PEPYPiP11W75PgPnPnPnPpPf1n7C>077D,Pf-08nD?RnP<PnC@P=P3b5b;b<X07R3%M41>4F'EPG[^07RFP4P:P0O2b2b9b:,i9EV1fDHPRP]PEPYP3PFP4P;P9O2b2b9b:,i6EVA8BJQ1AAJ;FTeA}0IHA|0IHEVXMGWLXU7XS7WQo"). Qed.

Lemma firstn_app_skipn : forall {A} (k w : nat) (l : list A),
  firstn k l ++ firstn w (skipn k l) = firstn (k + w) l.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) [] "p'0h01li001lh11kh21wh31Ah42IHh51xi011ap;1p;3p;2p;6p;4p200R0g00hRR1p4p710p8P0g001^R2p4p710p8P0g01;YR3p4p710p8P0g004;R4p4p710p8g00>kR5j11TP1j30Tg00h4j35TP3j34Tg01<6j22Tg005Yj33Tg00;mj28Tg00\2j17Tg00>Kj1:TP4j2<TP2j69Tg00^Oj36Tg01<Mj4;Tg018CR2f3R4#1R3f4R1#1R6f2R7f0R8501f1R9A51785015411279=01833]0^22R:X12%17g00eG/29=048,83W0X22P5f5R5f6R3#1R;%71R1=038A531890375431217=03833P8%15R1%:5R<%:393;8X01181<A059<1<59E9%74R4=05<A554<90595451249=05<531ef7R1f8R<#1f9R4#1R;1215=048R=f:R>#1A6>7812<3=0>996>733X0;A649=,8;A0418A54189045544P3P5P8O2E9%71R1A6498R3504A541390455441215=04353;eW0W5P9P8O2n10110000020020101100X06X22X4:X12P8C;W1X30o"). Qed.

(* [comment removed for export] *)
Lemma bytes_at_extend : forall M (a : Z) (pre bs : list byte),
  (0 <= a)%Z -> (a + Z.of_nat (length pre) + Z.of_nat (length bs) < 2 ^ 64)%Z ->
  bytes_at M a pre ->
  bytes_at (wbytes M (Z_to_bv 64 (a + Z.of_nat (length pre))) bs) a (pre ++ bs).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) [] "p'0h04__x1h14__x2h24__x3h34__p1h47__arithh54__ffh68__varmaph75__with84__x4h94cstrh:5cstr0h;6__sat2h<1zh=6__sat1h>2H1h?2Hah@2HihA1xhB2z1hC4__p2hD4__p3hE6__sat3hF4__x5hG4__x6hH1bhI1nhJ2H2hK2H3hL3HgehM3HlthN3HnwhO4HprehP1MhQ6__sat4hR6__sat5hS1ahT2bshU1ihV1mhW1ohX3prehY1si001shZ1yh[2z2h\2z3i011gi021lp%0p&0p;1p;2p;3p;6p;4p;<p;8p;7p;Bg007Aj1UTg007fk109Tg0056k101Tg01<nk10FTg00>kk108Tg009Oj20Tg00:Rj1}Tg00;0k20LTg00<oR0j21Tg01=Pj3~Tg01;Yj3XTg000Nj2]Tg00jKR1j1KTg01<6k206Tg01>Kk30[Tg004Zk605Tg01>jk20WTg01?Mk20VTg01@4R2j2ITg01@PR3k20STg008Dj2DTg01A0k400k30TTg00i1R4j1GTg01Ajj47j3xj2yk10BTg01BFj2<k10CTg005Yj38j1wTg00;mj2?Tg01BhR5k20KTg00l\k10@Tg00mAj2nTg00JFj26Tg00<Gk20cTg00=gk30bTg00\2j1TTg00\Qk207Tg00>Kk10]Tg00^oj2bTg00?Kk10ZTg00?ik10YTg00@Gk10XTg00`Ok204Tg00XFj1sTg00A2k202Tg00aVk10RTg00Ckk20QTg00DMk20PTg00E9k30OTg00EXj4|Tg00ogj4rTg01C@k60NTg001^j6WTg00=Kj2:Tg00AUk30MTg0063j2gTg0120j2qTg016\j2oTg01C]k30JTg01D7k60ETg00iQj25Tg00kBk20DTg01E:k20?Tg01E]k30GTg00l7l<pTg00nEk10>Tg00nck20ITg0176j3^Tg00oDj3{Tg01F:j8iTg01FWR6k20=Tg01Fok60;Tg01GLk60:Tg0154k20UTg015Qm<0fTg00]:j3dTg00]cj2[Tg00^Oj3VTg00_Mk40eTg00_kk60dTg00B8j4QTg00Bcj7RTg00a2j7uTg017_k70aTg00d<j8lTg00b8k30`Tg0166mB0_Tg00KFR7f0R8':p=3f1R9/]8#Kp=4f2R:1198'6p=220U78p=9g00IJR;g018CR<P;P;P4f4R4P1f3R=g018bP:P9P8N<0fp=zP<P;P5P1P0g01HNf5R0P4P=P:P9P8M<pp>0A1178p=>A8;98p=;1:87p=FA8;87p=\1698,o:p=C207;8p=SAd;98p=@Ad;989d;:p=Hg00efR5,[8p>0^g00L@R>?V98p>0\1[95=V>8p=cP;P:P9P8H0ep=BP9g00LlR?g00MKR@P@g00MkRAP8J0dp=a204;8p=ZP;P9g00NKRBP8CQp>03P=P?P@P@PAP:P9P?P@P@PAP8g00O2RCFRFup=`P:P?P@P@PAP;P9PBP8CQPCFRp=YP:P?P@P@PAP9P8Fup=kP:P?P@P@PAP9P8K0ap=_P:P?P@P@PAP;P9g00d`RBP8CQPCFRp=OP;P9g00fRRDP8CQp=LP=P?P@P@PAP:P?P@P@PAP9PCFRP8Fup=AP=P?P@P@PAP:P9P8Glp=Pf6REP?P@P@PAP0P4P=P?P@P@PAP:P9P8GlGlp=MP:P?P@P@PAP;P9PDP8CQPCFRp=hB0`;98p==Ad;:9/[5=V>8p=JP;P9PBP8CQp=NP4P?P@P@PAP=P?P@P@PAP:PCFRP9P8Glp=mP;P4P=P:P9P8EWp=EAd;98/[5p=eAV>989V>:p=fP<P<P<P;P;P;g019OP1P1P1PEg019oP0P4P=P:P9P8NB0_p>0H1[:51[95=V>85V>p=vP<P;P6P1P2g01I0P0P4P=P:P9P8M<pp>0<P;P9g01IRP8CQp=jP9P?P@P@PAP8PCFRp=tg00JaRC#UR?#UR2#UR6#U#U#UR5$09RB$01&096R6$01RD$0FRF[&08DRG%3:RH14D:,0=14D9'0%}?RI%}5R5+0LRJ'1A~04=%38AXD04,4D728P<AXDE0,]D%K8S0092H:XI<P81]DERK1]D0+06RLB0[DE0J05%39RM%KL729P;f7RL,]DRN006K#K%3=?2=8X<;P8%KN%KK'0RO20WNKJ05A2H:Of8RO,4DRN-0V=11=N1I=N+0SP3f9R3,4DRN,141I4Nf<RNf;RKf:RP,4DRQ'0,DBP310K0,DBH00PD%G0AXDP31D67R6C7,<D58FP8110QPFf=RR10NERS,DBRTO1RUPD%GLRVAXDNKP6C7,<DRW98F8XWFS01PFPD%GERXPKP6C7RY,<DRZQ01PDPYPDPVPNP6C7,<D1<D8S0258FXHD1?FZPDPXAXDKPP6C7S03PDPKPPP6PX1]DKRZ-0KX%9ERV%KZRY'1PXPVP8XA;S04%98XA;S05PEPE1?;EDzS06PZPY1?;YS07J0A&0@ZR[%3YR\P[P\1n7OS08%>O%9OR]/;O'6%FO%\]3CS09%93S0:P;20cI5R3%>I%35%>J[[R]%3IR^g00KdR_B0bI59UW?R5%3J\_^?^R^p-0R_g00eGR`#TRa#TRb#TRc#SRd%SbRb%SaRa207;`R`'@Re3H1@b`Rf,@dS0;$0^S0<&0]>Rg+0\'c&08>R>1b;:Rh1b;=Ri&0Z;Rj7B=7B9S0=&0Y;Rk&0X;RlPl1al0Pl204;CRm%s?#ZRn+03C`S0>1alES0?202;7Ro9YlmS0@5kl5_l&0R@R@Pl%Z?R?9OlnP@PlPlPl1Lon1alLCAP@AOlm?RpCPFM20QlARAP8P:g00ORRqg00P2Rr'?Rs20P8:=8qrdB0O;79RrC|Rqb5b6b7X0;X1;X2;X3_XC_WD1;8:,6=S0A%\8S0B7C411=:%34Rt/6L11=4[[[^0;^1;^2;^3_^C_^D_P8fBRu,4DS0CfARv,4DS0D'0,1R%FR%>RS0EPRQ0CP=P4PLPPO9b4b;bEbBb>b:b9CrJ0NEWPUPLPEP[P\P[P\P3P]P5P^PgP>ABh9jPkPlPpP@PlAhlomRU1al45klP@AklUpFMPAP8P:PsPrC|b5b6b7X0;X1;X3_118916M=A2H:=[[^0;^1;^3_P8f@,4DRrf?,4DRs'0,1KS0FPrPKP0POO5b4b=b;b:b9O2EWPR10NYRp,DBRwPPPTH00S0GPPPRPwPTPp108YRx/:JX<;S0HP[P\P[P\P3P]P5P^PgP>ABh9iS0IPkPl1=m?Rh%sCRy#ZRz'=R{202;I>0M;BRI5OlR|P@Ahl{ICPPAPqb5b6b7X0;X1;X2;1089/0:/1J109:R{/0=/:J[^0;^1;^2;P8PsPrPvPRO4b4b=b;b:b9S0J1gBwR}P[P\P[P\P3P]P5P^%TcRc#TS0K#SR~%ScRc?Hde/cg7JfP>1b;4S0L?B:j?B9iS0MPkPlPl1LozP@PlPl%Z2R2/N?P@PlAhlo2S0NQ0?5klP@PlP|P@PlPUP@PlPl1LohAOlhICACPS0OCPS0PCPDmDmPAPqb5b6b7X0;X1;X2;X8;X3_114:%30/6E10=4RU/00/1J100ER|#3?2|J\t[S0Q[[\H^0;^1;^2;^8;^3_P8Q0FPKPsPrPvP=P0POPRf>S0FO:b4b=b;b:b9,qpS0RDEPS14DN,0RRt,DB,gBR|,1810|Y/:8'oX<;Pp10RLRi/181:xi'oX<;11Sp10pQ/:SP[P\P[P\P3P]P5P^PgP>Q0IPkPlPl1N?zP@1=mzRf9OlhDmPAPqb5b6b7X0;X1;X2;119:109=S0I,1{[^0;^1;^2;P8PrPKPvP0O4b4b=b;b:b940JP}Q0RDE1gBTR{P[P\P[P\P3P]P5P^Q0<1ece;fgP>Q0MPkPlPlAhlo?S0<Pl1=z2S0R,N?C`P@Pl1=f2=OlIP@Q0OFMPAPqb5b6b7X0;X1;X2;X8;10:=RI92M9Q0I/04/1J%3U?2UJ\H[[^0;^1;^2;^8;P8PsPrPKPvPOPRQ0FO7b4b=b;b:b9,qSRHDEJ0EEWWMP8O11I0QPFPD15{}#GPPP6C7,<DQ01PSPD158|#GPKP6C7,<D=8FWX<;PpPD15i8#GPKP6C7,<D=8FWX<;PDPD20DXZRWPPP6C7S01PD15it#GPKP6C7,<DQ0258FXHDPDPF&0CDR|P|PD15SpRQ#GRJPPP6C7Q01PF\D/?|PDPDAxDJPAxDWPP6P6PGPD\DR|1yDJ1yDWPPPPP<P|\GR|&0BDRFPFPJPWP|\</?FA8<JW%9QRF15VY#9R|';P<P;%w<P1%w;%K9Q00';A8<9820?9840GXZ<XA<PJPFQ04Q05PQPQ1?;QDzPWP|1598#9XV;XI;PXPVQ06PZPYQ07K0HM<pP[P\P[P\Q08Q09Q0:P;158sR|,n7%>|%9|RW/;|'6%F|%\W3C159r#9P;10uNQ0D,0u'5Ru,n7%>u%9uR7/;u'6%Fu%\73CfCR7/0RQ0C,07'5#9P;P3P]P5P^Q0K#TR7#SRu&0>C-0I;RC=^;c/@`RNA^;Cu?Hc`RWA^;C~R|?Hd`RQA^;CdRF=H~`1@cb,euRJ1@ba,e~R<1@~N,euQ0;A^;CbRC/@`9H~FAHucC%T7#SR7AH7da/cg7JW9JuQ3v5J|9f<<3f7fJ'c3v3JP>Q0L1b;07B:1b;E9Bj=7B9PkPlPlPl%Uy#ZRj,=zQ0R5{;RJ,NoAYlmJCAPlPl1LJoQ0@CA5_lP@PlPlPl%sy#ZRy={;2RJ,NoAYl?JCAPlPl1LJoAYl?oCA5_lP@PlPl1alOPl203yjC`PlPl1LjoAYlyoCA5_lP@PlQ0NP@AYlm?FMFMPAPqb5b6b7X0;X1;X2;X8;XF;XG;X3_10:4Ry/5IRj#>1;8j'6%FjQ0B3C15E4Rj#>1;:j'6%Fj%\:3C1;LE,6O%FE%\L3C%3E1;40[[[[^0;^1;^2;^8;^F;^G;^3_P8%>vPLPvfF,4DfGP0P=P4PEPOPPO;b4bQbRb\bKb[bJbBb>b:b9CrGi1?GPGi1?D6GiGiQ03PDPKPPP6PX20=XZ1IVYPXPVQ06PZPYQ07J0<P[P\P[P\Q08Q09Q0:P;P3P]P5P^1@CeRC1cCg5JdP>Q0=PkPlQ0>PlPl1LnoQ0@CA5_lP@Pl1jn?,tlP@1jm?,tlFMPAPqb5b6b7X0;X1;X2;X3_Q0A%F:Q0B3C1I=:1I:=[[^0;^1;^2;^3_P8Q0EPRQ0CP=P4PLO6b4b;bEbBb>b:b9CrJ0;EWP}P[P\P[P\P3P]P5P^Q0;AJ~eg5JcP>Q0MPkPlQ0<P@Pl1j2?,tlP@PlPlQ0?Pl1=?z,N2C`P@Q0PCPFMPAPqb5b6b7X0;X1;X2;X8;X3_1I4:A2E0UQ0Q[[\M^0;^1;^2;^8;^3_P8%3KRMPKPsPrPvP4P0POPRQ0FO:b4b=b;b:b9,qpRUDEP{PHDEQ0GPPPRPwPTPpQ0HQ0JP}PUDEPp1DBi,gBRi,:8?2ixX<;PS1:t810tY728X<;P[P\P[P\P3P]P5P^PgP>Q0MPkPlPl1jz?P@PlPlQ0?Pl1=?2,NzC`P@PlPl1Lhf1=h29OlfCACPDmPAPqb5b6b7X0;X1;X2;X8;X3_1I:9A20=y1:Iy10I072y[[^0;^1;^2;^8;^3_P8PMPsPKPrPvP0POO7b4b=b;b:b9P{PHDEP}PUDEJ0:EWWLP8O1n200110000021110211101bYb@b@W@XU;14D4,00,DB>0TE=AXD4=7~0eWOWNW?XTGWXXS;WPo"). Qed.

Lemma vals_ev_map : forall E rvl i, (i < length rvl)%nat ->
  vals_ev (map (edenot E) rvl) i = edenot E (nth i rvl (ELit 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) [] "h01Eh12Hih21ih33rvlp;1p;2p;6p;4p;3g00>kj1=Tg000Nj2<Tg01Bhj22Tg007Aj10Tg007fj1;Tg0056j17Tg01J9j13j29Tg01KBj14Tg01LKj65Tg01Lgj46Tg01MCj21Tg01Ajj48Tg005Yj3:Tg01NGg01OOR0#=g018Cf0f1R1,<0'2P0g00Ja#0#0#0#0#0#0#;#7R2f3R3#3R4f2R5g00KF#4R6P1E5P0P2P4P5C6/11P0P1P5P6C8,935:2eW1W2W3W0o"). Qed.

(* [comment removed for export] *)
Lemma regs_ok_same : forall E sr R (rd : reg) e,
  regs_ok E sr R -> rd <> 0%bv -> getr R rd = edenot E e -> regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) [] "p'0h02Hrh11Hh21bh31rh42H0h52b1h62b2h71ni001nh81Eh92HRh:2Hch;3Hrdh<2Hvh=1Rh>1ei011eh?2rdh@1si021shA2srp;1p;2p;3p;4p;:p;6p;8p;5g00>kj1OTg007Aj16Tg00XFj1JTg007fj1@Tg0056j15Tg01PXj2LTg01QDj3ATg01RTj2ITg01S7j3DTg005Yj32Tg01SZj1;Tg01J9j27Tg01T3j21Tg01Tlj4NTg01UHl:MTg01VPj3=Tg01WKj18Tg01XRj3:Tg01Y[j2<Tg0063j20Tg01Zdj2HTg01@PR0j2FTg006]j3ETg00;mj2>Tg01[Dj4GTg001^j6?j8CTg01\Bj5KTg004Zj6BTf3R1f2R2f1R3'1f0R432p=3A=123/14p=9g00IJR5?234p=4g01NGg01OOR6#Og00Ja#6R7#J#@R8%67#6#6#6#6#@#5R7'L%58R9f4R:?A12g00KFR;g01]A1I8;d5D89292#;P7P:P1f6R;/72C3f8R<f7R=P;f5R>11;>R?P:P1P2P7P?17<:P3CNP4M:MP7A=;>?P4%8>=:=:/<4,7<C3P7P=P;11=;P3C9P7P<P2P4C3X271083R?108;R@'H14?@R@%;@'FP01082108='4R0%;0P7f9R0P1P0P<110<P1C9C3P41081108<'4R@g00IhRA%54RB%53RCg00JF%52?23410121013'4RD[10231024'4%51?223[RE%5:?212\DAE234P4n2001000000120000000W6W5W7PE^6C^5B^7AP4P8P>f:RAP3O4b4A29:0RBP9PAP7f<RCf;RE11CE3=P4f>RDf=RF%8E;:A/<4'7C3108C,4?P7PDP2PDPF11DFRDP2C9C3]0]1X39P711EA9=EAPA%8A=:C0/<A,7FC3108ER2/42P711FCR?A27D4X271>7?PFPCP?PCC9PFPCP?P0CGE?W0W1P>P4P:P3GCb4W0P4O1%;@P711A:R@P7PEP>P4C3X271>7@PAP011A0R@P:C9PAP0P@P:P3P9PA1084/42X39108A,>5P>P4E?O1X:B%;BeDKE?W0P4O1n200110200021110110100b@%8;=:<>/<3,70P4EBb1X39%8:=:;1=A=>eW<W;W9X>6W?W=WAW8o"). Qed.

(* [comment removed for export] *)

Section ReadLoop.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  (* [comment removed for export] *)
  Hypothesis AL_glob : forall a, al_globals a -> (0x69b38 <= bv_unsigned a < 0x69ee8)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x6b000)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x6b000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x6b000)%Z.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := O2Open.ENV a0s path.
  Let L : Z := Z.of_nat (length data).

  (* [comment removed for export] *)
  Definition fdsk (off : Z) : list (word * FdEntry) := (Z_to_bv 64 3, FdFile path (Z_to_bv 64 off)) :: O2Open.fds0.
  Definition modelk (off : Z) (vm : VmMaps) : Model := mkModelC (fdsk off) vm stdin0 fs0 None (Some tid) None.
  Definition model2 (vm : VmMaps) : Model := mkModelC O2Open.fds0 vm stdin0 fs0 None (Some tid) None.

  Lemma modelk_pure : forall off vm, md_pure (modelk off vm).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "h03offh12vmp;2p;1p;4g01]]j2:Tg007Aj10Tg007fj16Tg0056j14Tg01<nj19Tg00aVj18Tg00;mj21Tg01^Vj25Tg00>kj12Tg00>Kj13Tg01_6j47Tg00IJg01`5f1f0':g00Ja#0#0#0#0#0#0#6#4R0#9%80'11500R1#2%31'1%20%30'1C7W1W0o"). Qed.
  Lemma model2_pure : forall vm, md_pure (model2 vm).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "h02vmp;1p;2p;4g01`lj1:Tg007Aj10Tg007fj16Tg0056j14Tg01<nj19Tg00aVj18Tg00;mj21Tg01^Vj25Tg00>kj12Tg00>Kj13Tg01_6j47Tg01`5f0#:g00Ja#0#0#0#0#0#0#6#4R0#9%80'11500R1#2%31'1%20%30'1C7W0o"). Qed.
  Lemma fdsk_insert : forall off e, fd_insert (fdsk off) (Z_to_bv 64 3) e = (Z_to_bv 64 3, e) :: O2Open.fds0.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "h01eh13offp;1p;2p;4p;3g007Aj10Tg007fj1:Tg0056j12Tg01^Vj21Tg00>kj19Tg00XFj18Tg00:Rj13Tg008Dj24Tg01aej45Tg00^Oj36Tg00;mj27Tg00IJg01bER0g00JaR1#0#0#0#0#0#0#:R2#2R3/10R4#9P3P0%81#3,42f0C5g01c=564'7W0W1o"). Qed.
  Lemma fdsk_remove : forall off, fd_remove (fdsk off) (Z_to_bv 64 3) = O2Open.fds0.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "h03offp;1p;2g007Aj10Tg007fj15Tg0056j12Tg01^Vj21Tg00>kj14Tg00;mj23Tg00IJg00Ja#0#0#0#0#0#0#5#2g01bE'1#4g01c='3W0o"). Qed.
  Lemma fdsk_lookup3 : forall off, fd_lookup (fdsk off) (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 off)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "h03offp;1p;2g01<nj16Tg007Aj10Tg007fj12Tg008Dj21Tg01d0j25Tg01BFj24Tg00;mj23Tg00IJg01bER0#6p,4pathg00Ja#0#0#0#0#0#0#2f0'1'5,40'3W0o"). Qed.

  (* [comment removed for export] *)
  Definition slots (vals : list word) (buf : word) (len cap : Z) : Prop :=
    vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 a0s path envv /\ vals_ev vals 2 = p1 a0s path envv
    /\ vals_ev vals 5 = tid /\ vals_ev vals 6 = buf /\ vals_ev vals 7 = Z_to_bv 64 len /\ vals_ev vals 8 = Z_to_bv 64 cap.

  (* [comment removed for export] *)
  Definition vm_ok (vm : VmMaps) (j : nat) (cap : Z) : Prop :=
    vm_limit vm = lim /\ alloc_top vm = (bv_unsigned sp0 - 8388608)%Z /\ vm_init_sp vm = sp0
    /\ vm_resv (segments_reserved RSEGS) sp0 vm.
  Definition al_ok (A : AS) (M : word -> option byte) (vm : VmMaps) (buf : word) (cap : Z) (j : nat) : Prop :=
    ainv A M vm /\ live A buf = Some cap /\ (forall q, q <> buf -> live A q = None)
    /\ aroom A vm (need_k FUZZ_CALLS j) (need_b FUZZ_BMAX j cap).
  Definition side (A : AS) (vm : VmMaps) (M : word -> option byte) (buf : word) (cap : Z) (j : nat) : Prop :=
    al_ok A M vm buf cap j /\ vm_ok vm j cap /\ env_ok sp0 mem0 M /\ (cap = (65536 * 2 ^ Z.of_nat j)%Z /\ (Z.of_nat j <= 10)%Z).

  (* [comment removed for export] *)
  Definition at_loop (K : TSet) (j : nat) (buf : word) (cap len : Z) : Prop :=
    forall A vm vals R M,
      length vals = 41%nat -> slots vals buf len cap ->
      regs_ok (ENV vals) sr_L R -> know_ok RSEGS (ENV vals) M kn_ML ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) (firstn (Z.to_nat len) data) ->
      (0 <= len < cap)%Z -> (len <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x176e4) M (seg_rom RSEGS)) (modelk len vm)) K.

  Definition at_header (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 41%nat -> slots vals buf L cap ->
      regs_ok (ENV vals) sr_H R -> know_ok RSEGS (ENV vals) M kn_ML ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data -> (L < cap)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17714) M (seg_rom RSEGS)) (model2 vm)) K.

  Definition at_full (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 41%nat -> slots vals buf cap cap ->
      regs_ok (ENV vals) sr_F R -> know_ok RSEGS (ENV vals) M kn_ML ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) (firstn (Z.to_nat cap) data) -> (cap <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x176ac) M (seg_rom RSEGS)) (modelk cap vm)) K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition in_win (x : word) : Prop := (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z.

  (* [comment removed for export] *)
  Lemma buf_facts : forall A M vm buf cap j, side A vm M buf cap j ->
    (65536 <= cap)%Z /\ (0x6b000 <= bv_unsigned buf)%Z /\ (bv_unsigned buf + cap <= bv_unsigned sp0 - 8388608)%Z
    /\ (bv_unsigned buf mod 16 = 0)%Z
    /\ (forall x : word, (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z -> M x <> None /\ owned A x).
Proof.
  intros A M vm buf cap j (HAL & HVM & _ & Hcap & Hj).
  destruct HAL as (HI & Hl & _ & _). destruct HVM as (_ & Htop & _ & _).
  destruct (ai_live_hull A M vm buf cap HI Hl) as (Hc0 & Hal & Hend & Hbytes).
  pose proof (round16_ge cap) as Hr.
  assert (Hc1 : (2 ^ 0 <= 2 ^ Z.of_nat j)%Z) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 0)%Z with 1%Z in Hc1.
  assert (Hcap1 : (65536 <= cap)%Z) by lia.
  split; [exact Hcap1|].
  split; [exact (O2Malloc65536.live_big_lo sp0 Hvsp AL_grant A M vm buf cap HI Hl ltac:(lia))|].
  split; [lia|].
  split; [exact Hal|].
  intros x Hx.
  assert (Ea : at_ buf (bv_unsigned x - bv_unsigned buf) = x).
  { unfold at_. apply bv_eq. rewrite u_small by (pose proof (u64_range x); lia). lia. }
  destruct (Hbytes (bv_unsigned x - bv_unsigned buf)%Z ltac:(lia)) as (Ho & Hd & _).
  rewrite Ea in Ho, Hd. exact (conj Hd Ho).
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition in_data (x : word) : Prop :=
    (0x39000 <= bv_unsigned x < 0x49770)%Z \/ (0x498c8 <= bv_unsigned x < 0x69aa0)%Z \/ (0x69ee8 <= bv_unsigned x < 0x6b000)%Z.
(* [comment removed for export] *)

  Lemma side_frame : forall A vm M M' buf cap j,
    side A vm M buf cap j ->
    (forall x : word, M' x <> M x ->
       in_win x \/ in_data x \/ (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z) ->
    mem_grows M M' ->
    side A vm M' buf cap j.
Proof.
  intros A vm M M' buf cap j HS Hchg Hgr.
  (* keeps the section arguments the callers pass *)
  pose proof Htid as Htid0.
  pose proof SPlo as Hlo.
  pose proof (buf_facts A M vm buf cap j HS) as (Hcap & Hb0 & Hb1 & Hal & Hbb).
  destruct HS as (HAL & HVM & HENV & HCJ).
  destruct HAL as (HI & Hl & Hnl & Hroom).
  pose proof HVM as (_ & Htop & _ & _).
  (* [M'] agrees with [M] outside the stack window, the data ranges and the buffer *)
  assert (Hsame : forall x : word,
            ~ (in_win x \/ in_data x \/ (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z) -> M' x = M x).
  { intros x HP. destruct (M' x) as [b1|] eqn:E1; destruct (M x) as [b2|] eqn:E2.
    - destruct (bv_eq_dec _ b1 b2) as [->|NE]; [reflexivity|].
      exfalso. apply HP, Hchg. rewrite E1, E2. congruence.
    - exfalso. apply HP, Hchg. rewrite E1, E2. discriminate.
    - exfalso. apply HP, Hchg. rewrite E1, E2. discriminate.
    - reflexivity. }
  split; [|split; [exact HVM | split; [|exact HCJ]]].
  - split; [|split; [exact Hl | split; [exact Hnl | exact Hroom]]].
    apply (ai_frame A M M' vm HI).
    + intros a Ho Hn. apply Hsame. intros [W|[D|B]].
      * destruct (ai_owned_where A M vm a HI Ho) as [G|[[_ Gt] _]].
        -- pose proof (AL_glob a G). unfold in_win in W. lia.
        -- unfold in_win in W. lia.
      * destruct (ai_owned_where A M vm a HI Ho) as [G|[[Gr _] _]].
        -- pose proof (AL_glob a G). unfold in_data in D. lia.
        -- pose proof (AL_grant a Gr). unfold in_data in D. lia.
      * exact (Hn buf cap Hl B).
    + intros a _ Ha. exact (Hgr a Ha).
    + intros a [Gr Gt] Ha. pose proof (AL_grant a Gr) as Hg.
      destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned buf)) as [L1|L1];
        [| destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned buf + cap)) as [L2|L2]].
      * rewrite <- (Hsame a); [exact Ha|]. intros [W|[D|B]]; unfold in_win, in_data in *; lia.
      * exact (proj1 (Hbb a ltac:(lia))).
      * rewrite <- (Hsame a); [exact Ha|]. intros [W|[D|B]]; unfold in_win, in_data in *; lia.
  - destruct HENV as (Hab & Hcells & Hro). split; [|split].
    + intros a Ha. rewrite (Hsame a); [exact (Hab a Ha)|]. intros [W|[D|B]]; unfold in_win, in_data in *; lia.
    + intros a Ha Hne. rewrite (Hsame a); [exact (Hcells a Ha Hne)|]. intros [W|[D|B]]; unfold in_win, in_data in *; lia.
    + intros a Ha. rewrite (Hsame a); [exact (Hro a Ha)|]. intros [W|[D|B]]; unfold in_win, in_data in *; lia.
Qed.

  (* [comment removed for export] *)
  Lemma side_block : forall A vm M buf cap j E log,
    side A vm M buf cap j -> log_win_b 0 log = true -> ev E 0 = sp0 ->
    side A vm (mem_denot E M log) buf cap j
    /\ forall x : word, ~ in_win x -> mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "p'0h04__x1h14__x2h22Hah37__arithh44__ffh54__p1h66__sat3h76__sat4h88__varmaph95__with:4cstrh;5heq_Lh<1xh=6__sat5h>2H1h?2H2h@6__sat2hA1bhB1si001shC1AhD1EhE1HhF3HE0hG2HShH4HloghI3HnehJ2HxhK1MhL3OUThM6__sat1hN3bufhO3caphP1jhQ3loghR2vmi011gi021lp;3p;2p;1p;6p;4p;8p;:p;7g01dhj3}Tg01f1j3|Tg01g:j2hTg007Aj11Tg007fj1ITg0056j1TTg01<nj1gTg00>kj1ZTg01h;j6QTg02M7j2`Tg005Yj38Tg02N>j2KTg00XFj1BTg00:Rj1=Tg0063j22Tg00=Kj2:Tg02B0j1?Tg01SZj1<Tg00;0j2WTg000Nj2eTg00jKj1dTg00;mj2YTg00l\j1aTg00<Gj2PTg00<oj20Tg00=gj3OTg00Yij2_Tg00;Mj2^Tg00>Kj1]Tg00^oj2LTg00?ij1\Tg00@Gj1[Tg00A2j2FTg00`Oj2STg00aVj1{Tg00AUj3zTg00Ckj2yTg00DMj2xTg00E9j3vTg00EXj4oTg001^j6NTg00iQj2;Tg02OCj8nTg02PRj4Gj3mTg01?Mj2VTg01@4j26Tg01@PR0j2UTg02Bij1CTg009Oj2DTg016\j24Tg00?Kj1lTg00_Mj4kTg00oDj3jTg00B8j4>Tg00_kj6iTg02Ggj2MTg01C]j3fTg02Qdj3qTg02S<l:rTg011Uj4sTg00Bcj7tTg00d<j8uTg00JFj2XTg00a2j7cTg00CGj6bTf0R1#1#1p=E%B1#Bp=7%11#1#1#1p=w%11#1#1#1#1#1#1#1p=@g00KFR2/:1p=3g00IJR3f1R4g00fRP1C>p=HP4g00LlR5g00MKR6P6g00MkR7P1g00O2Ftp=9f3R8P5P6P6P7f2R9P4P1Gup=A1:94/X1p=5P9P5P6P6P7P4P1Fcp=JP4P5P6P6P7P1Ebp=R1041,X9p=pp,2ALR:p,2CLR;p,3ASR9}:;5|:'hg01`5g00JaR:#1R;#ER<#1R=#ER>#IR?#TR@%I<#TR<#gRA[g018Cg01NGg02T9#Zf7RBf6RCf5RDf4REP8P9EQg00ORRFg00eGRG/`4g00P2RH381K8Gp,3sp0RI58@p,4SPloRJ%B:#7#7#7#7#7#7#7#1#E#w#@#@#@#=RK12?IRL':%?1#<RMPBf;RNPCPGP4PEP@PI%=;RO%B;RP#1#ERQ#=RR'WRS12?1RT':XA@p,4data,e<R<#dRU,Y3p,1L=83URVeRWPV%a<R<%3URU1POR102ORX%3R102S[[%3ORYg00KdRZAOOR4UW2%3S\Z^2Y%BP#1#=RP,PORR%3P1WOPR[,02[\XRXAOOP4VZX2YRP%3[\Z^2YRY%==R=,_LRZ%3L%3=1^L=#3[[R=g00L@R[#]R\%Z[R[1L34%\3R]%[3R^1F3K1S3:R:'H,9^%{6R_1F3O%IQ5z3/H:,9^CA1y^7RQP1P91YFH1x19=8FHdAv324CoR2b4b8b9X031:K11:S4[^03P1PLPJO2b3bMb@b6b7b=b:b;1KBGRGP8ENP@PIg02UDRI,;T12?9RJ10JT35#<XA@P11;LI12?4RI10IL35#<ePGP8ENGnWJX<@PBPNPCP4CGPNP4O158A\M^<@f<RGPNf:RT=mCDRSf9RKf8RHPBEQPHPGPBP4CGPGP4O158A\M^<@PGPNPTPSPKPHPBPEPBPNPCP1CGPNP1O158A#<%1>#@#@#=R>,;LRA,VI10IA16IA'UP010JA16JA%?8%C8f=RJ,2?RI12?8RN1DIG,0N35'4'4P110NA%?ERG%CEf>,2?RS12?ERM1DSJ,0M35'4'4P8PDPEPWPVP<PUPRPXPPPYPZP=p-0RSP\P[P31L39P4%l3CkRJP]P^P31S3;R;g00d`RF1F3>9j3:ROC>,9^P_1HO;,9^R`P^P5P6P6P7PEEiRE5J^,R^CAPQP2b4b8b9X03X13W51;1>,041;4>R7?598g00PRR6[[^03^13^5SP112?TR5/0LP5PLPCO4b3b@b6b7b:b;%<GeO2O1'MW>P1O116NA1VML10ML16ML'UP012?DR0/0L160L%?C%CCf@R0,2?RM12?CRNf?,DM,0N35'4'4P110NL%?BRM%CBfA,2?RG12?BR?1DG0,0?35'4R?PWPVP<PUPRPXPPPYPZP=P\P[PJP]P^P3P;PFP:C>,9^RFP_P^P3P;g01IRRGPOC>,9^P_AJ^`FCACAPQP2b4b8b9X03X13104116971;9>1089758[[^03^13P1PIPLPCPKO4b3b6b7b=b:b;PMe3fW?P1O116NL14M?PCPHPBPWPVP<PUPRPXPPPYPZP=P\P[PJP]P^P3P;PGP:C>,9^P_AJ^EF,R^CAPQP2b4b8b9X03X13X5S1641Ap894P6[[^03^13^5SP11:AIPIPLPCO4b3b6b7b=b:b;%<MeO2O1'MW?P1O1n200110000021110211101bBW>P1O1n200110000021110211101bBWIX<@AqCTDM:rP1CsbLbEWFWHWGWQWDWPXO3XN@WKWRWCo"). Qed.

  (* [comment removed for export] *)
  Lemma side_block_wd : forall A vm M buf cap j E log,
    side A vm M buf cap j -> log_wd_b 0 0x39000 0x49770 log = true -> ev E 0 = sp0 ->
    side A vm (mem_denot E M log) buf cap j
    /\ forall x : word, ~ in_win x -> ~ (0x39000 <= bv_unsigned x < 0x49770)%Z -> mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "p'0h07__arithh16__sat5h24__x1h34cstrh45heq_Lh56__sat6h64__p1h74__ffh88__varmaph95__with:6__sat4h;6__sat7h<4__x2h=1si001sh>2H3h?2H4h@2HahA6__sat3hB1xhC2H1hD2H2hE1bhF1AhG1EhH1HhI2H0hJ3HE0hK2HShL4HloghM3HnehN3Hx1hO3Hx2hP1MhQ3OUThR3bufhS3caphT1jhU3loghV2vmi011gi021lp&0p;3p;2p;1p;6p;4p;=p;:p;7p;8g01dhk30:Tg01f1k309Tg01g:j2uTg007Aj11Tg007fj1TTg0056j1\Tg01<nj1tTg00>kj1ZTg01h;j6cTg02VEk405Tg005Yj3GTg02N>j2_Tg00XFj1=Tg0063j22Tg00=Kj27Tg02B0j1ATg01SZj1:Tg00:Rj1LTg00;0j2fTg000Nj2pTg00jKj1oTg00;mj2gTg00l\j1lTg00<Gj2YTg00<oj20Tg00=gj3XTg00Yij2jTg00;Mj2iTg00>Kj1hTg00^oj2WTg00?ik108Tg00@Gk107Tg00`Oj2eTg00aVk104Tg00AUk301Tg00Ckj2|Tg00DMj2{Tg00E9j3zTg00EXj4yTg001^j6aTg00?Kj1xTg00A2j2^Tg00oDj3dTg00iQj2@Tg02WKl=wTg02PRj4Qj3vTg01?Mj2KTg01@4j23Tg01@PR0j2JTg02Bij1FTg009Oj2CTg016\j25Tg00_Mj4sTg02Ggj2NTg01C]j3RTg02XYj3rTg02Qdj3qTg02S<l:}Tg011Uj4~Tg00JFj2VTg00B8j4UTg00Bck700Tg00d<j8nTg00_kk602Tg00a2k703Tg00CGj6mTg017_k706Tf0R1#1#1p=<%=1#=p=8%=1#1p=I%11#1#1#1#1#1#1#1p=?%11#1#1#Lp=B%11#=p=9%11#1#1#1p=]f3R2f2R3'7f1R4/01'Vp=4g00KFR5/71p=;%11#Lp=kg00IJR6/^1p=EP6P4g00fRP1CUp=HP4g00LlR7g00MKR8P8g00MkR9P1g00O2K00p=6P2P7P8P8P9P3P4P1Gnp=>P6P4g00d`P1CUp=MP4P7P8P8P9P1J02p=[P3P7P8P8P9P4P1K03p=DP4P7P8P8P9P1Emp=P1734/V1p=SP6P4g01IRP1CUp=O1041,V3p=bP3P7P8P8P9P4P1K06p=`p,2ALR7p,2CLR:p,3ASR:0:7:6097'ug01`5g00JaR7#1R:#<R;#1R<#<R=#TR>#\R?%T;#\R;#tR@[g018Cg01NGg02T9#Zf7RAf6RBf5RCf4RDP2P3Ecg00ORREg00eGRF%87RG#<#I#?#BRH%17#9#<#I#8#I#8#I#BRIP4H05g00P2RJ3G1_2Fp,3sp0RK5G?p,4SPloRL%=G#8#8#8#8#8#8#]#?#?#?#BRG12>KRM'7p,4SPhi%1=#?#?R=#1#]#?#?#B,7M%A1#:RNPH12>4ROPOPIC4#:RPf9RQf=RRf8RSPFPHPIP3PBP?PK%L:RT%=:RU#1#<RV#LRW'fRX12>1RY'7XE?p,4data,p;R;#oRZ,g6p,1L=G6ZR[eR\P[%l;R;%;ZRZ1YTWR]105TR^%;W105X[[R_%;TR`g00KdRaAXTW4UW@RW%;X\a^@`Rb%=U#kRU,YTRc%;U1fTURd,05[\^R^AXTU4VaX@`RU%;d\a^@`R`%L<R<,jMRa%;M%;<1iM<#;[[R<g00L@Rd#hRe%ZdRd1W64Rf&086Rg&076Rh%EG1e67Ri'H,6h&048R8%ET%TV6016RV/Hi,6hC>1|h9R9P1P31gEJ1{13=GEJdAz654CyRJb7b8b9X2617G117X4[^26P1PMPLO2b0bAb:b1b5b;b3b41_QFRFPCEaP\P[P;PZPcP^PUP`PaP<PePd%x6RLPg1^65%EHR5'H,6hP9PJb7b8b9%;HP1b0bAb:b1b3b4P\P[P;PZP]P_PWPbPcP^PUP`PaP<PePdPLPg%EIRb%L=R=#ERW9d6V'H,6hP9PJb7b8b91@X=,7IP1b0bAb:b1b5b;b3b4g02UDRV,@X,7IeP?PK1@YV12>2RKPKPYC4#:XE?P41@MV12>3RVPVPMC4#:ePFPCEaP1M=wWOWNXB?PQPRPSP3CQPRP3O15G@\P\N^B?PRf<RFf;RY=vABRXf:R_PQPSEcP_f>R]PQP3CQP]P3O15G@\P\N^B?PRPFPYPXP_PQPSPCPSPFPAP1CQPFP1O15G@#:1KOH10OH13OH'JP010VH13VH%A2%F212>]RVPKPK1CVRC4'5'5P110KH12>DRV1@M=RO'K10VO13VO'JP012>CRC/0O13CO%AB%FBfAR@,2>RX12>BRNPNf@RP,CXC4'5'5RXP110NO%AARG%FAREfB,2>RT12>ARjPj1CT@C4RT'5R@'5PBPSPAP\P[P;PZPcP^PUP`PaP<p-0RkPePdP61W63P4PLCsRLPgPh1e6:R:Ad6iWRW'M,6hP81HW:,6hRl1[hDRD5Dh,PhC>P9PJb7b8b9X26X<6W6Rm1@1=,041@4=Rn?S32g00PRRo[[^26^<6^6kRpP112>RRq/0MPqPMPBO4b0b:b1b5b3b4%:GeP\P[P;PZPcP^PUP`PaP<PePdPfPgPh1Mi5,6hP81H5i,6hRr1[h2Rs5Dh,PhC>P9PJb7b8b9X26X6kRt101HASH43Po[[^26^6kRuP110qIRvPqPQO3b0b:b1b5b3b4PHPjPjPIC4#:eO3O1'NW>P1O113NO1KjM10jM13jM'JP012>SRS/0M13SM%AQ%FQfDRw,2>Rx12>QRyPyfCRz,CxC4'5'5RxP110yM%A_R{%F_fE,2>R|12>_R}P}1C|wC4'5R|P\P[P;PZPcP^PUP`PaP<PePdPLPgPh1M:i,6hRwP8Ph1O:W,6hP8ADhlwC>C>P9PJb7b8b9X26X<6Rl1041133n1@3=P2P2P3C4[[^26^<6R=P112>PRPPMPBPQO4b0b1b5b;b3b4P{e3RW?P1O113yM15{|R|PQPYP_P\P[P;PZPcP^PUP`PaP<PePdPLPgPh1O:i,6hP8ADhDw,PhC>P9PJb7b8b9X26X<6X6kRw1341Ab234Po[[^26^<6^6kRDP117OPPPPMPBO4b0b1b5b;b3b4%:{R{eP\P[P;PZPcP^PUP`PaP<PtPuP110PIPPPFO3b0b1b5b;b3b4PHP}P}PIC4#:RueO3O1'NW?P1O1n200110000021110211101b=W>P1O1n200110000021110211101b=WCP1O113KH1KVI10VI13VI'JP010CI13CIPXP110NIP\P[P;PZPcP^PUP`PaP<PePdPfPgPh1Mib,6hRXP8Ph1Oi5,6hP8ADhrX%17#9#<#8#<#9#I#9#BRr#E/Hi,6h%=7#9#<#8#9#9#9#<#BR5#E,Mi,6h5Dh=`hs5`hC>C>P9PJb7b8b9X26X6k101I134HPHP3P3PIC4PrP3P3P5C4/52'5[[^26^6kP1%=7#9#<#8#8#9#8#9#BPqPq%=7#9#9#I#?#BC4PqPBPQO4b0bAb:b1b3b4PEe9RET9rG@WDP1O113NI1KjO10jO13jO'JP010SO13SOPxP110yOPQPYP_P\P[P;PZPcP^PUP`PaP<PmPpP110PMPPPMPBO4b0b:b1b5b3b4P{eP\P[P;PZPcP^PUP`PaP<PePdPfPgPh1Oib,6hP8ADhsX,PhC>P9PJb7b8b9X26X6kRJ131IAb34IPo[[^26^6kRkP117HPPPPQO3b0b:b1b5b3b4PueO3O1,N|W>P1O113yO1K}M10}M13}M'JP012>YR0/0M130M%AF%FFfGR0,2>R}12>FRyPyfF,C}C4'5'5P110yM%ARR}%FRfH,2>R|PqPq1C|0C4'5R|P\P[P;PZPcP^PUP`PaP<PlP=P112>zRzPMPBPQO4b0b1b5b;b3b4P}e3RW?P1O113yM15}|PFP]PRP\P[P;PZPcP^PUP`PaP<PwPDP117OzPzPMPBO4b0b1b5b;b3b4%:}eP\P[P;PZPcP^PUP`PaP<PJPkP117HzPzPFO3b0b1b5b;b3b4ASHqv#:eO3O1'NW?P1O1n200110000021110211101b=W>P1O1n200110000021110211101b=WDP1O1n200110000021110211101b=WCP1O1n200110000021110211101b=WMXB?AqAYBM:}P1C~bQbIbHWJWLWKWUWGWTXS6XR?WPWVWFo"). Qed.

  (* [comment removed for export] *)
  Definition DATA_RS : list (Z * Z) := [(0x39000, 0x49770); (0x498c8, 0x69aa0); (0x69ee8, 0x6b000)]%Z.
  Lemma side_block_wdl : forall A vm M buf cap j E log,
    side A vm M buf cap j -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    side A vm (mem_denot E M log) buf cap j
    /\ forall x : word, ~ in_win x -> ~ in_data x -> mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "p'0h04cstrh15heq_Lh27__arithh36__sat9h47__sat10h54__x1h61si001sh74__p1h84__ffh98__varmaph:5__with;7__sat11h<6__sat8h=2H7h>2H8h?6__sat5h@4__p2hA6__sat4hB6__sat3hC6__sat7hD2H5hE2H6hF4__p3hG6__sat6hH4__x2hI2H1hJ2H2hK2HahL1xhM1rhN2H3hO2H4hP1bhQ1AhR1EhS1HhT2H0hU3HE0hV2HShW4HloghX3HnehY3Hx1hZ3Hx2h[1Mh\3OUTh]3bufh^3caph_1jh`3logha2vmi011gi021lp%0p%1p&0p;3p;2p;1p;6p;4p;;p;:p;7p;8g01dhk30NTg01f1k30MTg01g:k20?Tg007Aj14Tg007fj1cTg0056j1tTg01<nk10>Tg00>kj1mTg01h;j6iTg02Y3k305Tg005Yj3RTg02N>j2fTg00XFj1FTg0063j23Tg00=Kj22Tg02B0j1GTg01SZj17Tg02Bij1HTg00:Rj1UTg00;0j2nTg000Nk20=Tg00jKk10;Tg00;mj2jTg00l\k108Tg00<Gj2kTg00<oj20Tg00=gj3hTg00Yik201Tg00;Mj2~Tg00>Kj1yTg00^oj2gTg00?ij1|Tg00@Gj1{Tg00`Oj2zTg00aVk10LTg00AUk30KTg00Ckk20JTg00DMk20ITg00E9k30HTg00EXk40ETg001^j6uTg01^Vk20DTg00iQj2QTg00JFj25Tg00^Oj3sTg00?Kk10@Tg00A2j2rTg00oDj3qTg011Uj4XTg02Z:j2pTg02Z[j6VTg02[<j3oTg02[]m;0<Tg02PRj4\k30:Tg01?Mj26Tg01@4j21Tg016\j2;Tg00_Mk407Tg02Ggj29Tg01C]j3lTg02Qdk304Tg02S<m:03Tg00B8j4`Tg00Bcj7bTg00d<j8[Tg02\lk30ATg02]Ik30BTg01aek40CTg00a2k700Tg00_kk60FTg017_k70GTg00CGj6wTg01@PR0j2vTg009Oj2dTg02XYj3}Tf0R1#4#4p=E%F1#Fp=>%41#4#4#4p=x%41#4#4#4#4#4#4#4p=J%41#4#4#Up=Pg00KFR2/21p=:%41#Up>02g00IJR3/r1p=If2R4g00LlR5g00MKR6P6g00MkR7P3f1R8g00fRP1C`g00O2R9Fbp=Af3R:P5P6P6P7P4P8P1G[p=eB0A331p=YB0B331p=Z%F1#4p=W%41#Fp=?P3P3P8P1H0Cp=a12:41081'5p=@P4P5P6P6P7P3P8g00d`P1C`P9Fbp=OP4P5P6P6P7P8P1K00p=BP8P5P6P6P7P1J0Fp=_P4P5P6P6P7P8P1K0Gp==P8P5P6P6P7P1Ewp=^f4R;P5P6P6P7P:P4P8P5P6P6P7P1EwG[p=K1248/51p=N1;81,;4p=C1081,54p=S10:41181'vp=8f6R<#Gf5R=#H12;:1d81,04'5';';p=L12;:1d81,04'5p=TP4P5P6P6P7P3P8g01IRP1C`P9Fbp=MP<P5P6P6P7P=P;P:P5P6P6P7P4P8P1G[G[p=DAl4819};:p=<1181,v4p=]1d81,04p>06%H:1248/51';p>09p,2ALR5p,2CLR9p,3ASR:0N5960M5+0?g01`5g00JaR5#4R9#ER>#4R?#ER@#cRA#tRB%c>#tR>$0>RC[g018Cg01NGg02T9#mf7RDP<P=P;P:P4Eig00ORREg00eGRFg02]fRG<058g00P2RH3R1f:Fp,3sp0RI5RBp,4SPloRJ%>5RK#F#>#>#>#>#>#>#x#J#J#J#PRL13AIRM'2p,4SPhi%4@#J#JR@#4#x#J#J#P,2M%G1#7RN%H8#7ROf9RPf=RQf8RRPFPGP4P<PBPI%U9RS%F9RT#4#ERU#URV'nRW13A1RX'2XPBp,4data-0=>R>$0;RY,j3p,1L=R3YRZeR[PZ&08>R>%:YRY1kSVR\102SR]%:V102W[[R^%:SR_g00KdR`AhSV8UWKRV%:W\`^K_Ra%FT$02RT,kSRb%:T1nSTRc,02[\]R]AhST8V`XK_RT%:c\`^K_R_%U?R?-01MR`%:M%:?1~M?#:[[R?g00L@Rc#yRd%mcRc1g38Re%|3Rf%{3Rg%IL1z35Rh5Ag&0L6R6%IS%cU60K3RU=AghCe20Jg7R7P1P41jEH20I14=REHdB0H328H0ERHb8b9b:X5312L112W8[^53P1PMPJO2b2bBbAb?bGbCb0b11fPFRFP=Eu20D33RJ%Y1RL#:RE%Z1RS%U@R@,QWRi'2'5XMJRj%EK#W#J#PRK%45#?#E#W#>#W#>#W#PRk'aRl%45#?#E#>#E#?#W#?#PRm%F5#?#E#>#?#?#?#E#PRn'aRo%F5#?#E#>#>#?#>#?#PRp%F5#?#?#W#J#PR5'aRq%yJRr5sJRs5sJRt%YlRu#:Rv%ZlRw/2iRxP[PZP>PYPbP]PTP_P`P?PdPc&0@3RyPf1r32R2%IKS005AgP7PHb8b9b:%:KP1b2bBbAb?b0b1PveP[PZP>PYP\P^PVPaPbP]PTP_P`P?PdPcPyPf%IkS01%I@Rv9q3URU5AgP7PHb8b9b:12kiP1b2bBbAb?bGbCb0b1PxeCXPJPjPoPs%YoRx#:Rz%ZoR{/2iR|P[PZP>PYPbP]PTP_P`P?PdPcPyPf%ImS029Ag2P7PHb8b9b:%:mP1b2bBbAb?b0b1PzeP[PZP>PYP\P^PVPaPbP]PTP_P`P?PdPcPyPf%InS03=AgUP7PHb8b9b:12niP1b2bBbAb?bGbCb0b1P|eCXPJPjPqPr%YqR|#:Rz%ZqR}/2iR~P[PZP>PYPbP]PTP_P`P?PdPcPyPf%IpS049Ag2P7PHb8b9b:%:pP1b2bBbAb?b0b1PzeP[PZP>PYP\P^PVPaPbP]PTP_P`P?PdPcPyPf%I5S05=AgUP7PHb8b9b:125iP1b2bBbAb?bGbCb0b1P~eCX1pJjEVEVEVg02UDRj,QW,2S,5EXMJ=oJGePBPI1QXj13A:RIPIPXC@#7XPBP81QMj13A4RjPjPMC@#7ePFP=EuPJPLPIPIPSC@#7XMJRSPlPtP[PZP>PYPbP]PTP_P`P?p-0RtPdPcPePfPgQ00=AghRlQ019OghS065BgRLQ02=AghRFQ039OghS075BgRX1_g:RE5=g5=gS08,^gP6PgPLDKP7PHb8b9b:X53W7101kS099NK1101nS0:9Nm1RW;C8g00PRR~[12K8Ri?S8kP~[[^53^7tP1Pp13ARRUPUP5C@RaPUP<O3b2bBbAb?b0b1PuPjPjPwC@#7ePJPSPoPsP[PZP>PYPbP]PTP_P`P?PdPcPePfPg1_g;Rs9=gX9=gES0;,^gP6PgPXDKP7PHb8b9b:X53X7tX@tAC8W4P~[12m8Ro?S8nP~[[^53^7t^@tP1Pa10UkS0<9NKURaPUP<O4b2bBbAb?b0b1PxPjPjP{C@#7ePJPSPqPrP[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ04=AghRrQ059OghS0=5BgRq9=gXRX9=gES0>,^gP6PgPqDKP7PHb8b9b:X53X7t1015S0?9Np19C8WP~[12p8RW?S85P~[[^53^7tP1PaPUP<O3b2bBbAb?b0b1P|PjPjP}C@#7e1pJSEVEVEVAoJSGeN;0<WZWYXLBPPPQPRP4C\PQP4O15RC\O\N^LBPQf<RSf;S0@>0:D<RJf:RGPPPREiPGf>R}PPP4C\P}P4O15RC\O\N^LBPQPSQ0@PJPGPPPRP=PRPSPDP1C\PSP1O15RC#713A8RC1QM@RR'6PCPRPCPRC8P010jR11jRP:P:13A}RjPIPIPjPQFLP110IR13A;S0A/6KQ0APKQ0APKC8P013A=S0B/0KQ0B/1KP<P<fAS0C,3ARC13A<RJPJPCf@RNFLS0DP110JK13ADRO/6pPOPpPOPpC8P010Up11UpPPPPfDR|,3ARa13APRqPqPafCR{FLS0EP110qp13AGRx/6mPxPmPxPmC8P0Q0@,3ARw/0m11wmPSPSfGS0F,3AS0G13ASRuPuQ0GfFRVFLS0HP110um%GQS0I%HQS0JfHS0K,3AR^13AQR\P\P^Q0FDTS0L';S0M';PSP}PQP[PZP>PYPbP]PTP_P`P?PdPcP31g34P8PyH07S0NPfPg1z39R9Aq3hvS0O5OgP6PgQ0O=Ag9S0P=BgsDKP7PHb8b9b:X53XH3X7tS0Q1Q1@,081Q8@S0R?N4:P~[[^53^H3^7tS0SP113A{Rv/0MPvPMf?RyO4b2b<b3b4b0b1Q0I#7eP[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ009OghRQP6PgABglEABgFs1_g=S0T9BgrS0U5=gS0V5=gDKP7PHb8b9b:X53X7tX@tXFtS0W101K15i415o:15W;3CP~[[^53^7t^@t^FtS0XP110v5S0Y10vnS0Z10vkPvPSO5b2b<b3b4b0b1Q0J#7eO3O1'9W=P1O111um16\nP\PnP\PnC8P010jn11jnPyPyfJS0[,3ARW13AyRoPoPWfIRWFLS0\P110on%GNS0]%HNRifK,3ARr13ANRFPFPrQ0[DTS0^';S0_PiQ0^P[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ029MghS0`P6PgPQP6Q08FDP7PHb8b9b:X53X7tS0a111m108KRrPKP4P4PkC@RlPmP4P4PnC@R};C:S0b[[^53^7tS0cP113AVRz10z5S0d5NpPzPPPyO4b2b3b4b;b0b1PieD<W>P1O111onQ0]Q0_';S0ePyQ0CPNP[PZP>PYPbP]PTP_P`P?Q0QQ0SP110zMPzPMfBR2O4b2S0fb3b4b;b0b1Q0]#7S0geP[PZP>PYPbP]PTP_P`P?Q0WQ0XP1Q0d10znS0h10zkS0iPzPyO5b2S0jb3b4b;b0b1%7iS0keO3O1'9W>P1O1n200110000021110211101b6W=P1O1n200110000021110211101b6WDP1O111qp16x5PxP5PxP5C8P010w511w5Q0HP110u5Q0IQ0MQ0JQ0LP[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ049MghS0lP6PgPQP6A=gLXFDP7PHb8b9b:X53S0m111pPpP4P4P5C@9Cl}\r[^53S0nP1PvPPPSO3b2bCb<b3b0b1Q0JeD<WEP1O111u516\mS0oP\PmP\PmC8S0pP010jmS0q11jmS0rQ0\P110omS0sQ0ePyQ0CPNP[PZP>PYPbP]PTP_P`P?Q0fb<b3b4b0b1Q0geS0fP[PZP>PYPbP]PTP_P`P?Q0jb<b3b4b0b1Q0keO3O1'9W=P1O111omS0j16FnS0tPFPnPFPnC8S0uP010CnS0v11CnS0wP2P2fMRr,3AR}13A2RlPlP}fLS0xFLS0yP110lnS0z%G{R}%H{RXfN,3ARLPvPvPLPrDTS0{';S0|PXQ0{P[PZP>PYPbP]PTP_P`P?Q0mQ0nP113AWRrPyP2O3b2b3b4b;b0b1PXeD<W>P1O111lnS0}Q0|,;}RLP2P|P{P[PZP>PYPbP]PTP_P`P?Q0QQ0SP110rMPrPMfERQO4b2S0~b3b4b;b0b1%7}S10eS11P[PZP>PYPbP]PTP_P`P?Q0WQ0XP110r5S1210rnS1310rkS14PrP2O5b2b3b4b;b0b1%7XS15eO3O1'9W>P1O1n200110000021110211101b6W=P1O1n200110000021110211101b6WEP1O1n200110000021110211101b6WDP1O1n200110000021110211101b6WIP1O111JK16OkPOPkPOPkC8P0Q0<11UkQ0EP110qk%GG%HGS0<13AQRGPxPxPGP|DTS16';Q0<Q16P[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ06P6PgQ009MghS00P6Q08FDP7PHb8b9b:X53X7tS08Q09118KQ0b[[^53^7tS09P110F5S0b9NpFPFP<PPO4b2bAb?bGb0b1Q0<eD<WJP1O111qk16xpS0<PxPpPxPpC8S16P010wpS1711wpS18Q0HP110upS19Q0oQ0pP0Q0qQ0rQ0\P1Q0sQ0ePyQ0CPNQ0fP[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ029OghP6PgQ049OghS04P6PgQ019MghS01P6PgQ069BgES06Q0V5=gDKFDP7PHb8b9b:X53X7tX@tXFtS0V101m108pS02114kS0fAS;:kRE12m:S1:/5=12p:S1;/5<S1<3CP~[[[[^53^7t^@t^FtS1=P1Q0dQ0h12KzS1>PzP<PPPSO7b2b<b3b4b0b1Q0keO3O1'9W=P1O1Q0jQ0tQ0uP0Q0vQ0wQ0yP1Q0zP}Q0|PXQ0{P[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ07P6PgQ0`P6PgQ04P6PgQ00P6Q0;FDFDP7PHb8b9b:X53X7tX@tS0;Q0:118m104p11:KPmP;P;PnC@=C=<[[[[^53^7t^@tS0`P112prS1?Q12'5S1@12KrS1AQ14'5S1BPrP<PPPSP2O7b2b3b4b;b0b1PXeD<W>P1O1Q0}P2P|P{Q11P[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ039MghP6PgQ04P6PgQ01P6PgQ06Q079BgsS04Q0U5=g5=gDKFDP7PHb8b9b:X53X7tX@tXFtS0U111nQ02Q0f10:nS03,5=S11Q1<5CEP~[[[[^53^7t^@t^FtS02P1Q1212mrS1<Q1APrP<PSPyO7b2b3b4b;b0b1Q15eO3O1,9LW>P1O1n200110000021110211101b6W=P1O1n200110000021110211101b6WDP1O111upS1C16\5S1DP\P5P\P5C8S1EP010j5S1F11j5S1GQ0\P110o5S1HQ0]Q0_PiQ0^P[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ0=P6PgQ0lP6PgQ00P6Q0>FDS0>CeP7PHb8b9b:X53X7tS00Q0?118pS1I114KQ1:Q03'5Q1;10:5R='55C;[[S1;[^53^7tS0?P1Q1>Q0i'5PzP<PPPyO5b2bCb<b3b0b1PieD<WEP1O111o5S1>16FmS03PFPmPFPmC8S1:P010CmS1J11CmS1KQ0yP110lmS1LP2P|P{P[PZP>PYPbP]PTP_P`P?Q0~b<b3b4b0b1Q10eP[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ059MghP6PgQ0lP6PgQ01P6PgQ06Q04Q0TQ0=5Bg5=g5=gDKFDP7PHb8b9b:X53X7tX@tXFtS061115Q1IQ0fQ1115<=5CEP~[[[[^53^7t^@t^FtS1IP1Q1?Q1<Q1APrPPPSPyO7b2b<b3b4b0b1Q15eO3O1,9LW=P1O111lmS1<16vnS1?Q0Z?]vnS0ZP010anS0f11anS11PQPQfPS04,3AREPGPGPEfOS0TFLS0=P110GnS01%GVRE%HVR=fQ,3AR;PzPzP;Q04DTS04';S0lP=Q04P[PZP>PYPbP]PTP_P`P?PdPcPePfPgQ07P6Q0>CeP7PHb8b9b:X53X7tS0>Q0:Q1;[^53^7tS0:P1Q0x,3ARe,2KS0x10ekS1;'5S07PeP<PyPQO5b2b3b4b;b0b1P=eD<W>P1O111GnS05Q0l,;ER;PQQ0FPVP[PZP>PYPbP]PTP_P`P?Q0QQ0SP110eMPePMQ0KO4b2b3b4b;b0b1%7ES0SeP[PZP>PYPbP]PTP_P`P?Q06Q1IP112peS0Q12meS0~Q0xPePSPyP2O7b2b3b4b;b0b1%7=S1MeO3O1'9W>P1O1n200110000021110211101b6W=P1O1n200110000021110211101b6WEP1O1n200110000021110211101b6WDP1O1n200110000021110211101b6WJP1O1n200110000021110211101b6WIP1O1n200110000021110211101b6WNP1O111IRQ0A/6MQ0APMQ0APMC8P0Q0B/0MQ0B/1MQ0DP110JM%GDS0DPDPlPOQ0C:06OlH09P[PZP>PYPbP]PTP_P`P?PdPcQ0NPfPgAOg9hRIP6PgQ0O9Mg9P6Q0P=BgIFDP7PHb8b9b:X53XH31081Q0R,141Q4@P:P:P4C@[[^53^H3P1P\PMP<PPO4b2b?bGbCb0b1Q0De3lWOP1O111JM16OKPOPKPOPKC8P010UK11UKQ0EP110qKQ0<Q16P0Q17Q18Q0HP1Q19Q0oQ0pP0Q0qQ0rQ0\P1Q0sQ0ePyQ0CPNP[PZP>PYPbP]PTP_P`P?PdPcQ0NPfPgAMg9hP6PgABgsIDKP7PHb8b9b:X53XH3X7tRH1181AS:48P~[[^53^H3^7tRtP112RzPzPMPyO4b2b<b3b4b0b1Q0geP[PZP>PYPbP]PTP_P`P?Q0WQ0XP1Q0dQ0hQ0iPzPSO5b2b<b3b4b0b1Q0keO3O1'9W=P1O1Q0jQ0tQ0uP0Q0vQ0wQ0yP1Q0zP}Q0|PXQ0{P[PZP>PYPbP]PTP_P`P?Q0aQ0cP1Q1@PrPPPyO4b2b3b4b;b0b1PXeD<W>P1O1Q0}P2P|P{P[PZP>PYPbP]PTP_P`P?PHPtP112RrPrPMP2O4b2R~b3b4b;b0b1Q10eP[PZP>PYPbP]PTP_P`P?Q0WQ0XP1Q12Q13Q14PrPyO5b2R:b3b4b;b0b1Q15eO3O1,9LW>P1O1n200110000021110211101b6W=P1O1n200110000021110211101b6WDP1O1Q1CQ1DQ1EP0Q1FQ1GQ0\P1Q1HQ0]Q0_PiQ0^P[PZP>PYPbP]PTP_P`P?Q0mQ0nP1PzPPPSO3b2bCb<b3b0b1PieD<WEP1O1Q1>Q03Q1:P0Q1JQ1KQ0yP1Q1LP2P|P{P[PZP>PYPbP]PTP_P`P?P~b<b3b4b0b1Q10eR~P[PZP>PYPbP]PTP_P`P?P:b<b3b4b0b1Q15eO3O1,9LW=P1O1Q1<Q1?Q0ZP0Q0fQ11Q0=P1Q01PEQ0lP=Q04P[PZP>PYPbP]PTP_P`P?Q0mQ0nP1PePyP2O3b2b3b4b;b0b1P=eD<W>P1O1Q05PQQ0FPVP[PZP>PYPbP]PTP_P`P?PHPtP112RePePMPQO4b2R:b3b4b;b0b1Q0SeRiP[PZP>PYPbP]PTP_P`P?Q0WQ0XP110e5R810enQ1;PeP2O5b2b3b4b;b0b1Q1MeO3O1,9;W>P1O1n200110000021110211101b6W=P1O1n200110000021110211101b6WEP1O1n200110000021110211101b6WDP1O1n200110000021110211101b6WIP1O111qK16xkPxPkPxPkC8P010wk11wkQ0HP110ukQ0IQ0MQ0JQ0LP[PZP>PYPbP]PTP_P`P?Q08Q09P1Q0Y9NpvPvP<PPO4b2b?bGbCb0b1Q0JeD<WJP1O111uk16\pP\PpP\PpC8P010jp11jpQ0\P110opQ03Q1:P0Q1JQ1KQ0yP1Q1LP2P|P{P~P[PZP>PYPbP]PTP_P`P?Q0VQ1=P1Q12Q13Q1APrP<PPPSO7b2b<b3b4b0b1Q15eO3O1,9LW=P1O1Q1<Q1?Q0ZP0Q0fQ11Q0=P1Q01PEQ0lP=Q04P[PZP>PYPbP]PTP_P`P?Q0;Q0`P1Q0Q/58Q07PeP<PPPSP2O7b2b3b4b;b0b1P=eD<W>P1O1Q05PQQ0FPVPiP[PZP>PYPbP]PTP_P`P?Q0UQ02P1P8Q0~Q0xPeP<PSPyO7b2b3b4b;b0b1Q1MeO3O1,9;W>P1O1n200110000021110211101b6W=P1O1n200110000021110211101b6WDP1O111op16F5Q0b?]F5P010C511C5Q0yP110l5P}Q0|PXQ0{P[PZP>PYPbP]PTP_P`P?Q00Q0?P1Q1BPrP<PPPyO5b2bCb<b3b0b1PXeD<WEP1O111l516vmPvPmPvPmC8P010am11amQ0=P110GmPQQ0FPVP[PZP>PYPbP]PTP_P`P?P:b<b3b4b0b1Q0SeP[PZP>PYPbP]PTP_P`P?Q06Q1IP1Q0QQ0~Q0xPePPPSPyO7b2b<b3b4b0b1Q1MeO3O1,9;W=P1O111Gm16znQ0h?]znP0Q0G/0nQ0G/1nQ0KQ0KfSR0,3ARzP^P^PzfRFLP110^n%GWRz%HWRGfT,3AR;PrPrP;P0DTR0';R;PGP0P[PZP>PYPbP]PTP_P`P?Q0>Q0:P1Q0T,3ARA,2KRK?SAkPAP<PyPQO5b2b3b4b;b0b1PGeD<W>P1O111^n1;z;Q0KQ0[PWP[PZP>PYPbP]PTP_P`P?PHPtP112RAPAPMQ0KO4b2b3b4b;b0b1%7zeP[PZP>PYPbP]PTP_P`P?Q06Q1IP112pA12mAPKPAPSPyP2O7b2b3b4b;b0b1%7GeO3O1'9W>P1O1n200110000021110211101b6W=P1O1n200110000021110211101b6WEP1O1n200110000021110211101b6WDP1O1n200110000021110211101b6WJP1O1n200110000021110211101b6WIP1O1n200110000021110211101b6WOP1O1n200110000021110211101b6WNP1O1n200110000021110211101b6WXXLBQ0@>04D<N:03P1CXb\bTbSWUWWWVW`WRW_X^3X]BW[WaWQo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma alu_add_wZ : forall (w : word) z, alu64 ALU_ADD w (Z_to_bv 64 z) = Z_to_bv 64 (bv_unsigned w + z).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "h05lemmah11wh21zp;1p;2p;3p;4p;6p;>p;9g007Aj10Tg007fj1ETg0056j1;Tg0063j26Tg008Dj21Tg005Yj3@j17Tg02^`j1:Tg02_PR0j35Tg02`8j42Tg02`_j18Tg02aNj43Tg02bEj39Tg02c;j4DTg02chj24Tg02dTj1CTg02eCj6?Tg02enl>=Tg009Oj2>Tg02fil9<Tg02:\j2ATg02gcj2BTg00Ja#0#0#0#0#0#0#ER1#;R2g00IJf1R3,61R4,11=@23P2%72R5%:2g02hoR6f2R71113R8351617R9,11R:=568g02i[R;P2\2R<\2R=%7;R>P2P<P5P2P2P5P5C2R?C2R@P0P=\;RAP;P=P>P@C2R>P;P=P@P2P<P?P2P2P5%82C3C3C399A>P0CDP614;6P7P:P2P5%C2P:P7f0R7E?P8P81428M>=1>93,11R9P91429M9<W01A131B47O2W2W1o"). Qed.

  Lemma stage_store_ok : forall vals M n, know_ok RSEGS (ENV vals) M l_knA -> (Z.of_nat n <= 65536)%Z ->
    store_ok RSEGS M (Z_to_bv 64 0x39739) n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "h02Hah17__arithh24__ffh36__sat1h46__sat2h56__sat3h68__varmaph75__with84cstrh95cstr0h:5heq_Lh;4__x1h<2HKh=2Hnh>1Mh?6__sat4h@6__sat5hA1nhB4valsp;1p;4p;2p;3p;8p;7p;>g007Aj12Tg007fj1ATg0056j1@Tg00>kj1KTg01<nj1GTg02jGj4XTg00jKj1<Tg00:Rj14Tg00=Kj28Tg00\2j1=Tg00XFj10Tg02kWj3^Tg00;mj2>Tg000Nj2YTg005Yj3FTg00l\j1ETg00<Gj2DTg00<oj2;Tg00;0j2CTg00=gj3BTg0063j2WTg00Yij2VTg00;Mj2UTg00>Kj1RTg00?Kj1QTg00?ij1OTg00@Gj1NTg00A2j27Tg00Ckj2MTg00DMj2PTg00E9j3LTg00EXj4STg00^oj2TTg00`Oj2bTg00aVj1aTg00b8j3JTg00d<j8`Tg009Oj2ITg00AUj3_Tg00B8j4HTg00a2j7]Tg00JFj2\Tg02l5l>[Tg00Bcj7ZTf0R0#2#2p=6%20#2#2#2p=3%=0#=p=5%00#2p=?g00KFR1/80p=1g00IJR2f1R3g00fRP0CHp=:P3g00LlR4g00MKR5P5g00MkR6P0g00O2FZp=9g00JaR7#2R8#6R9#2R:#6R;#AR<#@R=#K%A9#@R9#G\=g018Cg02@JR=p,3ENVR>f2R?O1P3g02mER@CX%<3%6;#3#3#4RA'8P=P>f4O1f3R>P@g00eG#=#5#5#5#5#5#5#5#5R=%07#0#6#0#3#3#3#4RB%07#6#?#3#3#3#4RC%07#0#6#?#0#0#0#6#0#0#0#6#0#4RDP?P3g02nBRE#GA^E@='>p,4data,Y9R9#<RE,>2p,1L=F2ER=eR@P=%E>RF%<>#1R>%E9R9%1ERE%48RG%08#?#4R8'DRH1;1GRI%181CG8RJ,;1[[RK%1GRLg00KdRMABG83UW0R8%1J\M^0LRJp,3sp0,W<RN%4:R:'VRO%1N%1:1UN:#1[[R:g00L@RN#RRP%KNRN%Q2RQ%O2RR%N2RS172BRT172DRU':'91MS6RVP0P?g00ORRWg00P2RX'>1P0?=FWXdAL213CSRXb2b6b718BDP0b1b3b4b5b9b8b:P@P=PFP>P9PEPHPKP8PJPOP:PPPN1T23PRPSP4P5P5P61b27R7172A':,9S%a5AJ2U7172C9J2T':,9SG`PVPXb2b6b7X;2180A1ID31IBC'8[^;2P0f9#<f7O2b1b3b4b5b9b8b:P@P=PFP>P9PE%4;R;,DG%1;1CG;RE,;1[\IABG;3VMX0L%1E\M^0LPHPKP8PJPOP:PPPNPQPRPSP4P5P5P61721/:U,9SP2PUg00d`172G=_2<CH,9SF]PVPXb2b6b7%1D1;DE'\P0b1b3b4b5b?b@b9b8b:M>[W=W<WAW>WBo"). Qed.

  Lemma slots_app : forall vals extra buf len cap, (9 <= length vals)%nat ->
    slots vals buf len cap -> slots (vals ++ extra) buf len cap.
Proof.
  intros vals extra buf len cap HL H. unfold slots in *.
  destruct H as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
  repeat split; rewrite vals_ev_app_l by lia; assumption. Qed.

  (* [comment removed for export] *)
  Lemma kwr_buf : forall A vm M buf cap j E (e : expr), side A vm M buf cap j -> edenot E e = buf ->
    kentry_ok RSEGS E M (KWr (SA e 0) 65536).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "p'0h04__x1h14__x2h24__x3h31xi001xh44__x4h54__x5h61Hh77__arithh84__ffh96__sat7h:6__sat8h;6__sat9h<8__varmaph=5__with>4cstrh?1dh@5heq_LhA1mhB2EMhC2HahD7__sat10hE7__sat11hF4__x6hG5cstr0hH2HxhI4__x7hJ1bi011bhK1zhL1AhM1EhN2H0hO2H1hP2H6hQ2HShR3Hb0hS3Hb1hT3HbbhU4HcaphV2HdhW2HmhX1MhY2_HhZ3bufh[3caph\1eh]2e0h^1jh_1oi021oh`2vmi033segp%0p&0p;3p;2p;1p;6p;7p;4p;8g01dhk30RTg01f1k30QTg01g:k20ETg007Aj11Tg007fj1{Tg0056j1zTg01<nR0k10DTg01h;k60@Tg01J9j2]Tg005Yj3<Tg02D`k704Tg00:Rj1ATg00=Kj22Tg00XFj1?Tg0063j20Tg009Oj23Tg00iQj2QTg00<oj29Tg00aVj1tTg00JFR1j25Tg034aj2TTg035lj4VTg00;0j2yTg00jKj1FTg008Dj2NTg037>j4[Tg000Nk20PTg00;mj2jTg00l\j1aTg00<Gk200Tg00=gj3~Tg00Yik20OTg00;Mj2}Tg00\2j1CTg00\Qj2|Tg00]cj2ZTg00>Kk10NTg00>kk10MTg00?Kk10LTg00?ik10KTg00@Gk10JTg00`Oj2xTg00oDj3fTg00A2j2vTg00AUk30CTg00Ckk20BTg00DMk20?Tg00E9k30>Tg00EXk40=Tg0120j2sTg001^j6rTg004Zj6kTg01BFj2dTg038>j3qTg039Bk10<Tg03:Dk10;Tg03;Ck10:Tg03<Ak109Tg03<_j1oTg03==j2nTg02Ggj2pTg01SZj1iTg029Xj4mTg02Fok408Tg03>Dk307Tg03?Ak606Tg011Uk40ATg03@Dj1wTg03AMj1uTg03BUk305Tg03Cbk203Tg03E1k20FTg00]:k30GTg00^Ok302Tg00^ok20HTg00_Mk40ITg00B8j4`Tg00b8j3lTg00Bcj7gTg00a2k701Tg00d<j8\Tf0R2#1#1p=c%12#1#1#1#1#1#1#1p=J%?2#?p=L%12#1#1#1p=hg00IJR3f1R4/}2g00KFR53<p=Bf2R6/24/52p=>f6R7f5R8f4R93<#if3R:P6P4P2Cm'5p=E1542,56p=S129:1342,96'5p==20F25p=P1364/22p=81325p=@1252p=4g00ORS00g00P2R;7<2p=U1|32p=IB0G342p=;g00L@R<@0242p=G20H32p=RP3P6P4P2H0Ip=61x32p=H1v32p=OP3P4g00fRR=P2C`p=KP3Al364P=P2C`p=YP6g00LlR>g00MKR?P?g00MkR@P3P4P=P2C`g00O2R=Fgp=7Al342p=DP3P4g00d`P2C`p=XP4P>P?P?P@P2P=Fgp=WP6P>P?P?P@P4P2K01p=MP9P>P?P?P@P:P>P?P?P@P6P=FgP4P2G\p=:P7P>P?P?P@P8P9P:P>P?P?P@P6P4P2G\G\p=_P:P>P?P?P@P6P4P2G\p=b1942,56p=eA<642#ip=^p,2ALR>p,2CLR=p,3ASR:0R>=60Q>R=+0Eg01`5g00JaRA#1RB#1S01#1S02#1RC#cRD#{RE#zRFQ02#{#zRG$0DRH[g018CRIg01NGg01OOf7RJP7P8P9P:P6J0@1]64=<F8f9RKPJf8RLP7P8P9P4K04%cD#JRM#ARN/28S03%?A#1#?#1#L#h#J#ARO10E7RP'213P8p,3sp0,0ERQ%1M#c#hRM#ARR'QRS%ACRC,BP10EJRT10E2RU13T7RV,9U3>PHPKP4O1%tGRWP>P=f;RXP4FE[^3F'53>3SP112N71BTC10ELRYPUPUPYPJD=PHf:RYP4O1PWP>P=f<RZP4FE[^3F'59>VS9>OTg02@JRVP8PK%P9/TNCVP212NL10EYR[13[K1B[C10EXR\13\YR],9U7>UPHf=R^P4O1PWP>P=f?R_P4FE[^3F'57>S5>OP112O\1B\C10EZS04PUPUQ04PXD=PHf>R\P4O1PWP>P=f@R`P4FE[^3F'59>]SPVPKP^%PL/TNCVP210E^,2O10E\R]/3^1B]C10E_R]13]\Ra,9U7>UPHfARbP4O1PWP>P=fCRcP4FE[^3F'57>SP112aS1B]C10E`R]PUPUP]P_D=PHfBR]P4O1PWP>P=fDRaP4FE[^3F'5PVP^Pb%PZ/TNCVP210Eb?8`S10E]/BC10EcRSPUPUPSP]D=PHfERdP4O1PWP>P=fGS05P4FE[^3F'5P11BSC10EaRSPUPUPSPcD=PHfFRSP4O1PWP>P=fHR1P4FE[^3FPVPbPd%P`/TNCVP210Ed/BCQ05,0ERbPUPUPbPSD=PHfIRbP4O1PWP>P=fKS06P4FE[^3Fp,4SPhi%JM#J#J#ARM,2QPFP1%@URe#4%ABRf%ADRD'yRg,9e%4NRhA8eNg'53S%44Re%F4=86NRiPVfNS0710E9#@/3:,NEP6C[#U[[^AI^?3'5XJF10E1#@Rj#419jgA8jNg,5h3SPVfMRjfL,0E#@/3:S08,NERkP6C[#U\i\e^AI^?3p,4data-0PGRl#FRm,j3p,1L=<3mRneS09Pn%alS0:%4mS0;200fDS0<195fRm%4D195g[[S0=%4fRlg00KdRoA~fD4UWCS0>%4g\o^ClS0?%?BRD#?#1#ARp-00fS0@%4p1yfpRq,95[\mS0AA~fp4VoXClS0B%4q\o^ClS0C20OQCS0D%4Q%4C1}QC#4[[S0Eg00eGRC#C#CRl#CS0F#CRq#CS0G#IS0H%IqRq%Il1|3CS0I';RC';';S0Jg00efRl'ZS0KQ0K&0N<Rp'G'G&0M<R<&0L3Rm%R:S0L?66m764&0K3Rr&0J3RsPs%?ARt#HRu%OMRv'K%t?R?PsPs1x3ARw%HDRD%ORRx9f3u3YP?Ps%OO=7swS0MP?Ps%ONRy=7sDP?PsPs%?tRz#?#L#L#L#L#L#L#1#c#h#J#J#J#AR{#OR|/KuP?1v35R}1Dw}R~57s%Of>0C3ERf,X~,WsA7s}y1D~y=7sf5Ms5Ms5MsD:F_D:D:20Bs@R@P2P6Q00/j;20?26#UdB0>354H0=R5b8b<b=X03X13X23124M1Q6R984:12O6Q0312{8%@8R;#419;gA8;Ng,5h3S[[[[[^03^13^23P2fOS0NPQfPS0O,0EPLP\P]PSp,4SPloRSO8b7b9b:b;bDbEb>b@PVP6PjPkP3Q08%F:S0P=82gXK3Q09Pn%a:S0QQ0P#4S0RQ0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0HQ0F#IS0F/;C,;q';/Zl/GpP<%R6%R9Rq%R8RC76:S0H764PrPsPs%HBRB?YuyP?PsPs1KDvP?PsPs%HzRzAf3Dx5YwP?PsPs1KyzP?PsA7s|DS0SP?1D~BRD/Du=7sfCbD:D:D:D:P@P5b8b<b=X03X13X23X43X53A846N129M1Q8R986712NJ12{JS0T13;7?8Jg[[[[[^03^13^23^43^53P2fTS0UPQ%FXS0VPZfUS0W,0ES0XPKP^PcQ06PSO:b7b9b:b;bDbEbGb>b@10EkQ08Q09PnQ0QQ0RQ0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0G#CRk#IQ0FQ0I';';/ZlR;%CkRk#CS0F#I%IkQ0J';';S0J/Zl/Gp'GP<Q0L?66qA6m8C764PrPsA7s}zS0LP?PsPsAYBzyP?PsPs1K}BP?PsPsQ01#HRk/KvP?PsPs%1t#HRtAf3kx5YwP?PsQ0MP?PsA7sytP?PsPs1K|kP?A7s}D1XDf,Ws5MsD:F_D:D:D:D:RDCbP@P5b8b<b=X03X13X23X43X53%49A868N%4:128M1Q7R989J12O812NK12{K%@L/3KRL#4?eLg[[[[[[[RL[^03^13^23^43^53P2Q0VQ0UPQPZQ0XPJPKPYP^PcQ05Q06PSO=b7b9b:b;bDbEbGb>b@'sEr10Ej#@/39,NE,0ERcPUPUPcQ0PD=P3Q07,0E#@/38Rc,NE,0EP210E6RUPUP2%F8RUD=XK3P2PcQ09Pn%a8%4UQ0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0F#C#IQ0J';/Zl/Gp,G;P<%R7Rl?6:m?66q%RJ?6Jm?6JC764PrPsQ02#HRCQ01#?#HRq57s1DCz,Xq,Ws5MsP?PDCbP@P5b8b<b=X03X13X23X43X53XF3XI31287RD13897e7PL[^03^13^23^43^53^F3^I3P2P[fW,0ER[#@/3\,NE,0E%F^fVPQP\P[PKPXPZP_PdPbPjPSO?b7b9b:b;bDbEbGb>b@,scEkPc10E4RZPZPc%F9D=Q0OP6O1PH1jH2fQP:O1=<H2P0PGfSP8O1Rc=<H2P0PGPHP41dG2RZP0g03F;R[PH%AARA9qVPQ00PH&0<2RL&0;2Rq&0:2$09RU,QT#o'nPWn0100000020000PWn10110000021010300n10110000021010100=^HW]BP4Q0UP7O1=<HZ1dG4=<HWRZPH1dG6P0PGp-0P2Pog00PRRon10110200021000000X]Hg01]APWP2EkPo1po2bOWN%iZeWBXJGP2O1fRP9O1=<HWP0P[PH10E8=qVAQ00PHPL1QPU#o,nqPWn0100000020000PWn10110000021010300=^HWA^HcWP>P=Q0WP8CmPXP8Q09Pn%aK%FK#4Q0:Q0;Q0@Q0AQ0BQ0CQ0DQ0EQ0K1G;p'GP<A6l7m?66mQ0H764PrPs1D~zR~=7sB1D~C,XB,Ws5MsP?Ps1DzC=7syP?PsQ0LP?PsA7syuP?PsQ0SP?A7swB1Dwu,XB,Ws5MsCbF_F_P@P5b8b<b=X03X13X23X43X53XF3%@2/39R9P4P4P9P8D=A887N%47Q03Q0T138J9eD7[[[[[^03^13^23^43^53^F3P2%F_P`PQfXQ04fY,0EPYP^P\Q0NPSO;b7b9b:b;bGb>b@O2P2H08'pWBn10110200021010101P2O1bBb_Q0O>07V6=^HWebHWHX3FJ06XWiXVeXAIX?3H0A1]daP]Er%PaRa#w,]d,0E%ua'3R]#419]gA8]Ng,5h3SPVPj%P1R1#w,]b,0E%u1'3/3:,NEP6C[#U\i\e^AI^?3'5eB05daNPVPj203b1/3:,NEP6C[#U\i\e^AI^?3'5ePVPdPb1TaNCVeb6WTWYP4P2O2n2001000000121000000W6WSP4P2O2n2001000000121000000W6WRP4P2O2n2001000000121000000W6WUP4P2O2n2011000000121000000b6WPWQW\WMW^X[3XZFWXW`WLo"). Qed.

  Lemma iter_from_ecall : forall K j buf cap len A vm vals R M (want : Z),
    ((L < cap)%Z -> at_header K j buf cap) -> ((cap <= L)%Z -> at_full K j buf cap) ->
    (forall len', (len < len')%Z -> at_loop K j buf cap len') ->
    length vals = 42%nat -> slots vals buf len cap -> vals_ev vals 41 = Z_to_bv 64 want ->
    want = Z.min (cap - len) 65536 ->
    regs_ok (ENV vals) (sr_upd l_srAn (ridx 12) (EVar 41)) R -> know_ok RSEGS (ENV vals) M l_knA ->
    side A vm M buf cap j -> bytes_at M (bv_unsigned buf) (firstn (Z.to_nat len) data) ->
    (0 <= len < cap)%Z -> (len <= L)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x37340) M (seg_rom RSEGS)) (modelk len vm)) K.
  Proof.
    intros K j buf cap len A vm vals R M want HDR FULL IH HL SL P41 Hwant HR HK HS HB Hlen HlenL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts A M vm buf cap j HS) as (Hcap & Hb0 & Hb1 & Hal & Hbb).
    assert (HLd : (L = Z.of_nat (length data))%Z) by reflexivity.
    assert (Hfl : Z.of_nat (length (firstn (Z.to_nat len) data)) = len) by (rewrite length_firstn; lia).
    assert (Hw : (1 <= want <= 65536)%Z) by lia.
    destruct l_itinA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRA & VLR & VLK).
    (* [comment removed for export] *)
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x37340) = Some ECALLW) by (vm_compute; reflexivity).
    assert (A17 : bv_unsigned (getr R 17) = 63%Z) by (regv HR (17 : reg); reflexivity).
    assert (A10 : getr R 10 = Z_to_bv 64 3) by (regv HR (10 : reg); reflexivity).
    assert (A11 : getr R 11 = Z_to_bv 64 0x39739) by (regv HR (11 : reg); reflexivity).
    assert (A12 : getr R 12 = Z_to_bv 64 want) by (regv HR (12 : reg); cbn [edenot ev ENV O2Open.ENV]; exact P41).
    destruct (read_bytes_map_of_store_ok RSEGS M (Z_to_bv 64 0x39739) (Z.to_nat want)
                (stage_store_ok vals M (Z.to_nat want) HK ltac:(lia)) ltac:(lia)) as [wv Hwv].
    rewrite Z2Nat.id in Hwv by lia.
    eapply (rz_read_file_at RSEGS R _ M (modelk len vm) ECALLW (Z_to_bv 64 3) (Z_to_bv 64 0x39739) (Z_to_bv 64 want)
              path (Z_to_bv 64 len) data wv K (modelk_pure len vm) HF is_ecall_ECALLW A17 A10
              ltac:(rewrite u_small by lia; lia) A11 A12 (fdsk_lookup3 len) Hfile Hwv).
    { rewrite u_small by lia. unfold rw_bytes_max. lia. }
    { unfold access_okb. rewrite !u_small by lia. unfold TASK_SIZE. apply andb_true_intro; split; apply Z.leb_le; lia. }
    rewrite v_addi_pc4 by lia. change (0x37340 + 4)%Z with 0x37344%Z.
    destruct (length_file_read data len want ltac:(lia) ltac:(lia)) as [Hbs Hn].
    set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)) in *.
    set (n := Z.of_nat (length bs)) in *.
    assert (HnE : n = Z.min want (L - len)) by lia. clear Hn.
    unfold len_word. fold n. rewrite bv_add_Z.
    unfold modelk. rewrite with_fds_C, m_fds_C, fdsk_insert. fold (fdsk (len + n)).
    change (mkModelC (fdsk (len + n)) vm stdin0 fs0 None (Some tid) None) with (modelk (len + n) vm).
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    - (* [comment removed for export] *)
      assert (HlenE : len = L) by lia.
      assert (Hbs0 : bs = []) by (destruct bs; [reflexivity | exfalso; subst n; cbn [length] in Hn0; lia]).
      rewrite Hbs0. cbn [wbytes]. rewrite Hn0, Z.add_0_r.
      pose proof (regs_set_a0 (ENV vals) _ R (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR1. clear HR. rename HR1 into HR.
      change (sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) (ELit 0)) with (l_srR (ELit 0)) in HR.
      assert (HK1 : know_ok RSEGS (ENV vals) M l_knR).
      { rewrite <- FRA. apply (know_ok_frame RSEGS (ENV vals) M M l_knA (ELit 0) 0x39739 65536 HK).
        - unfold flat, estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
        - intros; reflexivity.
        - apply mem_grows_refl. }
      clear HK. rename HK1 into HK.
      (* [comment removed for export] *)
      run_blk_keep scr0 42%nat.
      destruct l_itinC as (IC1 & _ & IC3). apply pair_equal_spec in IC3 as [MIS MISS].
      lazymatch type of EQM with _ = mem_denot _ _ ?log =>
        destruct (side_block A vm M buf cap j (ENV vals) log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
      rewrite <- EQM in HS1, OUT1.
      assert (HB1 : bytes_at M0 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. rewrite OUT1 by (unfold in_win; rewrite u_small by lia; lia). apply HB. rewrite Hfl. exact Hi. }
      clear EQM HS HB.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (B17 : bv_unsigned (getr Rc 17) = 57%Z) by (regv HR (17 : reg); reflexivity);
        assert (B10 : getr Rc 10 = Z_to_bv 64 3) by (regv HR (10 : reg); reflexivity)
      end.
      eapply (rz_close_at RSEGS _ _ _ (seg_rom RSEGS) (modelk len vm) ECALLW (Z_to_bv 64 3) _ K (modelk_pure len vm) HF
                is_ecall_ECALLW B17 B10 ltac:(rewrite u_small by lia; lia) (fdsk_lookup3 len)).
      rewrite v_addi_pc4 by lia. change (0x37340 + 4)%Z with 0x37344%Z.
      unfold modelk. rewrite with_fds_C, m_fds_C, fdsk_remove.
      change (mkModelC O2Open.fds0 vm stdin0 fs0 None (Some tid) None) with (model2 vm).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_set_a0 (ENV vals) sr Rc (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR1 end.
      clear HR. rename HR1 into HR.
      (* [comment removed for export] *)
      run_blk_keep scr0 42%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (HDR ltac:(lia) A vm (map (edenot (ENV vals)) h_rvl) Rx Mx) end.
      + rewrite length_map. reflexivity.
      + unfold slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth h_rvl rvl9 app tl edenot ev ENV O2Open.ENV].
        rewrite <- HlenE. repeat split; assumption.
      + change (ENV (map (edenot (ENV vals)) h_rvl)) with (xenv (ENV vals) h_rvl (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ =>
          p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) h_rvl idb _ (fun k => eq_refl) srb sr_H _ HR eq_refl eq_refl)) end.
        intros i Hi. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) h_rvl)) with (xenv (ENV vals) h_rvl (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          apply (know_ok_xfer_entails RSEGS (ENV vals) h_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + exact HS1.
      + rewrite HlenE in HB1. unfold L in HB1. rewrite Nat2Z.id, firstn_all in HB1. exact HB1.
      + lia.
    - (* [comment removed for export] *)
      assert (Hn1 : (1 <= n <= want)%Z) by lia. assert (HlenN : (len + n <= L)%Z) by lia. assert (HlenC : (len + n <= cap)%Z) by lia.
      set (M1 := wbytes M (Z_to_bv 64 0x39739) bs).
      assert (HS1 : side A vm M1 buf cap j).
      { apply (side_frame A vm M _ buf cap j HS); [| apply wbytes_grows].
        intros x Hne. right; left. unfold in_data. destruct (Z_lt_ge_dec (bv_unsigned x) 0x39739); [exfalso | destruct (Z_lt_ge_dec (bv_unsigned x) 0x49739); [lia | exfalso]];
          apply Hne; subst M1; apply wbytes_outside; rewrite u_small by lia; lia. }
      assert (HB1 : bytes_at M1 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. subst M1. rewrite wbytes_outside by (rewrite !u_small by lia; lia). apply HB. rewrite Hfl. exact Hi. }
      assert (Hsrc1 : rdn RSEGS M1 (Z_to_bv 64 0x39739) (length bs) = Some bs) by (apply rdn_wbytes_hit; rewrite u_small by lia; lia).
      assert (HK1 : know_ok RSEGS (ENV vals) M1 l_knR).
      { rewrite <- FRA. apply (know_ok_frame RSEGS (ENV vals) M M1 l_knA (ELit 0) 0x39739 65536 HK).
        - unfold flat, estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
        - intros x Hx. unfold estart in Hx. cbn [a_base a_off edenot] in Hx. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hx.
          subst M1. apply wbytes_outside; rewrite u_small by lia; lia.
        - apply wbytes_grows. }
      clear HK HS HB. clearbody M1.
      (* [comment removed for export] *)
      set (vals2 := vals ++ [Z_to_bv 64 n]).
      assert (HL2 : length vals2 = 43%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (SL2 : slots vals2 buf len cap) by (apply slots_app; [rewrite HL; lia | exact SL0]).
      assert (P42 : vals_ev vals2 42 = Z_to_bv 64 n).
      { subst vals2. replace 42%nat with (length vals + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
      pose proof (env_app_regs vals [Z_to_bv 64 n] (blobs_ev (blobs0 a0s path)) _ R ltac:(rewrite HL; exact VLR) HR) as HR2.
      pose proof (regs_set_a0 (ENV vals2) _ R (Z_to_bv 64 n) (EVar 42) HR2 P42) as HR3. clear HR HR2.
      change (sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) (EVar 42)) with (l_srR (EVar 42)) in HR3. rename HR3 into HR.
      pose proof (env_app_know RSEGS vals [Z_to_bv 64 n] (blobs_ev (blobs0 a0s path)) M1 l_knR ltac:(rewrite HL; exact VLK) HK1) as HK2. clear HK1.
      assert (HK : know_ok RSEGS (ENV vals2) M1 l_knRB).
      { apply Forall_cons; [| exact HK2]. cbn [kentry_ok edenot ev ENV O2Open.ENV]. fold vals2. rewrite P42, u_small by lia. lia. }
      clear HK2. destruct SL2 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
      (* [comment removed for export] *)
      run_blk_keep (SCR [false; true] [] []) 43%nat.
      lazymatch type of EQM with _ = mem_denot _ _ ?log =>
        destruct (side_block A vm M1 buf cap j (ENV vals2) log HS1 ltac:(vm_compute; reflexivity) Q0) as [HS2 OUT2] end.
      rewrite <- EQM in HS2, OUT2.
      assert (HB2 : bytes_at M0 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. rewrite OUT2 by (unfold in_win; rewrite u_small by lia; lia). apply HB1. rewrite Hfl. exact Hi. }
      assert (Hsrc2 : rdn RSEGS M0 (Z_to_bv 64 0x39739) (length bs) = Some bs).
      { rewrite <- Hsrc1. apply rdn_agree. intros k Hk. rewrite u_small by lia. apply OUT2. unfold in_win. rewrite u_small by lia. lia. }
      clear EQM HS1 HB1 Hsrc1.
      pose proof (buf_facts A M0 vm buf cap j HS2) as (_ & _ & _ & _ & Hbb2).
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned buf + len)).
      assert (Hdst : store_ok RSEGS M0 dst (length bs) = true).
      { apply store_ok_of_all; [subst dst; rewrite u_small by lia; lia|]. intros x Hx. subst dst. rewrite u_small in Hx by lia.
        unfold wview. destruct (M0 x) eqn:EM; [discriminate|]. exfalso. exact (proj1 (Hbb2 x ltac:(lia)) EM). }
      assert (MC : mcH M0 dst (Z_to_bv 64 0x39739) n bs).
      { constructor; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hsrc2.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = Z_to_bv 64 0x17698) by (regv HR (1 : reg); reflexivity);
        assert (B10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); cbn [edenot ev ENV O2Open.ENV]; fold vals2; rewrite Q6, Q7; subst dst; apply alu_add_wZ);
        assert (B11 : getr Rc 11 = Z_to_bv 64 0x39739) by (regv HR (11 : reg); reflexivity);
        assert (B12 : getr Rc 12 = Z_to_bv 64 n) by (regv HR (12 : reg); cbn [edenot ev ENV O2Open.ENV]; exact P42);
        destruct (ref_memcpy M0 dst (Z_to_bv 64 0x39739) n bs (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x17698)
                    ltac:(apply ret_ok_even; reflexivity) A1 B10 B11 B12) as (Rm & Hms & Hkeep);
        clear A1 B10 B11 B12
      end.
      replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
      set (M2 := wbytes M0 dst bs).
      assert (HS3 : side A vm M2 buf cap j).
      { apply (side_frame A vm M0 _ buf cap j HS2); [| apply wbytes_grows].
        intros x Hne. right; right.
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned buf + len)); [exfalso | destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned buf + len + n)); [lia | exfalso]];
          apply Hne; subst M2 dst; apply wbytes_outside; rewrite u_small by lia; lia. }
      assert (HB3 : bytes_at M2 (bv_unsigned buf) (firstn (Z.to_nat (len + n)) data)).
      { replace (firstn (Z.to_nat (len + n)) data) with (firstn (Z.to_nat len) data ++ bs).
        2:{ rewrite Hbs, firstn_app_skipn. rewrite <- (State.firstn_min_length _ data (Z.to_nat len + Z.to_nat want)), <- (State.firstn_min_length _ data (Z.to_nat (len + n))).
            f_equal. lia. }
        subst M2 dst. replace (bv_unsigned buf + len)%Z with (bv_unsigned buf + Z.of_nat (length (firstn (Z.to_nat len) data)))%Z by lia.
        apply bytes_at_extend; [lia | lia | exact HB2]. }
      (* [comment removed for export] *)
      destruct l_itinB as (_ & _ & VLB & _ & SRD & KND & VLD).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path)) sr Rc Rm callee_kept ltac:(rewrite HL2; exact VLB) HR Hkeep callee_kept_no0) as HR4 end.
      rewrite HL2 in HR4. lazymatch type of HR4 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR4 end.
      clear HR Hkeep.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_ok_call RSEGS (ENV vals2) M0 M2 [] 0 0 IHI 0x39000) as KC;
        specialize (KC ltac:(cbn [ev ENV O2Open.ENV]; fold vals2; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
        specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HK4; clear KC
      end.
      specialize (HK4 ltac:(intros x Hnt; subst M2 dst; apply wbytes_outside; [rewrite u_small by lia; lia|]; rewrite u_small by lia;
                              unfold touched, IHI, WIN in Hnt; cbn [ev ENV O2Open.ENV] in Hnt; fold vals2 in Hnt; rewrite Q0 in Hnt; lia)
                      ltac:(intros x _ Hx; apply (wbytes_grows bs M0 dst); exact Hx)
                      ltac:(intros m a k H1 H2; apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2])).
      lazymatch type of HK4 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK4 end. clear HK.
      pose proof (env_app_know RSEGS vals2 (junk_vals Rm) (blobs_ev (blobs0 a0s path)) M2 _ ltac:(rewrite HL2; exact VLD) HK4) as HK. clear HK4.
      rename HR4 into HR.
      set (vals3 := vals2 ++ junk_vals Rm) in *.
      assert (HL3 : length vals3 = 75%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (SL3 : slots vals3 buf len cap) by (subst vals3; apply slots_app; [rewrite HL2; lia | repeat split; assumption]).
      assert (R42 : vals_ev vals3 42 = Z_to_bv 64 n) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact P42).
      clearbody vals3. clear Q0 Q1 Q2 Q5 Q6 Q7 Q8. destruct SL3 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
      change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
      clearbody M2. clear Hdst MC Hsrc2 HB2 HS2 Hbb2.
      destruct l_itinD as (_ & _ & _ & IDn & IDt & S19).
      apply pair_equal_spec in IDn as [MISn MISSn]. apply pair_equal_spec in IDt as [MISt MISSt].
      destruct (Z.eq_dec (len + n) cap) as [Hfull|Hnf].
      + (* [comment removed for export] *)
        run_blk_keep (SCR [true] [] []) 75%nat.
        { cbn [sc_denot branch_taken edenot ev ENV O2Open.ENV]. rewrite Q7, Q8, R42, alu_add_Z.
          unfold bv_eqb. rewrite !u_small by lia. apply Z.eqb_eq. exact Hfull. }
        cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end. rewrite Hfull.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
          apply (FULL ltac:(lia) A vm (map (edenot (ENV vals3)) f_rvl) Rx Mx) end.
        * rewrite length_map. reflexivity.
        * unfold slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth f_rvl rvl9 app tl edenot ev ENV O2Open.ENV].
          repeat split; assumption.
        * change (ENV (map (edenot (ENV vals3)) f_rvl)) with (xenv (ENV vals3) f_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) f_rvl idb _ (fun k => eq_refl) srb sr_F _ HR eq_refl eq_refl)) end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[Hi|[]]]; [exfalso; lia|]. subst i.
          cbn [nth sr_F emap rv f_rvl rvl9 app tl idb edenot ev ENV O2Open.ENV]. rewrite Q7, Q8, R42, alu_add_Z. f_equal. lia.
        * change (ENV (map (edenot (ENV vals3)) f_rvl)) with (xenv (ENV vals3) f_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals3) f_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply (kwr_buf A vm M2 buf cap j _ (EVar 6) HS3). cbn [edenot ev ENV O2Open.ENV]. exact Q6.
        * exact HS3.
        * rewrite <- Hfull. exact HB3.
        * lia.
        (* [comment removed for export] *)
      + (* [comment removed for export] *)
        run_blk_keep (SCR [false] [] []) 75%nat.
        { cbn [sc_denot branch_taken edenot ev ENV O2Open.ENV]. rewrite Q7, Q8, R42, alu_add_Z.
          unfold bv_eqb. rewrite !u_small by lia. apply Z.eqb_neq. exact Hnf. }
        cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
          apply (IH (len + n)%Z ltac:(lia) A vm (map (edenot (ENV vals3)) d_rvl) Rx Mx) end.
        * rewrite length_map. reflexivity.
        * unfold slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth d_rvl rvl9 app tl edenot ev ENV O2Open.ENV].
          rewrite Q7, R42, alu_add_Z. repeat split; assumption || reflexivity.
        * change (ENV (map (edenot (ENV vals3)) d_rvl)) with (xenv (ENV vals3) d_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) d_rvl idb _ (fun k => eq_refl) srb sr_L _ HR eq_refl eq_refl)) end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * change (ENV (map (edenot (ENV vals3)) d_rvl)) with (xenv (ENV vals3) d_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals3) d_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply (kwr_buf A vm M2 buf cap j _ (EVar 6) HS3). cbn [edenot ev ENV O2Open.ENV]. exact Q6.
        * exact HS3.
        * exact HB3.
        * lia.
        * lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma want_x_val : forall vals len cap,
    vals_ev vals 7 = Z_to_bv 64 len -> vals_ev vals 8 = Z_to_bv 64 cap ->
    edenot (ENV vals) want_x = Z_to_bv 64 (cap - len).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop ()) ["ReadLoop"] "h01bh12Hah24__x1h34__x2h42H7h52H8h67__arithh74__ffh87__sat10h97__sat11h:6__sat9h;8__varmaph<5__with=3caph>4cstrh?5heq_Lh@3lenhA4valsp;1p;2p;3p;4p;7p;8p;6g007Aj13Tg007fj1BTg0056j1=Tg00>kj1<Tg00\2j12Tg01MCj25Tg008Dj21j1`Tg005Yj30Tg00nEj1OTg00W0j48Tg02_Pj36Tg00iQj29Tg00Poj2@Tg009Oj2CTg00;mj2:Tg000Nj2XTg00jKj1VTg00l\j1UTg00:Rj1;Tg00XFj1?Tg00<Gj2RTg00<oj2>Tg00;0j2QTg00=gj3NTg0063j2LTg00Yij2KTg00;Mj2HTg00>Kj1ITg00^oj2JTg00?Kj1GTg00_Mj4FTg00?ij1MTg00@Gj1ETg00A2j2PTg00`Oj2ATg00b[j3DTg00b8j3STg00oDj3TTg00B8j4cTg00Bcj7bTg00Ckj2aTg00DMj2_Tg00E9j3\Tg00EXj4[Tg01F:j8YTg02gcj2ZTg001^j67Tg0629j2WTg01J9j2]Tg00=Kj2^Tg00KFR0f0R1'^p=4g00JaR2#3R3#3#3R4#3R5#3#3#BR6#=R7#<g00IJR8f2R9g00eG#2#2#2#2#2#2#2R:'5f1R;,16R<507f3R=%2:R>'5=07<P7116=R<g02hoR?P6g00WZR@%O2RA,16RBP1C8f5/5>36f4RC,9=,16RD507X07P71169REP6P@PB116CC8=6?1=07DX07P71@A=RF,16RGA6?1<=07DX07P71CF9RH,16A071DX07P8P7%`6RDPDPH199=RHP7\8/:D%B4#=p,4data'XR4#VRD,:8p,1L=08DRIePI%U4%4D%;3RD%?3#?#3#;R4'R1>0D%441QD4RI,>0[[%4DRJg00KdRKAND4;UW1%4I\K^1Jp,3sp0,L6RJ%;5R5'K%4J%451HJ5#4[[g00L@R5#I%<5P81J89P;%G8CF%M8%E8R5g00Llg00MKRJPJg00MkRJP81P8A1A82R25D81A83R35S8g00NKAT832Ccg00O2Fb1a5JP1P9g00ORRJg00P2R5':1_19=0J5dA\80;C[b7b;b<X28X381@A1/C;19;1508^28^38P1f8f9O2b6b:b8b9b>b?GYA6?GE1ZF9E7P6P@PBP<C81WA=E715C>P1E715C:P;E7p,3ENVPCO1g05Sm']116H507eW5W4X=8W@WAo"). Qed.

  Theorem read_loop : forall K j buf cap,
    ((L < cap)%Z -> at_header K j buf cap) -> ((cap <= L)%Z -> at_full K j buf cap) ->
    forall len, at_loop K j buf cap len.
  Proof.
    intros K j buf cap HDR FULL len0.
    enough (G : forall fuel len, (cap - len <= Z.of_nat fuel)%Z -> at_loop K j buf cap len) by (apply (G (Z.to_nat (cap - len0))); lia).
    induction fuel as [|fuel IHf]; intros len Hle A vm vals R M HL SL HR HK HS HB Hlen HlenL; [exfalso; lia|].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts A M vm buf cap j HS) as (Hcap & Hb0 & Hb1 & Hal & Hbb).
    assert (Hfl : Z.of_nat (length (firstn (Z.to_nat len) data)) = len) by (rewrite length_firstn; unfold L in HlenL; lia).
    assert (IH : forall len', (len < len')%Z -> at_loop K j buf cap len') by (intros len' Hlt; apply IHf; lia).
    destruct l_itinA as (_ & _ & _ & _ & WX & SRU & VLn & VLt & VLK & _).
    pose proof (want_x_val vals len cap P7 P8) as HWX. unfold want_x in HWX.
    unfold modelk.
    destruct (Z_lt_ge_dec (cap - len) 65536) as [Hlt|Hge].
    - (* [comment removed for export] *)
      run_blk_keep (SCR [true] [] []) 41%nat.
      { cbn [sc_denot branch_taken]. rewrite HWX. cbn [edenot]. unfold bv_ltu. rewrite !u_small by lia. apply Z.ltb_lt. lia. }
      lazymatch type of EQM with _ = mem_denot _ _ ?log =>
        destruct (side_block A vm M buf cap j (ENV vals) log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
      rewrite <- EQM in HS1, OUT1.
      assert (HB1 : bytes_at M0 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. rewrite OUT1 by (unfold in_win; rewrite u_small by lia; lia). apply HB. rewrite Hfl. exact Hi. }
      clear EQM HS HB.
      set (vals1 := vals ++ [Z_to_bv 64 (cap - len)]).
      assert (P41 : vals_ev vals1 41 = Z_to_bv 64 (cap - len)).
      { subst vals1. replace 41%nat with (length vals + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [Z_to_bv 64 (cap - len)] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; exact VLt) HR) as HR1;
        pose proof (regs_ok_same (ENV vals1) sr Rc 12 (EVar 41) HR1 ltac:(intros H12; apply (f_equal bv_unsigned) in H12; discriminate H12)
                      ltac:(let e := eval vm_compute in (sr_get sr (12 : reg)) in
                            rewrite (HR (12 : reg)); change (sr_get sr (12 : reg)) with e;
                            rewrite HWX; cbn [edenot ev ENV O2Open.ENV]; symmetry; exact P41)) as HR2
      end.
      clear HR HR1.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      apply (iter_from_ecall K j buf cap len A vm vals1 _ M0 (cap - len) HDR FULL IH); try assumption.
      + subst vals1. rewrite length_app, HL. reflexivity.
      + subst vals1. apply slots_app; [rewrite HL; lia | exact SL0].
      + lia.
      + apply (env_app_know RSEGS vals _ (blobs_ev (blobs0 a0s path)) M0 _ ltac:(rewrite HL; exact VLK)). exact HK.
    - (* [comment removed for export] *)
      run_blk_keep (SCR [false] [] []) 41%nat.
      { cbn [sc_denot branch_taken]. rewrite HWX. cbn [edenot]. unfold bv_ltu. rewrite !u_small by lia. apply Z.ltb_ge. lia. }
      lazymatch type of EQM with _ = mem_denot _ _ ?log =>
        destruct (side_block A vm M buf cap j (ENV vals) log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
      rewrite <- EQM in HS1, OUT1.
      assert (HB1 : bytes_at M0 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. rewrite OUT1 by (unfold in_win; rewrite u_small by lia; lia). apply HB. rewrite Hfl. exact Hi. }
      clear EQM HS HB.
      set (vals1 := vals ++ [Z_to_bv 64 65536]).
      assert (P41 : vals_ev vals1 41 = Z_to_bv 64 65536).
      { subst vals1. replace 41%nat with (length vals + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [Z_to_bv 64 65536] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; exact VLn) HR) as HR1;
        pose proof (regs_ok_same (ENV vals1) sr Rc 12 (EVar 41) HR1 ltac:(intros H12; apply (f_equal bv_unsigned) in H12; discriminate H12)
                      ltac:(let e := eval vm_compute in (sr_get sr (12 : reg)) in
                            rewrite (HR (12 : reg)); change (sr_get sr (12 : reg)) with e;
                            cbn [edenot ev ENV O2Open.ENV]; symmetry; exact P41)) as HR2
      end.
      clear HR HR1.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      apply (iter_from_ecall K j buf cap len A vm vals1 _ M0 65536 HDR FULL IH); try assumption.
      + subst vals1. rewrite length_app, HL. reflexivity.
      + subst vals1. apply slots_app; [rewrite HL; lia | exact SL0].
      + lia.
      + apply (env_app_know RSEGS vals _ (blobs_ev (blobs0 a0s path)) M0 _ ltac:(rewrite HL; exact VLK)). exact HK.
  Qed.

  (* [comment removed for export] *)
  Theorem read_k0_entry : forall K,
    (forall buf, at_loop K 0 buf 65536 0) ->
    O2Malloc65536.at_buf sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim (FdFile path (Z_to_bv 64 0)) K.
  Proof.
    intros K HLOOP A1 vm1 vals R M HL P0 P1 P2 P5 HI Hlive Hlq Hroom Hvl Htop Hisp Hres HR HK HE.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    unfold O2Open.model1g. rewrite with_vmmaps_C.
    change (mkModelC (O2Open.fds1g (FdFile path (Z_to_bv 64 0))) vm1 stdin0 fs0 None (Some tid) None) with (modelk 0 vm1).
    change O2Malloc65536.ok_sr with ok_sr in HR. change O2Malloc65536.ok_kn with ok_kn in HK.
    unfold modelk.
    run_blk_keep (SCR [false] [] []) 70%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    destruct e_itin as [_ IE]. apply pair_equal_spec in IE as [MIS MISS].
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
      apply (HLOOP (vals_ev vals 48) A1 vm1 (map (edenot (ENV vals)) e_rvl) Rx Mx) end.
    - rewrite length_map. reflexivity.
    - unfold slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth e_rvl rvl9 app tl edenot ev ENV O2Open.ENV].
      repeat split; assumption || reflexivity.
    - change (ENV (map (edenot (ENV vals)) e_rvl)) with (xenv (ENV vals) e_rvl (blobs_ev (blobs0 a0s path))).
      lazymatch type of HR with regs_ok _ ?sr _ =>
        p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) e_rvl idb _ (fun k => eq_refl) srb sr_L _ HR eq_refl eq_refl)) end.
      intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
      destruct Hi as [Hi|[]]. exfalso; lia.
    - change (ENV (map (edenot (ENV vals)) e_rvl)) with (xenv (ENV vals) e_rvl (blobs_ev (blobs0 a0s path))).
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (know_ok_xfer_entails RSEGS (ENV vals) e_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
      lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    - split; [|split; [|split; [exact HE | split; [reflexivity | lia]]]].
      + split; [exact HI|]. split; [exact Hlive|]. split; [exact Hlq|]. exact Hroom.
      + split; [exact Hvl|]. split; [exact Htop|]. split; [exact Hisp|]. exact Hres.
    - intros i Hi. change (firstn (Z.to_nat 0) data) with (@nil byte) in Hi. cbn [length Z.of_nat] in Hi. lia.
    - lia.
    - unfold L. lia.
  Qed.
End ReadLoop.
