(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy; the exit tactic's thread-pointer and thread-id addresses corrected to this binary's). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibKnowXfer LibTail SymCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib LibWritevG.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2ExitBase V2StdioDefs V2Exit V2Startup V2StartupDefs V2StartupFacts V2MainEntry V2LibStdioCall V2OpenFail_defs V2OpenFail_tail V2OpenFail_tail2 V2Open_defs V2Open V2Oom_defs V2Oom V2MemPreds V2Malloc65536 V2DirRead_defs V2MemcpyBase V2Memcpy V2ReadLoop_defs V2ReadLoop V2Grow V2Hdr_defs V2Hdr V2FuzzIface V2TRun_defs V2TRun.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2TRunE () := "C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib2V2:V2MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib2V27V2TRunE8pendingPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C47Corelib4Init3Nat3mulC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec:zero_linesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Peano2le00C47Corelib4Init5Peano2ltC59OSSVerify5KrLib2V26V2TRun5callsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun:bufW_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC59OSSVerify5KrLib2V2=V2Malloc655366env_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_free_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC47Corelib4Init5Logic3notC59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun=ownedA_rangeTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsc59OSSVerify5KrLib2V27V2TRunE>pendingP_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open3ENVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2GrowAknow_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2or01C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_winC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2V2;V2StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun=ext_val_zx_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib2V2;V2StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2V2;V2StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2V2;V2StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC69OSSVerify5KrLib6Common9CliDriver3Amb6a_drawC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2StartupDefs8canary_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V27V2TRunEAzero_lines_lengthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib6Common9CliDriver8SymDrive:kblob_findC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9kblob_rdnC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2StartupDefs;guard_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2StartupFacts=guard_bytes_wC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2V2;V2StdioDefs>stdout_pending01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9t_eq_reflC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase7ai_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V27V2TRunE6at_fn1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open4fds0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6STOPSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7fn1_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7fn1_sr2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2V2;V2TRun_defs6sr_FN1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6kn_FN1C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs8fn1_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6fn1_r1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7fn1_kn1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs8fn1_kn2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6fn1_r2C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2V2>V2MallocLayout4LU16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2MallocLayout6LU17okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2V2:V2Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant02C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX true.
Tactic Notation "run_blkP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSP scr NX true.

(* [comment removed for export] *)
Ltac close_exit_code HR HK P0 Hh Hlazy sp0 OFF WLO WP2 CODE :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) with (exit_code CODE) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev V2Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x56270), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V2Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev V2Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V2Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V2Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V2Open.ENV] in Ktid |- *; lia
      | cbn [ev V2Open.ENV] in Ktid |- *; lia
      | lit_u; change (352880 - 168)%Z with 0x561c8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x561c8%Z 4%nat Htc; rewrite Htc; cbn [ev V2Open.ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
            | eexists; krd_solve HK | atexit_solve ltac:(idtac; krd_solve HK)      (* [comment removed for export] *)
| repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Lemma bytes_at_skipn : forall M (a : Z) (bs : list byte) (k : nat),
  bytes_at M a bs -> bytes_at M (a + Z.of_nat k)%Z (skipn k bs).
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunE ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p-1g0000R0p4p710p8p1000Pp4p70g001@R1p4p710R2p8p1001^p4p70P2p8p1002Lp4p7210P2p8p10038p4p70P2p8g003nR3p4p710P2p8g004Oj1HTg0054j1wTg005Rj1gTg0065j1~Tg006Wj1uTg0077j3qTg0082j3KTP0j25Tg008PR0j10Tg0090R2j23Tg009Lj26Tg009gj2YTP3k30ITg00:>j6sTg00:Zj28Tg00;7j2>Tg00;Qj37j1nTg00;kj3_Tg00<Qk10>Tg00<oj6^Tg00=Xj4\Tg00>?j1TTg00>dj2PTg00?Fj1|Tg00?fj2XTg00@Dj4LTg00@bj1yTg00A@j1xTg00Akj2JTg00BNj1cTg00C3j3QTg00CVk20HTg00D8k20GTg00Ddk30FTg00ECj4rTg00F5R3j21Tg00FRj2aTg00G8R4j1VTg00GXj4Nj3pj2ok10ATg00H4j2Wk10DTg00HVk20ETg00Hmk20@Tg00IPk30?Tg00Iml<lTg00JRj1CTg00K1k10<Tg00KOk20;Tg00L0j3iTg00LYj2hTg00MBk108Tg00M`k205Tg00NCk104Tg00Nek403Tg00OPj8RTg00Omk502TP1j6eTg00PKk307Tg00Pnj2tTg00QJk200Tg00QglBkTg00RMl<dTg00S2j2}Tg00SLj4UTg00T7j7[Tg00T[j3`Tg00UDj2MTg00V0j3ITg00VPk60BTg00W4k70CTg00WXj7{Tg00X<j8zTg00X`R1f0R5'tp=920015p=2g00Y>R6/>5p=;g00Y\R7P7P7P6P6P6g00Z;P0P0P0f6R8g00Z[f5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P0P0P9P:P;P<P=P5M<dp=bP6P6P2f7R>P2P8P9P:P;P<P=P5M<lp=Z1315p==1t51p=<A7651p=BA76;<,6:16=5'}p=?P<g00[BR2g00[aR?P?g00\AR@P6P=g00\aRAP5CUg00]HRBF[p=vA76=5p=OP6P7P6P6P4P:P0P;g00]hP<P=P5M<dp=mP7P7P7P6P6P6g00^UP0P0P0P3g00_5P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00_XR3g00`DR4,M=;I5p>0:A`6<=/M4=I35p=E1M<41M=4=I355I3p>09P=P2P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P2P?P?P@P<P=P2P?P?P@P5PBF[K0Cp=:P6P=g00a0P5CUp=FP=P2P?P?P@P5PBF[p=DP<P2P?P?P@P=P5F{p=]P6P=g00aWP5CUp=SP;P2P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI3=59I3<p>06g00b>R4#HR2#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P1%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|3RV%u3R3P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J62R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00bcR_g00cCR`'>Ra20G5<=7_`dB0F61=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA1RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P0%n6%0=R0/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P18%=8%28RiP8%<8%BiD?%2>P611cNRc,P1%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P1%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00ccRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP3P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20561R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c2,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P1K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP3P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;0AKD=<5q:eWGXM7WKXI6WHo"). Qed.

Section TRunE.
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
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x3c370.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x3c230.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x56270.
  Hypothesis AL_glob : forall a, al_globals a -> (0x76568 <= bv_unsigned a < 0x76918)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x77000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x561cc <= bv_unsigned a < 0x561d0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x77000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x77000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x77000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.


  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V2Open.ENV a0s path.
  Let model2 := model2 tid fs0 stdin0.
  Let sideW := sideW sp0 mem0 lim.
  Let calls := calls data.

  (* [comment removed for export] *)
  Definition pendingP (M : word -> option byte) (k : nat) (w : word) : Prop :=
    rdn RSEGS M (Z_to_bv 64 0x76940) (2 * k) = Some (zero_lines k) /\ bv_unsigned w = (0x76940 + 2 * Z.of_nat k)%Z /\ (k <= 3)%nat.

  (* [comment removed for export] *)
  Lemma pendingP_frame : forall M M' k w,
    pendingP M k w -> (forall a : word, (0x76940 <= bv_unsigned a < bv_unsigned w)%Z -> M' a = M a) -> pendingP M' k w.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunE ()) ["TRunE"] "h02Hah14__x1h24__x2h34__x3h43Hj0h53Hk0h67__arithh74__ffh86__sat3h96__sat4h:6__sat5h;8__varmaph<5__with=1ah>4cstrh?5cstr0h@9heq_callshA1HhB6__sat6hC6__sat7hD4__x4hE1zhF2HBhG2HFhH2HjhI2HkhJ2HwhK1MhL2M'hM1jhN1khO1ohP1whQ1xp&0p;1p;3p;2p;4p;6p;Bp;<p;7p;8g004Oj11Tg0054j1]Tg005Rj1YTg0065j1gTg00dBj3RTg006Wj1aTg00BNj1<Tg00e:j1?Tg00FRj2MTg00JRj1LTg00eXj2ITg00eoj4FTg00fgj1STg00H4j2PTg00;Qj36Tg00glj24Tg008PR0j10Tg00hVR1j2:Tg00F5j29Tg00i3R2j2DTg009LR3j27Tg00PnR4j2=Tg0090R5j22Tg00iMR6j2fTg00iej1lTg00=Xj4ZTg00>?j1XTg00jYj2WTg00kAj2VTg00k^j3UTg00lBj2hTg00m3k205Tg00LYj2TTg00K1k104Tg00KOk203Tg00L0k302Tg00T[j3KTg00UDj2eTg00?Fj1~Tg00V0j3cTg00?fj2QTg00MBj1|Tg00@bj1{Tg00A@j1zTg00M`j2HTg00Akj2GTg00NCj1yTg00mSj3xTg00C3j3_Tg00SLj4NTg00CVj2wTg00;7j2^Tg00D8j2tTg00Ddj3sTg00ECj4rTg00n6j2qTg00n_j3uTg00oHj3vTg00okj2\Tg001@j6[Tg011;j4`Tg011Wj6pTg00:>j6oTg012`j4bTg00QglBnTg00Iml<dTg00@Dj4}Tg00T7j7mTg00W4k700Tg00X<k801Tf0R7#1#1p=E%<7#<p=8%17#1#1#1p=>g00Y>R8f1R9;67p=@1^87p=Cg00Y\R:P:P:P8P8P8g013;P0P0P0P1g013[f5R1f4R;f3R<f2R=P9P7MBnp=kP:P8P6P0P5g014>P1P;P<P=P9P7M<dp=jP:P8P2P0P4g014`P1P;P<P=P9P7M<dp=ig00X`R4/=7p=3P8P=P9P7C}p=AP8P9g00a0P7CNp=BP9g00[BR0g00[aR2P2g00\AR5P7g00]HFmp=5P8P9g00aWP7CNp=JP=P0P2P2P5P9P7K00p=OP<P0P2P2P5P=P9P7L01p=;g00b>R0#1R6#ER>#1R?#ER@#]RA#YRB%]>#YRC#gRD[PD^QBAR<97P3%aCRC#gREg015BRFP;%80#1#8#1#<#E#<#1#<#E#>#?RG,MARHg00ccRI#L#LRJ/I=CF%S=,PC3614A9%?6RK%0=RL':,9G'@%LJRM,D='714A7RN,=GRO14A<,2N'7f6RPP9O1f7RQP9O156D[^=BAR1;<[P7PFPPPH1IJ;CF%S;,PC56E14A;%01,:K,9G'@1D1M'7P314A1%0P,:K,9G'@1DPM14AQR3,2N,7Of:RRP9O1f;RSP9O156D[^=Bf9RTf8RU;RQ[P7%0U,:K,9G,@31DTM14ARR3,2N,7Of=ROP9O1f>RNP9O156D[^=BPFf<RVPH1IJSRWCFRX%SS,PCRC56E%0S,:K,9G,@3R31DSMRS'7PEPFPOPHPWCFRYPFPOPH1IJVRZCF=6E7XOEPEPYPXPFPOPVPWPH1f7ZP8PGf@197L,MARZO1f?RWPZO156DXE8PDPN%09,9GRD,MARZO1PWPZO1P=PZP8PD1=G714AO,27'7XE8p,4data#lRF#Cp,5calls/@FRFeRXPF1IJNRY,f=%0NRE,:KR[,2LR\P=PL%CLPYP[PJPK%CKPNPE%CEEkEjP9CZREP\1DWM%0WRN%<0R[#?RY'=RLPWPN%CNPMPY%CYEiP1CZRNPL%X;RW%0;#3R]fAR^#XR_%0^#3R^%<6R`#<#1#?Ra,WKRb124KRc%3a1VKaRd,24[[Re%3KRfg016TRgAUKa9UW0Ra%3d\g^0fRdp,3sp0,4ARh%??R?'hRi%3h%3?205h?#3[[R?g00_XRj1T8MRM&040-0381T8JRJ60281T8IRI5K85K8g00`DRk'e%~jRl3c%ajRm1Q8;%|8Rn7A;1Q8<Ro7A=?A9n%{8Rp%z8Rq1H84Rr1G80R0'B,5qRs%y2R2Pq1H8KRt1G8>R>5x8Ru,J0,5qRvP2PqP81G86R6g00\a1H8GRw=_8uCN,5qP2Pq%8[#8#8#8#8#8#8#1#E#>#>#>#>#>#>#>#?Ru,H8Rx%1[,G8'B,5qP2A_8w0R0,Bw,5q1J06,5q5OqC;C;C;C;1wq5R5P7P=g00bcR6g00cCR['^1t7==66[dAs849CrR[b7b;b<X18X28X38XD8%37R61:K;Ry,291:K1,9G,@<1=u119G;Rz,=G12z1'7[[[[^18^28^38^D8P7fF#0PhfE,4A%0RP1PQPOp,4SPloROO8b6b8b9b:b?b>b5b4b@14AZPXPFPEP\PNPLPWP]P_P^%?@R@,WKRZ%3@1VK@R1,24[\cRcAUK@9VgX0fR@%31\g^0fRfPbPePaPdPiP?1q8K=u8MAK8JI5K8/ek=cjlPmAAo<n?A<n1Q8=?A<n7A9PpPqPsP2Pq1H8Y,B>,5qP2PqPvP2Pq1G8`,Bx,5qP21Br0,5qAv8tARt,J0,5q5OqC;C;C;C;P5P[b7b;b<X18X28X381=<Y12=y1=u;%3z12z1'7[[[\6^18^28^38P7fH#0Ph%0VPQPUPTPOO7b6b8b9b:bBbCb?b>b5b4b@,\DE[O2C`14AHPXPFPEP\PNPLPWP]P_P^PZPcP@PfPbPePaPdPiP?PlPmPnPp1Brw,5q1Jwt,5q5OqP5P[b7b;b<%3G12G1'7P7b6b8b9b:bBbCb?b>b5b4b@,\GE[WHXM:EpC`PCPPEoP3PSP=P9CbCbWGWIWJP9P7O2n2001000000121000000WAWFP9P7O2n2001000000121000000WAXPBXN:WLWKo"). Qed.

  Lemma zero_lines_length : forall k, length (zero_lines k) = (2 * k)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunE ()) ["TRunE"] "h01kh12Hah24__x1h31xh42IHh53IH0h67__arithh74__ffh86__sat3h96__sat4h:6__sat5h;8__varmaph<5__with=4cstrh>5cstr0h?9heq_callsh@1nhA1yp;1p;2p;3p;4p;7p;6p;Bp;<g004Oj14Tg0054j1GTg005Rj1UTg00fgj1:Tg0000j29Tg00JRR0j10Tg00eXj28Tg00;7j25Tg00iej1RTg00;Qj32j1FTg00e:j1;Tg008PR1j13Tg00hVR2j2<Tg00F5j26Tg00Hmj2YTg00IPj3WTg00=Xj4VTg00>?j1BTg00BNj1ATg00jYj2TTg0090j2@Tg00kAj2STg00k^j3QTg00glj2NTg00lBj2LTg00m3j2KTg00?Fj1JTg006Wj1MTg00?fj2ITg00@bj1OTg00A@j1PTg00M`j2?Tg00Akj2HTg00mSj3ETg00C3j3>Tg00SLj4eTg00T7j7dTg00CVj2cTg00D8j2bTg00Ddj3aTg00ECj4ZTg00Nej4[Tg001@j6\Tg0170j4XTg00QglB]Tg00RMl<^Tg00Iml<_Tg00Pnj2`Tg00Y\R3f1R4f0R532p=7P3P3P3g00Y>R6P6P6g013;P1P1P1P2g013[f5R2f4R7f3R8f2R9P4P5MB]p=DP3P3P6P6P0P1P1P8g017QP9P4P5M<^p==P3P6P5P1P4P9P8P7P2f6f7f8M<_p=Cg00X`R2/`5p=1g00b>R1#4R0#4#4R:#G#UR;%:5'9g00ccR<#0#0R=/85'7R>X0318=<,53P318=4%05#0%09R<,8=R?'7X@3p,4data#RR@,56p,5calls=26@R@eP@18=9R@#0RA#0RB/7?%;0RC%39RD'<RE%;1RF'6RG/6FRH16DFRI,<CRJ526%F3RK%F6RL%34%3552617451Y453WXA3X33RMPBPH165FRHX36RBPAPGPBP@PEP=PC156CRGP9PD156DRAEDRNC=C=P?PJP=PCPGP<PIPBP9PDPAC=EDM9C%:9,9;RA/7@%3ARD=26ERBPKPLPMPAPD156DP@PEPNM9CP4CVPB%B8%38#1%:7,9;R7#B%37#1%A0#A#4#;R0,TC1@2C%101SC0R7,@2[[%1CR8g016TRBAQC04UW1%17\B^18%4:R:#4#4#Gp,3sp0'NR8%;:R:'L%18%1:1K8:#1[[g00_XR:#J%M:1I64%O6%P6R:g00[Bg00[aR8P8g00\AR8P61?6CRB1H61R15E61?6FR75>6=>67g00\aA>6179E6BCeg00]HFd1c:8P5P9g00bcR8g00cCR:'51b59=28:dAa624CZb7b;b<X261<C5/6F/6F1<CH526^26P5f9#3O1b6b8b9b:b>b=b5C[b?%:4,9;P5E\%04R4#:,9;18=4'7eX4>X03P5CXX03o"). Qed.

  (* [comment removed for export] *)
  Definition at_fn1 (k : nat) (buf : word) (cap : Z) : Prop :=
    forall (fxp : FPState) A vm vals R M w,
      length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 5 = tid -> vals_ev vals 6 = buf -> vals_ev vals 7 = w ->
      regs_ok (ENV vals) sr_FN1 R -> know_ok RSEGS (ENV vals) M kn_FN1 -> sideW A vm M buf cap -> pendingP M k w ->
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x17a5c) M (seg_rom RSEGS)) (model2 vm))
               (t_emit (W 1 (zero_lines k)) (t_exit (exit_code 0) fs0)).

  Theorem fn1_tail : forall k buf cap, at_fn1 k buf cap.
  Proof.
    intros k buf cap fxp A vm vals R M w HL P0 P5 P6 P7 HR HK HS (HPb & HPw & Hk3).
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap HS) as (Hb0 & Hb1 & Hal & Hbb).
    destruct HS as (HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0).
    unfold model2, V2ReadLoop.model2.
    run_blk_keep scr0 40%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    destruct fn1_itin as (_ & _ & VLK1 & KNF & _ & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (F10 : getr Rc 10 = buf) by (regv HR (10 : reg); cbn [edenot ev ENV V2Open.ENV]; exact P6);
      assert (F1 : getr Rc 1 = Z_to_bv 64 0x17a64) by (regv HR (1 : reg); reflexivity);
      assert (F4 : getr Rc 4 = Z_to_bv 64 0x56270) by (regv HR (4 : reg); reflexivity);
      assert (F2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 128))
        by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V2Open.ENV];
            rewrite P0; first [reflexivity | f_equal; lia])
    end.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (EQcfg : mkst Rc (Z_to_bv 64 0x3c230) M (seg_rom RSEGS) = mkst Rc al_free_pc M al_rom)
        by (rewrite AL_free, AL_rom; reflexivity); rewrite EQcfg; clear EQcfg end.
    rewrite <- AL_segs.
    set (md := mkModelC V2Open.fds0 vm stdin0 fs0 None (Some tid) None).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (ai_free fxp A M md Rc buf (Z_to_bv 64 0x17a64) sp0 [a0s; path] envv _ HI) end.
    - constructor; reflexivity.
    - change (m_kernel md) with a_kernel. change (m_vmmaps md) with vm.
      exact (vm_resv_incl _ _ vm Hres Hisp).
    - apply AL_env. exact HE.
    - exact F10.
    - right. exists cap. exact Hl.
    - exact F1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite F4. symmetry. exact AL_tp.
    - rewrite F2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, F2, u_small by lia. lia.
    - rewrite F2, u_small by lia. lia.
    - intros a Ha. rewrite F2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V2Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - intros A'' m'' vm'' regs'' HI'' Hcs'' Hlbuf'' Hlq'' Hfr'' Hlm'' Hgr'' Hvl'' Htop'' Hisp'' Hres'' Hmb'' Hvlb''.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop''. rewrite Htop in Htop''.
      unfold md. rewrite with_vmmaps_C.
      assert (HP'' : pendingP m'' k w).
      { apply (pendingP_frame M m'' k w (conj HPb (conj HPw Hk3))). intros a Ha. apply Hfr''.
        - intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm _ HI Htop Ho) as [Hg|Hg]; lia.
        - intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A'' m'' vm'' _ HI'' Htop'' Ho) as [Hg|Hg]; lia.
        - intros He. apply AL_errno in He. lia.
        - rewrite F2, !u_small by lia. unfold ALLOC_STACK. lia. }
      destruct HP'' as (HPb'' & _ & _).
      set (vals2 := vals ++ junk_vals regs'').
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG a0s path vals sr Rc regs'' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs'') as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      clear HR. rename HR2 into HR.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_after_allocG sp0 a0s path Hvsp data AL_glob AL_grant AL_errno AL_hi A A'' vals M m'' vm vm'' regs'' kn
                      ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK1) HK HI Htop HI'' Htop'') as HK2 end.
      specialize (HK2 ltac:(intros a H1 H2 H3 H4; apply Hfr''; try assumption; rewrite F2, u_small by lia; exact H4)
                      ltac:(intros a Ha; destruct (Hgr'' a Ha) as [Ho|Hs]; [right; left; exact Ho | right; right; exact Hs])).
      lazymatch type of HK2 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK2 end.
      fold vals2 in HK2. clear HK. rename HK2 into HK.
      assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q7 : vals_ev vals2 7 = w) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      run_blk_keep scr0 72%nat.
      assert (HPb3 : rdn RSEGS M0 (Z_to_bv 64 0x76940) (2 * k) = Some (zero_lines k)).
      { rewrite <- HPb''. rewrite EQM. apply rdn_agree. intros j Hj. rewrite u_small by lia.
        lazymatch goal with |- mem_denot ?E _ ?log _ = _ =>
          rewrite (mem_denot_out_win E m'' log 0); [reflexivity | vm_compute; reflexivity | cbn [ev ENV V2Open.ENV]; rewrite Q0; lia
                                                  | cbn [ev ENV V2Open.ENV]; rewrite Q0, u_small by lia; unfold WIN; lia] end. }
      clear EQM.
      assert (Hh : m_halted (mkModelC V2Open.fds0 vm'' stdin0 fs0 None (Some tid) None) = None) by reflexivity.
      assert (Hlazy : m_vm_lazy (mkModelC V2Open.fds0 vm'' stdin0 fs0 None (Some tid) None) = []) by reflexivity.
      lazymatch type of HK with know_ok ?segs ?E ?Mf ?kn =>
      lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
        apply (rz_conseq segs _ (t_emit (W 1 (zero_lines k)) (t_exit (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) (m_fs model))));
        [ | cbn [m_fs]; replace (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) with (exit_code 0) by (apply bv_eq; reflexivity); apply t_eq_refl ];
        apply ref_exit_Z;
        pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl) as Ktid;
        cbn [kentry_ok edenot ev V2Open.ENV] in Ktid;
        pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 7)) in exact i) _ HK eq_refl) as Kw;
        cbn [kentry_ok edenot ev V2Open.ENV] in Kw; rewrite Q7 in Kw;
        lazymatch type of HR with regs_ok _ _ ?Rc =>
        exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x56270), (bv_unsigned (ev E 5)), (Z_to_bv 64 0), (Z_to_bv 64 0);
        split; [|split; [exact Hh|split; [exact Hlazy|]]]
        end end end.
      + constructor.
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV V2Open.ENV].
          rewrite Q0. first [reflexivity | f_equal; lia].
        * regv HR (4 : reg). reflexivity.
        * regv HR (10 : reg). reflexivity.
        * rewrite u_small by lia. lia.
        * rewrite u_small by lia. lia.
        * rewrite u_small by lia.
          lazymatch type of HK with know_ok ?segs ?E _ ?kn =>
          pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-192) 144) in exact i)
                        _ _ _ (-192) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end.
          unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V2Open.ENV] in Hst. rewrite Q0 in Hst.
          replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + (-192))%Z by lia. exact Hst.
        * lit_u. cbn [ev ENV V2Open.ENV] in Ktid |- *. lia.
        * lit_u. cbn [ev ENV V2Open.ENV] in Ktid |- *. lia.
        * cbn [ev ENV V2Open.ENV] in Ktid |- *. lia.
        * lit_u. change (352880 - 168)%Z with 0x561c8%Z.
          krd HK 0x561c8%Z 4%nat Htc. rewrite Htc. cbn [ev ENV V2Open.ENV] in Ktid |- *.
          rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
          rewrite Z_to_bv_bv_unsigned. reflexivity.
        * krd_solve HK. * krd_solve HK. * krd_solve HK. * krd_solve HK. * krd_solve HK. * krd_solve HK. * krd_solve HK.
        * eexists; krd_solve HK.
        * atexit_solve ltac:(idtac; krd_solve HK).
        * repeat split; krd_solve HK.
        * repeat split; krd_solve HK.
      + destruct k as [|k'].
        *
          left. split; [reflexivity|]. exists (Z_to_bv 64 0x76940), (Z_to_bv 64 0).
          cbn [Z.of_nat Z.mul Z.add] in HPw.
          assert (Hw : w = Z_to_bv 64 0x76940) by (apply bv_eq; rewrite HPw; reflexivity).
          split; [krd_solve HK|]. split.
          { krd HK (0x46020 + 40)%Z 8%nat Hwp. rewrite Hwp. cbn [ev ENV V2Open.ENV]. rewrite Q7, Hw. reflexivity. }
          split; [krd_solve HK|]. split; krd_solve HK.
        * right. exists 0x76940%Z, (bv_unsigned w).
          krd HK (0x46020 + 88)%Z 8%nat Hbufp. krd HK (0x46020 + 96)%Z 8%nat Hbsz.
          lazymatch type of Hbufp with _ = Some (word_to_le_bytes 8 ?bp) =>
          lazymatch type of Hbsz with _ = Some (word_to_le_bytes 8 ?bs) =>
            exists bp, bs, (Z_to_bv 64 0), (canary_w a_draw) end end.
          split; [| split; [reflexivity | exact a_reader]].
          constructor.
          -- krd_solve HK.
          -- krd HK (0x46020 + 40)%Z 8%nat Hwp. rewrite Hwp. cbn [ev ENV V2Open.ENV]. rewrite Q7, Z_to_bv_bv_unsigned. reflexivity.
          -- krd_solve HK.
          -- krd_solve HK.
          -- exact Hbufp.
          -- exact Hbsz.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- lia.
          -- rewrite zero_lines_length. lia.
          -- rewrite zero_lines_length. lia.
          -- rewrite zero_lines_length. exact HPb3.
          -- split; [krd_solve HK|].
             lazymatch type of HK with know_ok ?segs ?E ?Mf ?kn =>
               pose proof (kblob_rdn segs E Mf kn (ELit 0) 0x764d8 (ELit 8) 2%nat HK ltac:(vm_compute; reflexivity)) as Hcan end.
             cbn [eb ENV V2Open.ENV blobs_ev blobs0 nth length] in Hcan. rewrite adenot_lit0 in Hcan by lia.
             rewrite guard_bytes_w in Hcan. cbn [length word_to_le_bytes] in Hcan. exact Hcan.
  Qed.
End TRunE.
