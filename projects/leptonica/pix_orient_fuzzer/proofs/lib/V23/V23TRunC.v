(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of fe_tail and tl1_loop, made over the old 8 MiB launch stack window, replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped, with one computed premise added at the fz_call step for this unit's A_MORPH_BC coverage premise). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibKnowXfer LibTail SymCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib LibWritevG.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib Frame.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Room.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23ExitBase V23StdioDefs V23Exit V23Startup V23StartupDefs V23StartupFacts V23MainEntry V23LibStdioCall V23OpenFail_defs V23OpenFail_tail V23OpenFail_tail2 V23Open_defs V23Open V23Oom_defs V23Oom V23MemPreds V23Malloc65536 V23DirRead_defs V23MemcpyBase V23Memcpy V23ReadLoop_defs V23ReadLoop V23Grow V23Hdr_defs V23Hdr V23FuzzIface V23TRun_defs V23TRun V23TRunE V23TRunL V23PrintfBufBase V23PrintfBuf.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac FPSteps.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23TRunC () := "C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3V23;V23MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib3V237V23TRun9calls_rngC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib3V238V23TRunE>pendingP_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V238V23TRunE8pendingPC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC69OSSVerify5KrLib6Common9CliDriver4Spec:zero_linesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes7nat_indC59OSSVerify5KrLib3V237V23TRun5callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun6paylenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun1LC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib6Common9CliDriver:LibWritevG<bv_add_ZformC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC59OSSVerify5KrLib6Common7SeqExec7rdn_appC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrImgKTgt_pix_orient_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~____________________C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunC6slotsEC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr7cfg_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr6hdr_b2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun5sideWC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3V237V23TRun:bufW_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC59OSSVerify5KrLib3V23>V23Malloc655366env_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3V237V23TRun7payloadC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_free_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun=ownedA_rangeTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC59OSSVerify5KrLib3V237V23TRun=env_ok_allocTC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23Open3ENVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs9kn_acallTC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7fn1_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3V237V23TRunAknow_after_allocTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr6b1_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr6hdr_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun7sgn_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3lebC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3V23;V23ReadLoop;vals_ev_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V238V23TRunE8fn1_tailC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun;log_win_wdlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun;sideW_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23ReadLoop6in_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer2rvC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer<regs_ok_xferC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase7ai_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunC5at_feC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4emapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXferDknow_ok_xfer_entailsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23Open4fds0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs5sr_FEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs5kn_FEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6sr_FN1C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3V23@V23OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6STOPSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6kn_FN1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7fe_kn1iC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib6Common8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib3V23<V23FuzzIface7A_EMPTYC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3V23?V23MallocLayout4LU16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23MallocLayout6LU17okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7fe_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7fe_rvlpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6p_sr3eC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs5p_kn3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7fe_rvltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8tl1_sr3eC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl1_kn3C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6fe_r2nC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C59OSSVerify5KrLib3V23<V23TRun_defs6fe_r2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl1_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6tl_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8tl1_sr2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl_sr2iC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunC6at_tl1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun5roomTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr6slotsRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun<paylen_factsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V238V23TRunL:incb_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun5sideTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun5copyPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8kn_fcallC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23ReadLoop6model2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb6a_drawC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23>V23StartupDefs8canary_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun6stk_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;is_kimg_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC59OSSVerify5KrLib3V238V23TRunL;kimg_clearLC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC69OSSVerify5KrLib6Common9CliDriver8SymDrive:kblob_findC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9kblob_rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23>V23StartupDefs;guard_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23StartupFacts=guard_bytes_wC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3V23@V23PrintfBufBase3pfH01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3V23@V23PrintfBufBase3pfH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23PrintfBuf@printf0_bufferedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame6in_rngC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geC59OSSVerify5KrLib3V237V23TRun;sideW_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23>V23Malloc65536:live_whereC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunC=pendingP_snocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib3V23;V23ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3V23;V23ReadLoop:alu_add_wZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun;kword_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunC9addiw_decC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib6Common9CliDriver6SymRun<krange_introC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunC7fe_tailC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V238V23TRunL7fz_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame9frame_modC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6kn_TL1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl1_sr2C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204c59OSSVerify5KrLib3V238V23TRunC3PFUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8tl1_kn3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs5sr_TLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8tl1_kn2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8tl1_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8tl1_rvl0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6p_sr3lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6tl1_r1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl1_kn1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6tl1_r2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl1_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl1_r3lC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C59OSSVerify5KrLib3V23<V23TRun_defs7tl1_r3eC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl1_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8tl1_sr3lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23PrintfBufBase5PF_FRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail@callee_saved_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~".
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
      as Ktid; cbn [kentry_ok edenot ev V23Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x123d08), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V23Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev V23Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V23Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V23Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V23Open.ENV] in Ktid |- *; lia
      | cbn [ev V23Open.ENV] in Ktid |- *; lia
      | lit_u; change (1195272 - 168)%Z with 0x123c60%Z;
        let Htc := fresh "Htc" in
        krd HK 0x123c60%Z 4%nat Htc; rewrite Htc; cbn [ev V23Open.ENV] in Ktid |- *;
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
ltac2:(KReplay.run1 (kr_t_V23TRunC ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p-1g0000R0p4p710p8p1000Pp4p70g001@R1p4p710R2p8p1001^p4p70P2p8p1002Lp4p7210P2p8p10038p4p70P2p8g003nR3p4p710P2p8g004Oj1HTg0054j1wTg005Rj1gTg0065j1~Tg006Wj1uTg0077j3qTg0084j3KTP0j25Tg008RR0j10Tg0092R2j23Tg009Nj26Tg009ij2YTP3k30ITg00:@j6sTg00:\j28Tg00;9j2>Tg00;Sj37j1nTg00;mj3_Tg00<Sk10>Tg00=1j6^Tg00=Zj4\Tg00>Aj1TTg00>fj2PTg00?Hj1|Tg00?hj2XTg00@Fj4LTg00@dj1yTg00ABj1xTg00Amj2JTg00BPj1cTg00C5j3QTg00CXk20HTg00D:k20GTg00Dfk30FTg00EEj4rTg00F7R3j21Tg00FTj2aTg00G:R4j1VTg00GZj4Nj3pj2ok10ATg00H6j2Wk10DTg00HXk20ETg00Hok20@Tg00IRk30?Tg00Iol<lTg00JTj1CTg00K3k10<Tg00KQk20;Tg00L2j3iTg00L[j2hTg00MDk108Tg00Mbk205Tg00NEk104Tg00Ngk403Tg00ORj8RTg00Ook502TP1j6eTg00PMk307Tg00Q0j2tTg00QLk200Tg00QilBkTg00ROl<dTg00S4j2}Tg00SNj4UTg00T9j7[Tg00T]j3`Tg00UFj2MTg00V2j3ITg00VRk60BTg00W6k70CTg00WZj7{Tg00X>j8zTg00XbR1f0R5'tp=920015p=2g00Y@R6/>5p=;g00Y^R7P7P7P6P6P6g00Z=P0P0P0f6R8g00Z]f5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P0P0P9P:P;P<P=P5M<dp=bP6P6P2f7R>P2P8P9P:P;P<P=P5M<lp=Z1315p==1t51p=<A7651p=BA76;<,6:16=5'}p=?P<g00[DR2g00[cR?P?g00\CR@P6P=g00\cRAP5CUg00]JRBF[p=vA76=5p=OP6P7P6P6P4P:P0P;g00]jP<P=P5M<dp=mP7P7P7P6P6P6g00^WP0P0P0P3g00_7P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00_ZR3g00`FR4,M=;I5p>0:A`6<=/M4=I35p=E1M<41M=4=I355I3p>09P=P2P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P2P?P?P@P<P=P2P?P?P@P5PBF[K0Cp=:P6P=g00a2P5CUp=FP=P2P?P?P@P5PBF[p=DP<P2P?P?P@P=P5F{p=]P6P=g00aYP5CUp=SP;P2P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI3=59I3<p>06g00b@R4#HR2#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P1%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|3RV%u3R3P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J62R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00beR_g00cER`'>Ra20G5<=7_`dB0F61=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA1RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P0%n6%0=R0/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P18%=8%28RiP8%<8%BiD?%2>P611cNRc,P1%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P1%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00ceRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP3P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20561R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c2,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P1K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP3P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;0AKD=<5q:eWGXM7WKXI6WHo"). Qed.

(* [comment removed for export] *)
Lemma addiw_dec : forall r, (1 <= r <= 4)%Z ->
  (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 r)) (low32 (Z_to_bv 64 (-1)))) : word) = Z_to_bv 64 (r - 1).
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRunC ()) [] "h01Hh12Hrh24__x1h32b1h42b2h51nh61rh71Ch87__arithh94__ffh:8__varmaph;5__witp;1p;2p;4p;7p;8p;3g00dDj1?Tg00Q0j24Tg004Oj18Tg009NR0j2:Tg00?Hj1[Tg006Wj1UTg00?hj2PTg00@dj1MTg00ABj1ITg00Mbj2<Tg00Amj2GTg00SNj4@Tg00W6j7ZTg00NEj1VTg00BPj1TTg00X>j8STg00CXj2OTg00;9j2;Tg00D:j2NTg00;Sj32Tg00Dfj3LTg00EEj4KTg0054j1CTg005Rj17Tg00K3j1HTg00dbj21Tg00eLj3FTg001@j7=Tg00T9j7QTg00WZj7ETg00S4R1j2RTg00FTj2BTg00f0j1DTg00fXj3YTg00g@j3XTg00:\j2WTf1R2g00[DR3g00[cR4P4g00\CR5f0R6g00]JFQp=9g00Y@R7P2g00\cP6C@p=>f2R8P3P4P4P5P2P6FEp=AA2726p=0A2782/R6p=31B26#Dp=Jf4R9f3R:g00gk1B82#D;Y63Xp=61W26,B8p=5g00b@R;#?R</46%8;R=#8R>#?R?,46':R@g00_ZRA#[%UA1P72%M7%I7RAP3P4P4P5PAP3P4P4P5P71<7<R3g00a2RB1G7;RCC@,9AP7PCPB1<7?RBC@,9AFZ%V41>C3,9A%?=R=,<7,>C,9A%T;#?R3,<7,>C,9A1>CB,9A5AA5AA5AAGS1OA5P6P8g00beRAg00cER5';1N68=2A5dg00XbR5=L72CKb9b:b;X27102?9323932=932<RA\@^27P6P8P2O2b8PAP1108<108?9383938=%8>#8#8R>#8#CRA#7RB%C>R>PAPAP:%H;,JAR;D6A5A:<32P610:<P7P<P>PAPAP2P;D6A5A2<52B^1@X67R@14<<14<?RC':g00hWR4%76RD%72REP0%78?22611:811:2'0R0[11821186'0%7:?282[RF%79?2:8\0AF826P6n2001000000120000000W4W3W5R8PF^4E^3D^54R4P6PAP>PAPAP<P;D6RDA5A<<RE1;7511AD11AE'0dO4b0W1P9P6P:F=W0P6O110:?93:393:=P1109=109?9393P>PAPAf5R9P;D6A5A9<52BP6109=P7P=P@14<=14=?':P8P4P6PAP>PAPAP=P;D6R:A5A=<RE1;7<11A:11AE'0dO4b0W1f6REP6P9F=W0P6O1109?9393P110E310E?P>PAPAf7REP;D6A5AE<52BP610E3P7P3P@14<3143?':P8P4P6PAP>PAPAP3P;D6RBA5A3<R11;7=11AB11A1'0dO4b0W1f8R1P6PEF=W0P6O110E?P7P?P@14??,:CP8P4P6PAP>PAPAP?P;D6R;A5A?<R?1;7311A;11A?'0dO4b0W1P1P6PEF=W0P6O1n200100000021100011000W0P6O1n200100000021100011000W0P6O1n200100000021100011000b7W1X67o"). Qed.

Section TRunC.
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
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x10e958.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x10e818.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x1381d0.
  Hypothesis AL_glob : forall a, al_globals a -> (0x1584d0 <= bv_unsigned a < 0x158880)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x13812c <= bv_unsigned a < 0x138130)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x159000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.




  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V23Open.ENV a0s path.
  Let model2 := model2 tid fs0 stdin0.
  Let sideW := sideW sp0 mem0 lim.
  Let sideT := sideT sp0 mem0 lim data.
  Let copyP := copyP sp0 data.
  Let slotsR := slotsR sp0 a0s path envv tid data.
  Let slotsL := slotsL sp0 a0s path envv tid data.
  Let pendingP := pendingP.
  Let L := L data.
  Let cfg := cfg data.
  Let paylen := paylen data.
  Let payload := payload data.
  Let calls := calls data.
  Let counting := counting data.
  Let at_fn1 := at_fn1 sp0 a0s path tid mem0 fs0 stdin0 lim.

  Lemma calls_rngC : (1 <= calls <= 4)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRunC ()) ["TRunC"] "p;2g00i5j20Tp,3sp0p,4data'0o"). Qed.

  (* [comment removed for export] *)
  Lemma pendingP_snoc : forall M M' k (w w' : word),
    pendingP M k w -> (forall a : word, (0x1588b8 <= bv_unsigned a < bv_unsigned w)%Z -> M' a = M a) ->
    rdn RSEGS M' (Z_to_bv 64 (bv_unsigned w)) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a] ->
    bv_unsigned w' = (bv_unsigned w + 2)%Z -> (S k <= 3)%nat ->
    pendingP M' (S k) w'.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRunC ()) ["TRunC"] "h04__x1h11xh24Hk'0h33Hk0h47__arithh54__ffh66__sat3h76__sat4h86__sat5h98__varmaph:5__with;4cstrh<5heq_Lh=9heq_callsh>7heq_cfgh?:heq_paylenh@1zhA1HhB2HahC1yhD1khE1nhF6__sat6hG6__sat7hH4__x2hI1bhJ1lhK1mhL3APPhM2HBhN2HFhO2HPhP2HkhQ3Hk'hR3HrdhS2HwhT3Hw'hU2IHhV1MhW2M'hX1ahY1whZ2w'p%0p&0p;1p;2p;3p;9p;6p;4p;<p;8p;Bp;7g004Oj15Tg0054j1mTg005Rj1lTg0065j1vTg00BPj1CTg00dDj1@Tg00dbj29Tg00Q0R0j2=Tg0092S00j2BTg009NR1j2GTg00;Sj31j1xTg006Wj1yTg00FTj2?k10=Tg00JTR2j13Tg00?Hj1rTg00V2j3:Tg00H6j2MTg00ioR3j2;Tg00jIm90?Tg00kIk30<Tg00lCj2<Tg00lZj17Tg00m_j3HTg00;9j2LTg00:@j6[Tg00n<k402Tg00n]k101Tg00oSj1|Tg010Jj1{Tg011>j1zTg00HXj2ZTg008RR4j12Tg0120R5j2>Tg00F7R6j20Tg00Hok20NTg00IRk30MTg00Iol<OTg00=Zj4KTg00>Aj1_Tg012Mj2uTg0135j2tTg013Rj3sTg0146k20GTg014gk20FTg00?hj2qTg00@dk10ETg00ABk10DTg00Mbj2NTg00Amj2oTg015Gj3nTg00C5j3TTg00CXk20BTg00D:k20ATg00Dfk30@Tg00EEk40>Tg00Ngj4WTg00<Sj1bTg001@j6ITg00ORk80;Tg00=1k609Tg015jk207Tg00L[j2\Tg016Sk306Tg00T]j3fTg00UFj2eTg017<k205Tg00MDk104Tg00@Fj4gTg00NEk103Tg017hk308Tg00SNj4VTg018Kj2kTg019[j3^Tg01:@k200Tg01;Mj1wTg01<Hl9~Tg01=Cj4pTg01=^j4}Tg00QilBUTg00ROl<cTg00T9k70HTg01>Vk40ITg00W6k70JTg00X>k80KTf0R7#5#5p=Q%C7#Cp=Dg01?9R8f2R9f1R:P7C}p=J%57#5#5#5p=Fg00Y@R;10:7719p=E%27,>:p=S1L;7p=4A1;:7p=8g00Y^R<P<P<P;P;P;g01@`P4P4P4P5g01A@f5R=f4R>f3R?P9P:P7MBUp=`P<P<P<P;P;P;g00^WP4P4P4P6g00_7P=P>P?P9P:P7MBUp>0LP<P<P;P;P2P4P4P?g01AcP9P:P7M<cp=XP<P;P3P4P0g01BGP=P>P?P9P:P7M<Op=Pg00XbR3/=7p=6P;P:g00\cP7CVp=]P:g00[DR2g00[cR@P@g00\CRAP7g00]JK0Hp=A1>:7,09p=YP;P;g01BiP7H0Ip=jP<P;P;P;P4P4P=P>P?P9P:P7M<cp=iP;P;P;P;P;P;P6P7P:P9P6P?P>P=f6R6f7RBf8RCf9RDMBUp=hP;P;P0P=P0P>P3P3P?P9P:P7M<Op>0:P;P:g00a2P7CVp=RP9P2P@P@PAP:P7K0Jp=dP?P2P@P@PAP9P:P7L0Kp=aP;P;P;P;P;P;P5P7P:P9P5P?P>P=P6PBPCPDMBUp>0Cg00b@R5#5R2#QR0#5RE#QS01#mRF#lRG%m0R0#lRH#vRI[PI^1Gp,8pendingPRJP>P9P:O3%55#C#5#D#5#Q#C#5#Q#C#5#C#D#5#Q#@RK19F7RL'=19F?RM,BL'GP6P:O1PBP:O151I[^XG%yHRI#vRL1?FMg00ceRN#3#3RO5J=%C5RP#F#@,?0RQ%C2RR#5#@,?0R0%rH5:H5:HRS,MIS023119F>%@2R25EM%36%3ORM';p,3sp0RTp,4Hvspp,4dataRUPDPCPBP6P>P?N90?B0<CB6P11?FKRV1<OC5JD%7C,MI51L19FB1S2C7EK1;CM'GPJf:RC%3DPBO3P7f;RW1<OC7JV%7C,MI51L19FC1S2W7EK1;WM'GP119FWf<R1,S27EK1;1MPJf>RJf=R1#3PWO3P719F11S2J7EKf?S03/;MfAR1f@RW#3RX,<O7JV%7XRY,MI51L19FJS041S2X7EKS051;XMS06'G%37#7%77=HHS51IRXXD<%7N=HHS,LIPI%3:RZ#7R[%799:H09:HQ9:H09:HQA:H079:HQ51IXJIA:H0[9:HQ,LI%7:=HHSP7E[%3Z#7AHH[S51IeXUXXD<PWH02%7W=HHS91IYPI%71=HHSfCRYfBRX#3,<OS077JV1MI751LXJI&01UR[#4p,5calls/8[R[eRZP[%|URQ#4p,6paylen/8QRQeR0PQ%{UR\#4p,3cfg/8\R\eR]P\%zURU#4p,1L/8URUeR^PUfER_,<OR`/ZORa%3_Rb,<ORc51<%2_Rd,>2Re/02Rf%@5Rg,0dS08,>2Rh'8P<P;%x<P4%x;R4%2:%27Ri'8A1<:720N:740MXC<X1<PaPfP`PePOP2%42ReP_Pd%4dR`E`POP2PeJ0LPcPhPOP2PePbQ08107gRhX1;RcP_PdP`CXS09E`M<O1;_M%@PRf,=dRaP_PdP`PMPf%4fR`EPP=CKPafFRa#3R=/;M%2aRj/0g/=fRkP=PcPjO1PcPaPj%4jR=CXPMPfP`EPQ03CKPkfGRk#_%2kRl#6%CR#5#@Rm,u2Rn1B32S0:%6m1t2mRo,B3[[Rp%62Rqg01CMRrAs2m:UWBRm%6o\r^BqRo19FTRT%@ERE+0GRs%6T%6E20FTE#6[[REg00_ZRt#rRu%ytRv1q;:S0;&0E;Rw&0D;Rx1N;2Ry1o;5R55n;Rz=T;y1N;g9T;5S0<9n;yS0=']'A20BxARAP7P9g00beR{g00cER|'L20A79=1{|dB0@;3:H0>R|b5b9b:X0;1>27R{/021>2hS0>'8^0;P7fL#2O1b4b6b7b8b;b2b3CWb<b>b?b=1<O1/ZO%31Rh,<O51<P<1<OXR}/ZOfDR~?JV7%7Y=HHS,MI51LXE<P8PYP}POPV%7XPSPBPG19FVS0?%2}RS,?FR8,9FS0@'0,?F19FX,?FRI=1G7XIGP;PK1<OYS0A#2RY,?F,9F,07,?F91GIX@;P;PS10K7,?F91GIX@;P;PG&0=FRHPH19F1S0B10KSPG\;/LHP;%2X9YK2AE7KYX@;PZP[P0PQP]P\P^PU1>2jRY,0KRX1<OaS0C#2RH,0KS0D'818XXP;P;P4P7X1;R1P418:7#bXC;X1;S0EPXPX%4XQ0DPXP1P1P110:7#j#4XK;XE;S0DPKPK%4KS0FPHPYP1P1%4iX1<S0GQ0CPYPOP2PePaPjP=E`EiS0CM:hM<O1;aM1=jfS0HPaPjP=PMPfP`EPP6CKS0IQ0H%3kR=/;M10lg/=fRiP=PcPlO1PcPkPl%4lCXPMPfP`EPPWCKS0JPifHRl#_S0K%2l#6S0LPnPpPmPoPsPEPuPvQ0;Pw1N;KRl=T;zRk/]k,AxPAP|b5b9b:X0;10K{R{/8{^0;P7fM#2O1b4b6b7b8b;b2b3CWb<b>b?b=Q0BP?EIL0;Q0@PZP[P0PQP]P\P^PU%6HS0@Q01#@R=,t2RX,BHS01'G%6YS0M1BYXS0N'GQ0@Q01Q0MQ0NP11=:7#bXC;X1;1L;3PHPYQ0CJ0:P;P;Q00P1Q001B:7#bXC;X1;PHPYQ0CPXPX%4XM<OJ09Q0IQ0HQ0JPiQ0KQ0L1u2=RYQ0:%6=1B3X[[RHAs2=:VrXBqR=%6X\r^BqRqPnPpPmPoPsPE207;21\;O606;1\;NRN5f;g00`FRr'e%3M,\;9f;N/er-05N=:tu5:tPvP;&04;RtP:P;1q;9P9PtCgCgPwPx1N;3R3/R5,Ax&03@R@PxQ0<1N;f'R,AxP@Px%DP#D#D#D#D#D#D#5#Q#F#F#F#F#F#F#F#@RP,N;1o;R'R,AxP@1R3z,AxP;Pzg00aYRzB08;yFR@CV,Ax5dxCaCaCaPAP|b5b9b:X0;XH;%6710:g/=f1=P?1>2?R?#61B?X'G[[[^0;^H;P7PTfO#2P6PBp,4SPloO5b4b6b7b8bFbGb;b2b3CWb<b>b?b=,kSEIQ0?PZP[P0PQP]P\P^PUQ0IQ0HQ0JPiQ0KQ0LPYPHP=PqPnPpPmPoPsPEPuPvPtPw1R3l,AxP;PlPzP@CV,Ax5dxPAP|b5b9b:%6K1BKX'GP7b4b6b7b8bFbGb;b2b3b<b>b?b=,kKEIA^FV8200V8EIQ0B,?FR8%w}9^FVR}51GeP8PGeP}PGe51GPGPIAJ_7OQ0251LXIGPJQ0A#w9^FVP7E[bAM9~Q07P7E[bA%7hP7EIbLQ05Q06P;Q03,9FRF/02%2h9YK2Rh,87X@;P;%2W9YK21072/8hX@;PZP[P0PQP]P\P^PU%2~RU9YK2/02R^%3~R\#2R],>2RQ,0KR0'810UgRg,>2R[,0KRZ,8^P;P;P4P1P4Q0EP^P^%4^P0PZP1P1P1Q0DPKPKQ0FPQP[P1P1P11>:7#j#4XK;XE;P2P2PeP]PgP1P1Q0GP\PgPcP~PU%4URgCXEiN:0CM:hM<O1;~M1=UfR\P~PUPgPMPfP`EPP>CKP\1;bMQ08/=fR\PbPcPdO1Q09PMPfP`EPPJCKP\%_a%6jPnPpPmPoPsPEPuPvQ0;PwAT;kyQ0=9T;l'],AxPAP|b5b9b:X0;10{2Q0>7EK^0;P7fK#2O1b4b6b7b8b;b2b3CWb<b>b?b=PFP:EIQ04PCEIPDCpCpWPWSP:P7O2n2001000000121000000WAWMP:P7O2n2001000000121000000bAWQWTWRWNWOXZGXYGXD<WWWVo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition slotsE (vals : list word) (buf aligned owned : word) : Prop :=
    slotsR vals buf /\ vals_ev vals 14 = aligned /\ vals_ev vals 15 = owned.

  Definition at_fe (k : nat) (buf : word) (cap : Z) : Prop :=
    forall (fxp : FPState) A vm vals R M aligned owned w,
      length vals = 50%nat -> slotsE vals buf aligned owned -> vals_ev vals 18 = w ->
      regs_ok (ENV vals) sr_FE R -> know_ok RSEGS (ENV vals) M kn_FE ->
      sideT A vm M buf cap owned -> copyP M aligned owned -> pendingP M k w -> (0 <= paylen)%Z -> (L < cap)%Z ->
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x10e818) M (seg_rom RSEGS)) (model2 vm))
               (t_emit (W 1 (zero_lines k)) (t_exit (exit_code 0) fs0)).

  Theorem fe_tail : forall k buf cap, at_fe k buf cap.
  Proof.
    intros k buf cap fxp A vm vals R M aligned owned w HL SL P18 HR HK HS HC HP Hpl0 HcapL. pose proof (cfg_rng sp0 data) as Hcfr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P14 & P15).
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
    destruct HS as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    destruct HC as [HC1 HC0].
    unfold model2, V23ReadLoop.model2.
    assert (F10 : getr R 10 = owned) by (regv HR (10 : reg); cbn [edenot ev ENV V23Open.ENV]; exact P15).
    assert (F1 : getr R 1 = Z_to_bv 64 0x63508) by (regv HR (1 : reg); reflexivity).
    assert (F4 : getr R 4 = Z_to_bv 64 0x1381d0) by (regv HR (4 : reg); reflexivity).
    assert (F2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V23Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    assert (EQcfg : mkst R (Z_to_bv 64 0x10e818) M (seg_rom RSEGS) = mkst R al_free_pc M al_rom) by (rewrite AL_free, AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC V23Open.fds0 vm stdin0 fs0 None (Some tid) None).
    eapply (ai_free fxp A M md R owned (Z_to_bv 64 0x63508) sp0 [a0s; path] envv _ HI).
    - constructor; reflexivity.
    - change (m_kernel md) with a_kernel. change (m_vmmaps md) with vm.
      exact (vm_resv_incl _ _ vm Hres Hisp).
    - apply AL_env. exact HE.
    - exact F10.
    - destruct (Z.eq_dec paylen 0) as [Hp0|Hp0].
      + left. exact (proj1 (HC0 Hp0)).
      + right. exists paylen. apply Hlo'. unfold paylen in *. lia.
    - exact F1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite F4. symmetry. exact AL_tp.
    - rewrite F2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 208)%Z with (bv_unsigned sp0 + (-13) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, F2, u_small by lia. lia.
    - rewrite F2, u_small by lia. lia.
    - intros a Ha. rewrite F2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V23Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - intros A'' m'' vm'' regs'' HI'' Hcs'' Hlo'' Hlq'' Hfr'' Hlm'' Hgr'' Hvl'' Htop'' Hisp'' Hres'' Hmb'' Hvlb''.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop'', Hvl'', Hisp'', Hres'', Hmb'', Hvlb''. rewrite Htop in Htop''.
      unfold md. rewrite with_vmmaps_C.
      assert (HE'' : env_ok sp0 mem0 m'').
      { apply (env_ok_allocT sp0 mem0 Hvsp AL_glob AL_grant AL_errno A A'' M m'' vm vm'' HE HI Htop HI'' Htop'').
        intros a H1 H2 H3 H4. apply Hfr''; try assumption. rewrite F2, u_small by lia. unfold ALLOC_STACK in *. lia. }
      assert (Hlbuf'' : live A'' buf = Some cap).
      { rewrite Hlq''; [exact Hl|]. intros Heq. destruct (Z.eq_dec paylen 0) as [Hp0|Hp0].
        - rewrite (proj1 (HC0 Hp0)) in Heq. rewrite Heq in Hb0. rewrite u_small in Hb0 by lia. lia.
        - pose proof (Hlo' ltac:(unfold paylen in *; lia)) as Hlo2. rewrite <- Heq in Hlo2. rewrite Hl in Hlo2.
          injection Hlo2 as Hlo2. unfold paylen, L, cfg, V23TRun.paylen, V23TRun.L, V23TRun.cfg in *. lia. }
      assert (HW'' : sideW A'' vm'' m'' buf cap).
      { split; [exact HI''|]. split; [exact Hlbuf''|]. split; [rewrite Hvl''; exact Hvl|]. split; [exact Htop''|].
        split; [rewrite Hisp''; exact Hisp|]. split; [exact (vm_resv_step _ _ _ _ Hres Hres'' Hmb'')|]. split; [exact HE'' | exact Hc0]. }
      assert (HP'' : pendingP m'' k w).
      { apply (pendingP_frame sp0 Hvsp data M m'' k w HP). destruct HP as (_ & Hw & Hk3). intros a Ha. apply Hfr''.
        - intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm _ HI Htop Ho) as [Hg|Hg]; lia.
        - intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A'' m'' vm'' _ HI'' Htop'' Ho) as [Hg|Hg]; lia.
        - intros He. apply AL_errno in He. lia.
        - rewrite F2, !u_small by lia. unfold ALLOC_STACK. lia. }
      set (vals2 := vals ++ junk_vals regs'').
      assert (HL2 : length vals2 = 82%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG a0s path vals sr Rc regs'' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs'') as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      clear HR. rename HR2 into HR.
      destruct fe_itin as (_ & _ & VLK & KNA & In_ & Ic & Xn & Xc & _).
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_after_allocT sp0 a0s path Hvsp AL_glob AL_grant AL_errno AL_hi A A'' vals M m'' vm vm'' regs'' kn
                      ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK) HK HI Htop HI'' Htop'') as HK2 end.
      specialize (HK2 ltac:(intros a H1 H2 H3 H4; apply Hfr''; try assumption; rewrite F2, u_small by lia; exact H4)
                      ltac:(intros a Ha; destruct (Hgr'' a Ha) as [Ho|Hs]; [right; left; exact Ho | right; right; exact Hs])).
      rewrite KNA in HK2. fold vals2 in HK2. clear HK. rename HK2 into HK.
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q6 : vals_ev vals2 6 = buf) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
      assert (Q10 : vals_ev vals2 10 = Z_to_bv 64 (hdr_b1s data)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P10).
      assert (Q18 : vals_ev vals2 18 = w) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P18).
      clearbody vals2. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      pose proof (b1_rng sp0 data) as Hb1r. pose proof (sgn_val sp0 (hdr_b1 data) Hb1r) as SGN.
      change (bv_swrap 8 (hdr_b1 data)) with (hdr_b1s data) in SGN.
      assert (GO : forall rvl Rx Mx,
        (forall HRx : regs_ok (ENV (map (edenot (ENV vals2)) rvl)) sr_FN1 Rx, forall HKx : know_ok RSEGS (ENV (map (edenot (ENV vals2)) rvl)) Mx kn_FN1,
          length rvl = 40%nat -> nth 0 rvl (ELit 0) = EVar 0 -> nth 5 rvl (ELit 0) = EVar 5 -> nth 6 rvl (ELit 0) = EVar 6 -> nth 7 rvl (ELit 0) = EVar 18 ->
          sideW A'' vm'' Mx buf cap -> pendingP Mx k w ->
          realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x63334) Mx (seg_rom RSEGS)) (mkModelC V23Open.fds0 vm'' stdin0 fs0 None (Some tid) None))
                   (t_emit (W 1 (zero_lines k)) (t_exit (exit_code 0) fs0)))).
      { intros rvl Rx Mx HRx HKx Hlen E0 E5 E6 E7 HSx HPx.
        apply (fn1_tail sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp data AL_segs AL_rom AL_free AL_tp AL_glob AL_grant
                 AL_errno AL_ro AL_rw AL_hi AL_ret AL_env k buf cap fxp A'' vm'' (map (edenot (ENV vals2)) rvl) Rx Mx w).
        - rewrite length_map. exact Hlen.
        - rewrite vals_ev_map by lia. rewrite E0. exact Q0.
        - rewrite vals_ev_map by lia. rewrite E5. exact Q5.
        - rewrite vals_ev_map by lia. rewrite E6. exact Q6.
        - rewrite vals_ev_map by lia. rewrite E7. exact Q18.
        - exact HRx. - exact HKx. - exact HSx. - exact HPx. }
      destruct counting eqn:Hcnt; unfold counting, V23TRun.counting in Hcnt; rewrite Hcnt in SGN.
      +
        run_blk_keep (SCR [true] [] []) 82%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V23Open.ENV]. rewrite Q10. exact SGN. }
        lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
          destruct (sideW_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A'' vm'' m'' buf cap E log HW'' ltac:(apply log_win_wdl; vm_compute; reflexivity) Q0) as [HS3 OUT3] end.
        rewrite <- EQM in HS3, OUT3.
        assert (HP3 : pendingP M0 k w).
        { apply (pendingP_frame sp0 Hvsp data m'' M0 k w HP''). destruct HP'' as (_ & Hw & Hk3). intros a Ha. rewrite EQM.
          lazymatch goal with |- mem_denot ?E _ ?log _ = _ =>
            apply (mem_denot_out_win E m'' log 0); [vm_compute; reflexivity | cbn [ev ENV V23Open.ENV]; rewrite Q0; lia
                                                  | cbn [ev ENV V23Open.ENV]; rewrite Q0; unfold WIN; lia] end. }
        clear EQM OUT3.
        let rv := eval vm_compute in (fn1_rvl (EVar 18) (s_regs (fst (fst fe_r2c)))) in
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO rv Rx Mx); try reflexivity; [| | exact HS3 | exact HP3] end.
        * lazymatch goal with |- regs_ok (ENV (map _ ?rvl)) _ _ =>
            change (ENV (map (edenot (ENV vals2)) rvl)) with (xenv (ENV vals2) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HR with regs_ok _ ?sr _ =>
              p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals2) rvl idb _ (fun k => eq_refl) srb sr_FN1 _ HR eq_refl eq_refl)) end end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * lazymatch goal with |- know_ok _ (ENV (map _ ?rvl)) _ _ =>
            change (ENV (map (edenot (ENV vals2)) rvl)) with (xenv (ENV vals2) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              apply (know_ok_xfer_entails RSEGS (ENV vals2) rvl idb _ _ kn kn_FN1 (fun k => eq_refl) HK) end end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      +
        run_blk_keep (SCR [false] [] []) 82%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V23Open.ENV]. rewrite Q10. exact SGN. }
        lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
          destruct (sideW_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A'' vm'' m'' buf cap E log HW'' ltac:(apply log_win_wdl; vm_compute; reflexivity) Q0) as [HS3 OUT3] end.
        rewrite <- EQM in HS3, OUT3.
        assert (HP3 : pendingP M0 k w).
        { apply (pendingP_frame sp0 Hvsp data m'' M0 k w HP''). destruct HP'' as (_ & Hw & Hk3). intros a Ha. rewrite EQM.
          lazymatch goal with |- mem_denot ?E _ ?log _ = _ =>
            apply (mem_denot_out_win E m'' log 0); [vm_compute; reflexivity | cbn [ev ENV V23Open.ENV]; rewrite Q0; lia
                                                  | cbn [ev ENV V23Open.ENV]; rewrite Q0; unfold WIN; lia] end. }
        clear EQM OUT3.
        let rv := eval vm_compute in (fn1_rvl (EVar 18) (s_regs (fst (fst fe_r2n)))) in
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO rv Rx Mx); try reflexivity; [| | exact HS3 | exact HP3] end.
        * lazymatch goal with |- regs_ok (ENV (map _ ?rvl)) _ _ =>
            change (ENV (map (edenot (ENV vals2)) rvl)) with (xenv (ENV vals2) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HR with regs_ok _ ?sr _ =>
              p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals2) rvl idb _ (fun k => eq_refl) srb sr_FN1 _ HR eq_refl eq_refl)) end end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * lazymatch goal with |- know_ok _ (ENV (map _ ?rvl)) _ _ =>
            change (ENV (map (edenot (ENV vals2)) rvl)) with (xenv (ENV vals2) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              apply (know_ok_xfer_entails RSEGS (ENV vals2) rvl idb _ _ kn kn_FN1 (fun k => eq_refl) HK) end end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
  Qed.
  Definition PFU : list (Z * Z) := [(0x127db0, 0x127db4); (0x127dd8, 0x127de0); (0x1588b8, 0x158cb8)]%Z.

  Definition at_tl1 (rem k : nat) (buf : word) (cap : Z) : Prop :=
    forall (fxp : FPState) A vm vals R M aligned owned w,
      frm_zero (@fp_csr fxp) ->
      length vals = 50%nat -> slotsL vals buf aligned owned (Z.of_nat rem) -> vals_ev vals 18 = w ->
      regs_ok (ENV vals) sr_TL R -> know_ok RSEGS (ENV vals) M kn_TL1 ->
      sideT A vm M buf cap owned -> roomT A vm (Z.of_nat rem) -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
      pendingP M k w -> (1 <= rem)%nat -> (rem + k <= 3)%nat ->
      (L < cap)%Z -> (cap <= 67108864)%Z -> (6 + cfg <= L)%Z ->
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x634c8) M (seg_rom RSEGS)) (model2 vm))
               (t_emit (W 1 (zero_lines (k + rem))) (t_exit (exit_code 0) fs0)).

  Theorem tl1_loop : forall rem k buf cap, at_tl1 rem k buf cap.
  Proof.
    induction rem as [|rem IH]; intros k buf cap fxp A vm vals R M aligned owned w FRM HL SL P18 HR HK HS HRT HC HB HP Hrem Hrk HcapL Hcap26 HLc; [lia|].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    destruct (paylen_facts sp0 Hvsp data HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    unfold model2, V23ReadLoop.model2.
    run_blk_keep scr0 50%nat.
    lazymatch type of EQM with ?Mn = mem_denot _ _ _ => rename Mn into Mq end.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap owned E log HS ltac:(vm_compute; reflexivity) P0) as [HSb _] end.
    rewrite <- EQM in HSb.
    assert (OUTb : forall x : word, bv_unsigned x <> 0x137f14%Z -> Mq x = M x).
    { intros x Hx. rewrite EQM. cbn [mem_denot]. apply MemSplit.wbytes_outside;
        rewrite length_N_to_le_bytes; unfold adenot, v_addi; cbn [a_base a_off edenot];
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
    assert (HCb : copyP Mq aligned owned).
    { pose proof HS as ((HIq & _ & _ & Htopq & _) & Hloq & _).
      destruct HC as [HCa HCc]. split; [| exact HCc]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A M vm owned paylen HIq (Hloq Hp) Hp Htopq) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply OUTb. rewrite u_small by lia. lia. }
    assert (HBb : bytes_at Mq (bv_unsigned buf) data).
    { pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
      intros i Hi. unfold V23TRun.L in *. rewrite <- (HB i Hi). apply OUTb. rewrite u_small by lia. lia. }
    assert (HPx : pendingP Mq k w) by (apply (pendingP_frame sp0 Hvsp data M Mq k w HP); intros a Ha; apply OUTb; lia).
    clear HP. rename HPx into HP.
    clear EQM OUTb HS HC HB. clear M. rename Mq into M. rename HSb into HS. rename HCb into HC. rename HBb into HB.
    destruct tl1_itin as (_ & _ & _ & VLK1 & VLS1 & KF & _ & S2 & VLS2 & VLK2 & I3l & I3e & KA3 & S3e & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) ?K =>
      apply (fz_call sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp data AL_segs AL_rom AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw
               AL_hi AL_env FZ fxp K A vm vals Rc M buf cap aligned owned (Z.of_nat (S rem)) tl1_kn1 FRM HL SL0 HR HK VLK1
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HS HC HB HcapL Hcap26 HLc ltac:(lia) HRT) end.
    clear HR HK. intros fx2 A' vm' M' R' FRM2 HR HK HS' HC' HB' HFR HRT'. clear FRM. clear fxp.
    assert (HP' : pendingP M' k w).
    { apply (pendingP_frame sp0 Hvsp data M M' k w HP). destruct HP as (_ & Hw & Hk3). intros a Ha. apply HFR. lia. }
    rewrite KF in HK. clear HS HC HB HP HFR M.
    set (vals2 := vals ++ junk_vals R') in *.
    assert (HL2 : length vals2 = 82%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q16 : vals_ev vals2 16 = Z_to_bv 64 (Z.of_nat (S rem))) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P16).
    assert (Q18 : vals_ev vals2 18 = w) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P18).
    assert (SL2 : slotsL vals2 buf aligned owned (Z.of_nat (S rem))).
    { subst vals2. split; [repeat split|]; rewrite ?vals_ev_app_l by (rewrite HL; lia); try assumption.
      all: repeat split; rewrite ?vals_ev_app_l by (rewrite HL; lia); assumption. }
    clearbody vals2. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
    clear P0 P1 P2 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P18 SL0.
    destruct SL2 as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    destruct HP' as (HPb & HPw & HPk).
    run_blk_keep scr0 82%nat.
    lazymatch type of EQM with ?Mn = mem_denot _ _ _ => rename Mn into Mq end.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M' buf cap owned E log HS' ltac:(vm_compute; reflexivity) Q0) as [HSb _] end.
    rewrite <- EQM in HSb.
    assert (OUTb : forall x : word, bv_unsigned x <> 0x137f14%Z -> Mq x = M' x).
    { intros x Hx. rewrite EQM. cbn [mem_denot]. apply MemSplit.wbytes_outside;
        rewrite length_N_to_le_bytes; unfold adenot, v_addi; cbn [a_base a_off edenot];
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
    assert (HCb : copyP Mq aligned owned).
    { pose proof HS' as ((HIq & _ & _ & Htopq & _) & Hloq & _).
      destruct HC' as [HCa HCc]. split; [| exact HCc]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HIq (Hloq Hp) Hp Htopq) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply OUTb. rewrite u_small by lia. lia. }
    assert (HBb : bytes_at Mq (bv_unsigned buf) data).
    { pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A' vm' M' buf cap (proj1 HS')) as (Hb0 & Hb1 & Hal & Hbb).
      intros i Hi. unfold V23TRun.L in *. rewrite <- (HB' i Hi). apply OUTb. rewrite u_small by lia. lia. }
    assert (HPbb : rdn RSEGS Mq (Z_to_bv 64 0x1588b8) (2 * k) = Some (zero_lines k)).
    { rewrite <- HPb. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply OUTb. rewrite u_small by lia. lia. }
    clear HPb. rename HPbb into HPb.
    clear EQM OUTb HS' HC' HB'. clear M'. rename Mq into M'. rename HSb into HS'. rename HCb into HC'. rename HBb into HB'.
    pose proof HS' as HS0. destruct HS' as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A' vm' M' buf cap (proj1 HS0)) as (Hb0 & Hb1 & Hal & Hbb).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (G1 : getr Rc 1 = Z_to_bv 64 0x634ec) by (regv HR (1 : reg); reflexivity);
      assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11 : reg); reflexivity);
      assert (G2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
        by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V23Open.ENV];
            rewrite Q0; first [reflexivity | f_equal; lia])
    end.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals2) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    assert (PFH : pfH M' (Z_to_bv 64 (bv_unsigned sp0 - 208)) (bv_unsigned w) (bv_unsigned (canary_w a_draw))).
    { constructor.
      - rewrite u_small by lia. replace (bv_unsigned sp0 - 208)%Z with (bv_unsigned sp0 + (-13) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
      - rewrite u_small by lia. lia.
      - rewrite u_small by lia. lia.
      - intros a n Ha1 Ha2. rewrite u_small in Ha1, Ha2 by lia. unfold PF_FR in Ha1.
        pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z n ltac:(lia) ltac:(lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V23Open.ENV] in Hst. rewrite Q0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst. exact Hst.
      - lazymatch type of HK with know_ok _ _ _ ?kn =>
          exact (kimg_clearL sp0 Hvsp data (ENV vals2) M' kn 0x10000 0x127000 HK ltac:(vm_compute; reflexivity)) end.
      - krd_solve HK.
      - krd_solve HK.
      - krd HK 0x127dd8%Z 8%nat Hwp. rewrite Hwp. cbn [ev ENV V23Open.ENV]. rewrite Q18, Z_to_bv_bv_unsigned. reflexivity.
      - rewrite HPw. lia.
      - krd_solve HK.
      - krd_solve HK.
      - krd_solve HK.
      - lazymatch type of HK with know_ok ?segs ?E ?Mf ?kn =>
          pose proof (kblob_rdn segs E Mf kn (ELit 0) 0x158440 (ELit 8) 2%nat HK ltac:(vm_compute; reflexivity)) as Hcan end.
        cbn [eb ENV V23Open.ENV blobs_ev blobs0 nth length] in Hcan. rewrite SymDriveX.adenot_lit0 in Hcan.
        rewrite guard_bytes_w in Hcan. cbn [length word_to_le_bytes] in Hcan. rewrite Z_to_bv_bv_unsigned. exact Hcan.
      - apply u64_range. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      destruct (printf0_buffered Rc M' (seg_rom RSEGS) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (bv_unsigned w) (bv_unsigned (canary_w a_draw))
                  PFH G1 G2 G11) as (Rm & Mm & Hms & Hkeep & [Hagree Hgrows] & Hrd2 & Hwpos & Hflags) end.
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms PFH KW G1 G2 G11.
    assert (OUTP : forall x : word,
              ~ (bv_unsigned sp0 - 208 - 1056 <= bv_unsigned x < bv_unsigned sp0 - 208)%Z ->
              ~ (0x127db0 <= bv_unsigned x < 0x127db4)%Z -> ~ (0x127dd8 <= bv_unsigned x < 0x127de0)%Z ->
              ~ (bv_unsigned w <= bv_unsigned x < bv_unsigned w + 2)%Z -> Mm x = M' x).
    { intros x H1 H2 H3 H4. apply Hagree. cbn [outside]. unfold in_rng.
      rewrite (u_small (bv_unsigned sp0 - 208)) by lia. rewrite !u_small by lia. repeat split; lia. }
    assert (HS2 : sideT A' vm' Mm buf cap owned).
    { split; [| split; [exact Hlo' | exact Hln]].
      apply (sideW_frame sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A' vm' M' Mm buf cap (proj1 HS0)); [| exact Hgrows].
      intros x Hne.
      destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 208 - 1056)) as [Y1|Y1];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 208)) as [Y2|Y2]; [left; unfold V23ReadLoop.in_win; lia|]];
        (destruct (Z_lt_ge_dec (bv_unsigned x) 0x127db0) as [Y3|Y3];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x127de0) as [Y4|Y4]; [right; left; unfold in_data; lia|]]);
        (destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned w)) as [Y5|Y5];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned w + 2)) as [Y6|Y6]; [right; left; unfold in_data; lia|]]);
        exfalso; apply Hne; apply OUTP; lia. }
    assert (HC2 : copyP Mm aligned owned).
    { destruct HC' as [HC1 HC0]. split; [| exact HC0]. intros Hp. destruct (HC1 Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply OUTP; rewrite u_small by lia; lia. }
    assert (HB2 : bytes_at Mm (bv_unsigned buf) data).
    { intros i Hi. unfold V23TRun.L in *. rewrite <- (HB' i Hi). apply OUTP; rewrite u_small by lia; lia. }
    assert (HP2 : pendingP Mm (S k) (Z_to_bv 64 (bv_unsigned w + 2))).
    { apply (pendingP_snoc M' Mm k w _ (conj HPb (conj HPw HPk))); [| exact Hrd2 | rewrite u_small by lia; reflexivity | lia].
      intros a Ha. apply OUTP; lia. }
    clear HS0 HC' HB' HPb Hrd2.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path)) sr Rc Rm RefMemcpyLib.callee_saved ltac:(rewrite HL2; exact VLS2) HR Hkeep callee_saved_no0) as HR3 end.
    rewrite HL2 in HR3. lazymatch type of HR3 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR3 end.
    clear HR Hkeep. rename HR3 into HR.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (know_ok_call RSEGS (ENV vals2) M' Mm PFU (-208 - 1056) (-208) IHI 0x127000) as KC;
      specialize (KC ltac:(cbn [ev ENV V23Open.ENV]; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
      specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HKc; clear KC
    end.
    specialize (HKc ltac:(intros x Hnt; apply OUTP; unfold touched, IHI, WIN, PFU in Hnt; cbn [ev ENV V23Open.ENV] in Hnt; rewrite Q0 in Hnt;
                            [ intros Hx; apply Hnt; right; right; lia
                            | intros Hx; apply Hnt; left; split; [lia|]; exists (0x127db0, 0x127db4)%Z; split; [left; reflexivity | cbn; lia]
                            | intros Hx; apply Hnt; left; split; [lia|]; exists (0x127dd8, 0x127de0)%Z; split; [right; left; reflexivity | cbn; lia]
                            | intros Hx; apply Hnt; left; split; [lia|]; exists (0x1588b8, 0x158cb8)%Z; split; [right; right; left; reflexivity | cbn; lia] ])
                    ltac:(intros x _ Hx; apply Hgrows; exact Hx)
                    ltac:(intros m a n H1 H2; apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2])).
    lazymatch type of HKc with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HKc end. clear HK.
    assert (HK : know_ok RSEGS (ENV vals2) Mm tl1_kn3i).
    { unfold know_ok, tl1_kn3i. apply Forall_cons; [| apply Forall_cons; [| exact HKc]].
      - apply (kword_intro RSEGS (ENV vals2) Mm (ELit 0) (Z_to_bv 64 0) 0x127dd8 8 _ (Z_to_bv 64 (bv_unsigned w + 2)));
          [reflexivity | cbn [edenot ev ENV V23Open.ENV]; rewrite Q18; rewrite alu_add_wZ; reflexivity | lia | lia
          | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia
          | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; exact Hwpos].
      - apply (kword_intro RSEGS (ENV vals2) Mm (ELit 0) (Z_to_bv 64 0) 0x127db0 4 _ (Z_to_bv 64 5));
          [reflexivity | reflexivity | lia | lia
          | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia
          | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; exact Hflags]. }
    clear HKc.
    pose proof (env_app_know RSEGS vals2 (junk_vals Rm) (blobs_ev (blobs0 a0s path)) Mm tl1_kn3i ltac:(rewrite HL2; vm_compute; reflexivity) HK) as HK3.
    clear HK. rename HK3 into HK.
    set (vals3 := vals2 ++ junk_vals Rm) in *.
    assert (HL3 : length vals3 = 114%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
    assert (T0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q0).
    assert (T16 : vals_ev vals3 16 = Z_to_bv 64 (Z.of_nat (S rem))) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q16).
    assert (T18 : vals_ev vals3 18 = w) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q18).
    assert (SL3 : slotsL vals3 buf aligned owned (Z.of_nat (S rem))).
    { subst vals3. split; [repeat split|]; rewrite ?vals_ev_app_l by (rewrite HL2; lia); try assumption.
      all: repeat split; rewrite ?vals_ev_app_l by (rewrite HL2; lia); assumption. }
    clearbody vals3. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
    clear P0 P1 P2 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 Q0 Q16 Q18.
    destruct SL3 as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    assert (ADD16 : (sext 64 (alu32 ALU_ADD (low32 (vals_ev vals3 16)) (low32 (Z_to_bv 64 (-1)))) : word) = Z_to_bv 64 (Z.of_nat rem)).
    { rewrite T16, addiw_dec by lia. f_equal. lia. }
    assert (W2 : (0x1588b8 <= bv_unsigned w + 2 <= 0x1588b8 + 6)%Z) by lia.
    destruct rem as [|rem'].
    -
      run_blk_keep (SCR [false] [] []) 114%nat.
      { cbn [sc_denot branch_taken edenot ev ENV V23Open.ENV]. rewrite ADD16. reflexivity. }
      cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      replace (k + 1)%nat with (S k) by lia.
      let rv := eval vm_compute in fe_rvlt in
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (fe_tail (S k) buf cap fx2 A' vm' (map (edenot (ENV vals3)) rv) Rx Mx aligned owned (Z_to_bv 64 (bv_unsigned w + 2))) end.
      + rewrite length_map. reflexivity.
      + unfold slotsE, V23Hdr.slotsR; repeat split; rewrite vals_ev_map by (cbn; lia); cbn [nth edenot ev ENV V23Open.ENV]; assumption.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth edenot ev ENV V23Open.ENV]. rewrite T18, alu_add_wZ. reflexivity.
      + lazymatch goal with |- regs_ok (ENV (map _ ?rvl)) _ _ =>
          change (ENV (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) rvl idb _ (fun k => eq_refl) srb sr_FE _ HR eq_refl eq_refl)) end end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[Hi|[]]]; [exfalso; lia|]. subst i. cbn [nth emap edenot ev ENV V23Open.ENV idb]. rewrite ADD16. reflexivity.
      + lazymatch goal with |- know_ok _ (ENV (map _ ?rvl)) _ _ =>
          change (ENV (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals3) rvl idb _ _ kn kn_FE (fun k => eq_refl) HK) end end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
        apply Forall_cons; [| constructor]. apply krange_intro. cbn [edenot ev ENV V23Open.ENV]. rewrite T18, alu_add_wZ, u_small by lia. lia.
      + exact HS2.
      + exact HC2.
      + exact HP2.
      + lia.
      + exact HcapL.
    -
      run_blk_keep (SCR [true] [] []) 114%nat.
      { cbn [sc_denot branch_taken edenot ev ENV V23Open.ENV]. rewrite ADD16. unfold bv_eqb. rewrite !u_small by lia.
        replace (Z.of_nat (S rem') =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      replace (k + S (S rem'))%nat with (S k + S rem')%nat by lia.
      let rv := eval vm_compute in tl1_rvl in
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (IH (S k) buf cap fx2 A' vm' (map (edenot (ENV vals3)) rv) Rx Mx aligned owned (Z_to_bv 64 (bv_unsigned w + 2)) FRM2) end.
      + rewrite length_map. reflexivity.
      + unfold slotsL, V23TRunL.slotsL, slotsT, V23Hdr.slotsR; repeat split; rewrite vals_ev_map by (cbn; lia); cbn [nth edenot ev ENV V23Open.ENV];
          first [assumption | rewrite ADD16; reflexivity].
      + rewrite vals_ev_map by (cbn; lia). cbn [nth edenot ev ENV V23Open.ENV]. rewrite T18, alu_add_wZ. reflexivity.
      + lazymatch goal with |- regs_ok (ENV (map _ ?rvl)) _ _ =>
          change (ENV (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) rvl idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[]]. exfalso; lia.
      + lazymatch goal with |- know_ok _ (ENV (map _ ?rvl)) _ _ =>
          change (ENV (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals3) rvl idb _ _ kn kn_TL1 (fun k => eq_refl) HK) end end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
        apply Forall_cons; [| constructor]. apply krange_intro. cbn [edenot ev ENV V23Open.ENV]. rewrite T18, alu_add_wZ, u_small by lia. lia.
      + exact HS2.
      +
        replace (Z.of_nat (S rem')) with (Z.of_nat (S (S rem')) - 1)%Z by lia. exact HRT'.
      + exact HC2.
      + exact HB2.
      + exact HP2.
      + lia.
      + lia.
      + exact HcapL.
      + exact Hcap26.
      + exact HLc.
  Qed.
End TRunC.
