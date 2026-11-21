(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (writev's channel-reader flag; recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2ExitBase O2StdioDefs O2Exit O2LibStdioCall O2MemcpyBase O2Memcpy O2Memchr O2Strnlen O2Startup O2MainEntry.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2OpenFail_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2OpenFail_tail () := "C47Corelib7Program6Basics4flipC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2eq01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O2;O2StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib2O2:O2ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00I59OSSVerify5KrLib2O2;O2StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib6Common9CliDriver6SymRun=ext_val_zx_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib2O2;O2StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K59OSSVerify5KrLib2O2;O2StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib2O26O2Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib6Common8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs5STOPSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4srI0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4knI0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5aluop02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knIC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant01C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic8f_equal2C47Corelib4Init9Datatypes3appC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1c59OSSVerify5KrLib2O2?O2OpenFail_tail5PRE17C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail9nth_app_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C69OSSVerify5KrLib6Common9CliDriver:SymDriveH46win_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH49log_out_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:flat_introC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib6Common9CliDriver7LibTail9rdn_app_ZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C69OSSVerify5KrLib6Common9CliDriver4Spec3s2bC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List9app_nil_rC47Corelib4Init9Datatypes3fstK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_wZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_varC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_addC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_exit_has_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail7of_segIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2LibStdioCall@stdio_call_soundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4Ardn_mem_denot_outC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs6BUF_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs6BUF_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3srHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knHC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib2O2?O2OpenFail_defs4srH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4knH0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib2O2?O2OpenFail_tail;PRE17_wordsC1?~~~~~~~~~~~~~~~K46Stdlib7Strings6String6string01C59OSSVerify5KrLib2O2?O2OpenFail_defs>itinerary_le62C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs2rAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs2rBC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C59OSSVerify5KrLib2O2?O2OpenFail_defs2rCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs2rDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs2rEC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C59OSSVerify5KrLib2O2?O2OpenFail_defs2PXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs2rFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C59OSSVerify5KrLib2O2?O2OpenFail_defs2rGC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C59OSSVerify5KrLib2O2?O2OpenFail_defs2rHC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scOFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs2rIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:SpecConstsArw_bytes_max_ge17C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC59OSSVerify5KrLib6Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC69OSSVerify5KrLib6Common9CliDriver7LibTail6ltu_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vmul_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8kimg_rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4@wbytes_agree_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4>know_cut_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH46kn_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib6Common7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses:impl_morphc59OSSVerify5KrLib2O2?O2OpenFail_tail7of_segHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib2O2?O2OpenFail_defs4scrGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4srG0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4knG0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail6nl_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail4atG0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z:ltb_irreflC69OSSVerify5KrLib6Common9CliDriver:SymDriveH4>edenot_addw0_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4<edenot_exts4C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_allC46Stdlib5Lists4List:firstn_appC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC59OSSVerify5KrLib6Common7SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scrFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4srF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail7of_segGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail;of_segF_genC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notc59OSSVerify5KrLib2O2?O2OpenFail_tail4atF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6word_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib6Common9CliDriver7LibTail:rdn_byte_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith4Znat5Nat2Z2idC69OSSVerify5KrLib6Common9CliDriver7LibTail:In_nth_neqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Memchr<rodata_clearC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2O28O2Memchr5mchrH01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O28O2Memchr5mchrH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2Strnlen;ref_strnlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame6in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail<vals_ev_junkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun<krange_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<know_ok_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame=frame_mod_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4extzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib6Common9Leptonica5Frame9frame_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_geC59OSSVerify5KrLib2O2?O2OpenFail_defs4scrEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4knE0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4srD0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knCC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2O2?O2OpenFail_defs3knDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail@callee_saved_no0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib:wbytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs5logM1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTailBedenot_addw0_errnoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun;carry_afterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail=memcpy1_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail8of_segDEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4knC0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail9PRE17_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scrBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4srB0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4knB0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3srAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_tail9pre17_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knBC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section Tail.
  Variable sp0 : word.
  Variable BL : list (list byte).          (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Hypothesis Hrd2 : m_channel_reader model = true.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma of_segI : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32028) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x49840), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [|split; [exact Hh|split; [exact Hlazy|]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV vals) _ knI ltac:(let i := kidx knI (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (301120 - 168)%Z with 0x49798%Z.
        krd HK 0x49798%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * eexists; krd_solve HK.
      * atexit_solve ltac:(idtac; krd_solve HK).
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PRE17 : list byte := s2b "cli: cannot open "%string.

  Lemma PRE17_words :
    word_to_le_bytes 8 (Z_to_bv 64 7953747406983097443)
    ++ word_to_le_bytes 8 (Z_to_bv 64 7954887939408031598)
    ++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE17.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail_tail ()) ["Tail"] "h01Hh12b1h22b2h31np;1p;3p;2p;:g004Lj15Tg0051j1DTg005Oj1=Tg0062j1JTg01P;j1Hj30Tg006Rj1:Tg00ASj16Tg00C:j1ITg008dj3>Tg00=]j2?Tg01UFj3GTg00UBj2ETg02I^l:2Tg008Ej1<Tg00]Dj2@Tg01O3j2ATg02J<j3CTg02JYj2BTg00n1j3FTf0R0#5#5p=1%:0#:p=8%50#:p=3%:0#5p=4f3R1f2R2f1R3/B03Fp=7%60,B39F12p=9g01nLR41?30'Ep=;g02;aR5#5#1R6#DR7#=R8%J8R9P9%H8R:P7%:5R5#5R;#5R<#5R=#8#6R>P7%:;R;#:R?#:R@#5RA#5#8#1RB#5#3RC#3#4#1#8RD#1#4#1#1RE#1#8#4#4RF#3#4#4#3RG#3#4#8#1RH#3#4#1#8#6RIC7RJP7P>P7P>C7RKP7%1?#6R?P7PHC9RHP7%5;#3#6R;P7PGC9RGP7%45R5#4RL#6RMP7PFC9RFP7%16R6#6RNP7PEC9REP7P>P7PDC9RDP7%3=#6R=P7PCC9RCP7%6ARAP7PAC7R>P7PAP7%:B#3RB#3#8#1#1RA#3#4#8#8RO#1#4#1#1RP#3#8#3#1RQ#3#4#8#8RR#3#4#8#4#6RSC7RTP7%:@#6R@P7PRC9RRP7%5L#6RLP7PQC9RQP7PNP7PPC9RPP7P@P7POC9ROP7%55#1#6R5P7PAC9RAP7%:<#3#6R<P7PBC9RBP7PNP7PNC7RU%I8RV508RW908>RX508RY508RZ508R[508R\508R]508R^508R_508R`508Ra508Rb508Rc508Rd508Re508P7P?P7P?C7R?P7P;P7P;C7R;P7PMP7PMC7RMP7P=P7P=C7R=P7P@P7P@C7R@P7PLP7PLC7RLP7P5P7P5C7R5P7P<P7P<C7R<=08XRf508Rg908@Rh908URi508Rj508Rk908>Rl908>Rm508Rn908KRo908URp508Rq508Rr508g02HJRs%=0Rt%=3Rug00i7%=2?>301?121?135>4Rv[1?231?205>4%=1?>23[R4f4#=?>12\vAG230P0n2001000000120000000W2W1W3R3P4^2u^1t^3sRsP0P7PJPK1;7KRJO4b0P8P9P9P:PHP?PePrP3PsP0P7PHP?1;7?O4b0P8P9P9P:PGP;PdPqP3PsP0P7PGP;1;7;O4b0P8P9P9P:PFPMPcPpP3PsP0P7PFPM1;7MO4b0P8P9P9P:PEPUPbPoP3PsP0P7PEPU1;7UREO4b0P8P9P9P:PDPKPaPnP3PsP0P7PDPKPJO4b0P8P9P9P:PCP=P`PmP3PsP0P7PCP=1;7=O4b0P8P9P9P:P>P>P_PlP3PsP0P7P>P>1;7>RlO4b0R_P8P9P9P:PTP>P^PkP3PsP0P7PTP>PlO4b0P8P9P9P:PRP@P]PjP3PsP0P7PRP@1;7@RRO4b0P8P9P9P:PQPLP\PiP3PsP0P7PQPL1;7LO4b0P8P9P9P:PPPUP[PhP3PsP0P7PPPUPEO4b0P8P9P9P:POP@PZPgP3PsP0P7POP@PRO4b0P8P9P9P:PAP5PYPfP3PsP0P7PAP51;75O4b0P8P9P9P:PBP<PXPXP3PsP0P7PBP<1;7<O4b0P8P9P9P:P>P>PWPWP_P8P9P9P:PUPUPVPVP3PsP0P7PUPUPEO4b01E9VM:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2g02<F#<RV#<#<#<#<#<#<#<RE%56#DR6/@I'A1@6S,AE1@6N,AV5C85C8g02KL5>9do"). Qed.

  Lemma of_segH : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
    length vals = 231%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543 + P)) 1%nat = Some [Z_to_bv 8 10] ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scr0 231%nat.
    (* [comment removed for export] *)
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'. 
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + (length path + 1))
                  = Some (msg_cannot_open path)).
    { unfold msg_cannot_open. change (s2b _) with PRE17.
      apply rdn_app_Z; [exact H17 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 17 + Z.of_nat (length path))%Z
          with (bv_unsigned sp0 - 543 + P)%Z by lia. exact SBn'. }
    (* [comment removed for export] *)
    assert (LEN : length (msg_cannot_open path) = (17 + (length path + 1))%nat)
      by (unfold msg_cannot_open; rewrite !length_app; reflexivity).
    replace (W 2 (msg_cannot_open path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_cannot_open path ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_le62 as (_ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scOF (msg_cannot_open path) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scOF]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11cf6) 1 = Some [Z_to_bv 8 10].
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail_tail ()) ["Tail"] "p;1p;2p;3p;4g004Lj10Tg0051j17Tg005Oj13Tg0062j18Tg007cj1ATg006Rj11Tg00ASj15Tg02JYj2<Tg00n1j3;Tg00C:j1:Tg01P;j34Tg01P[j22Tg00UBj29Tg00fFj1@Tg00]Dj26Tg008Ej1?Tg01dGj4=Tg008dj3>Tg02;a#0R0#0#0R1#7R2#3R3#8R4#AR5%10#0#5R01<205;2%:3R6543,24'9g0244%01#0#0#7R7#3%@3U%11#1#1#0#0#1#1#1#1#0#1#1#0#5,67g02<F#?C=1620=436,245>5do"). Qed.

  Lemma of_segG : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
    length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * P + 63)%Z with (63 - P)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x11cf6) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x11cf6 1) in exact i)
                 _ _ 0x11cf6 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-543) 64) in exact i)
                    _ _ _ (-543 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 543 + P)%Z with (bv_unsigned sp0 + (-543 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x11cf6) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11cf6) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x11cf6) 1 _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x31d38 : word) with (Z_to_bv 64 0x31d38) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-543) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-543) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-543) BUF_HI IHI knG) with knH0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (of_segH path P vals1); try eassumption.
    - (* [comment removed for export] *)
      rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 543 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition atG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  Lemma of_segF_gen : forall (path : list byte) (pp : word) (P : Z) (T : TSet) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 63)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    atG0 path P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr HG0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) PX) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV PX]. rewrite P113, u_small by lia. lia. }
    unfold PX in Psmall.
    (* [comment removed for export] *)
    run_blk_keep scrF 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
      replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-543) 63) in exact i)
                    _ _ _ (-543) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 543)%Z with (bv_unsigned sp0 + -543)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp P path).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
      destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x31d38 : word) with (Z_to_bv 64 0x31d38) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-543) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-543) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-543) BUF_HI IHI knF) with knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HG0 vals1); try eassumption.
    (* [comment removed for export] *)
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 543))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  Lemma of_segF : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail_tail ()) ["Tail"] "h04__x1h12HKh23HK'h32HLh43HL'h53HL0h62HPh73HPrh82HRh93HR'h:4Hpp1h;4Hpp2h<4Hstrh=1Mh>2M'h?1Ph@2P0hA4P113hB2P2hC2Q0hD4Q113hE1RhF2R'hG2SBhH7__arithhI4__ffhJ8__varmaphK5__withL4cstrhM5cstr0hN4pathhO2pphP4valshQ5vals'hR1xhS1yp;1p;2p;3p;4p;<p;8p;=p;Cp;7g004Lj19Tg0051j1@Tg005Oj1HTg0062j1FTg006Rj17Tg0077j2`Tg007cj1MTg000Nj24Tg015WR0j16Tg008dj31j1RTg00>Gj23Tg00ASj15Tg00i7j2?Tg008Ej10Tg009>j2;Tg00]Dj2=Tg00=]j2DTg011oj2>Tg00:Bj1<Tg00;=j3LTg00<Mj4KTg02Thj2[Tg01dGj4ITg00C:j1JTg01P;j3ZTg02J<j3YTg01P[j2GTg02MPj1XTg00_Xj2WTg00QPj1VTg00RTj1UTg00SGj2TTg00a9j2STg0167j2sTg016Zj3rTg00UBj2ETg01`Hl<qTg0177j4pTg017^j1PTg018Cj2oTg018aj1nTg019?j1cTg01?Tj2ATg019jj2bTg00fFj1dTg01aQj8eTg01;0j2fTg01;Rj2_Tg01<>j3gTg01<]j4hTg00mTj2iTg04`Dl=jTg04Jmj3kTg04aClC]Tg01F@j4lTg01`mj7mTg01b5j7\Tf0R1#9#9p=2%71#7p=:%01#0p=O%01#0#0#0p=N%01#0#0#0#0#0#0#0p=a%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=8%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=^g01nLR2f1R3g021FP1Clp=BP3g01ogR4g020FR5P5g020fR6P1g021mFmp=Cf2R7P4P5P5P6P3P1F\p=Qg02;aR8#9R9#2R:#@R;#HR<#FR=%9:R>#2R?#@R@#HRA%FARB%79RC#@/`ARD%M<\AREf5RF,4<#6f3RG512g01oIRHf4RI'3%:8#:RJ#9#5RK,3I'?g01njRL14AIg02<FRM#0RN#0RO#0#O#N#a#8#8#8RP#O#N#^#8RQ311;FMp,3sp0RR51Af6RS/;Of8RO51Af7RT/;P1=@O51A1D@RRUf:RV,D@'3f;RW,D@/>V%5:'>%2?#2#2#2#2#2#2#2#5,>U'3%<Vg04\Yf9R?3Lg0244R:%<WP?g04]UCK%M=R?P:PVf>RXf?RY,4</[NCI1=;H%J<5Z<9Y<Y,G=31f@R;PYPX%59R9%X;'W%V9p,5model#U'T'SR9f=RNf<PWPV14ANRV=1LQ%6VRW%2C#7#:#5RC512RZPLP2%RLP0%R2%63%61512A1L311s313rXSLXRLPVPW1E2WPQPC1E2CM<qPOCpPZfA,4<RZ#P%6Z,3H14AYRY#P%6Y,3Hg02CgRY#J%FY1o23%n2%c2RYP4P5P5P61A2H1b28R8'B,CYR41A2K,B8,CY5QY%d5%7J#5RJ,A2,B8,CY9QY4Ge1fY6P1P7g022MRYg022mR6'E1_17=1Y6dAg2H3ChbIbJbKX0213H1131K'?13H3133J'?[^02P1fBRJPNO2bHbMbLb5POPTPSPFPIPGP7P3P114A7%8Q51L1;GM=1AR1;IPfCRP,=@51A%<Fg04Cb;LIP:%<SPIg04D^CKP:PF%7>#:#:#5,iU,=@fHR@,4<CI1G=@51?fIfGPOPTPSPPPJPFPIPGP7P3P1M=jWGW2W9WDWCW4X>EXFDXQBAk;X9eMC]W<W1W8W;W:WAWBW@W3W7W6W=WEWPX?2WOWNo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition atF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
      rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma of_segDE : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 103%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    atF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 103%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length path))%Z with (bv_unsigned pp + P)%Z in B1 by lia.
      replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite <- HP, Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x12580 32) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x326c8 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x326c8 : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 225252) with (0x36fe4 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x326c8 : word) with (Z_to_bv 64 0x326c8) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI knD
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI knD)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P).
    { subst vals1. change 113%nat with (103 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 knE0).
    { unfold knE0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV PX]. rewrite Q113, u_small by lia. lia. }
    clear HK3.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS M2 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrE 135%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q2, ?Q113). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1037a) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1037a) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1037a) 0 _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x31d38 : word) with (Z_to_bv 64 0x31d38) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knE ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 167%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    assert (W113 : vals_ev vals2 113 = Z_to_bv 64 P) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q113).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HF0 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pre17_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11ce3) 17 = Some PRE17.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail_tail ()) ["Tail"] "p;1p;3p;2p;4g004Lj11Tg0051j1;Tg005Oj19Tg0062j1ETg007cj1>Tg006Rj10Tg00ASj12Tg00C:j1<Tg01P;j37Tg01P[j2:Tg00UBj2DTg00fFj1CTg00]Dj2BTg008Ej18Tg01dGj4?Tg008dj3=Tg02JYj2@Tg00n1j3ATf0R0#1#1p=6f3R1f2R2f1R3/@03Ap=3f4A7230771p=5%80#8p=4g02;aR0#1#6R1#;R3#9R2#ER4#>R5P2P3%00R0#1R6#1R7#1R8#0#0#2R9P3P9C3R9P2P3%06R6#0R:#6#2R;P3P;C3P2P3%66#0#2R6P3P6C3P2P3%00#1R0#0#1R6#2R;P3P;C3P2P3%61R;#2R<P3P<C3R<P2P9P2P3%18#0#2R8P3P8C3P2P3%0:R:#1#2R8P3P8C3R8P2P8P2P3%0:#2R:P3P:C3R:P2P3%16#2R6P3P6C3P2P<P2P:P2P3%10#6#2R0P3P0C3P2P3%07#1#0#2R7P3P7C3P2P8%<2972<D5D5D5D5D5D5D5D5,:4'Dg0244%1;#;R;#9%C2U%01#0#0#6#0#0#0#1#6#0#0#2,B;g02<F#8#4#4#4#4#4#4#4#4C?g02KL,:45=5do"). Qed.

  Lemma PRE17_len : length PRE17 = 17%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail_tail ()) ["Tail"] "p;1p;2g008Ej11Tg00UBj22Tf0#1#1p=0g01njg02<F#1#0#0#0#0#0#0#0#0'2o"). Qed.

  (* [comment removed for export] *)
  Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE17.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail_tail ()) ["Tail"] "h04__x1h17__arithh24__ffh38__varmaph45__with51xh61nh71yh82Hah96__sat3h:6__sat4h;1zh<1Hh=2H0h>1Mh?2P0h@1bhA1lhB1mhC1ohD4valsp%0p&0p;1p;2p;3p;4p;<p;8p;6p;Bp;7g004Lj11Tg0051j1dTg005Oj1aTg0062j1_Tg007ck103Tg009>j2hTg008dj3Ek108Tg006Rj1<Tg00ASj1=Tg00=]j28Tg00>GR0j2NTg008Ej1ATg00]Dj29k109Tg01O3j2:Tg02J<j3gTg00:Bj1fTg00\2j3eTg00mTj2[Tg03nRR1j30j2Qj1WTg000Nj2bTg015WR2j1UTg05ICj2mTg00>cj1nTg00?lj1ZTg00CZj2YTg010fj2LTg00@Jj1XTg00o]j2;Tg011oR3j24Tg00UBj2BTg01CHj1^Tg01Cfk407Tg01`Hl<PTg00C:k102Tg018Ck201Tg018ak100Tg019?j1~Tg019jj2}Tg01cdj3TTg01:Mj3|Tg01F@j4OTg01;0j2{Tg01;Rj2zTg01<>j3yTg01<]j4xTg01DIj4RTg03l=j8DTg00fFj1uTg01?Tj2cTg01>Sj2tTg01>7R4j2HTg01=Oj2wTg01?0j3sTg01@7j3rTg02iVj3jTg001Kj6CTg05J8j2iTg01^7j1]Tg01_@j1\Tg05K@j4kTg0033j6qTg01bYl<pTg01c>lBoTg01`mk704Tg01aQk805Tf0R5#1#1p=7%<5#<p=2%<5#1p=3%15#1#1#1p=K%15#1#1#1#1#1#1#1p=@%15#<p=6f4R6f3R7f2R8f1R9;053Ep=?A0678?095p=M1989=075p=`1495,98p=5g01nLR:?E95p=J1B:5p=Ig01njR;P:P:P:P2P2f5R2P6P7P8P9P5M<pp>06P:P:P:P:P:P:P3P5P9P8P3P7P6P2f6f7f8f9MBop=l1c:5p=GP9g01ogR3g020FR<P<g020fR=P5g021mK04p=>g01oIR>/N5p=FP:P:P0P2P0P6P>P>P7P8P9P5M<Pp=vP:P9g021FP5COp=SP7P3P<P<P=P8P9P5L05p=Vg02;aR3#1R0#7R?#7R@#1RA#dRB#aRC#_%d?#aRD$03\CREg02<FRF,h9p,3sp0RG5ECp,4SPloS00%<3RH#<#2#2#2#2#2#2#3#7#K#@#@#@#=RI18BGRJ'Np,4SPhiS01%1A#@#@#@#@#@#=RK,NJ%_DRL%AFRM#A#A#A#A#A#A#ARN%6H#2#7#2#7RH#1#6#6#3#7#2#7#3#7#K#2#3#3#6#3#3#6#6#3#2#7#6#3#7#2#=RO,9BRP':RQ%<H#6#6#2#K#6#3#2#2#7#3#K#6#2#6#7#6#3#2#2#6#3#2#3#=RH,9BRR,:NRS%=@R@,9B,:MRT5gDRU5gDRVPE%f2R2g05LCRW7e6P6%<?RX#<#KRY#=RZ,[JR[,9BR\P5D?XALPEA07\QR]1bDQS02#UR^,m\R_;0US03%nFR`%ZYRY'YRa,L2%XORO,;2,:N506%1XRX#3#7#ZRb,Y`Rc,L2%XHRH,;2,:N%KX#ZRX,Y`R`,L2%X@R@,;2,:MDM=EE5XCER2PEP]P_PS1bDSRD#URd,m_PTDMReP2PCPGPEP6PB18B5RG/4YPQC`A5BGbPSA5BGXPTDMA06\QRG18B\R2=5B^R^;0S18B^=5BdRfPTD?X@CP;PNPEA5BJYRY=06Q14JbRg,9BRhPS14JXRi,9BRjPTDMRk%U5Rl95B2Rm=0GS18Bm=5BdPTD?X6;P;PNPEPk%UNRd95B2Rm=0GS18BmRn=5BlPTD?X6;P:P[PEPkA5B5dRo=0GS18Bo=5BdPTD?X;:P:14[dRpPEPk19BpRk=0GSPoPTD?X;:PLPEA07YQRY?0hSRo/QjA0]kSRG14pdRq,9BRr'QPTPTPCPE\LRs%Wo%WGPjPrPEPs\CRrP1P1PoPGPr\E/B1PLPE1QYh1Q]kPSPSPCPs%WY%W]RYPhPk1BrYP:PC&09BRYPYPgPpPC\:/BYRr1Jgp%=?R?,4[Rh,JgP:P:&08:RsP5X5:R1Ps1J95#^X7:X5:RGPgPg%IgPpPhP1P1P1P:P:g02Do1495H07#IXB:X6:RgP[P[%I[PdP?P1P1%IlX5;PNP?%I?J06R;M:lRlM<Pg02CgRt$02Ru%_tRt201:9Rv&00:Rw%~:RxP:1}:3R3%Gb5T:g02ESRy%GZ9|:3Rz%G?R{5T:R|CO'>1{x=R=P5P8g022MR}g022mR~'B1z58=E}~dAy:>9CxR~b2b3b4X0:145b1[5Z/4?Rb'J^0:P5PJO1R}b1CRGDGD1BLSGDGDP:PCPYPYPiPqPr1Jiq14h?Rr,JiP:P:PsP1PsPGPiPi%IiPqPrP1P1P1PgPpPhPlPdP?P;M:lM<PPuPtPvPwP:%GX9T:3PyAT:|{CO,>xP=P~b2b3b4X0:145X14b?'J^0:P}b1CRGDGD1BLTGD18Bk%Fp%FhP11N95#^X7:X5:1B:>PpPhPlEvPuPtPvPwPx%GI/S3,>xRk%u<R<1c:>RL/S|,>xCVP=P~b2b3b4X0:1NI5RI1[9ZRZ/4?R?#F[^0:P5PJQ00O2R}b1CR%=0R0%=ARA'tRb,Hp1HhbP:P:P4P1P41H95#^X7:X5:PpPhPlPbPb%IbM<P1w0ARl1H>0%FA1H>b[[R>%F0Rhg02DSR4As0A9UW8RA%Fb\4^8hRhPuPtPvPwPx%GK,S3,>xR3P<P:P|g023MR|%G0=r:BR0CO,>xCVP=P~b2b3b4X0:1N5KRK1H?b[^0:P5PJQ01O2RJb1b9b:CR5jpECP2PuPtPvPwPxPkP<1SLz,>xCVP=P~b2b3b4X0:%FZ\I^0:P}b1PlP>PAPhPuPtPvPwPxP3P<P:PzP|P0CO,>xCVP=P~b2b3b4X0:1HZb\K^0:PJb1b9b:5j[ECPEA0ojTA0]mSA5BndPTD?ePD1iNRECQ021iNPEC1h6FP8ECPEP7PB%f6R6%]a';,8B%\a'41;6O,:NROC`%]c,;6,8B%\c55B1;6H,:NRN%]`,;6,8B%\`55B1;6@,:MRMDMA0]^SPfPTD?e1L6a=07O1L6cPN1L6`PMDM=EEeeQ03PSPTP]P_CkECA07\VRVPQPUP7P\CkECAe67W=EEVeg02KLg03IfEqb=b<W?W>WDo"). Qed.

  Lemma of_segBC : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (2 ^ 64 - 4095 <= bv_unsigned (vals_ev vals 38))%Z ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    atF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x37344) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 P38 Hpp1 Hpp2 HR HK0 Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    pose proof (u64_range (vals_ev vals 38)) as H38r.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (HK : know_ok RSEGS (ENV vals) M knB0).
    { unfold knB0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK0]].
      - apply krange_intro. cbn [edenot ev ENV]. rewrite P2. lia.
      - apply krange_intro. cbn [edenot ev ENV]. lia. }
    clear HK0. change (sr_upd srA (ridx 10) (EVar 38)) with srB0 in HR.
    (* [comment removed for export] *)
    run_blk_keep scrB 39%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite edenot_addw0_errno by (cbn [edenot ev ENV]; lia).
      cbn [edenot ev ENV]. unfold bv_ltu. rewrite (u_small 18446744073709547521) by lia.
      apply (proj2 (Z.ltb_ge _ _)). lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x11ce3) 17 = Some PRE17).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x11ce3 17) in exact i)
                 _ _ 0x11ce3 17 HK eq_refl) by (cbn; lia). apply pre17_img. }
    assert (Hdst : store_ok RSEGS M' dst 17 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 17) in exact i)
                    _ _ _ (-560) 17 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x11ce3) 17 PRE17).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11ce3) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 17) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x11ce3) 17 _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x31d38 : word) with (Z_to_bv 64 0x31d38) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE17) knC0).
    { subst dst. rewrite <- (memcpy1_denot vals M' P0).
      eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE17) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE17) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE17_len; unorm; lia. }
    assert (Ht82 : rdn RSEGS (wbytes M' dst PRE17) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE17_len; unorm; lia. }
    clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE17) in *. clearbody M1. clear M' dst.
    assert (WOKS1 : win_ok (ENV vals1) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite Q0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 71%nat.
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    assert (Ht83 : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Ht82 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0, u_small by lia; lia
        | cbn [ev ENV]; rewrite Q0, u_small by lia; lia]. }
    clear EQM Hstr2 Ht82. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x11cf4) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11cf4) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x11cf4) 0 _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x31d38 : word) with (Z_to_bv 64 0x31d38) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knC ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 103%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (of_segDE path pp P T t8 vals2); eassumption.
  Qed.

End Tail.
