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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2ExitBase O2StdioDefs O2Exit O2LibStdioCall O2MemcpyBase O2Memcpy O2Memchr O2Strnlen O2Startup O2MainEntry O2OpenFail_defs O2OpenFail_tail O2OpenFail_tail2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntryN O2Usage_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Usage_tail () := "C47Corelib7Program6Basics4flipC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8f_equal2K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib2O2<O2Usage_tail4PRE7C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail4SUF7C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C69OSSVerify5KrLib6Common9CliDriver4Spec3s2bC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib6Common9CliDriver4Spec9msg_usageC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K46Stdlib7Strings6String6string01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O2;O2StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib2O2:O2ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib2O2;O2StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib6Common9CliDriver6SymRun=ext_val_zx_idC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib2O2;O2StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K59OSSVerify5KrLib2O2;O2StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib2O26O2Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs5STOPSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knH0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib6Common9CliDriver7LibTail9nth_app_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C69OSSVerify5KrLib6Common9CliDriver:SymDriveH46win_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH49log_out_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:flat_introC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib6Common9CliDriver7LibTail9rdn_app_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail<msg_usage_eqC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List:length_appC47Corelib4Init9Datatypes3fstK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_wZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_varC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_addC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_exit_has_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail7us_segHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2LibStdioCall@stdio_call_soundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4Ardn_mem_denot_outC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib2O2?O2OpenFail_defs6BUF_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs6BUF_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_srGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_knGC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib2O2<O2Usage_defs6u_srG0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knG0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib2O2<O2Usage_tail9PRE7_wordC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8SUF7_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8PRE7_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs;u_itineraryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs4u_rAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C59OSSVerify5KrLib2O2<O2Usage_defs4u_rBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs4u_rCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs4u_rDC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C59OSSVerify5KrLib2O2<O2Usage_defs2LXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs4u_rEC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C59OSSVerify5KrLib2O2<O2Usage_defs4u_rFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C59OSSVerify5KrLib2O2<O2Usage_defs4u_rGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_scGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs4u_rHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_rF3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srF3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knF3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_scF3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_rG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_scG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_rH3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_rE4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srE4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knE4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_scE4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_rF4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_rG4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srG4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knG4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_scG4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_rH4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:SpecConstsArw_bytes_max_ge17C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC59OSSVerify5KrLib6Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC69OSSVerify5KrLib6Common9CliDriver7LibTail6ltu_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vmul_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8kimg_rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4@wbytes_agree_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4>know_cut_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH46kn_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib6Common7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail7us_segGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail5atUF0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib2O2<O2Usage_defs6u_scrFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knF0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8suf7_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_knFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z:ltb_irreflC69OSSVerify5KrLib6Common9CliDriver:SymDriveH4>edenot_addw0_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4<edenot_exts4C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_allC46Stdlib5Lists4List:firstn_appC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC59OSSVerify5KrLib6Common7SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_scrEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srE0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_knDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_knEC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notc59OSSVerify5KrLib2O2<O2Usage_tail5atUE0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6word_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib6Common9CliDriver7LibTail:rdn_byte_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith4Znat5Nat2Z2idC69OSSVerify5KrLib6Common9CliDriver7LibTail:In_nth_neqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Memchr<rodata_clearC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2O28O2Memchr5mchrH01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O28O2Memchr5mchrH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2Strnlen;ref_strnlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame6in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail<vals_ev_junkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun<krange_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<know_ok_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame=frame_mod_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4extzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib6Common9Leptonica5Frame9frame_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_geC59OSSVerify5KrLib2O2<O2Usage_defs6u_scrDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knD0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srC0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_knBC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2O2<O2Usage_defs5u_knCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail@callee_saved_no0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8us_segCDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_srB0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knB0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_srH30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_knH30C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib6Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8us_segH3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_srG30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_knG30C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib6Common9CliDriver7LibTail7zbv_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8us_segG3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib2O2<O2Usage_defs7u_scrF3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_srH40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_knH40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8us_segH4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_srG40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_knG40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail9SUF7_wordC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_emit_has_nilC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib6Common9CliDriver9SymDriveX@know_after_storeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8us_segG4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AgentLib:t_emit_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC59OSSVerify5KrLib2O2<O2Usage_defs7u_srF40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_knF40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_scrE4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knF4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_gt_casesc59OSSVerify5KrLib2O2<O2Usage_tail7us_segFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail8us_segF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail;us_segE_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail9us_segEF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_tail7us_segBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PRE7 : list byte := s2b "usage: "%string.
Definition SUF7 : list byte := s2b " INPUT"%string ++ [Z_to_bv 8 10].

Section VP1.
Lemma PRE7_word : word_to_le_bytes 7 (Z_to_bv 64 9071406455288693) = PRE7.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_tail ()) ["VP1"] "h01Hh12b1h22b2h31np;1p;3p;2p;:p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8p1000np4p710p1001Kp4p710R0p8p1001ip4p710R1p1002Dp4p710p8P1P0p8p1002`p4p7210P0p8p1003=p4p710P0p8g003\j15Tg004Aj1?Tg004_j1<Tg005Bj1HTg005bj1Gj33Tg006Bj16Tg006gj11Tg007Ej1ATg007ej3=Tg008?j24Tg008ij3FTg009Mj2@Tg009gl::Tg00:Ej19Tg00:dj2DTg00;Jj2CTg00<Rj2BTg00=Ej3ETf0R0#5#5p=>%60#5p=8%60#6p=7%50#6p=0f3R1f2R2f1R3/B03Ep=2g00=hR4/@0p=;g00>FR5#5#>R6#?R7#<R8%H8R9P9%G8R:P7%65R5#8R;#8R<#6#1R=P7%>6R6#5R>#5#7#8#8R?#0#8#0#0R@#0#8#0#7RA#0#8#>#0RB#0#7#>#7RC#0#7#0#0#1RDC2REP7P=P7P=C2R=P7%5;#7#1R;P7%1CC2RCP7%>5R5#5#0#1RFP7%1BC2RBP7%65R5#7#1RGP7%1AC2RAP7%05#1R5P7%1@C2R@P7%1<R<P7%1?C2R?P7%16R6P7P6C2R6%A8RH538RI538RJ538RK538RL538RM538P7P;P7P;C2R;P7PFP7PFC2RFP7PGP7PGC2RGP7P5P7P5C2R5P7P<P7P<C2R<=38IRN538RO538RP538RQ538g00>kRR%<0RS%<3RTg00?I%<2?=30141214135=4RU[142314205=4%<1?=23[R4f4#<?=12\UAF230P0n2001000000120000000W2W1W3R3P4^2T^1S^3RRRP0P7PEP=147=#;O4b0P8P9P9P:PCP;PMPQP3PRP0P7PCP;147;#;O4b0P8P9P9P:PBPFPLPPP3PRP0P7PBPF147F#;O4b0P8P9P9P:PAPGPKPOP3PRP0P7PAPG147G#;O4b0P8P9P9P:P@P5PJPNP3PRP0P7P@P51475#;O4b0P8P9P9P:P?P<PIPIP3PRP0P7P?P<147<#;O4b0P8P9P9P:P6P6PHPHP3PRP0P7P6P61476#;O4b01@9HM::M::M::M::M::M::M::g00?d#9#9#9#9#9#9#9%?>/DD'Cg00@C5=9do"). Qed.
End VP1.
Section VP2.
Lemma SUF7_word : word_to_le_bytes 7 (Z_to_bv 64 2907475163367712) = SUF7.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_tail ()) ["VP2"] "h01Hh12b1h22b2h31np;1p;3p;2p;:g003\j13Tg004Aj1?Tg004_j1<Tg005Bj1ATg005bj1Gj35Tg006gj11Tg006Bj19Tg007Ej1@Tg007ej3=Tg008?j24Tg008ij3FTg009Mj2>Tg009gl:7Tg00:Ej18Tg00:dj2ETg00;Jj2DTg00<Rj2CTg00=Ej3BTf0R0#3#3p=6%90#3p=;%30#9p=2f3R1f2R2f1R3/C03Bp=0g00=hR4/>0p=:g00>F#3R5#3R6#3R7#?R8#<R9%A9R:P:%G9R;P8%67R7#1R<P8%;5R5#3R=#9#2#2#6R>#2#2#2#2R?#2#2#6#6R@#3#;#2#9#;RA#2#6#;#2RB#6#;#6#6#1RCC0RDP8P<P8P<C0R<P8%96R6#3#2#1REP8%1BC0RBP8%96#;#1R6P8%1AC0RAP8%6=#1R=P8%1@C0R@P8%;5RF#9#1RGP8%1?C0R?P8%3F#1RFP8%1>C0R>P8%15R5P8P5C0R5%@9RH559RI559RJ559RK559RL559RM559P8PEP8PEC0REP8P6P8P6C0R6P8P=P8P=C0R=P8PGP8PGC0RGP8PFP8PFC0RF=59IRN559RO559RP559RQ559g00>kRR%<0RS%<3RTg00?I%<2?=30141214135=4RU[142314205=4%<1?=23[R4f4#<?=12\UAF230P0n2001000000120000000W2W1W3R3P4^2T^1S^3RRRP0P8PDP<148<#:O4b0P9P:P:P;PBPEPMPQP3PRP0P8PBPE148E#:O4b0P9P:P:P;PAP6PLPPP3PRP0P8PAP61486#:O4b0P9P:P:P;P@P=PKPOP3PRP0P8P@P=148=#:O4b0P9P:P:P;P?PGPJPNP3PRP0P8P?PG148G#:O4b0P9P:P:P;P>PFPIPIP3PRP0P8P>PF148F#:O4b0P9P:P:P;P5P5PHPHP3PRP0P8P5P51485#:O4b01>:HM:7M:7M:7M:7M:7M:7M:7g00?d#8#8#8#8#8#8#8%37#?/EC'Dg00A<5=:do"). Qed.
End VP2.
Section VP3.
Lemma pre7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10bcd) 7 = Some PRE7.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_tail ()) ["VP3"] "p;1p;2p;3p;4p100B5p4p70R0p100Bcp4p7210p8P0p1002Dp4p710p8P0p1002`p4p7210p8g003\j11Tg004Aj19Tg004_j18Tg005Bj1;Tg00C?j1ATg006Bj10Tg006gj12Tg00<Rj24Tg00=Ej33Tg007Ej1<Tg005bj35Tg00Caj27Tg009Mj2:Tg00DCj1@Tg00:dj2?Tg00:Ej16Tg00Dej4=Tg007ej3>Tg00>FR0#1#1#1R1#9R2#8R3#;R4#AR5%00R0#0#1R6#0#1R7#0#2R81428532%16#0#0#2R61426532%10#1R0#1#1#0#2R61426532%00R0#0#0#2R61426532%10#0#2R01420532%27R71427532%11R1#1R7#2R01420532%<3553553553553553553553,74':g00E]%17#9R7#8%@3U%01#1#0#0#0#0#1#1#0#0#1#0#2,?7g00?d#6#6#6#6#6#6#6C=g00@C,745>5do"). Qed.
End VP3.
Section VP4.
Lemma suf7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10bd6) 7 = Some SUF7.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_tail ()) ["VP4"] "p;1p;2p;3p;4g003\j10Tg004Aj19Tg004_j18Tg005Bj1;Tg00C?j1ATg006gj12Tg00<Rj24Tg00=Ej33Tg006Bj11Tg007Ej1<Tg005bj35Tg00Caj27Tg009Mj2:Tg00DCj1@Tg00:dj2?Tg00:Ej16Tg00Dej4=Tg007ej3>Tg00>F#0R0#0R1#0R2#9R3#8R4#;R5#AR6%02R2#0R7#2R81438533%11R1#0#0#1#2R81438533%11#1#0#2R11431533%10#0R0#0#0#0#2R11431533%10#0R1#1#2R81438533%01#2R11431533%20R01430533%<4554554554554554554554,75':g00E]%07#9R7#8%@4U%12#0#1#1#1#1#0#1#0#1#1#0#2,?7g00?d#6#6#6#6#6#6#6C=g00A<,755>6do"). Qed.
End VP4.
Section VP5.
Lemma PRE7_len : length PRE7 = 7%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_tail ()) ["VP5"] "p;1p;2g00:Ej10Tg009Mj21Tg00GCg00?d#0#0#0#0#0#0#0'1o"). Qed.
End VP5.
Section VP6.
Lemma SUF7_len : length SUF7 = 7%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_tail ()) ["VP6"] "p;1p;2g00:Ej10Tg009Mj21Tg00GCg00?d#0#0#0#0#0#0#0'1o"). Qed.
End VP6.
Section VP7.
Lemma msg_usage_eq : forall a0s, msg_usage a0s = PRE7 ++ a0s ++ SUF7.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_tail ()) ["VP7"] "h03a0sp;1p;8p;2p;3g003\j13Tg004Aj1@Tg004_j1<Tg005Bj16Tg00Gbj80Tg00HAj24Tg00Hbj15Tg006Bj1;Tg006gj1:Tg00:dj27Tg007Ej18Tg005bj39Tg00I`j32Tg009Mj2?Tg00J=j1>Tg007ej3=Tf2f1f0R0'4'4p=1g00>F#3R1#3#3#@R2#<R3#6R4g00KAR5g00KaR6P5P6P5P5P5P6G0P5P5P6P6P5P5P5P6G0P5P6P6P6P6P5P5P6G0P5P5P5P6P6P5P5P6G0P5P6P5P6P6P5P5P6G0P6P5P6P5P5P5P6P6G0P6P6P6P6P6P5P6P6G0R7g00LAR8'4313131#5P5P6P6P5P6P6P5P6G0P6P5P5P5P6P6P5P6G0P6P6P6P6P5P6P5P6G0P5P6P5P6P5P6P5P6G0P6P6P5P6P5P6P5P6G0;1831517#5%;1#3#:,72%835935239230523,?4%>0g00@Cg00A<92305235=4eW0o"). Qed.
End VP7.

Section UTail.
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
Ltac close_exit_at HR HK P0 Hh Hlazy sp0 OFF WLO :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV EN] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x49840), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV EN];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV EN] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV EN] in Ktid |- *; lia
      | lit_u; cbn [ev ENV EN] in Ktid |- *; lia
      | cbn [ev ENV EN] in Ktid |- *; lia
      | lit_u; change (301120 - 168)%Z with 0x49798%Z;
        let Htc := fresh "Htc" in
        krd HK 0x49798%Z 4%nat Htc; rewrite Htc; cbn [ev ENV EN] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
            | eexists; krd_solve HK | atexit_solve ltac:(idtac; krd_solve HK)      (* [comment removed for export] *)
| repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH0 R -> know_ok RSEGS (ENV vals) M u_knH0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32028) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG : forall (a0s : list byte) (L : Z) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 66)%Z ->
    length vals = 230%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 112 = Z_to_bv 64 L ->
    regs_ok (ENV vals) u_srG0 R -> know_ok RSEGS (ENV vals) M u_knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553 + L)) 7%nat = Some SUF7 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L vals R M HP HPr HL P0 P112 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep scr0 230%nat.
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553 + L)) 7 = Some SUF7).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (7 + (length a0s + 7))
                  = Some (msg_usage a0s)).
    { rewrite msg_usage_eq.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 7)%Z with (bv_unsigned sp0 - 553)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 7 + Z.of_nat (length a0s))%Z
          with (bv_unsigned sp0 - 553 + L)%Z by lia. exact SBn'. }
    replace (W 2 (msg_usage a0s)) with (map (WriteEv (Z_to_bv 64 2)) (msg_usage a0s ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    assert (LEN : length (msg_usage a0s) = (7 + (length a0s + 7))%nat)
      by (rewrite msg_usage_eq, !length_app, PRE7_len, SUF7_len; reflexivity).
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG u_knG Rc Mc model u_scG (msg_usage a0s) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG u_knG) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Definition atUF0 (a0s : list byte) (L : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 198%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 112 = Z_to_bv 64 L ->
      regs_ok (ENV vals) u_srF0 R -> know_ok RSEGS (ENV vals) M u_knF0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.

  Lemma us_segF : forall (a0s : list byte) (L : Z), Z.of_nat (length a0s) = L -> (0 <= L <= 66)%Z ->
    atUF0 a0s L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L HP HPr vals R M HL P0 P112 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep u_scrF 198%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112).
      replace (-1 * L + 73)%Z with (73 - L)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553 + L)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x10bd6) 7 = Some SUF7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knF ltac:(let i := kidx u_knF (is_kimg_cov 0x10bd6 7) in exact i)
                 _ _ 0x10bd6 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
    assert (Hdst : store_ok RSEGS M' dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knF ltac:(let i := kidx u_knF (is_kwr_cov (EVar 0) (-553) 73) in exact i)
                    _ _ _ (-553 + L) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 553 + L)%Z with (bv_unsigned sp0 + (-553 + L))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x10bd6) 7 SUF7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?SUF7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10bd6) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x10bd6) 7 _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
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
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst SUF7) 0 (-553) BUF_HI IHI u_knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst SUF7 (ENV vals) 0 (-553) BUF_HI);
                        cbn [ev ENV]; rewrite P0, ?SUF7_len; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-553) BUF_HI IHI u_knF) with u_knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst SUF7) u_knG0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 230%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P112).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (us_segG a0s L vals1); try eassumption.
    - rewrite rdn_wbytes_out; [exact SBp' | | |]; rewrite ?SUF7_len; subst dst; rewrite ?u_small by lia; lia.
    - subst dst. rewrite <- SUF7_len.
      apply (rdn_wbytes_hit RSEGS SUF7 M'). rewrite SUF7_len, u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segE_gen : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 73)%Z ->
    length vals = 166%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp -> vals_ev vals 112 = Z_to_bv 64 L ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srE0 R -> know_ok RSEGS (ENV vals) M u_knD ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    atUF0 a0s L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T vals R M HP HPr HL P0 P1 P112 Hpp1 Hpp2 HR HK Hstr HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P112, u_small by lia. lia. }
    run_blk_keep u_scrE 166%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P112).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
    assert (Hsrc : rdn RSEGS M' pp (length a0s) = Some a0s).
    { replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length a0s) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knE ltac:(let i := kidx u_knE (is_kwr_cov (EVar 0) (-553) 73) in exact i)
                    _ _ _ (-553) (length a0s) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 553)%Z with (bv_unsigned sp0 + -553)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp L a0s).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P1);
      assert (A12 : getr Rc 12 = Z_to_bv 64 L) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P112);
      destruct (ref_memcpy M' dst pp L _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
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
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst a0s) 0 (-553) BUF_HI IHI u_knE
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst a0s (ENV vals) 0 (-553) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-553) BUF_HI IHI u_knE) with u_knF0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst a0s) u_knF0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 198%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P112).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HF0 vals1); try eassumption.
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS a0s M' (Z_to_bv 64 (bv_unsigned sp0 - 553))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition atUE0 (a0s : list byte) (pp : word) (L : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 166%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp -> vals_ev vals 112 = Z_to_bv 64 L ->
      regs_ok (ENV vals) u_srE0 R -> know_ok RSEGS (ENV vals) M u_knD ->
      rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.

  Lemma us_segCD : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 131071)%Z -> ~ In (Z_to_bv 8 0) a0s ->
    length vals = 102%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srC0 R -> know_ok RSEGS (ENV vals) M u_knB ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8 ->
    atUE0 a0s pp L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T t8 vals R M HP HPr Hnonul HL P0 P1 Hpp1 Hpp2 HR HK Hstr Ht8 HE0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 102%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (a0s ++ t8)) = Some (a0s ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length a0s) (a0s ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length a0s + 1) _ (length a0s)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + L) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length a0s))%Z with (bv_unsigned pp + L)%Z in B1 by lia.
      replace (bv_unsigned pp + L + Z.of_nat 0)%Z with (bv_unsigned pp + L)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (a0s ++ t8) L 0x7fffffff).
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
        intros E. apply (In_nth_neq a0s (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ u_knC ltac:(let k := kidx u_knC (is_kimg_cov 0x12580 32) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knC ltac:(let i := kidx u_knC (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x326c8 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P1);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (a0s ++ t8) L 0x7fffffff (seg_rom RSEGS) Rc (0x326c8 : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 225252) with (0x36fe4 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x326c8 : word) with (Z_to_bv 64 0x326c8) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI u_knC
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI u_knC)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 134%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L).
    { subst vals1. change 112%nat with (102 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 u_knD0).
    { unfold u_knD0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV LX]. rewrite Q112, u_small by lia. lia. }
    clear HK3.
    assert (Hstr2 : rdn RSEGS M2 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q112, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep u_scrD 134%nat.
    { unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q1, ?Q112). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length a0s + 1) _ (length a0s)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
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
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 u_knD ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 166%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W1 : vals_ev vals2 1 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q1).
    assert (W112 : vals_ev vals2 112 = Z_to_bv 64 L) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q112).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HE0 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segB : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 131071)%Z -> ~ In (Z_to_bv 8 0) a0s ->
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srB0 R -> know_ok RSEGS (ENV vals) M u_knB0 ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8 ->
    atUE0 a0s pp L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T t8 vals R M HP HPr Hnonul HL P0 P1 Hpp1 Hpp2 HR HK Hstr Ht8 HE0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    run_blk_keep scr0 70%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M3.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x10bd4) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10bd4) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x10bd4) 0 _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x31d38 : word) with (Z_to_bv 64 0x31d38) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals (junk_vals R4) (blobs_ev BL) M3 u_knB ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 102%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (W1 : vals_ev vals2 1 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (us_segCD a0s pp L T t8 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH3 : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH30 R -> know_ok RSEGS (ENV vals) M u_knH30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32028) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG3 : forall vals R M,
    length vals = 230%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srG30 R -> know_ok RSEGS (ENV vals) M u_knG30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x321f8) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 230%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG3 u_knG3 Rc Mc model u_scG3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG3 u_knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG3 length Z.of_nat] end.
    - lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - reflexivity.
    - reflexivity.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  Lemma us_segF3 : forall (a0s : list byte) (L : Z), Z.of_nat (length a0s) = L -> (67 <= L <= 73)%Z ->
    atUF0 a0s L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L HP HPr vals R M HL P0 P112 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep u_scrF3 198%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite <- (zbv_mod (-1 * L + 73)%Z).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (7 + length a0s) = Some (PRE7 ++ a0s)).
    { apply rdn_app_Z; [exact Hw0 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 7)%Z with (bv_unsigned sp0 - 553)%Z by lia. exact SBp'. }
    assert (Hsuf : rdn RSEGS M' (Z_to_bv 64 0x10bd6) 7 = Some SUF7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knF3 ltac:(let i := kidx u_knF3 (is_kimg_cov 0x10bd6 7) in exact i)
                 _ _ 0x10bd6 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
    rewrite msg_usage_eq, app_assoc. unfold W.
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srF3 u_knF3 Rc Mc model u_scF3 (PRE7 ++ a0s) SUF7
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srF3 u_knF3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scF3];
      rewrite ?length_app, ?PRE7_len, ?SUF7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm.
      replace (7 + length a0s)%nat with (7 + length a0s)%nat by lia. exact B80.
    - cbn [edenot]. exact Hsuf.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (us_segG3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH4 : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH40 R -> know_ok RSEGS (ENV vals) M u_knH40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32028) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG4 : forall vals R M,
    length vals = 230%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srG40 R -> know_ok RSEGS (ENV vals) M u_knG40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model)
               (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 230%nat.
    krdv HK 0%nat (-560)%Z 7%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite SUF7_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 SUF7) with (map (WriteEv (Z_to_bv 64 2)) (SUF7 ++ [])) by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG4 u_knG4 Rc Mc model u_scG4 SUF7 []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG4 u_knG4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG4];
      rewrite ?SUF7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot length Z.of_nat]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
    - reflexivity.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  Lemma us_segEF4 : forall (a0s : list byte) (pp : word) (L : Z), Z.of_nat (length a0s) = L -> (74 <= L <= 131071)%Z ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + L + 1 <= 0x800000000000)%Z ->   (* [comment removed for export] *)
    atUE0 a0s pp L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s pp L HP HPr Hpp1 Hpp2 Hpp3 vals R M HL P0 P1 P112 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P112, u_small by lia. lia. }
    run_blk_keep u_scrE4 166%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P112).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length a0s) = Some a0s).
    { replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE7 ++ a0s)) (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))))).
    2:{ rewrite msg_usage_eq, app_assoc. unfold W. rewrite (map_app _ (PRE7 ++ a0s)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srE4 u_knE4 Rc Mc model u_scE4 PRE7 a0s
             (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n u_srE4 u_knE4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scE4];
      rewrite ?PRE7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV LX]. rewrite P112. rewrite u_small by lia. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV LX]. rewrite P1. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV LX]. rewrite P1, P112. rewrite u_small by lia. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hw0.
    - cbn [edenot ev ENV LX]. rewrite P1. exact Hsrc.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with u_knF40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with u_srF40 in HR end.
      set (vals0 := vals) in P1, P112.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 198%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
      run_blk scr0 198%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hsuf : rdn RSEGS MG (Z_to_bv 64 0x10bd6) 7 = Some SUF7).
      { rewrite (kimg_rdn RSEGS (ENV vals1) _ u_knF4 ltac:(let i := kidx u_knF4 (is_kimg_cov 0x10bd6 7) in exact i)
                   _ _ 0x10bd6 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
      assert (Hdst : store_ok RSEGS MG dst 7 = true).
      { pose proof (kwr_store_ok RSEGS (ENV vals1) _ u_knF4 ltac:(let i := kidx u_knF4 (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                      _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x10bd6) 7 SUF7).
      { constructor; subst dst; rewrite ?u_small by lia; rewrite ?SUF7_len; try (cbn; lia).
        - exact Hsuf.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x10bd6) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x10bd6) 7 _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0x31d38 : word) with (Z_to_bv 64 0x31d38) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      pose proof (know_after_store RSEGS (ENV vals1) MG u_knF4 (SA (EVar 0) (-560)) 7 (ELit 2907475163367712) SUF7
                    u_knG40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply SUF7_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst SUF7) u_knG40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 230%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
      eapply (us_segG4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem us_tail : forall (a0s : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) a0s -> (Z.of_nat (length a0s) <= 131071)%Z ->
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 1 <= 0x800000000000)%Z ->
    regs_ok (ENV vals) u_srB0 R -> know_ok RSEGS (ENV vals) M u_knB0 ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length a0s))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31d38) M (seg_rom RSEGS)) model)
               (t_die (msg_usage a0s) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_tail ()) ["UTail"] "h04__x1h13HL0h27__arithh34cstrh45cstr0h54__ffh68__varmaph75__with84HL'0h95cstr1h:1oh;2HKh<3HK'h=2HLh>3HL'h?3HPlh@2HRhA3HR'hB3HgthC4Hgt2hD3HlehE4Hle2hF6HnonulhG4Hpp1hH4Hpp2hI4Hpp3hJ4HstrhK5Hstr'hL3Ht8hM1MhN2M'hO2P0hP2P1hQ2Q0hR2Q1hS4Q112hT1RhU2R'hV3a0shW2pphX2t8hY4valshZ5vals'h[1xh\1yp%0p&0p;1p;2p;3p;4p;5p;Cp;Bp;Ep;<p;7p;8g003\j12Tg004Aj1ZTg004_j1cTg005Bj1WTg006Bj19Tg00Lbj2{Tg00C?j1`Tg00:dj2TTg051dj3pTg052;j1mTg006gj16Tg00Qjj21Tg000Nj23Tg00:Ej10Tg00MNj2JTg007ej37j1iTg008?j2KTg01BLj2DTg00NRj1RTg00OJj3gTg00PZj4hTg02Vcj2_Tg00Dej4XTg007Ej1^Tg005bj3lTg00I`j3\Tg00Caj2VTg00J=j1PTg0102j2OTg00bjj1kTg00cnj1jTg00dak209Tg011Sj2UTg01F4R0j14Tg01FTk208Tg01G7k307Tg01GTj4ITg01H;j1BTg01H`k206Tg01I>k105Tg01I\k102Tg01JGk201Tg01V]j4QTg01KMj2zTg009Mj2eTg01Koj2yTg01L[j3xTg01M:j4wTg01P1j2FTg00DCj1vTg00?Ij2HTg0677j2bTg01NTj2@Tg01=5R1j2[Tg00anj1uTg00nDj5]Tg00o=j2aTg01gNj3dTg04Qhj3tTg067\j4sTg068Xj4rTg069UlC|Tg06:UlB}Tg052Tj4qTg06;SlE~Tg06<Ok200Tg01m2l<oTg01mWk703Tg01n_k704Tg01n;j8nTf0R2#2#2p=Nf1R3/32#4p=5%92#9p=:%02#0p=S%02#0#0#0p=Y%02#0#0#0#0#0#0#0p=f%02#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=>g00GCR4?732p=?%22#2#2#2#2#2#2#2p=L%92#2p=Cg00=hR5?732p=A1e52p==P4P5P2P0P3f2R0f3R6f4R7f5R8f6R9f7R:f8R;M<op=Mg02:>R</12p=<P3g02:\R=g02;;R>P>g02;[R?P2g02<bK03p=;P5P3g02<;P2CQp=EP0P=P>P>P?P3P2K04p=GP6P=P>P>P?P0P3P2Gnp=8g00>FR=#2R@#2RA#2RB#ZRC#cRD#WRE%2BRF#NRG#ZRH#cRI%WIS00%9@RJ#Z/{IS01%`D\IRK1TC<RC=pD8#m15D9%:=#:#:#:#:#:#:#:#6RL'113I7g00?dRM#0RN#0#S#YRO#S#Y#f#>#>#>RP'?1J8Mp,3sp0RQ57I1J9N=7I;1KHQRRf9RS,KH'1f:RT,KHf;RU,5D'D%6B'D%LG#LRG#6,DR'11KHUf<RR,5D'D%6='D%2G#L#L#L#6'1%RTg05YW;gSg00E]RG%RUPSg05ZRCh%`ERVPGPTf>RWf?RX,3D/_NCX%^D9lDCRC9\DX,VE37PGPU1KHXf@RY,5D'D,THPOCX1VEW57VfAROPY15DOS02%6@R@%PORZ'O%k@p,5modelR[#jR\+09R]'US03PXPWf=S04PR13IWR^/?P%4^R_%9B#C#6RB'AR`%i4Ra%i5Rb%43%42'A1?3220832407X\4X[4R4P^P_%=_PPPB%=BR_M9MPSCIR^P`fBRc,3DRd#BRe%4d#<Rd13IYRf#BRg%4f#<Rfg02J5Rh#^Ri%WhRh20653Rj&055Rk&025RlP52015=Rmg02KaPmCQ';1zl?R?P2P0g02=BRng00KARo'e1y20=7nodAx5<3CwRob5b6b7X05Rn1A22^05RpP2fERq,5DRrO1b2b4b3b1P^P`PePdPgPfPiPhPjPkPl1F5</Em,;lR<%v>R>Pl1F5L,Em,;lRdP>AGl<dC8C8P?Pob5b6b7X05%<2Re113LR`%<0R^110LRL'H[[^05P2PrP0PWO3b2b4b3b1PUPSP;P:P9P8P6P0P3P2Q00Q0113I0%SP#f#>#>RW#S#Y#>#>#>Rr'?1J6M=7IQ1J7N=7Iq1J8WfGRW,5D,TH57I%R9g04n<;g8PG%R:P8g04o7ChPGP9fIfJRq,3D/_NCXA\DqC,VE57VfK,5DRV%CARA#2#9#6RC'b11VC1@CV'[P1fLRV,5DRN/1C1@CNg02>kS05PT%C=#N#:#C#9#N#:#C#N#6,THS06PS%uGS07D]/a[fMRH#P,O@/U]5dGP215DHR=/1CfNRNPH15DNRQ%PN,O@/U]PRPUPT13IRRM/?r%4MRs%NJ#9#C#6RJ'ARtPaPbP4PMPs%=sPrPJ%=JS08M9MPSCIRsPt13IVRV/?P%4VRM/ABRuPaPbP4PVPM%=MPPPBP_M9MPWCIRWPufPRM,3DRV#BRv%4VRV#<Rw13INRx#BRy%4x#<RxPgPfPnPpP2fT,5DRpO1b2b9b4b3b1b8PsPtPWPuPvPwPyPxPgPfPiPhPjPkPlP<P>Pl1F5CS09,Em,;lRnP>AGl<nC8C8P?Pob5b6b7X05113CRz110CR{,H^[\e^05P2PpP6P9O3b2b9b4b3b1b8PSP;P:P9fCR|PcP8P7P6%9FRF#2#6R},bQ11Q}1@}Q'[P1fOR1,5DR~/1}1@}~%PM,O@/U]9tMVP211V}fQRM15DMR]%=]S0:13IXRX/?r%4XR@/AJR~PaPbP4PXP@%=@PrPJQ08M9MPRCIRJP~13I1R1/?P%41Rr/ABR@PaPbP4P1Pr%=rPPPBP_M9MPqCIRqP@fS,3DR_#BRB%4_#<R_13IMRP#BRr%4P#<RP13I|RI#BR1%4I#<RIPiPhPjPkPlP<P>Pl1F5}R4,Em,;lRbP>AGl<bC8C8P?Pob5b6b7X05113}110},H^[\e^05P2fW,5DRDP6P9O3b2b9b4b3b1b8CsWEP2O11@}VPMP]Q0:PJP~PqP@PBP_PrPPP1PIPiPhPjPkPlP5P4g02=bR4PmCQ,;lP>PlPnP>%9F#6RF,F5/Em,;l=GlnC8C8P?Pob5b6b7X051@}211F0/H{\z[^05P2PDP9PSO3b2b9b4b3b1b8CrWCP2O1n200100000021100011000b:MC|WDP2O11@C=PNPHPQ%=QPsPtPWPuPvPwPyPxPgPfPiPhPjPkPlP5Q09P4PmCQ,;lP>PlPdP>%CA#6RA,F5/Em,;l=GldC8C8P?Pob5b6b7X051@C211A0/HL\`[^05P2PpP9PHO3b2b9b4b3b1b8P|PcPOPRPUPTPSP;P:P9P8P7P6MB}WBP2O1n200100000021100011000b:WKW<WAWSWRWQW>XNKWUWZPOPYQ02Q03CqeME~Q05Q04Q06PRQ07D]/a[200Z\5dGeWLWJW;W@WIWHWGWPWOW=W?WFWMWTWYXXEWWWVo"). Qed.

End UTail.
