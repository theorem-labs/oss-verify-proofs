(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO and vvar pages; writev's channel-reader flag; recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy). *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibTail SymCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout SymExec RefNodes RefNodesFS PureModel RefMemcpyLib LibWritev.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2ExitBase O2Exit O2MemcpyBase O2Memcpy O2Memchr O2Strnlen O2Startup O2StartupFacts O2MainEntry.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2OpenFail_defs O2OpenFail_tail O2OpenFail_tail2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2OpenFail () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI47Corelib5Lists7ListDef6Forall00C47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z:mod_uniqueC59OSSVerify5KrLib6Common8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib5Lists4List2InC46Stdlib5Lists4List8nil_consC47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List<firstn_skipnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail6model0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathK47Corelib4Init5Logic4True01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenAopenat_plain_nameC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib6Common7FileSim<path_eqb_neqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec8dot_pathC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8dot_pathC47Corelib4Init5Peano2ltK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib2O2;O2MainEntry8main_strC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib4Init3Nat3addC59OSSVerify5KrLib2O2;O2MainEntry2p1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib6Common9CliDriver3Amb6a_drawC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb5a_uidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb7a_hwcapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib6Common9RefLayout:lay_bsb_nwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesI47Corelib4Init5Peano2le00C59OSSVerify5KrLib6Common:MuslStrlen?read_word_stackC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9w_add_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7ArgvEnv>rdn_wmem_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7ArgvEnv4wmemC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t03C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib2O29O2StartupDmain_entry_rdn_aboveC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M5phdrsC1@~~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail3ENVC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib2O2;O2MainEntry=main_str_fitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry6blobs0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail?errno_ret_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2@O2OpenFail_tail27of_tailC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib2O2?O2OpenFail_defs3srAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail8path_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail:path_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail=model0_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail;model0_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail:model0_fd2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail:path_nonulC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail9model0_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry<main_regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2E0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry<main_know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry5vals0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry5auxvpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry3rndC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;log_below_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?mem_denot_aboveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_winC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs5STOPSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry7sr_mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry7kn_mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsI47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_regsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC69OSSVerify5KrLib6Common9CliDriver8SymDrive;regs_set_a0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFailCref_open_fail_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive:v_addi_pc4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail;openat_regsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC59OSSVerify5KrLib6Common7FileSim3mrbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9read_cstrC46Stdlib5Lists4List@firstn_length_lec59OSSVerify5KrLib2O2:O2OpenFail9In_firstnC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List:firstn_appC59OSSVerify5KrLib6Common7SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FileSimHread_cstr_toolong_of_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFailAafter_openat_failC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail9of_blockAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesFSDrz_openat_toolong_atC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC69OSSVerify5KrLib6Common9CliDriver9SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFail;model0_pureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result00K4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result02C4ELinuxProcessSemantics?LinuxProcessSem5State<ENAMETOOLONGK4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result01C59OSSVerify5KrLib6Common7FileSim@read_cstr_of_rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesFSBrz_openat_empty_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOENTC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupc59OSSVerify5KrLib2O2:O2OpenFail:path_plainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesFSCrz_openat_absent_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFailEref_open_fail_toolongC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFailCref_open_fail_emptyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2OpenFailDref_open_fail_absentC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1.
Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
  (2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["VP1"] "h04__x1h14__p1h27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with82Hah91Hh:2Heh;1eh<1zp;1p;2p;3p;4p;6p;7p;8p10000p4p70R0g000`R1p4p710R2p8P0p1001<p4p710p8P0p1001Zp4p7210p8P0p10027p4p710p8P0g002XR0p4p710R3p8p10036p4p70R4P2p8P4P3p8p1003dp4p710P3p8g004Cj18Tg004aj20Tg005=j1=Tg005bj29Tg006=j12Tg006bj1QTg007@j1:Tg007]j2LTg008Cj2HTg008`j23Tg009=j2ATg009]j1DTg00:;j2gTg00:cj27Tg00;?j3YTg00;cj1XTg00<Cj1VTg00<cj2UTg00=Aj1PTg00=_j1NTg00>Jj24Tg00>mj2MTg00?Pj1KTg00@2j3ITg00@Uj3?Tg00A8j4;Tg00Acj6JTg00BGj7GTg00Bkj2FTg00CMj2ETg00Cgj2OTg00DSj3>Tg00Dmj3RTg00ELj4STg00F>j2TTg00FXj2fTg00G;j3eTg00G^j3dTg00HAj2^Tg00H^j2]Tg00I;j6\TP1j6ZTg00I_j1[TP0j6BTg00Jaj2WTg00KGj2CTg00L1j2_Tg00L`j1`Tg00MXj7aTg00N<j7bTg00N`j8cTf0R0#=#=p=5g00ODR1f1R3g00ObP0C;p=6P3g00PIR4g00PhR2P2g00QHR5P0g00QhFap=1f2R6P4P2P2P5P3P0Fbp=<f3R7P4P2P2P5P6P3P0Gcp=@g00RHR8#8R9/00%=8#5#5#5#5#5#8R:,00R;'9R<P1%28R=#2#2#2#2#2R>#QR?%:3R@'LRA%8=R=%8>R>'HRB/3:RC/00X<1RDP11A@BREPDP@PB%D8RF13B3RG1g=>RHg00RmRI/7=10I>17IB[[RJ10I=RKg00SKRLAY=>3UW8R>10IB\L^8KRKp-0RLg00SgRM#XRN%VMRM1U13RO%P1RP%N1RQ14191M18R8'6,1Q141:R:,68,1QRR5<Q%K2RSPQP4P2P2P5141I141==I1?R==?18RT'6,1QP1PTg00TSP=C;,1Q5<QPQP4P2P2P5P7EJR2FGC@1FQ5R5P0P6g00U:R4g00UZRU'E1O06=>4UdAR1I3CSRUb3b6b7X01W110IG17GB'9/T6\<^01^1LP0f4R<,3BR4,7B104I'9P<P7O3b2b4b5PHPJP>PKPNPMPOPPP11f18g00V:141F9e1==d1TC;,1QP5PUb3b6b7X01%:01^BF13B0']5>1^01P0P<O1b2b4b5E\A>1GEP113B6PDPHPJP>PKPNPMPOPPPQA<Q2RPSA?1=:/6T,1QC@P5PUb3b6b7X01X1L193;10CG[^01^1LP0f5RL,09PLP<O3b2b4b5%:6/ABP0EZb9PA%[@EB1W?@,C?1_?@EB%`3,C?,0CeW:X;1o"). Qed.
End VP1.

Section VP2.
Lemma In_firstn : forall {A} (l : list A) n x, In x (firstn n l) -> In x l.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["VP2"] "h01lh11Ah21ah32l'h41Hh52H0h61nh71xp;1p;3p;2p;4p;6p200R0g00VaR1p4p710p8P0g000`R2p4p710p8P0g00W8p4p710R3p8P0g00WUR4p4p710p8P0g00X4R5p4p710p8g00<Cj13TP4j32TP1j30Tg00XUj34Tg00Y3j31Tg00F>j25Tg00YPj49Tg00Yoj38TP5j37TP2j66Tf0R2#3R5g00ZIf2R1f3R4f1R6=241702f4R7#3R8A2714A4714517f5R9?012X08%36R8g005bA14169042A0764A0761'5R:[A0421A0426'5A17419076[R;A19749091\:P4P1P6P2C9P2n2001000000120000000X21W3X05X13P;^21^38^05^13P2P9A2947R2A4947R3P1A0912A0913;86O5b5P4A7714E6W4W7W6W0X10o"). Qed.
End VP2.

Section VP3.
Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["VP3"] "h04__x1h12Heh27__arithh34__ffh48__varmaph55__with61ep;3p;1p;2p;5p;4p;7p;8g00Vaj3WTg009]j1VTg00Zhj2GTg00[Ij1ATg00[hj2=Tg00\Qj3PTg00]:j3LTg00]cj2FTg00;cj1CTg00^Oj37Tg00<Cj1@Tg00<cj2?Tg00=Aj1>Tg00=_j1UTg005=j15Tg006=j16Tg004Cj12Tg00>mj2OTg00^oj5ETg00?Pj1DTg00A8j4;Tg00N<j7HTg00N`j8ITg00Bkj2BTg00CMj2JTg00Cgj2KTg00DSj34Tg00Dmj3MTg00ELj4NTg00F>j2:Tg004aj2<Tg005bj2QTg00>Jj2RTg00MXj7STg00BGj7TTg00ODR0f0R1'Rp=3P0f1R2g00V:P1C;p=9P2g00PIR3g00PhR4P4g00QHR5P1g00QhFSp=0%51#5p=1f2R6P3P4P4P5P2P1FTp=8g00_S9W01g00SgR7g00RHR8#V,G0g00`UR9#A,=05P01=095L0g00a4'FR9%C797799779977937%@71?02%>0%U0R7P3P4P4P5%58R9#6R:#6R;#2R<#31O08R='9,07%5:#2R:#3/9=,07%6;#2R;#3/9=,07%68#5#1#2R>#3/9=,07P7P3P4P4P5DE587587587587%D4P7P3P4P4P5P0%28R8#3g00ObR4P=C;,07P0P=P4%19#1#1#1#1#2R9#3C;,07FHGI1B75P1P6g00U:R7g00UZR5'J1K16=475dg00Rm=M02CNb3b4b5X00A40<1A40:1A40;1A40>1g00a`':':':':1<821<29'Q[^00P1P6P2O2b2W1X60o"). Qed.
End VP3.

Section OpenFail.
  Context {AMB : Amb}.
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
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).
  Definition model0 : Model :=
    with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso a_draw)) (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0))).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma model0_halted : m_halted model0 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "p;1p;2g006=j10Tg006bj15Tg00b=j12Tg00b`j11Tg00?Pj14Tg00CMj23Tg00RH#0#0#0#0#0#0#5#2R0#1%40'3o"). Qed.
  Lemma model0_lazy : m_vm_lazy model0 = [].
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "p;1p;2g006=j10Tg006bj16Tg00b=j12Tg00cBj21Tg00<Cj15Tg00;cj14Tg00CMj23Tg00RH#0#0#0#0#0#0#6#2R0/10R0#5%40'3o"). Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "p;1p;2g00b`j17Tg006=j10Tg006bj12Tg004Cj11Tg00Jaj26Tg00cbj15Tg00dZj23Tg00CMj24Tg00e<R0#7g00RH#0R1#0#0#0#0#0#2%11'6#5,30'4o"). Qed.
  Lemma model0_rd2 : m_channel_reader model0 = true.
  Proof. exact a_reader. Qed.
  Lemma model0_fs : m_fs model0 = fs0.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "p;2g00CMj20Tg0036p,3fs0'0o"). Qed.
  Lemma model0_pure : md_pure model0.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "p;1p;2p;4g006=j10Tg006bj19Tg00b=j15Tg00b`j14Tg00?Pj18Tg00CMj21Tg00cBj27Tg00<Cj12Tg00;cj13Tg00f4j46Tg00g3g00RH#0#0#0#0#0#0#9#5R0#4%80'11700R1#2%31'1%20%30'1C6o"). Qed.

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "p'0h01Hh12H0h21li001lh32H1h42Hlh52Hxh61ah71eh82H2h91xi011xh:2Hnh;2_Hh<3_H0h=3_H1h>3_H2h?1vp;1p;3p;2p;6g004Cj1<Tg006=j16Tg006bj1DTg00b=j1KTg00<CR0j1BTg00;cj1HTg00^Oj34Tg00glj2>Tg00hLj1=Tg004aj27Tg005bR1j25Tg00hlj1CTg0027R2j33Tg00Jaj2JTg00Vaj3:Tg00ihj1;Tg00jAj1ITg00DSj30Tg00kEj2GTg00l9j2FTg000`j6?Tg00lPj2ETg001Zj68Tg002Xj69Tg00CMj2@Tg005=j1ATf0R3#6#6p=1%A3#Ap=2p,3Hvag00RHR4#<%64#1R5#DR6#KR7#BR8p,3a0sR9p,4pathR:%H8R;548R<548R='>#=R>'7%65#1#1#1R5#<,7>'5R>%C=%65#1#1#1#1#1#<'7R51>73#=%24#2#2#2#2#2#2#2#<'7X68=38=R4g00Rm,J6R6=:73#;X68R?=38=R@g0000RAg00U:RB%I3g00loRC30g00mO,G3=0BC'5X6A1F8=33RA'5RC'5RB'5RD'5P1P>PDA:76:#;REP3P1P5PBPEP3P1P4PCPEP3P1P@PAPEP3P2P8P?%B8R1f1RF;0=PE[PFA01;=RGP1P;P0P8p-0P3g00SKg00a`RHn10110000020020000000X71RIg00nPRJP=P3E?PH1EE3RKb1X0GP3O1W0A:76F#;RGA38?FRLf3RMf2RN548RO=01=f4RP=48MRQ=01=P1P1P0P8P1P3f5RRP3n10110000020020100100X71RSA48RPRTP=P3E8A01P<P1P8P0P8P8P3f7R0PFn10110000020020100100X71RUf6RV=48RRRP=PFE8A08V9A0809P3f8RW=089P8P9f9RX=01<RYf;938?RZPE]4^5G[X28A01W<P3PYP1P<A:769#;R6PE^4L]5X21A38?<P2P8P?A01F<PE[P3A01;<R2P1P;PIPJP<P3E?PHPKb1X02P3O1W0A01O<A01Q<P1P1PSPTP<P3E8A01P;P1P8PUPRP<PFE8A08V:A080:P3A08W:P8P:A01X;R:PE^1Z^0G[X28A01W;P3P:P1P;PE^1L^0EX21A38?;PFW8X3Ef:R?P3E9b8W1PXP3E9b1W0P3O1b0P3O1b0W3P3PNPFO3W3X1LX0GX21X98PMPNPFP3O4n200210000000020041101100000000A013<PE[X21P<O1P31@1<O1b0W4X56P?P3E9b3W1PXP3E9b1W0P3O1b1P3O1b1W0P3PNPFO3W0W4W5X21X98PMPNPFP3O4n200210000000020141101100000000A013=PE[X21P=O1P31@1=O1b0X>AX:@PFP3O2n2001000000121000000X0CX=4PFP3O2n2001000000121000000X0BX<5PFP3O2n2011000000121000000X0DX;>PFP3O2n2011000000121000000b?o"). Qed.
  Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "p'0h01Hh12H0h21li001lh32H1h43Hl'h52Hxh61ah71eh82H2h91xi011xh:2Hlh;2_Hh<3_H0h=3_H1h>1vp;1p;3p;2p;6g004Cj1<Tg006=j19Tg006bj1BTg00b=j1KTg00<CR0j1@Tg00;cj1FTg00^Oj35Tg00glj27Tg00hLj18Tg004aj24Tg005bR1j26Tg00hlj1ATg0027R2j33Tg00Jaj2JTg00Vaj3ITg00ihj1HTg00jAj1GTg00DSj30Tg00kEj2ETg00l9j2DTg000`j6>Tg00lPj2CTg001Zj6:Tg002Xj6;Tg00CMj2=Tg005=j1?Tf0R3#9#9p=1%?3#?p=2p,3Hvag00RHR4#<%94#1R5#BR6#KR7#@R8p,3a0sR9p,4pathR:%F8R;558R<558R='7#8R>'4%95#1#1#1R5#<,4>'6R>%A=%95#1#1#1#1#1#<'4R51773#8%24#2#2#2#2#2#2#2#<R4'4X68R?=38=R@g00Rm,J6=I73#HX68=38=g0000R6g00U:RA%G3g00loRB30g00mO,E3=0AB'6X661D8=33'6R6'6RB'6RA'6P1P>PA177:#8/44RCP3P1P5PBPCP3P1P@P6PCP3P2P8P?%@8R1f1RD;0=PC[PDA01;=REP1P;P0P8p-0P3g00SKg00a`RFn10110000020020000000X71RGg00nPRHP=P3E>PF1CC3RIb1X0EP3O1W0177D#8/44REA38?DRJf3RKf2RL558RM=01=f4RN=58KRO=01=P1P1P0P8P1P3f5RPP3n10110000020020100100X71RQA58PNRRP=P3E:A01N<P1P8P0P8P8P3f7R0PDn10110000020020100100X71RSf6RT=58PRPP=PDE:A08T9A0809P3f8RU=089P8P9f9RV=01<RWf;938?RXPC]4^5E[X28A01U<P3PWP1P<1779#8/44R4PC^4J]5X21A38?<P2P8P?A01D<PC[P3A01;<R2P1P;PGPHP<P3E>PFPIb1X02P3O1W0A01M<A01O<P1P1PQPRP<P3E:A01N;P1P8PSPPP<PDE:A08T:A080:P3A08U:P8P:A01V;R:PC^1X^0E[X28A01U;P3P:P1P;PC^1J^0CX21A38?;PDW8X3Cf:R?P3E;b8W1PVP3E;b1W0P3O1b0P3O1b0W3P3PLPDO3W3X1JX0EX21X98PKPLPDP3O4n200210000000020041101100000000A013<PC[X21P<O1P31=1<O1b0W4X54P?P3E;b3W1PVP3E;b1W0P3O1b1P3O1b1W0P3PLPDO3W0W4W5X21X98PKPLPDP3O4n200210000000020141101100000000A013=PC[X21P=O1P31=1=O1b0X=6X:@PDP3O2n2001000000121000000X0BX<5PDP3O2n2011000000121000000X0AX;>PDP3O2n2011000000121000000b>o"). Qed.
  (* [comment removed for export] *)
  Lemma path_plain : path <> dot_path -> openat_plain_name path = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "p'0h01Hh12H0h23Hddh33Hslh41ah51bh61eh71li001lh82_Hh92H1h:3Hndh;3Htlh<3_H0h=3_H1h>3_H2h?1pi011ph@1vhA1xi021xp;1p;3p;2p;6g006=j18Tg006bj1PTg00b=j1KTg00<CR0j1ITg00DSj30Tg00ihj1FTg004Cj1<Tg00;cj1DTg00^Oj35Tg00glj2ETg00hLj1CTg004aj2;Tg005bR1j26Tg00hlj1STg0027R2j39Tg00Jaj2RTg00Vaj3QTg00jAj17Tg00kEj24Tg00l9j2OTg00nlj1NTg000`j6MTg00lPj2LTg001Zj6BTg0102j2>Tg010Oj1:Tg010mj2@Tg00CMj2GTg011Kj3JTg002Xj6ATg005=j1HTf0R3#8#8p=2%H3#Hp=3g00U:R4g00loR5703p=1g00UZR69043p==P4P5f3R7f2R8f1R9P3EAp=?g00RHR:#8#2R;#PR<#KR=#IR>p,4pathR?g012KR@30#Fp,3Hva%<:p,3a0s%D>RA95>?RB55>RC,E>#CRD';%8;#2#2#2R;#<,;D'6RD%SC%8;#2#2#2#2#2#<';R;1E=3#C%3:#3#3#3#3#3#3#3#<';X4>=9>CR:g00Rm,R<=Q=3#FX4>=9>CR=g0000R<%73#1g00mORE,43#1'6X4<RF1O>C39RC'6R>'6RG'6RH'6P1PDPH%N?#=RIP3P1P;PGPIP3P1P:P>PIP3P1P=PCPIP3P2P<PF%I<R2?09BPI[P3%D<RJ=02BRKP2PJP0P<p-0P3g00SKg00a`RJn10110000020020000000X62g00nPPBP3EMPJ1LI3b1X0KP3O1W0%79#1RK149E#1'6P1%78#1148E#1R1A9<F8f4RJ=5<7=02BPI[[P3%7J#1f5RJ/4E#1A9<FJf7RJf655<=02Bf8RF=5<J=02BP2P2P0P<P2P3f9RJP3n10110000020020101100X62A5<JFPBP3EBA02FAP2P<P0P<P<P3f;R0P9n10110000020020101100X62f:RF=5<JPBP9EBA0<F?A0<0?P3f<R0=0<?P<P?f=RF=02ARJPI^21^3K[X?<A020AP3PJP2PA%7?RA#1RJ14?ERE#1R0PI]2]3X72g013N,4?RK/>E#:%:3'@#=X541>K3#:%:5RK'@#=X541>35#:/@K#=X541G4614?@fW9J?@C?PEP3C?PAP9C?PIeX20X3Jf>P3EAb9W1PFP3EAb1W0P3O1b1P3O1b1W0P3P7P8O3W0W8W2W3P9P3O2n2001000000121000000W0X72XA<P7P8P9P3O4n200210000000020041102100000000A023BPI[X72PBO1P31G2BO1b0X;CX>=P9P3O2n2001000000121000000X0>X=:P9P3O2n2001000000121000000X0GX<;P9P3O2n2011000000121000000X0HX8DP9P3O2n2011000000121000000b@W:o"). Qed.

  (* [comment removed for export] *)
  Lemma path_facts :
    rdn RSEGS mem0 (p1 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 a0s path envv))%Z
    /\ (bv_unsigned (p1 a0s path envv) <= bv_unsigned sp0 + 2107576)%Z
    /\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (p1 a0s path envv) + Z.of_nat (length path))) 8 = Some t8.
  Proof.
    destruct (main_str sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & _).
    destruct (me_word_after sp0 [a0s; path] envv tid regs0 mem0 ME Hva Hve Hvsp RSEGS 1 ltac:(cbn; lia)) as (t8 & Hr8).
    cbn [nth] in Sr, Slo, Shi, Hr8.
    exact (conj Sr (conj Slo (conj Shi (ex_intro _ t8 Hr8)))).
  Qed.
  Lemma path_fits_task : (bv_unsigned (p1 a0s path envv) + Z.of_nat (length path) + 1 <= TASK_SIZE)%Z.
  Proof. exact (me_argv_fits sp0 [a0s; path] envv tid regs0 mem0 ME Hva Hve Hvsp 1%nat ltac:(cbn; lia)). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem ref_open_fail_errno : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
    vals_ev vals 2 = p1 a0s path envv ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x37344) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof path_len as HPl.
    destruct path_facts as (Sr & Slo & Shi & t8 & Ht8).
    pose proof (u64_range (p1 a0s path envv)) as Hpr.
    pose proof (main_str_fits sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia) Hfits) as Hfit1.
    cbn [nth] in Hfit1.
    rewrite <- model0_fs.
    apply (of_tail sp0 (blobs0 a0s path) model0 Hvsp model0_halted model0_lazy model0_fd2 model0_rd2
             path (p1 a0s path envv) t8 vals R M path_nonul HPl HL P0 P2).
    - rewrite P38. apply errno_ret_range. exact He.
    - exact Slo.
    - lia.
    - exact Hfit1.
    - exact HR.
    - exact HK.
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove.
      rewrite (u_small (bv_unsigned (p1 a0s path envv) + Z.of_nat (length path))) by lia.
      rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma of_blockA : forall T,
    (forall vals R M,
       length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 a0s path envv ->
       vals_ev vals 1 = p0 a0s path envv -> vals_ev vals 5 = tid ->
       regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
       (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
       (forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> M x = mem0 x) ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x37340) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17618) mem0 (seg_rom RSEGS)) model0) T.
  Proof.
    intros T HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok sp0 a0s path envv tid regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv tid regs0) with (ENV (vals0 sp0 a0s path envv tid regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 a0s path envv) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 a0s path envv) by reflexivity.
    assert (P5 : vals_ev vals 5 = tid) by reflexivity.
    clearbody vals.
    pose proof model0_halted as Hh.
    run_blk_keep scr0 38%nat.
    apply (HA vals); try assumption.
    - intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x6b000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - intros x Hx. rewrite EQM. apply (mem_denot_out_win (ENV vals) mem0 _ 0%nat);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; unfold WIN; exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 a0s path envv -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 a0s path envv
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "h01bh12b1h22b2h31nh41Hh52HRh62P2h71Rh84valsp;1p;2p;4p;3p;5p;6g006=j15Tg006bj1FTg00b=j18Tg00<Cj1PTg005=j10Tg01X7j2OTg00[Ij1GTg01Xcj2NTg018Xj4LTg00DSj31Tg01Ygj1DTg01_<j3ITg004Cj16Tg01[@j3?Tg031Yj2>Tg00Jaj2CTg00KGj23Tg032Rj2=Tg005bR0j2HTg0331j2:Tg034:j24Tg00CMj2BTg02Bbj1ATg035Cj5;Tg002Xj69Tg036Gj3MTg01\jj1JTg01P4j4@Tf0R1#5#5p=2g00ODR2g00RmR3711p=<%01#0p=E%01#0#0#0p=K%01#0#0#0#0#0#0#0p=7g00RHR4#5R5#2R6#5#2R7#FR8#8R9#P%05R5#FR:/O9f1R;g00`U#G#GR<'Np,3AMBp,3a0sp,4pathp,4envvCLR=519f2R>#Dg01oER?;I;%06#6g00nPR65?:R@,>>RA%04R4#0RB#5#2#6RC,C8RD519%55#6=?:6RE,>>RFg036kRG519RH%05#6=?:6R5,>>RI=19=RJ%24#6=?:6R6,>>R:,38g037eR4'=#<RK'HRL'HP9f3RM#DRN1:?@'4A191DX091B9D%AC,4N=19DePAPNP?P>P@P1D;E9PHPLP91:?E,4NA191GX09g038lRL%81RH%8;R@P0%8>?1;113M>13M;512R0[13>;13>1512%8M?1>;[RAf4#8?1M>\0AM>;1P1n2001000000120000000W2W1W3PA^2@^1H^3LP1P8%EB#K#7#7#7#7#7#7#2#0#E#2#6RB,C8PG138G,B2O4b4%AB,4N=19GePFPNP?P>PEP1D;E9PJPKP91:?5,4NA191=X09P;%J<,4N=19=ePIPNP?P>P5P1D;E9P91:?6,4N1381/=4#<X091B23%57#2#2#2#2#6R7,C8,38/=4#<d%A7,4N,38/=4#<eP:PNP?P>P6P1D;E9C@C@C@W5W6W7W8o"). Qed.

  (* [comment removed for export] *)
  Lemma after_openat_fail : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 a0s path envv ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x37340) 4) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "h01nh13HL0h22Hah37__arithh44__ffh56__sat3h66__sat4h78__varmaph85__with91bh:4cstrh;1xh<2HKh=3HK2h>2HLh?2HRh@3HR2hA6HabovehB2HehC1MhD2P0hE2P2hF1RhG6__sat5hH6__sat6hI1ehJ4valshK1yp&0p;1p;2p;3p;4p;5p;7p;8p;6p;<g006=j12Tg006bj1JTg00b=j1QTg00<Cj1dTg005=j18Tg01X7k203Tg00b`j1{Tg004Cj14Tg004aj2CTg005bj2hTg00glj27Tg01Xcj23j1cTg00DSj31j1]Tg018Xk402Tg01Ygj1ITg01_<j3TTg01`Lj4XTg00KGj2VTg00H^j2tTg00Jaj2UTg01[@j3sTg00L`j1BTg039Jj3^Tg01a\j1nTg01bXj5mTg01cQj2lTg01dFj1jTg01ePj2iTg01fPj3gTg00;cj1OTg00^Oj3DTg01iCj3fTg03:Ej1eTg03;Lj2NTg00CMj29Tg03<Sk70=Tg00Y3j3HTg03=_j2aTg03>gj2`Tg03?nk80<Tg018Aj2LTg00[Ij10Tg02ALk30;Tg014HR0j2GTg00:cR1j2:Tg00hLR2j1=Tg01IYk206Tg01J<k301Tg01JYj4PTg01<hj1ZTg00:;j2STg008Cj2YTg00;?j3RTg014`j1~Tg00=Aj1zTg00=_j1yTg00>Jj2>Tg00Bkj2xTg00Cgj2uTg00Dmj3vTg00ELj4wTg015>j4WTg03A:j4bTg002Xj6?Tg01nBj2rTg03BGj3|Tg03CTj1}Tg000`j6[Tg01\jk100Tg034:j2pTg03D8j7oTg03EBm<04Tg03FHk205Tg00A8j4_Tg00G^k307Tg00@2k308Tg03GCk309Tg01Mol<MTg00MXj7kTf0R3#2#2p=@%83#8p=5%03#0p>0?%03#0#0#0p>0>%03#0#0#0#0#0#0#0p=Fg00ZIR4f1R5;13p=;g00U:R6g00UZR7713p=AP4f4R8f3R9f2R:P5P3E?p=<P4g00ODR;P0P2P1g01RRR<g00`UR=g00RmR>P9P:P5P3M<Mp>0:P4P;P3P2P5P:P9P8f5R?f6R@f7RAf8RBM<Mp=\1C>3p=6P;P5g00TSP3C_p=KP5g00PIg00PhRCPCg00QHRCP3g00QhFkp=EP4P;P0P2P1P<P?P8P9P:P5P3M<Mp=qg00RHR<#2R1#2R2#2R0#2#@RD#JRE#QRF#d%81RG#JRH003F%J0#Q#{R0\F%4</C9%8<#5#5#5#5#5#4,C9'h17F9&0?=R9$0>#F#F#F#FRI';138=p,3sp0R851F13?9p,3AMBp,3a0sRJp,4pathRKp,4envvH02RL51F%I@g01oERM;T?g01S4RN%IAP?g020@ROCX1VE81VE3'CPBP5O1p,4mem0P5O1510[^;FPF%8<#2#8#5#@#5#2#8#@#@#@#4R<%42R0'tRP,UEg0233f9RQ%2G#4g00nP5sHRHf;RR#BRS3^P3PB%nNDmg00g3'l%jKp,3fs0'i5gNX9FPQf:RT#B%OFRU5DFRVp,3AMB?fJK#eRKPMPBPI1N3M#AX041967R71NIM#Ad17FQR6P?D<P:K0=AHFQV#c/aK?TMBPNPTADFSURSPKPBPOPI1`3O#AX04P71`IO#Ad17FTRVP@D<P:L0<PNAHFTS#c/aKPBPOCXf<RO%BORK=DFURS9HFRRNA^THKPQPB17FRRB17FS'L%0IRQ,;3X04PIf=#BRH=DFURU,7F,L3/;QX04194QPBPAD<17FNB0;FRSD<PF13R=A1F38X9FP@13N=PRPSP=PI1G=3X041G=I%52#2#4R2,:>R@19;>PIP219;2R8H0:1;BI%=BRQ=1;2RJ%]4RW%];RX%=5%=351;1;5320653401XK4X;4RYPBPQ19;QPIP2P8M9\PACPRQPJ17FORZ#ZR[%=Z#6RZ%41R1%8G#2#4RG'SR\1:>1R]%6G1Y1GR^,:>[[R_%61R`g00SKRaAR1G5UW2RG%6^\a^2`R^g00SgRb#ORc%dbRb%~;Rd%z;Re%y;Rf1>;>Rg1>;2Rh'K'E1xfCRCP3P:P71u3:#AdAv;>5CwR7b4b7b8P@P3b3b5b6b:b1CWPBPAD<CbE?P4PBAHFOU/33=1FHX04RUP41rB=PUPF13S=A1F3HX9F19FK1LB=,3NA|RS=E?PB%}BE[PIPAE[R=PF13R9A1F3LX9FP?13N9PRPSP9PI1G93X041G9I1:12R4P9P119;1PIP2P8EqPQPJP[PZP\P_PGP^PcPbPdPe1>;1RZ/Kh,EfPCP7b4b7b8P4P3b3b5b6b:b1CWPBPAD<CbE?%INRNPMPTPK&00IRTP5P=1pNT=1FKeFoP3P:N<04b=b@1UE<00501;6I%=6R:=1;2RKPWPXPYP6P:19;:PIP2P8M9\P?CPR?PK%ZVR8%=V#6RVP\P_PGP^PcPbPdPeP;Pgg00Ob1>;<RgC_,EfPCP7b4b7b8%6<P3b3b5b6b:b1P?PKP8PV%4DRD,S1%6D1Y1DRV,:>[\]AR1D5VaX2`%6V\a^2`P\P_PGP^PcPbPdPe1>;0:07;gB08;ZE'K,EfPCP7b4b7b81:PVP3b3b5b6bGbHb:b1609<E?WAW<W?WEWDW>WBWCWFWJXI;o"). Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_toolong :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17618) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlong. apply of_blockA. intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 a0s path envv)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x37340) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_toolong_at RSEGS R _ M model0 ECALLW _ model0_pure HF is_ecall_ECALLW
              ltac:(rewrite A17; reflexivity) A12).
    - rewrite A11. apply (read_cstr_toolong_of_rdn RSEGS M _ (firstn 4096 path)).
      + rewrite firstn_length_le; lia.
      + intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
      + pose proof path_fits_task. lia.
      + replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
          by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
        apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
        rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_empty :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17618) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hnil. apply of_blockA. intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 a0s path envv)) as Hpr.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x37340) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_empty_at RSEGS R _ M model0 ECALLW _ model0_pure HF is_ecall_ECALLW
              ltac:(rewrite A17; reflexivity) A12).
    - rewrite A11. apply (read_cstr_of_rdn RSEGS M _ []); [cbn; lia | intros [] | pose proof path_fits_task; cbn [length]; lia |].
      replace (length path + 1)%nat with (length ([] : list byte) + 1)%nat in Sr by (rewrite Hnil; reflexivity).
      replace (path ++ [Z_to_bv 8 0]) with ([] ++ [Z_to_bv 8 0]) in Sr by (rewrite Hnil; reflexivity).
      rewrite <- Sr. apply rdn_agree. intros j Hj. cbn in Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_absent :
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17618) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlen Hne Hnd Hfs. apply of_blockA. intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 a0s path envv)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x37340) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_absent_at RSEGS R _ M model0 ECALLW path _ model0_pure HF is_ecall_ECALLW
              ltac:(rewrite A17; reflexivity) A10 A12).
    - rewrite A11. apply (read_cstr_of_rdn RSEGS M _ path Hlen path_nonul); [pose proof path_fits_task; lia |].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - exact Hne.
    - apply path_plain. exact Hnd.
    - rewrite model0_fs. exact Hfs.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Corollary ref_open_fail_toolong_w :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (0x17618 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "h02H0h12b1h22b2h31nh41Hh51bp;1p;2p;3p;5p;6g006=j13Tg006bj18Tg00b=j14Tg00glj2DTg01?Sj2=Tg00DSj35Tg00KGj26Tg036Gj3;Tg005=j12Tg004Cj19Tg00Jaj2:Tg01[@j3GTg00CMj2FTg01a\j1ETg01bXj5CTg01cQj2BTg01dFj1>Tg01ePj2?Tg01fPj3@Tg03d>j1ATg000`j6<Tg00[Ij11Tf0R0#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0%30#3p=7g00`U#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0g00RHR1#3#7R2#8#4p,4pathR3'D'=g038lR4%40R5f1R6#4R7g005bf2R8#4?560g00ODR9f3R:/6816:635R;[16861680559%4:?586[R<f4#4?5:8\;A;860P0n2001000000120000000W2W1W3P<^27^15^34P0%32#7#8R2%31#2#2#2#3#2#2#7#7#2#2#3#7#9R1,:2R4g00nP9G21R11621,F9O4b0%42R2P1P2e754P2P4g01S4R4g0233p,5regs0P0p,4mem0%E4DCg00g3'B%>3p,3fs0'?3@X52%A6P1P0E<b0W4o"). Qed.

  Corollary ref_open_fail_empty_w :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (0x17618 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "h02H0h12b1h22b2h31nh41Hh51bp;1p;3p;2p;5p;6g006=j10Tg006bj16Tg00b=j13Tg00<Cj1ETg00;cj1<Tg00DSj32Tg00KGj24Tg036Gj38Tg005=j11Tg004Cj17Tg00Jaj29Tg01[@j3:Tg00CMj2DTg01a\j1CTg01bXj5BTg01cQj2=Tg01dFj1>Tg01ePj2?Tg01fPj3;Tg03eFj1@Tg000`j6ATf0R0#0#0p=5g00RHR1#0#5R2#6#3R3#Ep,4pathR4%<332g038lR3%30R5f1R6#3R7g005bf2R8#3?260g00ODR9f3R:/4814:632R;[14861480529%3:?286[R<f4#3?2:8\;A8860P0n2001000000120000000W2W1W3P<^27^15^33P0%02#5#6R2%01#1#1#1#0#1#1#5#5#1#1#0#5#7R1,92R3g00nP9:21R11421,D9O4b0%32R2P1P2e723P2P3g01S4R3g0233p,5regs0P0p,4mem0%C3DBg00g3'=%>4p,3fs0'?3;X52%@6P1P0EAb0W4o"). Qed.

  Corollary ref_open_fail_absent_w :
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes RSEGS (mkCfg (mkst regs0 (0x17618 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail ()) ["OpenFail"] "h01Hh12b1h22b2h31nh42H1h52H2h62H3h72H4h81bp;1p;2p;3p;5p;4p;6g006=j15Tg006bj18Tg00b=j14Tg00glj2QTg00[Ij11Tg01?Sj2;Tg00<Cj1:Tg00;cj1PTg00DSj32Tg00ihj19Tg00b`j1OTg03aBj2NTg00?Pj1LTg00KGj26Tg036Gj3BTg005=j13Tg004Cj1@Tg00Jaj2DTg01[@j3ETg00CMj2FTg01a\j1GTg01bXj5HTg01cQj2ITg01dFj1JTg01ePj2KTg01fPj3=Tg03fLj4<Tg000`j6MTf0R0#5#5p=7%10#1p=C%10#1#1#1p=A%10#1#1#1#1#1#1#1p=?%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=>%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00RHR1#5#7R2#8#4R3p,4pathR4'Qg00`U#1#C#A#?#>#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0';%:3R5%P3724#9g012K9254#9%O5p,3fs0R3/N4%L532g038lR5%40R6f1R7#4R8g005bf2R9#4?270g00ODR:f3R;/6916;732R<[1697169052:%4;?297[R=f4R>#4?2;9\<AB970P0n2001000000120000000W2W1W3P=^28^16^35P0%52#7#8R2%51#3#3#3#5#3#3#7#7#3#3#5#7#@R1,D2R5g00nP9E21R11621,F:O4b0%42R2P1P2e725P2P5g01S4R5g0233p,5regs0P0p,4mem0%G5DHg00g3'I%J4/K33=X82P>P;P9P7C<P1P0EMb0W7W6W5W4o"). Qed.

End OpenFail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
