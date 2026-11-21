(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from U/MainOpen.v for the budget-premise witness: the same statements and proof scripts over BudgetWit.Rzb.realizes; only the name tables change. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch input as a ProcInput. *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout StepTac SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame SymAux Spec RefNodes LibTail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefStartup RefStartupFacts RefMainEntry RefMainEntryN LibDiagKn RefPrintfFirst MainDefs MainWalk_defs MainSegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MainOpenB () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib5Lists7ListDef6Forall00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymAux7sregionC13~~~C47Corelib4Init5Logic6eq_indC46Stdlib9micromega5Tauto5eKindI46Stdlib9micromega5Tauto8GFormula00K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25s_logC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymAux;log_coveredC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen4regAC13~~~I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX28sidecond00C13~~~I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX27scripts00C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs2rAC13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr02C13~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr03C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry04C13~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init9Datatypes4list02I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26kentry00C13~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1Z01c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen2cAC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs3knAC13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24s_pcC13~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26sentry00C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs2rCC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen4regFC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs2rFC13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX28sidecond01C13~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen2cFC13~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2or00c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen3scFC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6EACCESC4ELinuxProcessSemantics?LinuxProcessSem5State6EMFILEC4ELinuxProcessSemantics?LinuxProcessSem5State6ENFILEI47Corelib4Init5Logic5False00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC4ELinuxProcessSemantics?LinuxProcessSem5State<ENAMETOOLONGC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOENTK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z:mod_uniqueC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec=bv_wrap64_modC13~~~C47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op205c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen4regUC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs2rUC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen2cUC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs3knUC13~~~I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd:and_elimF5C13~~~C47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathK47Corelib4Init5Logic4True01C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd:and_elimF4C13~~~I47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib7CatExec<cat_argv_ptrC13~~~C47Corelib5Lists7ListDef3nthC47Corelib4Init3Nat3addC47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsI47Corelib4Init5Logic2ex00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib3Amb5a_uidC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib3Amb7a_hwcapC13~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init5Peano2ltK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify6Proofs:boost_json:fuzz_parse3lib:MuslStrlen=argv_ptr_roomC13~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExecMbuild_stack_bytes_within_spanC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec8wrap_memC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC79OSSVerify6Proofs:boost_json:fuzz_parse3lib7StepTac<word_add_natC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec9u64_rangeC13~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S7u_smallC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U:RefStartupDmain_entry_rdn_aboveC13~~~K47Corelib4Init5Logic2ex01C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd:and_elimF2C13~~~I47Corelib4Init5Peano2le00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib:MuslStrlenBargv_word_readableC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd9ex_elimF1C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry8main_strC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec3rdnC13~~~K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C79OSSVerify:boost_json:fuzz_parse6images5Ubsan1M?loaded_segmentsC13~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC79OSSVerify:boost_json:fuzz_parse6images5Ubsan1M5phdrsC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun7vals_evC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen3ENVC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S7regs_okC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S7know_okC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib5Frame9frame_modC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen6frameAC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec4mkstC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I89OSSVerify6Proofs:boost_json:fuzz_parse3lib9BudgetWit3Rzb8realizes00~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry<main_regs_okC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry2E0C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry<main_know_okC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry5vals0C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry2p0C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry2p1C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry5auxvpC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry3rndC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive9junk_valsC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U>RefStartupDefs8canary_wC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX@junk_vals_lengthC13~~~C46Stdlib5Lists4List:length_appK89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX29sym_state01C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX28sym_execC13~~~K47Corelib4Init9Datatypes4prod01C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25carryC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S8sc_denotC13~~~K47Corelib5Lists7ListDef6Forall01C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26s_regsC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S9mem_denotC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S8log_flatC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S4flatC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26a_baseC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25a_offC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymAux<regions_flatC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymAuxAlog_covered_frameC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymAux6rdenotC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX:flat_introC13~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26edenotC13~~~C47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive5kreadC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive9kread_rdnC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26adenotC13~~~C99OSSVerify6Proofs:boost_json:fuzz_parse3lib9BudgetWit1U4RPFB9rz_run_lfC13~~~I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX25saddr00C13~~~I89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr00C13~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs5FUELMC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs6STOPSMC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs4scrAC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry7sr_mainC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry7kn_mainC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8ShapeAlg4TSetC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs3srAC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen6regA_wC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib4Scfg=hunspell_scfgC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen6cA_knAC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen4covAC13~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec4getrC13~~~C56Stdlib6ZArith6BinInt1Z5ldiffC89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26sr_getC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun7reg_valC13~~~C45stdpp9bitvector;definitions5bv_eqC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsI47Corelib7Numbers7BinNums1N00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib5Frame7outsideC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib7StoreOk9mem_growsC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen8path_lenC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen:path_nonulC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib5Frame6in_rngC13~~~K46Stdlib9micromega5Tauto8GFormula07C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX9rdn_agreeC13~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen:path_factsC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC45stdpp9bitvector;definitions4BvWfC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive;regs_set_a0C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24ridxC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX26sr_updC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec6regupdC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs6carryMC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX>edenot_add_litC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd:and_elimF3C13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive6rz_runC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs3srCC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs5noscrC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs4srC0C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen8rC_factsC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U<RefMainEntry6blobs0C13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymDrive8blobs_evC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun:sr_vars_ltC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX<env_app_regsC13~~~K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX23env01C13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun:kn_vars_ltC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX<env_app_knowC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX=vals_ev_app_rC13~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC79OSSVerify6Proofs:boost_json:fuzz_parse3lib9SymDriveX=vals_ev_app_lC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S9kentry_okC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen?errno_ret_rangeC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun<krange_introC13~~~K47Corelib5Lists7ListDef6Forall02C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S9scs_denotC13~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem<branch_takenC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs4scrFC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs4srF0C13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs4knF0C13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen6regF_wC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen8rF_factsC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen4covFC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs3srFC13~~~c99OSSVerify6Proofs:boost_json:fuzz_parse3lib9BudgetWit1U3MOB6frameU~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN=main_regs_okNC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN2ENC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN=main_know_okNC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN8evN_argcC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX22evC13~~~C79OSSVerify6Proofs:boost_json:fuzz_parse3lib7ArgvEnv5argcNC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN5valsNC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN8evN_junkC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen4ENVUC13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC79OSSVerify6Proofs:boost_json:fuzz_parse3lib7ArgvEnv7u_argcNC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs3srUC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=MainWalk_defs4scrUC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN8sr_mainNC13~~~C89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN8kn_mainNC13~~~c99OSSVerify6Proofs:boost_json:fuzz_parse3lib9BudgetWit1U3MOB6regU_w~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen6cU_knUC13~~~c89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U8MainOpen4covUC13~~~C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U=RefMainEntryN9main_strNC13~~~".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~he7sregion37Corelib7Numbers7BinNumsm11Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ne5saddr04prod04cons03nil04pairne4EVarne2SA03fstne8sidecondne9sym_state04bool04true37Corelib4Init5Logichh02eqheblog_coveredne5s_logne7scripts89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainOpen4FPX1~~~~~~hka4regA79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UdMainWalk_defs~~~~~~hp42rAne6kentryhka2cAhp43knAhp42rChh03andne6sentry03sndne4s_pcne4ELithka4regFhp42rF05false3h5LinuxProcessSemantics5Riscv5Instrij07ALU_ADDij06BC_LTUne5EAluwne4SCBrhka2cFm14Npos3h5LinuxProcessSemantics5Riscv3Semio55low3235stdpp9bitvectorbdefinitionsir07Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSem5Stateit89errno_ret3h5LinuxProcessSemantics5Riscv7Preludejh34sextio55alu32io5cbranch_taken5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openjladopenat_errnoshka3scF36Stdlib5Lists4Listjq62Init8cENAMETOOLONGit86ENOENT46Stdlib6ZArith6BinInt1Zjt92lejt93powjt93subir0bbv_unsignedhka4regUhp42rUhka2cUhp43knUir02bvhh03not3h5LinuxProcessSemanticsfLinuxProcessSem3Runkjcavalid_argv06lengthjt96of_natne3env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~koe8blobs_evne3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~ktb7vals_ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcRefMainEntry~~~~~~lhf6blobs006option04Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsln8h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ls43rdn69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~mg6floaded_segments03nathh02ex37Corelib4Init5Peanomla2ltjt93addjt93muljh35bvmaphh01Ils44getrir02BVir04BvWfkjc5mkCfgls44mkstls47seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ms2dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~nga8realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~nl1ccat_argv_ptr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~npb9frame_modnga4TSet89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainOpen5Usage~~~~~~nu86frameUnu86regU_w37Corelib5Lists7ListDefojf3nth03app37Corelib4Init3Natom23addkjch0entry_stack_fits3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutop09EntryDrawkjcavalid_envpkjc8valid_spjt92lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UaRefStartup~~~~~~ov1amain_entryit85Model04Noneit88m_haltedit89m_vm_lazy79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BudgetWit3Rzbpm68realizes99OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BudgetWit1U3MOB5Usagepqc6frameUpqc6regU_w" s.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import MainOpen.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.Rzb OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.U.RPFB.
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Usage.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable model0 : Model.
  (* LPS 727298f3 port: [main_entry] is over the run's whole input, and the argv-string facts
     read the launch, so the input and the launch facts are parameters here, tied to [av] /
     [envv] by [Hargv] / [Henvp] as RefMainEntryN's section does.  Section shape of
     boost-beast/http_request's lib/MainOpen.v [Section Usage]. *)
  Variable inp : ProcInput.
  Variables (mbase brk entryw : word).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Henvp : in_envp inp = envv.
  Hypothesis Hhw : in_hwcap inp = a_hwcap.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis ME : main_entry inp mbase entryw sp0 rdraw tid regs0 mem0.
  Hypothesis Hargc : length av <> 2%nat.
  Hypothesis Hh0 : m_halted model0 = None.
  Hypothesis Hlazy0 : m_vm_lazy model0 = [].


  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Definition regU_w : ltac2:(zQ "50!h8!s5!ine!na!kif@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!ine!na!kif!s5!sb!t1!t6!jve!isd!kg5@3$4@2$3@1$2@1$0#k0$1@4$6@1$2@1$0#k0$1@2$8@1$0#k0@2$7@2$9@1$0#k0?3sp0+o0+l0@1$5@2$3@1$2@1$0#k0$1").

  Definition frameU : ltac2:(zQ "40!ine!kif!lma!mo2>1R@2$3@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "h30!ine!kif!h8!lma!isd!ln2!hi4!lqf!lvf!mjc!jve!kg5!hv8!mob!mp0!mp8!mpe!ml4!mo2\1R@2$h2@1$0#5@1$1@1$0#k0\1M>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+j8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$4@1$0#k0+ttln4@2$c@2$h1@1$1@1$0#k0\1w@1$1@1$0#k0@3$6@1$3@1$2@1$1@1$0#8@4$8$9^2@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+k0N8@2$5@1$2@1$1@1$0#8@2$7N8^1@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+k8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+9Kv$d@2$h0@1$0#5+9@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+l0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h2Kv$d@2$h0@1$0#5+h2@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+l8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h3Kv$d@2$h0@1$0#5+h3@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+m0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h4Kv$d@2$h0@1$0#5+h4@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+m8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h5Kv$d@2$h0@1$0#5+h5@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+n0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h6Kv$d@2$h0@1$0#5+h6@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+n8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h7Kv$d@2$h0@1$0#5+h7").

  (* LPS 727298f3 port: written out (rule 11g), restated over the revision's
     [cat_argv_ptr] (the drawn stack top and the exec file name).  Text of
     boost-beast/http_request's lib/MainOpen.v [seg_U], applying RefMainEntryN's lemmas over
     their current sections. *)
  Lemma seg_U : forall T,
    (forall R M,
       getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 4 = Z_to_bv 64 1108984 -> getr R 8 = Z_to_bv 64 2 ->
       getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
       frame_mod mem0 M regU_w -> frameU R M ->
       rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0)) ->
       Rzb.realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 291196) M (seg_rom RSEGS)) model0) T) ->
    Rzb.realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 290788) mem0 (seg_rom RSEGS)) model0) T.
  Proof using All.
    intros T HU. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_okN inp mbase entryw sp0 av envv rdraw tid regs0 mem0) as HR.
    repeat lazymatch type of HR with
           | forall _ : word, _ => specialize (HR brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hargv | exact Henvp | exact Hhw | exact Hvl | exact Hlau ];
               specialize (HR h); clear h
           end.
    pose proof (main_know_okN inp mbase entryw sp0 av envv rdraw tid regs0 mem0) as HK.
    repeat lazymatch type of HK with
           | forall _ : word, _ => specialize (HK brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hargv | exact Henvp | exact Hhw | exact Hvl | exact Hlau ];
               specialize (HK h); clear h
           end.
    pose proof (evN_argc inp mbase entryw sp0 av envv rdraw tid regs0 mem0) as Hac.
    repeat lazymatch type of Hac with
           | forall _ : word, _ => specialize (Hac brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hargv | exact Henvp | exact Hhw | exact Hvl | exact Hlau ];
               specialize (Hac h); clear h
           end.
    assert (Uac : bv_unsigned (argcN inp) = Z.of_nat (length av)).
    { rewrite <- Hargv. eapply u_argcN. rewrite Hargv. exact Hva. }
    change (EN inp sp0 av envv rdraw tid regs0) with (ENVU (valsN inp sp0 av envv rdraw tid regs0)) in HR, HK, Hac.
    set (vals := valsN inp sp0 av envv rdraw tid regs0) in *.
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) by reflexivity.
    cbn [ev ENVU] in Hac.
    clearbody vals.
    eapply (rz_run_lf RSEGS FUELM STOPSM scrU 290788%Z sr_mainN kn_mainN 40%nat (fst (fst rU)) (snd (fst rU)) (snd rU)
              (fst (fst cU)) (snd (fst cU)) (snd cU) (ENVU vals) mem0 (seg_rom RSEGS) regs0 model0);
      [ vm_cast_no_check (@eq_refl _ rU) | vm_cast_no_check (@eq_refl _ cU) | exact HR | exact HK
      | | apply Forall_nil | exact Hh0 | exact Hlazy0 | ].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. unfold sc_denot. cbn [branch_taken edenot ev ENVU]. rewrite Hac.
      unfold bv_eqb. rewrite Uac. change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    intros R M HR' HK' EQM LF. rewrite cU_knU in HK'.
    change (s_pc (fst (fst rU))) with 291196%Z. change (s_regs (fst (fst rU))) with srU in HR'.
    assert (RF : regions_flat (ENVU vals) regU).
    { intros r Hr. unfold regU in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
      unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENVU]. rewrite P0. lia. }
    pose proof (log_covered_frame (ENVU vals) mem0 regU _ covU RF LF) as FR. rewrite <- EQM in FR.
    unfold regU, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot ev ENVU] in FR. rewrite P0 in FR.
    replace (bv_unsigned sp0 + -128)%Z with (bv_unsigned sp0 - 128)%Z in FR by lia.
    apply (HU R M).
    - regv HR' (2:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVU]. rewrite P0. f_equal; try lia.
    - regv HR' (4:reg). reflexivity.
    - regv HR' (8:reg). reflexivity.
    - regv HR' (11:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVU]. rewrite P0. f_equal; try lia.
    - exact FR.
    - unfold frameU.
      repeat split.
      + krdv HK' 0%nat (-56)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        replace (bv_unsigned sp0 - 56)%Z with (bv_unsigned sp0 + -56)%Z by lia. exact Hrd.
      + eexists. krdv HK' 0%nat (-64)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        replace (bv_unsigned sp0 - 64)%Z with (bv_unsigned sp0 + -64)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-72)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (9:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 72)%Z with (bv_unsigned sp0 + -72)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-80)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (18:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 80)%Z with (bv_unsigned sp0 + -80)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-88)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (19:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 88)%Z with (bv_unsigned sp0 + -88)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-96)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (20:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 96)%Z with (bv_unsigned sp0 + -96)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-104)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (21:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 104)%Z with (bv_unsigned sp0 + -104)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-112)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (22:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 112)%Z with (bv_unsigned sp0 + -112)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-120)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (23:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 120)%Z with (bv_unsigned sp0 + -120)%Z by lia. exact Hrd.
    - krdv HK' 0%nat 8%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
      unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0, P1 in Hrd. exact Hrd.
  Qed.
End Usage.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
