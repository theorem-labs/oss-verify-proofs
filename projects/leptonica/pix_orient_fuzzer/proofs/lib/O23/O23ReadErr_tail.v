(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the m_channel_reader premise; the recorded proofs of re_segI, re_segH, re_segG, re_segF_gen, re_segDE and re_segBC, made over the old 8 MiB launch stack window, replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped; the exit record's last fields proved in this unit's field order). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibTail.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec LibWritev RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23ExitBase O23StdioDefs O23Exit O23LibStdioCall O23MemcpyBase O23Memcpy O23Memchr O23Strnlen O23Startup O23MainEntry.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23ReadErr_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23ReadErr_tail () := "C47Corelib7Program6Basics4flipC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2eq01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3O23<O23StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib3O23;O23ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00I59OSSVerify5KrLib3O23<O23StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib6Common9CliDriver6SymRun=ext_val_zx_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3O23<O23StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K59OSSVerify5KrLib3O23<O23StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib3O237O23Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib6Common8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs5STOPSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4srI0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4knI0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5aluop02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3knIC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant01C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic8f_equal2C47Corelib4Init9Datatypes3appC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1c59OSSVerify5KrLib3O23?O23ReadErr_tail5PRE19C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail9nth_app_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec>msg_read_errorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C69OSSVerify5KrLib6Common9CliDriver:SymDriveH46win_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH49log_out_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:flat_introC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib6Common9CliDriver7LibTail9rdn_app_ZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C69OSSVerify5KrLib6Common9CliDriver4Spec3s2bC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List9app_nil_rC47Corelib4Init9Datatypes3fstK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_wZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_varC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_addC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_exit_has_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail7re_segIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23LibStdioCall@stdio_call_soundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4Ardn_mem_denot_outC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs6BUF_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs6BUF_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3IHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3srHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3knHC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3O23?O23ReadErr_defs4srH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4knH0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib3O23?O23ReadErr_tail;PRE19_wordsC1?~~~~~~~~~~~~~~~K46Stdlib7Strings6String6string01C59OSSVerify5KrLib3O23?O23ReadErr_defs<itinerary_reC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs2rBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs2rCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs2rDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs2rEC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C59OSSVerify5KrLib3O23?O23ReadErr_defs2PXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs2rFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C59OSSVerify5KrLib3O23?O23ReadErr_defs2rGC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C59OSSVerify5KrLib3O23?O23ReadErr_defs2rHC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4scREC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs2rIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:SpecConstsArw_bytes_max_ge17C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC59OSSVerify5KrLib6Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC69OSSVerify5KrLib6Common9CliDriver7LibTail6ltu_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vmul_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8kimg_rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O239O23Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4@wbytes_agree_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4>know_cut_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH46kn_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib6Common7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses:impl_morphc59OSSVerify5KrLib3O23?O23ReadErr_tail7re_segHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib3O23?O23ReadErr_defs4scrGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4srG0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4knG0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail9re_nl_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3knGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail4reG0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z:ltb_irreflC69OSSVerify5KrLib6Common9CliDriver:SymDriveH4>edenot_addw0_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4<edenot_exts4C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_allC46Stdlib5Lists4List:firstn_appC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC59OSSVerify5KrLib6Common7SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4scrFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4srF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3knEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3knFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail7re_segGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail;re_segF_genC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notc59OSSVerify5KrLib3O23?O23ReadErr_tail4reF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6word_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib6Common9CliDriver7LibTail:rdn_byte_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith4Znat5Nat2Z2idC69OSSVerify5KrLib6Common9CliDriver7LibTail:In_nth_neqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O239O23Memchr<rodata_clearC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3O239O23Memchr5mchrH01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3O239O23Memchr5mchrH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23Strnlen;ref_strnlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame6in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail<vals_ev_junkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun<krange_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<know_ok_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame=frame_mod_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4extzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib6Common9Leptonica5Frame9frame_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_geC59OSSVerify5KrLib3O23?O23ReadErr_defs4scrEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4knE0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4srD0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3knCC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3O23?O23ReadErr_defs3knDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail@callee_saved_no0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib:wbytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs5logM1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun;carry_afterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail@re_memcpy1_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail8re_segDEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs4knC0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail9PRE19_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs5srRE0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs5knRE0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_tail9pre19_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23ReadErr_defs3knBC1?~~~~~~~~~~~~~~~".
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
  Lemma re_segI : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x10073c) M (seg_rom RSEGS)) model)
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
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x123d20), (bv_unsigned (vals_ev vals 5)),
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
      * lit_u. change (1195296 - 168)%Z with 0x123c78%Z.
        krd HK 0x123c78%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
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
  Definition PRE19 : list byte := s2b "cli: read error on "%string.

  Lemma PRE19_words :
    word_to_le_bytes 8 (Z_to_bv 64 7018141077071293539)
    ++ word_to_le_bytes 8 (Z_to_bv 64 2338053693894893668)
    ++ word_to_le_bytes 2 (Z_to_bv 64 28271)
    ++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE19.
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadErr_tail ()) ["Tail"] "h01Hh12b1h22b2h31np;1p;3p;2p;:g004Lj14Tg0051j1ETg005Oj1>Tg0062j1KTg01O7j1Ij30Tg006Rj17Tg00ATj13Tg00C;j1JTg008dj3?Tg00=^j2@Tg01THj3HTg00T8j2FTg02Hil:1Tg008Ej1=Tg00\:j2ATg01Moj2BTg02IGj3CTg02Idj2DTg00lmj3GTf0R0#4#4p=2%70#7p=8%40#7p=:%40#7#7#4p=<%70#4p=6f3R1f2R2f1R3/D03Gp=5%30,D39G12p=9g01mPR41@30'Fp=;g02:kR5#4#2R6#ER7#>R8%K8R9P9%I8R:P7%75R5#4R;#4R<#4R=#8#3R>P7%:=R=#<#:#:R?#:#8#2#6R@#2#6#2#2RA#2#8#6#6RB#<#6#:RC#<#8#2RD#<#2#8#3REC5RFP7P>P7P>C5R>P7%7;R;#7RG#2#3RHP7PDC9RDP7%4;#:#3R;P7PCC9RCP7%65R5#6#3RIP7PBC9RBP7%26R6#3RJP7PAC9RAP7%45#6#3R5P7P@C9R@P7%6<R<#7#3RKP7P?C9R?P7%3=R=P7P=C5R=P7%4<#3R<P7%46R6#7#8#2#6RL#<#8#8RM#:#8#2#6RN#:#8#2#6RO#<#:#:RP#2#6#2#2RQ#<#:#2#3RRC5RSP7PJP7PQC9RQP7PKP7PPC9RPP7P5P7POC9ROP7P5P7PNC9RNP7%7GRG#7#3RTP7PMC9RMP7P5P7PLC9RLP7PJP7PJC5RUP7PTP7%4GRG#<#8#8#3RVC5RWP7%3GRGP7PGC5RG%J8RX908URY508RZ508R[508R\508R]508R^508R_508R`508Ra508Rb508Rc508Rd508Re508Rf508Rg508Rh508Ri508P7PHP7PHC5RHP7P;P7P;C5R;P7PIP7PIC5RIP7P5P7P5C5R5P7PKP7PKC5RKP7P<P7P<C5R<P7PTP7PTC5RTA08TZRj908URk9085Rl508Rm9085Rn9085Ro908KRp908URq508Rr908=Rs508Rt508Ru908URv508Rw508Rx508g02GURy%>0Rz%>3R{g00h1%>2??301@121@135?4R|[1@231@205?4%>1??23[R4f4#>??12\|AH230P0n2001000000120000000W2W1W3R3P4^2{^1z^3yRyP0P7PFP>1;7>O4b0P8P9P9P:PDPHPiPxP3PyP0P7PDPH1;7HO4b0P8P9P9P:PCP;PhPwP3PyP0P7PCP;1;7;O4b0P8P9P9P:PBPIPgPvP3PyP0P7PBPI1;7IO4b0P8P9P9P:PAPUPfPuP3PyP0P7PAPU1;7URAO4b0P8P9P9P:P@P5PePtP3PyP0P7P@P51;75R@O4b0P8P9P9P:P?PKPdPsP3PyP0P7P?PK1;7KR?O4b0P8P9P9P:P=P=PcPrP3PyP0P7P=P=1;7=O4b0P8P9P9P:PSP<PbPqP3PyP0P7PSP<1;7<O4b0P8P9P9P:PQPUPaPpP3PyP0P7PQPUPAO4b0P8P9P9P:PPPKP`PoP3PyP0P7PPPKP?O4b0P8P9P9P:POP5P_PnP3PyP0P7POP5P@O4b0P8P9P9P:PNP5P^PmP3PyP0P7PNP5P@O4b0P8P9P9P:PMPTP]PlP3PyP0P7PMPT1;7TRMO4b0P8P9P9P:PLP5P\PkP3PyP0P7PLP5P@O4b0P8P9P9P:PUPUP[PjP3PyP0P7PUPUPAO4b0RAP8P9P9P:PWPTPZPZP3PyP0P7PWPTPMO4b0P8P9P9P:PGPGPYPYP3PyP0P7PGPG1;7GO4b0P8P9P9P:PUPUPXPXPA1F9XM:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1M:1g02;P#=RX#=RA#=#=#=#=#=#=RU%E6R6/AE'B1A6R,BU1A6V,BA1A6J,BX5C85C85C8g02JW5?9do"). Qed.

  Lemma re_segH : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 231%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1%nat = Some [Z_to_bv 8 10] ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xfff20) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scr0 231%nat.
    (* [comment removed for export] *)
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'. 
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-542)%Z 1%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 19 = Some PRE19).
    { rewrite <- PRE19_words. change 19%nat with (8 + (8 + (2 + 1)))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + apply rdn_app_Z; [ | | lia | lia].
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2.
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2)%Z with (bv_unsigned sp0 + -542)%Z by lia.
          exact Hw3. }
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (19 + (length path + 1))
                  = Some (msg_read_error path)).
    { unfold msg_read_error. change (s2b _) with PRE19.
      apply rdn_app_Z; [exact H17 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19)%Z with (bv_unsigned sp0 - 541)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19 + Z.of_nat (length path))%Z
          with (bv_unsigned sp0 - 541 + P)%Z by lia. exact SBn'. }
    (* [comment removed for export] *)
    assert (LEN : length (msg_read_error path) = (19 + (length path + 1))%nat)
      by (unfold msg_read_error; rewrite !length_app; reflexivity).
    replace (W 2 (msg_read_error path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_read_error path ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_re as (_ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scRE (msg_read_error path) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRE]; rewrite ?LEN end.
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
      eapply (re_segI (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma re_nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1b8ac) 1 = Some [Z_to_bv 8 10].
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadErr_tail ()) ["Tail"] "p;1p;2p;3p;4g004Lj10Tg0051j17Tg005Oj13Tg0062j18Tg007cj1ATg006Rj11Tg00ATj15Tg02Idj2<Tg00lmj3;Tg00C;j1:Tg01O7j34Tg01OWj22Tg00T8j29Tg00e>j1@Tg00\:j26Tg008Ej1?Tg01cKj4=Tg008dj3>Tg02:kR0#0R1#0#0R2#7R3#3R4#8R5#AR6%11#0#5R11<315;3%:4R7544,25'9g0238%02#0#0#7R2#3%@4U%10#0#1#1#1#0#0#0#1#0#1#0#1#1#0#0#5,62g02;P#?C=1631=447,255>6do"). Qed.

  Lemma re_segG : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xfff20) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * P + 61)%Z with (61 - P)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x1b8ac) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x1b8ac 1) in exact i)
                 _ _ 0x1b8ac 1 HK eq_refl) by (cbn; lia). apply re_nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-541) 64) in exact i)
                    _ _ _ (-541 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541 + P)%Z with (bv_unsigned sp0 + (-541 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x1b8ac) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0xfff20 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1b8ac) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x1b8ac) 1 _ (seg_rom RSEGS) MC Rc (0xfff20 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 1088688) with (0x109cb0 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0xfff20 : word) with (Z_to_bv 64 0xfff20) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-541) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knG) with knH0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (re_segH path P vals1); try eassumption.
    - (* [comment removed for export] *)
      rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 541 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition reG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xfff20) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  Lemma re_segF_gen : forall (path : list byte) (pp : word) (P : Z) (T : TSet) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 61)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    reG0 path P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xfff20) M (seg_rom RSEGS)) model) T.
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
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
      replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-541) 63) in exact i)
                    _ _ _ (-541) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541)%Z with (bv_unsigned sp0 + -541)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp P path).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0xfff20 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
      destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0xfff20 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 1088688) with (0x109cb0 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0xfff20 : word) with (Z_to_bv 64 0xfff20) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-541) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knF) with knG0 in HK2.
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
    pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 541))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  Lemma re_segF : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xfff20) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadErr_tail ()) ["Tail"] "h04__x1h12HKh23HK'h32HLh43HL'h53HL0h62HPh73HPrh82HRh93HR'h:4Hpp1h;4Hpp2h<4Hstrh=1Mh>2M'h?1Ph@2P0hA4P113hB2P2hC2Q0hD4Q113hE1RhF2R'hG2SBhH7__arithhI4__ffhJ8__varmaphK5__withL4cstrhM5cstr0hN4pathhO2pphP4valshQ5vals'hR1xhS1yp;1p;2p;3p;4p;<p;8p;=p;Cp;7g004Lj17Tg0051j1>Tg005Oj1GTg0062j1ATg006Rj12Tg0077j2^Tg007cj1MTg000Nj25Tg014SR0j18Tg008dj31j1FTg00>Hj24Tg00ATj16Tg00h1j2ETg008Ej10Tg009>j2:Tg00\:j2<Tg00=^j2@Tg010kj2=Tg00:Bj1;Tg00;>j3LTg00<Nj4KTg02T3j2ZTg01cKj4ITg00C;j1JTg01O7j3YTg02IGj3XTg01OWj2HTg02L\j1WTg00^Nj2VTg00PFj1UTg00QJj1TTg00R=j2RTg00_oj2STg0153j2rTg015Vj3qTg00T8j2?Tg01_Ll<pTg0163j4oTg016Zj1QTg017?j2lTg017]j1kTg018;j1hTg01>Pj2CTg018fj2aTg00e>j1bTg01`Uj8_Tg019lj2cTg01:Nj2dTg01;:j3eTg01;Yj4fTg00lPj2gTg04^Ml=\Tg04I1j3iTg04_MlCjTg01E<j4[Tg01`1j7mTg01a9j7nTf0R1#7#7p=3%01#0p=P%01#0#0#0p=O%01#0#0#0#0#0#0#0p=`%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=9%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=]g01mPR2f1R3g020JP1C[p=BP3g01nkR4g01oJR5P5g01ojR6P1g0211Fmp=Df2R7P4P5P5P6P3P1Fnp=Ng02:kR8#7R9#3R:#>R;#GR<#AR=%7:R>#3R?#>R@#GRA%AARB%29RC#>/^ARD%M<\AREf5RF,5<#8f3RG512g01nMRHf4RI'4%28#2#2#7RJ#7#6RK,4I'Eg01mnRL15AIg02;PRM#0RN#0RO#0#P#O#`#9#9#9RP#P#O#]#9RQ311:FMp,3sp0RR51Af6RS/:Of8RO51Af7RT/:P1<@O51A1@@RRUf:RV,@@'4f;RW,@@/=V%6:'=%3?#3#3#3#3#3#3#3#6,=U'4%;Vg04Z_f9R?3Lg0238R:%;WP?g04[\CK%M=R?P:PVf>RXf?RY,5</ZNCI1<;H%J<5Y<9X<Y,H=31f@R;PYPX%69R9%W;'V%U9p,5model#T'R'SR9f=RNf<PWPV15ANRV=1LQ%8VRW%3C#2#2#2#6RC512RZPLP2%FLP0%F2%83%81512A1L311r313qXSLXRLPVPW1?2WPQPC1?2CM<pPOCoPZfA,5<RZ#Q%8Z,4H15AYRY#Q%8Y,4Hg02C2RY#J%AY1l23%k2%h2RYP4P5P5P61C2H1a28R8'B,DYR41C2K,B8,DY5NY%b5%2J#6RJ,C2,B8,DY9NY4G_1cY6P1P7g021QRYg0221R6'?1d17=1Y6dAe2H3CfbIbJbKX0214H1141K'E14H3143J'E[^02P1fBRJPNO2bHbMbLb5POPTPSPFPIPGP7P3P115A7%9Q51L1:GM=1AR1:IPfCRP,<@51A%;Fg04A_;LIP:%;SPIg04B\CKP:PF%2>#2#2#7#2#6,gU,<@fHR@,5<CI1H=@51?fIfGPOPTPSPPPJPFPIPGP7P3P1M=\WGW2W9WDWCW4X>EXFDXQBAi;X9eMCjW<W1W8W;W:WAWBW@W3W7W6W=WEWPX?2WOWNo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition reF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
      rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xfff20) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma re_segDE : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 103%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    reF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xfff20) M (seg_rom RSEGS)) model) T.
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
        pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x1ecc8 24) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x100ddc : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x100ddc : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 1091460) with (0x10a784 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x100ddc : word) with (Z_to_bv 64 0x100ddc) by (apply bv_eq; reflexivity).
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
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1081a) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0xfff20 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1081a) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1081a) 0 _ (seg_rom RSEGS) MC Rc (0xfff20 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 1088688) with (0x109cb0 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0xfff20 : word) with (Z_to_bv 64 0xfff20) by (apply bv_eq; reflexivity).
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

  Lemma pre19_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1b897) 19 = Some PRE19.
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadErr_tail ()) ["Tail"] "p;1p;3p;2p;4g004Lj12Tg0051j1;Tg005Oj1:Tg0062j1GTg007cj1DTg006Rj10Tg00ATj11Tg00C;j1=Tg01O7j39Tg01OWj2<Tg00T8j2FTg00e>j1ETg00\:j2CTg008Ej16Tg01cKj4@Tg008dj3ATg02Idj2?Tg00lmj3>Tf0R0#2#2p=7f3R1f2R2f1R3/?03>p=3%00#2p=5f4A9230791p=4%60#6p=B%60#6#6#6p=8g02:kR0#2#7R1#;R3#:R2#GR4#DR5P2P3%00R6#2R7#2R8#2R9#0#0#1R:P3P:C3P2P3%07R7#0R:#7#1R;P3P;C3P2P3%77#0#1R7P3P7C3P2P3%56R6#5#1R7P3P7C3P2P3%71R1#1R7P3P7C3R7P2P3%26#5#1R6P3P6C3R6P2P3%58R8#0#1R;P3P;C3R;P2P3%29#0#1R9P3P9C3P2P3%28#1R8P3P8C3P2P7P2P;P2P6P2P6P2P3%0:R:#0#1R;P3P;C3R;P2P6P2P7P2P;P2P3%2:#1R:P3P:C3%=29927D4D4D4D4D4D4D4D4D4,<4'Fg0238%21#;R1#:%E2U%50#0#0#5#7#0#7#5#0#0#0#1,C1g02;P#6#B#8#8#8#8C@g02JW,<45A5do"). Qed.

  Lemma PRE19_len : length PRE19 = 19%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadErr_tail ()) ["Tail"] "p;1p;2g008Ej10Tg00T8j22Tf0R0#0#0p=3%00#0#0#0p=1g01mng02;P#0#3#1#1#1#1'2o"). Qed.

  (* [comment removed for export] *)
  Lemma re_memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE19.
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadErr_tail ()) ["Tail"] "h04__x1h17__arithh24__ffh38__varmaph45__with51xh61nh76__sat3h86__sat4h91yh:1zh;2Hah<1Hh=2H0h>1Mh?2P0h@1bhA1lhB1mhC1ohD4valsp%0p&0p;1p;2p;3p;4p;8p;6p;<p;Bp;7g004Lj10Tg0051j1pTg005Oj1uTg0062j1mTg007ck10?Tg009>j2tTg008dj3Kk10@Tg006Rj17Tg00ATj1BTg00=^j2DTg00>HR0j2RTg008Ej1HTg00\:j28k10ATg01Moj2VTg02IGj3cTg00:Bj1rTg00Zhj3qTg00lPj2bTg03lMR1j31j2Tj1STg000Nj2_Tg014SR2j1QTg05G\j2fTg00>dj1yTg00?mj1\Tg00C[j2[Tg00obj2GTg00@Kj1ZTg010kR3j22Tg00T8j2ETg01BDj1lTg01Bbk40>Tg00C;k10=Tg017?k20<Tg017]k10;Tg018;k10:Tg018fk208Tg019Ik307Tg019lk206Tg01:Nk205Tg01;:k304Tg01;Yk403Tg01CEj4LTg03j6j89Tg00e>k102Tg01>Pj2nTg01=Ok201Tg01=3R4j2<Tg01<Kk200Tg01=lj3~Tg01?3j3}Tg02haj3`Tg001Kj6@Tg05HQj2eTg01];j1]Tg00nYj2WTg01^Dj1^Tg05IYj4hTg0033j6|Tg01a]l<{Tg01bBlBzTg01_Ll<gTg01bhk309Tg01E<j4iTg01`1j7xTg01`Uj8wTf0R5#0#0p=6%75#7p=3%75#0p=>%05#0#0#0p=U%05#0#0#0#0#0#0#0p=F%05#7p=M%75#0#0#7p=O%05#7#7#0p=Xf4R6f3R7f2R8f1R9;153Kp=A1W95,V8p=JA1678?195p=41295,88p=51D89/25,87p=?g01mPR:?K95p=;1E:5p=Cg01mnR;P:P:P:P2P2f5R2P6P7P8P9P5M<{p=vP:P:P:P:P:P:P3P5P9P8P3P7P6P2f6R3f7R<f8R=f9R>MBzp=kP:P:P5P9P8P7P6P2P3P<P=P>M<gp=j1n:5p=IB09:95p=PP:P9g02D^P5Cip=dP9g01nkR>g01oJR=P=g01ojR?P5g0211Fxp=:g01nMR@/R5p==P:P:P0P2P0P6P@P@P7P8P9P5M<gp=sP:P9g020JP5Cip=YP7P>P=P=P?P8P9P5Gwp=NP:P:P4P<P4P3P2P6P7P8P9P5M<gp=oP:P9g022QP5Cip=ag02:kR3#0R4#6R<#0R>#0R0#0RA#pRB#uRC#m%p<#uRD$0?\CREg02;PRF,t9p,3sp0RG5KCp,4SPloS00%73RH#7#3#3#3#3#3#3#>#6#U#F#F#F#BRI1DBGRJ'Rp,4SPhiS01%0A#F#F#F#F#F#BRK,RJ%mDRL%HFRM#HRN#H#H#H#H#H#HRO%0HRH#6#M#M#O#M#M#3#6#>#6#>#6#U#3#>#>#X#O#X#3#6#X#6#3#BRP,8BS02'VRQ%7A#3#6#>#X#3#3#M#3#6#O#3#6#O#O#M#6#>#U#M#O#6#BRR,8BS03,VORS%3H#>#X#3#3#BRH,8BS04,VNRT%B0R0,8B,VMRU5cDRV5cDRW5cDS05PE%r2R2g05J\S067q6P6%7<RX#7#URY#BRZ,bJR[,8BR\P5DAXALPEA17\QR]1_DQS07#QR^,f\R_;1WS08P6%yFR`%\YRY'[Ra,G2%ZPS099JO2%0XRX#>#6#\RP,[`Rb,G2%ZRS0:9JO2D4%UX#\RX,[`RR,G2%ZHS0;9JN2%7>#3#>#\R>,[`R`,G2%Z0S0<9JM2D4=KE5XCER2PEA1]_SS0=1_DSS0>#QR0,f_RH;1VS0?P2PEQ0=PHPT1_DTS0@#QRD,fHPUD4S0AP2PCPGPEP61DB5RG=5BYPQA5BGPPSD4A5BGXPTA5BG>PUD4A16\QRG1DB\R2=5B^R^PSPBPBP^P0C?RcPTD4PBPBPcPDC?S0BPUDAX@CP;POPEP6A5BJYRYPQ12JPRd,8BRePSD412JXRf,8BRgPT12J>Rh,8BRiPUD4RjPG%Q5Rk95B2RlPSPBPBPlP0C?R0PTD4PBPBP0PDC?PUDAX6;P;POPEPj%QOR095B2Rl=1GSRm1DBlRn=5BkRo;1TPBPBPoPDC?PUDAX6;P;PNPEPjA5Bn0Rn=1mT1DBnRm=5BkPUDAX6;P:P[PEPjPGA5B50RDPS1DBDRo=5B0RpPTD4PBPBPp%QNRpC?PUDAX::P:12[0RqPEPj18BqRr=1GSRG?1DTA5BopPUDAX::P:12q0RoPEPj18BoRj=1GTA5B5pPUDAX::PLPEA17YQRY?1eSRG?1gTRD/TiA1]rSRs?1jTRt12opRu,8BRv'TPUPUPCPE\LRw%SD%StPiPvPEPw\CRvP1P1PDPtPv\E/E1RtPLPE1TGg1TsjPTPTPCPw%SG%SsPgPjPEPvP1P1PGPsPtPLPE1TYe1T]rPSPSPCPw%SY%S]RYPePr1EvYP:PC&0ABRYPYPdPqPC\:/EYRv1;dq%B<R<,2[Re,;d&0@:RwP5X5:RtPw1;95#lX9:X5:RsPdPd%CdPqPePtPtPtP:P:g02D:1295H0>#CXB:X6:RdP[P[%C[P0P<PtPt%CkX5;S0CPOP<%C<EvS0DM:kR;M:jg02C2Rk$0=RG%mkRk20<:9R1&0;:Rg&0::Rx208:3R3%IP'P%IZ:07:3Ry%I<Rz'PR{'d':206x?R?P5P8g021QR|g0221R}'E20558=K|}dB04:@9H03R}b2b3b4X0:125P1b5Z/2<RP';^0:P5PJO1R|b1CLG9G91ELSG9G9P:PCPYPYPfPoPv1;fo12e<R~,;fPwPtPwPsPfPf%CfPoP~PtPtPtPdPqPeP;P0P<Q0DM:kR0M:jPGPkP1Pg%IX,P31P{zRz'd,:xP?P}b2b3b4X0:125X12P<RP';^0:P|b1CLG9G91ELTG9G9P:PCPYPYPhPuPv1;hu%B4R4,2~Rv,;hPwPtPwPsPhPh%ChPuPvPtPtPtPdPoP~P0PpP4PtPtQ0CPNP4%C4EvM:kM:jPGPkP1Pg%I>,P3%I4Rd,Pz'd,:xP?P}b2b3b4X0:125>12P4';^0:P|b1CLG9G91ELUG91DBj%=o%=~Pt1R95#lX9:X5:Rj1E:@RLPoP~P0EsPGPkP1PgPx%II/Y3,:xR|&02=R=1n:@RP/Yz,:xCNP?P}b2b3b4X0:1RI5RI1b9ZRZ/2<R>/2<R<#=[^0:P5PJQ00O2Rvb1CL%BARA-014Ru,<o1<~uPt1<95#lX9:X5:RhPoP~P0PuPu%CuR0Go2004AR~1<@4%=A1<@u[[R@%=4Rsg02C^RwA~4A9UW;RA%=u\w^;sRsPGPkP1PgPx%IK,Y3,:xR3P=A}:dBRd,az,:xCNP?P}b2b3b4X0:1R5KRK1<<u[^0:P5PJQ01O2RJb1b7b8CL5`oE@1DBr%=q%=ePtPjPLPqPeP;EsPGPkP1PgPxP|P=1YP{,:xCNP?P}b2b3b4X0:%=>\I^0:Pvb1CL1<qu1<euPtPhPqPeP;PuPuP0GoP~P@PAPsPGPkP1PgPxP3P=1a{d,:xCNP?P}b2b3b4X0:1<>u\K^0:PJb1b7b8CL5`qE@P2PGPkP1PgPxP|P=1YPy,:xCNP?P}b2b3b4X0:%=Z\I^0:Pvb1P~P@PAPsPGPkP1PgPxP3P=1ayd,:xCNP?P}b2b3b4X0:1<Zu\K^0:PJb1b7b85`[E@PEA1DiUP]PlPSPnPTD4A5BmpPUDAeQ0@Q04,eNE@Q0>Q03,eOE@Q07Q02,eOE@1t6FP8E@PEP7PBPB%r6R6%]a'W%^aC?Q099JO6R8PBPB%]b,W6%^bC?Q0:9JO6ROD4PBPB%]R,W6%^RC?Q0;9JN6RNPBPB%]`,W6%^`C?Q0<9JM6RMD4P]P^PSPcPTD4Q0BPUDAeP71G6aP81G6bPOD41G6RPN1G6`PMD4Q0A5KEeQ0?PTPUQ0=PHChE@Q08PSPVP]P_ChE@Q05917\R_PQPWP7P\ChE@Q069q67=KE_eg02JWg03IAE|b=b<W?W>WDo"). Qed.

  Lemma re_segBC : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srRE0 R -> know_ok RSEGS (ENV vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    reF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x62d48) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 39%nat.
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
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x1b897) 19 = Some PRE19).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x1b897 19) in exact i)
                 _ _ 0x1b897 19 HK eq_refl) by (cbn; lia). apply pre19_img. }
    assert (Hdst : store_ok RSEGS M' dst 19 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 19) in exact i)
                    _ _ _ (-560) 19 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x1b897) 19 PRE19).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0xfff20 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1b897) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 19) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x1b897) 19 _ (seg_rom RSEGS) MC Rc (0xfff20 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 1088688) with (0x109cb0 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0xfff20 : word) with (Z_to_bv 64 0xfff20) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE19) knC0).
    { subst dst. rewrite <- (re_memcpy1_denot vals M' P0).
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
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE19) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE19) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    assert (Ht82 : rdn RSEGS (wbytes M' dst PRE19) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE19) in *. clearbody M1. clear M' dst.
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
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1b8aa) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0xfff20 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1b8aa) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1b8aa) 0 _ (seg_rom RSEGS) MC Rc (0xfff20 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 1088688) with (0x109cb0 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0xfff20 : word) with (Z_to_bv 64 0xfff20) by (apply bv_eq; reflexivity).
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
    eapply (re_segDE path pp P T t8 vals2); eassumption.
  Qed.

End Tail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
