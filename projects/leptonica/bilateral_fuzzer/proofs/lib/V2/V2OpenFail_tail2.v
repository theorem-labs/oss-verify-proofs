(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2ExitBase V2StdioDefs V2Exit V2LibStdioCall V2MemcpyBase V2Memcpy V2Memchr V2Strnlen V2Startup V2MainEntry.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2OpenFail_defs V2OpenFail_tail.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2OpenFail_tail2 () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_tail3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2eq01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2V2;V2StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib2V2:V2ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00I59OSSVerify5KrLib2V2;V2StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib6Common9CliDriver6SymRun=ext_val_zx_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib2V2;V2StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K59OSSVerify5KrLib2V2;V2StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib2V26V2Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib6Common8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5STOPSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5srI30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5knI30C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5aluop02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant01C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes3fstK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_wZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_varC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_addC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib6Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_exit_has_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V2@V2OpenFail_tail28of_segI3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2LibStdioCall@stdio_call_soundC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2RelocImg7v2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4srH3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4knH3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib2V2?V2OpenFail_defs5srH30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5knH30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs?itinerary_63_64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3rG3C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5mulop01C59OSSVerify5KrLib2V2?V2OpenFail_defs2PXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4srG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4knG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3rH3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scH3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3rI3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3rF4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C59OSSVerify5KrLib2V2?V2OpenFail_defs4srF4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4knF4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scF4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3rG4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3rH4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4srH4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4knH4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scH4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3rI4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:SpecConstsArw_bytes_max_ge17C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3ltbC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC69OSSVerify5KrLib6Common9CliDriver7LibTail6ltu_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vmul_ZZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C69OSSVerify5KrLib6Common9CliDriver:SymDriveH46win_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH49log_out_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4Ardn_mem_denot_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:flat_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail9rdn_app_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8kimg_rdnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02c59OSSVerify5KrLib2V2@V2OpenFail_tail28of_segH3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib2V2?V2OpenFail_tail4atG0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib2V2?V2OpenFail_tail5PRE17C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib2V2?V2OpenFail_tail9PRE17_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5scrG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4srG0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4knG0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs6BUF_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs6BUF_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_tail;PRE17_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_tail6nl_imgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C47Corelib4Init5Logic8f_equal2C59OSSVerify5KrLib2V2?V2OpenFail_defs5srI40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5knI40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V2@V2OpenFail_tail28of_segI4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5srH40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5knH40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V2@V2OpenFail_tail27NL_wordC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z:ltb_irreflC69OSSVerify5KrLib6Common9CliDriver:SymDriveH4>edenot_addw0_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4<edenot_exts4C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List9app_nil_rC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_allC46Stdlib5Lists4List:firstn_appC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC59OSSVerify5KrLib6Common7SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_emit_has_nilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V28V2Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib6Common9CliDriver9SymDriveX@know_after_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V2@V2OpenFail_tail28of_segH4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AgentLib:t_emit_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib2V2?V2OpenFail_defs5srG40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5knG40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs5scrF4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4srF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3knEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4knG4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_gt_casesC59OSSVerify5KrLib2V2?V2OpenFail_tail7of_segFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V2@V2OpenFail_tail28of_segG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_tail;of_segF_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V2@V2OpenFail_tail29of_segFG4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_tail4atF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_tail8of_segBCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3srAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3knAC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac close_exit HR HK P0 Hh Hlazy sp0 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x56270), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | cbn [ev ENV] in Ktid |- *; lia
      | lit_u; change (352880 - 168)%Z with 0x561c8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x561c8%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
            | eexists; krd_solve HK | atexit_solve ltac:(idtac; krd_solve HK)      (* [comment removed for export] *)
| repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Section Tail2.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Hypothesis Hrd2 : m_channel_reader model = true.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma of_segI3 : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srI30 R -> know_ok RSEGS (ENV BL vals) M knI30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3ea4c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy sp0.
  Qed.

  Lemma of_segH3 : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH30 R -> know_ok RSEGS (ENV BL vals) M knH30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3ec1c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH3 knH3 Rc Mc model scH3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH3 knH3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH3 length Z.of_nat] end.
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
      eapply (of_segI3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segG3 : forall (path : list byte), Z.of_nat (length path) = 63%Z ->
    atG0 sp0 BL model path 63 (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path HP vals R M HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG3 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * 63 + 63)%Z with 0%Z by lia.
      rewrite ltu_ZZ by lia. reflexivity. }
    assert (WOK : win_ok (ENV BL vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
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
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + length path) = Some (PRE17 ++ path)).
    { apply rdn_app_Z; [exact H17 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'. }
    assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x11d14) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x11d14 1) in exact i)
                 _ _ 0x11d14 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    (* [comment removed for export] *)
    unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
    pose proof itinerary_63_64 as (_ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG3 knG3 Rc Mc model scG3 (PRE17 ++ path) [Z_to_bv 8 10]
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG3 knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scG3];
      rewrite ?length_app, ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (17 + length path)%nat with (17 + length path)%nat by lia. exact B80.
    - cbn [edenot]. exact Hnl.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma NL_word : word_to_le_bytes 1 (Z_to_bv 64 10) = [Z_to_bv 8 10].
Proof.
ltac2:(KReplay.run1 (kr_t_V2OpenFail_tail2 ()) ["Tail2"] "h02b1h12b2h21nh31Hp;1p;2p;3p;:g003kj10Tg004Pj14Tg004nj12Tg005Qj17Tg01PXj1Bj3?Tg0061j1=Tg00ARj1<Tg03mPj2;Tg00oSj3:Tg00C9j18Tg008cj31Tg00=\j23Tg01Ucj39Tg00UAj26Tg03nCl:ATg008Dj1@Tg00]Cj25Tg01OPj2>Tg02;l#0R0#0#0R1#4R2#2R3%73R4P4%B3%=0#0#<R01;205:2R5P5%83R6P6g02GZR7f0R8#2R9f1R:#2R;g00iTf2R<#2?1:8g01niR=f3R>/3<13>:31R?[13<:13<851=%2>?1<:[R@f4#2?1><\?A9<:8P8n2001000000120000000W1W0W2P@^1;^09^27P8P2P5P51325,6=O4b31646M:Ag02<Q#@%01#0#0#4/50'>1520=?36514do"). Qed.

  Lemma of_segI4 : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srI40 R -> know_ok RSEGS (ENV BL vals) M knI40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3ea4c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy sp0.
  Qed.

  Lemma of_segH4 : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH40 R -> know_ok RSEGS (ENV BL vals) M knH40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3e75c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    krdv HK 0%nat (-560)%Z 1%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite NL_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH4 knH4 Rc Mc model scH4 [Z_to_bv 8 10] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH4 knH4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH4 length Z.of_nat] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
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
      eapply (of_segI4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segFG4 : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (64 <= P <= 131071)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + P + 1 <= 0x800000000000)%Z ->   (* [comment removed for export] *)
    regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3e75c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 Hpp3 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV BL vals) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrF4 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV BL vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
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
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))))).
    2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srF4 knF4 Rc Mc model scF4 PRE17 path
             (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n srF4 knF4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scF4];
      rewrite ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P113. rewrite u_small by lia. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV PX]. rewrite P2. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P2, P113. rewrite u_small by lia. lia.   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact H17.
    - cbn [edenot ev ENV PX]. rewrite P2. exact Hsrc.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Hw1 Hw2 H17 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with knG40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with srG40 in HR end.
      set (vals0 := vals) in P2, P113.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
      run_blk scr0 199%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x11d14) 1 = Some [Z_to_bv 8 10]).
      { rewrite (kimg_rdn RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x11d14 1) in exact i)
                   _ _ 0x11d14 1 HK eq_refl) by (cbn; lia). apply nl_img. }
      assert (Hdst : store_ok RSEGS MG dst 1 = true).
      { pose proof (kwr_store_ok RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-560) 1) in exact i)
                      _ _ _ (-560) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x11d14) 1 [Z_to_bv 8 10]).
      { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hnl.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0x3e75c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x11d14) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x11d14) 1 _ (seg_rom RSEGS) MC Rc (0x3e75c : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 275580) with (0x4347c : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0x3e75c : word) with (Z_to_bv 64 0x3e75c) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      (* [comment removed for export] *)
      pose proof (know_after_store RSEGS (ENV BL vals1) MG knG4 (SA (EVar 0) (-560)) 1 (ELit 10) [Z_to_bv 8 10]
                    knH40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply NL_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV BL vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst [Z_to_bv 8 10]) knH40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 231%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR, HK.
      eapply (of_segH4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem of_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 131071)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (2 ^ 64 - 4095 <= bv_unsigned (vals_ev vals 38))%Z ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 1 <= 0x800000000000)%Z ->
    regs_ok (ENV BL vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV BL vals) M knA ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x43d68) M (seg_rom RSEGS)) model)
               (t_die (msg_cannot_open path) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2OpenFail_tail2 ()) ["Tail2"] "h04__x1h13HL0h27__arithh34cstrh45cstr0h54HL'0h64__ffh78__sat114h88__sat115h98__varmaph:5__with;5cstr1h<2Hah=4Q113h>7__sat39h?7__sat40h@4__x2hA4__x3hB1ohC3E63hD2HKhE3HK'hF2HLhG3HL'hH3HPlhI2HRhJ3HR'hK3HgthL4Hgt2hM3HlehN4Hle2hO6HnonulhP4Hpp1hQ4Hpp2hR4Hpp3hS4HstrhT5Hstr'hU3Ht8hV1MhW2M'hX2P0hY2P2hZ3P38h[2Q0h\2Q2h]1Rh^2R'h_4pathh`2ppha2t8hb4valshc5vals'hd1xhe1yhf1zp%0p&0p;1p;2p;3p;4p;5p;Hp;6p;Ip;Bp;7p;Lp;<p;8g003kj11Tg004Pj1bTg004nj1jTg005Qj1]Tg0061j1;Tg006Vk20HTg007Bj1lTg00]Cj2ITg04g2k302Tg04gIj1}Tg00ARj15Tg00>Fj22Tg007dj23Tg008Dj10Tg009=j2ETg008cj36j1qTg01@5k206Tg00n1k204Tg00=\j2GTg013Qj28Tg00:Aj2OTg04LQj2~Tg00oSj3|Tg04ekj1zTg00>bj1yTg04gbj3xTg00;<j3pTg00<Lj4rTg02d7j2fTg01ddj4WTg00C9j1eTg01PXj3tTg02Idj3sTg01Q8j2dTg03Ikj1TTg00_Wj2PTg00QOk10PTg00RSk10OTg00SFk20NTg00a8j2STg0179R0j1<Tg017Yk20LTg018<k30KTg018Yj4HTg019@j1:Tg01?1k20GTg01?Yj2=Tg01@Rk30DTg019ej2\Tg01:Ck10ATg01:ak10@Tg01;Lj2_Tg01<Rk209Tg00UAj2kTg01=4k208Tg01=`k307Tg01>?k405Tg01A6j2iTg00fck103Tg00iTj2QTg04hkj2hTg00mWS00j2gTg00PSk101Tg00]ij5aTg00^bj2YTg01[Aj3XTg04iPmI00Tg01Gbj4VTg002Sk60:Tg01DLk10;Tg00?kk10<Tg03\5j2{Tg03\Vj2`Tg03]?k30=Tg03]hj3mTg03^Qk20>Tg03Vlk40?Tg01dAj3MTg04jOk20BTg04kPmI0CTg04lSlBwTg04mUk70ETg04nQmL0FTg04oQk20ITg01`em<0JTg01aJj7oTg01bRj7uTg01ank80MTf0R1#1#1p=cf1R2/31#<p=4%;1#;p=7%01#0p=U%01#0#0#0p=^%01#0#0#0#0#0#0#0p=n%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=Dg01oGR3?621p=>%11#1#1#1#1#1#1#1p=Lg01niR4?621p=91k41p=CP3P4P1P0P2f2R0f3R5f4R6f5R7f6R8f7R9f8R:N<0Jp=Fg01ofR;%<1'2p=B12;1p=@P4P2g02DcP1CVp=[P2g020DR<g020cR=P=g021CR>P1g022JR?Fop=NP0P<P=P=P>P4P2g021cP1CVP?Fop=A1i41p=JP0P<P=P=P>P2P1Fup=RP5P<P=P=P>P0P2P1L0Mp=?%;1#1p=Z%11#;p=K%11#1#1#1p=vg02;lR<#1R?#1R@#1RA#bRB#jRC#]RD%1A#cRE#bRF#jRG%]GS01%;?RH#bRI00HGS02%lC\GS031IB;RB>02C7#}14C8%;<S04#;#7RJ#;S05#7#7#7RK#;#7#7#5RL'213G6g02<QRM#0RN#0RO#U#^RP#U#^#n#DRQ#0RR'>1E7Mp,3sp0RS56G1E8O=6G:%5?RT%5ERU+06RV%5K+041E9Q,GF'21GFSRKf:RW,GF'2f;RX,GFf<RY,4C'8%5ARA'8%LE#LRE#5RZ,8K'21GFYf=R[,4C'8%5<'8%1E#L#L#L#5'2p,2BLRE/OXg050Q%1HRH#5R\g02B[1~I\d5|I#z%yQ3x;pWg024QRQ1OEYPWg051LCr%lDRIPQPXf?R\f@R],3C/fNCW%eC9tCBRB9sC],dD36PQPY1GF]fAR^,4C'8,IFPPCW1dD\56IPSPEp,5modelRPp,4HvspS06p,2HhS07p,5HlazyS08fBR_P^14C_S09%T_S0:,PT&0PT&0OPS0;+0NR`'SS0<P]P\f>RaP[13G\Rb/>R%<bRc%;@#7#5R@'9Rd%q3Re%q4Rf%<2%<1'91>2120L2140KXe3Xd3R3PbPc%CcS0=PRP@%C@RgM9FPWCHRhPdfCRi,3CRj#:Rk%BjRj13G^Rl#:Rm%<lRn#@Ro20GTURp1=;T%@U1=;V[[Rq%@TRrg02CcRsB0DTU2UW<Rt%@V\s^<rRrg02C7Rs#eRV%]sRu1\42Rv&0A4Rw&0@4Rx1_4<Ry/[y'N209x>R>P1P0g022jRzg023JR{'k20810=6z{dB074;2H05R{b6b9b:X04S0>1911^04S0?P1fHS0@,4CRzO1b2b>b?b4b3b1PhPdPkPjPmPoPpPqPtPrPVPuPvPwPx1i4;S0A=AxyR;&03=R=Px%JL9AxyRoP=ARx;oC?C?P>P{b6b9b:X04%@1S0B122LS0C%@0S0D120LS0E'Q[[^04P1PzP6P^O3b2b>b?b4b3b1PYPWf9RLP:P9P8P7P5P0P2P1Q01Q02Q0313G0%UR#n#D#D#D#DRm#U#^#D#D#DRj'>1E5M=6GS1E6OfFS0F56G1E7m1IFz56G1OE8g04`e;p7PQ1OE9P7g04aaCrPQP8fJfKRz,3C/fNCWAsCzB,dD56IfL,4CRI%1J#5RJ'h12IJ1=JI'gQ00fMRI,4CRB/2J1=JBg026ES0GPW%;<#7#Z#K#7#K#K#7#c#5,IFS0HPL&01QS0IDa/YPfNRB#T,PT/S`5XQP114CBS0J/2JPSPEPPQ06Q07Q08p,4Hfd2p,4Hrd2fORkPB14CkRBPYPXPW13GYRd/>j%<dRh%KH#7#5RH'9R|PePfP3PdPh%ChPjPH%CHS0KM9FPLCHS0LP|13GIRh/>R%<hRd/9@R}PePfP3PhPd%CdPRP@PgM9FQ0@CHS0MP}fQRd,3CRh#:S0N%<hRh#@S0O13GkR~#:S0P%B~S0Q13G]R~#:S0R%B~R~PpPqPtPrQ0>Q0?P1fW,4CS0SO1b2b7b8b;b4b3b1b5Q0LP|Q0MP}Q0NQ0OQ0PQ0QQ0RP~PpPqPtPrPVPuPvPwPxP;P=Px%JJR~9AxyR}P=ARx;}C?C?P>P{b6b9b:X04Q0B122JQ0D120J'Q[[^04P1Q0SP7P:O3b2b7b8b;b4b3b1b5PLP:P9P8PiP_P7P6P5NI00WMP1O1Q0J,=JQ05#5R6,hB12B61=6B'gQ00fPRB,4CR7/261=67Q0GP[Q0HPYQ0IDa/YP%Td,PT/S`5XQP112h61>bj19cHR7PePfP3PbPcQ0=PjPHQ0KM9FPYCHS0=P713GBRB/>R%<BRc/9@RbPePfP3PBPc%CcPRP@PgM9FPzCHS0HPbfTRz,3CRc#:S00%BcS05fRRc,3GRB#:S0J%<BR}#@S0S13GiRi#:S0B%BiRiPpPqPtPrPVPuPvPwPx%J6R;9AxyP=PxP4P~g023jS0DPyCV,NxP=1[y;,NxC?C?P>P{b6b9b:X0412161=J21906RJ[[^04P1fZ,4CR~P:PXO3b2b7b8b;b4b3b1b514CcS0R/96P4fSR|,4C1E^m1IF156GXf4PWP6P1J0:1E]m1IF656GPSPEPPQ06Q07Q08PzP|P6%Tz,PT/S`P^P]P\P21>lj19nHR]PePfP3PlPn%CnPjPHQ0KM9FPaCHRHP]1>BR19}@RjPePfP3PBP}%C}PRP@PgM9FPICHRIPjfV,3CRg#:R@%BgRg13GzRR#:R}%BRRRfERB,3GRG#:R3%BGRGPpPqPtPrPVPu&0;4PwQ0A=Ax;AAx;;5RxP>P{b6b9b:%@61266'QP1b2b7b8b;b4b3b1b5PaP[PYP1Q0@PHP]PIPjP@PgP}PRP3PGPpPqPtPr&0<<,{41`4O60=41`4N1`4M5m45m4g03ld+0>=tsVPuP41\40P21\45H0?PwPxQ04,_4Rs/[;,NxP=PxAM4ys%JARs5M41_4?%JZ5M4R?5AxP=AM4y;=M4s=Ax?C?C?P>P{b6b9b:X04X@4XA41825/8A180Z'21806/8A185Z'2[\J^04^@4^A4P1f\,4CPKf[,GFPLPkO5b2b7b8b;b4b3b1b5PWPLP:20Bz2NI0Cb=bCWNP1O11=6hPcPdQ0RP\PaP[Q0=P7Q0HPbQ00Q05Q0JQ0SQ0BPiPpPqPtPrQ0>Q0?P1P~O1b2b7b8b;b4b3b1b5Q0=P7Q0HPbQ00Q05Q0JQ0SQ0BPiPpPqPtPrPVPuPvPwPxP4P;Q0DPyCV,NxP=PxPoP=%JU=Axy=RxoC?C?P>P{b6b9b:X041=61Q0C12U0Q0E'Q[[^04P1P~P:P|O3b2b7b8b;b4b3b1b5PYPXPWPLQ0FPBfDP:P9P8MBwWLP1O1n200100000021100011000bBWKP1O1n200100000021100011000bBWTWEWJW=W\W[WGWWW^WcPSPEPPP_P^Q09Q0<K0EeNL0FQ0GPa%v<#7#7#K#K#Z#Z#c#5,IFP[Q0IDa/YPQ0:Q0;+0I5XQeWUWSWDWIWRWQWPWZWYWXWFWHWOWVW]WbXaDW`W_o"). Qed.

End Tail2.
