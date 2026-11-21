(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy; the exit tactic's thread-pointer and thread-id addresses corrected to this binary's). *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibKnowXfer LibTail SymCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib LibWritevG.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Room.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2ExitBase V2StdioDefs V2Exit V2Startup V2StartupDefs V2StartupFacts V2MainEntry V2LibStdioCall V2OpenFail_defs V2OpenFail_tail V2OpenFail_tail2 V2Open_defs V2Open V2Oom_defs V2Oom V2MemPreds V2Malloc65536 V2DirRead_defs V2MemcpyBase V2Memcpy V2ReadLoop_defs V2ReadLoop V2Grow V2Hdr_defs V2Hdr V2FuzzIface V2TRun_defs V2TRun V2TRunE V2TRunL V2PrintfBufBase V2PrintfBuf V2TRunC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac FPSteps.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2TRunB () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib2V2:V2MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;is_kimg_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C47Corelib4Init5Peano2ltC59OSSVerify5KrLib2V26V2TRun5callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun6paylenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun1LC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C56Stdlib6ZArith4Znat5Nat2Z6inj_ltI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib6Common9CliDriver4Spec:zero_linesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib6Common8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun6slotsTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun5sideTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun5roomTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun5copyPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun9calls_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr6slotsRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop6model2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr6hdr_b2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun<paylen_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun7payloadC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2TRunL:incb_blockC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs8kn_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2TRunL;sideT_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop6in_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun5sideWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun:bufW_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC59OSSVerify5KrLib2V2=V2Malloc655366env_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc65536:live_whereC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C59OSSVerify5KrLib2V2:V2ReadLoop;model2_pureC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC59OSSVerify5KrLib6Common:RefNodesFS>fd_not_devnullC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC69OSSVerify5KrLib6Common9CliDriver8SymDrive;regs_set_a0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injc59OSSVerify5KrLib2V27V2TRunB:kimg_rdn_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_wZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib6Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_emit_has_nilC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2V2;V2StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop:alu_add_wZC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or02C59OSSVerify5KrLib2V26V2TRun;sideW_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib2V27V2TRunC9addiw_decC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK47Corelib5Lists7ListDef6Forall02C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib2V2:V2ReadLoop;vals_ev_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2TRunC6slotsEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer2rvC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer<regs_ok_xferC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun<krange_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXferDknow_ok_xfer_entailsC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib2V27V2TRunC7fe_tailC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib2V27V2TRunL6slotsLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2TRunC8tl1_loopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall7sc_bufpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall8sc_bufszC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2LibStdioCallCstdio_call_sound_frC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive:v_addi_pc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesFSArz_ioctl_winsz_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2TRunL7fz_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AgentLib:t_emit_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appc59OSSVerify5KrLib2V27V2TRunB<zero_lines_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedK46Stdlib9micromega5Tauto8GFormula07K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4emapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib2V26V2Open4fds0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6STOPSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tl_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5p_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2RelocImg7v2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5p_sr2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5p_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6p_sr3eC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6STOPSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop7DATA_RSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op204K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2V2;V2TRun_defs5sr_FEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5sr_TLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tl_sr2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tl_kn2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5kn_TLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tl_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5tl_r1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tl_kn1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5tl_r2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs4p_r1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs4p_r2C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs4p_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5p_r3lC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C59OSSVerify5KrLib2V2;V2TRun_defs5p_r3eC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6p_kn3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5p_kn3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface7A_EMPTYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOTTYI47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib2V27V2TRunB6nl_imgC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2V2;V2TRun_defs5kn_FEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6kn_TL1C1?~~~~~~~~~~~~~~~".
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
ltac2:(KReplay.run1 (kr_t_V2TRunB ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p10000p4p70R0p1000^p4p7210p8P0p1001:p4p7210R0p8P0g001WR0p4p710R1p8g0025R2p4p710P1p8g002Vj1HTg003;j1wTg003Yj1gTg004<j1~Tg004^j1uTg005>j3qTg0069j3KTg006Wj25Tg0077R1j10Tg007WR3j23Tg0083j26Tg008Nj2YTP2k30ITg008ej6sTg009Aj28Tg009^j2>Tg00:8j37j1nTg00:Rj3_Tg00;8k10>Tg00;Vj6^Tg00<?j4\Tg00<fj1TTg00=Kj2PTg00=mj1|Tg00>Mj2XTg00>kj4LTg00?Ij1yTg00?gj1xTg00@Rj2JTg00A5j1cTg00AZj3QTg00B=k20HTg00B_k20GTg00CKk30FTg00Cjj4rTg00D\R2j21Tg00E9j2aTg00E_R4j1VTg00F?j4Nj3pj2ok10ATg00F[j2Wk10DTg00G=k20ETg00GTk20@Tg00H7k30?Tg00HTl<lTg00I9j1CTg00IXk10<Tg00J6k20;Tg00JWj3iTg00K@j2hTg00Kik108Tg00LGk205Tg00Ljk104Tg00MLk403Tg00N7j8RTg00NTk502TP0j6eTg00O2k307Tg00OUj2tTg00P1k200Tg00PNlBkTg00Q4l<dTg00QYj2}Tg00R3j4UTg00R^j7[Tg00SBj3`Tg00Skj2MTg00TWj3ITg00U7k60BTg00U[k70CTg00V?j7{Tg00Vcj8zTg00WGR0f0R5'tp=920005p=2g00WeR6/>5p=;g00XCR7P7P7P6P6P6g00XbP1P1P1f6R8g00YBf5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P1P1P9P:P;P<P=P5M<dp=bP6P6P3f7R>P3P8P9P:P;P<P=P5M<lp=Z1305p==1t50p=<A7650p=BA76;<,6:16=5'}p=?P<g00YiR3g00ZHR?P?g00ZhR@P6P=g00[HRAP5CUg00[oRBF[p=vA76=5p=OP6P7P6P6P4P:P1P;g00\OP<P=P5M<dp=mP7P7P7P6P6P6g00]<P1P1P1P2g00]\P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00^?R2g00^kR4,M=;I5p>0:A`6<=/M4=I25p=E1M<41M=4=I255I2p>09P=P3P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P3P?P?P@P<P=P3P?P?P@P5PBF[K0Cp=:P6P=g00_WP5CUp=FP=P3P?P?P@P5PBF[p=DP<P3P?P?P@P=P5F{p=]P6P=g00`>P5CUp=SP;P3P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI2=59I2<p>06g00`eR4#HR3#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P0%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|2RV%u2R2P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J63R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00aJR_g00ajR`'>Ra20G5<=7_`dB0F60=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA0RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P1%n6%0=R1/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P08%=8%28RiP8%<8%BiD?%2>P611cNRc,P0%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P0%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00bJRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP2P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20560R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c3,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P0K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP2P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;1AKD=<5q:eWGXM7WKXI6WHo"). Qed.

Section TRunB.
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
  Let sideT := sideT sp0 mem0 lim data.
  Let copyP := copyP sp0 data.
  Let slotsL := slotsL sp0 a0s path envv tid data.
  Let L := L data.
  Let cfg := cfg data.
  Let paylen := paylen data.
  Let payload := payload data.
  Let calls := calls data.
  Let at_tl0 := at_tl0 sp0 a0s path envv tid mem0 fs0 stdin0 lim data.

  (* [comment removed for export] *)
  Lemma kimg_rdn_n : forall E M kn (a : Z) (n : nat) bs,
    know_ok RSEGS E M kn -> existsb (is_kimg_cov a (Z.of_nat n)) kn = true ->
    rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0 <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z ->
    rdn RSEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunB ()) ["TRunB"] "p'0h01Hh12Hch23Hinh31xi001xh42Hah54__x1h64__x2h74__x3h84__x4h92a0h:1ih;1ei011eh<1mi021mh=1ni031nh>2n0h?1Ah@2H1hA2H2hB3HexhC3Hj0hD7__arithhE4__ffhF6__sat3hG6__sat4hH6__sat5hI6__sat6hJ6__sat7hK8__varmaphL5__withM4__x5hN4__x6hO4cstrhP5cstr0hQ1fhR5heq_LhS9heq_callshT7heq_cfghU:heq_paylenhV2hii042hihW1lhX2loi052lohY1EhZ2HKh[3HKKh\3Ha0h]3Ha1h^4Himgh_2Hjh`2Hnha1Khb1Mhc2_Hhd3_H0he1ai061ahf2a1i072a1hg2a2i082a2hh2bshi2e0hj1jhk1ki091khl2knhm2n1i0:2n1hn2n2i0;2n2ho1ohp1vi0<1vhq1wi0=1whr1zi0>1bp%0p&0p;1p;4p;2p;3p;6p;<p;7p;8g002Vj17Tg003;j1mTg003Yj1gTg004<j1xTg004^j1OTg00bik40@Tg0077R0j10Tg00d9j2hj3=Tg00eDR1j3STg00Ljj1tTg00D\j2;Tg00e`j1KTg00f>j2sTg007WR2j28Tg00f[j3NTg0083R3j24Tg00g2R4j2PTg00gLk30=Tg00goj3RTg00i:j2VTg00iYj2WTg00jdj3UTg00koj2\Tg00m:j2>Tg00mWk300Tg00OUj21Tg00n:j2|Tg00nZj3fj4QTg00olj3eTg010Mj3zTg010oj6yTg00E9j2FTg00:8j39Tg011JR5j2wTg011bk10GTg012Vk10FTg013Kk10ETg014=k10DTg00<?k40BTg00<fj1rTg014mj2qTg015Uj3pTg00A5j1DTg0169j2oTg016ck20ATg017Tk20?Tg00I9j1ITg00K@j2GTg00SBj3HTg00Skj2^Tg00=mk10>Tg00TWj3]Tg00>Mj2JTg00Kik10<Tg00?Ik10;Tg00?gk10:Tg00LGj2ZTg00AZj3YTg00@Rj2lTg00B=k209Tg009^j2iTg00B_k208Tg00CKk304Tg00Cjk403Tg0184k305Tg018Wk206Tg001Wk607Tg019gk601Tg00F[j2uTg008ej6nTg01;0j2TTg01<;j3`Tg01=Fj2[Tg01>Qj4_Tg01?\j4aTg00HTl<~Tg00>kj4}Tg00R3j4bTg00R^j7dTg00U[j7{Tg00Vcj8cTf0R6#7#7p=vg00aJR7g00ajR8796p=3f6R9g01@TR:f5R;f4R<f3R='Ff2R>Caf1R?/u639p=:g00WGR@/16p=5g01AfRA?N?6p=2A=>?6=978p=6P7P>P?g01C1P8P6Enp=AP:P>P?P6Cap>0IP:P<1F=>P?Ca=9;6p>0Hg00WeRB/i6p=Eg00XCRCPBP5P0P2g01CMP;P<P=P>P?P6M<~p>0CPBP>P?P6C}p=<1lB6p=CPBP?g00_WR2P6Cbp=LPBP?g00`>P6Cbp=M%D6#Dp=B%76#7#7#7p=@P>g00YiR0g00ZHR5P5g00ZhRDPBP?P2P6Cbg00[oR2Fdp=XP?P0P5P5PDP6P2Fdp=kP>P0P5P5PDP?P6F{p=jP<P0P5P5PDP=P0P5P5PDP>P2FdP?P6Gcp=?P9P0P5P5PDP;P<P=P0P5P5PDP>P?P6GcGcp>02g01Cog00`eR0#7R2#7RE#7RF#7RG#vRH#mRI#gRJ%mF#gRK#xRL[%OA%OKRMP:P;P<P=H0@%0>RN,h==SA<#3%xMRO%tKRKVJRJPIP<P=PMP>F:%5;RP%0;RQ,;9%K2RR%KHRH'sRS'8P1p4p710R1P7\6RT%O?RUP3AS>?6#3AN<6>P=P6O1#3'4X3=,P=[RVAN=6?P>P6O1#3'4X3>,P>AS=>?#3RW[AN;6=P<P6O1#3'4X3<,P<\WB0=>?6P?n2001000000120000000WWWQW?PV^WU^QT^?1P6PAf8R1f7RT#0'hf9RUP<O4f:RV,26%01=6U6'4X3A,PAP4PAf;R4,26%0U=6V6'4X3APOf<RWPIPVPUPMP1F:P6f=RX,26%04=6W6'4P3f>RY,2?%0W=6X?POf@RZPIPYPXPMPWF:P612=Zf?R[#0=6Z<PAfCR\,26fBR]#0=6\?POfFR^PIfDR_P\PMP]F:]1]2P;g01E7R\g01FAR`AR>?6fHRa'2fGRb#0RcAR=>?56afIRd%0aReAR<=>3=P7p-0P6g01GJRfg01GgRgn0110>00020000S00X;7Rh;A6PfPOfLS01PIfJRiPdPMPaF:/V6Rjb0W1W2WpXqCW9P>P?P6O31W?6/2^fERk#0Rl1W>?56^%0^Rm1W=>5=b?Ah6PfPOPiPIPaPbPMP^F:/V6Rnb0W1W2X>`X9\P?P6O2AU>?6/2aAU=>?96acAU<=>9=de?Ah6PfPjb0W1W2XkCX>`X9\P>P?P6O31\?6/2^1\>?96^l1>=bRo1;bm/>>Rp<006%3o%3p'4P31><a#31;ac/>=#3POfKRpPIPdPaPMPbF:P61>9i#3%0iRo,;p/>9#3P31>?6#311>?[Rq11?61>>?#3Rr[11=>\r1|?6P?n2001000000120000000X<BX=BRrPq^<B^=BRqP6PUfMRsP>O311UsPrPqP6fOfNS02#0';RqPVP=O311qVfSRqfRRr5f:RUfQRt5eA126qP:fVRufURvP?CQ[^3A[126rP:PvfTRwP?CQ[^3AAf:wq=eAr[AzAUtPs1\W4R4PVEyP:PqPrP4CQP3%5X11WS11Y6186X'4Pv1FI?RXO1=9LK[^:B'4POPwPIPrPtPMfPF:P6%5[11[SfAR[/16186Z'4fXRtPXO1=9LK[^:B'4P311ZS11]6186['4fYR[PXO1=9LK[^:BPOPtPIPuPvPMPwF:P611]S11k6186_'4f\R_PXO1=9LK[^:BPO1FI[RX>0IJtPOP_PIfZP[P6J0HXoOP:f[R:PJPtPX1w6[PBP:f^R[1;6N,FIO1=9LKXrBP>%0?,;:p,4dataRK$0GRL#Ep,5calls=9BLRLeS03PL&0FKRN#Ep,6paylen=9BNRNeS04PN&0EKRX#Ep,3cfg=9BXRXeS05PX&0DKRK#Ep,1L=9BKRKeS06PK1w;[%0[Rt,8QRJP;PQ%EQP[Pt%EtJ0CP<H0BS07PJ%r9S08%09#5S09f`Rt#rS0:%0t#5S0;1qRHS0<18@RRt%5H18@S[[R[%5RRQApRH?VgW4RH%5S\g^4QR_%D2Rk#D#7#KR],qRRv%5]1sR]Ru,8@[\tRtApR]?VgX4QR]%5u\g^4QRQp,3sp0,oIRg%KGRG+0ARu%5g%5G20?gG#5[[RGg00^?RZg00bJR3#I#IRr#IRW#IR4,GB1GBW1GB3R35HB5HBRWg00^kRV'^%I4,GBR41GBr=HB35HB/^V&0>ZR35]Z3]%OZRr1JB;&0<BRs7<<1JB9?<9s7<>1JB=RU7<?&0;BRx&0:BRyPy1ZB@Rz%D0R{#CR|'L%t5R5PyPy%7k#CR},M|P5PyPy%C2R2=YB}%CER}'LP5PyPy1lB0R0/L2P5PyPy%B{#B#B#B#B#B#B#7#v#@#@#@#@#@#@#@#KR{,ZBR~%CFRF'LP5AYB2|R29Xy01M2},ky5jyD?D?D?D?D?209yDRDP6P>1i782086>#3dB04B@?H03R@bEbKbLX5BX6BX7BX8BXMBXNB%5>18=91;=T/1;11=<11{11;9TR9,1;1891'4[[[[[^5B^6B^7B^8B^MB^NBP6fg#0R9PgPq%0YRYfhRqPwPTP1PaPip,4SPloR8O;bDbFbGbHbIbJbPbObCbRbTbUbSO21FI:,oIQ03PLQ04PNQ05PXQ06PKQ07PJQ08Q09Q0:Q0;Q0<P[PHP_PvPtP]PQPuPGAHB4W/^V=]Z3PrA<U<s1JB<?<<s?<<s7<<1JB>?<<s7<?PxPyPy%DE#7#CRE,LzP5PyPy1MEFP5PyPyAYB0F1ZBR>05BIRR'MP5PyAXyz0RzP5Py%Ck9Xy~P51M0R,ky9jyzK02D?D?D?PDP@bEbKbLX5BX6BX7BX8B%5=R@18<=1;></8S11{;18;S,4P[\@[[[^5B^6B^7B^8BP6PYP9PgPqPTP1fafbP8O9bDbFbGbHbIbJbPbObCbRbTbUbS-06:J07W_XjCJ01fW,uMPwEnW`WdP?P6O2n2001000000121000000W0WcP?P6O2n2001000000121000000b[bAb0b@b0WAW@P?P6O2n2001000000121000000b1W1W2XVBXXBP?P6O21T?6/2^1T>?96^l1T=>9=bmQ00Xi7R7;A6PfPnb0W1W2X<BX;`P?P6O2A`>?6/2aA`=>?96acA`<=>9=de?A76PfPjb0W1W2XVBXXBX;`P>P?P6O31[?6/2^1[>?96^l1[=>9=bm?Ah6PfPnb0W1W2X>BX9\P?P6O2P=P>P?P6C_/2i%0dP<P=P>P?C_56iP;P<P=P>C_9=po?Ah6PfPOQ02PIQ01PpPMPiF:/V6b0W1W2XnBXg\XmBXf\P=P>P?P6O4n0110900083010610=10<2010610330106103109211051042010110230101105104201061034010710:10810;P?P6O2W1W2P?P6O2n2001000000121000000W0XaAP?P6O2n2001000000121100000bBb0W]W\W^WBWZWhX=CXeBWlWbWYo"). Qed.

  Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10a4c) 1 = Some [Z_to_bv 8 10].
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunB ()) ["TRunB"] "p;1p;2p;3p;4g002Vj12Tg003;j16Tg003Yj13Tg004^j1BTg004<j1<Tg00A5j11Tg00e`j14Tg01HCj2;Tg01I6j3:Tg00=mj19Tg00TWj35Tg00F[j27Tg009^j2ATg00Ljj1@Tg00E9j28Tg00I9j1=Tg01?\j4>Tg00:8j3?Tf0#2#2p=0g00`eR0#2R1#0R2#6R3#3R4#BR5#<R6%11#2#4R11;315:3%94R7554,75'Ag01@T%22#0#6R2#3%@4U%00#0#1#2#1#0#1#0#1#1#0#4,82g00bJ#=C>1831=547,755?6do"). Qed.

  Lemma zero_lines_S : forall n, zero_lines (S n) = [Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines n.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunB ()) ["TRunB"] "h01np;1p;2p;3g002Vj10Tg003;j1;Tg003Yj1:Tg004^j15Tg00A5j14Tg00e`j13Tg00E9j21Tg00=mj19Tg00TWj32Tg01IYj16Tg01J^j37Tg009^j28Tg00XCg00`eR0#0R1#0#0#;R2#:R3#5%40#0#0#0#0#3,12%41#0#3,12%93523523f0#6573'8W0o"). Qed.

  Theorem tl0_run : forall j buf cap,
    at_tl0 (t_emit (W 1 (zero_lines (Z.to_nat calls))) (t_exit (exit_code 0) fs0)) j buf cap.
  Proof.
    intros j buf cap fxp A vm vals R M aligned owned FRM HL SL HR HK HS HRT HC HB HcapL Hcap26 HLc.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0. pose proof (calls_rng sp0 data) as Hcr4. fold calls in Hcr4.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    destruct (paylen_facts sp0 Hvsp data HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcfr).
    unfold model2, V2ReadLoop.model2.
    replace (Z.to_nat calls) with (S (Z.to_nat calls - 1)) by lia. set (n1 := (Z.to_nat calls - 1)%nat).
    rewrite zero_lines_S. unfold W. rewrite map_app.
    lazymatch goal with |- realizes _ ?c (t_emit (?a ++ ?b) ?X) =>
      apply (rz_conseq RSEGS _ (t_emit a (t_emit b X))); [| apply t_eq_sym; apply t_emit_app] end.
    run_blk_keep scr0 50%nat.
    lazymatch type of EQM with ?Mn = mem_denot _ _ _ => rename Mn into Mq end.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap owned E log HS ltac:(vm_compute; reflexivity) P0) as [HSb _] end.
    rewrite <- EQM in HSb.
    assert (OUTb : forall x : word, bv_unsigned x <> 0x56174%Z -> Mq x = M x).
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
      intros i Hi. unfold V2TRun.L in *. rewrite <- (HB i Hi). apply OUTb. rewrite u_small by lia. lia. }
    clear EQM OUTb HS HC HB. clear M. rename Mq into M. rename HSb into HS. rename HCb into HC. rename HBb into HB.
    destruct tl_itin as (_ & _ & VLK1 & VLS1 & KF & _ & IP1 & SP1 & IP2 & SC & SCF & IP3l & IP3e & KA3 & SP3).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) ?K =>
      apply (fz_call sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp data AL_segs AL_rom AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw
               AL_hi AL_env FZ fxp K A vm vals Rc M buf cap aligned owned calls tl_kn1 FRM HL SL0 HR HK VLK1
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HS HC HB HcapL Hcap26 HLc ltac:(clear -Hcr4; lia) HRT) end.
    clear HR HK. intros fx2 A' vm' M' R' FRM2 HR HK HS' HC' HB' HFR HRT'. clear FRM. clear fxp.
    rewrite KF in HK. clear HS HC HB HFR HRT.
    set (vals2 := vals ++ junk_vals R') in *.
    assert (HL2 : length vals2 = 82%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q16 : vals_ev vals2 16 = Z_to_bv 64 calls) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P16).
    assert (SL2 : slotsL vals2 buf aligned owned calls).
    { subst vals2. unfold slotsL, V2TRunL.slotsL, slotsT, V2Hdr.slotsR; repeat split; rewrite ?vals_ev_app_l by (rewrite HL; lia); assumption. }
    clearbody vals2. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
    clear P0 P1 P2 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 SL0.
    destruct SL2 as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    run_blk_keep scr0 82%nat.
    lazymatch type of EQM with ?Mn = mem_denot _ _ _ => rename Mn into Mq end.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M' buf cap owned E log HS' ltac:(vm_compute; reflexivity) Q0) as [HSb _] end.
    rewrite <- EQM in HSb.
    assert (OUTb : forall x : word, bv_unsigned x <> 0x56174%Z -> Mq x = M' x).
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
      intros i Hi. unfold V2TRun.L in *. rewrite <- (HB' i Hi). apply OUTb. rewrite u_small by lia. lia. }
    clear EQM OUTb HS' HC' HB'. clear M'. rename Mq into M'. rename HSb into HS'. rename HCb into HC'. rename HBb into HB'.
    run_blkP_keep scr0 82%nat.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M' buf cap owned E log HS' ltac:(vm_compute; reflexivity) Q0) as [HS1 OUT1] end.
    rewrite <- EQM in HS1, OUT1.
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A' vm' M' buf cap (proj1 HS')) as (Hb0 & Hb1 & Hal & Hbb).
    pose proof HS' as HS'0. destruct HS' as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    assert (HC1 : copyP M0 aligned owned).
    { destruct HC' as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi.
      apply OUT1; [unfold V2ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
    assert (HB1 : bytes_at M0 (bv_unsigned buf) data).
    { intros i Hi. unfold V2TRun.L in *. rewrite <- (HB' i Hi). apply OUT1; [unfold V2ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
    clear EQM OUT1 HC' HB' HS'0.
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x3e8e0) = Some ECALLW) by (vm_compute; reflexivity).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A17 : bv_unsigned (getr Rc 17) = 29%Z) by (regv HR (17 : reg); reflexivity);
      assert (A10 : getr Rc 10 = Z_to_bv 64 1) by (regv HR (10 : reg); reflexivity);
      assert (A11 : bv_unsigned (getr Rc 11) = 0x5413%Z) by (regv HR (11 : reg); reflexivity);
      apply (rz_ioctl_winsz_at RSEGS Rc _ _ (seg_rom RSEGS) _ ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)) _
               (model2_pure tid fs0 stdin0 vm') HF is_ecall_ECALLW A17 A10 ltac:(rewrite u_small by lia; lia) eq_refl eq_refl A11);
      clear A17 A10 A11 HF
    end.
    rewrite v_addi_pc4 by lia. change (0x3e8e0 + 4)%Z with 0x3e8e4%Z.
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_set_a0 E sr Rc (errno_ret ENOTTY) (ELit (2 ^ 64 - 25)) HR ltac:(apply bv_eq; vm_compute; reflexivity)) as HR2 end.
    clear HR. rename HR2 into HR.
    run_blkP_keep scr0 82%nat.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M0 buf cap owned E log HS1 ltac:(vm_compute; reflexivity) Q0) as [HS2 OUT2] end.
    rewrite <- EQM in HS2, OUT2.
    assert (HC2 : copyP M1 aligned owned).
    { destruct HC1 as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi.
      apply OUT2; [unfold V2ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
    assert (HB2 : bytes_at M1 (bv_unsigned buf) data).
    { intros i Hi. unfold V2TRun.L in *. rewrite <- (HB1 i Hi). apply OUT2; [unfold V2ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
    clear EQM OUT2 HC1 HB1 HS1.
    assert (Hnl : rdn RSEGS M1 (Z_to_bv 64 0x10a4c) 1 = Some [Z_to_bv 8 10]).
    { lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (kimg_rdn_n (ENV vals2) M1 kn 0x10a4c 1 _ HK ltac:(vm_compute; reflexivity) nl_img); lia end. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?md) (t_emit _ ?K) =>
    apply (stdio_call_sound_fr vals2 (blobs_ev (blobs0 a0s path)) p_sr2 p_kn2 Rc Mc md p_sc [Z_to_bv 8 48] [Z_to_bv 8 10] K
             HR HK (eq_trans (f_equal (fun n => stdio_call n p_sr2 p_kn2) HL2) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn p_sc length Z.of_nat] end.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. reflexivity.
    - cbn. lia.
    - cbn. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV V2Open.ENV]; rewrite ?Q0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV V2Open.ENV]; rewrite ?Q0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. krd_solve HK.
    - cbn [edenot]. exact Hnl.
    - reflexivity.
    - exact a_reader.
    - reflexivity.
    - reflexivity.
    - apply t_emit_has_nil.
    - clear HR HK. intros Rw M2 HR HK HPOST.
      destruct HPOST as [Pagree Pgrows _ _ _]. cbn [edenot ev ENV V2Open.ENV] in Pagree. rewrite Q0 in Pagree.
      rewrite alu_add_wZ, u_small in Pagree by lia.
      assert (HS3 : sideT A' vm' M2 buf cap owned).
      { destruct HS2 as (HW2 & HSl & HSn). split; [| split; [exact HSl | exact HSn]].
        apply (sideW_frame sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A' vm' M1 M2 buf cap HW2); [| exact Pgrows].
        intros x Hne.
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 1296 - 112)) as [Y1|Y1];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 1296)) as [Y2|Y2]; [left; unfold V2ReadLoop.in_win; lia|]];
          (destruct (Z_lt_ge_dec (bv_unsigned x) (0x46020 + 32)) as [Y3|Y3];
            [| destruct (Z_lt_ge_dec (bv_unsigned x) (0x46020 + 64)) as [Y4|Y4]; [right; left; unfold in_data; lia|]]);
          exfalso; apply Hne; apply Pagree; lia. }
      assert (HC3 : copyP M2 aligned owned).
      { destruct HC2 as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
        split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
        pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
        intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply Pagree; rewrite u_small by lia; lia. }
      assert (HB3 : bytes_at M2 (bv_unsigned buf) data).
      { intros i Hi. unfold V2TRun.L in *. rewrite <- (HB2 i Hi). apply Pagree; rewrite u_small by lia; lia. }
      clear HS2 HC2 HB2 Pagree Pgrows Hnl M0 M1.
      set (vals3 := vals2 ++ junk_vals Rw) in *.
      assert (HL3 : length vals3 = 114%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (T0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q0).
      assert (T16 : vals_ev vals3 16 = Z_to_bv 64 calls) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q16).
      assert (SL3 : slotsL vals3 buf aligned owned calls).
      { subst vals3. unfold slotsL, V2TRunL.slotsL, slotsT, V2Hdr.slotsR; repeat split; rewrite ?vals_ev_app_l by (rewrite HL2; lia); assumption. }
      clearbody vals3. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
      clear P0 P1 P2 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 Q0 Q16.
      destruct SL3 as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
      assert (ADD16 : (sext 64 (alu32 ALU_ADD (low32 (vals_ev vals3 16)) (low32 (Z_to_bv 64 (-1)))) : word) = Z_to_bv 64 (calls - 1)).
      { rewrite T16, addiw_dec by lia. reflexivity. }
      destruct (Z.eq_dec calls 1) as [Hc1|Hc1].
      +
        run_blkP_keep (SCR [false] [] []) 114%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V2Open.ENV]. rewrite ADD16, Hc1. reflexivity. }
        lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
          destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M2 buf cap owned E log HS3 ltac:(vm_compute; reflexivity) T0) as [HS4 OUT4] end.
        rewrite <- EQM in HS4, OUT4.
        assert (HC4 : copyP M0 aligned owned).
        { destruct HC3 as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
          split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
          pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
          intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi.
          apply OUT4; [unfold V2ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
        clear EQM OUT4.
        subst n1. rewrite Hc1. change (Z.to_nat 1 - 1)%nat with 0%nat.
        let rv := eval vm_compute in fe_rvlp in
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
          apply (fe_tail sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data AL_segs AL_rom AL_free AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw
                   AL_hi AL_ret AL_env 0%nat buf cap fx2 A' vm' (map (edenot (ENV vals3)) rv) Rx Mx aligned owned (Z_to_bv 64 0x76940)) end.
        * rewrite length_map. reflexivity.
        * unfold slotsE, V2Hdr.slotsR; repeat split; rewrite vals_ev_map by (cbn; lia); cbn [nth edenot ev ENV V2Open.ENV]; assumption.
        * rewrite vals_ev_map by (cbn; lia). reflexivity.
        * lazymatch goal with |- regs_ok (_ (map _ ?rvl)) _ _ =>
            change (V2Open.ENV a0s path (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HR with regs_ok _ ?sr _ =>
              p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) rvl idb _ (fun k => eq_refl) srb sr_FE _ HR eq_refl eq_refl)) end end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[Hi|[]]]; [exfalso; lia|]. subst i. cbn [nth emap edenot ev ENV V2Open.ENV idb]. rewrite ADD16, Hc1. reflexivity.
        * lazymatch goal with |- know_ok _ (_ (map _ ?rvl)) _ _ =>
            change (V2Open.ENV a0s path (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              apply (know_ok_xfer_entails RSEGS (ENV vals3) rvl idb _ _ kn kn_FE (fun k => eq_refl) HK) end end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply krange_intro. cbn [edenot]. unorm. lia.
        * exact HS4.
        * exact HC4.
        * split; [reflexivity | split; [unorm; reflexivity | lia]].
        * lia.
        * exact HcapL.
      +
        run_blkP_keep (SCR [true] [] []) 114%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V2Open.ENV]. rewrite ADD16. unfold bv_eqb. rewrite !u_small by lia.
          replace (calls - 1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
        lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
          destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M2 buf cap owned E log HS3 ltac:(vm_compute; reflexivity) T0) as [HS4 OUT4] end.
        rewrite <- EQM in HS4, OUT4.
        assert (HC4 : copyP M0 aligned owned).
        { destruct HC3 as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
          split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
          pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
          intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi.
          apply OUT4; [unfold V2ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
        assert (HB4 : bytes_at M0 (bv_unsigned buf) data).
        { intros i Hi. unfold V2TRun.L in *. rewrite <- (HB3 i Hi). apply OUT4; [unfold V2ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
        clear EQM OUT4.
        replace n1 with (0 + n1)%nat by lia.
        let rv := eval vm_compute in tl1_rvl0 in
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
          apply (tl1_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data AL_segs AL_rom AL_free AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw
                   AL_hi AL_ret AL_env FZ n1 0%nat buf cap fx2 A' vm' (map (edenot (ENV vals3)) rv) Rx Mx aligned owned (Z_to_bv 64 0x76940) FRM2) end.
        * rewrite length_map. reflexivity.
        * unfold V2TRunL.slotsL, slotsT, V2Hdr.slotsR; repeat split; rewrite vals_ev_map by (cbn; lia); cbn [nth edenot ev ENV V2Open.ENV];
            first [assumption | rewrite ADD16; f_equal; lia].
        * rewrite vals_ev_map by (cbn; lia). reflexivity.
        * lazymatch goal with |- regs_ok (_ (map _ ?rvl)) _ _ =>
            change (V2Open.ENV a0s path (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HR with regs_ok _ ?sr _ =>
              p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) rvl idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * lazymatch goal with |- know_ok _ (_ (map _ ?rvl)) _ _ =>
            change (V2Open.ENV a0s path (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              apply (know_ok_xfer_entails RSEGS (ENV vals3) rvl idb _ _ kn kn_TL1 (fun k => eq_refl) HK) end end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply krange_intro. cbn [edenot]. unorm. lia.
        * exact HS4.
        *
          replace (Z.of_nat n1) with (calls - 1)%Z by (subst n1; clear -Hcr4; lia). exact HRT'.
        * exact HC4.
        * exact HB4.
        * split; [reflexivity | split; [unorm; reflexivity | lia]].
        * lia.
        * lia.
        * exact HcapL.
        * exact Hcap26.
        * exact HLc.
  Qed.
End TRunB.
