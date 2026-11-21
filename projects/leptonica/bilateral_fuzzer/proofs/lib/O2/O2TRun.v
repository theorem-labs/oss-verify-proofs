(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (proofs and definitions restated for the model's changed definitions; the recorded (KReplay) proofs of tm_step and trun_entry re-proved by tactics, as pix_orient_fuzzer's copy; side_W, bufW_facts and sideW_frame re-proved by tactics for the ledger's vDSO reservations; the exit tactic's thread-pointer and thread-id addresses corrected to this binary's). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibKnowXfer LibTail SymCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec Room.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2ExitBase O2StdioDefs O2Exit O2Startup O2StartupDefs O2StartupFacts O2MainEntry O2LibStdioCall O2OpenFail_defs O2OpenFail_tail O2OpenFail_tail2 O2Open_defs O2Open O2Oom_defs O2Oom O2MemPreds O2Malloc65536 O2DirRead_defs O2MemcpyBase O2Memcpy O2ReadLoop_defs O2ReadLoop O2Grow O2Hdr_defs O2Hdr O2FuzzIface O2TRun_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac FPSteps.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2TRun () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib2O2:O2MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib6Common9CliDriver8SymDrive?nth_map_seq_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop9buf_factsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun5sideWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop5al_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop5vm_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc655366env_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic3and01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase<ai_live_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7round16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop:round16_geC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib2O2=O2Malloc65536;live_big_loC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib2O25O2Hdr7cfg_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O25O2Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib2O26O2TRun3cfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun1LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun6paylenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun7payloadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O25O2Hdr6b2_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O25O2Hdr6hdr_b2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib2O26O2TRun5callsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib2O2?O2OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib6Common9CliDriver<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver<RefPrintfLib:alu_and3_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7div_1_rC56Stdlib6ZArith6BinInt1Z7pow_0_rC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics5Riscv3Sem5alu64I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs4kn_TC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs5kn_TLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7calls_xC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2O2;O2TRun_defs7t_itin1C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs5t_r1aC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib2O2;O2TRun_defs5t_r1cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C59OSSVerify5KrLib2O2;O2TRun_defs5t_r1bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs5t_r1dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tm_rvlaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6t_sr1aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs5sr_TMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs5t_kn1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tm_rvlcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6t_sr1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs4kn_RC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tl_rvlbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6t_sr1bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs5sr_TLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tl_rvldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6t_sr1dC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc65536<ownedA_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00c59OSSVerify5KrLib2O26O2TRun=ownedA_rangeTC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2O2:O2ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs9kn_acallTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Oom_defs4GLOBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2O26O2Open9above_sp0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3lebC46Stdlib4Bool4Bool3eqbC59OSSVerify5KrLib2O2:O2Hdr_defs4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC59OSSVerify5KrLib2O25O2Hdr7in_zseqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C46Stdlib4Bool4Bool8eqb_propc59OSSVerify5KrLib2O26O2TRun7sgn_tabC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop6in_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun:bufW_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib6Common8Mallocng9AllocBase9grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib6Common8Mallocng9AllocBase8ai_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init5Logic4True01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_wdlC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S?mem_denot_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun;sideW_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop7DATA_RSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall;entry_wdl_bC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C69OSSVerify5KrLib6Common9CliDriver7SymCall;entry_win_bC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00c59OSSVerify5KrLib2O26O2TRun6at_tl0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun6slotsMC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O25O2Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lc59OSSVerify5KrLib2O26O2TRun<paylen_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_malloc_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIfaceAfuzz_margin_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIface;fuzz_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure?alloc_margin_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure<alloc_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room7need_loC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsc59OSSVerify5KrLib2O26O2TRun=env_ok_allocTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room8fuzz_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room;fuzz_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:aroom_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun5roomTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc655367live_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun>bytes_at_skipnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase@ai_live_disjointC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib5Lists7ListDef3seqC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRunAknow_after_allocTC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Grow<bytes_at_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC59OSSVerify5KrLib6Common7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc65536:live_whereC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes?pair_equal_specC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib2O2:O2ReadLoop;vals_ev_mapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun6slotsTC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer2rvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4emapC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer<regs_ok_xferC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXferDknow_ok_xfer_entailsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure>ai_malloc_sureC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun5at_tmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open4fds0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6tm_sr2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6STOPSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tl_rvlmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tm_kn3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6tm_srMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6tm_knMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib2O2;O2TRun_defs7tm_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs5tm_r2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6tm_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tm_sr3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs5tm_r3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6tm_sr3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs6tm_kn3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIfaceAfuzz_calls_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun9calls_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure9ROOM_NMAXC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2O2>O2MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2MallocLayout6LS17okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tn_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2TRun_defs7tn_kn1iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FPSteps?fp_frm_zero_fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIface7A_EMPTYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O25O2Hdr6slotsRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop4sideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop6model2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun6side_WC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib2O26O2TRun7tm_stepC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib2O2:O2ReadLoop>side_block_wdlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun;calls_x_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2TRun8tr_shapeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib2O2:O2Hdr_defs4sr_RC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

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
      as Ktid; cbn [kentry_ok edenot ev O2Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x49840), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev O2Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev O2Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev O2Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev O2Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev O2Open.ENV] in Ktid |- *; lia
      | cbn [ev O2Open.ENV] in Ktid |- *; lia
      | lit_u; change (301120 - 168)%Z with 0x49798%Z;
        let Htc := fresh "Htc" in
        krd HK 0x49798%Z 4%nat Htc; rewrite Htc; cbn [ev O2Open.ENV] in Ktid |- *;
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
ltac2:(KReplay.run1 (kr_t_O2TRun ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0g0022R0p4p710p8p1002Rp4p70g003BR1p4p710R2p8p1003`p4p70P2p8p1004Np4p7210P2p8p1005:p4p70P2p8g0060R3p4p710P2p8g006Qj1HTg0076j1wTg007Tj1gTg0087j1~Tg008Yj1uTg0099j3qTg00:4j3KTP0j25Tg00:RR0j10Tg00;2R2j23Tg00;Nj26Tg00;ij2YTP3k30ITg00<@j6sTg00<\j28Tg00=9j2>Tg00=Sj37j1nTg00=mj3_Tg00>Sk10>Tg00?1j6^Tg00?Zj4\Tg00@Aj1TTg00@fj2PTg00AHj1|Tg00Ahj2XTg00BFj4LTg00Bdj1yTg00CBj1xTg00Cmj2JTg00DPj1cTg00E5j3QTg00EXk20HTg00F:k20GTg00Ffk30FTg00GEj4rTg00H7R3j21Tg00HTj2aTg00I:R4j1VTg00IZj4Nj3pj2ok10ATg00J6j2Wk10DTg00JXk20ETg00Jok20@Tg00KRk30?Tg00Kol<lTg00LTj1CTg00M3k10<Tg00MQk20;Tg00N2j3iTg00N[j2hTg00ODk108Tg00Obk205Tg00PEk104Tg00Pgk403Tg00QRj8RTg00Qok502TP1j6eTg00RMk307Tg00S0j2tTg00SLk200Tg00SilBkTg00TOl<dTg00U4j2}Tg00UNj4UTg00V9j7[Tg00V]j3`Tg00WFj2MTg00X2j3ITg00XRk60BTg00Y6k70CTg00YZj7{Tg00Z>j8zTg00ZbR1f0R5'tp=920015p=2g00[@R6/>5p=;g00[^R7P7P7P6P6P6g00\=P0P0P0f6R8g00\]f5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P0P0P9P:P;P<P=P5M<dp=bP6P6P2f7R>P2P8P9P:P;P<P=P5M<lp=Z1315p==1t51p=<A7651p=BA76;<,6:16=5'}p=?P<g00]DR2g00]cR?P?g00^CR@P6P=g00^cRAP5CUg00_JRBF[p=vA76=5p=OP6P7P6P6P4P:P0P;g00_jP<P=P5M<dp=mP7P7P7P6P6P6g00`WP0P0P0P3g00a7P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00aZR3g00bFR4,M=;I5p>0:A`6<=/M4=I35p=E1M<41M=4=I355I3p>09P=P2P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P2P?P?P@P<P=P2P?P?P@P5PBF[K0Cp=:P6P=g00c2P5CUp=FP=P2P?P?P@P5PBF[p=DP<P2P?P?P@P=P5F{p=]P6P=g00cYP5CUp=SP;P2P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI3=59I3<p>06g00d@R4#HR2#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P1%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|3RV%u3R3P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J62R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00deR_g00eER`'>Ra20G5<=7_`dB0F61=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA1RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P0%n6%0=R0/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P18%=8%28RiP8%<8%BiD?%2>P611cNRc,P1%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P1%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00eeRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP3P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20561R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c2,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P1K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP3P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;0AKD=<5q:eWGXM7WKXI6WHo"). Qed.

Section TRun.
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
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2f94c.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2f80c.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x49840.
  Hypothesis AL_glob : forall a, al_globals a -> (0x69b38 <= bv_unsigned a < 0x69ee8)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x6b000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x4979c <= bv_unsigned a < 0x497a0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x6b000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x6b000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x6b000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := O2Open.ENV a0s path.
  Let model2 := model2 tid fs0 stdin0.
  Let side := side sp0 mem0 lim.
  Let slotsR := slotsR sp0 a0s path envv tid data.
  Let at_trun := at_trun sp0 a0s path envv tid mem0 fs0 stdin0 lim data.

  Definition L : Z := Z.of_nat (length data).
  Definition cfg : Z := hdr_cfg data.
  Definition paylen : Z := (L - 6 - cfg)%Z.
  Definition payload : list byte := skipn (Z.to_nat (6 + cfg)) data.
  Definition calls : Z := (if cfg =? 0 then 1 else 1 + hdr_b2 data mod 4)%Z.
  Definition counting : bool := (128 <=? hdr_b1 data)%Z.

  (* [comment removed for export] *)
  Definition tr_shape (K : TSet) : TSet := K.

  (* [comment removed for export] *)
  Definition roomT (A : AS) (vm : VmMaps) (rem : Z) : Prop :=
    aroom A vm (fuzz_k FUZZ_CALLS rem) (fuzz_b FUZZ_BMAX rem).

  Definition slotsT (vals : list word) (buf aligned owned : word) (rem : Z) : Prop :=
    slotsR vals buf /\ vals_ev vals 13 = Z_to_bv 64 calls /\ vals_ev vals 14 = aligned /\ vals_ev vals 15 = owned
    /\ vals_ev vals 16 = Z_to_bv 64 rem.

  (* [comment removed for export] *)
  Definition sideW (A : AS) (vm : VmMaps) (M : word -> option byte) (buf : word) (cap : Z) : Prop :=
    ainv A M vm /\ live A buf = Some cap
    /\ vm_limit vm = lim /\ alloc_top vm = (bv_unsigned sp0 - 8388608)%Z /\ vm_init_sp vm = sp0
    /\ vm_resv (segments_reserved RSEGS) sp0 vm
    /\ env_ok sp0 mem0 M /\ (65536 <= cap)%Z.
  (* [comment removed for export] *)
  Definition sideT (A : AS) (vm : VmMaps) (M : word -> option byte) (buf : word) (cap : Z) (owned : word) : Prop :=
    sideW A vm M buf cap
    /\ ((0 < paylen)%Z -> live A owned = Some paylen)
    /\ (forall q, q <> buf -> ((0 < paylen)%Z -> q <> owned) -> live A q = None).

  Lemma side_W : forall A vm M buf cap j, side A vm M buf cap j -> sideW A vm M buf cap.
Proof.
  intros A vm M buf cap j ((HI & Hl & _ & _) & (Hvl & Htop & Hisp & Hres) & HE & Hcap & _).
  assert (Hc1 : (2 ^ 0 <= 2 ^ Z.of_nat j)%Z) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 0)%Z with 1%Z in Hc1.
  unfold sideW. refine (conj HI (conj Hl (conj Hvl (conj Htop (conj Hisp (conj Hres (conj HE _))))))). lia.
Qed.

  Lemma bufW_facts : forall A vm M buf cap, sideW A vm M buf cap ->
    (0x6b000 <= bv_unsigned buf)%Z /\ (bv_unsigned buf + cap <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned buf mod 16 = 0)%Z
    /\ (forall x : word, (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z -> M x <> None /\ owned A x).
Proof.
  intros A vm M buf cap (HI & Hl & _ & Htop & _ & _ & _ & Hcap).
  destruct (ai_live_hull A M vm buf cap HI Hl) as (Hc0 & Hal & Hend & Hbytes).
  pose proof (O2ReadLoop.round16_ge cap) as Hr.
  split; [exact (O2Malloc65536.live_big_lo sp0 Hvsp AL_grant A M vm buf cap HI Hl ltac:(lia))|].
  split; [lia|]. split; [exact Hal|].
  intros x Hx.
  assert (Ea : at_ buf (bv_unsigned x - bv_unsigned buf) = x).
  { unfold at_. apply bv_eq. rewrite u_small by (pose proof (u64_range x); lia). lia. }
  destruct (Hbytes (bv_unsigned x - bv_unsigned buf)%Z ltac:(lia)) as (Ho & Hd & _).
  rewrite Ea in Ho, Hd. exact (conj Hd Ho).
Qed.

  (* [comment removed for export] *)
  Definition copyP (M : word -> option byte) (aligned owned : word) : Prop :=
    ((0 < paylen)%Z -> aligned = owned /\ bytes_at M (bv_unsigned aligned) payload
                     /\ (0x1000 <= bv_unsigned aligned)%Z /\ (bv_unsigned aligned + paylen <= bv_unsigned sp0 - 8388608)%Z
                     /\ (bv_unsigned aligned mod 16 = 0)%Z)
    /\ (paylen = 0%Z -> owned = Z_to_bv 64 0 /\ aligned = Z_to_bv 64 A_EMPTY).

  (* [comment removed for export] *)
  Definition at_tl0 (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall (fxp : FPState) A vm vals R M aligned owned,
      frm_zero (@fp_csr fxp) ->
      length vals = 50%nat -> slotsT vals buf aligned owned calls ->
      regs_ok (ENV vals) sr_TL R -> know_ok RSEGS (ENV vals) M kn_TL ->
      sideT A vm M buf cap owned -> roomT A vm calls -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
      (L < cap)%Z -> (cap <= 67108864)%Z -> (6 + cfg <= L)%Z ->
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x179a0) M (seg_rom RSEGS)) (model2 vm)) K.

  Lemma paylen_facts : (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z ->
    (0 <= paylen < 2 ^ 26)%Z /\ Z.of_nat (length payload) = paylen /\ (0 <= cfg < 32768)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "h02Hah11xh24__p1h34__p2h44__p3h54__x1h64__x2h74__x3h84__x4h94__x5h:1nh;2H1h<2H2h=2H3h>2H4h?2Hch@7__arithhA4__ffhB6__sat5hC6__sat6hD6__sat7hE6__sat8hF6__sat9hG8__varmaphH5__withI4cstrhJ1mhK1yhL2z3hM2z4p&0p;1p;2p;3p;<p;6p;4p;Bp;7p;8g00DPj1>Tg006Qj11Tg00kaj1<Tg00H7j2KTg00S0j27Tg0194j2^Tg00;2j24Tg01LDj2pTg01M9j1kTg00;Nj20Tg0076j1VTg007Tk10;Tg0022j2TTg00I:R0k103Tg00;ij2~Tg00:RR1j1LTg00<\j26Tg00=9j2?Tg00=mj3\Tg00=Sj1lj3ITg00>Sj1jTg00Kol<eTg00?1j6aTg00@Aj1cTg00@fj2YTg00U4j2MTg01Fkj2XTg01GSj3WTg00l?j2bTg01F:k20=Tg00lik20<Tg00LTj1;Tg00M3k10:Tg00MQk209Tg00N2j3`Tg00N[j2_Tg00AHk102Tg008Yj1}Tg00Ahj2PTg00ODj1uTg00BFj4STg00Bdj1rTg00CBj1qTg00Cmj2GTg00RMj3QTg00Obj2HTg00PEj1oTg00E5j3nTg01Mnj3mTg00EXj2sTg00F:j2tTg00Ffj3vTg00GEj4wTg00Pgj4xTg00:4j3yTg0060j3zTg003Bj6{Tg00SLj2|Tg00TOl<]Tg00SimB00Tg00V]k301Tg00WFj2fTg00X2k304Tg00XRk605Tg00UNj4UTg00V9k706Tg00Y6k707Tg00YZj7dTg00Z>k808Tg00ZbR2f0R3'7p=2%13#1p=Z%13#1#1#1p=8g00[@R4f1R5;I3p=91|23p=DP4g00[^R6P4P4P0f4R0P1f3R7g00_jf2R8P5P3M<]p=iP6P6P6P4P4P4g00\=P1P1P1f6R9g00\]f5R:P0P7P8P5P3NB00p=hP6P4P4P4P1P1P:P0P7P8P5P3M<]p=g1423p=BAI432p=J%>3#>p==1_43p=EB01453p=5g00bF,f3p=Fg00aZR1@0453p=@P5g00]DR;g00]cR<P<g00^CR=P3J05p=RP4P5g00^cP3CUp=NP5P;P<P<P=P3g00_JK06p=3P8P;P<P<P=P5P3K07p=:P4P5g00c2P3CUp=CP8P;P<P<P=P5P3Fdp=[P4P5g00cYP3CUp=OP7P;P<P<P=P8P5P3L08p=Ag00d@R;#>R>#1R?#<R@g01NQRA'Kg01OCRB'7%1;RC#<RD%>?#1R?#<RE'^RF,4Bp,3sp0RBp,4dataRG'p%kGRH#2%1CRI#1RJ#1RK#ZRL#1#8#8#<RM,4H'0RNP6%VJ$0;RJ/TGRO1K@HRP$03RQ'~RR%LORS/6@/6HRT#214TF'0RU%L3RV/9T/0N'0X:6%LRRW/9TRX/0NRY,0U%DPRZ,6S#DR[/9TR\/0NR],0UPUPYPUP]p-0R]/?U9\UUPXPNP\PNP4P4%l4R\P3X14RXP\1953#jXK4X14PWP[PXPX1?4VX16PRP[1653#DXJ4X:4POPS1?4SPQPZPX%D3X14PPPP1?4PDiFhEgPTPT1?4TM<e1?]N9\NNEaEa%cO%2S1Y2P%BPRO19ZP'017P2%JZ'0'MPZP416S3RZ,Y2%BZ%DZRP/9Z'017Z2%JP'0'M16S5#DP4%=C#1#<RP,XD%BDRZ%2P1^DPRN#B[[%2DRTg01KhRXAWDP5UW0%2N\X^0T1XDE%2E%BF[\ZAWDE5VXX0T%2F\X^0T%VL/bBRB%<KRK+0=%2B%2K20<BK#2[[g00eeRK#;#;RL#;RT#;#;RX#;RE#;RZ#;#ERN&0:;-094RP%EZRZ5`4%EERE1_4KRK'5R['5RR'5#F%EL/5K,5Z#F15N[#F%EX%ET/5K'5#FA`4PE/5K,5Z#F%FR&021'@'@'@'@'@'@%}1P41P48P5P4P41P4:P:%u4CSP71P40CSCS%r4%q4R1f7RR,R11G4>RZ1G4;R;%>I,G4RI5Q4RK'N,315:11H42RE,CK,311NZE,315:15[1%o<R<P1f8RK,R11H4@RP1G4CRC5n4RT,NI,315:11CTE,31f9RI,R15:15[1P<P11CEC,311H4M,OC,315:1RXP<P11H4D%V?5m4R?,O;,31P<P11CT;,31P<P1%>>R>#>#=#=#=#=#=#=#1#Z#8#8#8#8#8#8#8#<RT,H41G4>'C,31P<AQ4;P=Q4CRC,CE,311OC?,315:11NZC,31=:1X5:1CACACACACACA1s1=P3P8g00deR1g00eER='?1t38=I1=dAv425CwbAbGbHX54X64X74X84X94X2]X3]X4]1630R5,98,0:1752%J8'0'M1K@8R8,9:,0R1782/0K'M%27147M'0147F1K@:/7017TK169@/6RR@#214@F'019K@%2R14RM'0'0'0[[[[[[^54^64^74^84^94^2]^3]^4]P3%JKPO16SK#BPKPBP9PHPSPRPIf;f<f=p,4SPloO>b@bBbCbDbEbFbMb>bLb=bICxAyJQG,TJAzJQGE{g01P3RQ,7214QF'0g01Ph,TJ#L=I4Q172A14AM'0'0'0eb?W<W;o"). Qed.

  Lemma calls_rng : (1 <= calls <= 4)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "p'0h07__arithh14__ffh26__sat3h36__sat4h46__sat5h58__varmaph65__with72Hah84__x1h91Hh:2H0h;6__sat6h<1bi001bp;2p;1p;3p;4p;8p;7g01Q^j2ZTg01RRj1YTg006Qj11Tg00kaj16Tg00;2j25Tg00;Nj24Tg01M9j1GTg01SFj2DTg00lij2<Tg00H7j2;Tg00S0j22Tg00DPj1>Tg01Fkj2XTg0194j2TTg01GSj3QTg0076j1OTg00l?j2NTg01F:j2=Tg00AHj1LTg008Yj1KTg00ODj1HTg00Bdj1FTg00CBj1ETg00Obj29Tg00EXj2CTg00=9j2ITg00F:j2JTg00=Sj3BTg00Ffj3ATg00GEj4MTg00UNj4:Tg01Scj3@Tg00Ahj2PTg00Cmj2?Tg00PEj1RTg00E5j3STg00Z>j8WTg00V9j7VTg00Y6j7UTg00ZbR0f0R1'2p=0g00[@R2f1R3g00c2P1C:p=7P3g00]DR4g00]cR5P5g00^CR6P1g00_JFVp=3f2R7P4P5P5P6P3P1FUp=8p,3sp0R8p,4dataR9'Z%Y9R:#0R;g00d@R<#1R=#1R>#1#1R?#1#1R@#1#1#6,5:'4%G9/D0g00deR9P9%6<RAP9P2P1PA%6>R>,<:RB,;An0100000020000RC'212C>'4P1%6=RC%>=#>#1#6R='XRD150C%0=1TC=RE,50[[RF%0CRGg01KhRHAQC=3UW7R=%0E\H^7GRG%O@/N8R8%6?R?'=R@%08%0?1<8?#0[[R?g00aZR8#LRH%K8R8%H2RE%F2RC%E2RI192ARJ/7J,3I192>RK,7J,3I381CI6RLP1P7g00eERM,I91J17=B9MdAA203CMRMb1b5b612AA12A>'4P1b0b2b3b4PDPFP=PGP@P?PHP8PEPCP21920REg00cYR9PKC:,3IPLPMb1b5b6150>P1b0b2b3b49@:>%0BR015B>'4PDPFP=PGP@P?1=:>%0>P0[\;PHP81P23PCPIP4P5P5P61?2<R<,7E,3IP2P<P9PKC:,3I58I%R5AS2J<R<,7J,3I17<K,3I58IGWPLPMb1b5b6X82%01151>'41;A3R3,2A123>'4[^82P1PBf5O2b0b2b3b4b;b:n0110000020101b<b9g01TJRB,2A12B>'4eo"). Qed.

  Lemma calls_x_val : forall vals, vals_ev vals 11 = Z_to_bv 64 (hdr_b2 data) -> cfg <> 0%Z ->
    edenot (ENV vals) calls_x = Z_to_bv 64 calls.
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "h01Hh14__x1h22Hah37__arithh44__ffh57__sat12h67__sat13h77__sat14h88__varmaph95__with:1bh;1zh<4__p1h=7__sat15h>1xh?1yh@2CXhA3H11hB2HbhC2HchD2_HhE3_H0hF3_H1hG3_H2hH3_H3hI3_H4hJ3_H5hK3_H6hL3_H7hM7__sat16hN1ahO1ehP4valsp&0p;1p;2p;3p;4p;5p;8p;6p;7g006Qj10Tg0076k10ATg007Tj1}Tg008Yj1OTg00LTj1MTg01U>j2tTg01RRk10:Tg00HTj25k10DTg00=Sj31Tg019lj1`Tg016\j2KTg01VBj3ATg01V_j1_Tg01Wfj3^Tg00DPj16Tg00AHj1JTg00X2j3]Tg01XCj1VTg01YKj3UTg01ZRj1TTg01[[j1\Tg01\dj4FTg01^1j5RTg01_>j2QTg01`Dj2PTg01aPj4LTg01b0j2iTg01c0k40HTg00kaj1<Tg01d9j3hTg00IZj4vTg00;NR0j22Tg01eBj2fTg01fKj4sTg01Q^k20GTg00;2j2CTg00:Rj1rTg01:Ej2qTg0194j2NTg01gUj2eTg00lij2ETg00H7j2[Tg01SFj2WTg01h2k20FTg01hSk40ETg00=9j2pTg01Fkj2oTg01GSj3nTg00l?j2mTg01F:j2lTg00Ahk20@Tg00Bdk10?Tg00CBk10>Tg00Cmk20=Tg00Obj2ZTg00E5j3kTg00UNj4YTg00EXk209Tg00F:k208Tg00Ffk307Tg00GEk405Tg00QRk804Tg00<@k603Tg01hok201Tg003Bj6;Tg00XRk600Tg00PEk106Tg01j;j2~Tg01kHk30;Tg01kkj1|Tg01lLj1{Tg01Mnk30<Tg01lmj2zTg01n=j4uTg01nYj3cTg00S0j2yTg00V9k70BTg00Y6k70CTg00Z>j8xTf0R1#0#0p=?%M1#Mp=>g00[@R2f2R3f1R4P1CLp=@%61#0p=9%01#0#0#0p=H%01#<p=7%01#6#0#0p=G%61#6p=3P2P2P4P1CLp=g%01#6p=8g01oAR5?]41p=IP4g00deR6P1g00eER7CLp=Xf5f4R8f3R9P3P4CL;11p=Bg020NR:P:P1g021YCup=jP:P:P1g022QCup=wg023JR;,f4=131p=:g024ER<?c41p=Dg0251R=?c34=191p==g00ZbR>/y1p=4g025]R?9161p=dP4g00]DR@g00]cRAPAg00^CRBP1g00_JK0Bp=SAc=41p>02P3P@PAPAPBP4P1K0Cp=aP9P@PAPAPBP3P4P1Gxp=bg00d@RC#0RD#0RE#0RF#0RG#?RH$0ARI#}RJ#Og00eeRK#MRL#M#>#>RM#>RN#MRO#>RP,t1p,4dataRQ$0:RR,5IRS51Jg01NQRT=12>#`g026=%O5RU,K2RV/K6RWPVP6g0278RX1KXURYg028FRZg029R3AR[7AUR\#_A^XU[5@U1K22R[%6CR]#6#?#9#?#H#H#7%0C#G#9#3#9#3#9#?#7'g%0C#G#3#?#8#9#G#7%6C#G#3#8#8#8#H#7'g%6C#G#3#3#8#3#G#7%6C#8#8#9#?#H#H#7'g%J[5][5][3]R[%V\5UK%8C#3#3#?#9#9#8#9#7R\P?g02:KR^%TORO%\>R_CFP?P^%TNRNP_CF%J5R5'IR`'I5@U,XVEBRaPWPVP6g02;=Rb9AYZRc9AXURd#_A^XUc5@U%Vd9UK[P7g02<6RdPOP_CFP7P^PNP_CF/I5R5'I9@U\,XVEBR\PWPVP6g02<hRN9AYZRc9AXURe#_A^XUc5@U%Ve9UK[%0C#3#3#?#3#8#H#7ReP7P^POP_CF/I`5@U,XVEBR`PWPVP6g02=aRW9AYZRZ9AXURY#_A^XUZ5@U%VY9UK[P?PdPOP_CF/I59@Ue,XVEBRVg00[^Re#ORU%O:R5'KROPUP5g02>ZRdg02?UR[g02@Pg02AJRYPKDRg02BC1Qd[#j'PPUP5%Je%J:CLR:EBRePOPUP5g02C<RdP[g02D7PYPKDRg02E1RY,ib1Qd[#j'PP:EBRdPOPUP5g02EhRbP[g02FcRZg02G]RXPKDR1iNY1Qb[#w'PP:EBRbPOPUP5g02HVR5P[g02IQRUPXPKDR1iWY1Q5[#w'PP:EBR:g02JKR5P?PKPL%TPH0H%<]R]#\5h<%<CR<#\5h=R[71;RYP5%>P#>#>#>RWPZP_Cv%TM%<DRM#\5h=R=515P5PWPUP_Cv=15='2R='2R_'2RU'2RW'2RZ'2RX'2RO'2RN'2R^'2P0PaP^p,3ENVRcP8O1g01TJ,5IRf5:JP1P0P\PNPcf8O1=:JfP1P0P`POPcf<O1=:JfP1P0PVPXPcf@O1=:JfP1P0PePZPcfDO1=:JfP1P0PdPWPcfHO1=:JfP1P0PbPUPcfLO1=:JfP1P0P:P_PcfPO1=:JfP1P0PYP=PcfTO1=:JfP1P5P[PcfXO1/f1=1JfXO5PJPSPJP?PKPLP1Cs15I]R]'D15I<R5PfC=X:Jp,3sp0Rg00GQ%4RRQ%0H#7Rh,CRRi'2P2PRPJ%<FRF%rK'q,NM,e1%rL,qF,NMRF'E,5I/D]P5PfC=X;2P2P<PJ1eR1/EF,5I/D]P5PfC=X;2P2PRPJ1E1F,5I/D]P5PfC=X;2P2PRPJ15I1/D]P5PfC=X;2PJ%<ERE,ERRF,5IRjPJP1P5PfC=X:JPJ1[F<Rk,5IRlA1J1fX:JP61WT>RmP?P01W41#dA1234#`R0[A1241#`1W34#d[Rn1W93#d\020F41P1n2001000000120000000X?2X>2Pn^?2^>2P1PTP>fWRTO3b0H0EA16?mP6P?P6P2P1P<1[<FRnn0100000020000,5I91JlX:6P2PJ&0DIR0P0PkPnPJ\2/p0%3D#7RD,oMR01C>MRn%4D1NMDRk,C>[[Ro%4MRpg01KhRqAnMD4UW2RD%4k\q^2pRk1mIgRg%<GRG'lRr%4g%4G1EgG#4[[RG1lRE%4E%4F[\Qg00aZRQ#JRE%OQRQ20@24Rg&0?2Rs&0>2RtP220=2CRC1Z2<Ru5k2g00^cAk2uCCY'S209tBRuP1P31p6720813=167dB072>4H05R7b4b8b9X121[1<1[<1512^12P1PFO1b3b5b6b7b=L04PmP1J03b0A1Jlfe202j5201F<E;1DS]RFP0PoPDPkPrPGp-0RjPEPQPgPsPtP21Z2>g00c2PCCY,StRlPtP@PAPAPBP9J005at&06ARAPlCbPuP7b4b8b9X12W<%41R9/24%44RB[^12^<jP1PiPRP8O3b3b5b6b7,~RE;PJPFP5PfC=e1ERhP0PoPDPkPrPGPEPQPgPsPtP2PCg00cYRF1Z2hCY,St9atlRiPAPiCbPuP7b4b8b9X121C1h,29R91C4h,2B[^12P1PRP8O2b3b5b6b7:0;RhE;1eR<%|RE;1NM>%{ME;1mIS%<HRH,oM%4H1NMHR<,C>[\nAnMH4VqX2p%4<\q^2pP0PoPDPkPrPGPEPQPgPsPtPiPAP2PCPF1Z2M>0<2ICY,St9atlCbPuP7b4b8b9X121C4<,2B\9^12P1PRf6O2b3b5b6b7b=bM,zRE;PJP?PKPLPSCs/D]P5PfC=ebB1tTPfVE;PcPTO1/f[=1JfeP;P4E;XL=X@YP4P1O2n2001000000121000000X0_XK:P4P1O2n2001000000121000000X0UXJbP4P1O2n2001000000121000000X0WXIdP4P1O2n2011000000121000000X0ZXHeP4P1O2n2011000000121000000X0XXGVP4P1O2n2111000000121000000X0OXF`P4P1O2n2111000000121000000X0NXE\P4P1O2n2111000000121000000X0^XDaP4P1O2n2111000000121000000bNWCWAWPo"). Qed.

  Lemma ownedA_rangeT : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x69b38 <= bv_unsigned a < 0x69ee8)%Z
                 \/ ((0x6b000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "p;7g02KTj70Tp,2ALp,2CLp,3ASRp,3sp0p,4Hvspp,7AL_globp,8AL_grantF0o"). Qed.

  Lemma know_after_allocT : forall (A A' : AS) vals (M M' : word -> option byte) vm vm' R' kn,
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> kn_vars_lt (length vals) kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 208 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    (forall a, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ owned A a \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_acallT kn).
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "h04__x1h14HLv0h27__arithh36__sat3h46__sat4h56__sat5h64cstrh74__ffh88__varmaph95__with:4__p1h;4__x2h<4__p2h=1rh>2Hah?1bh@1HhA2H0hB4__p3hC1ohD3HnthE2HxhF1ahG2HehH2HohI4__p4hJ6__sat6hK6__sat7hL4__x3hM1xhN1AhO2A'hP2H1hQ2H2hR2HIhS3HIAhT2HKhU3HLvhV2HMhW3HfrhX2HghY3HgrhZ2Hhh[3Hhih\2Hlh]3Hloh^3Hlth_2Hsh`4Htopha5HtopAhb1Mhc2M'hd2P0he2R'hf6__sat8hg6__sat9hh2knhi1mhj1nhk4valshl2vmhm3vm'p%0p%1p&0p;3p;2p;1p;4p;5p;6p;7p;8p;Ap;<g00gRk30kTg00h[k30jTg00idk20TTg006Qj13Tg0076j1eTg007Tk10@Tg008Yj1}Tg0087k10PTg00DPj18Tg004Nk20JTg00LTj1iTg0022j27Tg02LVR0k20FTg00=Sj3=Tg02M0k20[Tg02N7k40DTg011mk50CTg014kk10ATg00l?j25Tg00kaj1ATg00<\j2?Tg00mIj4ETg019lj1<Tg02OGk20;Tg00PEk109Tg02PKk10ITg00;2R1j21Tg00S0R2j20Tg02QMj1oTg02RUj3pTg00M3k10iTg0194k206Tg00:RR3j1:Tg00@Aj1MTg01Fkk202Tg01GSk301Tg01F:k20ZTg00lik20YTg00AHk10BTg00Ahk200Tg00Bdk10XTg00CBk10WTg00Cmj2qTg01Mnk30?Tg00EXk20VTg00=9j2[Tg00F:k20STg00Ffk30RTg00GEk40QTg003Bk60>Tg02S2R4j2{Tg00Obk20=Tg00Pgj4yTg02SJj4xTg02TWk20<Tg00ODk10OTg02U\k20NTg02V?k10:Tg00;Nj24Tg02V\k60LTg016\k20KTg02Waj3@Tg02X8j2TTg00H7j2BTg00<@j6jTg02XRj7vTg00X2j3gTg02YNj3UTg019Qj4]Tg02Yhj4tTg00U4S00j2STg02ZBj3ZTg00E5k308Tg02Z\k60HTg00N[j2nTg00V]j3|Tg00WFk207Tg02[@k205Tg02[_k50GTg02\_k30UTg02]Yk10hTg02^`k80gTg02_lmA0fTg02a6k10aTg01U>k20`Tg00Kom<0ETg00?Zk40_Tg00UNj4fTg00V9j7rTg00Y6k704Tg00Z>k803Tg00RMk30^Tg01VBk30]Tg01Wfk30bTg01aPk40cTg00XRk60\Tg00BFk40dTg00YZk70eTf0R5#3#3p=9g00eeR6-0`5p=R%35#3#3#3p=W%35#8p=>f3R7f2R8'0f1R9/15'4p=2A=895#<p=F1S95,S8p=d%85#8#8#8p=X%35#3#3#3#3#3#3#3p=V%35#Ap=I%85#3p=^%85#8p=h1089/45p=Cg00[@R:/[5p=Gg00[^S01P:P0P3P2g02b3f5R2f4R0P7P8P9P5N<0Ep=N20F07P8P9P5H0_p=Lg00ZbR;/05p=611;5p=O20=:5p=;P8g00]DR<g00]cR=P=g00^CR>P:P9g00c2R?P5Cfg00_JR@Frp=QP0P<P=P=P>P7P<P=P=P>P:P8P?P9CfP@FrP5K04p=Jf6RAP<P=P=P>P2P0P7P<P=P=P>P8P9P5L03L03p=\Q01P:P4P3P1g02bUP6P;P7P8P9P5N<0Ep=zP8P<P=P=P>P:P9g00cYR1P5CfP@Frp=DP7P<P=P=P>P8P9P5L03p=HB0^:95p=`1195,48p=wg02c7R3,?5p=_P:P9P?P5Cfp>0MP7P<P=P=P>P8P9P<P=P=P>P5P@FrK04p=lB0]::5p=kB0b::5p=m10781195'4,40p=P1489/S5p=K1495,S8p=aP:P:P9P5H0cp=uP9P<P=P=P>P5J0\p=cP8P<P=P=P>P9P5K04p=bP:P8P9P5H0dp=YP8P<P=P=P>P9P5K0ep=sP:P9P1P5Cfp=~p,2ALR1p,2CLR@p,3ASR:0k1@60j1R@+0TS02Q02g00d@R?#3R4#3S03#3S04#3RB#9RC#eRD$0@RE#}Q04#e$0@RF$0PRG\ES05Q05g01?bS06Q06%84RH#e00JEg020N#}%i6RI17EA+0Ff7RJ#Rp,3sp0S075=Eg00deRKf8RL,7E00[8g00eERM3=g01@YS08p,3ENVRNf9ROO1PLP7H0DP1P@f<S09POPJI0C&0ALQ07,5DRP%WCRC#9RQ#WRR#3#9#WRS#ART'?RU5=:P1P@f=RVf:S0:PLI0C&0AO==:UP1P@fAS0;P5CE#<P1P@Q0;P9CE#<20;18#<%8?RW#>#WRX#AS0<,?PRYg02d8'?15D7RZPZPYC2S0=#<S0>Q0;P0O1fBRYP0O15=G[[[[^FEf?S0?P5O1&09FRF5FG15D9R[&0I1R\'1P1P@fCR]P9CEQ0?P9O1=FGF3d[^FEp,4SPloS0@%8WRW#8#X#X#X#9#W#V#V#V#IR^/0Pp,4SPhiS0A%3S#9#W#V#V#IRS,0PQ08PN%oVS0B9pEYR_O1S0CQ0;f@S0Dg02e:R`&0iXRX%ACS0E'?RCPXg02f1Ra%9W#^#9#V#IS0FPE%RYS0G%A4RW%3H#9Rb#ARc+06Rd15D5Re%8HRH#hRf#ARg-06WRh,0e3CX?ERiPEQ07PiPI17EYRi%A?Rj%:iRk'0RlPIPj%GjRmPiPk%GkRnENf;S0HDLRoPl17E]Rp#MRq%:p#6Rp202Wg%OWRr%6g%Oh[[%6WRsg01KhRtB01Wg9UW>%6h\t^>s202WcRg%6c%Od[\rRuB01Wc9VtX>sRc%6d\t^>sRv%IHRH-02WRw%6H206WHRx#O[\rRrB01WH9VtX>sRH%6x\t^>sRs%ABRB-0ZPRt%6P%6B20YPB#6[[RBg00aZS0I$0BRxQ0I#}Ry200:9Rz&0X:R{&0W:R|1q:?R}%;S5Q|&09=R~P|%;^S0J=Q|}P~P|P|%;WRW%eb60?:RbP}%ef:0?:W9Q|}DJF\20V|>RWP5P81[KM20S58==KMdB0R:;9H0QRMb7b8b9X0:105S10^9108h9Cd8[[^0:P5PPQ0AQ0@O3b2b3b4b5bJbKbfbgb6b1Q0GQ0:J0>%R_PYQ0BP61{6i%Ok1[:;S0GPiPkPnCzPoPlPqPpPwPrPHPsPtPBPxPyPzP{P|%;j=Q|}P~20=:;Rn=D|}CHPWPMb7b8b9X0:S0A10j5%O9[^0:S0KP5fHS0L,7ES0M#:RkP2O2b2b3b4b5b6b1CyCxJ0>Q0C00<6,5DRi10ih5CdePoPlPqPpPgPuPcPvPwPrPHPsPtPBPxPy&0O:RvP{P|P|Pn%8?#>#>#^#9#V#IRc#;Ru%;TS0N,`b9D|uDJPWPMb7b8b9%6c1?dT7wcP5b2b3b4b5bJbKb6b1P;PaPa%_dC2ePoPlPqPpPwPrPHPsPtPBPxPyPvP{P|P|P|Q0N-0N:%;XS0OQ0E#;S0P'`S0QQ0QQ0O5Q|DJP|Q0O00MnClPWPMb7b8b9&0:T10CXRn7CC10X;R;'4P5b2b3b4b5b6b1&0:3?CCn/4;ePNf>S0R#o9pE]O1S0SP`PCPXPaPeJ0L#<PEfDRNQ0?#oR;5pE#R15D8Rn/1a20K::R3A@35`R`%k5RpPZPZ%m5RqDPX=3'T'4Rl10anRo%_eS0T7wn1BeCRdPnPn1BeXRbC23d#<X?EP5%RNRgPNP;P617ENR;,{6%:;Ri#OQ0GP;Pi%GiRhCzPIP;10jiR_PIPjPmP;PiPhENPVDLP_fER_,7ERh#M%:hRi#6PwPrPHPsPtPBQ0AQ0KP5fJS0U,7ES0V#:R;P2O2b2b3b4b5b6b1CyCxEj11[aP`PpPnPnPqDPX=3,T310a[15DgRg#_,1[1BgCP[P[1BgXC23K3K#<PE%R_S0W11ZaP`Pp15D0R`P`PqDPX=3,T310aZQ0T,1ZPdPZPZPbC23K3K#<X?EP5Q07PVEj%_PS0X9won1BPCS0YPnPn1BPXS0ZC25dl#<PJP7P1P@Q0LP7CES0[fIS0\fFS0]PNP0Q09Q0HP5Fv%8?#>#9#h#>#^#>#h#9#IRl/0`%8?#>#9#X#>#h#>#9#IRo,1`PcP`P`PUC2S0^%AQRQ/0`%ARRR,1`3a3KS0_Q00Pl15D2RbPbPoC2PcPbPbPUC2S0`10Qb11bR3ag02flS0aP5Pl15DARdPdPoC2P015DJRg/1cS0b1uloRS%3?#>#9#^#X#9#h#^#IRK%3?#>#9#^#X#>#W#IS0c'uR?1uQRRf&0B3S0d5g3S0e5g3S0f5g3S0g9@35S0hPp15DLS0iQ0iPqDPX=3S0j,T3S0k'4PcPgPgPUC2S0lQ0Y/0gQ0Z,1g3aQ0bQ0kPIQ0V10j;S0kPIPjPmQ0VP;%G;ENP]DLS0VQ0kfKS0b,7ES0m#MS0nQ0m#:S0o#6S0pPwPrPHPsPtPBp-0R;PxPyPzP{P|1c|7S0q%;oS0r9D|}S0s5b|P~AD|}uS0tCHPWPMb7b8b9X0:W:115oS0u,49119cS0v[^0:^:;P515DVRV,0lPVPAO3b2b3b4b5b6b1P3Q0jPSQ0g9@3S%kSPgPg%mSC2S0jA=3SSQ0f9@3S1[3S3UQ0VQ0kQ0nQ0pPwPrPHPsPtPBPxPyPzP{P|P|P|%;lP}Q0sDJS0sP~Q0sCHPWPMb7b8b9X0:Q0u9Cl5119oS0u9Cl9[^0:P5PVPAO2b2b3b4b5b6b1Q0jeC]CtC]3UO1WXP5O110cd11dUPQPdPdPRC23KQ00Q0lPQPgPgPRC2Q0aP5PcQ0iQ0iPUC2PA15DORg/1cS0lQ0hPpQ0:,5DRVPVPqDPX=3S0j,T3S0s'4S0pPcPgPgPUC2S0nQ0YPgPgQ0ZC2S0k'SS0VQ0nQ0kPIfLS0w,7ES0xQ0x#:S0y,0jS0zPIPjPmQ0xQ0yQ0y#GENP_DLS0{Q0zfMS0|,7ES0}#MS0~Q0}#:#6S0}PwPrPHPsPtPBPxPy200:8?Y9vS10P{P|P|P|PuP}1q:4R4Q0N'`9D|}DJS11P~Q11CHPWPMb7b8b9X0:X;:PcP5P51?9TS11C2PcP9P91?8TC2[^0:^;:P5PPQ0?,5DS0?PAO3b2b3b4b5b6b13U3ZO1WZP5O1PQQ0iQ0iPRC2PAQ0pQ0VQ0lQ0sQ0{Q0zQ0~Q0}PwPrPHPsPtPBPxPyPzP{P|Q0q%;RS0s9D|}S0l5b|P~Q0tCHPWPMb7b8b9X0:X:;115RS0i,49Q0v[^0:^:;P5Q0?,0QQ0?PAO3b2b3b4b5b6b1P3Q0jPfQ0g9@3f%kfPgPg%mfC2S0jA=3SfQ0f9@3fA=3?fQ0e9@3fA=3ffQ0d9@3f1[3f3U3Z3ZQ0{Q0zQ0~Q0}PwPrPHPsPtPBPxPyPzP{P|P|P|%;QP}Q0lDJRfP~PfCHPWPMb7b8b9X0:Q0i9CQ5119RS0i9CQ9[^0:P5Q0?PAO2b2b3b4b5b6b1Q0jeC]CtC]3UO1W\P5O1n200100000021100011000W@P5O1n200100000021100011000S0VbCWHQ0[#<eP1P@fGS0[P7CERfQ0LP_P]P0Q0:POP5FvQ0_Q0VbCWH%<fe20;17S0Vp,8AL_errnoP0P5O2PKP`P`Q0cC2P811bcS0_Q0hPpPdPdPqDPX=3S0p,T3Rf'4Q0`Q0Y/0bQ0Z,1b3aQ0_PfPIQ0M10jkS0_PIPjPmQ0MPk%GkENQ0;DLS0`Q0_Q0\,7ERf#MS0j%:f#6S0?PwPrPHPsPtPBPxPyPzP{P|Q0qQ0c#;9D|}S0l5b|P~Q0tCHPWPMb7b8b9X0:X:;Q0c,15S0t,49Q0v[^0:^:;P5Q0H,5DRf,0KPfPAO3b2b3b4b5b6b1P3Q0pP?Q0g9@3?%k?PbPb%m?C2S0gA=3S?Q0f9@3?A=3??Q0e9@3?1[3?3U3ZQ0`Q0_Q0jQ0?PwPrPHPsPtPBPxPyPzP{P|P|P|%;KP}Q0lDJRzP~PzCHPWPMb7b8b9X0:Q0t9CK5PKP9P9Q0cC2[^0:P5PfPAO2b2b3b4b5b6b1Q0geC]CtC]3UO1bGWGQ0V#<eQ0=P911`cQ0hPpPbPbPqDPX=3,T3'4Q0^Q0YP`P`Q0ZC2RK'SQ0^PIQ0[,7ERz%:zR?,0jRSPIPjPmPzP?%G?ENQ0DDLPSQ0M#M%6kPwPrPHPsPtPBPxPyQ10P{P|P|P|Q0<#;,`}RkQ0P'`P4AD|4kDJP~P|P|P<P=P=P>1c|0R>1c|2R=P|P|Q0Q:08:}P4Q0O:08:}9D|4DJR}5s|5s|J0HP~P}F\PWPMb7b8b9X0:X;:X:;X<;Q0<,?5R}Q0E'?P9P9P}C21B9CP8P81B9XC29d70Q0a[1B8CP7P71B8XC2[[^0:^;:^:;^<;P5PcPVPVPUC2RX11VcQ0hPpPfPfPqDPX=3,T3'4PVPPPAPJO6b2b3b4b5b6b17ZK3ZO1W_Q0>eO5bDbDWDXMEQ0S00<6,5DRK#_PePePKC2P]P9O1=FGFPEQ0D#oR]9pE_#RQ0TPZPZPeC2X?EP9Q0WP_P]P61{6h%OiQ0GPhPi%GiR]CzPIPh10jiRKPIPjPmPhPiP]ENQ0RDLPKQ0],7ERK#M%:K#6PwPrPHPsPtPBQ0AQ0KP5Q0oP2O2b2b3b4b5b6b1CyCxEjQ0W,5DRK#_PnPnPKC2PEQ0]#RQ0TP`P`PeC2X?EP5Q07Q0REjQ0XPZPZPPC2PJP0P8O211`\P1P@Q0\P0CEP_P0O1=FGF3dQ0011b\P1P@Q0UP2CEQ0]P2O1=FGF'SQ0[PAO1=FGFRbP511d\p,5AL_hi10\cQ0\PLO1=FGFRdPIQ0mQ0o,0jR_PIPjPmQ0mQ0oQ0o#GENPNDLP_Q0x#MQ0y#6PwPrPHPsPtPBQ0I%iIR_#iR`#i,n:1n:`1n:_1n:65|:5|:R65|:g00bFR_+07;gxPy200:7?Y8v?Y9v?Y7vP{P|AQ|4uP~P|Q04,q:Ru=D|4P~P|Q03,q:R4Q0N'`R`=Q|uRZ=b|=P~P|Q0J=Q|4R4P~P|P4P~1c|AReCHF\RKF\PWPMb7b8b9X0:X;:XL:X:;X<;105c11791?7T?C0210^010^2PO[[[[[^0:^;:^L:^:;^<;P5Q0aQ0R,5DR]/1PP]PPP\PAPJQ0:Q0DQ0@O:b2b3b4b5b6b1+05bAW@P5O1P1P@Q0bPACE/SbQ00P1P@Q0wPJCEQ0LPJO1=FGFPdP5P1P@Q0|PLCEfNQ0bQ0\POQ0;Q0DP5Fv10lg11goQ0n10Qg11gR3a3KQ00PlPVPVPoC210QV11VR5aXQ0wQ0HO1=FGFP5PlPfPfPoC2Q0|Q09O1=FGFRFPIfO,7ERG%:GRo,0jRXPIPjPmPGPo%GoENQ0LDLRoPXfP,7ERG#MRm%:G#6RGPwPrPHPsPtPBQ0I2076_;gxRxPyQ10?Y8v?Y8vRvP{P|P|P>P|Q0r,~uClP~PKCHPWPMb7b8b9X0:X;:X:;X<;XB;Q0u,48Q11/08RK/4010^8R_10^7R^PL[[[[^0:^;:^:;^<;^B;P5Q0a15DYRD/1PR610lDPDPPPAQ0RPNQ0@O9b2b3b4b5b6b1+05WAP5O110cf11fUPQPfPfPRC23KPoPXPmPGPwPrPHPsPtPBPxPyPvP{P|P|P>P|1~u`ClP|P=P|Q0s,~uCl5s|P~P|Ab|ZeP~P|P4P~P|P4P~1c|JF\F\PWPMb7b8b9X0:X;:X:;X<;XB;XI;1?5T,19Q0i,475K814K2PO\^\_[[^0:^;:^:;^<;^B;^I;P5Q0aP610QD10cDPDPPPAQ0RPNQ0@O:b2b3b4b5b6b1-05FWAP5O1n200100000021100011000bCW@P5O1P5X@dP5O1n200100000021100010000WAP5O1n200100000021100011000bCbEbEWVWEXMEQ05Q01Q0F/0[%:9,Bn/0aP0P7P8P9P5I0GWQWPWjXFEWiQ09Q08PYQ0Bp,3AMBp,3a0sp,4path40U$0hQ0;Q09POPLL0gNA0fQ08Q0CQ0DQ09$0aH0Deb[b]WYWWW`WRWaWSWTW^WdWUWhWeWmWlWcWbWkWOWNo"). Qed.


  Lemma env_ok_allocT : forall A A' M M' vm vm',
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 208 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "h04__x1h14__p1h21ah37__arithh44__ffh56__sat3h66__sat4h76__sat5h88__varmaph95__with:4__x2h;4__p2h<2Hah=1oh>1Hh?2H0h@2HehA2HohB4__p3hC1AhD2A'hE2FRhF2H1hG2H2hH3HEahI3HElhJ3HErhK2HIhL3HIAhM3HfrhN3HnehO4HtophP5HtopAhQ1MhR2M'hS2vmhT3vm'p%0p&0p;3p;2p;1p;5p;4p;7p;6p;8g00gRk30>Tg00h[k30=Tg00idk200Tg006Qj10Tg0076j1nTg007Tj1jTg0087j1~Tg0111j3^Tg02gIj3cTg00l?j2?Tg00;2j24Tg00DPj13Tg019lj1:Tg00=Sj32Tg00kaj1GTg00S0j21Tg00PEj1qTg00;NR0j29Tg011mj5JTg014kj1ITg00<\j2HTg00mIj4ATg02OGj2rTg02XRj7gTg01Fkk20<Tg0194k20;Tg01GSk30:Tg01F:k209Tg00lik208Tg00LTj1ZTg00N[j2STg00WFj2eTg00AHk106Tg00X2j3dTg008Yk105Tg00Ahj2mTg00ODk104Tg00Bdk103Tg00CBk102Tg00Cmj2VTg00EXj2}Tg00=9j2|Tg00F:j2{Tg00Ffj3zTg00GEj4yTg00RMj3_Tg00U4R1j2QTg003Bj6aTg019Qj4kTg00V]k301Tg00BFj4vTg00Obj2uTg00UNj4YTg00V9j7\Tg00Y6j7[Tg00XRk607Tg00YZj7pTg00Z>j8fTg02Z\j6sTf0R2#0#0p=]%02#3#0#0p=@%32#0p=;%32#3p=>%02#0#0#Gp=8%02#3p=6f2R3f1R4'1/92p=lf3R5/13/94/Q2p=B%32#3#3#3p=M%02#Gp=i11531442'9p=7%02#0#0#0p=E%02#0#0#0#0#0#0#0p=W1434,95/Q2p=tg00[@R6?242p=K1942,Q3p=Pg00ZbR7/12p=OB01642p=LP6P3P4P2Cvp=C1u62p=5P6P4g00c2R8P2CYp=TP3g00]DR9g00]cR:P:g00^CR;P6P4g00cYR<P2CYg00_JR=F\p==P5P9P:P:P;P3P9P:P:P;P4P=F\P2F[p=UP3P9P:P:P;P6P4P8P2CYP=F\p=<P4P9P:P:P;P2J07p=bf4R8P9P:P:P;P5P3P9P:P:P;P4P2F[Fpp=Df6R>P9P:P:P;f5R?P8P5P9P:P:P;P3P4P2GfGfp=N1442,93p=XP4P9P:P:P;P2Esp=RP5P9P:P:P;P3P4P2Gfp=FP3P9P:P:P;P4P2Fpp=xP3P9P:P:P;P4P2F[p=`P6P4P<P2CYp=hP5P9P:P:P;P3P4P9P:P:P;P2P=F\F[p=o1934/Q2p=wp,2ALR=p,2CLR9p,3ASR:0>=960==R9+00S00Q00g00d@R<#0R@#0RA#0RB#0RC#]RD#nRE#jRF%nB#jRG#~RH[S01Q01g01?bS02Q02p,3sp0RIp,4mem0RJ;^5P0AcIJ8%0<#@#;#>#;#>#;#8RK1?E2RL%0<#@#>#]#6#;#6#8RM,4L%3<#@#>#6#6#@#8RN%3<#@#>#6#;#6#>#8RO,4LRP7lLCBRQ%0<#@#;#M#]#>#;#iRR1?E4RSPS%0<#@#;#M#@#8RSC7#:RTf7RUP3O1PJP3O1RV52H[[^2F%EDS03#]RD#ERW#GRX/1LRYPL%3<RZ#3R[#E#W#8R\%><#E#;#6#@#8R]PLPL%><#E#;#6#6#6#8R^C7CtR_P>P4O1%qGRG52H[^2F'9P=P9PUP?P5DJ%I81?EIR`%EW#8RW'HRa'KP=P9f8RbP>P8DJ%I?/KaP=P9f<RcP2CA#:P=P9PcP4CA#:1r=3S04#:Rd%0Z#;#8RZ,H`S05g02d8'HS061?E5RePeQ05C7#:Rff=RgP8O1f>S07P8O152H[[[[^2Ff9Rh9^IJ[[[[[P2AcIJ>f:RiP3O1=2HV\T\Q^2FPhP4O1=2HG\_^2F'9P0f;R0P3O1=2HV\T\Q^2FPiP4O1=2HG\_^2FP=P9P0PhPUDJ%Ib/KaP=P9PcPiPbDJ%Ih/KaP=P9f@RjP2CA#:P=P9PjP4CA#:fAP8O1fBS08P8O152H\f\d[[^2FA^IJg[[[[[P2PgP3O1=2HV\T\Q^2FPgP4O1=2HG\_^2FP=P9Q07PcPiDJ%I0/KaP=P9f?PgP0DJ%Ic/KaP=P9fCS09P2CA#:P=P9Q09P4CA#:fDRcP8O1fERgP8O152H\f\d[[^2Fp,4SPloRf%3[#M#M#M#E#W#W#W#8R[/1`11`LS0:?PYPS0;P8P3P=P9fGS0<P3CAS0=fHfFS0>PcP5PhPbP2FgPOPe%3<#@#M#6#>#6#8RY,4e%3<#6#6#;#W#8RPPe14ea%GDRDPePePXC7CBCBS0?P1PO1?E8R1P1PYC7PPP1141aPDP1P1PXC7CBg02flR1P2PO1?E?RLPLPYC7%G@Rj%3@S0@#3#iRk+0<Rl147j%Ok20;jkRm,47[[Rn%OjRog01KhRpB0:jk4UW<Rk%Om\p^<oRo%GCRC-09`Rp%O`%OC208`C#O[[RCp-0Rmg00aZRjg00eeRq#ZRr#ZRs#ZRt,S6S0A1S6sRs1S6qS0B'L'Lg00bFRq'e&06jRu3dS0C&05jRv1m63S0D&046Rw7C4S0E?C3w?C3wS0F&036Rx&026RyPyPy%5ORz1V6BRB'T%5Y9=yBCU%q:R:PyPy1V6ARA=<yBS0GPy1by8R{A=yBzS0HDDP:Py%5[R|=<yAR}P:PyP}P:1by?S0IFNS0JFN1}y;R;P2P3g00deR}g00eER~'|1{23=2}~dAz674CyR7b4b8b9X06X:6X1mW;POP4P4PYC71143RY143OR~7P511[3R}11[5S0KPU[[S0L[[^06^:6^1m^;mP2P11?EiRi,1XPiP`P8PhP0PfO8b3b5b6b7W?P2O1PPPL14LaPDPLPLPXC7CBPlPnPkPoPpPCQ0CPvQ0FPxPyPyPyPy%5P/TB%5W9_6A9=yBCUPyP{%5XRA9=yBDDP:PyPyQ0GPyA<yABQ0HDDP:Q0JFNP;P7b4b8b9X06X:6X1mX;mPPP41H2W,44AX34XCB11X3=PY~Q0L[[^06^:6^1m^;mP2P111DiPiP`P8PhP0PfO8b3b5b6b7W?P2O1n200100000021100011000Rib=WAQ0=#:eP=P9Q0>P3CAR9Q0<PgQ09P5PUP>P2FgQ0?Pib=WA%:9eQ04p,8AL_errnoP5P2O2PRPePePSC7PlPnPkPoPpPCPuPv1m64Re?C4wR9?C4w?C4wPxPyPyPy%5RRi/TB%5SR=9=yBCURBP:Py1RyBP:1by5RBFNP;P7b4b8b9X06X1mPRP2P2PSC7RD11R4R~?X4SP1[RWP5[[^06^1mP2P11?EbP8P>O4b3b5b6b7b@W@PdePlPnPkPoPpPC%Zt,S61S6rRr,Ls'L/eq=djuPvQ0EPxPyPy1V6<R<1V6@R@5<yRsPyP{A=y@zRzDDP:PyA<y|<RtP:PyPtP:PyPy%5Z9_6<RtQ03#GRd#55_6/T@A=y@tCU,RyCFFNP;P7b4b8b9X06X:6X1m1124Rt144ORb7P311[41H5ZRZ/HdP8P8PZC7P1[\}[[^06^:6^1mP21?E>R>,1XP>P`P?PUPfO6b3b5b6b7Q061?E3REPEQ05C7#:eO5XNTW<X2FQ0;PcP3O1PgP3O1RE52H\T[^2FQ089cIJRIA2HEV\T\Q^2FRZPcP4O1Rc=2HG\_^2FRd'9Q0:PHPgP4O1RgA2H2VX=HQ07P4P2O2PcP3P4PlPnPkPoPpPCPuPvQ0EPxPyPsP:Axys{CFP;P7b4b8b9X06X:6X1m1QY5\t^06^:6^1mP211XLRt?XLOPLP`P8O4b3b5b6b7PlPnPkPoPpPCQ0AQ0B,Lr'L/eq=djuPvQ0D?C3w9Cw4PxPyQ0@,V6Rw=<y<P:PyA<y|wRwP:PyPwP:A=y<=R=9`y{,RyCFFNP;P7b4b8b9X06X:6X1m1142Q0KAX?5SP1[[\}[^06^:6^1mP211RLP`PLP8PUPfO6b3b5b6b7O3EaW<X2FPIePZPdPHQ0>P3O1PJP5O192H2X=HP0P3P4P2O3PEP5P3PlPnPkPoPpPCPuPvP9PxPyPyPyPy%5K/T@%5M9=y@CUPy%5N=<y@PzDDP:PyPBPyA<yA@RAPzDDRzCFP;P7b4b8b9X06X1mPKP2142MPNP2P2POC7CB11X4=P3bRb[^06^1mP211`>P>P?O3b3b5b6b7PlPnPkPoPpPCPuPvPePxPyA<yi<Ri=`y=,RyR=P:P=CFP;P7b4b8b9X06P1\DPW[^06P2P>P8O2b3b5b6b7O3EaXGTXFQX2FPHPgA2H2GX=HPhP4P2O2PcP3P4PlPnPkPoPpPCPuPvP9PxPyPyPyPAPy%5\RA,h@CoPy%5]=<y@%5^R99=y@DDP:PzCFP;P7b4b8b9X06X1mPXP2142\R\142^R^9l]2CBPb[^06^1mP211`LPLP8O3b3b5b6b7PlPnPkPoPpPCPuPvPePxPyPyPyPBPy1h<ACoPyP{A=y<9DDP:Q0I9`yi,RyCFP;P7b4b8b9X06X1mX;mXBm193^9w4\19~8P1[[^06^1m^;m^BmP214LS11]LPtPLP8O5b3b5b6b7O3EaX<_X2FCkCkbEb>WMWOWKWPWLWJWIP4P2O2n2101000010121000000W>WHP4P2O2n2011000010121000000W>WTWSWRWQWDWCo"). Qed.


  (* [comment removed for export] *)
  Lemma sgn_tab : forallb (fun b => Bool.eqb (bv_lts (Z_to_bv 64 (bv_swrap 8 b)) (Z_to_bv 64 0)) (128 <=? b)%Z) (zseq 256) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "h01bp;2p;1p;3g00=9j2=Tg006Qj12Tg0076j13Tg02hAj25Tg00HTj24Tg02hhj3<Tg00kaj1;Tg02iUj27Tg02j2j26Tg02jIj18Tg02k@j39Tg00=Sj3:Tg00LTj10Tf0R0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00deR1g00eER2'=g00[@R3g00d@#2#2#2R4#2#2#2R5#3R6%34/50,46g00Zb,463<%25#;/70'6X03g00ee#1#1#1#1#1#1#1#1#839=:12do"). Qed.
  Lemma sgn_val : forall b, (0 <= b < 256)%Z -> bv_lts (Z_to_bv 64 (bv_swrap 8 b)) (Z_to_bv 64 0) = (128 <=? b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "h01Th11xh22Hah34__x1h41bh52Hbh67__arithh74__ffh86__sat3h96__sat4h:6__sat5h;8__varmaph<5__with=5lemmah>1yp;1p;2p;3p;<p;6p;4p;7p;8g006Qj12Tg00kaj15Tg00;2R0j23Tg00;Nj27Tg0076j1BTg02hAj2=Tg00HTj29Tg02hhj3:Tg02iUj2;Tg02j2j2?Tg02jIj1FTg02k@j3iTg02Waj3<Tg02k\j2[Tg02l5j3YTg02lfj3XTg00:RR1j1ATg02mIj2WTg00=9j26Tg00=mj3VTg00>Sj1UTg00Kol<OTg00?1j6NTg00DPj1>Tg01Fkj2LTg0194j2KTg01GSj3JTg00l?j2ITg01F:j2HTg00lij2MTg00AHj1GTg008Yj1PTg00Ahj2QTg00Bdj1RTg00CBj1STg00Obj2@Tg00Cmj2hTg00UNj4ETg00Y6j7gTg00PEj1fTg00Z>j8eTg00EXj2aTg00F:j2`Tg00Ffj3\Tg00GEj4ZTg00Pgj4]Tg02n>j4^Tg02nYj3_Tg00=Sj3CTg00S0j2bTg00LTj10Tg00TOl<cTg00V9j7dTg00ZbR2f0R3'bp=1%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=4g00deR4g00eER57C3p=8g00[^R6g00[@R7P7P7P1P1f5f4R1f3R8f2R9f1R:P3M<cp=TP:g00]DR;g00]cR<P<g00^CR=P3g00_JFdp=D%13g00d@R>#2R?#2#2R@#2RA#2#2RB#2RC#2#5RD,33'7REg02o5%BBRB%B@R@/=3,9B19B2RF3:%5CRC/;3'?X47RGg00ee#4#4#4#4#4#4#4#4RH#FRI5i7#8RJA<73IPGP:O1#8[^17RK,[JAYJK3W=AX7GIP3O2PKP3P8A<78I%11%AHRK,31'7[%18RG138KRJ'7RLA<71I[1WH8PL138DRI,7GPGPJPGPIp-0/6G9VGGP7P7P0P3X17RGP013:3#UX>7X17P8P81678PKPDPGPG%A3,67X16PHPD167DETM<OEN%5?RH%>?#>#2#5R?'L132H%1?1KH?R6,32[[%1HRGg01KhRKAJH?:UW2%16\K^2Gp,3sp0,IBRG%5ARA'H%1G%1A1MGA#1[[g00aZRA#G%PA1Q7:%R7%S7RAP;P<P<P=PAP;P<P<P=P71@72g00c21h7>R>CE,DAP7P>g00cY1@7DCE,DAFgR>%f<P>Ge1aA=P3P916451`39#8dA\72:CZb7b;b<X37%1:13:D'7\E^37P3f7f6O2b6b8b9b:C]PLeC^O21=@8,9B=:BF1;C8'?#81=@1,9B=:BFRF1;C1RC;_3AC4FCP3b0b0b0b0W5X47o"). Qed.

  (* [comment removed for export] *)
  Lemma sideW_frame : forall A vm M M' buf cap,
    sideW A vm M buf cap ->
    (forall x : word, M' x <> M x -> O2ReadLoop.in_win sp0 x \/ in_data x \/ (exists p n, live A p = Some n /\ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z)) ->
    mem_grows M M' ->
    sideW A vm M' buf cap.
Proof.
  intros A vm M M' buf cap HS Hchg Hgr.
  (* keeps the section arguments the callers pass *)
  pose proof Htid as Htid0. pose proof model2 as model20.
  pose proof SPlo as Hlo.
  destruct HS as (HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hcap).
  assert (Hblk : forall x p n, live A p = Some n -> (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z ->
            M x <> None /\ (bv_unsigned x < bv_unsigned sp0 - 8388608)%Z /\ (al_globals x \/ al_grantable x)).
  { intros x p n Hp Hx.
    destruct (ai_live_hull A M vm p n HI Hp) as (Hn0 & _ & Hendp & Hbytesp).
    pose proof (O2ReadLoop.round16_ge n) as Hrn.
    assert (Ea : at_ p (bv_unsigned x - bv_unsigned p) = x).
    { unfold at_. apply bv_eq. rewrite u_small by (pose proof (u64_range x); lia). lia. }
    destruct (Hbytesp (bv_unsigned x - bv_unsigned p)%Z ltac:(lia)) as (Ho & Hd & _).
    rewrite Ea in Ho, Hd.
    split; [exact Hd|]. split; [lia|].
    destruct (ai_owned_where A M vm x HI Ho) as [G|[[Gr _] _]]; [left; exact G | right; exact Gr]. }
  assert (Hsame : forall x : word,
            ~ (O2ReadLoop.in_win sp0 x \/ in_data x
               \/ (exists p n, live A p = Some n /\ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z)) -> M' x = M x).
  { intros x HP. destruct (M' x) as [b1|] eqn:E1; destruct (M x) as [b2|] eqn:E2.
    - destruct (bv_eq_dec _ b1 b2) as [->|NE]; [reflexivity|].
      exfalso. apply HP, Hchg. rewrite E1, E2. congruence.
    - exfalso. apply HP, Hchg. rewrite E1, E2. discriminate.
    - exfalso. apply HP, Hchg. rewrite E1, E2. discriminate.
    - reflexivity. }
  unfold sideW. refine (conj _ (conj Hl (conj Hvl (conj Htop (conj Hisp (conj Hres (conj _ Hcap))))))).
  - apply (ai_frame A M M' vm HI).
    + intros a Ho Hn. apply Hsame. intros [W|[D|(p & n & Hp & B)]].
      * destruct (ai_owned_where A M vm a HI Ho) as [G|[[_ Gt] _]].
        -- pose proof (AL_glob a G). unfold O2ReadLoop.in_win in W. lia.
        -- unfold O2ReadLoop.in_win in W. lia.
      * destruct (ai_owned_where A M vm a HI Ho) as [G|[[Gr _] _]].
        -- pose proof (AL_glob a G). unfold in_data in D. lia.
        -- pose proof (AL_grant a Gr). unfold in_data in D. lia.
      * exact (Hn p n Hp B).
    + intros a _ Ha. exact (Hgr a Ha).
    + intros a [Gr Gt] Ha. pose proof (AL_grant a Gr) as Hg.
      destruct (M a) as [b|] eqn:Ea; [discriminate|].
      exfalso. destruct (Hchg a ltac:(rewrite Ea; exact Ha)) as [W|[D|(p & n & Hp & B)]].
      * unfold O2ReadLoop.in_win in W. lia.
      * unfold in_data in D. lia.
      * exact (proj1 (Hblk a p n Hp B) Ea).
  - destruct HE as (Hab & Hcells & Hro). split; [|split].
    + intros a Ha. rewrite (Hsame a); [exact (Hab a Ha)|].
      intros [W|[D|(p & n & Hp & B)]]; [unfold O2ReadLoop.in_win in W; lia | unfold in_data in D; lia |].
      destruct (Hblk a p n Hp B) as (_ & Hlt & _). lia.
    + intros a Ha Hne. rewrite (Hsame a); [exact (Hcells a Ha Hne)|].
      intros [W|[D|(p & n & Hp & B)]]; [unfold O2ReadLoop.in_win in W; lia | unfold in_data in D; lia |].
      destruct (Hblk a p n Hp B) as (_ & _ & [G|Gr]); [pose proof (AL_glob a G) | pose proof (AL_grant a Gr)]; lia.
    + intros a Ha. rewrite (Hsame a); [exact (Hro a Ha)|].
      intros [W|[D|(p & n & Hp & B)]]; [unfold O2ReadLoop.in_win in W; lia | unfold in_data in D; lia |].
      destruct (Hblk a p n Hp B) as (_ & _ & [G|Gr]); [pose proof (AL_glob a G) | pose proof (AL_grant a Gr)]; lia.
Qed.

  Lemma sideW_block : forall A vm M buf cap E log,
    sideW A vm M buf cap -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    sideW A vm (mem_denot E M log) buf cap
    /\ forall x : word, ~ O2ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "p'0h07__arithh16__sat9h27__sat10h34__x1h41si001sh54__p1h64__ffh78__varmaph85__with97__sat11h:6__sat8h;2H7h<2H8h=1nh>1ph?6__sat5h@4__p2hA6__sat4hB6__sat3hC6__sat7hD2H5hE2H6hF4__p3hG6__sat6hH4__x2hI2H1hJ2H2hK2HahL1xhM1rhN2H3hO2H4hP1bhQ1AhR1EhS1HhT2H0hU3HE0hV2HShW4HloghX3HnehY3Hx1hZ3Hx2h[1Mh\3OUTh]3bufh^3caph_3logh`2vmi011gi021lp%0p%1p&0p;3p;2p;1p;5p;4p;6p;;p;9p;7p;8g00gRk30MTg00h[k30LTg00idk20<Tg006Qj15Tg0076j1aTg007Tj1rTg0087j1mTg008Yj1kTg00nMj5iTg01YKk303Tg00=Sj3UTg02TWj2fTg00DPj1HTg00l?j23Tg00S0j22Tg02okj2KTg019lj19Tg030dj1MTg00kaj1VTg0194j2lTg01Fkj2jTg00;2j20Tg01GSj3hTg01F:k204Tg00lik202Tg00AHj1wTg00Ahj2xTg00Bdj1}Tg00CBj1{Tg00Cmj2gTg00PEj1zTg01Mnk30KTg00EXk20JTg00=9k20FTg00F:k20ETg00Ffk30CTg00GEk40@Tg003Bj6tTg016\k20?Tg00<\j2RTg00;Nj27Tg00X2j3sTg00ODk10>Tg00Obj2qTg00RMj3pTg019Qj4ZTg03;Oj2oTg03<0j6WTg03<Qj3nTg03=2m;0;Tg03>Aj4_k309Tg03?Sj28Tg03@:j21Tg00J6k208Tg00H7k207Tg02X8j2JTg00U4j2;Tg00BFk406Tg02[@j2:Tg02YNj3vTg03@Vk301Tg03Anm90=Tg00UNj4dTg00V9j7cTg00Z>j8]Tg01VBk300Tg01Wfj3~Tg01aPk40ATg00Y6k70BTg00XRj6|Tg00YZk70DTg02Z\j6yTg0344R0k20GTg01:bk40HTg02ZBk30ITf0R1#5#5p=G%H1#Hp=A%51#5#5#5p=u%51#5#5#5#5#5#5#5p=L%51#5#5#Vp=Sg00ZbR2/21p=<%51#Vp>05g00[@R3/q1p=If2R4g00]DR5g00]cR6P6g00^CR7P3f1R8g00c2P1Cdg00_JR9Fcp=Cf3R:P5P6P6P7P4P8P1G]p=eB00331p=\A~331p=[%H1#5p=X%51#Hp=BP3P3P8P1H0Ap=b12:41081'7p=4P4P5P6P6P7P3P8g00cYP1CdP9Fcp=QP4P5P6P6P7P8P1K0Bp=DP8P5P6P6P7P1E|p=`P4P5P6P6P7P8P1K0Dp=?P8P5P6P6P7P1Eyp=^f4R;P5P6P6P7P:P4P8P5P6P6P7P1EyG]p=N1248/71p=T1;81,;4p=E1081,74p=Y10:41181+0Gp=6f6R<f5R=P;P:P4H0H;U8/71p==1J31p=>1K;:%M41J81';';p=OP4P5P6P6P7P3P8g03BhP1CdP9Fcp=PP<P5P6P6P7P=P;P:P5P6P6P7P4P8P1G]G]p=FAv481:0I;:p=@%M41J81';p>0:p,2ALR5p,2CLR9p,3ASR:0M5960L5R9+0<g01?bg00d@R>#5R?#GR@#5RA#GRB#aRC#rRD%a@#r#mR@[g03COg03DW#kP<P=P;P:P4Dig00deREg00eeRFg03EbRG<038g00eERH3U1f:Fp,3sp0RI5UDp,4SPloRJ%A>RK#H#A#A#A#A#A#A#u#L#L#L#SRL13CIRM'2p,4SPhi%5B#L#LRB#5#u#L#L#S,2M1KI1#9RN%M8#9ROf9RPf<RQf8RRPFPGP4P<PDPI%V?RS%H?RT#5#GRU#VRV'lRW13C1RX'2XPD1jSVRY102SRZ%<V102W[[R[%<SR\g01KhR]AhSV8UWKRV%<W\]^K\R^%HT$05RT,jSR_%<T1lSTR`,02[\ZRZAhST8V]XK\RT%<`\]^K\R\%VARA-04MR]%<M%<A202MA#<[[RAg00aZR`#wRa%k`R`1x38Rb%}3Rc%{3Rd%IL1g3>Re5Cd%z6R6%IS%aU60K3RU=CdeCe20Jd7R7P1P420FEH20E14=UEHdB0C328H0@RHb6b7b8X3312L112W8[^33P1PMPJO2b0bBbAb?bGbC1fPFRFP=Et20?33RJ%\1RL#<RE%[1RS%VBRB,RWRf'2'7XMJRg%GK#X#L#SRK%5>#B#G#X#A#X#A#X#SRh'bRi%5>#B#G#A#G#B#X#B#SRj%H>#B#G#A#B#B#B#G#SRk'bRl%H>#B#G#A#A#B#A#B#SRm%H>#B#B#X#L#SR>'bRn%wJRo5sJRp5sJRq%\iRr#<Rs%[iRt/2fRuP_PZPTP\P]PAPaP`&0>3RvPc1q32R2%IKRw5CdP7PHb6b7b8%<KP1b0bBbAb?PsePYP[PVP^P_PZPTP\P]PAPaP`PvPc%IhS00%IBRs9p3URU5CdP7PHb6b7b812hfP1b0bBbAb?bGbCPueCZPJPgPlPp%\lRu#<Rx%[lRy/2fRzP_PZPTP\P]PAPaP`PvPc%IjR{9Cd2P7PHb6b7b8%<jP1b0bBbAb?PxePYP[PVP^P_PZPTP\P]PAPaP`PvPc%IkS01=CdUP7PHb6b7b812kfP1b0bBbAb?bGbCPzeCZPJPgPnPo%\nRz#<Rx%[nR|/2fR}P_PZPTP\P]PAPaP`PvPc%ImR~9Cd2P7PHb6b7b8%<mP1b0bBbAb?PxePYP[PVP^P_PZPTP\P]PAPaP`PvPc%I>S02=CdUP7PHb6b7b812>fP1b0bBbAb?bGbCP}eCZ1oJgEWEWEWg02c7Rg,RW,2S,7EXMJ=nJGePDPI1RXg13C:REPEPXC4#9XPDP81RMg13C4RgPgPMC4#9ePFP=EtPJPLPEPEPSC4#9XMJRSPiPqP_PZPTP\P]PAp-0RqPaP`PbPcPdACdweRiQ009QdeS035DdRLACd{eRFQ019QdeS045DdRX1`d:RW5?d5?dS05,^dP6PdPLDNP7PHb6b7b8X33W5101hS069TK1101kS079Tj1R};E8g02flRf[12K8RU?Y8hPf[[^33^5qP1Pm13C<R^P^P>C4RVP^P;O3b0bBbAb?PrPgPgPtC4#9ePJPSPlPpP_PZPTP\P]PAPaP`PbPcPd1`d;Rp9?dX9?dWS08,^dP6PdPXDNP7PHb6b7b8X33X5qX@qAE8}4Pf[12j8Rl?Y8kPf[[^33^5q^@qP1PVPKP^P^PhC4RVP^P;O4b0bBbAb?PuPgPgPyC4#9ePJPSPnPoP_PZPTP\P]PAPaP`PbPcPdACd~eRoQ029QdeS095DdRn9?dXRX9?dWS0:,^dP6PdPnDNP7PHb6b7b8X33X5q101>S0;9Tm19E8}Pf[12m8R}?Y8>Pf[[^33^5qP1PVP^P;O3b0bBbAb?PzPgPgP|C4#9e1oJSEWEWEWAnJSGeN;0;WZWYXLDPPPQPRP4C_PQP4O15U@\O\N^LDPQf;RSf7RJf:RG<09<R|PPPRDiPGf=RzPPP4C_PzP4O15U@\O\N^LDPQPSPGP|PPPRP=PRPSPJP1C_PSP1O15U@#913C8R@1RMBR|'8P@P|P@P|C6P010g|11g|PIP:P:PD%m3RgP5P9fBRNP820831ROP@13C=RVPV207@1RnC4F=X=3#>X>DDOP110E|13C;S0</8KQ0<PKQ0<PKC6P010VK11VKPIP<P<PDPgP5P9fERyP8POP@13CRRRPRPnC4F=X=3#>X>DDOS0=P110^K13CJRu/8mPuPmPuPmC6P010Rm11RmPIPPPPPDPgP5P9fHS0>P8POP@13CSRSPSPnC4F=X=3#>X>DDOS0?P113CPRP/0m13CGRt/8jPtPjPtPjC6P010Sj11SjPIPQPQPDPgP5P9fKS0@P8POP@f>Rr,3CR[P[PnC4F=X=3#>X>DDOS0AP113CQRY/0j1KIzS0B%MzS0CPgP5P9fLP8POP@f?S0D,3CRxPxPnC4F=X=3#>X>D,JDS0E';S0F';PQPrPzP_PZPTP\P]PAPaP`P31x34P8PvH06S0GPcPd1g3?R?Ap3esS0H5QdP6PdQ0H=Cd?S0I=DdpDNP7PHb6b7b8X33XH3X5qS0J1R1B,081R8BS0K?T4:Pf[[^33^H3^5qS0LP1fAS0M,3CRs/0MPsPMPzO4b0b:b1b2Q0B#9eP_PZPTP\P]PAPaP`PbPcPdAQdewRvP6PdADdiWADdFp1`d=S0N9DdoS0O5?dS0P5?dDNP7PHb6b7b8X33X5qX@qXFqS0Q101K17U417l:17};3EPf[[^33^5q^@q^FqS0RP110s>S0S10skS0T10shPsPGO5b0b:b1b2Q0C#9eO3O1':W;P1O111Yj13CzR}/8kP}PkP}PkC6P010[k11[kPIQ0DQ0DPDPgP5P9fNP8POP@PsPsPnC4F=X=3#>X>DDOS0UP110xkf@Rl,KIS0V%MlRUPgP5P9fOP8POP@13CNRoPoPnC4F=X=3#>X>D,JDS0W';S0XPUQ0WP_PZPTP\P]PAPaP`PbPcPdAPde{S0YP6PdPvP6Q05FFP7PHb6b7b8X33X5qS0Z111j108KRFPKP4P4PhC4RiPjP4P4PkC4Rr;E:S0[[[^33^5qS0\P1fDS0],3CRQ10Q>S0^5TmPQPJPzO4b0b1b2b9PUeD@W<P1O111xkQ0VQ0X';S0_Q0DQ0MPlP_PZPTP\P]PAQ0JQ0LP110QMPQPMPlO4b0S0`b1b2b9Q0V#9S0aeP_PZPTP\P]PAQ0QQ0RP1Q0^10QkS0b10QhS0cPQPzO5b0R2b1b2b9%9US0deO3O1':W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111Pm18t>PtP>PtP>C6P010S>11S>Q0AP110Y>Q0BQ0FQ0CQ0EP_PZPTP\P]PAPaP`PbPcPdAPde~S0eP6PdPvP6A?dLXFFP7PHb6b7b8X33S0f111mPmP4P4P>C49Eir\F[^33S0gP1PsPJPGO3b0bCb:b1Q0CeD@WEP1O111Y>18}jS0hP}PjP}PjC6S0iP010[jS0j11[jS0kQ0UP110xjS0lQ0_Q0DQ0MPlP_PZPTP\P]PAQ0`b:b1b2Q0aeS0`P_PZPTP\P]PAP2b:b1b2Q0deO3O1':W;P1O111xjS0m13ClR2/8kS0nP2PkP2PkC6S0oP0Q0T11skS0pPIPNPNPDPgP5P9fQP8POP@PQPQPnC4F=X=3#>X>DDOS0qP110okS0rfCRF,KIRr%MFRiPgP5P9fRP8POP@13CyRXPXPnC4F=X=3#>X>D,JDS0s';S0tPiQ0sP_PZPTP\P]PAQ0fQ0gP1fGS0u,3CRLPzPlO3b0b1b2b9PieD@W<P1O111okS0vQ0t,;rRvPNQ0]PFP_PZPTP\P]PAQ0JQ0LP110LMPLPMPFO4b0S0wb1b2b9%9rS0xeS0yP_PZPTP\P]PAQ0QQ0RP110L>S0z10LkS0{10LhS0|PLPlO5b0b1b2b9%9iS0}eO3O1':W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WIP1O111^K18uhPuPhPuPhC6P010Rh11RhQ0?P110Ph1KIG%MGS0~PgP5P9fIS10P8POP@PYPYPnC4F=X=3#>X>D,JDS11';Q0~Q11P_PZPTP\P]PAPaP`PbPcPdQ03P6PdAPdewS11P6Q05FFP7PHb6b7b8X33X5qS05Q06118KQ0[[[^33^5qS06P110[>S0[9Tm[P[P;PJO4b0bAb?bGQ0~eD@WJP1O111Ph18tmS0~PtPmPtPmC6S12P010SmS1311SmS14Q0AP110YmS15Q0hQ0iP0Q0jQ0kQ0UP1Q0lQ0_Q0DQ0MPlQ0`P_PZPTP\P]PAPaP`PbPcPdAQde{P6PdAQde~R~P6PdQ009PdeS00P6PdQ039DdWRWQ0P5?dDNFFP7PHb6b7b8X33X5qX@qXFqS0P101j108mS03114hR{AY;:hRw12j:S0`/7=12m:S16/7<S173EPf[[[[^33^5q^@q^FqS18P1Q0^Q0b12KQS19PQP;PJPGO7b0b:b1b2Q0deO3O1':W;P1O1Q0mQ0nQ0oP0Q0TQ0pQ0qP1Q0rPrQ0tPiQ0sP_PZPTP\P]PAPaP`PbPcPdQ04P6PdQ0YP6PdP~P6PdQ11P6Q08FFFFP7PHb6b7b8X33X5qX@qS08Q07118j104m11:KPjP;P;PkC4=E=<[[[[^33^5q^@qS0YP112mLS1:Q0z'7S1;12KLS1<Q0|'7S1=PLP;PJPGPlO7b0b1b2b9PieD@W<P1O1Q0vPNQ0]PFQ0yP_PZPTP\P]PAPaP`PbPcPdQ019PdeP6PdP~P6PdQ00P6PdQ049DdpS01Q0O5?d9?dWDNFFP7PHb6b7b8X33X5qX@qXFqS0O111kQ0310:kR~,7=S0yQ175EwPf[\{[[^33^5q^@q^FqS03P1Q0z12jLS17Q1<PLP;PGPzO7b0b1b2b9Q0}eO3O1,:vW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111YmS1>18}>S1?P}P>P}P>C6S1@P0Q0[11[>S1AQ0UP110x>S1BQ0VQ0XPUQ0WP_PZPTP\P]PAPaP`PbPcPdQ09P6PdQ0eP6PdQ11P6Q0:FFS0:CeP7PHb6b7b8X33X5qS11Q0;118mR=114KQ0`/7~Q1610:>R~'75E;[[S16[^33^5qS0;P1Q19Q0c'7PQP;PJPzO5b0bCb:b1PUeD@WEP1O111x>S19182jS0`P2PjP2PjC6S1CP010sjS1D11sjS1EQ0qP110ojS1FPNQ0]PFP_PZPTP\P]PAQ0wb:b1b2Q0xeP_PZPTP\P]PAPaP`PbPcPdQ029PdeP6PdQ0eP6PdQ00P6PdQ01Q0NQ095Dd5?d9?dWDNFFP7PHb6b7b8X33X5qX@qXFqS01111>Q0y17<~5EwPf[\{\=[^33^5q^@q^FqS0yP1Q1:Q17Q1<PLPJPGPzO7b0b:b1b2Q0}eO3O1,:vW;P1O111ojS1713CFR=/8kS1:P=PkP=PkC6S0NP0Q0b11QkS09PIPyPyPDPgP5P9fTP8POP@PLPLPnC4F=X=3#>X>DDOS00P110XkS0efFR{,KIRw%M{R~PgP5P9fUP8POP@Q0>,3CS02Q02PnC4F=X=3#>X>D,JDS0w';S1GP~Q0wP_PZPTP\P]PAPaP`PbPcPdQ04P6Q0:CeP7PHb6b7b8X33X5qS0:Q07Q16[^33^5qS07P1fJS16,3CRb,2KS0410bhS1H'7S1IPbP;PzPFO5b0b1b2b9P~eD@W<P1O111XkS1JQ1G,;wRWPyQ0uP{P_PZPTP\P]PAQ0JQ0LP110bMPbPMP{O4b0b1b2b9%9wS0LeP_PZPTP\P]PAQ01Q0yP112mbS0J12jbS1KQ04PbPGPzPlO7b0b1b2b9%9~S1LeO3O1':W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WJP1O1n200110000021110211101b4WIP1O1n200110000021110211101b4WNP1O111E|Q0</8MQ0<PMQ0<PMC6P010VM11VMQ0=P110^M1KIJRVPgP5P9P{P8POP@PPPPPnC4F=X=3#>X>D:0:JDP_PZPTP\P]PAPaP`Q0GPcPdAQd?eREP6PdQ0H9Pd?P6Q0I=DdEFFP7PHb6b7b8X33XH31081Q0K,141R4BP:P:P4C4[[^33^H3P1PSPMP;PJO4b0b?bGbCPVe3vWOP1O111^M18uKPuPKPuPKC6P010RK11RKQ0?P110PKQ0~Q12P0Q13Q14Q0AP1Q15Q0hQ0iP0Q0jQ0kQ0UP1Q0lQ0_Q0DQ0MPlP_PZPTP\P]PAPaP`Q0GPcPdAPd?eP6PdADdpEDNP7PHb6b7b8X33XH3X5qRH1181AY:48Pf[[^33^H3^5qRqP112|QPQPMPzO4b0b:b1b2Q0aeP_PZPTP\P]PAQ0QQ0RP1Q0^Q0bQ0cPQPGO5b0b:b1b2Q0deO3O1':W;P1O1Q0mQ0nQ0oP0Q0TQ0pQ0qP1Q0rPrQ0tPiQ0sP_PZPTP\P]PAQ0ZQ0\P1Q1;PLPJPzO4b0b1b2b9PieD@W<P1O1Q0vPNQ0]PFP_PZPTP\P]PAPHPqP112|LPLPMPlO4b0Rfb1b2b9Q0xeP_PZPTP\P]PAQ0QQ0RP1Q0zQ0{Q0|PLPzO5b0R:b1b2b9Q0}eO3O1,:vW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O1Q1>Q1?Q1@P0Q0[Q1AQ0UP1Q1BQ0VQ0XPUQ0WP_PZPTP\P]PAQ0fQ0gP1PQPJPGO3b0bCb:b1PUeD@WEP1O1Q19Q0`Q1CP0Q1DQ1EQ0qP1Q1FPNQ0]PFP_PZPTP\P]PAPfb:b1b2Q0xeRfP_PZPTP\P]PAP:b:b1b2Q0}eO3O1,:vW;P1O1Q17Q1:Q0NP0Q0bQ09Q00P1Q0ePwQ1GP~Q0wP_PZPTP\P]PAQ0fQ0gP1PbPzPlO3b0b1b2b9P~eD@W<P1O1Q1JPyQ0uP{P_PZPTP\P]PAPHPqP112|bPbPMPFO4b0R:b1b2b9Q0LeRUP_PZPTP\P]PAQ0QQ0RP110b>R410bkQ1HPbPlO5b0b1b2b9Q1LeO3O1,:WW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WIP1O111PK18thPtPhPtPhC6P010Sh11ShQ0AP110YhQ0BQ0FQ0CQ0EP_PZPTP\P]PAQ05Q06P1Q0S9TmsPsP;PJO4b0b?bGbCQ0CeD@WJP1O111Yh18}mP}PmP}PmC6P010[m11[mQ0UP110xmQ0`Q1CP0Q1DQ1EQ0qP1Q1FPNQ0]PFPfP_PZPTP\P]PAQ0PQ18P1Q0zQ0{Q1<PLP;PJPGO7b0b:b1b2Q0}eO3O1,:vW;P1O1Q17Q1:Q0NP0Q0bQ09Q00P1Q0ePwQ1GP~Q0wP_PZPTP\P]PAQ08Q0YP1Q0J/74Q1IPbP;PJPGPlO7b0b1b2b9P~eD@W<P1O1Q1JPyQ0uP{PUP_PZPTP\P]PAQ0OQ03P1P4Q1KQ04PbP;PGPzO7b0b1b2b9Q1LeO3O1,:WW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111xm182>P2P>P2P>C6P0Q0S11s>Q0qP110o>PrQ0tPiQ0sP_PZPTP\P]PAQ11Q0;P1Q1=PLP;PJPzO5b0bCb:b1PieD@WEP1O111o>18=jP=PjP=PjC6P010Qj11QjQ00P110XjPyQ0uP{P_PZPTP\P]PAP:b:b1b2Q0LeP_PZPTP\P]PAQ01Q0yP1Q0JQ1KQ04PbPJPGPzO7b0b:b1b2Q1LeO3O1,:WW;P1O111Xj13C{RX/8kPXPkPXPkC6P0Q0{11LkPIQ0>Q0>PDPgP5P9fWP8POP@PbPbPnC4F=X=3#>X>DDOP1Q02/0kQ10,KIRIQ10#MRbPgP5P9fXP8POP@Q0@,3CR@P@PnC4F=X=3#>X>D,JDRn';R@PbPnP_PZPTP\P]PAQ0:Q07P1fM,3CRC,2KRK?YChPCP;PzPFO5b0b1b2b9PbeD@W<P1O1Q02/1k1;I@Q0>Q16Q10P_PZPTP\P]PAPHPqP112|CPCPMP{O4b0b1b2b9%9IeP_PZPTP\P]PAQ01Q0yP112mC12jCPKPCPGPzPlO7b0b1b2b9%9beO3O1':W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WJP1O1n200110000021110211101b4WIP1O1n200110000021110211101b4WOP1O1n200110000021110211101b4WNP1O1n200110000021110211101b4WXXLDB01JG<N90=P1CZb\bTbSWUWWWVW_WRX^3X]DW[W`WQo"). Qed.

  (* [comment removed for export] *)
  Lemma log_win_wdl : forall log, log_win_b 0 log = true -> log_wdl_b 0 DATA_RS log = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2TRun ()) ["TRun"] "p'0h01Hh12Heh22H0h31xh42b1h52b2h62opi002oph71ni011nh81bi021bh91ei031eh:5lemmah;2sxi042sxh<7e_addr0h=5e_vali055e_valh>7e_widthi067e_widthh?1ii071ih@1ki081khA2k0hB2loi092lohC3loghD1vhE1whF1yhG1zi0:1zi0;1ai0<6a_basei0=5a_offi0>6e_addri0?1sp;1p;2p;3p;7p;4p;6g008Yj1TTg03F\j2STg03Gcj2Mj3JTg02k@j3ATg02k\R0j2ITg03Hlj2OTg03IJj7NTg02lfj3HTg03Ilj1Kj2GTg02l5j3RTg03K5j37Tg01[[j1?Tg03L@j21Tg02[@j26Tg01ZRj1CTg01d9j3=Tg03MJj3>Tg03NSj3@Tg03O\j3<Tg01c0j4:Tg03Pej4;Tg01YKj3LTg00=Sj39Tg02Waj3FTg00<@j6PTg00deR1f0R2g00eER339p=8g03DWR4f1R5;F2p=Eg00eeR6g03EbR7;J2=913p=D1G62=913p=Bf3R8f2R9;75=F42p=Q1189?752,G6=913p=2f4R:/18?795=F42p=01189?7529J67=913p=3A7952,G6p=5P1P9P5g03;3P3P2EPp=4%T41S62#81M67R3=A45#81E29R;%D5R<[^34'Ip-0R=P01O25XF=X3=g03QnAA439#81E28R0P<[^34P2FNW:AH435%K6R3=A45#8%B5R<\;^34R;'IAA439#8P<\0^34;R2W:AH435P2O2P;P9P5P2O2P<P4%B2f7R<,E5%D9]1]0P9g03RdR;P;g00[^R;g02JKR3A7952#BP8P9P5f=R>CQA7:89#D]1]0]=]>P2g00[@R?P8P9P5P2C2P:P8P9P5f@D0P3P2f5R@P:P8C2P5f6RAP@P:fCD0P9P<PAP@C3]1]0P@%?2PAP@P:C2%?5P<PAP@fDRBD0%?9f8RC'1?5<AP1P=P2g02flR=g01Khn0110200020000X91RD;45P=%?8f9REPCP<C3/62b2W1W0XG?P2O1%C2PAP@P:C2%C5P<PAP@PBD0P5%C9PCP<PAC3eW1W0X7;P2O1g03SnR<A=952f:RBPEPCC2A=895f;RFPBPEfHRGD0A=:89f<RH'1?5FB?4D5P=A=@:8P>PHPFC3/62b2W1W0X53X43W6P9P5P2O3A>952PBPEPCC2A>895PFPBPEPGD0A>:89/1H?5FB?4D5P=A>@:8P>PHPFC3/62b2W1W0X53X43X6<P9P5P2O3g03TZR<A@952PBPEPCC2A@895PFPBPEPGD0A@:89/1H?5FB?4D5P=A@@:8P>PHPFC3/62b2W1W0X53X43W6P9P5P2O3A<952PBPEPCC2A<895PFPBPEPGD0A<:89/1H?5FB?4D5P=A<@:8P>PHPFC3/62b2W1W0X53X43X6<P9P5P2O3P8P9P5P2C:PHPFPBC2P:P8P9P5C:P>PHPFfJR<D0P@P:P8P9C:f>RG'1?5>H?4D5P=PAP@P:P8C:f?REPGP>C3/62b2W1W0X83X7;XB;X;1P8P9P5P2O4P8P9P5P2C;PHPFPBC2P:P8P9P5C;P>PHPFP<D0P@P:P8P9C;/1G?5>H?4D5P=PAP@P:P8C;PEPGP>C3/62b2W1W0X7;X??XA;X;1P8P9P5P2O4n0110300081010:101013010010;1023010010;1023010010;1023010010;1024010410910110340104108107101P5P2O2W1W0XD3XE;W@X83P5P2O2n0110?00012110<10=W<P9P5P2O3n0110?00013110>106105P2P5O2b0X10X94b0O2AL675#8eW0WCo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition slotsM (vals : list word) (buf : word) : Prop := slotsR vals buf /\ vals_ev vals 13 = Z_to_bv 64 calls.

  Definition at_tm (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 46%nat -> slotsM vals buf ->
      regs_ok (ENV vals) sr_TM R -> know_ok RSEGS (ENV vals) M kn_T ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data -> (L < cap)%Z -> (6 + cfg <= L)%Z -> (0 < paylen)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2f94c) M (seg_rom RSEGS)) (model2 vm)) K.

  Lemma tm_step : forall K j buf cap,
    at_tl0 K j buf cap -> at_tm K j buf cap.
  Proof.
    intros K j buf cap HTL A vm vals R M HL SL HR HK HS HB HcapL HLc Hpay.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    assert (Hcap26 : (cap <= 67108864)%Z).
    { rewrite Hcapj. pose proof (Z.pow_le_mono_r 2 (Z.of_nat j) 10 ltac:(lia) Hj10) as Hp. change (2 ^ 10)%Z with 1024%Z in Hp.
      change 67108864%Z with (65536 * 1024)%Z. apply Z.mul_le_mono_nonneg_l; lia. }
    destruct (paylen_facts HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    assert (PLdef : paylen = (L - 6 - cfg)%Z) by reflexivity. assert (Ldef : L = Z.of_nat (length data)) by reflexivity.
    unfold model2, O2ReadLoop.model2.
    assert (R10 : getr R 10 = Z_to_bv 64 paylen) by (regv HR (10 : reg); cbn [edenot ev ENV O2Open.ENV]; rewrite P9; reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x1794c) by (regv HR (1 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x49840) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV O2Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    assert (EQcfg : mkst R (Z_to_bv 64 0x2f94c) M (seg_rom RSEGS) = mkst R al_malloc_pc M al_rom) by (rewrite AL_malloc, AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC O2Open.fds0 vm stdin0 fs0 None (Some tid) None).
    destruct tm_itin as (I2 & R2s & VLKT & VLS2 & VLK2 & SR3 & KN3 & VLK3 & I3 & IX & S19).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (alloc_margin_le paylen) as HMG. pose proof calls_rng as Hcalls.
    pose proof (need_lo FUZZ_CALLS FUZZ_BMAX j cap HFC0 ltac:(clear -HFB0; lia) Hj10 ltac:(change (2 ^ 26)%Z with 67108864%Z; clear -Hcap26 Hc0; lia))
      as (HNK & HNB).
    eapply (ai_malloc_sure fx0 A M md R paylen (need_k FUZZ_CALLS j) (need_b FUZZ_BMAX j cap)
              (Z_to_bv 64 0x1794c) sp0 [a0s; path] envv K HI).
    - constructor; reflexivity.
    - change (m_kernel md) with a_kernel. change (m_vmmaps md) with vm.
      exact (vm_resv_incl _ _ vm Hres Hisp).
    - apply AL_env. exact HE.
    - exact R10.
    - clear -Hpl. lia.
    - change (m_vmmaps md) with vm. exact Hroom.
    - clear -HNK HFC0. lia.
    - clear -HNB HMG Hpl HFB0. lia.
    - unfold ROOM_NMAX. clear -Hpl. lia.
    - exact R1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite R4. symmetry. exact AL_tp.
    - rewrite R2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 208)%Z with (bv_unsigned sp0 + (-13) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, R2, u_small by lia. lia.
    - rewrite R2, u_small by lia. lia.
    - intros a Ha. rewrite R2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV O2Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LS16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    -
      intros A' m' vm' regs' res HI' Ha0 Hcs Hnz Hl0 Hl1 Hlq' Hnew Hfr Hlm Hgr Hvl' Htop' Hisp' Hres' Hmb' Hroom'.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop', Hvl', Hisp', Hres', Hmb'. rewrite Htop in Htop'.
      unfold md. rewrite with_vmmaps_C. clear md.
      pose proof (u64_range res) as Hrr. pose proof (u64_range buf) as Hbr0.
      assert (Hbr : buf <> res) by (intros Heq; rewrite <- Heq in Hl0; rewrite Hl in Hl0; discriminate Hl0).
      assert (Hlbuf' : live A' buf = Some cap) by (rewrite (Hlq' buf Hbr); exact Hl).
      assert (HE' : env_ok sp0 mem0 m').
      { apply (env_ok_allocT A A' M m' vm vm' HE HI Htop HI' Htop'). intros a H1 H2 H3 H4. apply Hfr; try assumption.
        rewrite R2, u_small by lia. unfold ALLOC_STACK in *. lia. }
      assert (HRT : roomT A' vm' calls).
      { unfold roomT.
        destruct (fuzz_le4 FUZZ_CALLS FUZZ_BMAX calls HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hcalls; lia)) as (HK4 & HB4).
        destruct (fuzz_nonneg FUZZ_CALLS FUZZ_BMAX calls HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hcalls; lia)) as (HK0 & HB0).
        apply (aroom_mono A' vm' _ _ _ _ Hroom'); clear -HNK HNB HMG Hpl HK4 HB4 HK0 HB0; lia. }
      destruct (ai_live_hull A' m' vm' res paylen HI' Hl1) as (_ & Hres16 & Hend & HbytesN).
      pose proof (round16_ge paylen) as Hr2.
      assert (Hres31 : (0x1000 <= bv_unsigned res)%Z) by (apply (live_lo sp0 Hvsp AL_grant A' m' vm' res paylen HI' Hl1); lia).
      assert (HsomeN : forall x : word, (bv_unsigned res <= bv_unsigned x < bv_unsigned res + paylen)%Z -> m' x <> None).
      { intros x Hx. destruct (HbytesN (bv_unsigned x - bv_unsigned res)%Z ltac:(lia)) as (_ & Hs & _ & _).
        unfold at_ in Hs. replace (bv_unsigned res + (bv_unsigned x - bv_unsigned res))%Z with (bv_unsigned x) in Hs by lia.
        rewrite Z_to_bv_bv_unsigned in Hs. exact Hs. }
      assert (HB' : bytes_at m' (bv_unsigned buf) data).
      { intros i Hi. unfold L in *. rewrite <- (HB i Hi). pose proof (Hlm buf cap i Hl ltac:(lia)) as Hq. unfold at_ in Hq. exact Hq. }
      assert (HP' : bytes_at m' (bv_unsigned buf + 6 + cfg) payload).
      { unfold payload. replace (bv_unsigned buf + 6 + cfg)%Z with (bv_unsigned buf + Z.of_nat (Z.to_nat (6 + cfg)))%Z by lia.
        apply bytes_at_skipn. exact HB'. }
      pose proof (ai_live_disjoint A' m' vm' res paylen buf cap HI' Hl1 Hlbuf' ltac:(intros Heq; apply Hbr; symmetry; exact Heq)) as Hdisj.
      pose proof (round16_ge cap) as Hr1.
      set (vals2 := vals ++ junk_vals regs').
      assert (HL2 : length vals2 = 78%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (A56 : vals_ev vals2 56 = res).
      { subst vals2. replace 56%nat with (length vals + 10)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r.
        unfold junk_vals, vals_ev. rewrite (nth_map_seq_gen _ 32 0 10) by lia. cbn [Nat.add]. rewrite <- Ha0. reflexivity. }
      assert (SL2 : slotsM vals2 buf) by (subst vals2; destruct SL0 as [SLR S13]; split; [repeat split|]; rewrite vals_ev_app_l by (rewrite HL; lia); try assumption;
                                          destruct SLR as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12); assumption).
      destruct SL2 as ((Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) & Q13).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG a0s path vals sr Rc regs' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs) as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2. change (sr_after_call_j sr_TM KEPT_AL 46) with tm_srM in HR2. clear HR. rename HR2 into HR.
      destruct tn_itin as (_ & _ & _ & _ & KNT).
      assert (HK2 : know_ok RSEGS (ENV vals2) m' tm_knM).
      { unfold tm_knM. apply Forall_cons.
        - cbn [kentry_ok edenot ev ENV O2Open.ENV]. rewrite A56. lia.
        - subst vals2.
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            pose proof (know_after_allocT A A' vals M m' vm vm' regs' kn ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLKT) HK HI Htop HI' Htop') as HK5 end.
          specialize (HK5 ltac:(intros a H1 H2 H3 H4; apply Hfr; try assumption; rewrite R2, u_small by lia; exact H4) Hgr).
          rewrite KNT in HK5. exact HK5. }
      clear HK. rename HK2 into HK. clearbody vals2. clear KW R10 R1 R4 R2.
      run_blk_keep scr0 78%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      assert (MC : mcH m' res (Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) paylen payload).
      { assert (NW : (bv_unsigned buf + 6 + cfg + Z.of_nat (length payload) < 2 ^ 64)%Z) by (rewrite Hplen; lia).
        constructor; rewrite ?u_small by lia; try lia.
        - pose proof (u64_range buf). exact (bytes_at_rdn m' (bv_unsigned buf + 6 + cfg)%Z payload ltac:(lia) NW HP').
        - apply store_ok_of_all; [lia|]. intros x Hx. unfold wview.
          destruct (m' x) eqn:EM; [discriminate | exfalso; exact (HsomeN x ltac:(lia) EM)]. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (B1 : getr Rc 1 = Z_to_bv 64 0x17960) by (regv HR (1 : reg); reflexivity);
        assert (B10 : getr Rc 10 = res) by (regv HR (10 : reg); cbn [edenot ev ENV O2Open.ENV]; exact A56);
        assert (B11 : getr Rc 11 = Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) by (regv HR (11 : reg); cbn [edenot ev ENV O2Open.ENV]; rewrite Q12; reflexivity);
        assert (B12 : getr Rc 12 = Z_to_bv 64 paylen) by (regv HR (12 : reg); cbn [edenot ev ENV O2Open.ENV]; rewrite Q9; reflexivity);
        destruct (ref_memcpy m' res (Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) paylen payload (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x17960)
                    ltac:(apply ret_ok_even; reflexivity) B1 B10 B11 B12) as (Rm & Hms & Hkeep);
        clear B1 B10 B11 B12
      end.
      replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
      set (M2 := wbytes m' res payload).
      assert (OUT2 : forall x : word, ~ (bv_unsigned res <= bv_unsigned x < bv_unsigned res + paylen)%Z -> M2 x = m' x).
      { intros x Hx. subst M2. apply wbytes_outside; lia. }
      assert (HW' : sideW A' vm' m' buf cap).
      { split; [exact HI'|]. split; [exact Hlbuf'|]. split; [rewrite Hvl'; exact Hvl|]. split; [exact Htop'|].
        split; [rewrite Hisp'; exact Hisp|]. split; [exact (vm_resv_step _ _ _ _ Hres Hres' Hmb')|]. split; [exact HE' | exact Hc0]. }
      assert (HW2 : sideW A' vm' M2 buf cap).
      { apply (sideW_frame A' vm' m' M2 buf cap HW'); [| apply wbytes_grows].
        intros a Ha. right; right. exists res, paylen. split; [exact Hl1|].
        destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res)); [exfalso; apply Ha; apply OUT2; lia|].
        destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res + paylen)); [lia | exfalso; apply Ha; apply OUT2; lia]. }
      assert (HBres : bytes_at M2 (bv_unsigned res) payload).
      { intros i Hi. subst M2. rewrite wbytes_inside by (rewrite ?u_small by lia; lia). rewrite !u_small by lia. do 2 f_equal. lia. }
      assert (HB2 : bytes_at M2 (bv_unsigned buf) data).
      { intros i Hi. unfold L in *. rewrite OUT2 by (rewrite u_small by lia; lia). apply HB'. exact Hi. }
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path)) sr Rc Rm callee_kept ltac:(rewrite HL2; exact VLS2) HR Hkeep callee_kept_no0) as HR3 end.
      rewrite HL2 in HR3. lazymatch type of HR3 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR3 end.
      clear HR Hkeep.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_ok_call RSEGS (ENV vals2) m' M2 [(0x1000, 0x10000)%Z] 0 0 IHI 0x39000) as KC;
        specialize (KC ltac:(cbn [ev ENV O2Open.ENV]; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
        specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HK3; clear KC
      end.
      assert (OUT2t : forall x : word, ~ touched (ENV vals2) [(0x1000, 0x10000)%Z] 0 0 IHI (bv_unsigned x) -> M2 x = m' x).
      { intros x Hnt. apply OUT2. unfold touched, IHI, WIN in Hnt. cbn [ev ENV O2Open.ENV] in Hnt. rewrite Q0 in Hnt. intros Hx. apply Hnt.
        destruct (live_where sp0 Hvsp AL_grant A' m' vm' res paylen HI' Hl1 ltac:(lia) Htop') as [[W1 W2]|[W1 W2]].
        - left. split; [lia|]. exists (0x1000, 0x10000)%Z. split; [left; reflexivity | cbn; lia].
        - right. left. lia. }
      specialize (HK3 OUT2t
                      ltac:(intros x _ Hx; apply (wbytes_grows payload m' res); exact Hx)
                      ltac:(intros m a k H1 H2; apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2])).
      lazymatch type of HK3 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK3 end. clear HK.
      pose proof (env_app_know RSEGS vals2 (junk_vals Rm) (blobs_ev (blobs0 a0s path)) M2 _ ltac:(rewrite HL2; exact VLK3) HK3) as HK. clear HK3.
      rename HR3 into HR.
      set (vals3 := vals2 ++ junk_vals Rm) in *.
      assert (HL3 : length vals3 = 110%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (T0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q0).
      assert (T56 : vals_ev vals3 56 = res) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact A56).
      assert (SL3 : slotsM vals3 buf) by (subst vals3; split; [repeat split|]; rewrite vals_ev_app_l by (rewrite HL2; lia); assumption).
      clearbody vals3. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
      clearbody M2. clear MC HP' HB' HW' Q0 Q1 Q2 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13.
      destruct SL3 as ((Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) & Q13).
      run_blk_keep scr0 110%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      apply pair_equal_spec in IX as [MIS MISS].
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (HTL fx0 A' vm' (map (edenot (ENV vals3)) tl_rvlm) Rx Mx res res fp_frm_zero_fx0) end.
      + rewrite length_map. reflexivity.
      + unfold slotsT, O2Hdr.slotsR. rewrite !vals_ev_map by (cbn; lia). cbn [nth tl_rvlm rvl18 app tl tm_sr3 edenot ev ENV O2Open.ENV].
        repeat split; assumption.
      + change (ENV (map (edenot (ENV vals3)) tl_rvlm)) with (xenv (ENV vals3) tl_rvlm (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ =>
          p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) tl_rvlm idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[]]. exfalso; lia.
      + change (ENV (map (edenot (ENV vals3)) tl_rvlm)) with (xenv (ENV vals3) tl_rvlm (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          apply (know_ok_xfer_entails RSEGS (ENV vals3) tl_rvlm idb _ _ kn kn_TL (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + split; [exact HW2|]. split; [intros _; exact Hl1|].
        intros q Hq Hqr. rewrite (Hlq' q (Hqr Hpay)). apply Hlq. exact Hq.
      + exact HRT.
      + split; [| intros H0; exfalso; lia]. intros _. split; [reflexivity|]. split; [exact HBres|]. split; [exact Hres31|]. split; [lia | exact Hres16].
      + exact HB2.
      + exact HcapL.
      + exact Hcap26.
      + exact HLc.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem trun_entry : forall K j buf cap, at_tl0 K j buf cap -> at_trun (tr_shape K) j buf cap.
  Proof.
    intros K j buf cap HTL A vm vals R M HL SL HR HK HS HB HcapL HLc.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    pose proof (bufW_facts A vm M buf cap (side_W A vm M buf cap j HS0)) as (Hb0 & Hb1 & Hal & Hbb).
    assert (Hcap26 : (cap <= 67108864)%Z).
    { rewrite Hcapj. pose proof (Z.pow_le_mono_r 2 (Z.of_nat j) 10 ltac:(lia) Hj10) as Hp. change (2 ^ 10)%Z with 1024%Z in Hp.
      change 67108864%Z with (65536 * 1024)%Z. apply Z.mul_le_mono_nonneg_l; lia. }
    destruct (paylen_facts HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    assert (PLdef : paylen = (L - 6 - cfg)%Z) by reflexivity. assert (Ldef : L = Z.of_nat (length data)) by reflexivity.
    destruct t_itin1 as (Ia & Ic & Ib & Id & XA & XC & XB & XD & CX & S19b & S19d).
    apply pair_equal_spec in XA as [MISa MISSa]. apply pair_equal_spec in XC as [MISc MISSc].
    apply pair_equal_spec in XB as [MISb MISSb]. apply pair_equal_spec in XD as [MISd MISSd].
    unfold model2, O2ReadLoop.model2. unfold tr_shape.
    assert (CZ : forall b, bv_eqb (Z_to_bv 64 cfg) (Z_to_bv 64 0) = b <-> (if b then cfg = 0 else cfg <> 0)%Z).
    { intros b. unfold bv_eqb. rewrite !u_small by lia. destruct b; [apply Z.eqb_eq | apply Z.eqb_neq]. }
    assert (PZ : forall b, bv_eqb (Z_to_bv 64 paylen) (Z_to_bv 64 0) = b <-> (if b then paylen = 0 else paylen <> 0)%Z).
    { intros b. unfold bv_eqb. rewrite !u_small by lia. destruct b; [apply Z.eqb_eq | apply Z.eqb_neq]. }
    assert (GO_M : forall rvl Rx Mx, (0 < paylen)%Z ->
      length rvl = 46%nat ->
      (forall i, (i < 13)%nat -> nth i rvl (ELit 0) = EVar i) -> edenot (ENV vals) (nth 13 rvl (ELit 0)) = Z_to_bv 64 calls ->
      regs_ok (ENV (map (edenot (ENV vals)) rvl)) sr_TM Rx -> know_ok RSEGS (ENV (map (edenot (ENV vals)) rvl)) Mx kn_T ->
      side A vm Mx buf cap j -> bytes_at Mx (bv_unsigned buf) data ->
      realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x2f94c) Mx (seg_rom RSEGS)) (mkModelC O2Open.fds0 vm stdin0 fs0 None (Some tid) None)) K).
    { intros rvl Rx Mx Hp Hlen Hid H13 HRx HKx HSx HBx.
      apply (tm_step K j buf cap HTL A vm (map (edenot (ENV vals)) rvl) Rx Mx); try assumption.
      - rewrite length_map. exact Hlen.
      - split; [repeat split|]; rewrite vals_ev_map by lia; rewrite ?Hid by lia; cbn [edenot ev ENV O2Open.ENV]; try assumption. }
    assert (GO_L : forall rvl Rx Mx, paylen = 0%Z ->
      length rvl = 50%nat ->
      (forall i, (i < 13)%nat -> nth i rvl (ELit 0) = EVar i) -> edenot (ENV vals) (nth 13 rvl (ELit 0)) = Z_to_bv 64 calls ->
      nth 14 rvl (ELit 0) = ELit A_EMPTY -> nth 15 rvl (ELit 0) = ELit 0 -> edenot (ENV vals) (nth 16 rvl (ELit 0)) = Z_to_bv 64 calls ->
      regs_ok (ENV (map (edenot (ENV vals)) rvl)) sr_TL Rx -> know_ok RSEGS (ENV (map (edenot (ENV vals)) rvl)) Mx kn_TL ->
      side A vm Mx buf cap j -> bytes_at Mx (bv_unsigned buf) data ->
      realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x179a0) Mx (seg_rom RSEGS)) (mkModelC O2Open.fds0 vm stdin0 fs0 None (Some tid) None)) K).
    { intros rvl Rx Mx Hp Hlen Hid H13 H14 H15 H16 HRx HKx HSx HBx.
      apply (HTL fx0 A vm (map (edenot (ENV vals)) rvl) Rx Mx (Z_to_bv 64 A_EMPTY) (Z_to_bv 64 0) fp_frm_zero_fx0); try assumption.
      - rewrite length_map. exact Hlen.
      - split; [repeat split|]; rewrite ?vals_ev_map by lia; rewrite ?Hid by lia; rewrite ?H14, ?H15; cbn [edenot ev ENV O2Open.ENV]; try assumption; try reflexivity.
        repeat split; rewrite ?vals_ev_map by lia; rewrite ?H14, ?H15; try assumption; reflexivity.
      - split; [exact (side_W A vm Mx buf cap j HSx)|]. split; [intros Hc; exfalso; lia|]. intros q Hq _. apply Hlq. exact Hq.
      -
        unfold roomT. pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0. pose proof calls_rng as Hcalls.
        pose proof (need_lo FUZZ_CALLS FUZZ_BMAX j cap HFC0 ltac:(clear -HFB0; lia) Hj10
                      ltac:(change (2 ^ 26)%Z with 67108864%Z; pose proof (proj1 (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS0)); lia)) as (HNK & HNB).
        destruct (fuzz_le4 FUZZ_CALLS FUZZ_BMAX calls HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hcalls; lia)) as (HK4 & HB4).
        destruct (fuzz_nonneg FUZZ_CALLS FUZZ_BMAX calls HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hcalls; lia)) as (HK0 & HB0).
        apply (aroom_mono A vm _ _ _ _ Hroom); clear -HNK HNB HK4 HB4 HK0 HB0; lia.
      - split; [intros Hc; exfalso; lia|]. intros _. split; reflexivity. }
    assert (P8' : vals_ev vals 8 = Z_to_bv 64 cfg) by exact P8.
    assert (P9' : vals_ev vals 9 = Z_to_bv 64 paylen) by exact P9.
    Ltac t1_sc P8' P9' :=
      cbn [sc_denot branch_taken edenot ev O2Open.ENV]; rewrite ?P8', ?P9'; unfold bv_eqb; rewrite !u_small by lia;
      lazymatch goal with
      | |- context [(paylen =? 0)%Z] => destruct (Z.eqb_spec paylen 0); cbn [negb]; first [reflexivity | exfalso; lia]
      | |- context [(cfg =? 0)%Z] => destruct (Z.eqb_spec cfg 0); cbn [negb]; first [reflexivity | exfalso; lia]
      end.
    destruct (Z.eq_dec paylen 0) as [Hp0|Hp0];
      (destruct (Z.eq_dec cfg 0) as [Hc0|Hc0]);
      [ run_blk_keep (SCR [true; false] [] []) 45%nat
      | run_blk_keep (SCR [false; true] [] []) 45%nat
      | run_blk_keep (SCR [true; true] [] []) 45%nat
      | run_blk_keep (SCR [false; false] [] []) 45%nat ];
      try (t1_sc P8' P9');
      (lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
         destruct (side_block_wdl sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap j E log HS0 ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end);
      rewrite <- EQM in HS1, OUT1;
      (assert (HB1 : bytes_at M0 (bv_unsigned buf) data) by
        (intros i Hi; rewrite OUT1; [apply HB; exact Hi | unfold O2ReadLoop.in_win; rewrite u_small by lia; lia
                                                   | unfold O2ReadLoop.in_data; rewrite u_small by lia; lia]));
      clear EQM.
    -
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO_L tl_rvld Rx Mx Hp0 eq_refl) end;
        [ intros i Hi; do 13 (destruct i as [|i]; [reflexivity|]); lia
        | cbn [nth tl_rvld rvl18 app edenot]; unfold calls; rewrite (proj2 (Z.eqb_eq cfg 0) Hc0); reflexivity
        | reflexivity | reflexivity
        | cbn [nth tl_rvld rvl18 app edenot]; unfold calls; rewrite (proj2 (Z.eqb_eq cfg 0) Hc0); reflexivity
        | | | exact HS1 | exact HB1 ].
      + change (ENV (map (edenot (ENV vals)) tl_rvld)) with (xenv (ENV vals) tl_rvld (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ => p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) tl_rvld idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) tl_rvld)) with (xenv (ENV vals) tl_rvld (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn => apply (know_ok_xfer_entails RSEGS (ENV vals) tl_rvld idb _ _ kn kn_TL (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    -
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO_L tl_rvlb Rx Mx Hp0 eq_refl) end;
        [ intros i Hi; do 13 (destruct i as [|i]; [reflexivity|]); lia
        | cbn [nth tl_rvlb rvl18 app]; apply (calls_x_val vals P11 Hc0)
        | reflexivity | reflexivity
        | cbn [nth tl_rvlb rvl18 app]; apply (calls_x_val vals P11 Hc0)
        | | | exact HS1 | exact HB1 ].
      + change (ENV (map (edenot (ENV vals)) tl_rvlb)) with (xenv (ENV vals) tl_rvlb (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ => p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) tl_rvlb idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) tl_rvlb)) with (xenv (ENV vals) tl_rvlb (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn => apply (know_ok_xfer_entails RSEGS (ENV vals) tl_rvlb idb _ _ kn kn_TL (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    -
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO_M tm_rvlc Rx Mx ltac:(lia) eq_refl) end;
        [ intros i Hi; do 13 (destruct i as [|i]; [reflexivity|]); lia
        | cbn [nth tm_rvlc rvl13 app edenot]; unfold calls; rewrite (proj2 (Z.eqb_eq cfg 0) Hc0); reflexivity
        | | | exact HS1 | exact HB1 ].
      + change (ENV (map (edenot (ENV vals)) tm_rvlc)) with (xenv (ENV vals) tm_rvlc (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ => p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) tm_rvlc idb _ (fun k => eq_refl) srb sr_TM _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) tm_rvlc)) with (xenv (ENV vals) tm_rvlc (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn => apply (know_ok_xfer_entails RSEGS (ENV vals) tm_rvlc idb _ _ kn kn_T (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    -
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO_M tm_rvla Rx Mx ltac:(lia) eq_refl) end;
        [ intros i Hi; do 13 (destruct i as [|i]; [reflexivity|]); lia
        | cbn [nth tm_rvla rvl13 app]; apply (calls_x_val vals P11 Hc0)
        | | | exact HS1 | exact HB1 ].
      + change (ENV (map (edenot (ENV vals)) tm_rvla)) with (xenv (ENV vals) tm_rvla (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ => p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) tm_rvla idb _ (fun k => eq_refl) srb sr_TM _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) tm_rvla)) with (xenv (ENV vals) tm_rvla (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn => apply (know_ok_xfer_entails RSEGS (ENV vals) tm_rvla idb _ _ kn kn_T (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
  Qed.
End TRun.
