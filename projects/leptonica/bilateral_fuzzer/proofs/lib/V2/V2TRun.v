(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (proofs and definitions restated for the model's changed definitions; the recorded (KReplay) proofs of tm_step and trun_entry re-proved by tactics, as pix_orient_fuzzer's copy; side_W, bufW_facts and sideW_frame re-proved by tactics for the ledger's vDSO reservations; the exit tactic's thread-pointer and thread-id addresses corrected to this binary's). *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec Room.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2ExitBase V2StdioDefs V2Exit V2Startup V2StartupDefs V2StartupFacts V2MainEntry V2LibStdioCall V2OpenFail_defs V2OpenFail_tail V2OpenFail_tail2 V2Open_defs V2Open V2Oom_defs V2Oom V2MemPreds V2Malloc65536 V2DirRead_defs V2MemcpyBase V2Memcpy V2ReadLoop_defs V2ReadLoop V2Grow V2Hdr_defs V2Hdr V2FuzzIface V2TRun_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac FPSteps.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2TRun () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib2V2:V2MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib6Common9CliDriver8SymDrive?nth_map_seq_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop9buf_factsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun5sideWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop5al_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop5vm_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc655366env_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic3and01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase<ai_live_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7round16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop:round16_geC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib2V2=V2Malloc65536;live_big_loC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib2V25V2Hdr7cfg_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib2V26V2TRun3cfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun1LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun6paylenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun7payloadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr6b2_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr6hdr_b2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib2V26V2TRun5callsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib2V2?V2OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib6Common9CliDriver<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver<RefPrintfLib:alu_and3_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7div_1_rC56Stdlib6ZArith6BinInt1Z7pow_0_rC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics5Riscv3Sem5alu64I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs4kn_TC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5kn_TLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7calls_xC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2V2;V2TRun_defs7t_itin1C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5t_r1aC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib2V2;V2TRun_defs5t_r1cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C59OSSVerify5KrLib2V2;V2TRun_defs5t_r1bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5t_r1dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tm_rvlaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6t_sr1aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5sr_TMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5t_kn1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tm_rvlcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6t_sr1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Hdr_defs4kn_RC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tl_rvlbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6t_sr1bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5sr_TLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tl_rvldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6t_sr1dC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc65536<ownedA_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00c59OSSVerify5KrLib2V26V2TRun=ownedA_rangeTC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2V2:V2ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs9kn_acallTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs4GLOBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2V26V2Open9above_sp0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3lebC46Stdlib4Bool4Bool3eqbC59OSSVerify5KrLib2V2:V2Hdr_defs4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC59OSSVerify5KrLib2V25V2Hdr7in_zseqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C46Stdlib4Bool4Bool8eqb_propc59OSSVerify5KrLib2V26V2TRun7sgn_tabC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop6in_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun:bufW_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib6Common8Mallocng9AllocBase9grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib6Common8Mallocng9AllocBase8ai_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init5Logic4True01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_wdlC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S?mem_denot_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun;sideW_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop7DATA_RSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall;entry_wdl_bC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C69OSSVerify5KrLib6Common9CliDriver7SymCall;entry_win_bC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00c59OSSVerify5KrLib2V26V2TRun6at_tl0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun6slotsMC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lc59OSSVerify5KrLib2V26V2TRun<paylen_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_malloc_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIfaceAfuzz_margin_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface;fuzz_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure?alloc_margin_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure<alloc_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room7need_loC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsc59OSSVerify5KrLib2V26V2TRun=env_ok_allocTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room8fuzz_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room;fuzz_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:aroom_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun5roomTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc655367live_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun>bytes_at_skipnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase@ai_live_disjointC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib5Lists7ListDef3seqC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRunAknow_after_allocTC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Grow<bytes_at_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC59OSSVerify5KrLib6Common7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V28V2Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc65536:live_whereC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes?pair_equal_specC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib2V2:V2ReadLoop;vals_ev_mapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun6slotsTC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer2rvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4emapC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer<regs_ok_xferC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXferDknow_ok_xfer_entailsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure>ai_malloc_sureC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun5at_tmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open4fds0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tm_sr2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6STOPSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tl_rvlmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tm_kn3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tm_srMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tm_knMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib2V2;V2TRun_defs7tm_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5tm_r2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tm_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tm_sr3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5tm_r3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tm_sr3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tm_kn3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIfaceAfuzz_calls_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun9calls_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure9ROOM_NMAXC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2V2>V2MallocLayout4LU16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2MallocLayout6LU17okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tn_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tn_kn1iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FPSteps?fp_frm_zero_fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface7A_EMPTYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr6slotsRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop4sideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop6model2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun6side_WC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib2V26V2TRun7tm_stepC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib2V2:V2ReadLoop>side_block_wdlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun;calls_x_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2TRun8tr_shapeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib2V2:V2Hdr_defs4sr_RC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

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
ltac2:(KReplay.run1 (kr_t_V2TRun ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0g0022R0p4p710p8p1002Rp4p70g003BR1p4p710R2p8p1003`p4p70P2p8p1004Np4p7210P2p8p1005:p4p70P2p8g0060R3p4p710P2p8g006Qj1HTg0076j1wTg007Tj1gTg0087j1~Tg008Yj1uTg0099j3qTg00:4j3KTP0j25Tg00:RR0j10Tg00;2R2j23Tg00;Nj26Tg00;ij2YTP3k30ITg00<@j6sTg00<\j28Tg00=9j2>Tg00=Sj37j1nTg00=mj3_Tg00>Sk10>Tg00?1j6^Tg00?Zj4\Tg00@Aj1TTg00@fj2PTg00AHj1|Tg00Ahj2XTg00BFj4LTg00Bdj1yTg00CBj1xTg00Cmj2JTg00DPj1cTg00E5j3QTg00EXk20HTg00F:k20GTg00Ffk30FTg00GEj4rTg00H7R3j21Tg00HTj2aTg00I:R4j1VTg00IZj4Nj3pj2ok10ATg00J6j2Wk10DTg00JXk20ETg00Jok20@Tg00KRk30?Tg00Kol<lTg00LTj1CTg00M3k10<Tg00MQk20;Tg00N2j3iTg00N[j2hTg00ODk108Tg00Obk205Tg00PEk104Tg00Pgk403Tg00QRj8RTg00Qok502TP1j6eTg00RMk307Tg00S0j2tTg00SLk200Tg00SilBkTg00TOl<dTg00U4j2}Tg00UNj4UTg00V9j7[Tg00V]j3`Tg00WFj2MTg00X2j3ITg00XRk60BTg00Y6k70CTg00YZj7{Tg00Z>j8zTg00ZbR1f0R5'tp=920015p=2g00[@R6/>5p=;g00[^R7P7P7P6P6P6g00\=P0P0P0f6R8g00\]f5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P0P0P9P:P;P<P=P5M<dp=bP6P6P2f7R>P2P8P9P:P;P<P=P5M<lp=Z1315p==1t51p=<A7651p=BA76;<,6:16=5'}p=?P<g00]DR2g00]cR?P?g00^CR@P6P=g00^cRAP5CUg00_JRBF[p=vA76=5p=OP6P7P6P6P4P:P0P;g00_jP<P=P5M<dp=mP7P7P7P6P6P6g00`WP0P0P0P3g00a7P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00aZR3g00bFR4,M=;I5p>0:A`6<=/M4=I35p=E1M<41M=4=I355I3p>09P=P2P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P2P?P?P@P<P=P2P?P?P@P5PBF[K0Cp=:P6P=g00c2P5CUp=FP=P2P?P?P@P5PBF[p=DP<P2P?P?P@P=P5F{p=]P6P=g00cYP5CUp=SP;P2P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI3=59I3<p>06g00d@R4#HR2#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P1%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|3RV%u3R3P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J62R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00deR_g00eER`'>Ra20G5<=7_`dB0F61=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA1RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P0%n6%0=R0/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P18%=8%28RiP8%<8%BiD?%2>P611cNRc,P1%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P1%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00eeRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP3P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20561R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c2,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P1K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP3P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;0AKD=<5q:eWGXM7WKXI6WHo"). Qed.

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
    (0x77000 <= bv_unsigned buf)%Z /\ (bv_unsigned buf + cap <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned buf mod 16 = 0)%Z
    /\ (forall x : word, (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z -> M x <> None /\ owned A x).
Proof.
  intros A vm M buf cap (HI & Hl & _ & Htop & _ & _ & _ & Hcap).
  destruct (ai_live_hull A M vm buf cap HI Hl) as (Hc0 & Hal & Hend & Hbytes).
  pose proof (V2ReadLoop.round16_ge cap) as Hr.
  split; [exact (V2Malloc65536.live_big_lo sp0 Hvsp AL_grant A M vm buf cap HI Hl ltac:(lia))|].
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
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x17bf0) M (seg_rom RSEGS)) (model2 vm)) K.

  Lemma paylen_facts : (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z ->
    (0 <= paylen < 2 ^ 26)%Z /\ Z.of_nat (length payload) = paylen /\ (0 <= cfg < 32768)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "h02Hah11xh24__p1h34__p2h44__p3h54__x1h64__x2h74__x3h84__x4h94__x5h:1nh;2H1h<2H2h=2H3h>2H4h?2Hch@7__arithhA4__ffhB6__sat5hC6__sat6hD6__sat7hE6__sat8hF6__sat9hG8__varmaphH5__withI4cstrhJ1mhK1yhL2z3hM2z4p&0p;1p;2p;3p;<p;6p;4p;Bp;7p;8g00DPj1>Tg006Qj11Tg00kaj1<Tg00H7j2KTg00S0j27Tg0194j2^Tg00;2j24Tg01L0j2pTg01Lej1kTg00;Nj20Tg0076j1VTg007Tk10;Tg0022j2TTg00I:R0k103Tg00;ij2~Tg00:RR1j1LTg00<\j26Tg00=9j2?Tg00=mj3\Tg00=Sj1lj3ITg00>Sj1jTg00Kol<eTg00?1j6aTg00@Aj1cTg00@fj2YTg00U4j2MTg01FWj2XTg01G?j3WTg00l?j2bTg01Efk20=Tg00lik20<Tg00LTj1;Tg00M3k10:Tg00MQk209Tg00N2j3`Tg00N[j2_Tg00AHk102Tg008Yj1}Tg00Ahj2PTg00ODj1uTg00BFj4STg00Bdj1rTg00CBj1qTg00Cmj2GTg00RMj3QTg00Obj2HTg00PEj1oTg00E5j3nTg01MZj3mTg00EXj2sTg00F:j2tTg00Ffj3vTg00GEj4wTg00Pgj4xTg00:4j3yTg0060j3zTg003Bj6{Tg00SLj2|Tg00TOl<]Tg00SimB00Tg00V]k301Tg00WFj2fTg00X2k304Tg00XRk605Tg00UNj4UTg00V9k706Tg00Y6k707Tg00YZj7dTg00Z>k808Tg00ZbR2f0R3'7p=2%13#1p=Z%13#1#1#1p=8g00[@R4f1R5;I3p=91|23p=DP4g00[^R6P4P4P0f4R0P1f3R7g00_jf2R8P5P3M<]p=iP6P6P6P4P4P4g00\=P1P1P1f6R9g00\]f5R:P0P7P8P5P3NB00p=hP6P4P4P4P1P1P:P0P7P8P5P3M<]p=g1423p=BAI432p=J%>3#>p==1_43p=EB01453p=5g00bF,f3p=Fg00aZR1@0453p=@P5g00]DR;g00]cR<P<g00^CR=P3J05p=RP4P5g00^cP3CUp=NP5P;P<P<P=P3g00_JK06p=3P8P;P<P<P=P5P3K07p=:P4P5g00c2P3CUp=CP8P;P<P<P=P5P3Fdp=[P4P5g00cYP3CUp=OP7P;P<P<P=P8P5P3L08p=Ag00d@R;#>R>#1R?#<R@g01N=RA'Kg01NoRB'7%1;RC#<RD%>?#1R?#<RE'^RF,4Bp,3sp0RBp,4dataRG'p%kGRH#2%1CRI#1RJ#1RK#ZRL#1#8#8#<RM,4H'0RNP6%VJ$0;RJ/TGRO1K@HRP$03RQ'~RR%LORS/6@/6HRT#214TF'0RU%L3RV/9T/0N'0X:6%LRRW/9TRX/0NRY,0U%DPRZ,6S#DR[/9TR\/0NR],0UPUPYPUP]p-0R]/?U9\UUPXPNP\PNP4P4%l4R\P3X14RXP\1953#jXK4X14PWP[PXPX1?4VX16PRP[1653#DXJ4X:4POPS1?4SPQPZPX%D3X14PPPP1?4PDiFhEgPTPT1?4TM<e1?]N9\NNEaEa%cO%2S1Y2P%BPRO19ZP'017P2%JZ'0'MPZP416S3RZ,Y2%BZ%DZRP/9Z'017Z2%JP'0'M16S5#DP4%=C#1#<RP,XD%BDRZ%2P1^DPRN#B[[%2DRTg01KTRXAWDP5UW0%2N\X^0T1XDE%2E%BF[\ZAWDE5VXX0T%2F\X^0T%VL/bBRB%<KRK+0=%2B%2K20<BK#2[[g00eeRK#;#;RL#;RT#;#;RX#;RE#;RZ#;#ERN&0:;-094RP%EZRZ5`4%EERE1_4KRK'5R['5RR'5#F%EL/5K,5Z#F15N[#F%EX%ET/5K'5#FA`4PE/5K,5Z#F%FR&021'@'@'@'@'@'@%}1P41P48P5P4P41P4:P:%u4CSP71P40CSCS%r4%q4R1f7RR,R11G4>RZ1G4;R;%>I,G4RI5Q4RK'N,315:11H42RE,CK,311NZE,315:15[1%o<R<P1f8RK,R11H4@RP1G4CRC5n4RT,NI,315:11CTE,31f9RI,R15:15[1P<P11CEC,311H4M,OC,315:1RXP<P11H4D%V?5m4R?,O;,31P<P11CT;,31P<P1%>>R>#>#=#=#=#=#=#=#1#Z#8#8#8#8#8#8#8#<RT,H41G4>'C,31P<AQ4;P=Q4CRC,CE,311OC?,315:11NZC,31=:1X5:1CACACACACACA1s1=P3P8g00deR1g00eER='?1t38=I1=dAv425CwbAbGbHX54X64X74X84X94X2]X3]X4]1630R5,98,0:1752%J8'0'M1K@8R8,9:,0R1782/0K'M%27147M'0147F1K@:/7017TK169@/6RR@#214@F'019K@%2R14RM'0'0'0[[[[[[^54^64^74^84^94^2]^3]^4]P3%JKPO16SK#BPKPBP9PHPSPRPIf;f<f=p,4SPloO>b@bBbCbDbEbFbMb>bLb=bICxAyJQG,TJAzJQGE{g01O_RQ,7214QF'0g01PT,TJ#L=I4Q172A14AM'0'0'0eb?W<W;o"). Qed.

  Lemma calls_rng : (1 <= calls <= 4)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "p'0h07__arithh14__ffh26__sat3h36__sat4h46__sat5h58__varmaph65__with72Hah84__x1h91Hh:2H0h;6__sat6h<1bi001bp;2p;1p;3p;4p;8p;7g01QJj2ZTg01R>j1YTg006Qj11Tg00kaj16Tg00;2j25Tg00;Nj24Tg01Lej1GTg01S2j2DTg00lij2<Tg00H7j2;Tg00S0j22Tg00DPj1>Tg01FWj2XTg0194j2TTg01G?j3QTg0076j1OTg00l?j2NTg01Efj2=Tg00AHj1LTg008Yj1KTg00ODj1HTg00Bdj1FTg00CBj1ETg00Obj29Tg00EXj2CTg00=9j2ITg00F:j2JTg00=Sj3BTg00Ffj3ATg00GEj4MTg00UNj4:Tg01SOj3@Tg00Ahj2PTg00Cmj2?Tg00PEj1RTg00E5j3STg00Z>j8WTg00V9j7VTg00Y6j7UTg00ZbR0f0R1'2p=0g00[@R2f1R3g00c2P1C:p=7P3g00]DR4g00]cR5P5g00^CR6P1g00_JFVp=3f2R7P4P5P5P6P3P1FUp=8p,3sp0R8p,4dataR9'Z%Y9R:#0R;g00d@R<#1R=#1R>#1#1R?#1#1R@#1#1#6,5:'4%G9/D0g00deR9P9%6<RAP9P2P1PA%6>R>,<:RB,;An0100000020000RC'212C>'4P1%6=RC%>=#>#1#6R='XRD150C%0=1TC=RE,50[[RF%0CRGg01KTRHAQC=3UW7R=%0E\H^7GRG%O@/N8R8%6?R?'=R@%08%0?1<8?#0[[R?g00aZR8#LRH%K8R8%H2RE%F2RC%E2RI192ARJ/7J,3I192>RK,7J,3I381CI6RLP1P7g00eERM,I91J17=B9MdAA203CMRMb1b5b612AA12A>'4P1b0b2b3b4PDPFP=PGP@P?PHP8PEPCP21920REg00cYR9PKC:,3IPLPMb1b5b6150>P1b0b2b3b49@:>%0BR015B>'4PDPFP=PGP@P?1=:>%0>P0[\;PHP81P23PCPIP4P5P5P61?2<R<,7E,3IP2P<P9PKC:,3I58I%R5AS2J<R<,7J,3I17<K,3I58IGWPLPMb1b5b6X82%01151>'41;A3R3,2A123>'4[^82P1PBf5O2b0b2b3b4b;b:n0110000020101b<b9g01T6RB,2A12B>'4eo"). Qed.

  Lemma calls_x_val : forall vals, vals_ev vals 11 = Z_to_bv 64 (hdr_b2 data) -> cfg <> 0%Z ->
    edenot (ENV vals) calls_x = Z_to_bv 64 calls.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "h01Hh14__x1h22Hah37__arithh44__ffh57__sat12h67__sat13h77__sat14h88__varmaph95__with:1bh;1zh<4__p1h=7__sat15h>1xh?1yh@2CXhA3H11hB2HbhC2HchD2_HhE3_H0hF3_H1hG3_H2hH3_H3hI3_H4hJ3_H5hK3_H6hL3_H7hM7__sat16hN1ahO1ehP4valsp&0p;1p;2p;3p;4p;5p;8p;6p;7g006Qj10Tg0076k10ATg007Tj1}Tg008Yj1NTg00LTj1LTg01Tjj2tTg01R>k10:Tg00HTj26k10DTg00=Sj31Tg019lj1`Tg016\j2JTg01Unj39Tg01VKj1^Tg01WRj3QTg00DPj1?Tg00AHj1HTg00X2j3XTg01Woj1]Tg01Y7j3VTg01Z>j1UTg01[Gj1TTg01\Pj4GTg01]]j5WTg01^jj2PTg01`0j2OTg01a<j4ITg01a\j2_Tg01b\k40HTg00kaj17Tg01cej3hTg00IZj4vTg00;NR0j24Tg01dnj2gTg01f7j4sTg01QJk20GTg00;2j2CTg00:Rj1qTg01:Ej2pTg0194j2MTg01gAj2eTg00lij2FTg00H7j2[Tg01S2j2YTg01g^k20FTg01h?k40ETg00=9j2oTg01FWj2nTg01G?j3mTg00l?j2lTg01Efj2kTg00Ahk20@Tg00Bdk10?Tg00CBk10>Tg00Cmk20=Tg00Obj2ZTg00E5j3jTg00UNj4RTg00EXk209Tg00F:k208Tg00Ffk307Tg00GEk405Tg00QRk804Tg00<@k603Tg01h[k201Tg003Bj6=Tg00XRk600Tg00PEk106Tg01igj2~Tg01k4k30;Tg01kWj1|Tg01l8j1{Tg01MZk30<Tg01lYj2zTg01mij4uTg01nEj3cTg00S0j2yTg00V9k70BTg00Y6k70CTg00Z>j8xTf0R1#0#0p=A%L1#Lp=:g00[@R2f2R3f1R4P1CIp=<%?1#0p=3%01#0#0#0p=K%01#0#0#7p=>%?1#?p=2%01#?p=DP2P2P4P1CIp=fg01nmR5?X41p=EP4g00deR6P1g00eER7CIp=\f5f4R8f3R9P3P4CI;11p=;g020:R:P:P1g021ECup=iP:P:P1g022=Cup=wg0236R;,g4=131p=8g0241R<?c41p=Bg024]R=?c34=191p=@g00ZbR>/y1p=5%01#7p=rg025IR?9161p=dP4g00]DR@g00]cRAPAg00^CRBP1g00_JK0Bp=SAc=41p>02P3P@PAPAPBP4P1K0Cp=aP9P@PAPAPBP3P4P1Gxp=bg00d@RC#0RD#0RE#0RF#0RG#ARH$0ARI#}RJ#Ng00eeRK#LRL#L#:#:RM#:RN#LRO#:RP,t1p,4dataRQ$0:RR,6IRS51Jg01N=RT=12>#`g025i%N5RU,J2RV/J6RWPVP6g026dRX1JXURYg0282RZg029>39R[79UR\#^AQXU[5<U1J22R[%0C#A#3#3#K#K#>%0C#3#2#K#2#D#A#>'f%0C#3#2#A#D#D#2#2#>%?C#3#2#A#3#D#3#3#>'f%?C#3#2#D#A#3#A#2#>%?C#3#2#3#K#K#>'f%H[5X[5X[3XR[%]\5VK%2C#3#A#D#3#2#3#>R\P?g02:7R]%UORO%T>R^CGP?P]%UNRNP^CG%H5R5'ER_'E5<U,\VE;R`PWPVP6g02:iRa99YZRb99XURc#^AQXUb5<U%]c9VK[P7g02;bRcPOP^CGP7P]PNP^CG/E5R5'E9<U\,\VE;R\PWPVP6g02<TRN99YZRb99XURd#^AQXUb5<U%]d9VK[%0C#2#2#D#2#2#3#>RdP7P]POP^CG/E_5<U,\VE;R_PWPVP6g02=MRW99YZRZ99XURY#^AQXUZ5<U%]Y9VK[P?PcPOP^CG/E59<Ud,\VE;RVg00[^Rd#NRU%N:R5'JROPUP5g02>FRcg02?AR[g02@<g02A6RYPKDWg02Ao1Pc[#i'OPUP5%Hd%H:CIR:E;RdPOPUP5g02BhRcP[g02CcPYPKDWg02D]RY,_a1Pc[#i'OP:E;RcPOPUP5g02ETRaP[g02FORZg02GIRXPKDW1_NY1Pa[#w'OP:E;RaPOPUP5g02HBR5P[g02I=RUPXPKDW1_WY1P5[#w'OP:E;R:g02J7R5P?PKPL%UPH0H%?C#7R[#T5h<%7CR<#T5h=RY71;RWP5%:P#:#:#:RXPZP^Cv%UM%7DRM#T5h=R=515P5PXPUP^Cv=15='4R='4R^'4RU'4RX'4RZ'4RO'4RN'4R]'4Rb'4P0P`Pbp,3ENVReP8O1g01T6,6IRf58JP1P0P\P]Pef8O1=8JfP1P0P_PNPef<O1=8JfP1P0PVPOPef@O1=8JfP1P0PdPZPefDO1=8JfP1P0PcPXPefHO1=8JfP1P0PaPUPefLO1=8JfP1P0P:P^PefPO1=8JfP1P0PWP=PefTO1=8JfP1P5PYPefXO1/g1=1JfXO5PJPSPJP?PKPLP1Cs16I[R['B16I<R5PfC@X:Jp,3sp0Rg00GQ%5RRQ%0H#rRh,CRRi'4P2PRPJ%7FRF%qK'p,MM,e1%qL,pF,MMRF'F,6I/B[P5PfC@X;2P2P<PJ1eR1/FF,6I/B[P5PfC@X;2P2PRPJ1F1F,6I/B[P5PfC@X;2P2PRPJ16I1/B[P5PfC@X;2PJ%7ERE,FRRF,6IRjPJP1P5PfC@X:JPJ1[F<Rk,6IRlA1J1fX:JP61YT>RmP?P01Y41#dA1234#`R0[A1241#`1Y34#d[Rn1Y93#d\020F41P1n2001000000120000000X?2X>2Pn^?2^>2P1PTP>fWRTO3b0H0EA16?mP6P?P6P2P1P<1[<FRnn0100000020000,6I91JlX:6P2PJ&0DIR0P0PkPnPJ\2/o0%2D#rRD,nMR01C>MRn%5D1MMDRk,C>[[Ro%5MRpg01KTRqAmMD4UW2RD%5k\q^2pRk1lIgRg%7GRG'kRr%5g%5G1FgG#5[[RG1kRE%5E%5F[\Qg00aZRQ#HRE%NQRQ20@24Rg&0?2Rs&0>2RtP220=2CRC1Z2<Ru5j2g00^cAj2uCCR'S209tBRuP1P31o6720813=167dB072>4H05R7b4b8b9X121[1<1[<1512^12P1PFO1b3b5b6b7b=L04PmP1J03b0A1Jlfe202j5201F<E=1BS[RFP0PoPDPkPrPGp-0RjPEPQPgPsPtP21Z2>g00c2PCCR,StRlPtP@PAPAPBP9J005at&06ARAPlCbPuP7b4b8b9X12W<%51R9/44%54RB[^12^<jP1PiPRP8O3b3b5b6b7,~RE=PJPFP5PfC@e1FRhP0PoPDPkPrPGPEPQPgPsPtP2PCg00cYRF1Z2hCR,St9atlRiPAPiCbPuP7b4b8b9X121C1h,49R91C4h,4B[^12P1PRP8O2b3b5b6b7:0;RhE=1eR<%|RE=1MM>%{ME=1lIS%7HRH,nM%5H1MMHR<,C>[\nAmMH4VqX2p%5<\q^2pP0PoPDPkPrPGPEPQPgPsPtPiPAP2PCPF1Z2M>0<2ICR,St9atlCbPuP7b4b8b9X121C4<,4B\9^12P1PRf6O2b3b5b6b7b=bM,zRE=PJP?PKPLPSCs/B[P5PfC@ebB1tTPfVE=PePTO1/gY=1JfeP;P4E=XL=X@WP4P1O2n2001000000121000000X0^XK:P4P1O2n2001000000121000000X0UXJaP4P1O2n2001000000121000000X0XXIcP4P1O2n2011000000121000000X0ZXHdP4P1O2n2011000000121000000X0OXGVP4P1O2n2111000000121000000X0NXF_P4P1O2n2111000000121000000X0]XE\P4P1O2n2111000000121000000X0bXD`P4P1O2n2111000000121000000bNWCWAWPo"). Qed.

  Lemma ownedA_rangeT : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x76568 <= bv_unsigned a < 0x76918)%Z
                 \/ ((0x77000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "p;7g02K@j70Tp,2ALp,2CLp,3ASRp,3sp0p,4Hvspp,7AL_globp,8AL_grantF0o"). Qed.

  Lemma know_after_allocT : forall (A A' : AS) vals (M M' : word -> option byte) vm vm' R' kn,
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> kn_vars_lt (length vals) kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 208 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    (forall a, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ owned A a \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_acallT kn).
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "h04__x1h14HLv0h27__arithh36__sat3h46__sat4h56__sat5h64cstrh74__ffh88__varmaph95__with:4__p1h;4__x2h<4__p2h=1rh>2Hah?1bh@1HhA2H0hB4__p3hC1ohD3HnthE2HxhF1ahG2HehH2HohI4__p4hJ6__sat6hK6__sat7hL4__x3hM1xhN1AhO2A'hP2H1hQ2H2hR2HIhS3HIAhT2HKhU3HLvhV2HMhW3HfrhX2HghY3HgrhZ2Hhh[3Hhih\2Hlh]3Hloh^3Hlth_2Hsh`4Htopha5HtopAhb1Mhc2M'hd2P0he2R'hf6__sat8hg6__sat9hh2knhi1mhj1nhk4valshl2vmhm3vm'p%0p%1p&0p;3p;2p;1p;4p;5p;6p;7p;8p;Ap;<g00gRk30jTg00h[k30iTg00idk20STg006Qj13Tg0076j1dTg007Tk10@Tg008Yj1|Tg0087k10OTg00DPj1ITg004Nk20ITg00LTj1pTg0022j28Tg02LBR0k20ETg00=Sj3=Tg02L\k20[Tg02Mck40CTg011mk50ATg014kk10?Tg00l?j25Tg00kaj1@Tg00<\j2?Tg00mIj4ETg019lj1>Tg02O3k20:Tg00PEk108Tg02P7k10HTg00;2R1j21Tg00S0R2j20Tg02Q9j1lTg02RAj3mTg00M3k10hTg0194k203Tg00:RR3j1;Tg00@Aj1LTg01FWk201Tg01G?k300Tg01Efk20ZTg00lik20YTg00AHk10BTg00Ahj2~Tg00Bdk10XTg00CBk10WTg00Cmj2nTg01MZk30>Tg00EXk20VTg00=9j2`Tg00F:k20RTg00Ffk30QTg00GEk40PTg003Bk60=Tg02R^R4j2{Tg00Obk20<Tg00Pgj4yTg02S6j4xTg02TCk20;Tg00ODk10NTg02UHk20MTg02Ukk109Tg00;Nj24Tg02VHk60KTg016\k20JTg02WMj3ATg02Wdj2VTg00H7j2BTg00<@j6gTg02X>j7vTg00X2j3fTg02Y:j3WTg019Qj4YTg02YTj4tTg00U4S00j2RTg02Ynj3]Tg00E5k307Tg02ZHk60GTg00N[j2kTg00V]j3rTg00WFk206Tg02Zlk204Tg02[Kk50FTg02\Kk30TTg02]Ek10UTg02^Lk80gTg02_XmA0fTg02`bk10eTg01Tjk20aTg00Kom<0DTg00?Zk40`Tg00UNj4eTg00V9j7qTg00Y6k702Tg00Z>k805Tg00RMk30_Tg01Unk30^Tg01WRk30]Tg01a<k40bTg00XRk60cTg00BFk40\Tg00YZk70dTf0R5#3#3p=:g00eeR6-0a5p=U%35#3#3#3p=P%35#Ip=jf3R7f2R8'0f1R9/15'4p=2A=895#>p=F1R95,R8p=c%I5#Ip=7%35#3#3#3#3#3#3#3p=X%35#@p=O%I5#3p=<1089/45p=Cg00[@R:/`5p=Hg00[^S01P:P0P3P2g02a_f5R2f4R0P7P8P9P5N<0Dp=N20E07P8P9P5H0`p=Jg00ZbR;/05p=611;5p=T20<:5p=9P8g00]DR<g00]cR=P=g00^CR>P:P9g00c2R?P5Ceg00_JR@Fqp=SP0P<P=P=P>P7P<P=P=P>P:P8P?P9CeP@FqP5K02p=Kf6RAP<P=P=P>P2P0P7P<P=P=P>P8P9P5L05L05p=^Q01P:P4P3P1g02bAP6P;P7P8P9P5N<0Dp=zP8P<P=P=P>P:P9g00cYR1P5CeP@Fqp=GP7P<P=P=P>P8P9P5L05p=DB0_:95p=\1195,48p=wg02bcR3,?5p=_P:P9P?P5Cep>0LP7P<P=P=P>P8P9P<P=P=P>P5P@FqK02p=iB0^::5p=hB0]::5p=o10781195'4,40p=Q1489/R5p=M1495,R8p=ZP:P:P9P5H0bp=uP9P<P=P=P>P5J0cp=aP8P<P=P=P>P9P5K02p=bP:P8P9P5H0\p=[P8P<P=P=P>P9P5K0dp=sP:P9P1P5Cep=}p,2ALR1p,2CLR@p,3ASR:0j1@60i1R@+0SS02Q02g00d@R?#3R4#3S03#3S04#3RB#:RC#dRD$0@RE#|Q04#d$0@RF$0ORG\ES05Q05g01?bS06Q06%I4RH#d00IEg020:#|%p6RI18EA+0Ef7RJ#Up,3sp0S075=Eg00deRKf8RL,8E00[8g00eERM3=g01@YS08p,3ENVRNf9ROO1PLP7H0CP1P@f<S09POPJI0A&0?LQ07,5DRP%PCRC#:RQ#PRR#3#:#PRS#@RT'?RU5=:P1P@f=RVf:S0:PLI0A&0?O==:UP1P@fAS0;P5CE#>P1P@Q0;P9CE#>20:18#>%I?RW#j#PRX#@S0<,?PRYg02cd'?15D7RZPZPYC2S0=#>S0>Q0;P0O1fBRYP0O15=G[[[[^FEf?S0?P5O1&08FRF5FG15D9R[&0H1R\'1P1P@fCR]P9CEQ0?P9O1=FGF3c[^FEp,4SPloS0@%7W#7#7#7#7#7#7#:#P#X#X#X#ORW/0Pp,4SPhiS0A%3S#:#P#X#X#ORS,0PQ08PN%lVS0B9mEYR^O1S0CQ0;f@S0Dg02dfR_&0hXRX%@CS0E'?RCPXg02e]R`%3?#:#<#<#:#X#OS0FPE%UYS0G%@4Ra%3H#:Rb#@Rc+03Rd15D5Re%IHRH#7Rf#@Rg-03aRh,0e3CX?ERiPEQ07PiPI18EYRi%@?Rj%;iRk'0RlPIPj%HjRmPiPk%HkRnENf;S0HDJRoPl18E]Rp#LRq%;p#6Rp201ag%TaRr%6g%Th[[%6aRsg01KTRtB00ag9UW>%6h\t^>s201acRg%6c%Td[\rRuB00ac9VtX>sRc%6d\t^>sRv%OHRH-01aRw%6H203aHRx#T[\rRrB00aH9VtX>sRH%6x\t^>sRs%@BRB-0ZPRt%6P%6B20YPB#6[[RBg00aZS0I$0BRxQ0I#|Ry1~:9Rz&0X:R{&0W:R|1n:?R}%9S5S|&08=R~P|%9WS0J=S|}P~P|P|%9aRa%db60>:RbP}%df:0>:a9S|}DKF^20V|>RaP5P81`KM20R58==KMdB0Q:;9H0PRMb7b8b9X0:105S10W9108h9Cd8[[^0:P5PPQ0AQ0@O3b2b3b4b5bJbKbfbgb6b1Q0GQ0:J0=%U^PYQ0BP61{6i%Tk1`:;S0GPiPkPnCzPoPlPqPpPwPrPHPsPtPBPxPyPzP{P|%9j=S|}P~20<:;Rn=G|}CDPaPMb7b8b9X0:S0A10j5%T9[^0:S0KP5fHS0L,8ES0M#;RkP2O2b2b3b4b5b6b1CyCxJ0=Q0C00;6,5DRi10ih5CdePoPlPqPpPgPuPcPvPwPrPHPsPtPBPxPy&0N:RvP{P|P|Pn%I?#<#7#<#:#X#ORc#9Ru%9TS0N,\b9G|uDKPaPMb7b8b9%6c1?dT7wcP5b2b3b4b5bJbKb6b1P;P`P`%_dC2ePoPlPqPpPwPrPHPsPtPBPxPyPvP{P|P|P|Q0N-0M:%9XS0OQ0E#9S0P'\S0QQ0QQ0O5S|DKP|Q0O00LnCiPaPMb7b8b9&09T10CXRn7CC10X;R;'4P5b2b3b4b5b6b1&093?CCn/4;ePNf>S0R#l9mE]O1S0SP_PCPXP`PeJ0K#>PEfDRNQ0?#lR;5mE#U15D8Rn/1`20J::R3AA35_R_%h5RpPZPZ%o5RqDQX=3'V'4Rl10`nRo%_eS0T7wn1BeCRdPnPn1BeXRbC23c#>X?EP5%UNRgPNP;P618ENR;,{6%;;Ri#TQ0GP;Pi%HiRhCzPIP;10jiR^PIPjPmP;PiPhENPVDJP^fER^,8ERh#L%;hRi#6PwPrPHPsPtPBQ0AQ0KP5fJS0U,8ES0V#;R;P2O2b2b3b4b5b6b1CyCxEg11[`P_PpPnPnPqDQX=3,V310`[15DgRg#_,1[1BgCP[P[1BgXC23M3M#>PE%U^S0W11Z`P_Pp15D0R_P_PqDQX=3,V310`ZQ0T,1ZPdPZPZPbC23M3M#>X?EP5Q07PVEg%_PS0X9won1BPCS0YPnPn1BPXS0ZC25cl#>PJP7P1P@Q0LP7CES0[fIS0\fFS0]PNP0Q09Q0HP5Fv%I?#<#7#:#<#<#7#j#:#ORl/0_%I?#<#7#j#:#<#:#7#:#ORo,1_PcP_P_PUC2S0^%@QRQ/0_%@RRR,1_3Z3MS0_Q00Pl15D2RbPbPoC2PcPbPbPUC2S0`10Qb11bR3Zg02fXS0aP5Pl15DARdPdPoC2P015DJRg/1cS0b1uloRS%3?#<#7#P#7#<#j#<#ORK%3?#<#7#P#7#<#<#:#OS0c'uR?1uQRRf&0B3S0d5f3S0e5f3S0f5f3S0g9A35S0hPp15DLS0iQ0iPqDQX=3S0j,V3S0k'4PcPgPgPUC2S0lQ0Y/0gQ0Z,1g3ZQ0bQ0kPIQ0V10j;S0kPIPjPmQ0VP;%H;ENP]DJS0VQ0kfKS0b,8ES0m#LS0nQ0m#;S0o#6S0pPwPrPHPsPtPBp-0R;PxPyPzP{P|1a|7S0q%9oS0r9G|}S0s5b|P~AG|}uS0tCDPaPMb7b8b9X0:W:115oS0u,49119cS0v[^0:^:;P515DVRV,0lPVPAO3b2b3b4b5b6b1P3Q0jPSQ0g9A3S%hSPgPg%oSC2S0jA=3SSQ0f9A3S1`3S3WQ0VQ0kQ0nQ0pPwPrPHPsPtPBPxPyPzP{P|P|P|%9lP}Q0sDKS0sP~Q0sCDPaPMb7b8b9X0:Q0u9Cl5119oS0u9Cl9[^0:P5PVPAO2b2b3b4b5b6b1Q0jeCYCtCY3WO1WXP5O110cd11dUPQPdPdPRC23MQ00Q0lPQPgPgPRC2Q0aP5PcQ0iQ0iPUC2PA15DORg/1cS0lQ0hPpQ0:,5DRVPVPqDQX=3S0j,V3S0s'4S0pPcPgPgPUC2S0nQ0YPgPgQ0ZC2S0k'RS0VQ0nQ0kPIfLS0w,8ES0xQ0x#;S0y,0jS0zPIPjPmQ0xQ0yQ0y#HENP^DJS0{Q0zfMS0|,8ES0}#LS0~Q0}#;#6S0}PwPrPHPsPtPBPxPy1~:8?[9vS10P{P|P|P|PuP}1n:4R4Q0N'\9G|}DKS11P~Q11CDPaPMb7b8b9X0:X;:PcP5P51?9TS11C2PcP9P91?8TC2[^0:^;:P5PPQ0?,5DS0?PAO3b2b3b4b5b6b13W3]O1WZP5O1PQQ0iQ0iPRC2PAQ0pQ0VQ0lQ0sQ0{Q0zQ0~Q0}PwPrPHPsPtPBPxPyPzP{P|Q0q%9RS0s9G|}S0l5b|P~Q0tCDPaPMb7b8b9X0:X:;115RS0i,49Q0v[^0:^:;P5Q0?,0QQ0?PAO3b2b3b4b5b6b1P3Q0jPfQ0g9A3f%hfPgPg%ofC2S0jA=3SfQ0f9A3fA=3?fQ0e9A3fA=3ffQ0d9A3f1`3f3W3]3]Q0{Q0zQ0~Q0}PwPrPHPsPtPBPxPyPzP{P|P|P|%9QP}Q0lDKRfP~PfCDPaPMb7b8b9X0:Q0i9CQ5119RS0i9CQ9[^0:P5Q0?PAO2b2b3b4b5b6b1Q0jeCYCtCY3WO1W\P5O1n200100000021100011000W@P5O1n200100000021100011000S0VbCWHQ0[#>eP1P@fGS0[P7CERfQ0LP^P]P0Q0:POP5FvQ0_Q0VbCWH%>fe20:17S0Vp,8AL_errnoP0P5O2PKP_P_Q0cC2P811bcS0_Q0hPpPdPdPqDQX=3S0p,V3Rf'4Q0`Q0Y/0bQ0Z,1b3ZQ0_PfPIQ0M10jkS0_PIPjPmQ0MPk%HkENQ0;DJS0`Q0_Q0\,8ERf#LS0j%;f#6S0?PwPrPHPsPtPBPxPyPzP{P|Q0qQ0c#99G|}S0l5b|P~Q0tCDPaPMb7b8b9X0:X:;Q0c,15S0t,49Q0v[^0:^:;P5Q0H,5DRf,0KPfPAO3b2b3b4b5b6b1P3Q0pP?Q0g9A3?%h?PbPb%o?C2S0gA=3S?Q0f9A3?A=3??Q0e9A3?1`3?3W3]Q0`Q0_Q0jQ0?PwPrPHPsPtPBPxPyPzP{P|P|P|%9KP}Q0lDKRzP~PzCDPaPMb7b8b9X0:Q0t9CK5PKP9P9Q0cC2[^0:P5PfPAO2b2b3b4b5b6b1Q0geCYCtCY3WO1bGWGQ0V#>eQ0=P911_cQ0hPpPbPbPqDQX=3,V3'4Q0^Q0YP_P_Q0ZC2RK'RQ0^PIQ0[,8ERz%;zR?,0jRSPIPjPmPzP?%H?ENQ0DDJPSQ0M#L%6kPwPrPHPsPtPBPxPyQ10P{P|P|P|Q0<#9,\}RkQ0P'\P4AG|4kDKP~P|P|P<P=P=P>1a|0R>1a|2R=P|P|Q0Q:07:}P4Q0O:07:}9G|4DKR}5s|5s|J0GP~P}F^PaPMb7b8b9X0:X;:X:;X<;Q0<,?5R}Q0E'?P9P9P}C21B9CP8P81B9XC29c70Q0a[1B8CP7P71B8XC2[[^0:^;:^:;^<;P5PcPVPVPUC2RX11VcQ0hPpPfPfPqDQX=3,V3'4PVPPPAPJO6b2b3b4b5b6b17]K3]O1W_Q0>eO5bDbDWDXMEQ0S00;6,5DRK#_PePePKC2P]P9O1=FGFPEQ0D#lR]9mE^#UQ0TPZPZPeC2X?EP9Q0WP^P]P61{6h%TiQ0GPhPi%HiR]CzPIPh10jiRKPIPjPmPhPiP]ENQ0RDJPKQ0],8ERK#L%;K#6PwPrPHPsPtPBQ0AQ0KP5Q0oP2O2b2b3b4b5b6b1CyCxEgQ0W,5DRK#_PnPnPKC2PEQ0]#UQ0TP_P_PeC2X?EP5Q07Q0REgQ0XPZPZPPC2PJP0P8O211_\P1P@Q0\P0CEP^P0O1=FGF3cQ0011b\P1P@Q0UP2CEQ0]P2O1=FGF'RQ0[PAO1=FGFRbP511d\p,5AL_hi10\cQ0\PLO1=FGFRdPIQ0mQ0o,0jR^PIPjPmQ0mQ0oQ0o#HENPNDJP^Q0x#LQ0y#6PwPrPHPsPtPBQ0I%pIR^#pR_#p,k:1k:_1k:^1k:65r:5r:R65r:g00bFR^+06;fxPy1~:7?[8v?[9v?[7vP{P|AS|4uP~P|Q04,n:Ru=G|4P~P|Q03,n:R4Q0N'\R_=S|uRZ=b|=P~P|Q0J=S|4R4P~P|P4P~1a|AReCDF^RKF^PaPMb7b8b9X0:X;:XL:X:;X<;105c11791?7T?C0210W010W2PO[[[[[^0:^;:^L:^:;^<;P5Q0aQ0R,5DR]/1PP]PPP\PAPJQ0:Q0DQ0@O:b2b3b4b5b6b1+04bAW@P5O1P1P@Q0bPACE/RbQ00P1P@Q0wPJCEQ0LPJO1=FGFPdP5P1P@Q0|PLCEfNQ0bQ0\POQ0;Q0DP5Fv10lg11goQ0n10Qg11gR3Z3MQ00PlPVPVPoC210QV11VR5ZXQ0wQ0HO1=FGFP5PlPfPfPoC2Q0|Q09O1=FGFRFPIfO,8ERG%;GRo,0jRXPIPjPmPGPo%HoENQ0LDJRoPXfP,8ERG#LRm%;G#6RGPwPrPHPsPtPBQ0I2066^;fxRxPyQ10?[8v?[8vRvP{P|P|P>P|Q0r,}uCiP~PKCDPaPMb7b8b9X0:X;:X:;X<;XB;Q0u,48Q11/08RK/4010W8R^10W7RWPL[[[[^0:^;:^:;^<;^B;P5Q0a15DYRD/1PR610lDPDPPPAQ0RPNQ0@O9b2b3b4b5b6b1+04WAP5O110cf11fUPQPfPfPRC23MPoPXPmPGPwPrPHPsPtPBPxPyPvP{P|P|P>P|1}u_CiP|P=P|Q0s,}uCi5s|P~P|Ab|ZeP~P|P4P~P|P4P~1a|JF^F^PaPMb7b8b9X0:X;:X:;X<;XB;XI;1?5T,19Q0i,475M814K2PO\W\^[[^0:^;:^:;^<;^B;^I;P5Q0aP610QD10cDPDPPPAQ0RPNQ0@O:b2b3b4b5b6b1-04FWAP5O1n200100000021100011000bCW@P5O1P5X@dP5O1n200100000021100010000WAP5O1n200100000021100011000bCbEbEWVWEXMEQ05Q01Q0F/0[%;9,Bn/0`P0P7P8P9P5I0FWQWPWjXFEWiQ09Q08PYQ0Bp,3AMBp,3a0sp,4path40T$0UQ0;Q09POPLL0gNA0fQ08Q0CQ0DQ09$0eH0Ceb[b]WYWWW`WRWaWSWTW^WdWUWhWeWmWlWcWbWkWOWNo"). Qed.


  Lemma env_ok_allocT : forall A A' M M' vm vm',
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 208 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "h04__x1h14__p1h21ah37__arithh44__ffh56__sat3h66__sat4h76__sat5h88__varmaph95__with:4__x2h;4__p2h<2Hah=1oh>1Hh?2H0h@2HehA2HohB4__p3hC1AhD2A'hE2FRhF2H1hG2H2hH3HEahI3HElhJ3HErhK2HIhL3HIAhM3HfrhN3HnehO4HtophP5HtopAhQ1MhR2M'hS2vmhT3vm'p%0p&0p;3p;2p;1p;5p;4p;7p;6p;8g00gRk30>Tg00h[k30=Tg00idk200Tg006Qj10Tg0076j1nTg007Tj1kTg0087j1~Tg0111j3^Tg02g5j3bTg00l?j2?Tg00;2j24Tg00DPj15Tg019lj1:Tg00=Sj33Tg00kaj1ETg00S0j21Tg00PEj1qTg00;NR0j2<Tg011mj5ITg014kj1MTg00<\j2HTg00mIj4ATg02O3j2rTg02X>j7gTg01FWk20<Tg0194k20;Tg01G?k30:Tg01Efk209Tg00lik208Tg00LTj1ZTg00N[j2QTg00WFj2eTg00AHk106Tg00X2j3dTg008Yk105Tg00Ahj2mTg00ODk104Tg00Bdk103Tg00CBk102Tg00Cmj2UTg00EXj2}Tg00=9j2|Tg00F:j2{Tg00Ffj3zTg00GEj4yTg00RMj3_Tg00U4R1j2RTg003Bj6]Tg019Qj4lTg00V]k301Tg00BFj4vTg00Obj2uTg00UNj4YTg00V9j7\Tg00Y6j7[Tg00XRk607Tg00YZj7pTg00Z>j8fTg02ZHj6sTf0R2#0#0p=@%52#0#5#5p=J%02#0#0#0p=F%52#5p=7%02#5p=;%02#0#0#Ep=9%52#0p=2%52#5#0#0p=cf2R3f1R4'1/<2p=jf3R5/13/<4/R2p=C%02#Ep=i11531442'<p=8%02#0#0#0#0#0#0#0p=V1434,<5/R2p=tg00[@R6?342p=K1<42,R3p=Pg00ZbR7/12p=OB01642p=LP6P3P4P2Cvp=B1u62p=6P6P4g00c2R8P2CYp=TP3g00]DR9g00]cR:P:g00^CR;P6P4g00cYR<P2CYg00_JR=F\p=>P5P9P:P:P;P3P9P:P:P;P4P=F\P2F[p=WP3P9P:P:P;P6P4P8P2CYP=F\p==P4P9P:P:P;P2J07p=af4R8P9P:P:P;P5P3P9P:P:P;P4P2F[Fpp=Df6R>P9P:P:P;f5R?P8P5P9P:P:P;P3P4P2GfGfp=N1442,<3p=XP4P9P:P:P;P2Esp=SP5P9P:P:P;P3P4P2Gfp=GP3P9P:P:P;P4P2Fpp=xP3P9P:P:P;P4P2F[p=`P6P4P<P2CYp=hP5P9P:P:P;P3P4P9P:P:P;P2P=F\F[p=o1<34/R2p=wp,2ALR=p,2CLR9p,3ASR:0>=960==R9+00S00Q00g00d@R<#0R@#0RA#0RB#0RC#@RD#nRE#kRF%nB#kRG#~RH[S01Q01g01?bS02Q02p,3sp0RIp,4mem0RJ;^5P0AbIJ8%0<#J#F#7#;#@#9RK1?E2RL%0<#2#c#;#;#7#7#9RM,4L%5<#2#c#2#;#2#2#9RN%5<#2#c#2#J#;#9RO,4LRP7jLCCRQ%0<#J#F#7#2#;#2#iRR1?E4RSPS%0<#J#F#7#2#2#9RSC8#:RTf7RUP3O1PJP3O1RV53H[[^2F%FDS03#@RD#FRW#ERX/1LRYPL%0<#@#2#@#V#9RZ%0<#@#2#;#7#;#2#;#9R[PLPL%0<#@#2#;#7#;#2#2#9R\C8CtR]P>P4O1%qGRG53H[^2F'<P=P9PUP?P5DI%M81?EIR^%FW#9RW'HR_'KP=P9f8R`P>P8DI%M?/K_P=P9f<RaP2CA#:P=P9PaP4CA#:1r=3S04#:Rb%5<Rc#0#2#9Rd,H^S05g02cd'HS061?E5RePeQ05C8#:Rff=RgP8O1f>S07P8O153H[[[[^2Ff9Rh9^IJ[[[[[P2AbIJ>f:RiP3O1=3HV\T\Q^2FPhP4O1=3HG\]^2F'<P0f;R0P3O1=3HV\T\Q^2FPiP4O1=3HG\]^2FP=P9P0PhPUDI%M`/K_P=P9PaPiP`DI%Mh/K_P=P9f@RjP2CA#:P=P9PjP4CA#:fAP8O1fBS08P8O153H\f\b[[^2FA^IJg[[[[[P2PgP3O1=3HV\T\Q^2FPgP4O1=3HG\]^2FP=P9Q07PaPiDI%M0/K_P=P9f?PgP0DI%Ma/K_P=P9fCS09P2CA#:P=P9Q09P4CA#:fDRaP8O1fERgP8O153H\f\b[[^2Fp,4SPloRf%7c#7#7#7#7#7#7#F#V#V#V#9Rc/1^11^LS0:?PYPS0;P8P3P=P9fGS0<P3CAS0=fHfFS0>PaP5PhP`P2FgPOPe%5<#J#;#@#2#@#7#9RY,4e%5<#J#2#V#9RPPe14e_%EDRDPePePXC8CCCCS0?P1PO1?E8R1P1PYC8PPP1141_PDP1P1PXC8CCg02fXR1P2PO1?E?RLPLPYC8%E@Rj%5@S0@#5#iRk+0<Rl147j%Ok20;jkRm,47[[Rn%OjRog01KTRpB0:jk4UW<Rk%Om\p^<oRo%ECRC-09^Rp%O^%OC208^C#O[[RCp-0Rmg00aZRjg00eeRq#ZRr#ZRs#ZRt,Q6S0A1Q6sRs1Q6qS0B'L'Lg00bFRq'e&06jRu3dS0C&05jRv1m63S0D&046Rw7B4S0E?B3w?B3wS0F&036Rx&026RyPyPy%6ORz1U6BRB'T%6Y9>yBCW%q:R:PyPy1U6ARA==yBS0GPy1ay8R{A>yBzS0HDDP:Py%6cR|==yAR}P:PyP}P:1ay?S0IFNS0JFN1}y;R;P2P3g00deR}g00eER~'|1{23=3}~dAz674CyR7b4b8b9X06X:6X1mW;POP4P4PYC81143RY143OR~7P511c3R}11c5S0KPU[[S0L[[^06^:6^1m^;mP2P11?EiRi,1XPiP^P8PhP0PfO8b3b5b6b7W?P2O1PPPL14L_PDPLPLPXC8CCPlPnPkPoPpPCQ0CPvQ0FPxPyPyPyPy%6P/TB%6W9_6A9>yBCWPyP{%6XRA9>yBDDP:PyPyQ0GPyA=yABQ0HDDP:Q0JFNP;P7b4b8b9X06X:6X1mX;mPPP41H2W,44AX34XCC11X3=PY~Q0L[[^06^:6^1m^;mP2P111DiPiP^P8PhP0PfO8b3b5b6b7W?P2O1n200100000021100011000Rib=WAQ0=#:eP=P9Q0>P3CAR9Q0<PgQ09P5PUP>P2FgQ0?Pib=WA%:9eQ04p,8AL_errnoP5P2O2PRPePePSC8PlPnPkPoPpPCPuPv1m64Re?B4wR9?B4w?B4wPxPyPyPy%6RRi/TB%6SR=9>yBCWRBP:Py1SyBP:1ay5RBFNP;P7b4b8b9X06X1mPRP2P2PSC8RD11R4R~?X4SP1[RWP5[[^06^1mP2P11?E`P8P>O4b3b5b6b7b@W@PbePlPnPkPoPpPC%Zt,Q61Q6rRr,Ls'L/eq=djuPvQ0EPxPyPy1U6<R<1U6@R@5=yRsPyP{A>y@zRzDDP:PyA=y|<RtP:PyPtP:PyPy%6d9_6<RtQ03#ERb#65_6/T@A>y@tCW,SyCGFNP;P7b4b8b9X06X:6X1m1124Rt144OR`7P311c41H5dRd/HbP8P8PdC8P1[\}[[^06^:6^1mP21?E>R>,1XP>P^P?PUPfO6b3b5b6b7Q061?E3REPEQ05C8#:eO5XNTW<X2FQ0;PaP3O1PgP3O1RE53H\T[^2FQ089bIJRIA3HEV\T\Q^2FRdPaP4O1Ra=3HG\]^2FRb'<Q0:PHPgP4O1RgA3H2VX=HQ07P4P2O2PaP3P4PlPnPkPoPpPCPuPvQ0EPxPyPsP:Axys{CGP;P7b4b8b9X06X:6X1m1RY5\t^06^:6^1mP211XLRt?XLOPLP^P8O4b3b5b6b7PlPnPkPoPpPCQ0AQ0B,Lr'L/eq=djuPvQ0D?B3w9Bw4PxPyQ0@,U6Rw==y<P:PyA=y|wRwP:PyPwP:A>y<=R=9`y{,SyCGFNP;P7b4b8b9X06X:6X1m1142Q0KAX?5SP1[[\}[^06^:6^1mP211RLP^PLP8PUPfO6b3b5b6b7O3E]W<X2FPIePdPbPHQ0>P3O1PJP5O193H2X=HP0P3P4P2O3PEP5P3PlPnPkPoPpPCPuPvP9PxPyPyPyPy%6K/T@%6M9>y@CWPy%6N==y@PzDDP:PyPBPyA=yA@RAPzDDRzCGP;P7b4b8b9X06X1mPKP2142MPNP2P2POC8CC11X4=P3`R`[^06^1mP211^>P>P?O3b3b5b6b7PlPnPkPoPpPCPuPvPePxPyA=yi<Ri=`y=,SyR=P:P=CGP;P7b4b8b9X06P1\DPW[^06P2P>P8O2b3b5b6b7O3E]XGTXFQX2FPHPgA3H2GX=HPhP4P2O2PaP3P4PlPnPkPoPpPCPuPvP9PxPyPyPyPAPy%6ZRA,h@CoPy%6[==y@%6\R99>y@DDP:PzCGP;P7b4b8b9X06X1mPXP2142ZRZ142\R\9j[2CCP`[^06^1mP211^LPLP8O3b3b5b6b7PlPnPkPoPpPCPuPvPePxPyPyPyPBPy1h<ACoPyP{A>y<9DDP:Q0I9`yi,SyCGP;P7b4b8b9X06X1mX;mXBm1<3\9w4Z1<~8P1[[^06^1m^;m^BmP214LS11[LPtPLP8O5b3b5b6b7O3E]X<]X2FClClbEb>WMWOWKWPWLWJWIP4P2O2n2101000010121000000W>WHP4P2O2n2011000010121000000W>WTWSWRWQWDWCo"). Qed.


  (* [comment removed for export] *)
  Lemma sgn_tab : forallb (fun b => Bool.eqb (bv_lts (Z_to_bv 64 (bv_swrap 8 b)) (Z_to_bv 64 0)) (128 <=? b)%Z) (zseq 256) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "h01bp;2p;1p;3g00=9j2=Tg006Qj12Tg0076j13Tg02gmj25Tg00HTj24Tg02hTj3<Tg00kaj1;Tg02iAj27Tg02i^j26Tg02j5j18Tg02jlj39Tg00=Sj3:Tg00LTj10Tf0R0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00deR1g00eER2'=g00[@R3g00d@#2#2#2R4#2#2#2R5#3R6%34/50,46g00Zb,463<%25#;/70'6X03g00ee#1#1#1#1#1#1#1#1#839=:12do"). Qed.
  Lemma sgn_val : forall b, (0 <= b < 256)%Z -> bv_lts (Z_to_bv 64 (bv_swrap 8 b)) (Z_to_bv 64 0) = (128 <=? b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "h01Th11xh22Hah34__x1h41bh52Hbh67__arithh74__ffh86__sat3h96__sat4h:6__sat5h;8__varmaph<5__with=5lemmah>1yp;1p;2p;3p;<p;6p;4p;7p;8g006Qj12Tg00kaj15Tg00;2R0j23Tg00;Nj27Tg0076j1BTg02gmj2=Tg00HTj29Tg02hTj3:Tg02iAj2;Tg02i^j2?Tg02j5j1FTg02jlj3iTg02WMj3<Tg02kHj2[Tg02kaj3YTg02lRj3XTg00:RR1j1ATg02m5j2WTg00=9j26Tg00=mj3VTg00>Sj1UTg00Kol<OTg00?1j6NTg00DPj1>Tg01FWj2LTg0194j2KTg01G?j3JTg00l?j2ITg01Efj2HTg00lij2MTg00AHj1GTg008Yj1PTg00Ahj2QTg00Bdj1RTg00CBj1STg00Obj2@Tg00Cmj2hTg00UNj4ETg00Y6j7gTg00PEj1fTg00Z>j8eTg00EXj2aTg00F:j2`Tg00Ffj3\Tg00GEj4ZTg00Pgj4]Tg02mjj4^Tg02nEj3_Tg00=Sj3CTg00S0j2bTg00LTj10Tg00TOl<cTg00V9j7dTg00ZbR2f0R3'bp=1%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=4g00deR4g00eER57C3p=8g00[^R6g00[@R7P7P7P1P1f5f4R1f3R8f2R9f1R:P3M<cp=TP:g00]DR;g00]cR<P<g00^CR=P3g00_JFdp=D%13g00d@R>#2R?#2#2R@#2RA#2#2RB#2RC#2#5RD,33'7REg02na%BBRB%B@R@/=3,9B19B2RF3:%5CRC/;3'?X47RGg00ee#4#4#4#4#4#4#4#4RH#FRI5i7#8RJA<73IPGP:O1#8[^17RK,[JAYJK3W=AX7GIP3O2PKP3P8A<78I%11%AHRK,31'7[%18RG138KRJ'7RLA<71I[1WH8PL138DRI,7GPGPJPGPIp-0/6G9VGGP7P7P0P3X17RGP013:3#UX>7X17P8P81678PKPDPGPG%A3,67X16PHPD167DETM<OEN%5?RH%>?#>#2#5R?'L132H%1?1KH?R6,32[[%1HRGg01KTRKAJH?:UW2%16\K^2Gp,3sp0,IBRG%5ARA'H%1G%1A1MGA#1[[g00aZRA#G%PA1Q7:%R7%S7RAP;P<P<P=PAP;P<P<P=P71@72g00c21h7>R>CE,DAP7P>g00cY1@7DCE,DAFgR>%f<P>Ge1aA=P3P916451`39#8dA\72:CZb7b;b<X37%1:13:D'7\E^37P3f7f6O2b6b8b9b:C]PLeC^O21=@8,9B=:BF1;C8'?#81=@1,9B=:BFRF1;C1RC;_3AC4FCP3b0b0b0b0W5X47o"). Qed.

  (* [comment removed for export] *)
  Lemma sideW_frame : forall A vm M M' buf cap,
    sideW A vm M buf cap ->
    (forall x : word, M' x <> M x -> V2ReadLoop.in_win sp0 x \/ in_data x \/ (exists p n, live A p = Some n /\ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z)) ->
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
    pose proof (V2ReadLoop.round16_ge n) as Hrn.
    assert (Ea : at_ p (bv_unsigned x - bv_unsigned p) = x).
    { unfold at_. apply bv_eq. rewrite u_small by (pose proof (u64_range x); lia). lia. }
    destruct (Hbytesp (bv_unsigned x - bv_unsigned p)%Z ltac:(lia)) as (Ho & Hd & _).
    rewrite Ea in Ho, Hd.
    split; [exact Hd|]. split; [lia|].
    destruct (ai_owned_where A M vm x HI Ho) as [G|[[Gr _] _]]; [left; exact G | right; exact Gr]. }
  assert (Hsame : forall x : word,
            ~ (V2ReadLoop.in_win sp0 x \/ in_data x
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
        -- pose proof (AL_glob a G). unfold V2ReadLoop.in_win in W. lia.
        -- unfold V2ReadLoop.in_win in W. lia.
      * destruct (ai_owned_where A M vm a HI Ho) as [G|[[Gr _] _]].
        -- pose proof (AL_glob a G). unfold in_data in D. lia.
        -- pose proof (AL_grant a Gr). unfold in_data in D. lia.
      * exact (Hn p n Hp B).
    + intros a _ Ha. exact (Hgr a Ha).
    + intros a [Gr Gt] Ha. pose proof (AL_grant a Gr) as Hg.
      destruct (M a) as [b|] eqn:Ea; [discriminate|].
      exfalso. destruct (Hchg a ltac:(rewrite Ea; exact Ha)) as [W|[D|(p & n & Hp & B)]].
      * unfold V2ReadLoop.in_win in W. lia.
      * unfold in_data in D. lia.
      * exact (proj1 (Hblk a p n Hp B) Ea).
  - destruct HE as (Hab & Hcells & Hro). split; [|split].
    + intros a Ha. rewrite (Hsame a); [exact (Hab a Ha)|].
      intros [W|[D|(p & n & Hp & B)]]; [unfold V2ReadLoop.in_win in W; lia | unfold in_data in D; lia |].
      destruct (Hblk a p n Hp B) as (_ & Hlt & _). lia.
    + intros a Ha Hne. rewrite (Hsame a); [exact (Hcells a Ha Hne)|].
      intros [W|[D|(p & n & Hp & B)]]; [unfold V2ReadLoop.in_win in W; lia | unfold in_data in D; lia |].
      destruct (Hblk a p n Hp B) as (_ & _ & [G|Gr]); [pose proof (AL_glob a G) | pose proof (AL_grant a Gr)]; lia.
    + intros a Ha. rewrite (Hsame a); [exact (Hro a Ha)|].
      intros [W|[D|(p & n & Hp & B)]]; [unfold V2ReadLoop.in_win in W; lia | unfold in_data in D; lia |].
      destruct (Hblk a p n Hp B) as (_ & _ & [G|Gr]); [pose proof (AL_glob a G) | pose proof (AL_grant a Gr)]; lia.
Qed.

  Lemma sideW_block : forall A vm M buf cap E log,
    sideW A vm M buf cap -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    sideW A vm (mem_denot E M log) buf cap
    /\ forall x : word, ~ V2ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "p'0h07__arithh16__sat9h27__sat10h34__x1h41si001sh54__p1h64__ffh78__varmaph85__with97__sat11h:6__sat8h;2H7h<2H8h=1nh>1ph?6__sat5h@4__p2hA6__sat4hB6__sat3hC6__sat7hD2H5hE2H6hF4__p3hG6__sat6hH4__x2hI2H1hJ2H2hK2HahL1xhM1rhN2H3hO2H4hP1bhQ1AhR1EhS1HhT2H0hU3HE0hV2HShW4HloghX3HnehY3Hx1hZ3Hx2h[1Mh\3OUTh]3bufh^3caph_3logh`2vmi011gi021lp%0p%1p&0p;3p;2p;1p;5p;4p;6p;;p;9p;7p;8g00gRk30MTg00h[k30LTg00idk20<Tg006Qj15Tg0076j1aTg007Tj1sTg0087j1nTg008Yj1lTg00nMj5jTg01Y7k303Tg00=Sj3TTg02TCj2gTg00DPj1GTg00l?j23Tg00S0j22Tg02oWj2KTg019lj19Tg030Pj1LTg00kaj1VTg0194j2mTg01FWj2kTg00;2j20Tg01G?j3iTg01Efk204Tg00lik202Tg00AHj1wTg00Ahj2xTg00Bdj1}Tg00CBj1{Tg00Cmj2hTg00PEj1zTg01MZk30KTg00EXk20JTg00=9k20FTg00F:k20ETg00Ffk30CTg00GEk40@Tg003Bj6uTg016\k20?Tg00<\j2RTg00;Nj28Tg00X2j3tTg00ODk10>Tg00Obj2rTg00RMj3qTg019Qj4ZTg03;;j2pTg03;\j6WTg03<=j3oTg03<^m;0;Tg03=mj4^k309Tg03??j26Tg03?fj21Tg00J6k208Tg00H7k207Tg02Wdj2JTg00U4j2;Tg00BFk406Tg02Zlj2<Tg02Y:j3vTg03@Bk301Tg03AZm90=Tg00UNj4eTg00V9j7cTg00Z>j8]Tg01Unk300Tg01WRj3~Tg01a<k40ATg00Y6k70BTg00XRj6|Tg00YZk70DTg02ZHj6yTg033`R0k20GTg01:bk40HTg02Ynk30ITf0R1#5#5p=N%G1#Gp=:%51#5#5#5p=d%51#5#5#5#5#5#5#5p=M%51#5#5#Vp=Sg00ZbR2/21p==%51#Vp>05g00[@R3/r1p=If2R4g00]DR5g00]cR6P6g00^CR7P3f1R8g00c2P1Ceg00_JR9Fcp=Bf3R:P5P6P6P7P4P8P1G]p=fB00331p=\A~331p=[%G1#5p=D%51#Gp=YP3P3P8P1H0Ap=b12:41081'8p=4P4P5P6P6P7P3P8g00cYP1CeP9Fcp=QP4P5P6P6P7P8P1K0Bp=CP8P5P6P6P7P1E|p=_P4P5P6P6P7P8P1K0Dp=@P8P5P6P6P7P1Eyp=`f4R;P5P6P6P7P:P4P8P5P6P6P7P1EyG]p=H1248/81p=U1;81,;4p=E1081,84p=X10:41181+0Gp=7f6R<f5R=P;P:P4H0H;T8/81p=>1J31p=?1K;:%L41J81';';p=OP4P5P6P6P7P3P8g03BTP1CeP9Fcp=PP<P5P6P6P7P=P;P:P5P6P6P7P4P8P1G]G]p=FAv481:0I;:p=A%L41J81';p>0:p,2ALR5p,2CLR9p,3ASR:0M5960L5R9+0<g01?bg00d@R>#5R?#NR@#5RA#NRB#aRC#sRD%a@#s#nR@[g03C;g03DC#lP<P=P;P:P4Djg00deREg00eeRFg03ENRG<038g00eERH3T1g:Fp,3sp0RI5TDp,4SPloRJ%G>#:#:#:#:#:#:#:#d#M#M#M#SRK13CIRL'2p,4SPhi%5B#M#MRB#5#d#M#M#S,2L1KI1#9RM%L8#9RNf9ROf<RPf8RQPFPGP4P<PDPI%V?RR%G?RS#5#NRT#VRU'mRV13C1RW'2XPD1kRURX102RRY%=U102V[[RZ%=RR[g01KTR\AiRU8UWKRU%=V\\^K[R]%GS$05RS,kRR^%=S1mRSR_,02[\YRYAiRS8V\XK[RS%=_\\^K[R[%VARA-04LR\%=L%=A202LA#=[[RAg00aZR_#wR`%l_R_1x38Ra%}3Rb%{3Rc%IK1h3>Rd5Bc%z6R6%IR%aT60K3RT=BcdCf20Jc7R7P1P420FEH20E14=TEHdB0C328H0@RHb6b7b8X3312K112V8[^33P1PLPJO2b0bBbAb?bGbC1gOFRFP=Eu20?33RJ%\1RK#=RE%[1RR%VBRB,RVRe'2'8XMJRf%5>#N#D#D#M#SRg%5>#D#:#d#:#Y#N#SRh'bRi%5>#D#:#N#Y#Y#:#:#SRj%G>#D#:#N#D#Y#D#D#SRk'bRl%G>#D#:#Y#N#D#N#:#SRm%G>#D#:#D#M#SR>'bRn%wJRo5tJRp5tJRq%\iRr#=Rs%[iRt/2eRuP^PYPSP[P\PAP`P_&0>3RvPb1r32R2%IgRw5BcP7PHb6b7b8%=gP1b0bBbAb?PsePXPZPUP]P^PYPSP[P\PAP`P_PvPb%IhS00%IBRs9q3TRT5BcP7PHb6b7b812heP1b0bBbAb?bGbCPueCZPJPfPlPp%\lRu#=Rx%[lRy/2eRzP^PYPSP[P\PAP`P_PvPb%IjR{9Bc2P7PHb6b7b8%=jP1b0bBbAb?PxePXPZPUP]P^PYPSP[P\PAP`P_PvPb%IkS01=BcTP7PHb6b7b812keP1b0bBbAb?bGbCPzeCZPJPfPnPo%\nRz#=Rx%[nR|/2eR}P^PYPSP[P\PAP`P_PvPb%ImR~9Bc2P7PHb6b7b8%=mP1b0bBbAb?PxePXPZPUP]P^PYPSP[P\PAP`P_PvPb%I>S02=BcTP7PHb6b7b812>eP1b0bBbAb?bGbCP}eCZ1pJfEWEWEWg02bcRf,RV,2R,8EXMJ=oJGePDPI1RWf13C:REPEPWC4#9XPDP81RLf13C4RfPfPLC4#9ePFP=EuPJPKPEPEPRC4#9XMJRRPiPqP^PYPSP[P\PAp-0RqP`P_PaPbPcABcwdRiQ009QcdS035CcRKABc{dRFQ019QcdS045CcRW1_c:RV5@c5@cS05,`cP6PcPKDHP7PHb6b7b8X33W5101hS069Ug1101kS079Uj1R};E8g02fXRe[12g8RT?X8hPe[[^33^5qP1Pm13C<R]P]P>C4RUP]P;O3b0bBbAb?PrPfPfPtC4#9ePJPRPlPpP^PYPSP[P\PAP`P_PaPbPc1_c;Rp9@cW9@cVS08,`cP6PcPWDHP7PHb6b7b8X33X5qX@qAE8}4Pe[12j8Rl?X8kPe[[^33^5q^@qP1PUPgP]P]PhC4RUP]P;O4b0bBbAb?PuPfPfPyC4#9ePJPRPnPoP^PYPSP[P\PAP`P_PaPbPcABc~dRoQ029QcdS095CcRn9@cWRW9@cVS0:,`cP6PcPnDHP7PHb6b7b8X33X5q101>S0;9Um19E8}Pe[12m8R}?X8>Pe[[^33^5qP1PUP]P;O3b0bBbAb?PzPfPfP|C4#9e1pJREWEWEWAoJRGeN;0;WZWYXLDPOPPPQP4C^PPP4O15T@\N\M^LDPPf;RRf7RJf:RG<09<R|POPQDjPGf=RzPOP4C^PzP4O15T@\N\M^LDPPPRPGP|POPQP=PQPRPJP1C^PRP1O15T@#913C8R@1RLBR|'6P@P|P@P|C7P010f|11f|PIP:P:PD%n3RfP5P9fBRMP820831RNP@13C=RUPU207@1RnC4F>X=3#?X>DDOP110E|13C;S0</6gQ0<PgQ0<PgC7P010Ug11UgPIP<P<PDPfP5P9fERyP8PNP@13CQRQPQPnC4F>X=3#?X>DDOS0=P110]g13CJRu/6mPuPmPuPmC7P010Qm11QmPIPOPOPDPfP5P9fHS0>P8PNP@13CRRRPRPnC4F>X=3#?X>DDOS0?P113CORO/0m13CGRt/6jPtPjPtPjC7P010Rj11RjPIPPPPPDPfP5P9fKS0@P8PNP@f>Rr,3CRZPZPnC4F>X=3#?X>DDOS0AP113CPRX/0j1KIzS0B%LzS0CPfP5P9fLP8PNP@f?S0D,3CRxPxPnC4F>X=3#?X>D,JDS0E';S0F';PPPrPzP^PYPSP[P\PAP`P_P31x34P8PvH06S0GPbPc1h3?R?Aq3dsS0H5QcP6PcQ0H=Bc?S0I=CcpDHP7PHb6b7b8X33XH3X5qS0J1R1B,081R8BS0K?U4:Pe[[^33^H3^5qS0LP1fAS0M,3CRs/0LPsPLPzO4b0b:b1b2Q0B#9eP^PYPSP[P\PAP`P_PaPbPcAQcdwRvP6PcACciVACcFp1_c=S0N9CcoS0O5@cS0P5@cDHP7PHb6b7b8X33X5qX@qXFqS0Q101g18T418l:18};3EPe[[^33^5q^@q^FqS0RP110s>S0S10skS0T10shPsPGO5b0b:b1b2Q0C#9eO3O1'<W;P1O111Xj13CzR}/6kP}PkP}PkC7P010Zk11ZkPIQ0DQ0DPDPfP5P9fNP8PNP@PsPsPnC4F>X=3#?X>DDOS0UP110xkf@Rl,KIS0V%LlRTPfP5P9fOP8PNP@13CMRoPoPnC4F>X=3#?X>D,JDS0W';S0XPTQ0WP^PYPSP[P\PAP`P_PaPbPcAPcd{S0YP6PcPvP6Q05FFP7PHb6b7b8X33X5qS0Z111j108gRFPgP4P4PhC4RiPjP4P4PkC4Rr;E:S0[[[^33^5qS0\P1fDS0],3CRP10P>S0^5UmPPPJPzO4b0b1b2b9PTeDAW<P1O111xkQ0VQ0X';S0_Q0DQ0MPlP^PYPSP[P\PAQ0JQ0LP110PLPPPLPlO4b0S0`b1b2b9Q0V#9S0aeP^PYPSP[P\PAQ0QQ0RP1Q0^10PkS0b10PhS0cPPPzO5b0R2b1b2b9%9TS0deO3O1'<W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111Om16t>PtP>PtP>C7P010R>11R>Q0AP110X>Q0BQ0FQ0CQ0EP^PYPSP[P\PAP`P_PaPbPcAPcd~S0eP6PcPvP6A@cKWFFP7PHb6b7b8X33S0f111mPmP4P4P>C49Eir\F[^33S0gP1PsPJPGO3b0bCb:b1Q0CeDAWEP1O111X>16}jS0hP}PjP}PjC7S0iP010ZjS0j11ZjS0kQ0UP110xjS0lQ0_Q0DQ0MPlP^PYPSP[P\PAQ0`b:b1b2Q0aeS0`P^PYPSP[P\PAP2b:b1b2Q0deO3O1'<W;P1O111xjS0m13ClR2/6kS0nP2PkP2PkC7S0oP0Q0T11skS0pPIPMPMPDPfP5P9fQP8PNP@PPPPPnC4F>X=3#?X>DDOS0qP110okS0rfCRF,KIRr%LFRiPfP5P9fRP8PNP@13CyRWPWPnC4F>X=3#?X>D,JDS0s';S0tPiQ0sP^PYPSP[P\PAQ0fQ0gP1fGS0u,3CRKPzPlO3b0b1b2b9PieDAW<P1O111okS0vQ0t,;rRvPMQ0]PFP^PYPSP[P\PAQ0JQ0LP110KLPKPLPFO4b0S0wb1b2b9%9rS0xeS0yP^PYPSP[P\PAQ0QQ0RP110K>S0z10KkS0{10KhS0|PKPlO5b0b1b2b9%9iS0}eO3O1'<W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WIP1O111]g16uhPuPhPuPhC7P010Qh11QhQ0?P110Oh1KIG%LGS0~PfP5P9fIS10P8PNP@PXPXPnC4F>X=3#?X>D,JDS11';Q0~Q11P^PYPSP[P\PAP`P_PaPbPcQ03P6PcAPcdwS11P6Q05FFP7PHb6b7b8X33X5qS05Q06118gQ0[[[^33^5qS06P110Z>S0[9UmZPZP;PJO4b0bAb?bGQ0~eDAWJP1O111Oh16tmS0~PtPmPtPmC7S12P010RmS1311RmS14Q0AP110XmS15Q0hQ0iP0Q0jQ0kQ0UP1Q0lQ0_Q0DQ0MPlQ0`P^PYPSP[P\PAP`P_PaPbPcAQcd{P6PcAQcd~R~P6PcQ009PcdS00P6PcQ039CcVRVQ0P5@cDHFFP7PHb6b7b8X33X5qX@qXFqS0P101j108mS03114hR{AX;:hRw12j:S0`/8=12m:S16/8<S173EPe[[[[^33^5q^@q^FqS18P1Q0^Q0b12gPS19PPP;PJPGO7b0b:b1b2Q0deO3O1'<W;P1O1Q0mQ0nQ0oP0Q0TQ0pQ0qP1Q0rPrQ0tPiQ0sP^PYPSP[P\PAP`P_PaPbPcQ04P6PcQ0YP6PcP~P6PcQ11P6Q08FFFFP7PHb6b7b8X33X5qX@qS08Q07118j104m11:gPjP;P;PkC4=E=<[[[[^33^5q^@qS0YP112mKS1:Q0z'8S1;12gKS1<Q0|'8S1=PKP;PJPGPlO7b0b1b2b9PieDAW<P1O1Q0vPMQ0]PFQ0yP^PYPSP[P\PAP`P_PaPbPcQ019PcdP6PcP~P6PcQ00P6PcQ049CcpS01Q0O5@c9@cVDHFFP7PHb6b7b8X33X5qX@qXFqS0O111kQ0310:kR~,8=S0yQ175EwPe[\{[[^33^5q^@q^FqS03P1Q0z12jKS17Q1<PKP;PGPzO7b0b1b2b9Q0}eO3O1,<vW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111XmS1>16}>S1?P}P>P}P>C7S1@P0Q0[11Z>S1AQ0UP110x>S1BQ0VQ0XPTQ0WP^PYPSP[P\PAP`P_PaPbPcQ09P6PcQ0eP6PcQ11P6Q0:FFS0:CfP7PHb6b7b8X33X5qS11Q0;118mR=114gQ0`/8~Q1610:>R~'85E;[[S16[^33^5qS0;P1Q19Q0c'8PPP;PJPzO5b0bCb:b1PTeDAWEP1O111x>S19162jS0`P2PjP2PjC7S1CP010sjS1D11sjS1EQ0qP110ojS1FPMQ0]PFP^PYPSP[P\PAQ0wb:b1b2Q0xeP^PYPSP[P\PAP`P_PaPbPcQ029PcdP6PcQ0eP6PcQ00P6PcQ01Q0NQ095Cc5@c9@cVDHFFP7PHb6b7b8X33X5qX@qXFqS01111>Q0y18<~5EwPe[\{\=[^33^5q^@q^FqS0yP1Q1:Q17Q1<PKPJPGPzO7b0b:b1b2Q0}eO3O1,<vW;P1O111ojS1713CFR=/6kS1:P=PkP=PkC7S0NP0Q0b11PkS09PIPyPyPDPfP5P9fTP8PNP@PKPKPnC4F>X=3#?X>DDOS00P110WkS0efFR{,KIRw%L{R~PfP5P9fUP8PNP@Q0>,3CS02Q02PnC4F>X=3#?X>D,JDS0w';S1GP~Q0wP^PYPSP[P\PAP`P_PaPbPcQ04P6Q0:CfP7PHb6b7b8X33X5qS0:Q07Q16[^33^5qS07P1fJS16,3CRa,2gS0410ahS1H'8S1IPaP;PzPFO5b0b1b2b9P~eDAW<P1O111WkS1JQ1G,;wRVPyQ0uP{P^PYPSP[P\PAQ0JQ0LP110aLPaPLP{O4b0b1b2b9%9wS0LeP^PYPSP[P\PAQ01Q0yP112maS0J12jaS1KQ04PaPGPzPlO7b0b1b2b9%9~S1LeO3O1'<W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WJP1O1n200110000021110211101b4WIP1O1n200110000021110211101b4WNP1O111E|Q0</6LQ0<PLQ0<PLC7P010UL11ULQ0=P110]L1KIJRUPfP5P9P{P8PNP@POPOPnC4F>X=3#?X>D:0:JDP^PYPSP[P\PAP`P_Q0GPbPcAQc?dREP6PcQ0H9Pc?P6Q0I=CcEFFP7PHb6b7b8X33XH31081Q0K,141R4BP:P:P4C4[[^33^H3P1PRPLP;PJO4b0b?bGbCPUe3vWOP1O111]L16ugPuPgPuPgC7P010Qg11QgQ0?P110OgQ0~Q12P0Q13Q14Q0AP1Q15Q0hQ0iP0Q0jQ0kQ0UP1Q0lQ0_Q0DQ0MPlP^PYPSP[P\PAP`P_Q0GPbPcAPc?dP6PcACcpEDHP7PHb6b7b8X33XH3X5qRH1181AX:48Pe[[^33^H3^5qRqP112|PPPPLPzO4b0b:b1b2Q0aeP^PYPSP[P\PAQ0QQ0RP1Q0^Q0bQ0cPPPGO5b0b:b1b2Q0deO3O1'<W;P1O1Q0mQ0nQ0oP0Q0TQ0pQ0qP1Q0rPrQ0tPiQ0sP^PYPSP[P\PAQ0ZQ0\P1Q1;PKPJPzO4b0b1b2b9PieDAW<P1O1Q0vPMQ0]PFP^PYPSP[P\PAPHPqP112|KPKPLPlO4b0Reb1b2b9Q0xeP^PYPSP[P\PAQ0QQ0RP1Q0zQ0{Q0|PKPzO5b0R:b1b2b9Q0}eO3O1,<vW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O1Q1>Q1?Q1@P0Q0[Q1AQ0UP1Q1BQ0VQ0XPTQ0WP^PYPSP[P\PAQ0fQ0gP1PPPJPGO3b0bCb:b1PTeDAWEP1O1Q19Q0`Q1CP0Q1DQ1EQ0qP1Q1FPMQ0]PFP^PYPSP[P\PAPeb:b1b2Q0xeReP^PYPSP[P\PAP:b:b1b2Q0}eO3O1,<vW;P1O1Q17Q1:Q0NP0Q0bQ09Q00P1Q0ePwQ1GP~Q0wP^PYPSP[P\PAQ0fQ0gP1PaPzPlO3b0b1b2b9P~eDAW<P1O1Q1JPyQ0uP{P^PYPSP[P\PAPHPqP112|aPaPLPFO4b0R:b1b2b9Q0LeRTP^PYPSP[P\PAQ0QQ0RP110a>R410akQ1HPaPlO5b0b1b2b9Q1LeO3O1,<VW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WIP1O111Og16thPtPhPtPhC7P010Rh11RhQ0AP110XhQ0BQ0FQ0CQ0EP^PYPSP[P\PAQ05Q06P1Q0S9UmsPsP;PJO4b0b?bGbCQ0CeDAWJP1O111Xh16}mP}PmP}PmC7P010Zm11ZmQ0UP110xmQ0`Q1CP0Q1DQ1EQ0qP1Q1FPMQ0]PFPeP^PYPSP[P\PAQ0PQ18P1Q0zQ0{Q1<PKP;PJPGO7b0b:b1b2Q0}eO3O1,<vW;P1O1Q17Q1:Q0NP0Q0bQ09Q00P1Q0ePwQ1GP~Q0wP^PYPSP[P\PAQ08Q0YP1Q0J/84Q1IPaP;PJPGPlO7b0b1b2b9P~eDAW<P1O1Q1JPyQ0uP{PTP^PYPSP[P\PAQ0OQ03P1P4Q1KQ04PaP;PGPzO7b0b1b2b9Q1LeO3O1,<VW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111xm162>P2P>P2P>C7P0Q0S11s>Q0qP110o>PrQ0tPiQ0sP^PYPSP[P\PAQ11Q0;P1Q1=PKP;PJPzO5b0bCb:b1PieDAWEP1O111o>16=jP=PjP=PjC7P010Pj11PjQ00P110WjPyQ0uP{P^PYPSP[P\PAP:b:b1b2Q0LeP^PYPSP[P\PAQ01Q0yP1Q0JQ1KQ04PaPJPGPzO7b0b:b1b2Q1LeO3O1,<VW;P1O111Wj13C{RW/6kPWPkPWPkC7P0Q0{11KkPIQ0>Q0>PDPfP5P9fWP8PNP@PaPaPnC4F>X=3#?X>DDOP1Q02/0kQ10,KIRIQ10#LRaPfP5P9fXP8PNP@Q0@,3CR@P@PnC4F>X=3#?X>D,JDRn';R@PaPnP^PYPSP[P\PAQ0:Q07P1fM,3CRC,2gRg?XChPCP;PzPFO5b0b1b2b9PaeDAW<P1O1Q02/1k1;I@Q0>Q16Q10P^PYPSP[P\PAPHPqP112|CPCPLP{O4b0b1b2b9%9IeP^PYPSP[P\PAQ01Q0yP112mC12jCPgPCPGPzPlO7b0b1b2b9%9aeO3O1'<W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WJP1O1n200110000021110211101b4WIP1O1n200110000021110211101b4WOP1O1n200110000021110211101b4WNP1O1n200110000021110211101b4WXXLDB01JG<N90=P1CZb\bTbSWUWWWVW_WRX^3X]DW[W`WQo"). Qed.

  (* [comment removed for export] *)
  Lemma log_win_wdl : forall log, log_win_b 0 log = true -> log_wdl_b 0 DATA_RS log = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRun ()) ["TRun"] "p'0h01Hh12Heh22H0h31xh42b1h52b2h62opi002oph71ni011nh81bi021bh91ei031eh:5lemmah;2sxi042sxh<7e_addr0h=5e_vali055e_valh>7e_widthi067e_widthh?1ii071ih@1ki081khA2k0hB2loi092lohC3loghD1vhE1whF1yhG1zi0:1zi0;1ai0<6a_basei0=5a_offi0>6e_addri0?1sp;1p;2p;3p;7p;4p;6g008Yj1TTg03FHj2STg03GOj2Mj3JTg02jlj3ATg02kHR0j2ITg03HXj2OTg03I6j7NTg02lRj3HTg03IXj1Kj2GTg02kaj3RTg03Jaj37Tg01[Gj1?Tg03Klj21Tg02Zlj26Tg01Z>j1CTg01cej3=Tg03M6j3>Tg03N?j3@Tg03OHj3<Tg01b\j4:Tg03PQj4;Tg01Y7j3LTg00=Sj39Tg02WMj3FTg00<@j6PTg00deR1f0R2g00eER339p=8g03DCR4f1R5;F2p=Eg00eeR6g03ENR7;J2=913p=D1G62=913p=Bf3R8f2R9;75=F42p=Q1189?752,G6=913p=2f4R:/18?795=F42p=01189?7529J67=913p=3A7952,G6p=5P1P9P5g03:_P3P2EPp=4%T41S62#81M67R3=A45#81E29R;%D5R<[^34'Ip-0R=P01O25XF=X3=g03QZAA439#81E28R0P<[^34P2FNW:AH435%K6R3=A45#8%B5R<\;^34R;'IAA439#8P<\0^34;R2W:AH435P2O2P;P9P5P2O2P<P4%B2f7R<,E5%D9]1]0P9g03RPR;P;g00[^R;g02J7R3A7952#BP8P9P5f=R>CQA7:89#D]1]0]=]>P2g00[@R?P8P9P5P2C2P:P8P9P5f@D0P3P2f5R@P:P8C2P5f6RAP@P:fCD0P9P<PAP@C3]1]0P@%?2PAP@P:C2%?5P<PAP@fDRBD0%?9f8RC'1?5<AP1P=P2g02fXR=g01KTn0110200020000X91RD;45P=%?8f9REPCP<C3/62b2W1W0XG?P2O1%C2PAP@P:C2%C5P<PAP@PBD0P5%C9PCP<PAC3eW1W0X7;P2O1g03SZR<A=952f:RBPEPCC2A=895f;RFPBPEfHRGD0A=:89f<RH'1?5FB?4D5P=A=@:8P>PHPFC3/62b2W1W0X53X43W6P9P5P2O3A>952PBPEPCC2A>895PFPBPEPGD0A>:89/1H?5FB?4D5P=A>@:8P>PHPFC3/62b2W1W0X53X43X6<P9P5P2O3g03TFR<A@952PBPEPCC2A@895PFPBPEPGD0A@:89/1H?5FB?4D5P=A@@:8P>PHPFC3/62b2W1W0X53X43W6P9P5P2O3A<952PBPEPCC2A<895PFPBPEPGD0A<:89/1H?5FB?4D5P=A<@:8P>PHPFC3/62b2W1W0X53X43X6<P9P5P2O3P8P9P5P2C:PHPFPBC2P:P8P9P5C:P>PHPFfJR<D0P@P:P8P9C:f>RG'1?5>H?4D5P=PAP@P:P8C:f?REPGP>C3/62b2W1W0X83X7;XB;X;1P8P9P5P2O4P8P9P5P2C;PHPFPBC2P:P8P9P5C;P>PHPFP<D0P@P:P8P9C;/1G?5>H?4D5P=PAP@P:P8C;PEPGP>C3/62b2W1W0X7;X??XA;X;1P8P9P5P2O4n0110300081010:101013010010;1023010010;1023010010;1023010010;1024010410910110340104108107101P5P2O2W1W0XD3XE;W@X83P5P2O2n0110?00012110<10=W<P9P5P2O3n0110?00013110>106105P2P5O2b0X10X94b0O2AL675#8eW0WCo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition slotsM (vals : list word) (buf : word) : Prop := slotsR vals buf /\ vals_ev vals 13 = Z_to_bv 64 calls.

  Definition at_tm (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 46%nat -> slotsM vals buf ->
      regs_ok (ENV vals) sr_TM R -> know_ok RSEGS (ENV vals) M kn_T ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data -> (L < cap)%Z -> (6 + cfg <= L)%Z -> (0 < paylen)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3c370) M (seg_rom RSEGS)) (model2 vm)) K.

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
    unfold model2, V2ReadLoop.model2.
    assert (R10 : getr R 10 = Z_to_bv 64 paylen) by (regv HR (10 : reg); cbn [edenot ev ENV V2Open.ENV]; rewrite P9; reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x17b9c) by (regv HR (1 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x56270) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V2Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    assert (EQcfg : mkst R (Z_to_bv 64 0x3c370) M (seg_rom RSEGS) = mkst R al_malloc_pc M al_rom) by (rewrite AL_malloc, AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC V2Open.fds0 vm stdin0 fs0 None (Some tid) None).
    destruct tm_itin as (I2 & R2s & VLKT & VLS2 & VLK2 & SR3 & KN3 & VLK3 & I3 & IX & S19).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (alloc_margin_le paylen) as HMG. pose proof calls_rng as Hcalls.
    pose proof (need_lo FUZZ_CALLS FUZZ_BMAX j cap HFC0 ltac:(clear -HFB0; lia) Hj10 ltac:(change (2 ^ 26)%Z with 67108864%Z; clear -Hcap26 Hc0; lia))
      as (HNK & HNB).
    eapply (ai_malloc_sure fx0 A M md R paylen (need_k FUZZ_CALLS j) (need_b FUZZ_BMAX j cap)
              (Z_to_bv 64 0x17b9c) sp0 [a0s; path] envv K HI).
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
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V2Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
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
        - cbn [kentry_ok edenot ev ENV V2Open.ENV]. rewrite A56. lia.
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
        assert (B1 : getr Rc 1 = Z_to_bv 64 0x17bb0) by (regv HR (1 : reg); reflexivity);
        assert (B10 : getr Rc 10 = res) by (regv HR (10 : reg); cbn [edenot ev ENV V2Open.ENV]; exact A56);
        assert (B11 : getr Rc 11 = Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) by (regv HR (11 : reg); cbn [edenot ev ENV V2Open.ENV]; rewrite Q12; reflexivity);
        assert (B12 : getr Rc 12 = Z_to_bv 64 paylen) by (regv HR (12 : reg); cbn [edenot ev ENV V2Open.ENV]; rewrite Q9; reflexivity);
        destruct (ref_memcpy m' res (Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) paylen payload (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x17bb0)
                    ltac:(apply ret_ok_even; reflexivity) B1 B10 B11 B12) as (Rm & Hms & Hkeep);
        clear B1 B10 B11 B12
      end.
      replace (Z_to_bv 64 275580) with (0x4347c : word) by (apply bv_eq; reflexivity).
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
        pose proof (know_ok_call RSEGS (ENV vals2) m' M2 [(0x1000, 0x10000)%Z] 0 0 IHI 0x45000) as KC;
        specialize (KC ltac:(cbn [ev ENV V2Open.ENV]; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
        specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HK3; clear KC
      end.
      assert (OUT2t : forall x : word, ~ touched (ENV vals2) [(0x1000, 0x10000)%Z] 0 0 IHI (bv_unsigned x) -> M2 x = m' x).
      { intros x Hnt. apply OUT2. unfold touched, IHI, WIN in Hnt. cbn [ev ENV V2Open.ENV] in Hnt. rewrite Q0 in Hnt. intros Hx. apply Hnt.
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
      + unfold slotsT, V2Hdr.slotsR. rewrite !vals_ev_map by (cbn; lia). cbn [nth tl_rvlm rvl18 app tl tm_sr3 edenot ev ENV V2Open.ENV].
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
    unfold model2, V2ReadLoop.model2. unfold tr_shape.
    assert (CZ : forall b, bv_eqb (Z_to_bv 64 cfg) (Z_to_bv 64 0) = b <-> (if b then cfg = 0 else cfg <> 0)%Z).
    { intros b. unfold bv_eqb. rewrite !u_small by lia. destruct b; [apply Z.eqb_eq | apply Z.eqb_neq]. }
    assert (PZ : forall b, bv_eqb (Z_to_bv 64 paylen) (Z_to_bv 64 0) = b <-> (if b then paylen = 0 else paylen <> 0)%Z).
    { intros b. unfold bv_eqb. rewrite !u_small by lia. destruct b; [apply Z.eqb_eq | apply Z.eqb_neq]. }
    assert (GO_M : forall rvl Rx Mx, (0 < paylen)%Z ->
      length rvl = 46%nat ->
      (forall i, (i < 13)%nat -> nth i rvl (ELit 0) = EVar i) -> edenot (ENV vals) (nth 13 rvl (ELit 0)) = Z_to_bv 64 calls ->
      regs_ok (ENV (map (edenot (ENV vals)) rvl)) sr_TM Rx -> know_ok RSEGS (ENV (map (edenot (ENV vals)) rvl)) Mx kn_T ->
      side A vm Mx buf cap j -> bytes_at Mx (bv_unsigned buf) data ->
      realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x3c370) Mx (seg_rom RSEGS)) (mkModelC V2Open.fds0 vm stdin0 fs0 None (Some tid) None)) K).
    { intros rvl Rx Mx Hp Hlen Hid H13 HRx HKx HSx HBx.
      apply (tm_step K j buf cap HTL A vm (map (edenot (ENV vals)) rvl) Rx Mx); try assumption.
      - rewrite length_map. exact Hlen.
      - split; [repeat split|]; rewrite vals_ev_map by lia; rewrite ?Hid by lia; cbn [edenot ev ENV V2Open.ENV]; try assumption. }
    assert (GO_L : forall rvl Rx Mx, paylen = 0%Z ->
      length rvl = 50%nat ->
      (forall i, (i < 13)%nat -> nth i rvl (ELit 0) = EVar i) -> edenot (ENV vals) (nth 13 rvl (ELit 0)) = Z_to_bv 64 calls ->
      nth 14 rvl (ELit 0) = ELit A_EMPTY -> nth 15 rvl (ELit 0) = ELit 0 -> edenot (ENV vals) (nth 16 rvl (ELit 0)) = Z_to_bv 64 calls ->
      regs_ok (ENV (map (edenot (ENV vals)) rvl)) sr_TL Rx -> know_ok RSEGS (ENV (map (edenot (ENV vals)) rvl)) Mx kn_TL ->
      side A vm Mx buf cap j -> bytes_at Mx (bv_unsigned buf) data ->
      realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x17bf0) Mx (seg_rom RSEGS)) (mkModelC V2Open.fds0 vm stdin0 fs0 None (Some tid) None)) K).
    { intros rvl Rx Mx Hp Hlen Hid H13 H14 H15 H16 HRx HKx HSx HBx.
      apply (HTL fx0 A vm (map (edenot (ENV vals)) rvl) Rx Mx (Z_to_bv 64 A_EMPTY) (Z_to_bv 64 0) fp_frm_zero_fx0); try assumption.
      - rewrite length_map. exact Hlen.
      - split; [repeat split|]; rewrite ?vals_ev_map by lia; rewrite ?Hid by lia; rewrite ?H14, ?H15; cbn [edenot ev ENV V2Open.ENV]; try assumption; try reflexivity.
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
      cbn [sc_denot branch_taken edenot ev V2Open.ENV]; rewrite ?P8', ?P9'; unfold bv_eqb; rewrite !u_small by lia;
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
        (intros i Hi; rewrite OUT1; [apply HB; exact Hi | unfold V2ReadLoop.in_win; rewrite u_small by lia; lia
                                                   | unfold V2ReadLoop.in_data; rewrite u_small by lia; lia]));
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
