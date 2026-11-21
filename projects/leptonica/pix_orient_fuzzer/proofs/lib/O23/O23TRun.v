(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the reserved ledger: vm_resv instead of vm_reserved; the recorded proofs of tm_step and trun_entry, made over the old 8 MiB launch stack window, and of side_W, bufW_facts and sideW_frame, made over the old vm_ok and sideW with vm_reserved, replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibKnowXfer LibTail SymCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib Frame.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec Room.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23ExitBase O23StdioDefs O23Exit O23Startup O23StartupDefs O23StartupFacts O23MainEntry O23LibStdioCall O23OpenFail_defs O23OpenFail_tail O23OpenFail_tail2 O23Open_defs O23Open O23Oom_defs O23Oom O23MemPreds O23Malloc65536 O23DirRead_defs O23MemcpyBase O23Memcpy O23ReadLoop_defs O23ReadLoop O23Grow O23Hdr_defs O23Hdr O23FuzzIface O23TRun_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac FPSteps.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23TRun () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3O23;O23MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib6Common9CliDriver8SymDrive?nth_map_seq_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop9buf_factsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun5sideWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop5al_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop5vm_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23>O23Malloc655366env_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic3and01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase<ai_live_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7round16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop:round16_geC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib3O23>O23Malloc65536;live_big_loC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3O236O23Hdr7cfg_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib3O237O23TRun3cfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun1LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun6paylenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun7payloadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr6b2_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr6hdr_b2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib3O237O23TRun5callsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3O23@O23OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib6Common9CliDriver<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver<RefPrintfLib:alu_and3_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7div_1_rC56Stdlib6ZArith6BinInt1Z7pow_0_rC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics5Riscv3Sem5alu64I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs4kn_TC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5kn_TLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7calls_xC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib3O23<O23TRun_defs7t_itin1C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5t_r1aC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib3O23<O23TRun_defs5t_r1cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C59OSSVerify5KrLib3O23<O23TRun_defs5t_r1bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5t_r1dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tm_rvlaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6t_sr1aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5sr_TMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5t_kn1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tm_rvlcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6t_sr1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23Hdr_defs4kn_RC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tl_rvlbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6t_sr1bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5sr_TLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tl_rvldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6t_sr1dC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23>O23Malloc65536<ownedA_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00c59OSSVerify5KrLib3O237O23TRun=ownedA_rangeTC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3O23;O23ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs9kn_acallTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23Oom_defs4GLOBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3O237O23Open9above_sp0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3lebC46Stdlib4Bool4Bool3eqbC59OSSVerify5KrLib3O23;O23Hdr_defs4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC59OSSVerify5KrLib3O236O23Hdr7in_zseqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C46Stdlib4Bool4Bool8eqb_propc59OSSVerify5KrLib3O237O23TRun7sgn_tabC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop6in_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun:bufW_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib6Common8Mallocng9AllocBase9grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib6Common8Mallocng9AllocBase8ai_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init5Logic4True01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_wdlC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S?mem_denot_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun;sideW_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop7DATA_RSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall;entry_wdl_bC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C69OSSVerify5KrLib6Common9CliDriver7SymCall;entry_win_bC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00c59OSSVerify5KrLib3O237O23TRun6at_tl0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun6slotsMC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lc59OSSVerify5KrLib3O237O23TRun<paylen_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_malloc_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIfaceAfuzz_margin_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface;fuzz_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure?alloc_margin_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure<alloc_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room7need_loC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsc59OSSVerify5KrLib3O237O23TRun=env_ok_allocTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room8fuzz_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room;fuzz_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:aroom_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun5roomTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23>O23Malloc655367live_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun>bytes_at_skipnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase@ai_live_disjointC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib5Lists7ListDef3seqC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRunAknow_after_allocTC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Grow<bytes_at_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC59OSSVerify5KrLib6Common7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O239O23Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23>O23Malloc65536:live_whereC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes?pair_equal_specC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3O23;O23ReadLoop;vals_ev_mapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun6slotsTC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer2rvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4emapC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer<regs_ok_xferC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXferDknow_ok_xfer_entailsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure>ai_malloc_sureC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun5at_tmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open4fds0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6tm_sr2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6STOPSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tl_rvlmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tm_kn3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6tm_srMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6tm_knMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3O23<O23TRun_defs7tm_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5tm_r2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6tm_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tm_sr3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5tm_r3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6tm_sr3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6tm_kn3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIfaceAfuzz_calls_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun9calls_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure9ROOM_NMAXC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib3O23?O23MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23MallocLayout6LS17okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tn_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tn_kn1iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FPSteps?fp_frm_zero_fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface7A_EMPTYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr6slotsRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop4sideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop6model2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun6side_WC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib3O237O23TRun7tm_stepC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib3O23;O23ReadLoop>side_block_wdlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun;calls_x_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23TRun8tr_shapeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib3O23;O23Hdr_defs4sr_RC1?~~~~~~~~~~~~~~~".
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
      as Ktid; cbn [kentry_ok edenot ev O23Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x123d08), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev O23Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev O23Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev O23Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev O23Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev O23Open.ENV] in Ktid |- *; lia
      | cbn [ev O23Open.ENV] in Ktid |- *; lia
      | lit_u; change (1195272 - 168)%Z with 0x123c60%Z;
        let Htc := fresh "Htc" in
        krd HK 0x123c60%Z 4%nat Htc; rewrite Htc; cbn [ev O23Open.ENV] in Ktid |- *;
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
ltac2:(KReplay.run1 (kr_t_O23TRun ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0g0022R0p4p710p8p1002Rp4p70g003BR1p4p710R2p8p1003`p4p70P2p8p1004Np4p7210P2p8p1005:p4p70P2p8g0060R3p4p710P2p8g006Qj1HTg0076j1wTg007Tj1gTg0087j1~Tg008Yj1uTg0099j3qTg00:6j3KTP0j25Tg00:TR0j10Tg00;4R2j23Tg00;Pj26Tg00;kj2YTP3k30ITg00<Bj6sTg00<^j28Tg00=;j2>Tg00=Uj37j1nTg00=oj3_Tg00>Uk10>Tg00?3j6^Tg00?\j4\Tg00@Cj1TTg00@hj2PTg00AJj1|Tg00Ajj2XTg00BHj4LTg00Bfj1yTg00CDj1xTg00Coj2JTg00DRj1cTg00E7j3QTg00EZk20HTg00F<k20GTg00Fhk30FTg00GGj4rTg00H9R3j21Tg00HVj2aTg00I<R4j1VTg00I\j4Nj3pj2ok10ATg00J8j2Wk10DTg00JZk20ETg00K1k20@Tg00KTk30?Tg00L1l<lTg00LVj1CTg00M5k10<Tg00MSk20;Tg00N4j3iTg00N]j2hTg00OFk108Tg00Odk205Tg00PGk104Tg00Pik403Tg00QTj8RTg00R1k502TP1j6eTg00ROk307Tg00S2j2tTg00SNk200Tg00SklBkTg00TQl<dTg00U6j2}Tg00UPj4UTg00V;j7[Tg00V_j3`Tg00WHj2MTg00X4j3ITg00XTk60BTg00Y8k70CTg00Y\j7{Tg00Z@j8zTg00ZdR1f0R5'tp=920015p=2g00[BR6/>5p=;g00[`R7P7P7P6P6P6g00\?P0P0P0f6R8g00\_f5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P0P0P9P:P;P<P=P5M<dp=bP6P6P2f7R>P2P8P9P:P;P<P=P5M<lp=Z1315p==1t51p=<A7651p=BA76;<,6:16=5'}p=?P<g00]FR2g00]eR?P?g00^ER@P6P=g00^eRAP5CUg00_LRBF[p=vA76=5p=OP6P7P6P6P4P:P0P;g00_lP<P=P5M<dp=mP7P7P7P6P6P6g00`YP0P0P0P3g00a9P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00a\R3g00bHR4,M=;I5p>0:A`6<=/M4=I35p=E1M<41M=4=I355I3p>09P=P2P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P2P?P?P@P<P=P2P?P?P@P5PBF[K0Cp=:P6P=g00c4P5CUp=FP=P2P?P?P@P5PBF[p=DP<P2P?P?P@P=P5F{p=]P6P=g00c[P5CUp=SP;P2P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI3=59I3<p>06g00dBR4#HR2#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P1%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|3RV%u3R3P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J62R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00dgR_g00eGR`'>Ra20G5<=7_`dB0F61=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA1RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P0%n6%0=R0/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P18%=8%28RiP8%<8%BiD?%2>P611cNRc,P1%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P1%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00egRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP3P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20561R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c2,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P1K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP3P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;0AKD=<5q:eWGXM7WKXI6WHo"). Qed.

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
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0xfa4b4.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0xfa374.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x123d20.
  Hypothesis AL_glob : forall a, al_globals a -> (0x144020 <= bv_unsigned a < 0x1443d0)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x123c7c <= bv_unsigned a < 0x123c80)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x145000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := O23Open.ENV a0s path.
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
    intros A vm M buf cap j HS. pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & _).
    destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    split; [exact HI|]. split; [exact Hl|]. split; [exact Hvl|]. split; [exact Htop|]. split; [exact Hisp|]. split; [exact Hres|].
    split; [exact HE | exact Hc0].
  Qed.

  Lemma bufW_facts : forall A vm M buf cap, sideW A vm M buf cap ->
    (0x145000 <= bv_unsigned buf)%Z /\ (bv_unsigned buf + cap <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned buf mod 16 = 0)%Z
    /\ (forall x : word, (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z -> M x <> None /\ owned A x).
  Proof.
    intros A vm M buf cap (HI & Hl & _ & Htop & _ & _ & _ & Hcap).
    destruct (ai_live_hull A M vm buf cap HI Hl) as (Hc0 & Hal & Hend & Hbytes). pose proof (round16_ge cap) as Hr.
    split.
    { apply (live_big_lo sp0 Hvsp AL_grant A M vm buf cap HI Hl). lia. }
    split; [lia|]. split; [exact Hal|].
    intros x Hx. destruct (Hbytes (bv_unsigned x - bv_unsigned buf)%Z ltac:(lia)) as (Ho & Hs & _).
    unfold at_ in Ho, Hs. replace (bv_unsigned buf + (bv_unsigned x - bv_unsigned buf))%Z with (bv_unsigned x) in Ho, Hs by lia.
    rewrite Z_to_bv_bv_unsigned in Ho, Hs. split; assumption.
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
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x62ea4) M (seg_rom RSEGS)) (model2 vm)) K.

  Lemma paylen_facts : (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z ->
    (0 <= paylen < 2 ^ 26)%Z /\ Z.of_nat (length payload) = paylen /\ (0 <= cfg < 32768)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "h02Hah11xh24__p1h34__p2h44__p3h54__x1h64__x2h74__x3h84__x4h94__x5h:1nh;2H1h<2H2h=2H3h>2H4h?2Hch@7__arithhA4__ffhB6__sat5hC6__sat6hD6__sat7hE6__sat8hF6__sat9hG8__varmaphH5__withI4cstrhJ1mhK1yhL2z3hM2z4p&0p;1p;2p;3p;<p;6p;4p;Bp;7p;8g00DRj1>Tg006Qj11Tg00kej1<Tg00H9j2KTg00S2j27Tg019@j2^Tg00;4j24Tg01LYj2pTg01MPj1kTg00;Pj20Tg0076j1VTg007Tk10;Tg0022j2TTg00I<R0k103Tg00;kj2~Tg00:TR1j1LTg00<^j26Tg00=;j2?Tg00=oj3\Tg00=Uj1lj3ITg00>Uj1jTg00L1l<eTg00?3j6aTg00@Cj1cTg00@hj2YTg00U6j2MTg01G>j2XTg01Gfj3WTg00lCj2bTg01FMk20=Tg00lmk20<Tg00LVj1;Tg00M5k10:Tg00MSk209Tg00N4j3`Tg00N]j2_Tg00AJk102Tg008Yj1}Tg00Ajj2PTg00OFj1uTg00BHj4STg00Bfj1rTg00CDj1qTg00Coj2GTg00ROj3QTg00Odj2HTg00PGj1oTg00E7j3nTg01NGj3mTg00EZj2sTg00F<j2tTg00Fhj3vTg00GGj4wTg00Pij4xTg00:6j3yTg0060j3zTg003Bj6{Tg00SNj2|Tg00TQl<]Tg00SkmB00Tg00V_k301Tg00WHj2fTg00X4k304Tg00XTk605Tg00UPj4UTg00V;k706Tg00Y8k707Tg00Y\j7dTg00Z@k808Tg00ZdR2f0R3'7p=2%13#1p=Z%13#1#1#1p=8g00[BR4f1R5;I3p=91|23p=DP4g00[`R6P4P4P0f4R0P1f3R7g00_lf2R8P5P3M<]p=iP6P6P6P4P4P4g00\?P1P1P1f6R9g00\_f5R:P0P7P8P5P3NB00p=hP6P4P4P4P1P1P:P0P7P8P5P3M<]p=g1423p=BAI432p=J%>3#>p==1_43p=EB01453p=5g00bH,f3p=Fg00a\R1@0453p=@P5g00]FR;g00]eR<P<g00^ER=P3J05p=RP4P5g00^eP3CUp=NP5P;P<P<P=P3g00_LK06p=3P8P;P<P<P=P5P3K07p=:P4P5g00c4P3CUp=CP8P;P<P<P=P5P3Fdp=[P4P5g00c[P3CUp=OP7P;P<P<P=P8P5P3L08p=Ag00dBR;#>R>#1R?#<R@g01NjRA'Kg01O^RB'7%1;RC#<RD%>?#1R?#<RE'^RF,4Bp,3sp0RBp,4dataRG'p%kGRH#2%1CRI#1RJ#1RK#ZRL#1#8#8#<RM,4H'0RNP6%VJ$0;RJ/TGRO1K@HRP$03RQ'~RR%LORS/6@/6HRT#214TF'0RU%L3RV/9T/0N'0X:6%LRRW/9TRX/0NRY,0U%DPRZ,6S#DR[/9TR\/0NR],0UPUPYPUP]p-0R]/?U9\UUPXPNP\PNP4P4%l4R\P3X14RXP\1953#jXK4X14PWP[PXPX1?4VX16PRP[1653#DXJ4X:4POPS1?4SPQPZPX%D3X14PPPP1?4PDiFhEgPTPT1?4TM<e1?]N9\NNEaEa%cO%2S1Y2P%BPRO19ZP'017P2%JZ'0'MPZP416S3RZ,Y2%BZ%DZRP/9Z'017Z2%JP'0'M16S5#DP4%=C#1#<RP,XD%BDRZ%2P1^DPRN#B[[%2DRTg01L=RXAWDP5UW0%2N\X^0T1XDE%2E%BF[\ZAWDE5VXX0T%2F\X^0T%VL/bBRB%<KRK+0=%2B%2K20<BK#2[[g00egRK#;#;RL#;RT#;#;RX#;RE#;RZ#;#ERN&0:;-094RP%EZRZ5`4%EERE1_4KRK'5R['5RR'5#F%EL/5K,5Z#F15N[#F%EX%ET/5K'5#FA`4PE/5K,5Z#F%FR&021'@'@'@'@'@'@%}1P41P48P5P4P41P4:P:%u4CSP71P40CSCS%r4%q4R1f7RR,R11G4>RZ1G4;R;%>I,G4RI5Q4RK'N,315:11H42RE,CK,311NZE,315:15[1%o<R<P1f8RK,R11H4@RP1G4CRC5n4RT,NI,315:11CTE,31f9RI,R15:15[1P<P11CEC,311H4M,OC,315:1RXP<P11H4D%V?5m4R?,O;,31P<P11CT;,31P<P1%>>R>#>#=#=#=#=#=#=#1#Z#8#8#8#8#8#8#8#<RT,H41G4>'C,31P<AQ4;P=Q4CRC,CE,311OC?,315:11NZC,31=:1X5:1CACACACACACA1s1=P3P8g00dgR1g00eGR='?1t38=I1=dAv425CwbAbGbHX54X64X74X84X94X2]X3]X4]1630R5,98,0:1752%J8'0'M1K@8R8,9:,0R1782/0K'M%27147M'0147F1K@:/7017TK169@/6RR@#214@F'019K@%2R14RM'0'0'0[[[[[[^54^64^74^84^94^2]^3]^4]P3%JKPO16SK#BPKPBP9PHPSPRPIf;f<f=p,4SPloO>b@bBbCbDbEbFbMb>bLb=bICxAyJQG,TJAzJQGE{g01PPRQ,7214QF'0g01QG,TJ#L=I4Q172A14AM'0'0'0eb?W<W;o"). Qed.

  Lemma calls_rng : (1 <= calls <= 4)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "p'0h07__arithh14__ffh26__sat3h36__sat4h46__sat5h58__varmaph65__with72Hah84__x1h91Hh:2H0h;6__sat6h<1bi001bp;2p;1p;3p;4p;8p;7g01R?j2ZTg01S5j1YTg006Qj11Tg00kej16Tg00;4j25Tg00;Pj24Tg01MPj1GTg01Skj2DTg00lmj2<Tg00H9j2;Tg00S2j22Tg00DRj1>Tg01G>j2XTg019@j2TTg01Gfj3QTg0076j1OTg00lCj2NTg01FMj2=Tg00AJj1LTg008Yj1KTg00OFj1HTg00Bfj1FTg00CDj1ETg00Odj29Tg00EZj2CTg00=;j2ITg00F<j2JTg00=Uj3BTg00Fhj3ATg00GGj4MTg00UPj4:Tg01THj3@Tg00Ajj2PTg00Coj2?Tg00PGj1RTg00E7j3STg00Z@j8WTg00V;j7VTg00Y8j7UTg00ZdR0f0R1'2p=0g00[BR2f1R3g00c4P1C:p=7P3g00]FR4g00]eR5P5g00^ER6P1g00_LFVp=3f2R7P4P5P5P6P3P1FUp=8p,3sp0R8p,4dataR9'Z%Y9R:#0R;g00dBR<#1R=#1R>#1#1R?#1#1R@#1#1#6,5:'4%G9/D0g00dgR9P9%6<RAP9P2P1PA%6>R>,<:RB,;An0100000020000RC'212C>'4P1%6=RC%>=#>#1#6R='XRD150C%0=1TC=RE,50[[RF%0CRGg01L=RHAQC=3UW7R=%0E\H^7GRG%O@/N8R8%6?R?'=R@%08%0?1<8?#0[[R?g00a\R8#LRH%K8R8%H2RE%F2RC%E2RI192ARJ/7J,3I192>RK,7J,3I381CI6RLP1P7g00eGRM,I91J17=B9MdAA203CMRMb1b5b612AA12A>'4P1b0b2b3b4PDPFP=PGP@P?PHP8PEPCP21920REg00c[R9PKC:,3IPLPMb1b5b6150>P1b0b2b3b49@:>%0BR015B>'41=:>%0>P0[\;PDPFP=PGP@P?PHP81P23PCPIP4P5P5P61?2<R<,7E,3IP2P<P9PKC:,3I58I%R5AS2J<R<,7J,3I17<K,3I58IGWPLPMb1b5b6X82%01151>'41;A3R3,2A123>'4[^82P1PBf5O2b0b2b3b4b;b:n0110000020101b<b9g01ToRB,2A12B>'4eo"). Qed.

  Lemma calls_x_val : forall vals, vals_ev vals 11 = Z_to_bv 64 (hdr_b2 data) -> cfg <> 0%Z ->
    edenot (ENV vals) calls_x = Z_to_bv 64 calls.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "h01Hh14__x1h22Hah37__arithh44__ffh57__sat12h67__sat13h77__sat14h88__varmaph95__with:1bh;1zh<4__p1h=7__sat15h>1xh?1yh@2CXhA3H11hB2HbhC2HchD2_HhE3_H0hF3_H1hG3_H2hH3_H3hI3_H4hJ3_H5hK3_H6hL3_H7hM7__sat16hN1ahO1ehP4valsp&0p;1p;2p;3p;4p;5p;8p;6p;7g006Qj10Tg0076k10ATg007Tj1}Tg008Yj1OTg00LVj1NTg01Uej2tTg01S5k10:Tg00HVj26k10DTg00=Uj31Tg01:8j1`Tg016hj2ITg01Vij3;Tg01WFj1^Tg01XMj3]Tg00AJj1KTg00X4j3YTg01Xjj1\Tg01Z2j3WTg01[9j1VTg01\Bj1UTg01]Kj4HTg00DRj1ETg01^Xj5RTg01_ej2QTg01`kj2PTg01b7j4JTg01bWj2iTg01cYk40HTg00kej1<Tg01dbj3hTg00I\j4vTg00;PR0j22Tg01ekj2fTg01g4j4sTg01R?k20GTg00;4j2CTg00:Tj1rTg01:Qj2qTg019@j2MTg01h>j2eTg00lmj2FTg00H9j2[Tg01Skj2XTg01h[k20FTg01i<k40ETg00=;j2pTg01FMj2oTg01G>j2nTg01Gfj3mTg00lCj2lTg00Ajk20@Tg00Bfk10?Tg00CDk10>Tg00Cok20=Tg00Odj2ZTg00E7j3kTg00UPj4STg00EZk209Tg00F<k208Tg00Fhk307Tg00GGk405Tg00QTk804Tg00<Bk603Tg01iXk201Tg003Bj6=Tg00XTk600Tg00PGk106Tg01jdj2~Tg01l1k30;Tg01lTj1|Tg01m5j1{Tg01NGk30<Tg01mVj2zTg01nfj4uTg01oBj3cTg00S2j2yTg00V;k70BTg00Y8k70CTg00Z@j8xTf0R1#0#0p=B%N1#Np=@g00[BR2f2R3f1R4P1CJp=A%E1#0p=:%01#Ep=3%E1#0#0#0p=8%01#0#0#0p=L%01#<p=7%E1#Ep=5P2P2P4P1CJp=gg01ojR5?Y41p=GP4g00dgR6P1g00eGR7CJp=_f5f4R8f3R9P3P4CJ;11p=>g0217R:P:P1g022BCup=jP:P:P1g023<Cup=wg0247R;,f4=131p=9g0254R<?c41p=Dg025`R=?c34=191p=?g00ZdR>/y1p=4g026LR?9161p=dP4g00]FR@g00]eRAPAg00^ERBP1g00_LK0Bp=TAc=41p>02P3P@PAPAPBP4P1K0Cp=aP9P@PAPAPBP3P4P1Gxp=bg00dBRC#0RD#0RE#0RF#0RG#BRH$0ARI#}RJ#Og00egRK#NRL#N#@#@RM#@RN#NRO#@RP,t1p,4dataRQ$0:RR,6IRS51Jg01NjRT=12>#`g026l%O5RU,I2RV/I6RWPVP6g027iRX1IXURYg0297RZg02:C3;R[7;UR\#^A]XU[5AU1I22R[%:F#3#8#L#L#7%0C#3#B#3#5#8#:#8#7'g%0C#8#3#5#:#:#5#3#B#7%0C#8#3#5#5#5#B#3#B#7'g%0C#8#8#3#5#5#L#7%0C#8#:#8#L#L#7'g%K[5Y[5Y[3YR[%\\5WK%5C#5#3#B#:#3#3#:#:#7R\P?g02;>R]%VORO%U>R^CHP?P]%VNRNP^CH%K5R5'GR_'G5AU,_VE>R`PWPVP6g02<0Ra9;YZRb9;XURc#^A]XUb5AU%\c9WK[P7g02<kRcPOP^CHP7P]PNP^CH/G5R5'G9AU\,_VE>R\PWPVP6g02=]RN9;YZRb9;XURd#^A]XUb5AU%\d9WK[%EC#B#3#3#5#3#3#B#:#7RdP7P]POP^CH/G_5AU,_VE>R_PWPVP6g02>XRW9;YZRZ9;XURY#^A]XUZ5AU%\Y9WK[P?PcPOP^CH/G59AUd,_VE>RVg00[`Rd#ORU%O:R5'IROPUP5g02?SRcg02@PR[g02AMg02BIRYPKDRg02CD1Qc[#j'PPUP5%Kd%K:CJR:E>RdPOPUP5g02D?RcP[g02E<PYPKDRg02F8RY,ia1Qc[#j'PP:E>RcPOPUP5g02G1RaP[g02GnRZg02HjRXPKDR1iNY1Qa[#w'PP:E>RaPOPUP5g02IeR5P[g02JbRUPXPKDR1iWY1Q5[#w'PP:E>R:g02K^R5P?PKPL%VPH0H%EC#<R[#U5h<%<CR<#U5h=RY71;RWP5%@P#@#@#@RXPZP^Cv%VM%<DRM#U5h=R=515P5PXPUP^Cv=15='2R='2R^'2RU'2RX'2RZ'2RO'2RN'2R]'2Rb'2P0P`Pbp,3ENVReP8O1g01To,6IRf59JP1P0P\P]Pef8O1=9JfP1P0P_PNPef<O1=9JfP1P0PVPOPef@O1=9JfP1P0PdPZPefDO1=9JfP1P0PcPXPefHO1=9JfP1P0PaPUPefLO1=9JfP1P0P:P^PefPO1=9JfP1P0PWP=PefTO1=9JfP1P5PYPefXO1/f1=1JfXO5PJPSPJP?PKPLP1Cs16I[R['D16I<R5PfC?X:Jp,3sp0Rg00GQ%4RRQ%0H#7Rh,CRRi'2P2PRPJ%<FRF%rK'q,MM,e1%rL,qF,MMRF'F,6I/D[P5PfC?X;2P2P<PJ1eR1/FF,6I/D[P5PfC?X;2P2PRPJ1F1F,6I/D[P5PfC?X;2P2PRPJ16I1/D[P5PfC?X;2PJ%<ERE,FRRF,6IRjPJP1P5PfC?X:JPJ1[F<Rk,6IRlA1J1fX:JP61XT>RmP?P01X41#dA1234#`R0[A1241#`1X34#d[Rn1X93#d\020F41P1n2001000000120000000X?2X>2Pn^?2^>2P1PTP>fWRTO3b0H0EA16?mP6P?P6P2P1P<1[<FRnn0100000020000,6I91JlX:6P2PJ&0DIR0P0PkPnPJ\2/p01oRE%4E%4F[\Q%5D#7RD,nMRQ1C>MRE%4D1MMDR0,C>[[Rn%4MRkg01L=RoAmMD4UW2RD%40\o^2kR01lIgRg%<GRG'oRp%4g%4G1FgG#4[[RGg00a\Rg#KRq%OgRg20@24Rr&0?2Rs&0>2RtP220=2CRC1Z2<Ru5k2g00^eAk2uCCS'T209tBRuP1P31p6720813=167dB072>4H05R7b4b8b9X121[1<1[<1512^12P1PFO1b3b5b6b7b=L04PmP1J03b0A1Jlfe202j5201F<E=1DS[RFPQPnPDP0PpPGp-0RjPqPgPrPsPtP21Z2>g00c4PCCS,TtRlPtP@PAPAPBP9J005at&06ARAPlCbPuP7b4b8b9X12W<%41R9/24%44RB[^12^<jP1PiPRP8O3b3b5b6b7,~RE=PJPFP5PfC?e1FRhPQPnPDP0PpPGPqPgPrPsPtP2PCg00c[RF1Z2hCS,Tt9atlRiPAPiCbPuP7b4b8b9X121C1h,29R91C4h,2B[^12P1PRP8O2b3b5b6b7:0;RhE=1eR<%|RE=1MM>%{ME=1lIS%<HRH,nM%4H1MMHR<,C>[\EAmMH4VoX2k%4<\o^2kPQPnPDP0PpPGPqPgPrPsPtPiPAP2PCPF1Z2M>0<2ICS,Tt9atlCbPuP7b4b8b9X121C4<,2B\9^12P1PRf6O2b3b5b6b7b=bM,zRE=PJP?PKPLPSCs/D[P5PfC?ebB1tTPfVE=PePTO1/fY=1JfeP;P4E=XL=X@WP4P1O2n2001000000121000000X0^XK:P4P1O2n2001000000121000000X0UXJaP4P1O2n2001000000121000000X0XXIcP4P1O2n2011000000121000000X0ZXHdP4P1O2n2011000000121000000X0OXGVP4P1O2n2111000000121000000X0NXF_P4P1O2n2111000000121000000X0]XE\P4P1O2n2111000000121000000X0bXD`P4P1O2n2111000000121000000bNWCWAWPo"). Qed.

  Lemma ownedA_rangeT : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x144020 <= bv_unsigned a < 0x1443d0)%Z
                 \/ ((0x145000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "p;7g02Lgj70Tp,2ALp,2CLp,3ASRp,3sp0p,4Hvspp,7AL_globp,8AL_grantF0o"). Qed.

  Lemma know_after_allocT : forall (A A' : AS) vals (M M' : word -> option byte) vm vm' R' kn,
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> kn_vars_lt (length vals) kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 208 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    (forall a, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ owned A a \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_acallT kn).
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "h04__x1h14HLv0h27__arithh36__sat3h46__sat4h56__sat5h64cstrh74__ffh88__varmaph95__with:4__p1h;4__x2h<4__p2h=1rh>2Hah?1bh@1HhA2H0hB4__p3hC1ohD3HnthE2HxhF1ahG2HehH2HohI4__p4hJ6__sat6hK6__sat7hL4__x3hM1xhN1AhO2A'hP2H1hQ2H2hR2HIhS3HIAhT2HKhU3HLvhV2HMhW3HfrhX2HghY3HgrhZ2Hhh[3Hhih\2Hlh]3Hloh^3Hlth_2Hsh`4Htopha5HtopAhb1Mhc2M'hd2P0he2R'hf6__sat8hg6__sat9hh2knhi1mhj1nhk4valshl2vmhm3vm'p%0p%1p&0p;3p;2p;1p;4p;5p;6p;7p;8p;Ap;<g00gTk30kTg00h]k30jTg00ifk20TTg006Qj13Tg0076j1fTg007Tk10@Tg008Yj1}Tg0087k10PTg00DRj1RTg004Nk20JTg00LVj1iTg0022j27Tg02MkR0k20FTg00=Uj3;Tg02NEk20[Tg02OLk40DTg0129k50CTg0157k10ATg00lCj25Tg00kej1@Tg00<^j2=Tg00mMj4ETg01:8j1<Tg02P\k20;Tg00PGk109Tg02Q`k10ITg00;4R1j21Tg00S2R2j20Tg02Rbj1oTg02Sjj3pTg00M5k10iTg019@k206Tg00:TR3j19Tg00@Cj1NTg01G>k202Tg01Gfk301Tg01FMk20ZTg00lmk20YTg00AJk10BTg00Ajk200Tg00Bfk10XTg00CDk10WTg00Coj2qTg01NGk30?Tg00EZk20VTg00=;j2\Tg00F<k20STg00Fhk30RTg00GGk40QTg003Bk60>Tg02TGR4j2{Tg00Odk20=Tg00Pij4yTg02T_j4xTg02Ulk20<Tg00OFk10OTg02W1k20NTg02WTk10:Tg00;Pj24Tg02X1k60LTg016hk20KTg02Y6j3ATg02YMj2VTg00H9j2?Tg00<Bj6jTg02Ygj7vTg00X4j3hTg02Zej3XTg019]j4^Tg02[?j4tTg00U6S00j2UTg02[Yj3[Tg00E7k308Tg02\3k60HTg00N]j2nTg00V_j3|Tg00WHk207Tg02\Wk205Tg02]6k50GTg02^8k30UTg02_4k10hTg02`;k80gTg02aGmA0fTg02bQk10aTg01Uek20`Tg00L1m<0ETg00?\k40_Tg00UPj4gTg00V;j7rTg00Y8k704Tg00Z@k803Tg00ROk30^Tg01Vik30]Tg01XMk30bTg01b7k40cTg00XTk60\Tg00BHk40dTg00Y\k70eTf0R5#3#3p=Ig00egR6-0`5p=W%35#3#3#3p=K%35#Rp=Pf3R7f2R8'0f1R9/15'4p=2A;895#<p=D1U95,U8p=d%R5#Rp=:%35#3#3#3#3#3#3#3p=Y%35#@p=G%R5#3p=e%R5#3#3#3p=H1089/45p=>g00[BR:/\5p=Bg00[`S01P:P0P3P2g02cPf5R2f4R0P7P8P9P5N<0Ep=O20F07P8P9P5H0_p=Lg00ZdR;/05p=611;5p=Q20=:5p=8P8g00]FR<g00]eR=P=g00^ER>P:P9g00c4R?P5Cgg00_LR@Frp=TP0P<P=P=P>P7P<P=P=P>P:P8P?P9CgP@FrP5K04p=Jf6RAP<P=P=P>P2P0P7P<P=P=P>P8P9P5L03L03p=]Q01P:P4P3P1g02d2P6P;P7P8P9P5N<0Ep=zP8P<P=P=P>P:P9g00c[R1P5CgP@Frp=CP7P<P=P=P>P8P9P5L03p=FB0^:95p=`1195,48p=wg02dTR3,=5p=_P:P9P?P5Cgp>0MP7P<P=P=P>P8P9P<P=P=P>P5P@FrK04p=lB0]::5p=kB0b::5p=m10781195'4,40p=S1489/U5p=M1495,U8p=aP:P:P9P5H0cp=uP9P<P=P=P>P5J0\p=cP8P<P=P=P>P9P5K04p=bP:P8P9P5H0dp=ZP8P<P=P=P>P9P5K0ep=sP:P9P1P5Cgp=~p,2ALR1p,2CLR@p,3ASR:0k1@60j1R@+0TS02Q02g00dBR?#3R4#3S03#3S04#3RB#IRC#fRD$0@RE#}Q04#f$0@RF$0PRG\ES05Q05g01@2S06Q06%R4RH#f00JEg0217#}%i6RI17EA+0Ff7RJ#Wp,3sp0S075;Eg00dgRKf8RL,7E00[8g00eGRM3;g01@iS08p,3ENVRNf9ROO1PLP7H0DP1P@f<S09POPJI0C&0ALQ07,5DRP%KCRC#IRQ#KRR#3#I#KRS#@RT'=RU5;:P1P@f=RVf:S0:PLI0C&0AO=;:UP1P@fAS0;P5CE#<P1P@Q0;P9CE#<20;18#<%R?RW#P#KRX#@S0<,=PRYg02eU'=15D7RZPZPYC2S0=#<S0>Q0;P0O1fBRYP0O15;G[[[[^FEf?S0?P5O1&09FRF5DG15D9R[&0I1R\'1P1P@fCR]P9CEQ0?P9O1=DGF3d[^FEp,4SPloS0@%:W#:#:#:#:#:#:#I#K#Y#Y#Y#GRW/0Pp,4SPhiS0A%3S#I#K#Y#Y#GRS,0PQ08PN%oVS0B9pEYR^O1S0CQ0;f@S0Dg02fWR_&0iXRX%@CS0E'=RCPXg02gPR`Q04#e#P#H#Y#GS0FPE%WYS0G%@4Ra%3H#IRb#@Rc+06Rd15D5Re%RHRH#:Rf#@Rg-06aRh,0e3>X?ERiPEQ07PiPI17EYRi%@?Rj%9iRk'0RlPIPj%BjRmPiPk%BkRnEOf;S0HDLRoPl17E]Rp#NRq%9p#6Rp202ag%QaRr%6g%Qh[[%6aRsg01L=RtB01ag9UW>%6h\t^>s202acRg%6c%Qd[\rRuB01ac9VtX>sRc%6d\t^>sRv%GHRH-02aRw%6H206aHRx#Q[\rRrB01aH9VtX>sRH%6x\t^>sRs%@BRB-0ZPRt%6P%6B20YPB#6[[RBg00a\S0I$0BRxQ0I#}Ry200:9Rz&0X:R{&0W:R|1q:?R}%8S5T|&09=R~P|%8WS0J=T|}P~P|P|%8aRa%fb60?:RbP}%ff:0?:a9T|}DJF]20V|>RaP5P81\KM20S58=;KMdB0R:;9H0QRMb7b8b9X0:105S10W9108h9>d8[[^0:P5PPQ0AQ0@O3b2b3b4b5bJbKbfbgb6b1Q0GQ0:J0>%W^PYQ0BP61{6i%Qk1\:;S0GPiPkPnCzPoPlPqPpPwPrPHPsPtPBPxPyPzP{P|%8j=T|}P~20=:;Rn=C|}CFPaPMb7b8b9X0:S0A10j5%Q9[^0:S0KP5fHS0L,7ES0M#9RkP2O2b2b3b4b5b6b1CyCxJ0>Q0C00<6,5DRi10ih5>dePoPlPqPpPgPuPcPvPwPrPHPsPtPBPxPy&0O:RvP{P|P|Pn%3?#H#e#H#Y#GRc#8Ru%8TS0N,`b9C|uDJPaPMb7b8b9%6c1=dT7wcP5b2b3b4b5bJbKb6b1P;P`P`%_dC2ePoPlPqPpPwPrPHPsPtPBPxPyPvP{P|P|P|Q0N-0N:%8XS0OQ0E#8S0P'`S0QQ0QQ0O5T|DJP|Q0O00MnClPaPMb7b8b9&0:T10CXRn7>C10X;R;'4P5b2b3b4b5b6b1&0:3?>Cn/4;ePNf>S0R#o9pE]O1S0SP_PCPXP`PeJ0L#<PEfDRNQ0?#oR;5pE#W15D8Rn/1`20K::R3AA35_R_%k5RpPZPZ%m5RqDSX=3'V'4Rl10`nRo%_eS0T7wn1?eCRdPnPn1?eXRbC23d#<X?EP5%WNRgPNP;P617ENR;,{6%9;Ri#QQ0GP;Pi%BiRhCzPIP;10jiR^PIPjPmP;PiPhEOPVDLP^fER^,7ERh#N%9hRi#6PwPrPHPsPtPBQ0AQ0KP5fJS0U,7ES0V#9R;P2O2b2b3b4b5b6b1CyCxEj11[`P_PpPnPnPqDSX=3,V310`[15DgRg#_,1[1?gCP[P[1?gXC23M3M#<PE%W^S0W11Z`P_Pp15D0R_P_PqDSX=3,V310`ZQ0T,1ZPdPZPZPbC23M3M#<X?EP5Q07PVEj%_PS0X9won1?PCS0YPnPn1?PXS0ZC25dl#<PJP7P1P@Q0LP7CES0[fIS0\fFS0]PNP0Q09Q0HP5Fv%3?#H#H#K#P#K#GRl/0_%3?#H#H#P#:#e#H#GRo,1_PcP_P_PUC2S0^%@QRQ/0_%@RRR,1_3a3MS0_Q00Pl15D2RbPbPoC2PcPbPbPUC2S0`10Qb11bR3ag02hMS0aP5Pl15DARdPdPoC2P015DJRg/1cS0b1uloRS%3?#P#I#P#:#H#:#:#e#GRK%3?#P#I#P#:#e#P#I#K#GS0c'uR?1uQRRf&0B3S0d5h3S0e5h3S0f5h3S0g9A35S0hPp15DLS0iQ0iPqDSX=3S0j,V3S0k'4PcPgPgPUC2S0lQ0Y/0gQ0Z,1g3aQ0bQ0kPIQ0V10j;S0kPIPjPmQ0VP;%B;EOP]DLS0VQ0kfKS0b,7ES0m#NS0nQ0m#9S0o#6S0pPwPrPHPsPtPBp-0R;PxPyPzP{P|1c|7S0q%8oS0r9C|}S0s5b|P~AC|}uS0tCFPaPMb7b8b9X0:W:115oS0u,49119cS0v[^0:^:;P515DVRV,0lPVPAO3b2b3b4b5b6b1P3Q0jPSQ0g9A3S%kSPgPg%mSC2S0jA;3SSQ0f9A3S1\3S3XQ0VQ0kQ0nQ0pPwPrPHPsPtPBPxPyPzP{P|P|P|%8lP}Q0sDJS0sP~Q0sCFPaPMb7b8b9X0:Q0u9>l5119oS0u9>l9[^0:P5PVPAO2b2b3b4b5b6b1Q0jeC^CtC^3XO1WXP5O110cd11dUPQPdPdPRC23MQ00Q0lPQPgPgPRC2Q0aP5PcQ0iQ0iPUC2PA15DORg/1cS0lQ0hPpQ0:,5DRVPVPqDSX=3S0j,V3S0s'4S0pPcPgPgPUC2S0nQ0YPgPgQ0ZC2S0k'US0VQ0nQ0kPIfLS0w,7ES0xQ0x#9S0y,0jS0zPIPjPmQ0xQ0yQ0y#BEOP^DLS0{Q0zfMS0|,7ES0}#NS0~Q0}#9#6S0}PwPrPHPsPtPBPxPy200:8?Z9vS10P{P|P|P|PuP}1q:4R4Q0N'`9C|}DJS11P~Q11CFPaPMb7b8b9X0:X;:PcP5P51=9TS11C2PcP9P91=8TC2[^0:^;:P5PPQ0?,5DS0?PAO3b2b3b4b5b6b13X3[O1WZP5O1PQQ0iQ0iPRC2PAQ0pQ0VQ0lQ0sQ0{Q0zQ0~Q0}PwPrPHPsPtPBPxPyPzP{P|Q0q%8RS0s9C|}S0l5b|P~Q0tCFPaPMb7b8b9X0:X:;115RS0i,49Q0v[^0:^:;P5Q0?,0QQ0?PAO3b2b3b4b5b6b1P3Q0jPfQ0g9A3f%kfPgPg%mfC2S0jA;3SfQ0f9A3fA;3?fQ0e9A3fA;3ffQ0d9A3f1\3f3X3[3[Q0{Q0zQ0~Q0}PwPrPHPsPtPBPxPyPzP{P|P|P|%8QP}Q0lDJRfP~PfCFPaPMb7b8b9X0:Q0i9>Q5119RS0i9>Q9[^0:P5Q0?PAO2b2b3b4b5b6b1Q0jeC^CtC^3XO1W\P5O1n200100000021100011000W@P5O1n200100000021100011000S0VbCWHQ0[#<eP1P@fGS0[P7CERfQ0LP^P]P0Q0:POP5FvQ0_Q0VbCWH%<fe20;17S0Vp,8AL_errnoP0P5O2PKP_P_Q0cC2P811bcS0_Q0hPpPdPdPqDSX=3S0p,V3Rf'4Q0`Q0Y/0bQ0Z,1b3aQ0_PfPIQ0M10jkS0_PIPjPmQ0MPk%BkEOQ0;DLS0`Q0_Q0\,7ERf#NS0j%9f#6S0?PwPrPHPsPtPBPxPyPzP{P|Q0qQ0c#89C|}S0l5b|P~Q0tCFPaPMb7b8b9X0:X:;Q0c,15S0t,49Q0v[^0:^:;P5Q0H,5DRf,0KPfPAO3b2b3b4b5b6b1P3Q0pP?Q0g9A3?%k?PbPb%m?C2S0gA;3S?Q0f9A3?A;3??Q0e9A3?1\3?3X3[Q0`Q0_Q0jQ0?PwPrPHPsPtPBPxPyPzP{P|P|P|%8KP}Q0lDJRzP~PzCFPaPMb7b8b9X0:Q0t9>K5PKP9P9Q0cC2[^0:P5PfPAO2b2b3b4b5b6b1Q0geC^CtC^3XO1bGWGQ0V#<eQ0=P911_cQ0hPpPbPbPqDSX=3,V3'4Q0^Q0YP_P_Q0ZC2RK'UQ0^PIQ0[,7ERz%9zR?,0jRSPIPjPmPzP?%B?EOQ0DDLPSQ0M#N%6kPwPrPHPsPtPBPxPyQ10P{P|P|P|Q0<#8,`}RkQ0P'`P4AC|4kDJP~P|P|P<P=P=P>1c|0R>1c|2R=P|P|Q0Q:08:}P4Q0O:08:}9C|4DJR}5s|5s|J0HP~P}F]PaPMb7b8b9X0:X;:X:;X<;Q0<,=5R}Q0E'=P9P9P}C21?9CP8P81?9XC29d70Q0a[1?8CP7P71?8XC2[[^0:^;:^:;^<;P5PcPVPVPUC2RX11VcQ0hPpPfPfPqDSX=3,V3'4PVPPPAPJO6b2b3b4b5b6b17[K3[O1W_Q0>eO5bDbDWDXMEQ0S00<6,5DRK#_PePePKC2P]P9O1=DGFPEQ0D#oR]9pE^#WQ0TPZPZPeC2X?EP9Q0WP^P]P61{6h%QiQ0GPhPi%BiR]CzPIPh10jiRKPIPjPmPhPiP]EOQ0RDLPKQ0],7ERK#N%9K#6PwPrPHPsPtPBQ0AQ0KP5Q0oP2O2b2b3b4b5b6b1CyCxEjQ0W,5DRK#_PnPnPKC2PEQ0]#WQ0TP_P_PeC2X?EP5Q07Q0REjQ0XPZPZPPC2PJP0P8O211_\P1P@Q0\P0CEP^P0O1=DGF3dQ0011b\P1P@Q0UP2CEQ0]P2O1=DGF'UQ0[PAO1=DGFRbP511d\p,5AL_hi10\cQ0\PLO1=DGFRdPIQ0mQ0o,0jR^PIPjPmQ0mQ0oQ0o#BEOPNDLP^Q0x#NQ0y#6PwPrPHPsPtPBQ0I%iIR^#iR_#i,n:1n:_1n:^1n:65|:5|:R65|:g00bHR^+07;hxPy200:7?Z8v?Z9v?Z7vP{P|AT|4uP~P|Q04,q:Ru=C|4P~P|Q03,q:R4Q0N'`R_=T|uRZ=b|=P~P|Q0J=T|4R4P~P|P4P~1c|AReCFF]RKF]PaPMb7b8b9X0:X;:XL:X:;X<;105c11791=7T?>0210W010W2PO[[[[[^0:^;:^L:^:;^<;P5Q0aQ0R,5DR]/1PP]PPP\PAPJQ0:Q0DQ0@O:b2b3b4b5b6b1+05bAW@P5O1P1P@Q0bPACE/UbQ00P1P@Q0wPJCEQ0LPJO1=DGFPdP5P1P@Q0|PLCEfNQ0bQ0\POQ0;Q0DP5Fv10lg11goQ0n10Qg11gR3a3MQ00PlPVPVPoC210QV11VR5aXQ0wQ0HO1=DGFP5PlPfPfPoC2Q0|Q09O1=DGFRFPIfO,7ERG%9GRo,0jRXPIPjPmPGPo%BoEOQ0LDLRoPXfP,7ERG#NRm%9G#6RGPwPrPHPsPtPBQ0I2076^;hxRxPyQ10?Z8v?Z8vRvP{P|P|P>P|Q0r,~uClP~PKCFPaPMb7b8b9X0:X;:X:;X<;XB;Q0u,48Q11/08RK/4010W8R^10W7RWPL[[[[^0:^;:^:;^<;^B;P5Q0a15DYRD/1PR610lDPDPPPAQ0RPNQ0@O9b2b3b4b5b6b1+05WAP5O110cf11fUPQPfPfPRC23MPoPXPmPGPwPrPHPsPtPBPxPyPvP{P|P|P>P|1~u_ClP|P=P|Q0s,~uCl5s|P~P|Ab|ZeP~P|P4P~P|P4P~1c|JF]F]PaPMb7b8b9X0:X;:X:;X<;XB;XI;1=5T,19Q0i,475M814K2PO\W\^[[^0:^;:^:;^<;^B;^I;P5Q0aP610QD10cDPDPPPAQ0RPNQ0@O:b2b3b4b5b6b1-05FWAP5O1n200100000021100011000bCW@P5O1P5X@dP5O1n200100000021100010000WAP5O1n200100000021100011000bCbEbEWVWEXMEQ05Q01Q0F/0[%99,?n/0`P0P7P8P9P5I0GWQWPWjXFEWiQ09Q08PYQ0Bp,3AMBp,3a0sp,4path40U$0hQ0;Q09POPLL0gNA0fQ08Q0CQ0DQ09$0aH0Deb[b]WYWWW`WRWaWSWTW^WdWUWhWeWmWlWcWbWkWOWNo"). Qed.


  Lemma env_ok_allocT : forall A A' M M' vm vm',
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 208 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "h04__x1h14__p1h21ah37__arithh44__ffh56__sat3h66__sat4h76__sat5h88__varmaph95__with:4__x2h;4__p2h<2Hah=1oh>1Hh?2H0h@2HehA2HohB4__p3hC1AhD2A'hE2FRhF2H1hG2H2hH3HEahI3HElhJ3HErhK2HIhL3HIAhM3HfrhN3HnehO4HtophP5HtopAhQ1MhR2M'hS2vmhT3vm'p%0p&0p;3p;2p;1p;5p;4p;7p;6p;8g00gTk30ATg00h]k30@Tg00ifk203Tg006Qj10Tg0076j1rTg007Tj1pTg0087k102Tg011;j3aTg02hjj3gTg00lCj2=Tg00;4j24Tg01:8j19Tg00=Uj32Tg00kej1CTg00S2j21Tg00DRj13Tg00PGj1jTg00;PR0j2:Tg0129j5ITg0157j1HTg00<^j2GTg00mMj4BTg02P\k20?Tg02Ygj7tTg01G>k20>Tg019@k20=Tg01Gfk30<Tg01FMk20;Tg00lmk20:Tg00LVj1]Tg00N]j2UTg00WHj2hTg00AJk109Tg00X4j3fTg008Yk108Tg00Ajj2qTg00OFk107Tg00Bfk105Tg00CDk104Tg00Coj2TTg00EZk201Tg00=;k200Tg00F<j2~Tg00Fhj3}Tg00GGj4|Tg00ROj3`Tg00U6R1j2PTg003Bj6cTg019]j4oTg00V_j3yTg00BHj4xTg00Odk206Tg00UPj4\Tg00V;j7_Tg00Y8j7^Tg00XTj6wTg00Y\j7kTg00Z@j8iTg02\3j6vTf0R2#0#0p=X%02#3p=V%02#0#0#3p=D%32#3p=@%32#0#0#0p=O%32#0p=7%02#0#0#Cp=8%32#3#3#0p=E%32#3#3#3p=[%02#0#0#0p=J%02#3#0#0p=ef2R3f1R4'1/:2p=nf3R5/13/:4/P2p=>%02#Cp=m11531442':p=6%02#0#0#0#0#0#0#0p=W1434,:5/P2p=ug00[BR6?242p=L1:42,P3p=Yg00ZdR7/12p=NAy642p=KP6P3P4P2Cxp=A20662p=5P6P4g00c4R8P2C\p=RP3g00]FR9g00]eR:P:g00^ER;P6P4g00c[R<P2C\g00_LR=F_p=;P5P9P:P:P;P3P9P:P:P;P4P=F_P2F^p=SP3P9P:P:P;P6P4P8P2C\P=F_p=<P4P9P:P:P;P2Ewp=df4R8P9P:P:P;P5P3P9P:P:P;P4P2F^Fkp=?f6R>P9P:P:P;f5R?P8P5P9P:P:P;P3P4P2GiGip=M1442,:3p=ZP4P9P:P:P;P2Evp=QP5P9P:P:P;P3P4P2Gip=FP3P9P:P:P;P4P2Fkp={P3P9P:P:P;P4P2F^p=bP6P4P<P2C\p=lP5P9P:P:P;P3P4P9P:P:P;P2P=F_F^p=s1:34/P2p=zp,2ALR=p,2CLR9p,3ASR:0A=960@=R9+03S00Q00g00dBR<#0R@#0RA#0RB#0RC#XRD#rRE#pRF%rB#pRG$02RH[S01Q01g01@2S02Q02p,3sp0RIp,4mem0RJ;a5P0AgIJ8%0<#V#D#@#O#7#7#8RK1=E2RL%0<#7#D#E#7#@#V#8RM,4L%0<#7#D#@#[#D#8RN%0<#O#O#J#e#8RO,4LRP7nLC>RQ%0<#V#D#@#O#@#E#mRR1=E4RSPS%0<#V#D#E#V#J#8RSC6#9RTf7RUP3O1PJP3O1RV52H[[^2F%JDS03#XRD#JRW#CRX/1LRYPL%3C#E#W#8RZ%0<#X#7#e#E#7#@#8R[PLPL%0<#X#7#e#E#@#X#8R\C6CuR]P>P4O1%jGRG52H[^2F':P=P9PUP?P5DI%H81=EIR^%JW#8RW'GR_'LP=P9f8R`P>P8DI%H?/L_P=P9f<RaP2CB#9P=P9PaP4CB#920?=3S04#9Rb%3<Rc#0#7#8Rd,G^S05g02eU'GS061=E5RePeQ05C6#9Rff=RgP8O1f>S07P8O152H[[[[^2Ff9Rh9aIJ[[[[[P2AgIJ>f:RiP3O1=2HV\T\Q^2FPhP4O1=2HG\]^2F':P0f;R0P3O1=2HV\T\Q^2FPiP4O1=2HG\]^2FP=P9P0PhPUDI%H`/L_P=P9PaPiP`DI%Hh/L_P=P9f@RjP2CB#9P=P9PjP4CB#9fAP8O1fBS08P8O152H\f\b[[^2FAaIJg[[[[[P2PgP3O1=2HV\T\Q^2FPgP4O1=2HG\]^2FP=P9Q07PaPiDI%H0/L_P=P9f?PgP0DI%Ha/L_P=P9fCS09P2CB#9P=P9Q09P4CB#9fDRaP8O1fERgP8O152H\f\b[[^2Fp,4SPloRf%@c#[#[#[#J#W#W#W#8Rc/1^11^LS0:?YYPS0;P8P3P=P9fGS0<P3CBS0=fHfFS0>PaP5PhP`P2FtPOPe%0<#O#7#D#E#7#8RY,4e%0<#O#7#7#W#8RPPe14e_%CDRDPePePXC6C>C>S0?P1PO1=E8R1P1PYC6PPP1141_PDP1P1PXC6C>g02hMR1P2PO1=E?RLPLPYC6%C@Rj%3@S0@#3#mRk+0>Rl147j%Nk20=jkRm,47[[Rn%NjRog01L=RpB0<jk4UW<Rk%Nm\p^<oRo%CCRC-0;^Rp%N^%NC20:^C#N[[RCp-0Rmg00a\Rjg00egRq#]Rr#]Rs#]Rt,U6S0A1U6sRs1U6qS0B'K'Kg00bHRq'h&09jRu3fS0C&08jRv1q63S0D&076Rw7A4S0E?A3w?A3wS0F&056Rx&046RyPyPy%5ORz1T6BRB'R%5Y9;yBCS%j:R:PyPy1T6ARA=<yBS0GPy1dy8R{A;yBzS0HD?P:Py%5cR|=<yAR}P:PyP}P:1dy?S0IFMS0JFM201y;R;P2P3g00dgR}g00eGR~+001~23=2}~dA}674C|R7b4b8b9X06X:6X1mW;POP4P4PYC61143RY143OR~7Y511c3R}11c5S0KPU[[S0L[[^06^:6^1m^;mP2P11=EiRi,1XPiP^P8PhP0PfO8b3b5b6b7W?P2O1PPPL14L_PDPLPLPXC6C>PlPnPkPoPpPCQ0CPvQ0FPxPyPyPyPy%5P/RB%5W9`6A9;yBCSPyP{%5XRA9;yBD?P:PyPyQ0GPyA<yABQ0HD?P:Q0JFMP;P7b4b8b9X06X:6X1mX;mPPP41G2W,44AZ34XC>11X3=YY~Q0L[[^06^:6^1m^;mP2P111DiPiP^P8PhP0PfO8b3b5b6b7W?P2O1n200100000021100011000Rib=WAQ0=#9eP=P9Q0>P3CBR9Q0<PgQ09P5PUP>P2FtQ0?Pib=WA%99eQ04p,8AL_errnoP5P2O2PRPePePSC6PlPnPkPoPpPCPuPv1q64Re?A4wR9?A4w?A4wPxPyPyPy%5RRi/RB%5SR=9;yBCSRBP:Py1QyBP:1dy5RBFMP;P7b4b8b9X06X1mPRP2P2PSC6RD11R4R~?Z4SP1[RWP5[[^06^1mP2P11=E`P8P>O4b3b5b6b7b@W@PbePlPnPkPoPpPC%]t,U61U6rRr,Ks'K/hq=fjuPvQ0EPxPyPy1T6<R<1T6@R@5<yRsPyP{A;y@zRzD?P:PyA<y|<RtP:PyPtP:PyPy%5d9`6<RtQ03#CRb#55`6/R@A;y@tCS,QyCFFMP;P7b4b8b9X06X:6X1m1124Rt144OR`7Y311c41G5dRd/GbP8P8PdC6P1[\}[[^06^:6^1mP21=E>R>,1XP>P^P?PUPfO6b3b5b6b7Q061=E3REPEQ05C6#9eO5XNTW<X2FQ0;PaP3O1PgP3O1RE52H\T[^2FQ089gIJRIA2HEV\T\Q^2FRdPaP4O1Ra=2HG\]^2FRb':Q0:PHPgP4O1RgA2H2VX=HQ07P4P2O2PaP3P4PlPnPkPoPpPCPuPvQ0EPxPyPsP:A{ys{CFP;P7b4b8b9X06X:6X1m1PY5\t^06^:6^1mP211XLRt?ZLOPLP^P8O4b3b5b6b7PlPnPkPoPpPCQ0AQ0B,Kr'K/hq=fjuPvQ0D?A3w9Aw4PxPyQ0@,T6Rw=<y<P:PyA<y|wRwP:PyPwP:A;y<=R=9by{,QyCFFMP;P7b4b8b9X06X:6X1m1142Q0KAZ?5SP1[[\}[^06^:6^1mP211RLP^PLP8PUPfO6b3b5b6b7O3EcW<X2FPIePdPbPHQ0>P3O1PJP5O192H2X=HP0P3P4P2O3PEP5P3PlPnPkPoPpPCPuPvP9PxPyPyPyPy%5K/R@%5M9;y@CSPy%5N=<y@PzD?P:PyPBPyA<yA@RAPzD?RzCFP;P7b4b8b9X06X1mPKP2142MPNP2P2POC6C>11X4=Y3`R`[^06^1mP211^>P>P?O3b3b5b6b7PlPnPkPoPpPCPuPvPePxPyA<yi<Ri=by=,QyR=P:P=CFP;P7b4b8b9X06P1\DPW[^06P2P>P8O2b3b5b6b7O3EcXGTXFQX2FPHPgA2H2GX=HPhP4P2O2PaP3P4PlPnPkPoPpPCPuPvP9PxPyPyPyPAPy%5ZRA,l@CsPy%5[=<y@%5\R99;y@D?P:PzCFP;P7b4b8b9X06X1mPXP2142ZRZ142\R\9n[2C>P`[^06^1mP211^LPLP8O3b3b5b6b7PlPnPkPoPpPCPuPvPePxPyPyPyPBPy1l<ACsPyP{A;y<9D?P:Q0I9byi,QyCFP;P7b4b8b9X06X1mX;mXBm1:3\9z4Z1:~8P1[[^06^1m^;m^BmP214LS11[LPtPLP8O5b3b5b6b7O3EcX<]X2FCoCobEb>WMWOWKWPWLWJWIP4P2O2n2101000010121000000W>WHP4P2O2n2011000010121000000W>WTWSWRWQWDWCo"). Qed.


  (* [comment removed for export] *)
  Lemma sgn_tab : forallb (fun b => Bool.eqb (bv_lts (Z_to_bv 64 (bv_swrap 8 b)) (Z_to_bv 64 0)) (128 <=? b)%Z) (zseq 256) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "h01bp;2p;1p;3g00=;j2=Tg006Qj12Tg0076j13Tg02idj25Tg00HVj24Tg02jKj3<Tg00kej1;Tg02k8j27Tg02kUj26Tg02klj18Tg02lej39Tg00=Uj3:Tg00LVj10Tf0R0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00dgR1g00eGR2'=g00[BR3g00dB#2#2#2R4#2#2#2R5#3R6%34/50,46g00Zd,463<%25#;/70'6X03g00eg#1#1#1#1#1#1#1#1#839=:12do"). Qed.
  Lemma sgn_val : forall b, (0 <= b < 256)%Z -> bv_lts (Z_to_bv 64 (bv_swrap 8 b)) (Z_to_bv 64 0) = (128 <=? b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "h01Th11xh22Hah34__x1h41bh52Hbh67__arithh74__ffh86__sat3h96__sat4h:6__sat5h;8__varmaph<5__with=5lemmah>1yp;1p;2p;3p;<p;6p;4p;7p;8g006Qj12Tg00kej15Tg00;4R0j23Tg00;Pj27Tg0076j1BTg02idj2=Tg00HVj29Tg02jKj3:Tg02k8j2;Tg02kUj2?Tg02klj1FTg02lej3iTg02Y6j3<Tg02mAj2[Tg02mZj3YTg02nKj3XTg00:TR1j1ATg02nnj2WTg00=;j26Tg00=oj3VTg00>Uj1UTg00L1l<OTg00?3j6NTg00DRj1>Tg01G>j2LTg019@j2KTg01Gfj3JTg00lCj2ITg01FMj2HTg00lmj2MTg00AJj1GTg008Yj1PTg00Ajj2QTg00Bfj1RTg00CDj1STg00Odj2@Tg00Coj2hTg00UPj4ETg00Y8j7gTg00PGj1fTg00Z@j8eTg00EZj2aTg00F<j2`Tg00Fhj3\Tg00GGj4ZTg00Pij4]Tg02oej4^Tg030@j3_Tg00=Uj3CTg00S2j2bTg00LVj10Tg00TQl<cTg00V;j7dTg00ZdR2f0R3'bp=1%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=4g00dgR4g00eGR57C3p=8g00[`R6g00[BR7P7P7P1P1f5f4R1f3R8f2R9f1R:P3M<cp=TP:g00]FR;g00]eR<P<g00^ER=P3g00_LFdp=D%13g00dBR>#2R?#2#2R@#2RA#2#2RB#2RC#2#5RD,33'7REg030\%BBRB%B@R@/=3,9B19B2RF3:%5CRC/;3'?X47RGg00eg#4#4#4#4#4#4#4#4RH#FRI5i7#8RJA<73IPGP:O1#8[^17RK,[JAYJK3W=AX7GIP3O2PKP3P8A<78I%11%AHRK,31'7[%18RG138KRJ'7RLA<71I[1WH8PL138DRI,7GPGPJPGPIp-0/6G9VGGP7P7P0P3X17RGP013:3#UX>7X17P8P81678PKPDPGPG%A3,67X16PHPD167DETM<OEN%5?RH%>?#>#2#5R?'L132H%1?1KH?R6,32[[%1HRGg01L=RKAJH?:UW2%16\K^2Gp,3sp0,IBRG%5ARA'H%1G%1A1MGA#1[[g00a\RA#G%PA1Q7:%R7%S7RAP;P<P<P=PAP;P<P<P=P71@72g00c41h7>R>CE,DAP7P>g00c[1@7DCE,DAFgR>%f<P>Ge1aA=P3P916451`39#8dA\72:CZb7b;b<X37%1:13:D'7\E^37P3f7f6O2b6b8b9b:C]PLeC^O21=@8,9B=:BF1;C8'?#81=@1,9B=:BFRF1;C1RC;_3AC4FCP3b0b0b0b0W5X47o"). Qed.

  (* [comment removed for export] *)
  Lemma sideW_frame : forall A vm M M' buf cap,
    sideW A vm M buf cap ->
    (forall x : word, M' x <> M x -> O23ReadLoop.in_win sp0 x \/ in_data x \/ (exists p n, live A p = Some n /\ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z)) ->
    mem_grows M M' ->
    sideW A vm M' buf cap.
  Proof.
    intros A vm M M' buf cap HS Hchg Hgr. pose proof (bufW_facts A vm M buf cap HS) as (Hb0 & Hb1 & Hal & Hbb).
    destruct HS as (HI & Hl & Hvl & Htop & Hisp & Hres & (HEa & HEl & HEr) & Hc0). pose proof SPlo.
    assert (EQ : forall x : word, ~ O23ReadLoop.in_win sp0 x -> ~ in_data x ->
                 ~ (exists p n, live A p = Some n /\ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z) -> M' x = M x).
    { intros x H1 H2 H3. destruct (M' x) as [b'|] eqn:E1; destruct (M x) as [b|] eqn:E2.
      - destruct (Z.eq_dec (bv_unsigned b') (bv_unsigned b)) as [Hb|Hb]; [f_equal; apply bv_eq; exact Hb|].
        exfalso. destruct (Hchg x ltac:(rewrite E1, E2; intros HH; injection HH as HH; apply Hb; rewrite HH; reflexivity)) as [?|[?|?]]; tauto.
      - exfalso. destruct (Hchg x ltac:(rewrite E1, E2; discriminate)) as [?|[?|?]]; tauto.
      - exfalso. destruct (Hchg x ltac:(rewrite E1, E2; discriminate)) as [?|[?|?]]; tauto.
      - reflexivity. }
    assert (LIVEB : forall p n x, live A p = Some n -> (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z -> M x <> None /\ owned A x).
    { intros p n x Hp Hx. destruct (ai_live_hull A M vm p n HI Hp) as (Hn0 & _ & _ & Hbytes). pose proof (round16_ge n).
      destruct (Hbytes (bv_unsigned x - bv_unsigned p)%Z ltac:(lia)) as (Ho & Hs & _).
      unfold at_ in Ho, Hs. replace (bv_unsigned p + (bv_unsigned x - bv_unsigned p))%Z with (bv_unsigned x) in Ho, Hs by lia.
      rewrite Z_to_bv_bv_unsigned in Ho, Hs. split; assumption. }
    split; [|split; [exact Hl | split; [exact Hvl | split; [exact Htop | split; [exact Hisp | split; [exact Hres | split; [|exact Hc0]]]]]]].
    - apply (ai_frame A M M' vm HI).
      + intros a Ho Hnl. apply EQ.
        * intros Hw. unfold O23ReadLoop.in_win in Hw. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
        * intros Hd. unfold O23ReadLoop.in_data in Hd. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
        * intros (p & n & Hp & Hk). exact (Hnl p n Hp Hk).
      + intros a Ho HM. apply Hgr. exact HM.
      + intros a [Hg Hlt] HM'. pose proof (AL_grant a Hg) as Hg'. rewrite Htop in Hlt.
        destruct (M a) eqn:EM; [discriminate|]. exfalso.
        assert (NE : M' a <> M a) by (rewrite EM; exact HM').
        destruct (Hchg a NE) as [Hw|[Hd|(p & n & Hp & Hk)]]; [unfold O23ReadLoop.in_win in Hw; lia | unfold O23ReadLoop.in_data in Hd; lia |].
        exact (proj1 (LIVEB p n a Hp Hk) EM).
    - split; [|split].
      + intros a Ha. rewrite EQ; [apply HEa; exact Ha | unfold O23ReadLoop.in_win; lia | unfold O23ReadLoop.in_data; lia |].
        intros (p & n & Hp & Hk). destruct (ai_live_hull A M vm p n HI Hp) as (_ & _ & Hend & _). pose proof (round16_ge n). lia.
      + intros a H1 H2. rewrite EQ; [apply HEl; assumption | unfold O23ReadLoop.in_win; lia | unfold O23ReadLoop.in_data; lia |].
        intros (p & n & Hp & Hk). destruct (LIVEB p n a Hp Hk) as [_ Ho]. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
      + intros a Ha. rewrite EQ; [apply HEr; exact Ha | unfold O23ReadLoop.in_win; lia | unfold O23ReadLoop.in_data; lia |].
        intros (p & n & Hp & Hk). destruct (LIVEB p n a Hp Hk) as [_ Ho]. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
  Qed.

  Lemma sideW_block : forall A vm M buf cap E log,
    sideW A vm M buf cap -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    sideW A vm (mem_denot E M log) buf cap
    /\ forall x : word, ~ O23ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "p'0h07__arithh16__sat9h27__sat10h34__x1h41si001sh54__p1h64__ffh78__varmaph85__with97__sat11h:6__sat8h;2H7h<2H8h=1nh>1ph?6__sat5h@4__p2hA6__sat4hB6__sat3hC6__sat7hD2H5hE2H6hF4__p3hG6__sat6hH4__x2hI2H1hJ2H2hK2HahL1xhM1rhN2H3hO2H4hP1bhQ1AhR1EhS1HhT2H0hU3HE0hV2HShW4HloghX3HnehY3Hx1hZ3Hx2h[1Mh\3OUTh]3bufh^3caph_3logh`2vmi011gi021lp%0p%1p&0p;3p;2p;1p;5p;4p;6p;;p;9p;7p;8g00gTk30OTg00h]k30NTg00ifk20<Tg006Qj13Tg0076j1dTg007Tj1uTg0087j1oTg008Yj1mTg00nQj5kTg01Z2k305Tg00=Uj3TTg02Ulj2iTg00DRj1BTg00lCj24Tg00S2j22Tg031Tj2KTg01:8j19Tg032Oj1ITg00kej1UTg019@j2nTg01G>j2lTg00;4j20Tg01Gfj3jTg01FMk204Tg00lmk202Tg00AJj1yTg00Ajj2zTg00Bfj1}Tg00CDj1|Tg00Coj2hTg00PGk10MTg01NGk30LTg00EZk20HTg00=;k20GTg00F<k20DTg00Fhk30BTg00GGk40ATg003Bj6xTg016hk20@Tg00<^j2RTg00;Pj26Tg00X4j3tTg00OFk10=Tg00Odj2sTg00ROj3rTg019]j4\Tg03=>j2qTg03=_j6VTg03>@j3pTg03>am;0;Tg03@0j4`k30:Tg03ABj28Tg03Aij21Tg00J8k209Tg00H9k208Tg02YMj2GTg00U6j2:Tg00BHk407Tg02\Wj2;Tg02Zej3vTg03BEk30>Tg03C]m90?Tg00UPj4fTg00V;j7eTg00Z@j8_Tg01Vik301Tg01XMk30CTg01b7k400Tg00Y8j7~Tg00XTk60ETg00Y\k70FTg02\3j6{Tg035cR0k20ITg01:nk40JTg02[Yk30KTf0R1#3#3p=Y%B1#Bp=[%B1#B#B#Bp=Z%31#3#3#3p=w%31#3#3#3#3#3#3#3p=J%31#3#3#Up=Lg00ZdR2/21p=>%31#Up>06g00[BR3/s1p=Ff2R4g00]FR5g00]eR6P6g00^ER7P3f1R8g00c4P1Cfg00_LR9Fep=Cf3R:P5P6P6P7P4P8P1G_p=gB01331p=^B0C331p=]%B1#3p=Q%31#Bp=P%B1#3#3#3p=WP3P3P8P1H00p=c12:41081'6p=5P4P5P6P6P7P3P8g00c[P1CfP9Fep=OP4P5P6P6P7P8P1F~p=AP8P5P6P6P7P1J0Ep=bP4P5P6P6P7P8P1K0Fp=?P8P5P6P6P7P1E{p=af4R;P5P6P6P7P:P4P8P5P6P6P7P1E{G_p=H1248/61p=S1:81,:4p=D1081,64p=X10:41181+0Ip=7f6R<f5R=P;P:P4H0J;T8/61p==1G31p=<1K;:%I41G81':':p=MP4P5P6P6P7P3P8g03DYP1CfP9Fep=NP<P5P6P6P7P=P;P:P5P6P6P7P4P8P1G_G_p=EAv481:0K;:p=@%I41G81':p>03p,2ALR5p,2CLR9p,3ASR:0O5960N5R9+0<g01@2g00dBR>#3R?#YR@#3RA#YRB#dRC#uRD%d@#u#oRE[g03E@g03FH#mP<P=P;P:P4Dkg00dgRFg00egRGg03GSRH<058g00eGRI3T1i:Gp,3sp0RJ5TDp,4SPloRK%B>#[#Z#Z#Z#w#J#J#J#LRL14CJRM'2p,4SPhi%3B#J#JRB#3#w#J#J#L,2M1KJ1#9RN%I8#9ROf9RPf<RQf8RRPGPHP4P<PDPJ%U?RS%B?RT#3#YRU#URV'nRW14C1RX'2XPD1lSVRY102SRZ%>V102W[[R[%>SR\g01L=R]AjSV8UWKRV%>W\]^K\R^%BT$06RT,lSR_%>T1nSTR`,02[\ZRZAjST8V]XK\RT%>`\]^K\R\%UARA-04MR]%>M%>A202MA#>[[RAg00a\R`#yRa%m`R`1z38Rb%}3Rc%|3Rd%FL1h3>Re5Cd&0M6R6%FS%dU60L3RU=CdeCg20Hd7R7P1P420GFI20D14=TFIdB0B328H0ARIb6b7b8X3312L112W8[^33P1PMPKO2b0bBbAb?bGbC1iPGRGP=Ex20@33RK%^1RL#>RF%]1RS%UBRB,RWRf'2'6XMKRg%Q@#P#Q#J#LR@%3>#P#Y#P#[#W#Q#Q#LRh'cRi%3>#W#P#[#Q#Q#[#P#LRj%3>#W#P#[#Z#Y#P#LRk'cRl%3>#W#W#P#Z#Y#LRm%3>#W#Q#Q#J#LR>'cRn%yKRo5tKRp5tKRq%^iRr#>Rs%]iRt/2fRuP_PZPTP\P]PAPaP`&0=3RvPc1s32R2%F@Rw5CdP7PIb6b7b8%>@P1b0bBbAb?PsePYP[PVP^P_PZPTP\P]PAPaP`PvPc%FhS00%FBRs9r3URU5CdP7PIb6b7b812hfP1b0bBbAb?bGbCPueC\PKPgPlPp%^lRu#>Rx%]lRy/2fRzP_PZPTP\P]PAPaP`PvPc%FjR{9Cd2P7PIb6b7b8%>jP1b0bBbAb?PxePYP[PVP^P_PZPTP\P]PAPaP`PvPc%FkS01=CdUP7PIb6b7b812kfP1b0bBbAb?bGbCPzeC\PKPgPnPo%^nRz#>Rx%]nR|/2fR}P_PZPTP\P]PAPaP`PvPc%FmR~9Cd2P7PIb6b7b8%>mP1b0bBbAb?PxePYP[PVP^P_PZPTP\P]PAPaP`PvPc%F>S02=CdUP7PIb6b7b812>fP1b0bBbAb?bGbCP}eC\1qKgEVEVEVg02dTRg,RW,2S,6FXMK=pKHePDPJ1RXg14C:RFPFPXC5#9XPDP81RMg14C4RgPgPMC5#9ePGP=ExPKPLPFPFPSC5#9XMKRSPiPqP_PZPTP\P]PAp-0RqPaP`PbPcPdACdweRiQ009OdeS035AdRLACd{eRGQ019OdeS045AdRX1bd:RW5?d5?dS05,adP6PdPLDHP7PIb6b7b8X33W5101hS069S@1101kS079Sj1R};D8g02hMRf[12@8RU?X8hPf[[^33^5qP1Pm14C<R^P^P>C5RVP^P;O3b0bBbAb?PrPgPgPtC5#9ePKPSPlPpP_PZPTP\P]PAPaP`PbPcPd1bd;Rp9?dX9?dWS08,adP6PdPXDHP7PIb6b7b8X33X5qX@qAD8}4Pf[12j8Rl?X8kPf[[^33^5q^@qP1PVP@P^P^PhC5RVP^P;O4b0bBbAb?PuPgPgPyC5#9ePKPSPnPoP_PZPTP\P]PAPaP`PbPcPdACd~eRoQ029OdeS095AdRn9?dXRX9?dWS0:,adP6PdPnDHP7PIb6b7b8X33X5q101>S0;9Sm19D8}Pf[12m8R}?X8>Pf[[^33^5qP1PVP^P;O3b0bBbAb?PzPgPgP|C5#9e1qKSEVEVEVApKSHeN;0;WZWYXLDPPPQPRP4C`PQP4O15TE\O\N^LDPQf;RSf7RKf:RH<0:<R|PPPRDkPHf=RzPPP4C`PzP4O15TE\O\N^LDPQPSPHP|PPPRP=PRPSPKP1C`PSP1O15TE#914C8RE1RMBR|'8PEP|PEP|C7P010g|11g|PJP:P:PD%o3RgP5P9fBRNP820931ROPE14C=RVPV208E1RnC5F=X=3#<X>DDMP110F|14C;S0</8@Q0<P@Q0<P@C7P010V@11V@PJP<P<PDPgP5P9fERyP8POPE14CRRRPRPnC5F=X=3#<X>DDMS0=P110^@14CKRu/8mPuPmPuPmC7P010Rm11RmPJPPPPPDPgP5P9fHS0>P8POPE14CSRSPSPnC5F=X=3#<X>DDMS0?P114CPRP/0m14CHRt/8jPtPjPtPjC7P010Sj11SjPJPQPQPDPgP5P9fKS0@P8POPEf>Rr,4CR[P[PnC5F=X=3#<X>DDMS0AP114CQRY/0j1KJzS0B%IzS0CPgP5P9fLP8POPEf?S0D,4CRxPxPnC5F=X=3#<X>D,GDS0E':S0F':PQPrPzP_PZPTP\P]PAPaP`P31z34P8PvH07S0GPcPd1h3?R?Ar3esS0H5OdP6PdQ0H=Cd?S0I=AdpDHP7PIb6b7b8X33XH3X5qS0J1R1B,081R8BS0K?S4:Pf[[^33^H3^5qS0LP1fAS0M,4CRs/0MPsPMPzO4b0b:b1b2Q0B#9eP_PZPTP\P]PAPaP`PbPcPdAOdewRvP6PdAAdiWAAdGp1bd=S0N9AdoS0O5?dS0P5?dDHP7PIb6b7b8X33X5qX@qXFqS0Q101@16U416l:16};3DPf[[^33^5q^@q^FqS0RP110s>S0S10skS0T10shPsPHO5b0b:b1b2Q0C#9eO3O1';W;P1O111Yj14CzR}/8kP}PkP}PkC7P010[k11[kPJQ0DQ0DPDPgP5P9fNP8POPEPsPsPnC5F=X=3#<X>DDMS0UP110xkf@Rl,KJS0V%IlRUPgP5P9fOP8POPE14CNRoPoPnC5F=X=3#<X>D,GDS0W':S0XPUQ0WP_PZPTP\P]PAPaP`PbPcPdANde{S0YP6PdPvP6Q05FEP7PIb6b7b8X33X5qS0Z111j108@RGP@P4P4PhC5RiPjP4P4PkC5Rr;D:S0[[[^33^5qS0\P1fDS0],4CRQ10Q>S0^5SmPQPKPzO4b0b1b2b9PUeD@W<P1O111xkQ0VQ0X':S0_Q0DQ0MPlP_PZPTP\P]PAQ0JQ0LP110QMPQPMPlO4b0S0`b1b2b9Q0V#9S0aeP_PZPTP\P]PAQ0QQ0RP1Q0^10QkS0b10QhS0cPQPzO5b0R2b1b2b9%9US0deO3O1';W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111Pm18t>PtP>PtP>C7P010S>11S>Q0AP110Y>Q0BQ0FQ0CQ0EP_PZPTP\P]PAPaP`PbPcPdANde~S0eP6PdPvP6A?dLXFEP7PIb6b7b8X33S0f111mPmP4P4P>C59Dir\G[^33S0gP1PsPKPHO3b0bCb:b1Q0CeD@WEP1O111Y>18}jS0hP}PjP}PjC7S0iP010[jS0j11[jS0kQ0UP110xjS0lQ0_Q0DQ0MPlP_PZPTP\P]PAQ0`b:b1b2Q0aeS0`P_PZPTP\P]PAP2b:b1b2Q0deO3O1';W;P1O111xjS0m14ClR2/8kS0nP2PkP2PkC7S0oP0Q0T11skS0pPJPNPNPDPgP5P9fQP8POPEPQPQPnC5F=X=3#<X>DDMS0qP110okS0rfCRG,KJRr%IGRiPgP5P9fRP8POPE14CyRXPXPnC5F=X=3#<X>D,GDS0s':S0tPiQ0sP_PZPTP\P]PAQ0fQ0gP1fGS0u,4CRLPzPlO3b0b1b2b9PieD@W<P1O111okS0vQ0t,:rRvPNQ0]PGP_PZPTP\P]PAQ0JQ0LP110LMPLPMPGO4b0S0wb1b2b9%9rS0xeS0yP_PZPTP\P]PAQ0QQ0RP110L>S0z10LkS0{10LhS0|PLPlO5b0b1b2b9%9iS0}eO3O1';W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WIP1O111^@18uhPuPhPuPhC7P010Rh11RhQ0?P110Ph1KJH%IHS0~PgP5P9fIS10P8POPEPYPYPnC5F=X=3#<X>D,GDS11':Q0~Q11P_PZPTP\P]PAPaP`PbPcPdQ03P6PdANdewS11P6Q05FEP7PIb6b7b8X33X5qS05Q06118@Q0[[[^33^5qS06P110[>S0[9Sm[P[P;PKO4b0bAb?bGQ0~eD@WJP1O111Ph18tmS0~PtPmPtPmC7S12P010SmS1311SmS14Q0AP110YmS15Q0hQ0iP0Q0jQ0kQ0UP1Q0lQ0_Q0DQ0MPlQ0`P_PZPTP\P]PAPaP`PbPcPdAOde{P6PdAOde~R~P6PdQ009NdeS00P6PdQ039AdWRWQ0P5?dDHFEP7PIb6b7b8X33X5qX@qXFqS0P101j108mS03114hR{AX;:hRw12j:S0`/6=12m:S16/6<S173DPf[[[[^33^5q^@q^FqS18P1Q0^Q0b12@QS19PQP;PKPHO7b0b:b1b2Q0deO3O1';W;P1O1Q0mQ0nQ0oP0Q0TQ0pQ0qP1Q0rPrQ0tPiQ0sP_PZPTP\P]PAPaP`PbPcPdQ04P6PdQ0YP6PdP~P6PdQ11P6Q08FEFEP7PIb6b7b8X33X5qX@qS08Q07118j104m11:@PjP;P;PkC5=D=<[[[[^33^5q^@qS0YP112mLS1:Q0z'6S1;12@LS1<Q0|'6S1=PLP;PKPHPlO7b0b1b2b9PieD@W<P1O1Q0vPNQ0]PGQ0yP_PZPTP\P]PAPaP`PbPcPdQ019NdeP6PdP~P6PdQ00P6PdQ049AdpS01Q0O5?d9?dWDHFEP7PIb6b7b8X33X5qX@qXFqS0O111kQ0310:kR~,6=S0yQ175DwPf[\{[[^33^5q^@q^FqS03P1Q0z12jLS17Q1<PLP;PHPzO7b0b1b2b9Q0}eO3O1,;vW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111YmS1>18}>S1?P}P>P}P>C7S1@P0Q0[11[>S1AQ0UP110x>S1BQ0VQ0XPUQ0WP_PZPTP\P]PAPaP`PbPcPdQ09P6PdQ0eP6PdQ11P6Q0:FES0:CgP7PIb6b7b8X33X5qS11Q0;118mR=114@Q0`/6~Q1610:>R~'65D;[[S16[^33^5qS0;P1Q19Q0c'6PQP;PKPzO5b0bCb:b1PUeD@WEP1O111x>S19182jS0`P2PjP2PjC7S1CP010sjS1D11sjS1EQ0qP110ojS1FPNQ0]PGP_PZPTP\P]PAQ0wb:b1b2Q0xeP_PZPTP\P]PAPaP`PbPcPdQ029NdeP6PdQ0eP6PdQ00P6PdQ01Q0NQ095Ad5?d9?dWDHFEP7PIb6b7b8X33X5qX@qXFqS01111>Q0y16<~5DwPf[\{\=[^33^5q^@q^FqS0yP1Q1:Q17Q1<PLPKPHPzO7b0b:b1b2Q0}eO3O1,;vW;P1O111ojS1714CGR=/8kS1:P=PkP=PkC7S0NP0Q0b11QkS09PJPyPyPDPgP5P9fTP8POPEPLPLPnC5F=X=3#<X>DDMS00P110XkS0efFR{,KJRw%I{R~PgP5P9fUP8POPEQ0>,4CS02Q02PnC5F=X=3#<X>D,GDS0w':S1GP~Q0wP_PZPTP\P]PAPaP`PbPcPdQ04P6Q0:CgP7PIb6b7b8X33X5qS0:Q07Q16[^33^5qS07P1fJS16,4CRb,2@S0410bhS1H'6S1IPbP;PzPGO5b0b1b2b9P~eD@W<P1O111XkS1JQ1G,:wRWPyQ0uP{P_PZPTP\P]PAQ0JQ0LP110bMPbPMP{O4b0b1b2b9%9wS0LeP_PZPTP\P]PAQ01Q0yP112mbS0J12jbS1KQ04PbPHPzPlO7b0b1b2b9%9~S1LeO3O1';W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WJP1O1n200110000021110211101b4WIP1O1n200110000021110211101b4WNP1O111F|Q0</8MQ0<PMQ0<PMC7P010VM11VMQ0=P110^M1KJKRVPgP5P9P{P8POPEPPPPPnC5F=X=3#<X>D:03KDP_PZPTP\P]PAPaP`Q0GPcPdAOd?eRFP6PdQ0H9Nd?P6Q0I=AdFFEP7PIb6b7b8X33XH31081Q0K,141R4BP:P:P4C5[[^33^H3P1PSPMP;PKO4b0b?bGbCPVe3vWOP1O111^M18u@PuP@PuP@C7P010R@11R@Q0?P110P@Q0~Q12P0Q13Q14Q0AP1Q15Q0hQ0iP0Q0jQ0kQ0UP1Q0lQ0_Q0DQ0MPlP_PZPTP\P]PAPaP`Q0GPcPdANd?eP6PdAAdpFDHP7PIb6b7b8X33XH3X5qRI1181AX:48Pf[[^33^H3^5qRqP112|QPQPMPzO4b0b:b1b2Q0aeP_PZPTP\P]PAQ0QQ0RP1Q0^Q0bQ0cPQPHO5b0b:b1b2Q0deO3O1';W;P1O1Q0mQ0nQ0oP0Q0TQ0pQ0qP1Q0rPrQ0tPiQ0sP_PZPTP\P]PAQ0ZQ0\P1Q1;PLPKPzO4b0b1b2b9PieD@W<P1O1Q0vPNQ0]PGP_PZPTP\P]PAPIPqP112|LPLPMPlO4b0Rfb1b2b9Q0xeP_PZPTP\P]PAQ0QQ0RP1Q0zQ0{Q0|PLPzO5b0R:b1b2b9Q0}eO3O1,;vW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O1Q1>Q1?Q1@P0Q0[Q1AQ0UP1Q1BQ0VQ0XPUQ0WP_PZPTP\P]PAQ0fQ0gP1PQPKPHO3b0bCb:b1PUeD@WEP1O1Q19Q0`Q1CP0Q1DQ1EQ0qP1Q1FPNQ0]PGP_PZPTP\P]PAPfb:b1b2Q0xeRfP_PZPTP\P]PAP:b:b1b2Q0}eO3O1,;vW;P1O1Q17Q1:Q0NP0Q0bQ09Q00P1Q0ePwQ1GP~Q0wP_PZPTP\P]PAQ0fQ0gP1PbPzPlO3b0b1b2b9P~eD@W<P1O1Q1JPyQ0uP{P_PZPTP\P]PAPIPqP112|bPbPMPGO4b0R:b1b2b9Q0LeRUP_PZPTP\P]PAQ0QQ0RP110b>R410bkQ1HPbPlO5b0b1b2b9Q1LeO3O1,;WW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WIP1O111P@18thPtPhPtPhC7P010Sh11ShQ0AP110YhQ0BQ0FQ0CQ0EP_PZPTP\P]PAQ05Q06P1Q0S9SmsPsP;PKO4b0b?bGbCQ0CeD@WJP1O111Yh18}mP}PmP}PmC7P010[m11[mQ0UP110xmQ0`Q1CP0Q1DQ1EQ0qP1Q1FPNQ0]PGPfP_PZPTP\P]PAQ0PQ18P1Q0zQ0{Q1<PLP;PKPHO7b0b:b1b2Q0}eO3O1,;vW;P1O1Q17Q1:Q0NP0Q0bQ09Q00P1Q0ePwQ1GP~Q0wP_PZPTP\P]PAQ08Q0YP1Q0J/64Q1IPbP;PKPHPlO7b0b1b2b9P~eD@W<P1O1Q1JPyQ0uP{PUP_PZPTP\P]PAQ0OQ03P1P4Q1KQ04PbP;PHPzO7b0b1b2b9Q1LeO3O1,;WW<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WDP1O111xm182>P2P>P2P>C7P0Q0S11s>Q0qP110o>PrQ0tPiQ0sP_PZPTP\P]PAQ11Q0;P1Q1=PLP;PKPzO5b0bCb:b1PieD@WEP1O111o>18=jP=PjP=PjC7P010Qj11QjQ00P110XjPyQ0uP{P_PZPTP\P]PAP:b:b1b2Q0LeP_PZPTP\P]PAQ01Q0yP1Q0JQ1KQ04PbPKPHPzO7b0b:b1b2Q1LeO3O1,;WW;P1O111Xj14C{RX/8kPXPkPXPkC7P0Q0{11LkPJQ0>Q0>PDPgP5P9fWP8POPEPbPbPnC5F=X=3#<X>DDMP1Q02/0kQ10,KJRJQ10#IRbPgP5P9fXP8POPEQ0@,4CREPEPnC5F=X=3#<X>D,GDRn':REPbPnP_PZPTP\P]PAQ0:Q07P1fM,4CRC,2@R@?XChPCP;PzPGO5b0b1b2b9PbeD@W<P1O1Q02/1k1:JEQ0>Q16Q10P_PZPTP\P]PAPIPqP112|CPCPMP{O4b0b1b2b9%9JeP_PZPTP\P]PAQ01Q0yP112mC12jCP@PCPHPzPlO7b0b1b2b9%9beO3O1';W<P1O1n200110000021110211101b4W;P1O1n200110000021110211101b4WEP1O1n200110000021110211101b4WDP1O1n200110000021110211101b4WJP1O1n200110000021110211101b4WIP1O1n200110000021110211101b4WOP1O1n200110000021110211101b4WNP1O1n200110000021110211101b4WXXLDB0>KH<N90?P1C\b\bTbSWUWWWVW_WRX^3X]DW[W`WQo"). Qed.

  (* [comment removed for export] *)
  Lemma log_win_wdl : forall log, log_win_b 0 log = true -> log_wdl_b 0 DATA_RS log = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun ()) ["TRun"] "p'0h01Hh12Heh22H0h31xh42b1h52b2h62opi002oph71ni011nh81bi021bh91ei031eh:5lemmah;2sxi042sxh<7e_addr0h=5e_vali055e_valh>7e_widthi067e_widthh?1ii071ih@1ki081khA2k0hB2loi092lohC3loghD1vhE1whF1yhG1zi0:1zi0;1ai0<6a_basei0=5a_offi0>6e_addri0?1sp;1p;2p;3p;7p;4p;6g008Yj1TTg03HOj2STg03IVj2Mj3JTg02lej3ATg02mAR0j2ITg03J_j2OTg03K=j7NTg02nKj3HTg03K_j1Kj2GTg02mZj3RTg03Lhj37Tg01\Bj1?Tg03N3j21Tg02\Wj26Tg01[9j1CTg01dbj3=Tg03O=j3>Tg03PFj3@Tg03QOj3<Tg01cYj4:Tg03RXj4;Tg01Z2j3LTg00=Uj39Tg02Y6j3FTg00<Bj6PTg00dgR1f0R2g00eGR339p=8g03FHR4f1R5;F2p=Eg00egR6g03GSR7;J2=913p=D1G62=913p=Bf3R8f2R9;75=F42p=Q1189?752,G6=913p=2f4R:/18?795=F42p=01189?7529J67=913p=3A7952,G6p=5P1P9P5g03<bP3P2EPp=4%T41S62#81M67R3=A45#81E29R;%D5R<[^34'Ip-0R=P01O25XF=X3=g03SaAA439#81E28R0P<[^34P2FNW:AH435%K6R3=A45#8%B5R<\;^34R;'IAA439#8P<\0^34;R2W:AH435P2O2P;P9P5P2O2P<P4%B2f7R<,E5%D9]1]0P9g03TWR;P;g00[`R;g02K^R3A7952#BP8P9P5f=R>CQA7:89#D]1]0]=]>P2g00[BR?P8P9P5P2C2P:P8P9P5f@D0P3P2f5R@P:P8C2P5f6RAP@P:fCD0P9P<PAP@C3]1]0P@%?2PAP@P:C2%?5P<PAP@fDRBD0%?9f8RC'1?5<AP1P=P2g02hMR=g01L=n0110200020000X91RD;45P=%?8f9REPCP<C3/62b2W1W0XG?P2O1%C2PAP@P:C2%C5P<PAP@PBD0P5%C9PCP<PAC3eW1W0X7;P2O1g03UaR<A=952f:RBPEPCC2A=895f;RFPBPEfHRGD0A=:89f<RH'1?5FB?4D5P=A=@:8P>PHPFC3/62b2W1W0X53X43W6P9P5P2O3A>952PBPEPCC2A>895PFPBPEPGD0A>:89/1H?5FB?4D5P=A>@:8P>PHPFC3/62b2W1W0X53X43X6<P9P5P2O3g03VMR<A@952PBPEPCC2A@895PFPBPEPGD0A@:89/1H?5FB?4D5P=A@@:8P>PHPFC3/62b2W1W0X53X43W6P9P5P2O3A<952PBPEPCC2A<895PFPBPEPGD0A<:89/1H?5FB?4D5P=A<@:8P>PHPFC3/62b2W1W0X53X43X6<P9P5P2O3P8P9P5P2C:PHPFPBC2P:P8P9P5C:P>PHPFfJR<D0P@P:P8P9C:f>RG'1?5>H?4D5P=PAP@P:P8C:f?REPGP>C3/62b2W1W0X83X7;XB;X;1P8P9P5P2O4P8P9P5P2C;PHPFPBC2P:P8P9P5C;P>PHPFP<D0P@P:P8P9C;/1G?5>H?4D5P=PAP@P:P8C;PEPGP>C3/62b2W1W0X7;X??XA;X;1P8P9P5P2O4n0110300081010:101013010010;1023010010;1023010010;1023010010;1024010410910110340104108107101P5P2O2W1W0XD3XE;W@X83P5P2O2n0110?00012110<10=W<P9P5P2O3n0110?00013110>106105P2P5O2b0X10X94b0O2AL675#8eW0WCo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition slotsM (vals : list word) (buf : word) : Prop := slotsR vals buf /\ vals_ev vals 13 = Z_to_bv 64 calls.

  Definition at_tm (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 46%nat -> slotsM vals buf ->
      regs_ok (ENV vals) sr_TM R -> know_ok RSEGS (ENV vals) M kn_T ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data -> (L < cap)%Z -> (6 + cfg <= L)%Z -> (0 < paylen)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xfa4b4) M (seg_rom RSEGS)) (model2 vm)) K.

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
    unfold model2, O23ReadLoop.model2.
    assert (R10 : getr R 10 = Z_to_bv 64 paylen) by (regv HR (10 : reg); cbn [edenot ev ENV O23Open.ENV]; rewrite P9; reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x62e50) by (regv HR (1 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x123d20) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV O23Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    assert (EQcfg : mkst R (Z_to_bv 64 0xfa4b4) M (seg_rom RSEGS) = mkst R al_malloc_pc M al_rom) by (rewrite AL_malloc, AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC O23Open.fds0 vm stdin0 fs0 None (Some tid) None).
    destruct tm_itin as (I2 & R2s & VLKT & VLS2 & VLK2 & SR3 & KN3 & VLK3 & I3 & IX & S19).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (alloc_margin_le paylen) as HMG. pose proof calls_rng as Hcalls.
    pose proof (need_lo FUZZ_CALLS FUZZ_BMAX j cap HFC0 ltac:(clear -HFB0; lia) Hj10 ltac:(change (2 ^ 26)%Z with 67108864%Z; clear -Hcap26 Hc0; lia))
      as (HNK & HNB).
    eapply (ai_malloc_sure fx0 A M md R paylen (need_k FUZZ_CALLS j) (need_b FUZZ_BMAX j cap)
              (Z_to_bv 64 0x62e50) sp0 [a0s; path] envv K HI).
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
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV O23Open.ENV] in Hst. rewrite P0 in Hst.
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
        - cbn [kentry_ok edenot ev ENV O23Open.ENV]. rewrite A56. lia.
        - subst vals2.
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            pose proof (know_after_allocT A A' vals M m' vm vm' regs' kn ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLKT) HK HI Htop HI' Htop') as HK5 end.
          specialize (HK5 ltac:(intros a H1 H2 H3 H4; apply Hfr; try assumption; rewrite R2, u_small by lia; exact H4) Hgr).
          rewrite KNT in HK5. match goal with |- ?g => idtac g end. exact HK5. }
      clear HK. rename HK2 into HK. clearbody vals2. clear KW R10 R1 R4 R2.
      run_blk_keep scr0 78%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      assert (MC : mcH m' res (Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) paylen payload).
      { assert (NW : (bv_unsigned buf + 6 + cfg + Z.of_nat (length payload) < 2 ^ 64)%Z) by (rewrite Hplen; lia).
        constructor; rewrite ?u_small by lia; try lia.
        - pose proof (u64_range buf). match goal with |- ?g => idtac g end. exact (bytes_at_rdn m' (bv_unsigned buf + 6 + cfg)%Z payload ltac:(lia) NW HP').
        - apply store_ok_of_all; [lia|]. intros x Hx. unfold wview.
          destruct (m' x) eqn:EM; [discriminate | exfalso; exact (HsomeN x ltac:(lia) EM)]. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (B1 : getr Rc 1 = Z_to_bv 64 0x62e64) by (regv HR (1 : reg); reflexivity);
        assert (B10 : getr Rc 10 = res) by (regv HR (10 : reg); cbn [edenot ev ENV O23Open.ENV]; exact A56);
        assert (B11 : getr Rc 11 = Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) by (regv HR (11 : reg); cbn [edenot ev ENV O23Open.ENV]; rewrite Q12; reflexivity);
        assert (B12 : getr Rc 12 = Z_to_bv 64 paylen) by (regv HR (12 : reg); cbn [edenot ev ENV O23Open.ENV]; rewrite Q9; reflexivity);
        destruct (ref_memcpy m' res (Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) paylen payload (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x62e64)
                    ltac:(apply ret_ok_even; reflexivity) B1 B10 B11 B12) as (Rm & Hms & Hkeep);
        clear B1 B10 B11 B12
      end.
      replace (Z_to_bv 64 1088688) with (0x109cb0 : word) by (apply bv_eq; reflexivity).
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
        pose proof (know_ok_call RSEGS (ENV vals2) m' M2 [(0x1000, 0x10000)%Z] 0 0 IHI 0x113000) as KC;
        specialize (KC ltac:(cbn [ev ENV O23Open.ENV]; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
        specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HK3; clear KC
      end.
      assert (OUT2t : forall x : word, ~ touched (ENV vals2) [(0x1000, 0x10000)%Z] 0 0 IHI (bv_unsigned x) -> M2 x = m' x).
      { intros x Hnt. apply OUT2. unfold touched, IHI, WIN in Hnt. cbn [ev ENV O23Open.ENV] in Hnt. rewrite Q0 in Hnt. intros Hx. apply Hnt.
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
      + unfold slotsT, O23Hdr.slotsR. rewrite !vals_ev_map by (cbn; lia). cbn [nth tl_rvlm rvl18 app tl tm_sr3 edenot ev ENV O23Open.ENV].
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
    unfold model2, O23ReadLoop.model2. unfold tr_shape.
    assert (CZ : forall b, bv_eqb (Z_to_bv 64 cfg) (Z_to_bv 64 0) = b <-> (if b then cfg = 0 else cfg <> 0)%Z).
    { intros b. unfold bv_eqb. rewrite !u_small by lia. destruct b; [apply Z.eqb_eq | apply Z.eqb_neq]. }
    assert (PZ : forall b, bv_eqb (Z_to_bv 64 paylen) (Z_to_bv 64 0) = b <-> (if b then paylen = 0 else paylen <> 0)%Z).
    { intros b. unfold bv_eqb. rewrite !u_small by lia. destruct b; [apply Z.eqb_eq | apply Z.eqb_neq]. }
    assert (GO_M : forall rvl Rx Mx, (0 < paylen)%Z ->
      length rvl = 46%nat ->
      (forall i, (i < 13)%nat -> nth i rvl (ELit 0) = EVar i) -> edenot (ENV vals) (nth 13 rvl (ELit 0)) = Z_to_bv 64 calls ->
      regs_ok (ENV (map (edenot (ENV vals)) rvl)) sr_TM Rx -> know_ok RSEGS (ENV (map (edenot (ENV vals)) rvl)) Mx kn_T ->
      side A vm Mx buf cap j -> bytes_at Mx (bv_unsigned buf) data ->
      realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0xfa4b4) Mx (seg_rom RSEGS)) (mkModelC O23Open.fds0 vm stdin0 fs0 None (Some tid) None)) K).
    { intros rvl Rx Mx Hp Hlen Hid H13 HRx HKx HSx HBx.
      apply (tm_step K j buf cap HTL A vm (map (edenot (ENV vals)) rvl) Rx Mx); try assumption.
      - rewrite length_map. exact Hlen.
      - split; [repeat split|]; rewrite vals_ev_map by lia; rewrite ?Hid by lia; cbn [edenot ev ENV O23Open.ENV]; try assumption. }
    assert (GO_L : forall rvl Rx Mx, paylen = 0%Z ->
      length rvl = 50%nat ->
      (forall i, (i < 13)%nat -> nth i rvl (ELit 0) = EVar i) -> edenot (ENV vals) (nth 13 rvl (ELit 0)) = Z_to_bv 64 calls ->
      nth 14 rvl (ELit 0) = ELit A_EMPTY -> nth 15 rvl (ELit 0) = ELit 0 -> edenot (ENV vals) (nth 16 rvl (ELit 0)) = Z_to_bv 64 calls ->
      regs_ok (ENV (map (edenot (ENV vals)) rvl)) sr_TL Rx -> know_ok RSEGS (ENV (map (edenot (ENV vals)) rvl)) Mx kn_TL ->
      side A vm Mx buf cap j -> bytes_at Mx (bv_unsigned buf) data ->
      realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x62ea4) Mx (seg_rom RSEGS)) (mkModelC O23Open.fds0 vm stdin0 fs0 None (Some tid) None)) K).
    { intros rvl Rx Mx Hp Hlen Hid H13 H14 H15 H16 HRx HKx HSx HBx.
      apply (HTL fx0 A vm (map (edenot (ENV vals)) rvl) Rx Mx (Z_to_bv 64 A_EMPTY) (Z_to_bv 64 0) fp_frm_zero_fx0); try assumption.
      - rewrite length_map. exact Hlen.
      - split; [repeat split|]; rewrite ?vals_ev_map by lia; rewrite ?Hid by lia; rewrite ?H14, ?H15; cbn [edenot ev ENV O23Open.ENV]; try assumption; try reflexivity.
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
      cbn [sc_denot branch_taken edenot ev O23Open.ENV]; rewrite ?P8', ?P9'; unfold bv_eqb; rewrite !u_small by lia;
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
        (intros i Hi; rewrite OUT1; [apply HB; exact Hi | unfold O23ReadLoop.in_win; rewrite u_small by lia; lia
                                                   | unfold O23ReadLoop.in_data; rewrite u_small by lia; lia]));
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
