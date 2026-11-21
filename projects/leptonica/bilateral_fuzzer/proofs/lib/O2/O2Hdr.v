(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy; p0 and p1 without the stack pointer; the exit tactic's thread-pointer and thread-id addresses corrected to this binary's). *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2ExitBase O2StdioDefs O2Exit O2Startup O2StartupDefs O2StartupFacts O2MainEntry O2LibStdioCall O2OpenFail_defs O2OpenFail_tail O2OpenFail_tail2 O2Open_defs O2Open O2Oom_defs O2Oom O2MemPreds O2Malloc65536 O2DirRead_defs O2ReadLoop_defs O2ReadLoop O2Grow O2Hdr_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Hdr () := "C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive03C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr9MSG_SHORTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr;MSG_OVERRUNC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List:in_map_iffC47Corelib5Lists7ListDef3seqI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib2O2:O2Hdr_defs4zseqC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List7forallbC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallc59OSSVerify5KrLib2O25O2Hdr7in_zseqC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib2O2:O2Hdr_defs4cfgFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib2O2:O2Hdr_defs8cfgF_tabC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc59OSSVerify5KrLib2O25O2Hdr6hdr_b0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr6hdr_b1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr6hdr_b2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc65536<ownedA_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop9buf_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop5al_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop5vm_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc655366env_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_free_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega7EnvRing5PExpr05C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr=ownedA_rangeHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open3ENVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2GrowAknow_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O2;O2StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O2;O2StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun=ext_val_zx_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib2O2;O2StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2O2;O2StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase7ai_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Room6need_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open4fds0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6STOPSHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5f_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5f_sr2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5sr_F2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5kn_F2C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6f_itinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs4f_r1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5f_kn1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6f_kn2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs4f_r2C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2O2>O2MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2MallocLayout6LS17okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2O2:O2Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;is_kimg_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsC47Corelib4Init5Logic9False_indK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop5slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop4sideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop6model2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic7f_equalK47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib6Common9CliDriver7SymCall8log_wd_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop=side_block_wdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop6in_winC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr<kimg_rdn_msgC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes?pair_equal_specC59OSSVerify5KrLib2O2;O2MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_wZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib6Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_exit_has_nilC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O2;O2StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop:alu_add_wZC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib2O2:O2ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop:side_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop:side_blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib2O2:O2ReadLoop;vals_ev_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer2rvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4emapC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer<regs_ok_xferC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXferDknow_ok_xfer_entailsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr8msg_tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall7sc_bufpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall8sc_bufszC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2LibStdioCallCstdio_call_sound_frC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_srSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_knSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr=MSG_SHORT_lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib2O2?O2ReadLoop_defs4sr_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5kn_MLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9msg_shortC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c59OSSVerify5KrLib2O25O2Hdr=msg_short_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs7h_itinSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs4h_rSC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_scSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_rS2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6f_rvlSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6h_srS2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6h_knS2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs7STOPSH2C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC69OSSVerify5KrLib6Common9CliDriver<LibKnowFrame<rdn_1_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun;kword_introC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat;le_preorderc59OSSVerify5KrLib2O25O2Hdr8cfgF_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr=cfglen_x_cfgFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr6b0_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr6b1_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs8cfglen_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ReadLoop9slots_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr>kwordv1_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5kn_H6C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr6b2_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr:hdr6_entryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr8cfgx_valC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib6Common9CliDriver<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_srOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_knOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr?MSG_OVERRUN_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec;msg_overrunC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr7cfg_rngC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c59OSSVerify5KrLib2O25O2Hdr?msg_overrun_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs7h_itinOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs4h_rOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_scOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_rO2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6f_rvlOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6h_srO2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs6h_knO2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_0_lC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_Zc59OSSVerify5KrLib2O25O2Hdr7at_trunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4extzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr?bytes_le_to_Z_1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_nextC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv3Sem7mul_divC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib2O2:O2ReadLoop8md_mul_ZC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3mulC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7div_1_rC56Stdlib6ZArith6BinInt1Z7pow_0_rc59OSSVerify5KrLib2O25O2Hdr6slotsRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5r_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5b1s_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs7h_itinKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs4h_rKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs8paylen_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5pay_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_srKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs4sr_RC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs5h_knKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Hdr_defs4kn_RC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00c59OSSVerify5KrLib2O25O2Hdr<header_shortC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr>header_overrunC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr9header_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O25O2Hdr9hdr_shapeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPSH scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSH scr NX true.
Tactic Notation "run_blk2_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSH2 scr NX true.

(* [comment removed for export] *)
Ltac close_exit_gen HR HK P0 Hh Hlazy sp0 OFF WLO WP2 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
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
      | regv HR (10 : reg); reflexivity
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

Definition MSG_SHORT : list byte := msg_short.
Definition MSG_OVERRUN : list byte := msg_overrun.
Lemma MSG_SHORT_len : length MSG_SHORT = 31%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) [] "p;1p;2p-1p10000p4p710p8g000Pj11Tg000oj22Tf0R0#1#1p=3%10#1#1#1p=0g001Ig001h#1#3#0#0#0#0#0#0#0'2o"). Qed.
Lemma MSG_OVERRUN_len : length MSG_OVERRUN = 31%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) [] "p;1p;2g000Pj11Tg000oj22Tf0R0#1#1p=3%10#1#1#1p=0g001Ig001h#1#3#0#0#0#0#0#0#0'2o"). Qed.
Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x121c9) 31 = Some MSG_SHORT.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) [] "p;1p;2p;4p;3p-1R0p1002Gp4p710p9P0p1002jp4p710p9P0p1003VR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10044p4p710p9p1004lp4p70p1005\p4p710R0p8p1006:p4p70R1p1006hp4p7210p8P1p1007Dp4p710p8P1P0p8p1007`p4p7210P0p8p1008Lp4p70P0p8g009Bj10Tg009gj1@Tg00:Ej1=Tg00:hj1BTg00;Hj1ITg00;jj11Tg00<Oj29Tg00=Bj1;Tg00=`j1ATg00>@j2?Tg000oj2HTg00>bj1GTg00?Dj2FTg000Pj16Tg00?jj4DTg00@bj3CTg00A<j3>Tg00A_j3<Tf0R0#1#;p=4%00#;p=5%00#0p=8f3R1f2R2f1R3/903>p=3f4R4A>123;<0p=:A<2309<41p=2%60#6p=E%60#6#6#6p=7g00B?R0#0R4#0R1#0R3#@R2#=R5#BR6#IR7P5P2%10R0#0R8#0R9#0R:#1#4R;192;P5P2%18R8#1R;#0#5R<192<P5P2%88R8#4R<P2P<C3R<P5P2%10#0R0#1#0R=#;R>P2P>C3P5P2%83R3#;R>P2P>C3R>P5P<P5P2%1;R;#5R<P2P<C3R<P5P2%00R0#0#5R?P2P?C3P5P2%4=R?192?P5P2%5=R=P2P=C3R=P5P>P5P2%10R0#4R?192?P5P2%58R8P2P8C3R8P5P2%4;R;P2P;C3P5P2%50R0P2P0C3R0P5P=P5P2%19#0R9#4R;P2P;C3R;P5P0P5P>P5P=P5P8P5P2%0:#4R:P2P:C3R:P5P<P5P>P5P8P5P;P5P:P5P2%59R9P2P9C3P5P;P5P0P5P2%14#5R41924%A5D:D2D2D2D2D2D2D2D2D2D:D2D:D2D2D2D:D:,?6'Hg00Bd%03#@R3#=%G5U%11#8#8#1#1#1#8#1#8#4,F3g001h#6#E#7#7#7#7#7#7#7CDg00DJ,?65C7do"). Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10bde) 31 = Some MSG_OVERRUN.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) [] "p;1p;2p;4p;3g009Bj10Tg009gj1@Tg00:Ej1=Tg00:hj1BTg00;Hj1ITg00;jj11Tg00=Bj1:Tg00<Oj29Tg00=`j1ATg00>@j2?Tg000oj2HTg00>bj1GTg00?Dj2FTg000Pj16Tg00?jj4DTg00@bj3CTg00A<j3>Tg00A_j3;Tf0R0#1#:p=5f3R1f2R2f1R3/903>p=2%00#:p=4%10#1p=8f4R4A>123;;0p=<A;2309;41p=3%60#6p=E%60#6#6#6p=7g00B?R0#0R4#0#0R1#@R3#=R2#BR5#IR6P2P3%10R0#0R7#0R8#0#1#5R9P3P9C2R9P2P3%17R7#1R:#0#4R;P3P;C2R;P2P3%07#0#5R7P3P7C2R7P2P3%10#0R0#1R<#0R=#:R>P3P>C2P2P3%01R1#0R>#:R?P3P?C2R?P2P9P2P3%1:R:#5R9P3P9C2R9P2P3%4:R:P3P:C2R:P2P3%18R8#1R@#4RA193AP2P7P2P3%5@R@P3P@C2P2P3%14R4#1#8#5R@193@P2P;P2P3%08#5R8P3P8C2R8P2P:P2P?P2P9P2P3%1<#4R<P3P<C2P2P8P2P3%00R0#1R8#4R<P3P<C2R<P2P<P2P3%5=R<P3P<C2R<P2P:P2P3%58R8P3P8C2P2P?P2P7P2P:P2P3%00#4R0P3P0C2P2P<P2P3%4=R=P3P=C2P2P3%44R41934%A2D<D3D3D3D3D3D3D3D3D3D<D3D<D3D3D3D3,?5'Hg00Bd%0>#@R>#=%G2U%11#0#8#8#0#8#8#4,F>g001h#6#E#7#7#7#7#7#7#7CDg00EA,?55C6do"). Qed.

(* [comment removed for export] *)
Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) [] "p'0h04__x1h14__x2h21xi001xh31Hh41nh54__p1h63lenh75starth87__arithh94__ffh:8__varmaph;5__with<4cstrh=2H0h>2Hkh?4__p2h@4__x3hA1zhB2z0hC3Hk0hD2HzhE5cstr0hF1khG5lemmahH1yp&0p;3p;1p;2p;9p;5p;6p;4p;<p;Bp;7p;8g00F:j3ITg00FQR0j11Tg00G1R1j20Tg00GLR2j2\Tg00GfR3j2bTg00H?j2jTg00Hkl9fTg00Iek50;Tg00JDj2KTg00J`R4j2@Tg00K:j2>Tg00KQR5j2?Tg00Kij3yTg00LDR6j2GTg00LaR7j2<Tg000oj2NTg00M=j6cTg00Mfj4pTg00NMj1JTg00=`j1mTg00:hj1lTg00O2j2XTg00OPj1kTg00Onj4WTg00PLj1iTg00Pjj1hTg00QUj2gTg00R8j2MTg009Bk10:Tg00R[k309Tg00>bk108Tg00S>k204Tg00S`k203Tg00@bj3Rj1zTg00TLj3~Tg00Tkj4}Tg007Dj6|Tg00U]R8j1_Tg00V=j2CTg00VZj1xTg00W8l<PTg00W]j2]Tg00X?R9j2BTg00X[j2FTg000Pj1HTg00Y5j2DTg00Y^j1vTg00Z<j2uTg00Z]j3[Tg00[Fj4VTg00;jj1tTg00\1j4^Tg00\Lj4sTg00\fj1rTg006hj4qTg00]]lB{Tg00^Cj4STg00^nk700Tg00_Rk701Tg00`6k802Tg00`Zl<dTg00a?j3oTg00ahj2nTg00A_k305Tg00bTk606Tg00c8k707Tg001hR:f0R;'Kp=:g001IR<g00c\R=P0P;Cqp=ef1R>=R=;p=2AI<>;p=5g00d:R?/B;p=3f2R@1<>;'0p=61N=;p==P<P=P4P0P9g00dXP:P?f3R9P@P>P;M<Pp=ZP<P<P<P=P=P=g00e:P0P0P0P6g00eZP:P?P9P@P>P;MB{p=UP<P=P5P0P7g00f=f5R7f4R5P9P@P>P;M<Pp=`P=P>g00f_P;CSp=EP>g00gFR6g00geR4P4g00hERAP;g00heK00p=4P=P>g00iEP;CSp=LP@P6P4P4PAP>P;K01p=7P9P6P4P4PAP@P>P;L02p=AP=P<P=P=P8P5P0P9g00ilP@P>P;M<dp=TP<P=P=P=P0P0P7P5P9P@P>P;M<dp=wAR=;?p=OAo=>;p=8g00jY,n;p=;g00kER8@05>;p=9P>P6P4P4PAP;J06p=YP=P>g00l1P;CSp=QP@P6P4P4PAP>P;K07p=a%:>R6#e9I=;%1;RB/2>%:@RC,5;'0X2<,\<RD'bp-0REP3g00lX%eC9I=>12B@%:9,5;'0X2<R3,\<RFP;%3>RG%1@RH76>RIPI1jEIM9fWGP<P=P0P6P;I0;PI\D%3;RI%1>R676;R0PF[P2P<P3%3@R2%19RF76@P;12B5%:7,5;'0P11267f6R6#:,5>%36f7RJ#1RK766P;12FJP=%15f:#:,57f;RL#1RM96G>[XA=f9#:,55P11K>@,5;1@@>1>@9,?>'0RN[RO1@>;1>>@,?;'01K@9,5>RP[RQ1@9@1>95,?@'0\PAy@>;RPP>n2001000000120000000X4<X7<X6<PO^4<^7<^6<P;PLP:P6P>O41@:61>:L,?6'01@:JRLf<RR,>:RS,?JRT'0%3KRU%1RRV,G?RW,<KRX'0RYPLPTPUPX1N=?RXPJPK%=KRUCZPJPKPUPSPWPXPRPV%=VCUE`EcP;CpPYf8RY#J%1Y#3f>RV#J%1V#3%m8RV%l8R8P=1X=@RRP>%k=CWRW%i=RS%h=RU1g=?RJg00B?RT,M=RL'E,4URZ&0:T,M=R[:09=J,LL,4U57UR\&084R41LL[,4U97UZCA204UARAP;P@g00mIRZg00miR]'N203;@=RZ]dA~=?>C}R]b9b:b;X0=X1=1G?>96I;A6G>@[^0=^1=P;f@#1PMP9O3b8bEb<bCb>b3W>PYP;E|W3P>P;O2n2001000000121000000W3XF<P>P;O2n2001000000121100000X3DP<P3%_>R3%13RD/2>RY153CPY1C?>RY/2>P=P=%z=RCP;X2=RMPC12>;#xXH=X2=PDPYPMPM%=BX2<P3PYPM1C?;X2=RYP>P>%=>R3DTEwP>P>P3M<P%J@%3H1]?@1<?@RH1C?@R3/2@'01B@?%O3'0'F1C?9RBP=%H:RD#HRC,D=RG1D=D1D=:RD'8RI'8RZ#;%HCRC,D=R^%vT,u=R_=[=G/8DRG'8#;%;G/9V'9'9P8PWPSPU1YU51QL[,4URW57U1E[J,4U1QLJ,4URG57U5aUP4PU1EJ[,4U1YU7R`57UP4PWCACAPAP]b9b:b;X0=X1=X5EX?E12;>,0@1B>?%O;RW'0'F102512@9[[^0=^1=^5E^?EP;%16,<71<?7P7P>P@P5O6b8bBb=b<CVP1POPQ1K95,5@\NPPP;n2001000000120000000X4<X7<X6<PQ^4<^7<^6<P;P9P:%_@RQ1@:QRP1>:9R:,?QRN'0%33RO1G?FR1,<3Ra'0PPPNPOPaPXPQP3PMPYP@P@%=@DTRYCZPQP3PYP:P1PXP9PF%=FCUE`Ec%J9%3F1]?91<?912B9'01B9?%OB'0'F1C?5P=18^Z#;A[=_^/8DRD#;%HC,D=/8D#;18^I#;/9V'9'9'9P8P=PRP>1X=9CWPSPU%tT,M=RT,LJ,4U1QLT,4U57UA7U`G5aUP4PU1EJT,4U1LT[,4U57UP4P\CACAPAP]b9b:b;X0=X1=X@=X5E12;@,0H109W'F%39?69@1G?9962@[[^0=^1=^@=^5EP;1B6?P6PKP>P@P7O6b8bBb=b<CVO4b3C^CsXD0C^O2%r>9I=;/b0eXA=X4<o"). Qed.
Lemma cfgF_val : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) [] "h02b0h11Th21xh37__arithh44__x1h52b1h61nh71Hh84__ffh98__varmaph:5__with;2Hah<6__sat2h=2b2h>5lemmah?1mh@2H0hA2H1hB6__sat3hC6__sat4hD1yhE1zp;1p;2p;3p;6p;4p;<p;7p;8g009Bj1DTg00=Bj1ETg00LaR0j21Tg00G1R1j23Tg009gj1mTg00?Dj24Tg00nIj27Tg00nfj28Tg00\fj1yTg00oCj3BTg00F:j3CTg00Gfj2UTg00o_j3OTg010Pj3RTg00FQR2j1PTg0113j2LTg000oj2=Tg011hj3WTg00VZj1bTg00M=j6JTg00=`j1`Tg00:hj1_Tg00O2j2^Tg00PLj1]Tg00Pjj1\Tg00QUj2FTg00R8j2[Tg00^Cj4ITg00>bj1ZTg00S>j2xTg00S`j2wTg00TLj3vTg00Tkj4uTg00[Fj4XTg012Nj4VTg012ij2rTg00:Ej1ATg00@bj3@Tg013Ij29Tg0143j3qTg014Wj2TTg015Nj2STg015nj2QTg00OPj1pTg016_j3lTg017Fj2kTg017nj2hTg018Kj3gTg018oj3iTg019Rj2jTg01:bj4fTg005\j6nTg00X?j2oTg00LDj2NTg000Pj10Tg00`Zl<eTg00W8l<dTg00^nj7cTg00_Rj7sTg00`6j8tTg00d:R3f0R4'op=2%D4#Dp=>f2R5f1R6/T4'9p=:1N56/S4p=5%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=;g00mIR7g00miR87@4p=6g001IR9g00c\R:P:P:P2P2f5R2f4R;f3R<P5P6P4M<ep=aP:P:P0f7R=P0f6R0P2P;P<P5P6P4M<dp=KP6g00gFR>g00geR?P?g00hER@P4g00heFcp=?P:P6g00iEP4CIp=GP5P>P?P?P@P6P4Fsp=HP<P>P?P?P@P5P6P4Gtp=YA@:64p=<1764,N5p=M%26R>g00B?RA#DRB#D#>#>RC#>RD#ERE,16'3RFg01;>%mCRG14G4RH14G63:17E6%DD#>#>#>#ERD554'8X0:g001h#;#;#;#;#;#;#;#;RI#yRJ5B:X5:RK=B:J#6RLAC:4JRMPKP6O1#6[^2:RN,ULAOLN4W>AR:KJP4O2PNP4P;AC:;J%22%PIRN,12'3[%2;RK11;NRL'3ROAC:2J[1LI;PO11;ERP,3KPKPLPKPPp-0RP/=K9WKKP4X2:RK1164#bXD:X2:RLP;P;1=:;PNPEPKPK%P4,=:X29PIPE1=:EEaR9GKEJg00kERQ#`RR%_QRQ1^:6RS%]:RT%\:RUP:1F:3RVg00f_1[:ARACI,?URW1F:E,GA,?U5HURX%Z?R?PXCY1xU@R@P4P51=781w45#6dAv:36CuR8b8b9b:X4:R7%24RX114E'3PF[^4:RYP4P2P<O2b3CXPOeCVO214G29:GH17E2=54D'8X0:=B:J#614G0R29:GH17E0RO=54D'8X0:RZ=B:J#6f8R[,4GR\9:GH17E[R]=54D'8X0:P6O1#6\M^2:R^'U14G=R_9:GH17E==54D'8X0:=B:J#6f9R`,4GRa9:GH17E`=54D'8X0:P6O1#6\M^2:;O4W>AR:ZJP4O2P^P4P=AC:=J%2[11[N'3[%2=R^11=NRZ'3RMAC:[J[1LI=PM11=ERI,3^P^PZP^PI1=P^9W^^PKPLP=P=1=:=PNPEP9GKEJP7PYP4P[P0O2b3CXPMeCVO2A:G_2A5=OD'8#6P11864#61<56[RO1<641856#6R=[1<<5\=1r64P6n2001000000120000000X?:X6:PO^?:^6:P4A:Ga\RaA5`]DR`P6O31<a`g01<9R`%A4Ra%A6R]P1%A5?@6419<519<6'<R1[19561954'<%A<?@56[R\%A;?@<5\1Aq564P4n2001000000120000000W=W5W6P\^=]^5a^6`P4PGf;R`,4Gf:Ra,4G'TR]AM`EaRa/SDR\,4GR5P:P\f<R117E`;5D,4G,9G,<4XE:P:19G5P\1QaD%2a%2DR5f=R`17E1;5D#2[[PRPQ%p:PT1F:DR1,GV,?UP@P8b8b9b:113DP4b3b<9laD%2\11\D'3%EBRB%ECRC'k113B%2C1hBCRa,13[[%2BR3g01<WRVAgBC6UW;%2a\V^;3f>?ME`R`/QD%2`f@f?,7E;5DRE#2\5[PRPQPSPTPU1GA1,?U9HUWP?1F:B=i:G,GA,?U9HUWCYP@P8b8b9b:X4:114D,3X116a,3>[^4:P4PEP;O2b3b<bBbCb7,j\Cf19G]P6EnO4b7b1b7b1b1b1b1b1XAFW@X5:X0:o"). Qed.
Lemma cfglen_x_cfgF : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_x = cfgF (vals_ev vals 41) (vals_ev vals 42).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) [] "h02blh14valsp;1p;2g009Bj11Tg009gj16Tg00:Ej14Tg00:hj13Tg000Pj10Tg01=3j25Tg014Wj28Tg000oj27Tf0#0#0#0#0#0#0#0#0p=2g00B?#1#1#1R0#1#1#1#6#4R1#3%60#4#3#3f1R0g001h#0#2#2#2#2#2R2'5%02,50'8,71W0W1o"). Qed.

Section Hdr.
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

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := O2Open.ENV a0s path.
  Let L : Z := Z.of_nat (length data).
  Let model2 := model2 tid fs0 stdin0.
  Let at_header := at_header sp0 a0s path envv tid mem0 fs0 stdin0 lim data.
  Let side := side sp0 mem0 lim.
  Let slots := slots sp0 a0s path envv tid.

  (* [comment removed for export] *)
  Definition hdr_b0 : Z := bv_unsigned (nth 0 data (Z_to_bv 8 0)).
  Definition hdr_b1 : Z := bv_unsigned (nth 1 data (Z_to_bv 8 0)).
  Definition hdr_b2 : Z := bv_unsigned (nth 2 data (Z_to_bv 8 0)).
  Definition hdr_cfg : Z := ((hdr_b0 + 256 * hdr_b1) mod 32768)%Z.
  Definition hdr_b1s : Z := bv_swrap 8 hdr_b1.       (* [comment removed for export] *)
  Lemma b0_rng : (0 <= hdr_b0 < 256)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "h02Hah14__x1h21Hh37__arithh44__ffh56__sat3h66__sat4h76__sat5h88__varmaph95__with:4cstrh;5heq_Lp;1p;2p;4p;3p;7p;8g009Bj11Tg009gj1=Tg00:Ej1JTg00?Dj2ATg01>7j4XTg01>Sj2UTg013Ij28Tg01?Fj1CTg00Laj22Tg00G1j23Tg0000j2?Tg00FQj1>Tg000oj2<Tg00@bj3:Tg00NMj1VTg00=Bj14Tg00;jj19Tg017Fj2TTg017nj2MTg018Kj3LTg015nj2KTg015Nj2ITg00=`j1HTg00:hj1DTg00O2j2ETg00PLj1FTg00Pjj1GTg00QUj2;Tg00R8j2BTg00^Cj46Tg00_Rj7@Tg00>bj1NTg00`6j8OTg00S>j2PTg00S`j2QTg00TLj3RTg00Tkj4STg00X?j25Tg00^nj7WTg00d:R0f0R1'5p=0f1R2g00gFR3g00geR4P4g00hER5P1g00heFWp=7g00B?R6#1R7#1#1R8#=R9%J9R:g001hp,4dataR;1A90CXR<'U189<R<#0%C9,2<'3g00c\R91?:;R;#>R:'<p,1L=:9:R=eP=%V;%0:%47R:%97#9#1#4R7'T120:%071M:7R;,20[[%0:R=g01<WR>AL:72UW0%0;\>^0=%18R8#1#1R=#=p,3sp0'8R>%48R8'K%0>%081I>8#0[[g00kER8#H%D81E92%F9%G9R8P3P4P4P5P8P3P4P4P5P91;90g00f_1B96R6C6,78P9P6g00iE%1=#1#4R=,;9C6,78F@R6%N4P6GO1P85P1f2R8g00mIR5g00miR6'<1Q18=:56dAR902CSb4b8b9X19%01121='3%02122='3[^19P1P<f6O2b3b5b6b7b:b;b2g01?oR<,5012<='3eo"). Qed.
  Lemma b1_rng : (0 <= hdr_b1 < 256)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "h02Hah14__x1h21Hh37__arithh44__ffh56__sat3h66__sat4h76__sat5h88__varmaph95__with:4cstrh;5heq_Lp;1p;2p;4p;3p;7p;8g009Bj11Tg009gj1<Tg00:Ej1GTg000Pj1ATg00?Dj2YTg01>7j4VTg01>Sj2OTg013Ij28Tg01?Fj1BTg00Laj22Tg00G1j23Tg0000j2>Tg00FQj1XTg000oj2;Tg00@bj35Tg00NMj1UTg00=Bj14Tg00;jj1:Tg017Fj2NTg017nj2MTg018Kj3LTg015nj2FTg015Nj2ETg00=`j1DTg00:hj1CTg00O2j2HTg00PLj1ITg00Pjj1JTg00QUj26Tg00R8j2KTg00^Cj47Tg00_Rj7@Tg00>bj1?Tg00`6j8PTg00S>j2QTg00S`j2RTg00TLj3STg00Tkj4TTg00X?j2=Tg00^nj7WTg00d:R0f0R1'=p=0f1R2g00gFR3g00geR4P4g00hER5P1g00heFWp=9g00B?R6#1R7#1#1R8#<R9%G9R:g001h#Ap,4dataR;1Y90CVR<'O189<R<#0%B9,2<'3g00c\R91>:;R;#XR:';p,1L=59:R=eP=%U;%0:%47R:%:7#:#1#4R7'N120:%071M:7R;,20[[%0:R=g01<WR>AL:72UW0%0;\>^0=%18R8#1#1R=#<p,3sp0'8R>%48R8'F%0>%081E>8#0[[g00kER8#D%C81H92%I9%J9R8P3P4P4P5P8P3P4P4P5P91690g00f_1K96R6C7,98P9P6g00iE%1=#1#4R=,69C7,98F@R6%?4P6GP1Q85P1f2R8g00mIR5g00miR6';1R18=556dAS902CTb4b8b9X19%01121='3%02122='3[^19P1P<f6O2b3b5b6b7b:b;b2g01@cR<,=012<='3eo"). Qed.
  Lemma b2_rng : (0 <= hdr_b2 < 256)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "h02Hah14__x1h21Hh37__arithh44__ffh56__sat3h66__sat4h76__sat5h88__varmaph95__with:4cstrh;5heq_Lp;1p;2p;4p;3p;7p;8g009Bj11Tg009gj1=Tg00:Ej1GTg000Pj15Tg00?Dj2YTg01>7j4VTg01>Sj2OTg013Ij28Tg01?Fj1BTg00Laj22Tg00G1j23Tg0000j2?Tg00FQj1XTg000oj2<Tg00@bj3;Tg00NMj1UTg00=Bj14Tg00;jj1:Tg017Fj2NTg017nj2MTg018Kj3LTg015nj2FTg015Nj2ETg00=`j1DTg00:hj1CTg00O2j2HTg00PLj1ITg00Pjj1JTg00QUj26Tg00R8j2KTg00^Cj47Tg00_Rj7ATg00>bj1@Tg00`6j8PTg00S>j2QTg00S`j2RTg00TLj3STg00Tkj4TTg00X?j2>Tg00^nj7WTg00d:R0f0R1'>p=0f1R2g00gFR3g00geR4P4g00hER5P1g00heFWp=9g00B?R6#1R7#1#1R8#=R9%G9R:g001h#5#5p,4dataR;1Y90CVR<'O189<R<#0%B9,2<'3g00c\R91?:;R;#XR:'<p,1L=;9:R=eP=%U;%0:%47R:%:7#:#1#4R7'N120:%071M:7R;,20[[%0:R=g01<WR>AL:72UW0%0;\>^0=%18R8#1#1R=#=p,3sp0'8R>%48R8'F%0>%081E>8#0[[g00kER8#D%C81H92%I9%J9R8P3P4P4P5P8P3P4P4P5P91690g00f_1K96R6C7,98P9P6g00iE%1=#1#4R=,69C7,98FAR6%@4P6GP1Q85P1f2R8g00mIR5g00miR6'<1R18=;56dAS902CTb4b8b9X19%01121='3%02122='3[^19P1P<f6O2b3b5b6b7b:b;b2g01AWR<,>012<='3eo"). Qed.
  Lemma cfg_rng : (0 <= hdr_cfg < 32768)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "h02Hah17__arithh24__ffh36__sat3h46__sat4h56__sat5h68__varmaph75__with84cstrh95heq_Lp;1p;2p;3p;4p;7g009Bj12Tg00=Bj13Tg00nIj2=Tg00LDj2STg009gj19Tg00:Ej1ITg0000j2ATg00FQj1?Tg000oj27Tg00@bj35Tg00NMj1;Tg00;jj1:Tg017Fj2RTg00Laj24Tg017nj2QTg018Kj3PTg013Ij2NTg015nj2HTg015Nj2FTg00=`j1BTg00:hj1@Tg00OPj1CTg00PLj1DTg00Pjj1ETg00QUj28Tg00^Cj4GTg00^nj7>Tg00S>j2JTg00S`j2KTg00TLj3<Tg00Tkj4LTg016_j3MTg00X?j26Tg00G1j2OTf0R0#2#2p=1g00d:R1/60p=0g01?og00B?#2R2#1R3#2R4#1R5#1R6#3g01@c'='S%26#1#1#1#3R6g00c\R7%93#Ip,4data'AR3#?R8'7p,1L=578R9eP9%;3%08%32R8%:2#:#2#3R2'R1418%021Q82R3,41[[%08R9g01<WR:f1R;9P82UW0%03\:^09%95p,3sp0'NR5%34R4'H%05%041F54#0[[g00kER4#B%@4%C7%D7%E7R4g00gFg00geR5P5g00hER5P71871g00iE1876CGg00heF>1J45P0f2R5g00mIR4g00miR9'71K05=549dA<71;CLb2b6b71416P0b1b3b4b5b8b93Mg01BKR0,611406'Oeo"). Qed.

  (* [comment removed for export] *)
  Definition slotsR (vals : list word) (buf : word) : Prop :=
    vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 a0s path envv /\ vals_ev vals 2 = p1 a0s path envv
    /\ vals_ev vals 5 = tid /\ vals_ev vals 6 = buf /\ vals_ev vals 7 = Z_to_bv 64 L
    /\ vals_ev vals 8 = Z_to_bv 64 hdr_cfg /\ vals_ev vals 9 = Z_to_bv 64 (L - 6 - hdr_cfg)
    /\ vals_ev vals 10 = Z_to_bv 64 hdr_b1s /\ vals_ev vals 11 = Z_to_bv 64 hdr_b2
    /\ vals_ev vals 12 = Z_to_bv 64 (bv_unsigned buf + 6 + hdr_cfg).

  Definition at_trun (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 45%nat -> slotsR vals buf ->
      regs_ok (ENV vals) sr_R R -> know_ok RSEGS (ENV vals) M kn_R ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data -> (L < cap)%Z -> (6 + hdr_cfg <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x178e8) M (seg_rom RSEGS)) (model2 vm)) K.

  Definition hdr_shape (K : TSet) : TSet :=
    if (L <? 6)%Z then t_die msg_short fs0 else if (L <? 6 + hdr_cfg)%Z then t_die msg_overrun fs0 else K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma ownedA_rangeH : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x69b38 <= bv_unsigned a < 0x69ee8)%Z
                 \/ ((0x6b000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "p;7g01C@j70Tp,2ALp,2CLp,3ASRp,3sp0p,4Hvspp,7AL_globp,8AL_grantF0o"). Qed.

  Lemma msg_tail : forall j buf cap A vm vals R M,
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 5 = tid -> vals_ev vals 6 = buf ->
    regs_ok (ENV vals) sr_F2 R -> know_ok RSEGS (ENV vals) M kn_F2 -> side A vm M buf cap j ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1780c) M (seg_rom RSEGS)) (model2 vm)) (t_exit (exit_code 2) fs0).
  Proof.
    intros j buf cap A vm vals R M HL P0 P5 P6 HR HK HS.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    unfold model2, O2ReadLoop.model2.
    (* [comment removed for export] *)
    run_blk_keep scr0 39%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    destruct f_itin as (_ & _ & VLK1 & KNF & _ & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (F10 : getr Rc 10 = buf) by (regv HR (10 : reg); cbn [edenot ev ENV O2Open.ENV]; exact P6);
      assert (F1 : getr Rc 1 = Z_to_bv 64 0x17814) by (regv HR (1 : reg); reflexivity);
      assert (F4 : getr Rc 4 = Z_to_bv 64 0x49840) by (regv HR (4 : reg); reflexivity);
      assert (F2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 128))
        by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV O2Open.ENV];
            rewrite P0; first [reflexivity | f_equal; lia])
    end.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (EQcfg : mkst Rc (Z_to_bv 64 0x2f80c) M (seg_rom RSEGS) = mkst Rc al_free_pc M al_rom)
        by (rewrite AL_free, AL_rom; reflexivity); rewrite EQcfg; clear EQcfg end.
    rewrite <- AL_segs.
    set (md := mkModelC O2Open.fds0 vm stdin0 fs0 None (Some tid) None).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (ai_free fx0 A M md Rc buf (Z_to_bv 64 0x17814) sp0 [a0s; path] envv (t_exit (exit_code 2) fs0) HI) end.
    - constructor; reflexivity.
    - change (m_kernel md) with a_kernel. change (m_vmmaps md) with vm.
      exact (vm_resv_incl _ _ vm Hres Hisp).
    - apply AL_env. exact HE.
    - exact F10.
    - right. exists cap. exact Hl.
    - exact F1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite F4. symmetry. exact AL_tp.
    - rewrite F2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, F2, u_small by lia. lia.
    - rewrite F2, u_small by lia. lia.
    - intros a Ha. rewrite F2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV O2Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LS16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeH A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - (* [comment removed for export] *)
      intros A'' m'' vm'' regs'' HI'' Hcs'' Hlbuf'' Hlq'' Hfr'' Hlm'' Hgr'' Hvl'' Htop'' Hisp'' Hres'' Hmb'' Hvlb''.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop''. rewrite Htop in Htop''.
      unfold md. rewrite with_vmmaps_C.
      set (vals2 := vals ++ junk_vals regs'').
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG a0s path vals sr Rc regs'' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs'') as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      clear HR. rename HR2 into HR.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_after_allocG sp0 a0s path Hvsp data AL_glob AL_grant AL_errno AL_hi A A'' vals M m'' vm vm'' regs'' kn
                      ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK1) HK HI Htop HI'' Htop'') as HK2 end.
      specialize (HK2 ltac:(intros a H1 H2 H3 H4; apply Hfr''; try assumption; rewrite F2, u_small by lia; exact H4)
                      ltac:(intros a Ha; destruct (Hgr'' a Ha) as [Ho|Hs]; [right; left; exact Ho | right; right; exact Hs])).
      lazymatch type of HK2 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK2 end.
      fold vals2 in HK2. clear HK. rename HK2 into HK.
      assert (HL2 : length vals2 = 71%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      (* [comment removed for export] *)
      run_blk_keep scr0 71%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      assert (Hh : m_halted (mkModelC O2Open.fds0 vm'' stdin0 fs0 None (Some tid) None) = None) by reflexivity.
      assert (Hlazy : m_vm_lazy (mkModelC O2Open.fds0 vm'' stdin0 fs0 None (Some tid) None) = []) by reflexivity.
      close_exit_gen HR HK Q0 Hh Hlazy sp0 48%Z (-192)%Z (Z_to_bv 64 0x69f08).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma kimg_rdn_msg : forall E M kn (a : Z) bs,
    know_ok RSEGS E M kn -> existsb (is_kimg_cov a 31) kn = true ->
    rdn RSEGS (fun _ => None) (Z_to_bv 64 a) 31 = Some bs -> (0 <= a)%Z -> (a + 31 < 2 ^ 64)%Z ->
    rdn RSEGS M (Z_to_bv 64 a) 31 = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "p'0h01Hh12Hch23Hinh31xi001xh41ni011nh52Hah64__x1h72a0h81ih91ei021eh:1mi031mh;1Ah<2H1h=2H2h>3Hexh?3Hk0h@7__arithhA4__ffhB6__sat3hC6__sat4hD6__sat5hE6__sat6hF6__sat7hG8__varmaphH5__withI4__x2hJ4__x3hK4__x4hL4__x5hM4cstrhN5cstr0hO1fhP5heq_LhQ2hii042hihR1ki051khS1lhT2loi062lohU1EhV2HKhW3HKKhX3Ha0hY3Ha1hZ4Himgh[2Hkh\2Hnh]1Kh^1Mh_2_Hh`3_H0ha1ai071ahb2a1i082a1hc2a2i092a2hd2bshe2e0hf2knhg2n1i0:2n1hh2n2i0;2n2hi1ohj1vi0<1vhk1wi0=1whl1zi0>1bp&0p;1p;4p;2p;3p;6p;<p;7p;8g009Bj17Tg009gj1eTg00:Ej1bTg00;Hj1uTg00:hj1QTg01Hek40;Tg00;jj1JTg00=Bj1FTg041mj2sj3>Tg0438R0j3RTg00>bj1qTg000Pj1<Tg00LDj28Tg017nj2gTg00LaR1j26Tg00F:j3OTg00G1R2j23Tg00GLR3j2LTg043Tk304Tg01bPj3VTg0447j2\Tg044Vj2^Tg01c[j3TTg01dfj2STg045aj2=Tg046>j3wTg00X?j20Tg046aj2vTg02iTj3aj4`Tg047Aj3tTg047bk30CTg048Dk60BTg00?Dj2ETg00@bj3;Tg00KQR4j2nTg00FQR5j1ITg0000k20>Tg000oj2KTg00Mfk40<Tg00NMj1lTg017Fj2kTg018Kj3jTg013Ij2iTg015nk20:Tg015Nk209Tg00Y5j2GTg00a?j3PTg00ahj2hTg00=`k108Tg00A_j3fTg00O2j2]Tg00OPk107Tg00Onj4XTg00PLk106Tg00Pjk105Tg00QUj2NTg00R8j2HTg00R[j3WTg00S>k203Tg00S`k202Tg00TLk301Tg00Tkj4}Tg018oj3~Tg019Rk200Tg005\j6|Tg048_j6{Tg00>@j2rTg007Dj6cTg01\Zj2_Tg01]ej3ZTg01`:j2UTg01aEj4YTg00?jj4[Tg00W8l<zTg00^Cj4mTg00^nj7yTg00_Rj7xTg00`6k80?Tf0R6#7#7p=p%J6#Jp=@g00mIR7g00miR87;6p=4%<6#<p=o%<6#<#<#<p=Cf6R9g00BdR:f5R;f4R<f3R='Ef2R>C[f1R?/r63;p=9g00d:R@/06p=2g03RFRA?O?6p=1A>>?6=;78p=5P7P>P?g03fDP8P6Ecp=BP:P>P?P6C[p>0AP:P<1E=>P?C[=;;6p>0@g001IRBg00c\RCP4P5P1g00f=P;P<P=P>P?P6M<zp>0=PCP?g00f_P6Cmp=DP?g00gFR1g00geR5P5g00hER4P6g00heFyp=:PCP?g00iEP6Cmp=M%76#7#7#7p=AP>P1P5P5P4P?P6Fxp=dP=P1P5P5P4P>P?P6L0?p=?g049hg00B?R1#7RD#7RE#7RF#7RG#pRH#eRI#bRJ%eF#bRF#uRK[%QA%QFRLP:P<P=P>H0;%J1RM#JRN#@RO#FRP,s>=RA=#4%uLRQ%qFRRVJRJPIP=g001hRS#oRT#<RU#<RV#<RW#o#C#C#C#C#C#CRXPLP>F9%2<18;P%FDRY%FHRH'gRZ'6P0p4p710R0P7\6R[%Q?R\P2AR>?6#4AO<6>P=P6O1#4'3X3=,L=[R]AO=6?P>P6O1#4'3X3>,L>AR=>?#4R^[AO;6=P<P6O1#4'3X3<,L<\^B04>?6P?n2001000000120000000WSWOW;P]^S\^O[^;0P6PAf7R0/sPf8R[P<O4f9R\,16A5[P6'3X3A,LAP3PAf:R3,16A5\P6'3X3APQf;R]PIP\PXPLP[F9P6f<R^,16A5]P6'3P2f=R_,1?A5^P?PQf?R`PIP_PXPLP^F9P611=`A5`P<PAfBRa,16A5aP?PQfERbPIfCPXPLPaF9]1]2P;g04;0Rcg03Q=RdAV>?6fGRe'1AV=>?95ePfHRfAV<=>7>PP7p-0P6g03l8Rgg01<WRhn0110>00020000RiX97Rj;B6PgPQfKRkPIfIRlPXPLPfF9/\6Rmb0W1W2WjXkBW7P>P?P6O31^?6/1b1^>?95bPfFRn1^=>7>P?Bj6PgPQPlPIPePXPLPnF9/\6Rob0W1W2X4dX7cP?P6O2AT>?6/1eAT=>?95ePAT<=>9>fP?Bj6PgPmb0W1W2XRBX4dX7cP>P?P6O31S?6/1b1S>?95bP1==nRp18nP/=>Rq;w6%4p%4q'3P21=<e#418eP/==#4PQfJRqPIPfPXPLPeF9P61=9l#418qP/=9#4P21=?6#410>?[Rp10?61=>?#4Rr[10=>\r1v?6P?n2001000000120000000X:CX4CRrPp^:C^4CRpP6P\fLRsP>O310\sPrPpP6fN/8PRpP3P=O310p3fRRpfQRr5a:RsfPR\5tA116pP:fURtfTRuP?C`[^3A[116rP:PufSRvP?C`[^3AAa:vp=tAr[B0CAs\fMRs1S^]RwP3J0BP:PpPrPwC`P2%2_10^Zf>/06166_'3Pu1EI?R_O1=;KR[^8C'3PQPvPIPrPXPLP\F9P6%2`10`ZfAR`/06f@Rv,66'3fWR^P_O1=;KR[^8C'3P210vZ10a6166`'3fXR`P_O1=;KR[^8CPQP^PIPtPXPLPuF9P610aZ10b6fD,66'3f[RaP_O1=;KR[^8CPQ1EI`R`>0AJXPQPaPIfYPXP6J0@XiQP:fZR:PJPXP`1n6XPCP:f]%I>R`,86,EIO1=;KRXlCP>%I?,8:p,4data-0>FRF#IRR,KCp,1L=;CRRKeRJPK1n>X16`PRaP>P`1KC`PXPP1KCPJ0=P?H0<R`Pa%l=R_%I=#2Rt%lFRF%2RRR1kYHRv16@YR2%2H16@Z[[Rw%2YRpAjYH?VhW5RH%2Z\h^5pR3%@D#7#FRx,kYRy%2x1gYxRz,6@[\2R2AjYx?VhX5pRx%2z\h^5pRpp,3sp0,iIRh%FGRG+0:Rz%2h%2G209hG#2[[RGg00kER{1GCV1GCU1GCSRS5PC5PCg00jYRU'h1GCW1GCT=PCS5PC/hU&08{RU5f{3f%Q{R{PCPC1]C<P>&07CRSCXP?PCPSP=1]C;CXCX&06CRS&05CRT1NC@RW1HCMRM'D,:T%q5R5PT1NCPRV,MM,:TP5PT1HCDRD=WCV1HCERE'D,:TP5PT1HC1R1/DD,:TP5PT%JO#@#@#@#@#@#7#p#A#A#A#A#A#A#A#FRO,NC1HCN'D,:TP5AWCDMRD,D1,:T1MDE,:T5dTC?C?C?C?C?203T4R4P6P>1K782026>#4dB01C@?C}R@bAbGbHX6CXICXJCXKCXLC%2>R816=P18=P/0;10=<10O[1890R9,0;169['3[[[[[^6C^IC^JC^KC^LCP6PhP\%I]fdR]PrP0P[PbPep,4SPloO:b@bBbCbDbEbFbNbMb?bPO21EI:,iIPJPKP`PaP_PtPFPRPvPwPHP3PyP2PxPpPzPGPUP{1]C?PSPTAWC1V1NCY=~CIRY'M,:TP5PT1DW1,:TRWP51M1Y,:T9dTWC?C?P4P@bAbGbHX6C186P/6Z%2?16>Z,38[[^6CP6P]f^f_O3b@bBbCbDbEbFbNbMb?bP-00:E|W[XRBE{1rL^PuEcW\W`P?P6O2n2001000000121000000W0W_P?P6O2n2001000000121000000bWb=b0b<b0W=W<P?P6O2n2001000000121000000b1W1W2XQCXTCP?P6O21_?6/1b1_>?95bP1_=>9>nPPiXe7R7;B6PgPob0W1W2X:CX9dP?P6O2AZ>?6/1eAZ=>?95ePAZ<=>9>fP?B76PgPmb0W1W2XQCXTCX9dP>P?P6O31U?6/1b1U>?95bP1U=>9>nP?Bj6PgPob0W1W2X4CX7cP?P6O2P=P>P?P6CY/1lP<P=P>P?CY95lPP;P<P=P>CY9>qP?Bj6PgPQPsPIPkPXPLPqF9/\6b0W1W2XhCXccXgCXbcP=P>P?P6O4n0110500083010710=10<2010710130107101105211061042010210330102106104201071014010810:10910;P?P6O2W1W2P?P6O2n2001000000121000000W0X]AP?P6O2n2001000000121100000b>b0WYWXWZW>WVWdXaCWfW^WUo"). Qed.

  Theorem header_short : forall j buf cap, (L < 6)%Z -> at_header (t_die msg_short fs0) j buf cap.
  Proof.
    intros j buf cap HL6 A vm vals R M HL SL HR HK HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    unfold O2ReadLoop.model2. unfold t_die.
    (* [comment removed for export] *)
    run_blk_keep (SCR [true] [] []) 41%nat.
    { cbn [sc_denot branch_taken edenot ev ENV O2Open.ENV]. rewrite P7. unfold bv_ltu. rewrite !u_small by (unfold L in *; lia).
      cbn. apply (f_equal negb (y := false)). apply Z.ltb_ge. unfold L in HL6 |- *. lia. }
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (side_block_wd sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap j E log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
    rewrite <- EQM in HS1, OUT1.
    assert (HB1 : bytes_at M0 (bv_unsigned buf) data).
    { intros i Hi. unfold L in *. pose proof (u_small (bv_unsigned buf + i) ltac:(lia)) as Hu.
      rewrite OUT1; [apply HB; exact Hi | unfold O2ReadLoop.in_win; rewrite Hu; lia | rewrite Hu; lia]. }
    clear EQM HS HB.
    assert (Hsrc : rdn RSEGS M0 (Z_to_bv 64 0x121c9) 31 = Some MSG_SHORT).
    { lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (kimg_rdn_msg (ENV vals) M0 kn 0x121c9 MSG_SHORT HK ltac:(vm_compute; reflexivity) msg_short_img); lia end. }
    replace (W 2 msg_short) with (map (WriteEv (Z_to_bv 64 2)) ([] ++ MSG_SHORT)) by reflexivity.
    pose proof h_itinS as (_ & SC & _ & _ & IF). apply pair_equal_spec in IF as [MIS MISS].
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?md) _ =>
    apply (stdio_call_sound_fr vals (blobs_ev (blobs0 a0s path)) h_srS h_knS Rc Mc md h_scS [] MSG_SHORT
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n h_srS h_knS) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn h_scS length Z.of_nat] end.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. lia.
    - lia.
    - cbn [edenot]. rewrite MSG_SHORT_len. apply u_small. lia.
    - rewrite MSG_SHORT_len. cbn [length Z.of_nat]. lia.
    - rewrite MSG_SHORT_len. cbn [length Z.of_nat]. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV O2Open.ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV O2Open.ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [edenot]. rewrite MSG_SHORT_len. exact Hsrc.
    - reflexivity.
    - exact a_reader.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK HPOST.
      (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows _ _ _]. cbn [edenot ev ENV O2Open.ENV] in Pagree. rewrite P0 in Pagree.
      rewrite alu_add_wZ, u_small in Pagree by lia.
      assert (HS2 : side A vm M2 buf cap j).
      { apply (side_frame sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M0 M2 buf cap j HS1); [| exact Pgrows].
        intros x Hne.
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 192 - 112)) as [H1|H1];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 192)) as [H2|H2]; [left; unfold O2ReadLoop.in_win; lia|]];
          (destruct (Z_lt_ge_dec (bv_unsigned x) (0x39508 + 32)) as [H3|H3];
            [| destruct (Z_lt_ge_dec (bv_unsigned x) (0x39508 + 64)) as [H4|H4]; [right; left; unfold O2ReadLoop.in_data; lia|]]);
          exfalso; apply Hne; apply Pagree; lia. }
      assert (HB2 : bytes_at M2 (bv_unsigned buf) data).
      { intros i Hi. unfold L in *. pose proof (u_small (bv_unsigned buf + i) ltac:(lia)) as Hu.
        rewrite Pagree; [apply HB1; exact Hi | rewrite Hu; lia | rewrite Hu; lia | rewrite Hu; lia]. }
      clear HS1 HB1 Pagree Pgrows.
      set (vals2 := vals ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q6 : vals_ev vals2 6 = buf) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      (* [comment removed for export] *)
      run_blk2_keep scr0 73%nat.
      lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
        destruct (side_block sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M2 buf cap j E log HS2 ltac:(vm_compute; reflexivity) Q0) as [HS3 OUT3] end.
      rewrite <- EQM in HS3, OUT3. clear EQM.
      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (msg_tail j buf cap A vm (map (edenot (ENV vals2)) f_rvlS) Rx Mx) end.
      + rewrite length_map. reflexivity.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlS app edenot ev ENV O2Open.ENV]. exact Q0.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlS app edenot ev ENV O2Open.ENV]. exact Q5.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlS app edenot ev ENV O2Open.ENV]. exact Q6.
      + change (ENV (map (edenot (ENV vals2)) f_rvlS)) with (xenv (ENV vals2) f_rvlS (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ =>
          p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals2) f_rvlS idb _ (fun k => eq_refl) srb sr_F2 _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[]]. exfalso; lia.
      + change (ENV (map (edenot (ENV vals2)) f_rvlS)) with (xenv (ENV vals2) f_rvlS (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          apply (know_ok_xfer_entails RSEGS (ENV vals2) f_rvlS idb _ _ kn kn_F2 (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + exact HS3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kwordv1_of_mem : forall E M (e : expr) (a : word) off (i : nat) (z : Z),
    edenot E e = a -> ev E i = Z_to_bv 64 z -> (0 <= z < 256)%Z ->
    (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + 1 <= 2 ^ 64)%Z ->
    M (Z_to_bv 64 (bv_unsigned a + off)) = Some (Z_to_bv 8 z) ->
    kentry_ok RSEGS E M (KWord (SA e off) 1 (EVar i)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "h02Hah17__arithh24__ffh36__sat3h46__sat4h56__sat5h66__sat6h76__sat7h88__varmaph95__with:4__x1h;4cstrh<5heq_Lh=1zh>1Eh?2H1h@2H2hA2HehB2HihC2HmhD2HzhE1MhF1ahG1ehH1ihI1ohJ3offhK1xp;1p;2p;3p;4p;8p;6p;5p;@p;<p;7g009Bj12Tg009gj1LTg00:Ej1ETg00;Hj1ATg024Tj2lTg00@bj33Tg030Lj2YTg00?Dj21Tg00=Bj15Tg00Laj27Tg00G1j2@Tg013Ij28Tg00LDj2:Tg017nj2JTg00X?R0j2?Tg00>@j26Tg000Pj14Tg01ZHj1ZTg05MKj3XTg05N@j4WTg0000j2VTg00FQR1j1UTg000oj2;Tg00J`R2j2TTg00NMj1RTg017Fj2CTg018Kj3BTg00;jj1ITg015nj2OTg015Nj2NTg00=`j1DTg00:hj1HTg00OPj1MTg00PLj1PTg00Pjj1QTg00QUj29Tg00^Cj4<Tg00S>j2kTg00S`j2jTg00TLj3iTg00Tkj4bTg00[Fj4aTg00A_j3>Tg036;j2GTg00O2j2_Tg00R8j2^Tg00>bj1]Tg018oj3\Tg00`6j8[Tg019Rj2`Tg005\j6KTg00?jj4cTg05Nnj5dTg05P=l@eTg00W8l<fTg00^nj7gTg00_Rj7hTg00d:R3f0R4'?p=0g001IR5g00c\R6P2P1P0g00dXf5R0f4R1f3R7f2R8f1R9P4M<fp=SP9g00gFR:g00geR;P;g00hER<P4g00heFgp==P8P:P;P;P<P9P4Fhp=Fg049hg00B?R=#2R>#2#2R?#2R@#2#2RA#LRB#ERC%L?RD#ERE#ARF]Kg03Q=f6RG/l1=3C7f7R7/Y811B953C%08%2A#2#5RH,78'@18BG/:0#018B7/:G%5=RI':%5>RJ%5ARA'JRK'?f:RLf8RM,8B/:7,1BO111D0,6E53Fg00BdRFf<f;RNPLf9RLPMg001h#4RO%Z711BGRPP0P1P5P2g05QE9X52POCWp,4data,VER2#UR1,;6p,1L=361R0eRQP0%4O#4#4#4#4#4#4RR,TO%5?R?,?IRSPOPI1;6IPRP?1;6?ES%R2R2%01R11CJARR173JRT%0A173K[[RU%0JRVg01<WRWABJA9UW0RA%0K\W^0VRX%I>#I#2#5R>,CJRY%0>1JJ>RZ,73[\TRTABJ>9VWX0VR>%0Z\W^0VRVp,3sp0,8BRW%5@R@'ORZ%0W%0@1NW@#0[[R@g00kERW#DR[%HWRW%M6%P6R\%Q6R]P6196Ig00f_RI196?C<'=1k]<R?P4P8g00mIR^g00miR_';1j48=3^_dAi639CbR_b2b8b9PSP4b1b3b4b5b6b7b;Cab<P8P9%HER8#ARS11DGR^%DER`5>E,68Ra11B7,GO,6893S4XISP6PG11D7=>E`,6811D4=>E`,6853SX=61;Sa18BPPQP0P2P1PRPUPAPXPYPTP>PVPZP@P[PW1_69P\P]P:P;P;P<P61963PI1^6=R=C<,=]RIP6P=g00iER3196HC<,=]5F]%];P6P=P3196J=\6BC<,=]9F]IG[P?P_b2b8b9X:6%04174H'@%09179K'@[^:6P4f>PNO2b1b3b4b5b6b7b;b<,`GEK1GOP,6893SaePFPN18BL/:M,1BRBPOCcPFPNPBP^P4DdEKM@eWCW@W?WDWBWAX=6XH5XJ6XFCWGWEW>o"). Qed.

  Lemma cfgx_val : forall vals, vals_ev vals 41 = Z_to_bv 64 hdr_b0 -> vals_ev vals 42 = Z_to_bv 64 hdr_b1 ->
    edenot (ENV vals) cfglen_x = Z_to_bv 64 hdr_cfg.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "h01bh13H41h23H42h34valsp;1p;2p;3p;4p;6g009Bj12Tg009gj1ATg00:Ej1<Tg00:hj1;Tg000Pj10Tg01=3j23j19Tg00?Dj27Tg00@bj31Tg014Wj25Tg05Qmj4:Tg005\j66Tg04Ugj3@Tg04Vaj1?Tg05:Fj2>Tg024Tj28Tg05Rcj2=Tf0R0#0#0#0#0#0#0#0#0p=4g00B?#2#2#2#2#2#2#AR1#<R2#;g001h#0#4#4#4#4#4R3,30g01?oR4,71R5512f1R6%03R7'3g01@cR8,71R9512P2f2R:/33R313:7R;'5g01BK,71R19120X02P2P5f3/37,50=121X02P2P91550=121X02P4P8g05S^g05TRC:1559=121eP;P0E6P3P6E6%9:p,3AMBp,3a0sp,4path3@R6#?'>g05UFR3'81=:6E6p,3ENVP:O1/83=121eW2W1W3o"). Qed.

  (* [comment removed for export] *)
  Lemma hdr6_entry : forall A vm vals R M buf cap j,
    length vals = 41%nat -> slots vals buf L cap ->
    regs_ok (ENV vals) sr_H R -> know_ok RSEGS (ENV vals) M kn_ML -> side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data ->
    (6 <= L)%Z ->
    let vals3 := vals ++ [Z_to_bv 64 hdr_b0; Z_to_bv 64 hdr_b1; Z_to_bv 64 hdr_b2] in
    length vals3 = 44%nat /\ slots vals3 buf L cap
    /\ vals_ev vals3 41 = Z_to_bv 64 hdr_b0 /\ vals_ev vals3 42 = Z_to_bv 64 hdr_b1 /\ vals_ev vals3 43 = Z_to_bv 64 hdr_b2
    /\ regs_ok (ENV vals3) sr_H R /\ know_ok RSEGS (ENV vals3) M kn_H6.
Proof.
    intros A vm vals R M buf cap j HL SL HR HK HS HB HL6 vals3.
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof b0_rng as R0. pose proof b1_rng as R1. pose proof b2_rng as R2.
    assert (HL3 : length vals3 = 44%nat) by (subst vals3; rewrite length_app, HL; reflexivity).
    assert (E41 : vals_ev vals3 41 = Z_to_bv 64 hdr_b0)
      by (subst vals3; replace 41%nat with (length vals + 0)%nat by lia; rewrite vals_ev_app_r; reflexivity).
    assert (E42 : vals_ev vals3 42 = Z_to_bv 64 hdr_b1)
      by (subst vals3; replace 42%nat with (length vals + 1)%nat by lia; rewrite vals_ev_app_r; reflexivity).
    assert (E43 : vals_ev vals3 43 = Z_to_bv 64 hdr_b2)
      by (subst vals3; replace 43%nat with (length vals + 2)%nat by lia; rewrite vals_ev_app_r; reflexivity).
    assert (SL3 : slots vals3 buf L cap)
      by (subst vals3; apply (slots_app sp0 a0s path envv tid data vals); [rewrite HL; lia | exact SL]).
    assert (HR3 : regs_ok (ENV vals3) sr_H R)
      by (subst vals3; exact (env_app_regs vals [Z_to_bv 64 hdr_b0; Z_to_bv 64 hdr_b1; Z_to_bv 64 hdr_b2]
                                (blobs_ev (blobs0 a0s path)) sr_H R ltac:(rewrite HL; vm_compute; reflexivity) HR)).
    assert (HK3 : know_ok RSEGS (ENV vals3) M kn_ML)
      by (subst vals3; exact (env_app_know RSEGS vals [Z_to_bv 64 hdr_b0; Z_to_bv 64 hdr_b1; Z_to_bv 64 hdr_b2]
                                (blobs_ev (blobs0 a0s path)) M kn_ML ltac:(rewrite HL; vm_compute; reflexivity) HK)).
    assert (Q6 : vals_ev vals3 6 = buf) by (destruct SL3 as (_ & _ & _ & _ & Q6 & _); exact Q6).
    red in HB. unfold L in HL6.
    assert (BY : forall k : Z, (0 <= k < 3)%Z ->
                   M (Z_to_bv 64 (bv_unsigned buf + k)) = Some (Z_to_bv 8 (bv_unsigned (nth (Z.to_nat k) data (Z_to_bv 8 0)))))
      by (intros k Hk; rewrite Z_to_bv_bv_unsigned; apply HB; lia).
    do 6 (split; [assumption|]).
    red. unfold kn_H6.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons;
      [| apply Forall_cons; [| exact HK3]]]]]].
    - apply (kwordv1_of_mem _ M (EVar 6) buf 0%Z 41%nat hdr_b0);
        [exact Q6 | exact E41 | exact R0 | lia | lia | exact (BY 0%Z ltac:(lia))].
    - apply (kwordv1_of_mem _ M (EVar 6) buf 1%Z 42%nat hdr_b1);
        [exact Q6 | exact E42 | exact R1 | lia | lia | exact (BY 1%Z ltac:(lia))].
    - apply (kwordv1_of_mem _ M (EVar 6) buf 2%Z 43%nat hdr_b2);
        [exact Q6 | exact E43 | exact R2 | lia | lia | exact (BY 2%Z ltac:(lia))].
    - cbn [kentry_ok]. change (edenot (ENV vals3) (EVar 41)) with (vals_ev vals3 41). rewrite E41, u_small by lia. lia.
    - cbn [kentry_ok]. change (edenot (ENV vals3) (EVar 42)) with (vals_ev vals3 42). rewrite E42, u_small by lia. lia.
    - cbn [kentry_ok]. change (edenot (ENV vals3) (EVar 43)) with (vals_ev vals3 43). rewrite E43, u_small by lia. lia. Qed.

  Theorem header_overrun : forall j buf cap, (6 <= L)%Z -> (L < 6 + hdr_cfg)%Z -> at_header (t_die msg_overrun fs0) j buf cap.
  Proof.
    intros j buf cap HL6 HLc A vm vals0 R M HL0 SL0 HR0 HK0 HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct (hdr6_entry A vm vals0 R M buf cap j HL0 SL0 HR0 HK0 HS HB HL6) as (HL & SL & E41 & E42 & E43 & HR & HK).
    set (vals := vals0 ++ _) in HL, SL, E41, E42, E43, HR, HK. clearbody vals. clear HL0 SL0 HR0 HK0.
    destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    pose proof (cfgx_val vals E41 E42) as CFG. pose proof cfg_rng as Hcr.
    unfold O2ReadLoop.model2. unfold t_die.
    (* [comment removed for export] *)
    run_blk_keep (SCR [false; true] [] []) 44%nat.
    { cbn [sc_denot branch_taken]. fold cfglen_x. cbn [edenot]. rewrite CFG. cbn [ev ENV O2Open.ENV]. rewrite P7, alu_add_Z.
      unfold bv_ltu. rewrite !u_small by (unfold L in *; lia). apply Z.ltb_lt. unfold L in *. lia. }
    { cbn [sc_denot branch_taken edenot ev ENV O2Open.ENV]. rewrite P7. unfold bv_ltu. rewrite !u_small by (unfold L in *; lia).
      cbn. apply (f_equal negb (y := true)). apply Z.ltb_lt. unfold L in *. lia. }
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (side_block_wd sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap j E log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
    rewrite <- EQM in HS1, OUT1.
    clear EQM HS HB.
    assert (Hsrc : rdn RSEGS M0 (Z_to_bv 64 0x10bde) 31 = Some MSG_OVERRUN).
    { lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (kimg_rdn_msg (ENV vals) M0 kn 0x10bde MSG_OVERRUN HK ltac:(vm_compute; reflexivity) msg_overrun_img); lia end. }
    replace (W 2 msg_overrun) with (map (WriteEv (Z_to_bv 64 2)) ([] ++ MSG_OVERRUN)) by reflexivity.
    pose proof h_itinO as (_ & SC & _ & _ & IF). apply pair_equal_spec in IF as [MIS MISS].
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?md) _ =>
    apply (stdio_call_sound_fr vals (blobs_ev (blobs0 a0s path)) h_srO h_knO Rc Mc md h_scO [] MSG_OVERRUN
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n h_srO h_knO) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn h_scO length Z.of_nat] end.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. lia.
    - lia.
    - cbn [edenot]. rewrite MSG_OVERRUN_len. apply u_small. lia.
    - rewrite MSG_OVERRUN_len. cbn [length Z.of_nat]. lia.
    - rewrite MSG_OVERRUN_len. cbn [length Z.of_nat]. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV O2Open.ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV O2Open.ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [edenot]. rewrite MSG_OVERRUN_len. exact Hsrc.
    - reflexivity.
    - exact a_reader.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK HPOST.
      destruct HPOST as [Pagree Pgrows _ _ _]. cbn [edenot ev ENV O2Open.ENV] in Pagree. rewrite P0 in Pagree.
      rewrite alu_add_wZ, u_small in Pagree by lia.
      assert (HS2 : side A vm M2 buf cap j).
      { apply (side_frame sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M0 M2 buf cap j HS1); [| exact Pgrows].
        intros x Hne.
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 192 - 112)) as [H1|H1];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 192)) as [H2|H2]; [left; unfold O2ReadLoop.in_win; lia|]];
          (destruct (Z_lt_ge_dec (bv_unsigned x) (0x39508 + 32)) as [H3|H3];
            [| destruct (Z_lt_ge_dec (bv_unsigned x) (0x39508 + 64)) as [H4|H4]; [right; left; unfold O2ReadLoop.in_data; lia|]]);
          exfalso; apply Hne; apply Pagree; lia. }
      clear HS1 Pagree Pgrows.
      set (vals2 := vals ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 76%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q6 : vals_ev vals2 6 = buf) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      (* [comment removed for export] *)
      run_blk2_keep scr0 76%nat.
      lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
        destruct (side_block sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M2 buf cap j E log HS2 ltac:(vm_compute; reflexivity) Q0) as [HS3 OUT3] end.
      rewrite <- EQM in HS3, OUT3. clear EQM.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (msg_tail j buf cap A vm (map (edenot (ENV vals2)) f_rvlO) Rx Mx) end.
      + rewrite length_map. reflexivity.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlO app edenot ev ENV O2Open.ENV]. exact Q0.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlO app edenot ev ENV O2Open.ENV]. exact Q5.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlO app edenot ev ENV O2Open.ENV]. exact Q6.
      + change (ENV (map (edenot (ENV vals2)) f_rvlO)) with (xenv (ENV vals2) f_rvlO (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ =>
          p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals2) f_rvlO idb _ (fun k => eq_refl) srb sr_F2 _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[]]. exfalso; lia.
      + change (ENV (map (edenot (ENV vals2)) f_rvlO)) with (xenv (ENV vals2) f_rvlO (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          apply (know_ok_xfer_entails RSEGS (ENV vals2) f_rvlO idb _ _ kn kn_F2 (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + exact HS3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bytes_le_to_Z_1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "h01zh11bp;1p;2p;3p;6g009Bj10Tg009gj1>Tg00:Ej18Tg013Ij23Tg060Tj24Tg00@bj31Tg000oj2;Tg0611j17Tg005\j62Tg00=Bj16Tg061Rj25Tg0622j19Tg00=`j1:Tg00A_j3=Tg062Vj1<Tg00B?#0#0#0R0#>R1#8R2g00c\R3g00d:R4f1,31R5f0R6'4=135X03P31316R1A1365X031;311414%71E2%60R0,54%90E2%:29=26#<=131eW1o"). Qed.

  Theorem header_ok : forall K j buf cap, (6 + hdr_cfg <= L)%Z -> at_trun K j buf cap -> at_header K j buf cap.
  Proof.
    intros K j buf cap HLc HTR A vm vals0 R M HL0 SL0 HR0 HK0 HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof cfg_rng as Hcr.
    destruct (hdr6_entry A vm vals0 R M buf cap j HL0 SL0 HR0 HK0 HS HB ltac:(lia)) as (HL3 & SL3 & E41 & E42 & E43 & HR3 & HK3).
    set (vals3 := vals0 ++ _) in HL3, SL3, E41, E42, E43, HR3, HK3. clearbody vals3. clear HL0 SL0 HR0 HK0.
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    (* [comment removed for export] *)
    set (byte := fun k : Z => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat k) data (Z_to_bv 8 0)))).
    set (vals := vals3 ++ [byte (hdr_cfg + 3); byte (hdr_cfg + 2); byte (hdr_cfg + 4); byte (hdr_cfg + 5)]%Z).
    assert (HL : length vals = 48%nat) by (subst vals; rewrite length_app, HL3; reflexivity).
    assert (SL : slots vals buf L cap) by (subst vals; apply (slots_app sp0 a0s path envv tid data vals3); [rewrite HL3; lia | exact SL3]).
    assert (P41 : vals_ev vals 41 = Z_to_bv 64 hdr_b0) by (subst vals; rewrite vals_ev_app_l by (rewrite HL3; lia); exact E41).
    assert (P42 : vals_ev vals 42 = Z_to_bv 64 hdr_b1) by (subst vals; rewrite vals_ev_app_l by (rewrite HL3; lia); exact E42).
    assert (P43 : vals_ev vals 43 = Z_to_bv 64 hdr_b2) by (subst vals; rewrite vals_ev_app_l by (rewrite HL3; lia); exact E43).
    assert (P44 : vals_ev vals 44 = byte (hdr_cfg + 3)%Z) by (subst vals; replace 44%nat with (length vals3 + 0)%nat by (rewrite HL3; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (P45 : vals_ev vals 45 = byte (hdr_cfg + 2)%Z) by (subst vals; replace 45%nat with (length vals3 + 1)%nat by (rewrite HL3; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (P46 : vals_ev vals 46 = byte (hdr_cfg + 4)%Z) by (subst vals; replace 46%nat with (length vals3 + 2)%nat by (rewrite HL3; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (P47 : vals_ev vals 47 = byte (hdr_cfg + 5)%Z) by (subst vals; replace 47%nat with (length vals3 + 3)%nat by (rewrite HL3; reflexivity); rewrite vals_ev_app_r; reflexivity).
    pose proof (env_app_regs vals3 [byte (hdr_cfg + 3); byte (hdr_cfg + 2); byte (hdr_cfg + 4); byte (hdr_cfg + 5)]%Z (blobs_ev (blobs0 a0s path)) sr_H R ltac:(rewrite HL3; vm_compute; reflexivity) HR3) as HR.
    pose proof (env_app_know RSEGS vals3 [byte (hdr_cfg + 3); byte (hdr_cfg + 2); byte (hdr_cfg + 4); byte (hdr_cfg + 5)]%Z (blobs_ev (blobs0 a0s path)) M kn_H6 ltac:(rewrite HL3; vm_compute; reflexivity) HK3) as HK.
    fold vals in HR, HK. change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path))) with (ENV vals) in HR, HK.
    clear HR3 HK3. clearbody vals. destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (cfgx_val vals P41 P42) as CFG.
    assert (ACFG : edenot (ENV vals) (EAlu ALU_ADD (EVar 6) cfglen_x) = Z_to_bv 64 (bv_unsigned buf + hdr_cfg)).
    { cbn [edenot]. rewrite CFG. cbn [ev ENV O2Open.ENV]. rewrite P6. apply alu_add_wZ. }
    assert (RB : forall k, (2 <= k <= 5)%Z ->
      (exists bs, rdn RSEGS M (adenot (ENV vals) (SA (EAlu ALU_ADD (EVar 6) cfglen_x) k)) 1 = Some bs
                  /\ Z_to_bv 64 (extz false 1 (bytes_le_to_Z bs)) = byte (hdr_cfg + k)%Z)
      /\ flat (ENV vals) (SA (EAlu ALU_ADD (EVar 6) cfglen_x) k) (elenZ (ENV vals) (ELit 1))).
    { intros k Hk. unfold adenot, flat, estart, elenZ. cbn [a_base a_off]. rewrite ACFG. unfold v_addi. rewrite !u_small by lia.
      cbn [edenot]. rewrite u_small by lia. split; [|lia].
      exists [nth (Z.to_nat (hdr_cfg + k)) data (Z_to_bv 8 0)]. split.
      - apply rdn_1_of_mem. replace (bv_unsigned buf + hdr_cfg + k)%Z with (bv_unsigned buf + (hdr_cfg + k))%Z by lia. apply HB. unfold L in *. lia.
      - unfold extz. rewrite bytes_le_to_Z_1. reflexivity. }
    unfold O2ReadLoop.model2.
    (* [comment removed for export] *)
    run_blk_keep (SCR [false; false] [] []) 44%nat;
      try (lazymatch goal with
           | |- sc_denot _ _ _ (SCReadBase (SA _ ?k) _ _ (EVar ?v)) =>
               cbn [sc_denot]; destruct (RB k ltac:(lia)) as [[bs [Hr Hv]] _]; exists bs; split; [exact Hr | rewrite Hv; cbn [edenot ev ENV O2Open.ENV]; symmetry; assumption]
           | |- sc_denot _ _ _ (SCFlat (SA _ ?k) _) => cbn [sc_denot]; exact (proj2 (RB k ltac:(lia)))
           end).
    { cbn [sc_denot branch_taken]. fold cfglen_x. cbn [edenot]. rewrite CFG. cbn [ev ENV O2Open.ENV]. rewrite P7, alu_add_Z.
      unfold bv_ltu. rewrite !u_small by (unfold L in *; lia). apply Z.ltb_ge. unfold L in *. lia. }
    { cbn [sc_denot branch_taken edenot ev ENV O2Open.ENV]. rewrite P7. unfold bv_ltu. rewrite !u_small by (unfold L in *; lia).
      cbn. apply (f_equal negb (y := true)). apply Z.ltb_lt. unfold L in *. lia. }
    cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    (* [comment removed for export] *)
    destruct h_itinK as (_ & PAYL & PAY & IK). apply pair_equal_spec in IK as [MIS MISS].
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
      apply (HTR A vm (map (edenot (ENV vals)) r_rvl) Rx Mx) end.
    - rewrite length_map. reflexivity.
    - unfold slotsR. rewrite !vals_ev_map by (cbn; lia). unfold r_rvl. rewrite PAYL, PAY. cbn [nth app].
      repeat split.
      + exact P0. + exact P1. + exact P2. + exact P5. + exact P6. + exact P7.
      + exact CFG.
      + cbn [edenot]. rewrite CFG. cbn [ev ENV O2Open.ENV]. rewrite P7, md_mul_Z, !alu_add_Z. f_equal. lia.
      + unfold b1s_x. cbn [edenot ev ENV O2Open.ENV]. rewrite P42. unfold ext_val, ext_Z, hdr_b1s. pose proof b1_rng.
        rewrite u_small by lia. rewrite Z.pow_0_r, Z.div_1_r. change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z. rewrite Z.mod_small by lia. reflexivity.
      + cbn [edenot ev ENV O2Open.ENV]. exact P43.
      + cbn [edenot]. rewrite CFG. cbn [ev ENV O2Open.ENV]. rewrite P6. rewrite !alu_add_wZ. rewrite ?u_small by lia. f_equal. lia.
    - change (ENV (map (edenot (ENV vals)) r_rvl)) with (xenv (ENV vals) r_rvl (blobs_ev (blobs0 a0s path))).
      lazymatch type of HR with regs_ok _ ?sr _ =>
        p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) r_rvl idb _ (fun k => eq_refl) srb sr_R _ HR eq_refl eq_refl)) end.
      intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
    - change (ENV (map (edenot (ENV vals)) r_rvl)) with (xenv (ENV vals) r_rvl (blobs_ev (blobs0 a0s path))).
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (know_ok_xfer_entails RSEGS (ENV vals) r_rvl idb _ _ kn kn_R (fun k => eq_refl) HK) end.
      lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    - exact HS.
    - exact HB.
    - exact HcapL.
    - exact HLc.
  Qed.

  (* [comment removed for export] *)
  Theorem header_cases : forall K,
    (forall j buf cap, at_trun K j buf cap) -> forall j buf cap, at_header (hdr_shape K) j buf cap.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr ()) ["Hdr"] "p'0h04__x1h14__x2h27__arithh34__ffh46__sat7h56__sat8h66__sat9h78__varmaph85__with94cstrh:5heq_Lh;2H6h<2Hah=2Hch>1bi001bh?2b0h@3bufhA3caphB1jhC3HTRhD1Kp;1p;4p;2p;3p;5p;6p;7p;8g009Bj10Tg009gj1DTg00:Ej1>Tg063Sj4HTg00;jj19Tg00=Bj14Tg06MQj2?Tg00Laj23Tg00X?j22Tg04Daj2;Tg06N3R0j3<Tg04AIj2@Tg00LDj25Tg06NWj4`Tg0000j2WTg00FQj1VTg000oj2BTg00@bj3ATg00NMj1UTg017Fj2RTg017nj2QTg018Kj3PTg013Ij2OTg015nj2NTg015Nj2MTg00=`j1LTg00:hj1KTg00O2j2:Tg00PLj1ITg00Pjj1JTg00QUj2GTg00R8j2=Tg00^Cj46Tg00>bj1FTg00S>j2ETg00S`j2STg00TLj3TTg00Tkj4_Tg00OPj1^Tg00Onj4]Tg00R[j3CTg06OQj5XTg06PMj6YTg06QDj1ZTg00^nj7[Tg00`6j8\Tg00d:R1f0R2'2p=1f1R3g00gFR4g00geR5P5g00hER6P2g00heF[p=7f3R7P4P5P5P6f2R4P3P2G\p=8g06DaR8g001IR9g00B?R:#0R;#0#0R<#0R=#0#0#DR>#>R?g00c\R@P7P4P3P2CH]A]@]Bp,1LR7%9:#0#4RA'?137ARB12A7RC1;7ARD3<PDg00mIRDP0PBPCp,9at_headerREPDP8P3g05BKp,3fs0RF'@PDP8g01BKRG,5ARH,;7RIg05dZ/@FRFf8RJn0100000020000n0100000020000f6RKf5RLf4RMO4P3PKPLPMP2C`X;BP2O11?7H137HRB12H7RH;<IPIPDP0PBPHPEPDP8P3PFf<RFn0100000020000f:R8f9R0PJO4P3P8P0PJ%D<#>p,4data'WR<#VRI,B@AA@7IRLeRNPL%U<R<%1IRI%4;RO%9;#9#0#4RP'RRQ131O%1P1QOPRR,31[[RS%1ORTg01<WRUAPOP3UW<RP%1R\U^<TRTp,3sp0,O>R>%4=R='NRU%1>%1=1M>=#1[[R=g00kER>#LRR%K>R>1:@3%I@RO%J@RVP@1G@ARWg00f_RX1=@:R:C6,7VRY%F5R5PYC81EV6R6P2P4g00miRY,BD1S24=ADYdAT@13C_R1b3b7b8X0@12A212A3[^0@P2P7P8O2b2b4b5b6b9b:PNPLP<PIPQPSPPPTPUP=PRP>P@1:@4P3%^@C]RYPOPVP@P:g00iE1=@;R;9C@WC6,7VRDP5PDC8P6P1b3b7b8X0@X1@15A3RD,3215A4,33[^0@^1@P2PGP7PKO3b2b4b5b6b9b:DXX=BP2O1PFP8P0PJPNPLP<PIPQPSPPPTPUP=PRP>PYPOPVP@AC@W:PXP;C6,7VRVP5PVC8P6P1b3b7b8X0@X1@15A2/2312D4[^0@^1@P2P7PGPKO3b2b4b5b6b9b:f;P8P0PJO3EYX=HP2O1n200210000000021100011000b?b>X;CP2O1n200210000000021000011000b?b>PE%ZMP4P3P2O4eXA@X@?XB9WCWDo"). Qed.
End Hdr.
