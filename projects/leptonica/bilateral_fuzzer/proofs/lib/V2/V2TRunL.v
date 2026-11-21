(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (proofs and definitions restated for the model's changed definitions; fz_call's recorded (KReplay) proof re-proved by tactics, as pix_orient_fuzzer's copy, less its step for a premise this binary's fuzz call does not have; sideT_block and incb_block re-proved by tactics for the ledger's vDSO reservations; the exit tactic's thread-pointer and thread-id addresses corrected to this binary's). *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2ExitBase V2StdioDefs V2Exit V2Startup V2StartupDefs V2StartupFacts V2MainEntry V2LibStdioCall V2OpenFail_defs V2OpenFail_tail V2OpenFail_tail2 V2Open_defs V2Open V2Oom_defs V2Oom V2MemPreds V2Malloc65536 V2DirRead_defs V2MemcpyBase V2Memcpy V2ReadLoop_defs V2ReadLoop V2Grow V2Hdr_defs V2Hdr V2FuzzIface V2TRun_defs V2TRun.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac FPSteps.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2TRunL () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib2V2:V2MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;is_kimg_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC59OSSVerify5KrLib2V2:V2MemPreds9img_clearC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib2V26V2TRun5callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun6paylenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun1LC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun5sideWC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop6in_winC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib2V2:V2ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun;sideW_blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop7DATA_RSC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib2V2:V2ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs8kn_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface>A_LEPT_HANDLERC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface:LEPT_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs5LGLOBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib2V2=V2Malloc655366env_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open9above_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun<paylen_factsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib9micromega;ZifyClasses3injC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun:bufW_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedc59OSSVerify5KrLib2V27V2TRunL=paylen_factsLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V27V2TRunL;sideT_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun7payloadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc65536:live_whereC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2V2;V2FuzzIface7A_EMPTYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V27V2TRunL6slotsLC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:is_kwr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun5roomTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr6slotsRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V25V2Hdr6hdr_b2C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<In_nth_errorC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28expr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIfaceAfuzz_margin_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface;fuzz_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room9fuzz_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room;fuzz_nonnegC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V27V2TRunL;kimg_clearLC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC59OSSVerify5KrLib6Common8VmLedger;init_sp_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2TRun=ownedA_rangeTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open3ENVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc65536>regs_ok_same10C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V27V2TRunL@know_after_fcallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V27V2TRunL<env_ok_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:aroom_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs7tl_sr2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2TRun_defs6tl_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8PropExec7FPState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface:A_LEPT_SEVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface:A_LEPT_PMMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface8A_GOT_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface8A_GOT_HIC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib2V2;V2FuzzIface7PC_FUZZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open4fds0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2V2;V2FuzzIfaceAfuzz_calls_nonnegC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC59OSSVerify5KrLib2V2>V2MallocLayout4LU16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2MallocLayout6LU17okC1?~~~~~~~~~~~~~~~".
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
ltac2:(KReplay.run1 (kr_t_V2TRunL ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p10000p4p70g000`R0p4p710R1p8p1001>p4p70P1p8p1001lp4p7210P1p8p1002Xp4p70P1p8g003NR2p4p710P1p8g003oj1HTg004Tj1wTg0052j1gTg005Uj1~Tg0067j1uTg006Wj3qTg007Rj3KTg0080j25Tg008PR1j10Tg0090R3j23Tg009Lj26Tg009gj2YTP2k30ITg00:>j6sTg00:Zj28Tg00;7j2>Tg00;Qj37j1nTg00;kj3_Tg00<Qk10>Tg00<oj6^Tg00=Xj4\Tg00>?j1TTg00>dj2PTg00?Fj1|Tg00?fj2XTg00@Dj4LTg00@bj1yTg00A@j1xTg00Akj2JTg00BNj1cTg00C3j3QTg00CVk20HTg00D8k20GTg00Ddk30FTg00ECj4rTg00F5R2j21Tg00FRj2aTg00G8R4j1VTg00GXj4Nj3pj2ok10ATg00H4j2Wk10DTg00HVk20ETg00Hmk20@Tg00IPk30?Tg00Iml<lTg00JRj1CTg00K1k10<Tg00KOk20;Tg00L0j3iTg00LYj2hTg00MBk108Tg00M`k205Tg00NCk104Tg00Nek403Tg00OPj8RTg00Omk502TP0j6eTg00PKk307Tg00Pnj2tTg00QJk200Tg00QglBkTg00RMl<dTg00S2j2}Tg00SLj4UTg00T7j7[Tg00T[j3`Tg00UDj2MTg00V0j3ITg00VPk60BTg00W4k70CTg00WXj7{Tg00X<j8zTg00X`R0f0R5'tp=920005p=2g00Y>R6/>5p=;g00Y\R7P7P7P6P6P6g00Z;P1P1P1f6R8g00Z[f5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P1P1P9P:P;P<P=P5M<dp=bP6P6P3f7R>P3P8P9P:P;P<P=P5M<lp=Z1305p==1t50p=<A7650p=BA76;<,6:16=5'}p=?P<g00[BR3g00[aR?P?g00\AR@P6P=g00\aRAP5CUg00]HRBF[p=vA76=5p=OP6P7P6P6P4P:P1P;g00]hP<P=P5M<dp=mP7P7P7P6P6P6g00^UP1P1P1P2g00_5P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00_XR2g00`DR4,M=;I5p>0:A`6<=/M4=I25p=E1M<41M=4=I255I2p>09P=P3P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P3P?P?P@P<P=P3P?P?P@P5PBF[K0Cp=:P6P=g00a0P5CUp=FP=P3P?P?P@P5PBF[p=DP<P3P?P?P@P=P5F{p=]P6P=g00aWP5CUp=SP;P3P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI2=59I2<p>06g00b>R4#HR3#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P0%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|2RV%u2R2P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J63R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00bcR_g00cCR`'>Ra20G5<=7_`dB0F60=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA0RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P1%n6%0=R1/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P08%=8%28RiP8%<8%BiD?%2>P611cNRc,P0%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P0%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00ccRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP2P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20560R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c3,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P0K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP2P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;1AKD=<5q:eWGXM7WKXI6WHo"). Qed.

Section TRunL.
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
  Let slotsT := slotsT sp0 a0s path envv tid data.
  Let L := L data.
  Let cfg := cfg data.
  Let paylen := paylen data.
  Let payload := payload data.
  Let calls := calls data.

  (* [comment removed for export] *)
  Definition slotsL (vals : list word) (buf aligned owned : word) (rem : Z) : Prop := slotsT vals buf aligned owned rem.

  Lemma kimg_clearL : forall E M kn lo hi,
    know_ok RSEGS E M kn -> existsb (is_kimg_cov lo (hi - lo)) kn = true -> img_clear M lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunL ()) ["TRunL"] "p'0h01Hh12Hch23Hinh31xi001xh41ih51ni011nh61ai021ah71ei031eh81mi041mh91Ah:2H1h;2H2h<2Hah=3Hexh>4__x1h?4__x2h@4__x3hA4__x4hB4__x5hC4__x6hD1fhE3hi0hF1lhG3lo0hH1EhI2HKhJ3HKKhK2HihL2HnhM1KhN1MhO2_HhP3_H0hQ7__arithhR4__ffhS6__sat3hT6__sat4hU6__sat5hV8__varmaphW5__withX2a1i052a1hY2a2i062a2hZ2e0h[5heq_Lh\9heq_callsh]7heq_cfgh^:heq_paylenh_2hii072hih`1ki081kha2knhb2loi092lohc2n1i0:2n1hd2n2i0;2n2he1vi0<1vhf1wi0=1wi0>1bp&0p;1p;4p;2p;3p;6p;7p;8g003oj14Tg004Tj1aTg0052j1_Tg005Uk108Tg0067j1XTg00dBj4xTg00:Zj21Tg00eRj2ej3=Tg00f]R0j3ZTg00g9j3KTg009LR1j2>Tg00gPR2j2NTg00gjk306Tg00hMj36Tg00iIj3QTg00jTj2TTg00k3j2[Tg00l>j3RTg00mIj2VTg00nTj2<Tg00F5j2HTg00o1j3mTg00Pnj25Tg00oTj2jTg0104j3`j4PTg011Fj3^Tg011gj3iTg012Ij6hTg012dj1DTg013Bj2]Tg0090j29Tg00FRk207Tg00NCj1fTg00;Qj37Tg013_k105Tg00;7j2JTg014Sk104Tg015Hk102Tg016:k101Tg00BNj1:Tg016jj2~Tg017Rj3}Tg0186j2|Tg018`j2{Tg019Qj2zTg00JRj1GTg00LYj2ITg00T[j3MTg00UDj2dTg00?Fj1wTg00V0j3cTg00MBj1vTg00?fj2UTg00@Dj4ETg00@bj1uTg00A@j1tTg00Akj2BTg00SLj4STg00PKj3sTg00C3j3rTg00M`j2qTg00CVj2pTg00D8j2oTg00Ddj3yTg00ECj4nTg01:1j2WTg01;<j3\Tg01<Gj2OTg01=Rj4YTg00:>k600Tg00T7j7lTg00W4j7kTg00X<k803Tf0R3#4#4p=gg00bcR4g00cCR5773p=2g01>]R6f1R7;K3p=0f2R8?=73=745p=3P4P8P7g01?hP5P3J00p=Ag00X`R9/53p=;1587/>3p=8g00Y>R:P7g00a0P3CSp=FP7g00[BR;g00[aR<P<g00\AR=P3g00]HFlp=@P8P;P<P<P=P7P3Fkp=b%:3#:p=C%43#4#4#4p=?f3R>P;P<P<P=P8P7P3L03p=Lg01@Dg00b>R;#4R?#4R@#4RA#4RB#gRC#aRD#_%aA#_RA$08RE[%X6g01ALRFf4RGP>P8Cx1178,e8=Z6>#2P0p4p710R0P4\3RH%X7RIP1AZ873#2AKG38P>P3O1#2'>X3>,N>[RJAK>37P8P3O1#2'>X38,N8AZ>87#2RK[f5RL?K3>PGP3O1#2'>X3G,NG\KB06873P7n2001000000120000000WFWDW9PJ^FI^DH^90P3P611>G,eGPLP7O4f6R0,0311GL=3L3'>X36,N6P2P6f7R2,0311L0=303'>X36f8RH?60LP3f9RI,03112H=3H3'>P1f:R2,0711HI=3I7f<RJ?62IP310>Jf;RK/1J=3JGP6f?RM,03f>RN/1M=3M7fBROf@RP;6M]1]2PLg01B^RQg00Y\RRg01ChRSAQ873fDRT'0fCRU/1TRVAQ>8753TfERW11TWRXAQG>83=P4p-0P3g01E1RYg01ENRZn0110>00020000R[X74R\;A3PYfHR]fFR^;6W/T3R_b0W1W2WeWfW6P8P7P3O31[73/0OfAR`/1ORa1[8753O11OURb1[>85=U?A\3PYA6^TU/T3Rcb0W1W2X5SX6QP7P3O2AR873/0TAR>8793TVARG>89=WX?A\3PYP_b0W1W2X`RX5SX6QP8P7P3O31V73/0O1V8793Oa1<>URR1HUb/<8Rd;m3%2R%2d'>P11<GT#21HTV/<>#2fGRd?6WTP31<0^#211^dRR,Hd/<0#2P11<73#21587[Re15731<87#2Rf[15>8\f1j73P7n2001000000120000000X8:X5:RfPe^8:^5:ReP3PIfIRgP8O315IgPfPeP3fKRefJRf/1e'HReP2P>O315e2fORefNRg5`FRhfMRi5^6103ePFfRRjfQRkP7CP[^36[103gPFPkfPRlP7CP[^36A`Fle=^6g[Ai6hiPf1VJKRKP2EhPFPePgPKCPP1f=RK#;%D?RF%DC']RC193K98N3Pk207D7RNO1%fARA57E[^4:58JA6lgiP3%;M193P98`3fTRlPNO1=7EA[^4:98MCP115PC193`98O3fUR`PNO1=7EA[^4:A6ljkP315OC193T98W3fXPNO1=7EA[^4:fV193`783P8P7p,4dataRA$05RE,J:p,5calls=7:EREePE&04ARE,J:p,6paylen=7:EREePE&02ARE,J:p,3cfg=7:EREePE&01ARA,J:p,1L=7:ARAePA%:?RA#:#4#DRE,~F199F%;E1]FERN,99[[%;FRCA}FE7VZW<%;N\Z^<Cp,3sp0,|DRD%DBRB'{%;D%;B1zDB#;[[g00_XRBg00ccRC#G#GRZ#GRN#GRE#G,I:1I:Z1I:CRC5M:5M:g00`DRZ'd1I:E1I:N=M:C5M:/dZ%wB5cB3c%XBP:P:%v:RBP8P:1U:0P0PBCECEP7P:P:1U:LP0PBCEP>1U:GCECE%u:%t:RB%:@,B:R@1B:?R?'F,@BP:P?g00aWRZ%4A,B:RACS,@B5bB%f<R<PBAs:A@9r:@%:;RA,B:RC'F,@BP<PB1B:;R;/F@,@BP<PB%:ARA#:#C#C#C#C#C#C#4#g#?#?#?#?#?#?#?#DR@,q:1B:A'F,@BP<1F;?,@BP:P?PZPCCS,@B5bBCLCLCLCL1pB=P3P81J451o38#2dAy:97CnbRbVbWX>:X?:X@:XA:XB:XC:197L98G7110L,HL/5>158015@019L098GL[[[[^>:^?:^@:^A:^B:^C:P3f^f_PDPgPIPePHPUPWp,4SPloO:bQbSbTbUb[b]b^b\O2WKX4:fW?6`leWLWPP7P3O2n2001000000121000000W0WOP7P3O2n2001000000121000000bJb;b0b:b0W;W:P7P3O2n2001000000121000000b1W1W2XE:XG:P7P3O21W73/0O1W8793Oa1W>89=UbP[XZ4R4;A3PYPcb0W1W2X8:X7SP7P3O2A\873/0TA\>8793TVA\G>89=WX?A43PYP_b0W1W2XE:XG:X7SP8P7P3O31O73/0O1O8793Oa1O>89=Ub?A\3PYPcb0W1W2X5:X6QP7P3O2P>P8P7P3CY/0^11W^PGP>P8P7CY53^PLPGP>P8CY9=dR?A\3PYA6f]d/T3b0W1W2Xd:XYQXc:XXQP>P8P7P3O4n0110800083010210=10<2010210130102101108211091072010310430103109107201021014010510:10610;P7P3O2W1W2P7P3O2n2001000000121000000W0XM6P7P3O2n2001000000121100000b=b0W=WIX_:Xb:WaWNWHo"). Qed.

  Lemma sideT_block : forall A vm M buf cap owned E log,
    sideT A vm M buf cap owned -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    sideT A vm (mem_denot E M log) buf cap owned
    /\ forall x : word, ~ V2ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x.
Proof.
  intros A vm M buf cap owned E log (HW & Hown & Hq) Hlog HE0.
  destruct (sideW_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A vm M buf cap E log HW Hlog HE0)
    as (HW' & Hout).
  split; [exact (conj HW' (conj Hown Hq)) | exact Hout].
Qed.

  (* [comment removed for export] *)
  Lemma know_after_fcall : forall (A : AS) vals (M M' : word -> option byte) vm R' kn,
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> kn_vars_lt (length vals) kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a : word, ~ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) -> ~ al_globals a -> ~ al_errno_slot a ->
                      ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8)%Z ->
                      ~ (bv_unsigned sp0 - 208 - LEPT_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    (forall a : word, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_fcall kn).
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunL ()) ["TRunL"] "p'0h04__x1h14HLv0h27__arithh36__sat3h46__sat4h56__sat5h64cstrh75heq_Lh89heq_callsh97heq_cfgh::heq_paylenh;4__ffh<4__p1h=8__varmaph>5__with?4__x2h@4__p2hA1rhB2HahC1bhD2HghE4Hlt'hF1ahG1HhH3HnthI2HxhJ2H0hK2HehL2HlhM6__sat6hN6__sat7hO4__x3hP1xhQ1AhR2H1hS2H2hT2HIhU2HKhV3HLvhW2HMhX3HfrhY3Hg1hZ3Hg2h[3Hgrh\2Hhh]3Hhih^3Hihh_3Hloh`3Hltha2Hshb4Htophc1Mhd2M'he2P0hf2R'hg6__sat8hh6__sat9hi2knhj1mhk1nhl1ohm1si001shn4valsho2vmhp1zi011gi021lp%0p%1p&0p;3p;2p;1p;4p;5p;6p;8p;Ap;<p;7g01Ejk30uTg01G3k30tTg01H<k20WTg003oj13Tg004Tj1kTg0052k10BTg0067j1~Tg005Uk10TTg00BNj1<Tg001lk20MTg00JRj1pTg0080j2;Tg01ToR0k20GTg00;Qj35Tg01UIk20`Tg00dBk40DTg01VPk50[Tg01WSj1aTg0186j24Tg012dj1@Tg00:Zj2CTg01XKj2HTg01MAj18Tg01YNk20>Tg01ZOk20<Tg00F5j2BTg00NCk109Tg01[Sk10ITg0090R1j22Tg00PnR2j21Tg01\Uj1vTg01]]j3uTg00K1k10dTg013Bk206Tg013_k10aTg014Sk10^Tg015Hk10]Tg016:k10\Tg008PR3j1=Tg00>?j1PTg016jk202Tg017Rk301Tg018`k20ZTg019Qk20YTg00?Fk10ATg00?fk200Tg00@bk10XTg00A@k10VTg00Akj2jTg01^:k30@Tg00CVk20UTg00;7j2_Tg00D8k20STg00Ddk30RTg00ECk40QTg000`k60?Tg01^]R4j2}Tg00M`k20=Tg00Nej4{Tg01_5j4zTg01J1k20;Tg00MBk10PTg01`Bk20OTg01`ek10:Tg009LS00j27Tg01aBk60LTg01bGk20KTg00g9j3:Tg00gPj2ZTg00:>j6cTg01bgk20HTg01cNj2rTg01cjS01k20JTg00V0j3iTg00S2S02j2lTg01dJj3LTg01ddj3NTg01ONj4OTg01e>j4wTg00SLj4eTg00C3k307Tg00LYj2tTg00T[k303Tg00UDk20rTg00jTk20FTg01eXk50qTg01fXk30kTg01gRk10jTg01hYk80iTg01iemA0hTg01jok10gTg01kkk20fTg00Imm<0ETg00=Xk40eTg00T7j7mTg00W4k705Tg00X<k804Tg00PKk30cTg01lok30bTg01mLk30lTg01mik40mTg00@Dk40nTg00VPk60oTg00WXk70pTg01nIk60_Tf0R5#3#3p=>g00ccR6-0f5p=V%35#3#3#3p=\f2R7f1R8/25'7p=^f3R9/171285'7p=0%35#<p=qA5785#8p=I1l85,l7p=b%<5#<p=?%35#3#3#3#3#3#3#3p=]%35#3#3#@p=K%<5#3#<#<p=U%<5#3p=F1178/75p=Dg00Y>R:/_5p=Ag00Y\S03P:P0P3P2g01nmf5R2f4R0P9P7P8P5N<0Ep=X20G09P7P8P5H0ep=Sg00X`R;/15p=612;5p=Q%35#@p>0C20=:5p=9P7g00[BR<g00[aR=P=g00\AR>P:P8g00a0R?P5Ceg00]HR@Fmp=GP0P<P=P=P>P9P<P=P=P>P:P7P?P8CeP@FmP5K05p=Rf6RAP<P=P=P>P2P0P9P<P=P=P>P7P8P5L04L04p=JQ03P:P4P3P1g01oOP6P;P9P7P8P5N<0Ep=|P7P<P=P=P>P:P8g00aWR1P5CeP@Fmp=EP9P<P=P=P>P7P8P5L04p=MB0c:85p=[g0201R3,C5p=dP:P8P?P5Cep>0NP9P<P=P=P>P7P8P<P=P=P>P5P@FmK05p=yB0b::5p=hB0l::5p=g11971285'7,70p=T1778/l5p=`%a5,28p=fP:P:P8P5H0mp=oP:P7P8P5H0np=WP8P<P=P=P>P5J0op=nP7P<P=P=P>P8P5K05p=YP7P<P=P=P>P8P5K0pp=sP8P<P=P=P>P5J0_p=xP:P8P1P5Cep>08P8P<P=P=P>P5P@Fmp>0sp,2ALR@p,2CLR<p,3ASR:0u@<60t@R<+0Wg00b>R1#3S04#3S05#3R?#3R4#>RB#kRC$0BRD#~%k?$0BRE$0TRF\DS06Q06g01RmQ04#<S07#k00MDg01>]#~%p6RG1;D2+0G%VAp,3sp0S0855Dg00bcRHf7RI,;D00`7g00cCRJ35g01ALS09p,3ENVRKf8RLO1PIP9H0DP@P<f:R<PLPAI0[%aIQ08,4CRM%>B#\RB#>RN#>RO#3#>#\RP#@RQ'CRR55:1H@514C5RSf9S0:#a3^#820>@8#820<@7#8g0212RT14C9RUPU%@?S0;,BTC0S0<#8S0=%<1RT#q#\R?#@S0>,CMS0?g0224'CS0@14C0RVPVQ0?C0#8f?S0AP2O1f@RWP2O155F[[[[[^FDf<RXP5O1&09ERE5IF14C8RY&0I@RZ'21H@8f;R[#a7^YPXP8O1=IFE3b[^FDp,4SPloS0B%<TS0C#<#?#?#?#?#?#?#\#]#]#]#KS0D/1Mp,4SPhiS0E%3P#\#]#]#KRP,1Mp,5AL_hi%<1#U#F#]#KRT,1ZQ09PK%vXS0F9uDWR\O1S0GQ0Af>R]g0232R^&0d?R?%@NS0H'CRNP?g023kR_%31#>#F#F#]#KS0IPD%VWS0JQ04#@R`Q07#3#>Ra#@Rb+06RcQ07#<Rd#?Re#@Rf-06`Rg,1S7DSXCDRhPDQ08Php,4dataRh$0aRi#Ap,5calls=5:iRieRjPi&0^hRk#Ap,6paylen=5:kRkeRlPk&0]hRm#Ap,3cfg=5:mRmeRnPm&0\hRh#Ap,1L=5:hRheRoPhPGfDS0K,;DRp%@1Rq%=pRr'1RsPGPq%AqS0LPpPr%ArS0MEXP]DSRtPsfES0N,;DRu#PRv%=u#6Ru202`f%Q`Rw%6f%Qg[[%6`Rxg01ENRyB01`f8UWB%6g\y^Bx202`bS0O%6b%Qc[\wS0PB01`b8VyXBxS0Q%6c\y^BxS0R&0CdRd-02`Rb%6d206`dRf#Q[\wRwB01`d8VyXBxRd%6f\y^BxRx%@4R4-0ZMRy%6M%6420YM4#6[[R4g00_XS0S$0ARfQ0S#~Rz200:8R{&0X:R|&0V:R}1j:1R~%9P5G}&09=R=P}Q0D#9S0T=G}~P=P}P}%9`R`%ka60@:RaP~%ke:0@:`9G}~DRFJ20U}>R>P5P71_HJ20S57=5HJdB0R:;8H0QRJb;b=b>X0:115PQ0D/18117g9Dc7[[^0:P5PMQ0EQ0BO3b2b3b4b5bMbNbgbhb6b1b7b9b:b8Q0JQ0:J0?%V\PWQ0FP6PjPiPlPkPnPmPoPh1}6p%Qr1_:;S0JPpPrQ0MC|PtPsPvPuPbPwPdPxPyP4PfPzP{P|P}%9q=G}~P=20=:;Rr=E}~CMP>PJb;b=b>X0:S0M11q5%Q8[^0:S0EP5fJS0U,;DS0V#=S0WP2O2b2b3b4b5b6b1C{b7b9b:b8CzJ0?Q0G00;6,4CRp11pg5DcePjPiPlPkPnPmPoPhPtPsPvPuQ0OQ0PQ0QQ0RPbPwPdPxPyP4PfPz&0P:RpP|P}P}Pr%9TS0RQ0R%9QS0Q,[a5E}DRP>PJb;b=b>%6T1CcQ7^TP5b2b3b4b5bMbNb6b1b7b9b:b8P;P_P_%dcC0ePjPiPlPkPnPmPoPhPtPsPvPuPbPwPdPxPyP4PfPzPpP|P}P}P}Q0Q-0O:%9?S0PQ0H#9S0O'[S0XQ0XQ0P5G}DRP}Q0P00NrCyP>PJb;b=b>&0:Q11N?Rr7DN11?;R;'7P5b2b3b4b5b6b1b7b9b:b8&0:3?DNr/7;ePKfAS0Yf=S0Z#v5uDO1S0[P^PNP?P_PSJ0L#8PDfBRK%v]R;5uD#V14C7Rr/2_20K::R3A:35^R^%h5S0\PUPU%g5S0]DTXA3'Z'7Ru11_rRv%dSS0^7^r1BSNRsPrPr1BS?RtC03b#8XCDP5%VKRcPKP;P6PjPiPlPkPnPmPoPhfFS0_,;DR;,}6%=;Ra#QQ0JP;Pa%AaRgC|PGP;11qaR\PGPqQ0LP;PaPgEXPWDSP\fGS0`,;DS0a#PQ0a#=R\#6PbPwPdPxPyP4Q0MQ0EP5fLS0b,;DS0c#=S0dP2O2b2b3b4b5b6b1C{b7b9b:b8CzEc12Y_P^Q0\PrPrQ0]DTXA3,Z311_Y14CcRc#d,2Y1BcNPYPY1Bc?C03`3`#8PDfCRc#VS0e12U_P^Q0\PVPVQ0]DTXA3,Z311_UQ0^,2UPsPUPUPtC03`3`#8XCDP5Q08PXEc%dMS0f9^vr1BMNS0gPrPr1BM?S0hC05bu#8PLP91H@9Q0Y#a7^US0iQ001H@0S0j1fVKS0kg01E1RuP51H@AS0l14CIQ0N'fS0mp,8AL_grantPLP8O2%@BRB14CLS0n%@OROQ0nQ0nPTC0#83DQ00Q0:,4CS0o,1BPOQ0oQ0oPTC0#8PuP514C[,1BPO14CXS0pQ0pPTC0#8P:fKS0q#aS0r14C]RX/25Xp:S0sP2PRPcEcQ0Z,4C/2RS0t20HXO12XO1rXO+0JQ01Q0A,4CRv/2O1rvOPuP514CWS01/2OP]Q0Y,4CRt/2TS0u%31#>#U#?#F#>#F#KRs%31#>#U#?#F#>#?#KS0v'oR^%<1#U#>#F#U#q#KRg%<1#U#q#>#F#>#?#KS0w'oRa%31#U#\#?#F#q#F$0CR;%31#U#\#?#F#F#KS0x'oR11oBORP&0A3S0y5i3S0z5i3S0{5i3RH5i3R`9:35S0|Q0\14CKRePeQ0]DTXA3S0},Z3Re'7S0~PTPtPtPRC0S10Q0gPtPtQ0hC0S11'lS12Q0uPePjPiPlPkPnPmPoPhPGfV,;DS0uQ0u#=Re,1qS13PGPqQ0LQ0uPe%AeEXfPDSS0uQ13fW,;DRe#PS14%=e#6S15PbPwPdPxPyP4p-0RePfPz200:7S16?W7p9Wp8S17P|P}Q07,j:Q0Q'[9E}~S07P=P}1n}0S18Q0R=G}~S19Q075Y}1n}2S1:5s}5s},x}S1;P=Q0R9E}~S1<FJP>PJb;b=b>X0:X?:X<eW@1C8QS1=,25PTP8P81C7QS1>C0=b90Pu[127T[[^0:^?:^<e^@eP5Q0gQ0q,4CS1?Q1?Q0hC0S1@Q1?/2TQ0|Q0\Q0b,4CS1AQ1AQ0]DTXA3,Z3'7S1APMQ1?Q0ZfHS1BO6b2b3b4b5b6b1b7b9b:b8P3Q0}PPA:3P`%hPPtPt%gPC0S0}A53^PA:3PHA53aPQ0{9:3PA531PQ0z9:3PA53PPQ0y9:3P1_3P3L3N3N3NPjPiPlPkPnPmPoPhQ0uQ13Q14Q15PbPwPdPxPyP4PfPzQ17P|P}P}P}%9ORPP~Q1<DR,x}S17P=P}%9B=G}~S0yP=P}Q07P=P}Q1;P=P}Q0yP}208~PCyFJFJP>PJb;b=b>X0:X?:X<eX@ePOP5P5PTC0Pu[11B81C9Q,27S0yPTP9P91C0QC0S1;=b2APu[PBP0P0POC0[[[[^0:^?:^<e^@eP5Q1@Q1APMQ1?P]Q0AQ0ZQ1BO8b2b3b4b5b6b1b7b9b:b8Q0}eCOCwCO3LO1WLP5O1Q01/rOP]Q0~Q12Q10Q11PjPiPlPkPnPmPoPhQ0uQ13Q14Q15PbPwPdPxPyP4PfPzQ16?W8pS15P|P}P:P~g024fPPCe-0s}P=P}Q17P=P}Q04,j:RPQ0Q'[9E}~RBP=Q19=Y}BCMFJP>PJb;b=b>X0:X?:1r5O128TS199DO8Pu[Q0yQ1;[[[^0:^?:P5PMQ1?P<P]Q0ZO5b2b3b4b5b6b1b7b9b:b83L3NO1WLP5O1n200110000021110211101bmbEWZWYP8P5O2n2001000000121000000bFWEWDP8P5O2n2001000000121000000WGQ0i#8e20>@9S0ip,7AL_globP0P5O2PgPVPVQ0wC0P714C2RO/2TS12Q0|Q0\14CARBPBQ0]DTXA3S0~,Z3S11'7S1011TO12ORQ0gPOPOQ0hC03`S1?Q12Q11PjPiPlPkPnPmPoPhPGQ0VQ0W,1qS0yPGPqQ0LQ0VQ0WQ0W#AEXQ0KDSS1;Q0yQ0q,;DS0q#PS04Q0q#=#6S0qPbPwPdPxPyP4PfPzP{P|P}1n}9S17Q0w#99E}~S145Y}P=Q1<CMP>PJb;b=b>X0:X<eQ0w,25S13,78Q19[^0:^<eP511gvPvP<O3b2b3b4b5b6b1b7b9b:b8P3Q0~PaA:3a`%haPOPO%gaC0S0uA53^aA:3aHA53aaQ0{9:3a1_3a3L3NPjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}P}P}%9gP~Q14DRS14P=Q14CMP>PJb;b=b>X0:Q139Dg5PgP8P8Q0wC0[^0:P5PvP<O2S0wb2b3b4b5b6b1b7b9b:b8Q0ueCOCwCO3LO1bDWDQ0i#8e20<@9S0ip,8AL_errnoP0P5O2P;PVPVQ0xC0P7Q10Q1?Q12Q11PjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}Q17Q0x#99E}~S115Y}P=Q1<CMP>PJb;b=b>X0:X<eQ0x,25Rg,78Q19[^0:^<eP511;vPvP<O3b2b3b4b5b6b1b7b9b:b8P3Q0~P1A:31`%h1POPO%g1C0S0~A53^1A:31HA53a1Q0{9:31A5311Q0z9:311_313L3N3NPjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}P}P}%9;P~Q11DRR1P=P1CMP>PJb;b=b>X0:AD;5gP;P8P8Q0xC0[^0:Q0wb2b3b4b5b6b1b7b9b:b8Q0~eCOCwCO3LO1bKWKQ0i#8eQ0<P812VTR;Q0|Q0\POPOQ0]DTXA3S0i,Z3Rg'7S1?PTPVPVPRC0S10Q0gPVPVQ0hC0S0h'lS0gP;PgPjPiPlPkPnPmPoPhPGfIS0~,;DRg%=gR;,1qR1PGPqQ0LPgP;%A;EXPcDSS0wP1Q0V#PS0VQ0W#6S0WPbPwPdPxPyP4PfPzP{P|P}Q17%9sR;Q0;#9607:9E}~Rg5Y}P=Q1<CMP>PJb;b=b>X0:X<eQ0;,Bs,25Ra,78Q19[^0:^<eP511sXPXP<O3b2b3b4b5b6b1b7b9b:b8P3Q0iP^A:3^`%h^PVPV%g^C0R`A53^^A:3^H1_3^3LPjPiPlPkPnPmPoPhQ0wP1Q0VQ0WPbPwPdPxPyP4PfPzP{P|P}AG};~R;=Y}gP=P}P;P}Q0v#9-08~CyCMP>PJb;b=b>X0:ADs5aPsP8P8Q0vC0[^0:P5PXP<O2b2b3b4b5b6b1b7b9b:b8P`eCOCwCO3LO1W\Q0=eQ0@PUPUQ0?C0R`P8Q1?Q0gQ10Q0hPjPiPlPkPnPmPoPhQ0wP1Q0VQ0WPbPwPdPxPyP4PfPzQ15P|P}P}P}Q0>#9,[~R1Q0O'[PPAE}P1DRP=P}Q18Q1:P}P}Q0X:07:~PPQ0P:07:~9E}PDRR~5s}5s},x}P=P~FJP>PJb;b=b>X0:X?:X<eX@eQ0>,C5R~Q0H'CP8P8P~C01B8NP7P71B8?C09b90Pu[1B7NP9P91B7?C0[[^0:^?:^<e^@eP5PTPXPXPRC012XTQ0|Q0\PvPvQ0]DTXA3,Z3'7PXPMP<P[O6b2b3b4b5b6b1b7b9b:b83N3NO1Wa%8`eO6bHbHWHXPDQ0[00;6,4CR`#dPSPSP`C0Q0YP8O1=IFEPDQ0A#vR`9uDc#VQ0^PUPUPSC0XCDP8Q0ePcP`P6PjPiPlPkPnPmPoPhQ0a,}6%Q\Q0JQ0aP\%A\R`C|PGQ0a11q\RXPGPqQ0LQ0aP\P`EXQ0YDSPXQ1B,;DRX#P%=X#6PbPwPdPxPyP4Q0MQ0EP5fMRX,;DR`#=R\P2O2b2b3b4b5b6b1C{b7b9b:b8CzEcQ0e,4CR3#dPrPrP3C0PDQ0K#VQ0^PVPVPSC0XCDP5Q08Q0ZEcQ0fPUPUPMC0PLP0P7O212VZQ0jQ0k'7PcP0O1=IFE3bQ0212OZ1H@21fOcQ0KP2O1=IFE3`Q0NPAO1=IFEROP512BZQ0_PIO1=IFERVPjPiPlPkPnPmPoPhPGQ0cQ0d,1qRUPGPqQ0LQ0cQ0dQ0d#AEXQ0_DSPU%P`%6\PbPwPdPxPyP4Q0S%pGR\#pR`#p,t:1t:`1t:\1t:6603:603:603:g00`D+0r;ifPzQ15200:99Wp97W9P|P}Q0C,j:R6=E}PP=P}Q05,j:R\Q0Q'[R`=G}6RUQ1:5Y}P=P}Q0R9G}PP=P}Q0T=G}\R\P=P}P\P=1n}ACMFJFJP>PJb;b=b>X0:X?:XO:X<eX@e1275Q1>?D90117TQ0D/10Q0D/12Q0:[[[[[^0:^?:^O:^<e^@eP5Pu12tMPtPMPZP<Q0ZPKQ0KQ0BO:b2b3b4b5b6b1b7b9b:b8+0FWGP5O1Q0lQ0K,fB;`OQ021H@IQ0m'7PVQ0`PLO1=IFERVP51H@LQ0nQ0_#a3^Q00Q0:,H@Q0oQ0`'fQ0~P<O1=IFEP51H@[Q0pQ0U'fQ0bQ0ZO1=IFEP:Q0rQ0sP5PRPcEcQ0tPjPiPlPkPnPmPoPhPGfS,;DRh%=hRo,1qRmPGPqQ0LPhPo%AoEXPXDSPmfT,;DRm#P%=m#6PbPwPdPxPyP4PfPzAW{7pQ169Wp77W7P|P}AE}6`P=P}Q189Y}UP=Q1:FJP>PJb;b=b>X0:X?:X<eX@e1C5Q,28Q1=?D79P2[[^0:^?:^<e^@eP5PuQ1B,4CRC/2MPCPMP<Q0KO6b2b3b4b5b6b1b7b9b:b8bE+0FWEWDP8P5O2n2001000000121000000WJP5O1P5XGVP5O1n200100000021100010000WJP5O1n200100000021100011000blbIbIWWWIXPDQ06Q03Q0I/1Y%=8,Br/1_P0P9P7P8P5I0qWSWRWkXFDWjP[Q09PWQ0Fp,3AMBp,3a0sp,4path40k$0jQ0AP[PLPIL0iNA0hQ09Q0GP]&0g[H0Deb^b]b_W[WXWbWTWUW`WeWVWiWfWoWdWcWnWQo"). Qed.

  Lemma env_ok_fcall : forall A M M' vm,
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a : word, ~ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) -> ~ al_globals a -> ~ al_errno_slot a ->
                      ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8)%Z ->
                      ~ (bv_unsigned sp0 - 208 - LEPT_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunL ()) ["TRunL"] "h04__x1h14__p1h21ah34__p2h44__x2h57__arithh64__ffh76__sat3h86__sat4h96__sat5h:8__varmaph;5__with<5heq_Lh=9heq_callsh>7heq_cfgh?:heq_paylenh@4__p3hA2HahB1HhC2HghD1ohE2HehF3HlthG1AhH2FRhI2H0hJ2H1hK2H2hL3HEahM3HElhN3HErhO2HIhP3HfrhQ3Hg1hR3Hg2hS3HnehT4HtophU1MhV2M'hW2a0hX2vmhY1xhZ1zp%0p&0p;3p;2p;1p;5p;6p;4p;7p;8g01Ejk30JTg01G3k30ITg01H<k206Tg003oj10Tg004Tj1wTg0052j1tTg005Uk105Tg025Mj3fTg026Ij3kTg0186j28Tg00Pnj21Tg0090j22Tg00BNj13Tg00;Qj34Tg012dj1DTg00NCj1vTg009LR0j2;Tg01VPj5eTg01WSj1@Tg00:Zj2WTg01XKj2`Tg01YNj2oTg01MAj1UTg01ZOk20HTg00F5j2xTg00:>k60GTg013_k10FTg00;7j2_Tg014Sk10ETg015Hk10CTg016:k10BTg016jk20ATg013Bk20@Tg017Rk30?Tg018`k20=Tg019Qk20<Tg00?Fk10;Tg0067k10:Tg00?fj2uTg00MBk109Tg00@bk108Tg00A@k107Tg00Akj2\Tg00PKj3gTg00CVk204Tg00D8k203Tg00Ddk302Tg00ECk401Tg00JRj1[Tg00LYj2STg00UDj2aTg00C3k300Tg000`j6lTg00S2j2]Tg01ONj4pTg00@Dj4}Tg00M`j2|Tg00SLj4YTg00T7j7RTg00W4j7^Tg01nIj6{Tg00WXj7cTg00VPk60DTg00X<j8mTg00T[j3zTg00V0j3yTf0R1#0#0p=K%31#0#3#3p=B%01#0#0#0p=X%31#3p=9%01#3p=<%01#0#0#Dp=7%31#0p=:%31#3#0#0p>0>%01#0#3#0p=Pf3R2f2R3'1f1R4/21';p=61;34/]1p=?%01#Dp=s11231241';#Up=E%31#0#0#0p=r%01#0#0#0#0#0#0#0p=Zg00Y>R5?441p=L1241,;3#Up=d1241,;3p=>1]41,]3p=J1134/;1p=ng00X`R6/11p=VP5P3P4P1C}p=C1|51p=5P3g00[BR7g00[aR8P8g00\AR9P5P4g00a0R:P1CYg00]HR;FRp==P5P4g00aWR<P1CYp=iP2P7P8P8P9P3P4P7P8P8P9P1P;FRF^p=hP4P7P8P8P9P1E{p=IP3P7P8P8P9P5P4P<P1CYP;FRp=Hf6R=P7P8P8P9f5R>P7P8P8P9P5f4R?P:P2CYP;FRP3P7P8P8P9P5P4P<P1CYP;FRF^p=FP3P7P8P8P9P4P1F^p=OP?P7P8P8P9P2P7P8P8P9P3P4F^P1Fcp=TP?P7P8P8P9P2P3P7P8P8P9P4P1FcFcp=MP4P7P8P8P9P1J0Dp=bP=P7P8P8P9P>P?P2P7P8P8P9P3P4P1GmGmp=AAz541p=Ng00_XR<?y41p=QP2P7P8P8P9P3P4P1Gmp=GP?P7P8P8P9P2P7P8P8P9P5P3P:P4CYP;FRP1F^p=qP3P7P8P8P9P4P1Fcp=j1;41,]3p=~p,2ALR7p,2CLR;p,3ASR:0J7;60I7R;+06g00b>R:#0R@#0RA#0RB#0RC#KRD#wRE#tRF%wB#tRG$05RH[PH^YFg01Rmp,3sp0RIp,4mem0RJ;f3P0AkIJ2%0:#B#X#9#<#K#7RK18E1RL'1%0:#:$0>#<#<#9#9#7RM,2L%3:#B#P#<#:#:#7RNPLPL%3:#B#P#B#<#7ROC63?RP%0:#B#X#9#:#<#:#sRQ18E4RRPR%0:#B#X#9#:#:#7RRCERSP=P3O1PJP3O1RT54H[[^2F%KD#XRD#KS00#KRU#DRV/1LRW%0:#K#r#Z#7S01,2L%0:#P#<#9#<#:#<#7RXPLPL%0:#P#<#9#<#:#:#7RYC63?RZP>P4O1%vGRG54H[^2F';P7P;P>P?P3De%@218EIR[%XU#7RU'WR\'L1`71R]%@>7dL1o74#UR^20H73S02#UR_g0212S0318E2R`P`Q03%DBRB'xS04CERa%3:Rb#0#:#7Rc,W[S05g0224'WS0618E?RdPdQ05CERdf;ReP>O1f<RfP>O154H[[[[[^2FAfIJ=[[[P1AkIJ>f9RgP3O1=4HT\S\P^2Ff8RhP4O1=4HG\Z^2F';P0f:RiP3O1=4HT\S\P^2FPgP4O1=4HG\Z^2FP7P;PgPhP=Def7Rj#@/L\%@g9d]Lf?S07P>O1f@RkP>O154H\d\a\_\^[^2FAfIJi[[[P1PfP3O1=4HT\S\P^2FPfP4O1=4HG\Z^2FP7P;PfPePgDe%@i/L\%@f9d]LfBS08P>O1fCS09P>O154H\d\a\_\^[^2Fp,4SPloR^%3bRb#3#9#9#9#9#9#9#X#Z#Z#Z#7Ra/1[11[LS0:%0:#P#:#Z#7Rd9>WL;JPS0;P?P31`7318E3RW%@k3>S0<P01`72fAS0=#@,2`g01E1RkP11`7>18E=fDS0>#@'2p,8AL_grantPjP4O2%DDRD18EjRLPVPLPL%3:#B#:#Z#7RLCE3nP018EhR0,1DPVP0P0PLCEPkP118EiR0,1DPV18EeRDPDPLCEP5fJ#@f=S0?,8E/21XZ5P>P\Q07J0G18EfRD/2\p,4dataR\$0FR],_5p,5calls/L]R]eR;P]&0E\Rl,_5p,6paylen/LlRleRmPl&0C\Rn,_5p,3cfg/LnRneRoPn&0B\R\,_5p,1L/L\R\eRpP\%D@Rq%3@S0@#3#sRr+0ARs126q%Vr20@qrRt,26[[Ru%VqRvg01ENRwB0?qr4UWARr%Vt\w^AvRv%DCRC-0=[Rw%V[%VC20<[C#V[[RCp-0Rt&0;<Rq&0:<R<1u54Rx&095Ry7C31u53Rz9Cy37C3S0A&085R{&075R|P|%5VS0B1\5bRb5=|R}P|%5L,ibCh,I|%v8R8P|1\5ARA%5U5g59H|bP8P|P|P|%5QS0CPbP|Pb%5RS0DFFS0E,I|S0FP8P|P|A=|AbS0GP|%5dR~9H|bS0H9O|}P|P|%5KS0I==|b%5MS0J9H|bS0KP|P|%5NS0LPbP|Pb%5OS0MFFS0NDTDMP81b|?R}FAFA204|9R9P1P3g00bcS0Og00cCS0P'_Q0O20313Q0P34dB02564H01R6b6b:b;X05X45W111V4S0P?>4LPk[1W4U,23122RS0O9nQ2Pk[112?PVP?P?PdC611K?12?MPNP?P?POC63?3JP=[[[[^05^45^1tP1PkfE,8EP[PgPhQ09Q0>O7b5b7b8b9b<b>b?b=bFWRWQP4P1O2n2001000000121000000bWWFWCP4P1O2n2001000000121000000WIQ0<#Ue1o73S0<p,7AL_globP2P1O2POP`P`%3:#B#<#K#r#9#7R7C6P;P]PmPlPoPnPpP\PsPuPrPvPwPCg00ccRU#[S0>#[RL#[S0Q#[S0R,S5S0S1S5LS0T1S5US0U'N'Ng00`DRU'a/QqS0VP<Q0AP{P|P|P|Q0MPbP|Pb%57FFP8P|Q0FP8P|P|Q0GP|Q0H9O|}P|P|1b|>RbQ0KQ0NDTDMP8P|%5aRL==|ARAP8P|PAP81b|=R=CGFAFAP9P6b6b:b;X05X45X1tX3tX@tPOP4P4P7C6PQP3P3PRC6Pk[1132A>?2d122MPNP2P2POC65?>3J11a2R711a?Pg[[[[[^05^45^1t^3t^@tP1Pk11KD11VDPDP[PhPiPeQ0?P^O:b5b7b8b9b<b>b?b=bCWCQ0<#UeQ02p,8AL_errnoP2P1O2PQP`P`PRC6P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<ACy4x9Cy4P{P|Q0EP8P|Q0FP81b|2R`FAP9P6b6b:b;X05X1tPQP1P1PRC6S0F11Q4S0E?>4RPk[RAP2[[^05^1tP1PkPDPhPiO4b5b7b8b9b<b>b?b=bEWEP_eP;P]PmPlPoPnPpP\PsPuPrPvPwPCQ0VP<ACz3y9Cy4S0VP{P|P|Q0@,\5R_1\5:Ri5=|S0@P|P|P}P|1ii~ChP|P|Q0I==|iPbP|P|Q0LPiP=DqDTDMP8P|A=|L_R_P8P|P_P8P|P|%0:#K#B#9#:#P#7R:#5R=PiP|Pi%5B:005=FF,I|CGFAP9P6b6b:b;X05X45X1tX3tX@t1141S02A>31d11K1S0<11N1S0?/;?7?23J11a3RaP:P2P21x:BC6Pk[\7[[^05^45^1t^3t^@tP1120O120M11V0R:P[P0PgPeP^O8b5b7b8b9b<b>b?b=Q03PWPWQ04CEeP;P]PmPlPoPnPpP\PsPuPrPvPwPCQ0SQ0TQ0>,S5RB'NR='N/aURDQ0R#[,S5/N=/aU/Qq,QD,QD'QP<ACz4yS0RP{P|P|P|Q0C1\5@R@P|P@Q0DFF,I|P8P|P|A=|i@RzP|AH|@~S0S9O|}P|P|PbQ0J9H|@S0JP|P|Q0LP@P|P@Q0MFFR~DTDMP8P|A=|LiRLP8P|PLP8P|P|%5c9g5iRLQ00#DRD#55g5P@P|P@PLFF,I|FAFAP9P6b6b:b;X05X45X1tX3t1143RLA>23d123MR=PNP3P3POC65??3J1W?cRc/WDP>P>PcC6Pk[\7\a[\A^05^45^1t^3tP111K0P:P0P[PhPgPeP^O8b5b7b8b9b<b>b?b=Q06PWPWQ05CEeO6XSSWAX2FQ0;Q0=P3O1Q08P3O1RW54H\S[^2FQ079kIJS07A4HWT\S\P^2FRIQ0=P4O1Rc=4HG\Z^2FRD';Q0:PHQ08P4O1S08A4H1TXDHPfP4P1O2PcP3P4P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<Q0RP{P|PzP8P|PzP|P}P|P|Q0IP@Q0JDqRz=j|bDMCGP9P6b6b:b;X05X45X1tX3t111411K3??=?9JL2[^05^45^1t^3tP1PN18EgREPEPOC6RL11VER=?>EdPEP[PhO5b5b7b8b9b<b>b?b=P;P]PmPlPoPnPpP\PsPuPrPvPwPCQ0Q,S5Q0U,NB'N/aU/QqP<Q0VP{P|Q0@P8P|P_P8P|P_P8Q0D9H|iR_9O|},I|CGFAP9P6b6b:b;X05X45X1tQ02Q0O,;>Pk[\7\a[^05^45^1tP111QEP[PEPhPeP^O6b5b7b8b9b<b>b?b=O3ElWAX2FQ07ePIPDPHQ09P3O1PJP2O194H1XDHPgP3P4P1O3PWP2P3P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<ACx4yRyP{P|Aj|z~R~P8P|P`P|P}P~DMCGP9P6b6b:b;X05X1tX3tQ0<121MQ0??>1O3?PKP4P4PMC6RM11N4124O3~9J32[^05^1t^3tP1A>:0d11[0P0PgO4b5b7b8b9b<b>b?b=P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<PxP{P|Q0C==|iRg=O|_,I|R_P8P_CGP9P6b6b:b;X05Q0FPk[PA[^05P1P0PhO2b5b7b8b9b<b>b?b=O3ElXKSXJPX2FPHQ08A4H1GXDHPjP4P1O2PcP3P4P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<PyP{P|P|P|Q0B==|@RyQ01#5Rc9H|@P|P|%5XP@P|P@%5YR@FFDTP8P|P`P|Q0S9O|yAj|z}DMCGP9P6b6b:b;X05X1tX3t11V1Q01,21RV121YRY9nX13?Q0P?>4d1]M25J3[^05^1t^3tP1PL11[EPEPhO4b5b7b8b9b<b>b?b=P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<PxP{P|P|P|P`AH|icP|P}P|1ii@ChDTP8AO|gb,I|CGP9P6b6b:b;X05X1tX3tX@t1;3Y9?4VQ0E/;?Pk[[^05^1t^3t^@tP112ER11XEP=PEPhO5b5b7b8b9b<b>b?b=O3ElXAZX2FCpCpbHbBWPWTWOWNWMP4P1O2n2101000010121000000WBWLP4P1O2n2011000010121000000WBWXWVWUWGo"). Qed.

  Lemma paylen_factsL : (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z ->
    (0 <= paylen < 2 ^ 26)%Z /\ Z.of_nat (length payload) = paylen /\ (0 <= cfg < 32768)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2TRunL ()) ["TRunL"] "p;1p;2p;5g00BNj12Tg003oj11Tg012dj10Tg00F5j23Tg00Pnj27Tg013Bj26Tg0090j25Tg027Aj54Tg00b>R0#2#1R1#0p,3cfg'3p,1LR2'7%10#0%21#1#0'6,52p,3sp0p,4Hvspp,4dataf1f0D4UUo"). Qed.

  (* [comment removed for export] *)
  Definition A_INCB : Z := 0x56174.   (* [comment removed for export] *)
  Lemma incb_block : forall A vm M buf cap owned aligned E (v : expr),
    (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z -> ev E 0 = sp0 ->
    sideT A vm M buf cap owned -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
    sideT A vm (mem_denot E M [SE (SA (ELit 0) 0x56174) 1 v]) buf cap owned
    /\ copyP (mem_denot E M [SE (SA (ELit 0) 0x56174) 1 v]) aligned owned
    /\ bytes_at (mem_denot E M [SE (SA (ELit 0) 0x56174) 1 v]) (bv_unsigned buf) data
    /\ (forall x : word, bv_unsigned x <> 0x56174%Z -> mem_denot E M [SE (SA (ELit 0) 0x56174) 1 v] x = M x).
Proof.
  intros A vm M buf cap owned aligned E v HL6 HL26 HE0 HT HC HB.
  pose proof SPlo as Hlo. pose proof SPhi as Hhi.
  assert (HLd : L = Z.of_nat (length data)) by reflexivity.
  destruct (paylen_factsL HL6 HL26) as (Hpl & Hlenp & _).
  destruct (sideT_block A vm M buf cap owned E [SE (SA (ELit 0) 0x56174) 1 v] HT ltac:(vm_compute; reflexivity) HE0)
    as [HT' _].
  destruct HT as (HW & Hown & _).
  pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap HW) as (Hb0 & Hb1 & _ & _).
  destruct HW as (HI & _ & _ & Htop & _ & _ & _ & Hcap).
  assert (Ea : adenot E (SA (ELit 0) 0x56174) = Z_to_bv 64 0x56174) by (apply bv_eq; reflexivity).
  assert (Hout : forall x : word, bv_unsigned x <> 0x56174%Z -> mem_denot E M [SE (SA (ELit 0) 0x56174) 1 v] x = M x).
  { intros x Hx. cbn [mem_denot]. rewrite Ea.
    apply MemSplit.wbytes_outside; rewrite ?length_N_to_le_bytes; unorm; lia. }
  split; [exact HT'|]. split; [|split; [|exact Hout]].
  - destruct HC as (HC1 & HC2). split; [|exact HC2].
    intros Hp. destruct (HC1 Hp) as (Eao & Hba & Hal1 & Hal2 & Hal3).
    split; [exact Eao|]. split; [|split; [exact Hal1 | split; [exact Hal2 | exact Hal3]]].
    subst aligned.
    destruct (ai_live_hull A M vm owned paylen HI (Hown Hp)) as (_ & _ & _ & Hbytes).
    pose proof (V2ReadLoop.round16_ge paylen) as Hr.
    intros i Hi. rewrite Hout; [exact (Hba i Hi)|].
    assert (Hi' : (0 <= i < paylen)%Z) by (rewrite <- Hlenp; exact Hi).
    destruct (Hbytes i ltac:(lia)) as (Ho & _). unfold at_ in Ho.
    assert (Eu : bv_unsigned (Z_to_bv 64 (bv_unsigned owned + i)) = (bv_unsigned owned + i)%Z) by (apply u_small; lia).
    destruct (ai_owned_where A M vm _ HI Ho) as [G|[[Gr _] _]];
      [pose proof (AL_glob _ G) as Hx | pose proof (AL_grant _ Gr) as Hx]; rewrite Eu in Hx |- *; lia.
  - intros i Hi. rewrite Hout; [exact (HB i Hi)|].
    rewrite u_small by lia. lia.
Qed.

  (* [comment removed for export] *)
  Theorem fz_call : forall (fxp : FPState) (K : TSet) A vm vals R M buf cap aligned owned (rem : Z) kn,
    frm_zero (@fp_csr fxp) ->
    length vals = 50%nat -> slotsL vals buf aligned owned rem ->
    regs_ok (ENV vals) tl_sr1 R -> know_ok RSEGS (ENV vals) M kn -> kn_vars_lt 50 kn = true ->
    existsb (is_kimg_cov A_EMPTY 16) kn = true -> existsb (is_kimg_cov A_LEPT_SEV 8) kn = true ->
    existsb (is_kimg_cov A_LEPT_PMM 16) kn = true -> existsb (is_kimg_cov A_GOT_LO (A_GOT_HI - A_GOT_LO)) kn = true ->
    existsb (is_kwr_cov (EVar 0) (-6144513) 6144513) kn = true ->
    sideT A vm M buf cap owned -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
    (L < cap)%Z -> (cap <= 67108864)%Z -> (6 + cfg <= L)%Z ->
    (* [comment removed for export] *)
    (1 <= rem)%Z -> roomT A vm rem ->
    (forall (fx' : FPState) A' vm' M' R',
        frm_zero (@fp_csr fx') ->
        regs_ok (ENV (vals ++ junk_vals R')) tl_sr2i R' -> know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_fcall kn) ->
        sideT A' vm' M' buf cap owned -> copyP M' aligned owned -> bytes_at M' (bv_unsigned buf) data ->
        (forall a : word, (0x76918 <= bv_unsigned a < 0x77000)%Z -> M' a = M a) ->
        roomT A' vm' (rem - 1) ->
        realizes RSEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x17c04) M' (seg_rom RSEGS)) (model2 vm')) K) ->
    realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x17d08) M (seg_rom RSEGS)) (model2 vm)) K.
  Proof.
    intros fxp K A vm vals R M buf cap aligned owned rem kn FRM HL SL HR HK VLK Xe Xs Xp Xg Xw HS HC HB HcapL Hcap26 HLc Hrem1 HRT HKONT.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    destruct (paylen_factsL HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    destruct HC as [HC1 HC0].
    unfold model2, V2ReadLoop.model2.
    assert (R10 : getr R 10 = aligned) by (regv HR (10 : reg); cbn [edenot ev ENV V2Open.ENV]; exact P14).
    assert (R11 : getr R 11 = Z_to_bv 64 paylen) by (regv HR (11 : reg); cbn [edenot ev ENV V2Open.ENV]; rewrite P9; reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x17c04) by (regv HR (1 : reg); reflexivity).
    assert (R3 : getr R 3 = Z_to_bv 64 0x10800) by (regv HR (3 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x56270) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V2Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    assert (KW : forall (d : Z) (m : nat), (-6144513 <= d)%Z -> (d + Z.of_nat m <= -6144513 + 6144513)%Z ->
                 store_ok RSEGS M (adenot (ENV vals) (SA (EVar 0) d)) m = true).
    { apply existsb_exists in Xw as (Kw & Hin & Hc). apply In_nth_error in Hin as [iw Hiw].
      destruct Kw as [| | | | | |[bw kw] nw|]; try discriminate Hc.
      cbn [is_kwr_cov] in Hc. apply andb_prop in Hc as [Hc Hn]. apply andb_prop in Hc as [Hb Hk].
      apply expr_eqb_eq in Hb. apply Z.leb_le in Hk. apply Z.leb_le in Hn. subst bw.
      intros d m Hd Hm. apply (kwr_store_ok RSEGS (ENV vals) M kn iw (EVar 0) kw nw d m HK Hiw); lia. }
    assert (EQcfg : @mkst fxp R (Z_to_bv 64 0x17d08) M (seg_rom RSEGS) = @mkst fxp R (Z_to_bv 64 PC_FUZZ) M al_rom) by (rewrite AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC V2Open.fds0 vm stdin0 fs0 None (Some tid) None).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (fuzz_margin_bound paylen Hpl) as HFM.
    destruct (fuzz_step FUZZ_CALLS FUZZ_BMAX rem) as (EK & EB).
    destruct (fuzz_nonneg FUZZ_CALLS FUZZ_BMAX (rem - 1) HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hrem1; lia)) as (HK0 & HB0).
    eapply (FZ fxp A M md R aligned paylen payload (Z_to_bv 64 0x17c04) sp0 [a0s; path] envv K FRM HI).
    - constructor; reflexivity.
    - change (m_kernel md) with a_kernel. change (m_vmmaps md) with vm.
      exact (vm_resv_incl _ _ vm Hres Hisp).
    - apply AL_env. exact HE.
    - exact R10.
    - exact R11.
    - symmetry. exact Hplen.
    - lia.
    - intros Hp. destruct (HC1 Hp) as (-> & _). apply Hlo'. exact Hp.
    - intros i Hi. destruct (Z_lt_ge_dec 0 paylen) as [Hp|Hp]; [| exfalso; lia].
      destruct (HC1 Hp) as (_ & HBp & _). apply HBp. unfold payload in Hplen. rewrite Hplen. exact Hi.
    - intros Hp0. destruct (HC0 Hp0) as [_ ->]. split; [reflexivity|].
      intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_EMPTY (A_EMPTY + 16) HK); [| exact Ha].
      replace (A_EMPTY + 16 - A_EMPTY)%Z with 16%Z by lia. exact Xe.
    - destruct (Z.eq_dec paylen 0) as [Hp0|Hp0].
      + destruct (HC0 Hp0) as [_ ->]. reflexivity.
      + destruct (HC1 ltac:(lia)) as (_ & _ & _ & _ & Hal16). exact Hal16.
    - exact R1.
    - apply ret_ok_even. reflexivity.
    - exact R3.
    - rewrite R4. symmetry. exact AL_tp.
    - rewrite R2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 208)%Z with (bv_unsigned sp0 + (-13) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, R2, u_small by lia. unfold LEPT_STACK. lia.
    - rewrite R2, u_small by lia. lia.
    - unfold sp_window_hi. lia.
    - change (m_vmmaps md) with vm. unfold init_sp_win, sp_window_lo, sp_window_hi. rewrite Hisp. lia.
    - intros a Ha. rewrite R2, u_small in Ha by lia. unfold LEPT_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V2Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_LEPT_SEV (A_LEPT_SEV + 8) HK); [| exact Ha].
      replace (A_LEPT_SEV + 8 - A_LEPT_SEV)%Z with 8%Z by lia. exact Xs.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_LEPT_PMM (A_LEPT_PMM + 16) HK); [| exact Ha].
      replace (A_LEPT_PMM + 16 - A_LEPT_PMM)%Z with 16%Z by lia. exact Xp.
    - rewrite AL_segs. apply store_ok_data; unfold A_LEPT_HANDLER; rewrite u_small by lia; cbn; lia.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_GOT_LO A_GOT_HI HK); [exact Xg | exact Ha].
    - change (m_vmmaps md) with vm. exact HRT.
    - clear -EK HK0. lia.
    - clear -EB HB0 HFM. lia.
    -
      intros fx' A' m' vm' regs' FRM' HI' Hlive' Ha0 Hcs Hfr Hlm Hgr Hvl' Htop' Hisp' Hres' Hmb' Hroom'.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Hfr, Hgr, Hvl', Htop', Hisp', Hres', Hmb'.
      pose proof Htop' as Htop''. rewrite Htop in Htop''.
      unfold md. rewrite with_vmmaps_C.
      assert (Hfr2 : forall a : word, ~ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) -> ~ al_globals a -> ~ al_errno_slot a ->
                      ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8)%Z ->
                      ~ (bv_unsigned sp0 - 208 - LEPT_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> m' a = M a).
      { intros a H1 H2 H3 H4 H5. apply Hfr; try assumption. rewrite R2, u_small by lia. exact H5. }
      assert (IMGFR : forall a : word, (0x44000 <= bv_unsigned a < 0x77000)%Z -> ~ (0x76568 <= bv_unsigned a < 0x76918)%Z ->
                       ~ (0x561cc <= bv_unsigned a < 0x561d0)%Z -> ~ (0x45f10 <= bv_unsigned a < 0x45f18)%Z -> m' a = M a).
      { intros a H1 H2 H3 H4. apply Hfr2.
        - intros [Hg Hlt]. destruct (AL_grant a Hg) as [Hg1 Hg2]. lia.
        - intros Hg. apply AL_glob in Hg. lia.
        - intros He. apply AL_errno in He. lia.
        - unfold A_LEPT_HANDLER. lia.
        - unfold LEPT_STACK. lia. }
      apply (HKONT fx' A' vm' m' regs' FRM').
      +
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (regs_after_allocG a0s path vals sr Rc regs' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs) as HR2 end.
        rewrite HL in HR2.
        pose proof (regs_ok_same10 _ _ regs' (ELit 0) HR2 ltac:(cbn [edenot]; exact Ha0)) as HR3.
        lazymatch type of HR3 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR3 end.
        exact HR3.
      +
        apply (know_after_fcall A vals M m' vm regs' kn ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK) HK HI Htop Hfr2 Hgr).
      +
        split; [| split; [intros Hp; rewrite Hlive'; exact (Hlo' Hp) | intros q Hq Hq'; rewrite Hlive'; exact (Hln q Hq Hq')]].
        split; [exact HI'|]. split; [rewrite Hlive'; exact Hl|]. split; [rewrite Hvl'; exact Hvl|]. split; [exact Htop''|].
        split; [rewrite Hisp'; exact Hisp|]. split; [exact (vm_resv_step _ _ _ _ Hres Hres' Hmb')|]. split; [| exact Hc0].
        exact (env_ok_fcall A M m' vm HE HI Htop Hfr2).
      +
        split; [| exact HC0]. intros Hp. destruct (HC1 Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
        split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
        intros i Hi. rewrite <- (HBp i Hi). pose proof (Hlm aligned paylen i ltac:(rewrite Hao; apply Hlo'; exact Hp) ltac:(rewrite <- Hplen; exact Hi)) as Hq.
        unfold at_ in Hq. exact Hq.
      +
        intros i Hi. unfold V2TRun.L in *. rewrite <- (HB i Hi). pose proof (Hlm buf cap i Hl ltac:(lia)) as Hq. unfold at_ in Hq. exact Hq.
      + intros a Ha. apply IMGFR; lia.
      +
        unfold roomT. apply (aroom_mono A' vm' _ _ _ _ Hroom'); clear -EK EB HK0 HB0 HFM; lia.
  Qed.
End TRunL.
