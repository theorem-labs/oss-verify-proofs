(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's stack window: 6144513 writable bytes below the entry stack pointer instead of 8 MiB; fz_call's recorded proof, made over the old 8 MiB launch stack window, replaced by leptonica/kernel_fuzzer's plain proof, addresses mapped, with one step added for its A_MORPH_BC premise; incb_block's recorded proof, made over the old sideW with vm_reserved, replaced by a plain proof; sideT_block's recorded proof re-encoded to pass the Amb instance to sideW, which now depends on it through its vm_resv conjunct). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibKnowXfer LibTail SymCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib LibWritevG.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib Frame.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Room.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23ExitBase V23StdioDefs V23Exit V23Startup V23StartupDefs V23StartupFacts V23MainEntry V23LibStdioCall V23OpenFail_defs V23OpenFail_tail V23OpenFail_tail2 V23Open_defs V23Open V23Oom_defs V23Oom V23MemPreds V23Malloc65536 V23DirRead_defs V23MemcpyBase V23Memcpy V23ReadLoop_defs V23ReadLoop V23Grow V23Hdr_defs V23Hdr V23FuzzIface V23TRun_defs V23TRun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac FPSteps.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23TRunL () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3V23;V23MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;is_kimg_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC59OSSVerify5KrLib3V23;V23MemPreds9img_clearC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3V237V23TRun5callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun6paylenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun1LC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgKTgt_pix_orient_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~____________________I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun5sideWC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23ReadLoop6in_winC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3V23;V23ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun;sideW_blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23ReadLoop7DATA_RSC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3V23;V23ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs8kn_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface>A_LEPT_HANDLERC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface:LEPT_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs5LGLOBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib3V23>V23Malloc655366env_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23Open9above_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun<paylen_factsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib9micromega;ZifyClasses3injC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun:bufW_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedc59OSSVerify5KrLib3V238V23TRunL=paylen_factsLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunL;sideT_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun7payloadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23>V23Malloc65536:live_whereC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib3V23<V23FuzzIface7A_EMPTYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunL6slotsLC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:is_kwr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun5roomTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr6slotsRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V236V23Hdr6hdr_b2C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<In_nth_errorC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28expr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIfaceAfuzz_margin_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface;fuzz_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room9fuzz_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room;fuzz_nonnegC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunL;kimg_clearLC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC59OSSVerify5KrLib6Common8VmLedger;init_sp_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23TRun=ownedA_rangeTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23Open3ENVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23>V23Malloc65536>regs_ok_same10C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunL@know_after_fcallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V238V23TRunL<env_ok_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:aroom_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs7tl_sr2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23TRun_defs6tl_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8PropExec7FPState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface:A_LEPT_SEVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface:A_LEPT_PMMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface:A_MORPH_BCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface8A_GOT_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23FuzzIface8A_GOT_HIC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3V23<V23FuzzIface7PC_FUZZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23Open4fds0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3V23<V23FuzzIfaceAfuzz_calls_nonnegC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC59OSSVerify5KrLib3V23?V23MallocLayout4LU16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23MallocLayout6LU17okC1?~~~~~~~~~~~~~~~".
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
      as Ktid; cbn [kentry_ok edenot ev V23Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x123d08), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V23Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev V23Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V23Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V23Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V23Open.ENV] in Ktid |- *; lia
      | cbn [ev V23Open.ENV] in Ktid |- *; lia
      | lit_u; change (1195272 - 168)%Z with 0x123c60%Z;
        let Htc := fresh "Htc" in
        krd HK 0x123c60%Z 4%nat Htc; rewrite Htc; cbn [ev V23Open.ENV] in Ktid |- *;
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
ltac2:(KReplay.run1 (kr_t_V23TRunL ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p10000p4p70g000`R0p4p710R1p8p1001>p4p70P1p8p1001lp4p7210P1p8p1002Xp4p70P1p8g003NR2p4p710P1p8g003oj1HTg004Tj1wTg0052j1gTg005Uj1~Tg0067j1uTg006Wj3qTg007Tj3KTg0082j25Tg008RR1j10Tg0092R3j23Tg009Nj26Tg009ij2YTP2k30ITg00:@j6sTg00:\j28Tg00;9j2>Tg00;Sj37j1nTg00;mj3_Tg00<Sk10>Tg00=1j6^Tg00=Zj4\Tg00>Aj1TTg00>fj2PTg00?Hj1|Tg00?hj2XTg00@Fj4LTg00@dj1yTg00ABj1xTg00Amj2JTg00BPj1cTg00C5j3QTg00CXk20HTg00D:k20GTg00Dfk30FTg00EEj4rTg00F7R2j21Tg00FTj2aTg00G:R4j1VTg00GZj4Nj3pj2ok10ATg00H6j2Wk10DTg00HXk20ETg00Hok20@Tg00IRk30?Tg00Iol<lTg00JTj1CTg00K3k10<Tg00KQk20;Tg00L2j3iTg00L[j2hTg00MDk108Tg00Mbk205Tg00NEk104Tg00Ngk403Tg00ORj8RTg00Ook502TP0j6eTg00PMk307Tg00Q0j2tTg00QLk200Tg00QilBkTg00ROl<dTg00S4j2}Tg00SNj4UTg00T9j7[Tg00T]j3`Tg00UFj2MTg00V2j3ITg00VRk60BTg00W6k70CTg00WZj7{Tg00X>j8zTg00XbR0f0R5'tp=920005p=2g00Y@R6/>5p=;g00Y^R7P7P7P6P6P6g00Z=P1P1P1f6R8g00Z]f5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P1P1P9P:P;P<P=P5M<dp=bP6P6P3f7R>P3P8P9P:P;P<P=P5M<lp=Z1305p==1t50p=<A7650p=BA76;<,6:16=5'}p=?P<g00[DR3g00[cR?P?g00\CR@P6P=g00\cRAP5CUg00]JRBF[p=vA76=5p=OP6P7P6P6P4P:P1P;g00]jP<P=P5M<dp=mP7P7P7P6P6P6g00^WP1P1P1P2g00_7P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00_ZR2g00`FR4,M=;I5p>0:A`6<=/M4=I25p=E1M<41M=4=I255I2p>09P=P3P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P3P?P?P@P<P=P3P?P?P@P5PBF[K0Cp=:P6P=g00a2P5CUp=FP=P3P?P?P@P5PBF[p=DP<P3P?P?P@P=P5F{p=]P6P=g00aYP5CUp=SP;P3P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI2=59I2<p>06g00b@R4#HR3#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P0%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|2RV%u2R2P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J63R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00beR_g00cER`'>Ra20G5<=7_`dB0F60=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA0RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P1%n6%0=R1/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P08%=8%28RiP8%<8%BiD?%2>P611cNRc,P0%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P0%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00ceRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP2P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20560R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c3,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P0K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP2P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;1AKD=<5q:eWGXM7WKXI6WHo"). Qed.

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
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x10e958.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x10e818.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x1381d0.
  Hypothesis AL_glob : forall a, al_globals a -> (0x1584d0 <= bv_unsigned a < 0x158880)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x13812c <= bv_unsigned a < 0x138130)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x159000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.



  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V23Open.ENV a0s path.
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
ltac2:(KReplay.run1 (kr_t_V23TRunL ()) ["TRunL"] "p'0h01Hh12Hch23Hinh31xi001xh41ih51ni011nh61ai021ah71ei031eh81mi041mh91Ah:2H1h;2H2h<2Hah=3Hexh>4__x1h?4__x2h@4__x3hA4__x4hB4__x5hC4__x6hD1fhE3hi0hF1lhG3lo0hH1EhI2HKhJ3HKKhK2HihL2HnhM1KhN1MhO2_HhP3_H0hQ7__arithhR4__ffhS6__sat3hT6__sat4hU6__sat5hV8__varmaphW5__withX2a1i052a1hY2a2i062a2hZ2e0h[5heq_Lh\9heq_callsh]7heq_cfgh^:heq_paylenh_2hii072hih`1ki081kha2knhb2loi092lohc2n1i0:2n1hd2n2i0;2n2he1vi0<1vhf1wi0=1wi0>1bp&0p;1p;4p;2p;3p;6p;7p;8g003oj14Tg004Tj1aTg0052j1_Tg005Uk108Tg0067j1XTg00dDj4xTg00:\j21Tg00eTj2ej3=Tg00f_R0j3ZTg00g;j3KTg009NR1j2>Tg00gRR2j2NTg00glk306Tg00hOj36Tg00iMj3QTg00jXj2TTg00k7j2[Tg00lBj3RTg00mMj2VTg00nXj2<Tg00F7j2HTg00o5j3mTg00Q0j25Tg00oXj2jTg0108j3`j4PTg011Jj3^Tg011kj3iTg012Mj6hTg012hj1DTg013Fj2]Tg0092j29Tg00FTk207Tg00NEj1fTg00;Sj37Tg013ck105Tg00;9j2JTg014Yk104Tg015Pk102Tg016Dk101Tg00BPj1:Tg0176j2~Tg017^j3}Tg018Bj2|Tg018lj2{Tg019]j2zTg00JTj1GTg00L[j2ITg00T]j3MTg00UFj2dTg00?Hj1wTg00V2j3cTg00MDj1vTg00?hj2UTg00@Fj4ETg00@dj1uTg00ABj1tTg00Amj2BTg00SNj4STg00PMj3sTg00C5j3rTg00Mbj2qTg00CXj2pTg00D:j2oTg00Dfj3yTg00EEj4nTg01:=j2WTg01;Hj3\Tg01<Sj2OTg01=^j4YTg00:@k600Tg00T9j7lTg00W6j7kTg00X>k803Tf0R3#4#4p=gg00beR4g00cER5773p=2g01>iR6f1R7;K3p=0f2R8?=73=745p=3P4P8P7g01@4P5P3J00p=Ag00XbR9/53p=;1587/>3p=8g00Y@R:P7g00a2P3CSp=FP7g00[DR;g00[cR<P<g00\CR=P3g00]JFlp=@P8P;P<P<P=P7P3Fkp=b%:3#:p=C%43#4#4#4p=?f3R>P;P<P<P=P8P7P3L03p=Lg01@Pg00b@R;#4R?#4R@#4RA#4RB#gRC#aRD#_%aA#_RA$08RE[%X6g01AXRFf4RGP>P8Cx1178,e8=Z6>#2P0p4p710R0P4\3RH%X7RIP1AZ873#2AKG38P>P3O1#2'>X3>,N>[RJAK>37P8P3O1#2'>X38,N8AZ>87#2RK[f5RL?K3>PGP3O1#2'>X3G,NG\KB06873P7n2001000000120000000WFWDW9PJ^FI^DH^90P3P611>G,eGPLP7O4f6R0,0311GL=3L3'>X36,N6P2P6f7R2,0311L0=303'>X36f8RH?60LP3f9RI,03112H=3H3'>P1f:R2,0711HI=3I7f<RJ?62IP310>Jf;RK/1J=3JGP6f?RM,03f>RN/1M=3M7fBROf@RP;6M]1]2PLg01C?RQg00Y^RRg01DIRSAQ873fDRT'0fCRU/1TRVAQ>8753TfERW11TWRXAQG>83=P4p-0P3g01ERRYg01EoRZn0110>00020000R[X74R\;A3PYfHR]fFR^;6W/T3R_b0W1W2WeWfW6P8P7P3O31[73/0OfAR`/1ORa1[8753O11OURb1[>85=U?A\3PYA6^TU/T3Rcb0W1W2X5SX6QP7P3O2AR873/0TAR>8793TVARG>89=WX?A\3PYP_b0W1W2X`RX5SX6QP8P7P3O31V73/0O1V8793Oa1<>URR1HUb/<8Rd;m3%2R%2d'>P11<GT#21HTV/<>#2fGRd?6WTP31<0^#211^dRR,Hd/<0#2P11<73#21587[Re15731<87#2Rf[15>8\f1j73P7n2001000000120000000X8:X5:RfPe^8:^5:ReP3PIfIRgP8O315IgPfPeP3fKRefJRf/1e'HReP2P>O315e2fORefNRg5`FRhfMRi5^6103ePFfRRjfQRkP7CP[^36[103gPFPkfPRlP7CP[^36A`Fle=^6g[Ai6hiPf1VJKRKP2EhPFPePgPKCPP1f=RK#;%D?RF%DC']RC193K98N3Pk207D7RNO1%fARA57E[^4:58JA6lgiP3%;M193P98`3fTRlPNO1=7EA[^4:98MCP115PC193`98O3fUR`PNO1=7EA[^4:A6ljkP315OC193T98W3fXPNO1=7EA[^4:fV193`783P8P7p,4dataRA$05RE,J:p,5calls=7:EREePE&04ARE,J:p,6paylen=7:EREePE&02ARE,J:p,3cfg=7:EREePE&01ARA,J:p,1L=7:ARAePA%:?RA#:#4#DRE,~F199F%;E1]FERN,99[[%;FRCA}FE7VZW<%;N\Z^<Cp,3sp0,|DRD%DBRB'{%;D%;B1zDB#;[[g00_ZRBg00ceRC#G#GRZ#GRN#GRE#G,I:1I:Z1I:CRC5M:5M:g00`FRZ'd1I:E1I:N=M:C5M:/dZ%wB5cB3c%XBP:P:%v:RBP8P:1U:0P0PBCECEP7P:P:1U:LP0PBCEP>1U:GCECE%u:%t:RB%:@,B:R@1B:?R?'F,@BP:P?g00aYRZ%4A,B:RACS,@B5bB%f<R<PBAs:A@9r:@%:;RA,B:RC'F,@BP<PB1B:;R;/F@,@BP<PB%:ARA#:#C#C#C#C#C#C#4#g#?#?#?#?#?#?#?#DR@,q:1B:A'F,@BP<1F;?,@BP:P?PZPCCS,@B5bBCLCLCLCL1pB=P3P81J451o38#2dAy:97CnbRbVbWX>:X?:X@:XA:XB:XC:197L98G7110L,HL/5>158015@019L098GL[[[[^>:^?:^@:^A:^B:^C:P3f^f_PDPgPIPePHPUPWp,4SPloO:bQbSbTbUb[b]b^b\O2WKX4:fW?6`leWLWPP7P3O2n2001000000121000000W0WOP7P3O2n2001000000121000000bJb;b0b:b0W;W:P7P3O2n2001000000121000000b1W1W2XE:XG:P7P3O21W73/0O1W8793Oa1W>89=UbP[XZ4R4;A3PYPcb0W1W2X8:X7SP7P3O2A\873/0TA\>8793TVA\G>89=WX?A43PYP_b0W1W2XE:XG:X7SP8P7P3O31O73/0O1O8793Oa1O>89=Ub?A\3PYPcb0W1W2X5:X6QP7P3O2P>P8P7P3CY/0^11W^PGP>P8P7CY53^PLPGP>P8CY9=dR?A\3PYA6f]d/T3b0W1W2Xd:XYQXc:XXQP>P8P7P3O4n0110800083010210=10<2010210130102101108211091072010310430103109107201021014010510:10610;P7P3O2W1W2P7P3O2n2001000000121000000W0XM6P7P3O2n2001000000121100000b=b0W=WIX_:Xb:WaWNWHo"). Qed.

  Lemma sideT_block : forall A vm M buf cap owned E log,
    sideT A vm M buf cap owned -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    sideT A vm (mem_denot E M log) buf cap owned
    /\ forall x : word, ~ V23ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRunL ()) ["TRunL"] "h01xh11qh21Hh31Ah41Eh53HE0h62HWh73HW'h83Hlnh93Hloh:4Hlogh;1Mh<3OUTh=1ah>3bufh?3caph@3loghA5ownedhB2vmp;3p;2p;1p;;p;4p;Hg01FKj3LTg01GTj3KTg01H]j2FTg003oj16Tg004Tj1?Tg0052j1>Tg005Uj1=Tg0067j1ETg01I^l;7Tg014Yj1BTg0092j2ATg00H6j2@Tg00NEj1JTg009NR0j24Tg01JTj28Tg00;Sj30Tg01KYj33j45Tg01Lkj2GTg01Mfj1:Tg01N?j1DTg01O;lHCTg01P7j4<Tg01PRj4HTg01QUj3ITf5R1f4R2f3R3f2R4f1R5CHf0R630p=2A0456#:p=1g00ceR7g01R\;I6p=;g00beg00cE706p=9p,2ALR8p,2CLR9p,3ASRR:9L895K8R;'Fg01SXg00b@#6#6#6R<#6#6#6#?#>R=%?<#>#=R<[g00Y@R>g01@Pg01TO#Ep,5sideTR?f7R@f6RAP1P2P3P4O6P0P8P9P:p,3sp0R3p,4mem0RBp,3limRCf8RDP@PAP1P2M;7Tp/C59OSSVerify5KrLib3V237V23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limf8f7f6f5f4O<g00Xbp,4data#BRE'ARF%=>RGP8P;f9RHP21@>EREE2[A1=6AA1=4A\FPGP8P;f;RIP4%J>R>E2[[^1='4%;4#91827=0=3P?PIf:RJA31H2PDP@PAO61G36#:R2%D5#:R1PDf<RKP@P4C5PKP4O150<[[^0='4[[P6P8P9P:P3PBPCPJPHPDP@PAM;7Tp/C59OSSVerify5KrLib3V237V23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limf:f9f8f7f6O<PGP8P;PKP@PEE2\FA1=6HA1=4H\FPGP8P;f>RLP4P>E2[[^1='4P0PGP8P;f=RMPDPEE2\FA1=6JA1=4J\FPGP8P;f?RNP4P>E2[[^1=%;A#918D7=0=3P?PNPLA3HMDPKPIPJO6PKf@RAPIP4C5PAP4O150<\1\2^0='4[[P6PGP8P;PNPJPEE2\FA1=6MA1=4M\FPGP8P;fBRJP4P>E2[[^1=%;H#918I7=0=3p,3AMBP8P9P:P3p,3tidPBp,3fs0p,6stdin0PCp,4Hvspp,4Htidp,7AL_globp,8AL_grantPJfAR7PAPNPLPKPIP@P5P6MHCP8P9P:P3PBPCPJP7A3KAIPNPLM;7Tp/C59OSSVerify5KrLib3V237V23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limfBfAp/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotf<f@f;O3f?f>O<PNfCRIPLP4C5PIP4O150<\1\2^0='4P0P8P9P:P3PBPCPIPJA3M7KPAPNM;7Tp/C59OSSVerify5KrLib3V237V23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limfCfBp/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotf=fAf<O3f@f?O<PAfDRKPNP4C5PKP4O150<\1\2^0=P?PKPIA3LJMP7PAPNO6P7fERMPAP4C5PMP4O150<\1\2^0='4P6P8P9P:P3PBPCPMPKA3NILPJP7M;7Tp/C59OSSVerify5KrLib3V237V23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limfEfDp/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotf?fCf>O3fBfAO<PIfGRNPJP4C5PNP4O150<\1\2^0=P?PNfFR?A37MAR7PKPIPJO6PKfHRJPIP4C5PJP4O150<\1\2^0=P8P9P:P3PBPCPNP?P7PKPIM;7Tp/C59OSSVerify5KrLib3V237V23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limfGfFp/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotfAfEf@O3fDfCO<PGP8P;PJPIPEE2\FREA1=6MA1=4M\FPGP8P;fJP4P>E2[[^1=R>'4P5PEP>PDP@C<C<P6C<W<W7P5P6O2n2001000000121000000b=W5W:W8W9P5P6O2n2001000000121000000W2W6P5P6O2n2001000000121000000W2W@W4XA=W?X>=W;WBW3o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_V23TRunL ()) ["TRunL"] "p'0h04__x1h14HLv0h27__arithh36__sat3h46__sat4h56__sat5h64cstrh75heq_Lh89heq_callsh97heq_cfgh::heq_paylenh;4__ffh<4__p1h=8__varmaph>5__with?4__x2h@4__p2hA1rhB2HahC1bhD2HghE4Hlt'hF1ahG1HhH3HnthI2HxhJ2H0hK2HehL2HlhM6__sat6hN6__sat7hO4__x3hP1xhQ1AhR2H1hS2H2hT2HIhU2HKhV3HLvhW2HMhX3HfrhY3Hg1hZ3Hg2h[3Hgrh\2Hhh]3Hhih^3Hihh_3Hloh`3Hltha2Hshb4Htophc1Mhd2M'he2P0hf2R'hg6__sat8hh6__sat9hi2knhj1mhk1nhl1ohm1si001shn4valsho2vmhp1zi011gi021lp%0p%1p&0p;3p;2p;1p;4p;5p;6p;8p;Ap;<p;7g01FKk30tTg01GTk30sTg01H]k20UTg003oj13Tg004Tj1lTg0052k10ATg0067j1}Tg005Uk10RTg00BPj1NTg001lk20LTg00JTj1qTg0082j2;Tg01UZR0k20FTg00;Sj35Tg01V4k20^Tg00dDk40CTg01W;k50ZTg01X>j1bTg018Bj24Tg012hj1@Tg00:\j2CTg01Y6j2HTg01Mfj19Tg01Z9k20<Tg01[:k20:Tg00F7j2BTg00NEk108Tg01\>k10ITg0092R1j22Tg00Q0R2j21Tg01]@j1vTg01^Hj3uTg00K3k10fTg013Fk203Tg013ck10`Tg014Yk10]Tg015Pk10\Tg016Dk10[Tg008RR3j1>Tg00>Aj1WTg0176k201Tg017^k300Tg018lk20YTg019]k20XTg00?Hk10@Tg00?hj2~Tg00@dk10WTg00ABk10VTg00Amj2jTg01^ek30?Tg00CXk20TTg00;9j2aTg00D:k20STg00Dfk30QTg00EEk40PTg000`k60>Tg01_HR4j2|Tg00Mbk20=Tg00Ngj4zTg01_`j4yTg01JTk20;Tg00MDk10OTg01`mk20NTg01aPk109Tg009NS00j26Tg01amk60KTg01c2k20JTg00g;j3=Tg00gRj2[Tg00:@j6dTg01cRk20HTg01d9j2pTg01dUS01k20GTg00V2j3hTg00S4S02j2gTg01e5j3MTg01eOj3LTg01P7j4RTg01eij4nTg00SNj4fTg00C5k306Tg00L[j2tTg00T]k305Tg00UFk20qTg00jXk20ETg01fCk50pTg01gEk30oTg01hAk10iTg01iHk80hTg01jTmA0gTg01k^k10eTg01l\k20dTg00Iom<0DTg00=Zk40cTg00T9j7mTg00W6k702Tg00X>k804Tg00PMk30bTg01m`k30aTg01n=k30jTg01nZk40kTg00@Fk40lTg00VRk60_Tg00WZk70mTg01o:k60nTf0R5#3#3p=<g00ceR6-0d5p=Z%35#3#3#3p=Jf2R7f1R8/25'6p=`f3R9/171285'6p=0%35#Np=AA5785#9p=I1g85,g7p=^%N5#Np=7%35#3#3#3#3#3#3#3p=_%35#3#3#@p=P%N5#3p=?1178/65p=Eg00Y@R:/a5p=Dg00Y^S03P:P0P3P2g01o^f5R2f4R0P9P7P8P5N<0Dp=Y20F09P7P8P5H0cp=Xg00XbR;/15p=812;5p=V%35#@p>0B20=:5p=:P7g00[DR<g00[cR=P=g00\CR>P:P8g00a2R?P5Cfg00]JR@Fmp=GP0P<P=P=P>P9P<P=P=P>P:P7P?P8CfP@FmP5K02p=Tf6RAP<P=P=P>P2P0P9P<P=P=P>P7P8P5L04L04p=KQ03P:P4P3P1g020@P6P;P9P7P8P5N<0Dp={P7P<P=P=P>P:P8g00aYR1P5CfP@Fmp=FP9P<P=P=P>P7P8P5L04p=OB0b:85p=\g020bR3,C5p=eP:P8P?P5Cfp>0MP9P<P=P=P>P7P8P<P=P=P>P5P@FmK02p=xB0a::5p=iB0j::5p=k11971285'6,60p=Q1678/g5p=]%b5,28p=cP:P:P8P5H0kp=rP:P7P8P5H0lp=UP8P<P=P=P>P5J0_p=oP7P<P=P=P>P8P5K02p=SP7P<P=P=P>P8P5K0mp=sP8P<P=P=P>P5J0np=wP:P8P1P5Cfp>07P8P<P=P=P>P5P@Fmp>0rp,2ALR@p,2CLR<p,3ASR:0t@<60s@R<+0Ug00b@R1#3S04#3S05#3R?#3R4#<RB#lRC$0ARD#}%l?$0ARE$0RRF\DS06Q06g01SXQ04#NS07#l00LDg01>i#}%q6RG1;D2+0F%ZAp,3sp0S0855Dg00beRHf7RI,;D00^7g00cERJ35g01AXS09p,3ENVRKf8RLO1PIP9H0CP@P<f:R<PLPAI0Z%bIQ08,4CRM%<B#JRB#<RN#<RO#3#<#JRP#@RQ'CRR55:1H@514C5RSf9S0:#b3`#920<@8#920:@7#9g021cRT14C9RUPU%@?S0;,BTC0S0<#9S0=%N1RT#A#JR?#@S0>,CMS0?g022g'CS0@14C0RVPVQ0?C0#9f?S0AP2O1f@RWP2O155F[[[[[^FDf<RXP5O1&08ERE5IF14C8RY&0I@RZ'21H@8f;R[#b7`YPXP8O1=IFE3^[^FDp,4SPloS0B%NTS0C#N#7#7#7#7#7#7#J#_#_#_#PS0D/1Mp,4SPhiS0E%3P#J#_#_#PRP,1Mp,5AL_hi%31#?#7#<#?#_#PRT,1ZQ09PK%vXS0F9uDWR\O1S0GQ0Af>R]g023gR^&0f?R?%@NS0H'CRNP?g024bR_%31#A#<#7#?#_#PS0IPD%ZWS0JQ04#@R`Q07#3#<Ra#@Rb+03RcQ07#NRd#7Re#@Rf-03`Rg,1S7ESXCDRhPDQ08Php,4dataRh$0`Ri#Dp,5calls=5:iRieRjPi&0]hRk#Dp,6paylen=5:kRkeRlPk&0\hRm#Dp,3cfg=5:mRmeRnPm&0[hRh#Dp,1L=5:hRheRoPhPGfDS0K,;DRp%@1Rq%>pRr'1RsPGPq%DqS0LPpPr%DrS0MEYP]DXRtPsfES0N,;DRu#WRv%>u#8Ru201`f%V`Rw%8f%Vg[[%8`Rxg01EoRyB00`f8UWB%8g\y^Bx201`bS0O%8b%Vc[\wS0PB00`b8VyXBxS0Q%8c\y^BxS0R&0BdRd-01`Rb%8d203`dRf#V[\wRwB00`d8VyXBxRd%8f\y^BxRx%@4R4-0YMRy%8M%8420XM4#8[[R4g00_ZS0S$0@RfQ0S#}Rz1~:8R{&0W:R|&0V:R}1j:1R~%:P5G}&08=R=P}Q0D#:S0T=G}~P=P}P}%:`R`%la60?:RaP~%le:0?:`9G}~DTFK20T}>R>P5P71aHJ20S57=5HJdB0Q:;8H0PRJb;b=b>X0:115PQ0D/18117g9Ec7[[^0:P5PMQ0EQ0BO3b2b3b4b5bMbNbgbhb6b1b7b9b:b8Q0JQ0:J0>%Z\PWQ0FP6PjPiPlPkPnPmPoPh1|6p%Vr1a:;S0JPpPrQ0MC{PtPsPvPuPbPwPdPxPyP4PfPzP{P|P}%:q=G}~P=20=:;Rr=F}~COP>PJb;b=b>X0:S0M11q5%V8[^0:S0EP5fJS0U,;DS0V#>S0WP2O2b2b3b4b5b6b1Czb7b9b:b8CyJ0>Q0G00;6,4CRp11pg5EcePjPiPlPkPnPmPoPhPtPsPvPuQ0OQ0PQ0QQ0RPbPwPdPxPyP4PfPz&0O:RpP|P}P}Pr%:TS0RQ0R%:QS0Q,\a5F}DTP>PJb;b=b>%8T1CcQ7`TP5b2b3b4b5bMbNb6b1b7b9b:b8P;P_P_%ecC0ePjPiPlPkPnPmPoPhPtPsPvPuPbPwPdPxPyP4PfPzPpP|P}P}P}Q0Q-0N:%:?S0PQ0H#:S0O'\S0XQ0XQ0P5G}DTP}Q0P00MrCxP>PJb;b=b>&09Q11N?Rr7EN11?;R;'6P5b2b3b4b5b6b1b7b9b:b8&093?ENr/6;ePKfAS0Yf=S0Z#v5uDO1S0[P^PNP?P_PSJ0K#9PDfBRK%v]R;5uD#Z14C7Rr/2_20J::R3A=35^R^%i5S0\PUPU%k5S0]DQXA3'['6Ru11_rRv%eSS0^7`r1BSNRsPrPr1BS?RtC03^#9XCDP5%ZKRcPKP;P6PjPiPlPkPnPmPoPhfFS0_,;DR;,|6%>;Ra#VQ0JP;Pa%DaRgC{PGP;11qaR\PGPqQ0LP;PaPgEYPWDXP\fGS0`,;DS0a#WQ0a#>R\#8PbPwPdPxPyP4Q0MQ0EP5fLS0b,;DS0c#>S0dP2O2b2b3b4b5b6b1Czb7b9b:b8CyEd12Y_P^Q0\PrPrQ0]DQXA3,[311_Y14CcRc#e,2Y1BcNPYPY1Bc?C03]3]#9PDfCRc#ZS0e12U_P^Q0\PVPVQ0]DQXA3,[311_UQ0^,2UPsPUPUPtC03]3]#9XCDP5Q08PXEd%eMS0f9`vr1BMNS0gPrPr1BM?S0hC05^u#9PLP91H@9Q0Y#b7`US0iQ001H@0S0j1cVKS0kg01ERRuP51H@AS0l14CIQ0N'cS0mp,8AL_grantPLP8O2%@BRB14CLS0n%@OROQ0nQ0nPTC0#93EQ00Q0:,4CS0o,1BPOQ0oQ0oPTC0#9PuP514C[,1BPO14CXS0pQ0pPTC0#9P:fKS0q#bS0r14C]RX/25Xp:S0sP2PRPcEdQ0Z,4C/2RS0t20HXO12XO1pXO+0GQ01Q0A,4CRv/2O1pvOPuP514CWS01/2OP]Q0Y,4CRt/2TS0u%31#A#<#7#7#?#<#7#A#PRs%31#A#<#7#7#?#<#7#?#PS0v'rR^%31#?#7#J#?#A#?#?#PRg%31#?#7#<#A#<#A#J#PS0w'rRa%31#A#7#<#J#?#A#A#?$0BR;%31#A#7#<#J#?#A#?#PS0x'rR11rBORP&0@3S0y5h3S0z5h3S0{5h3RH5h3R`9=35S0|Q0\14CKRePeQ0]DQXA3S0},[3Re'6S0~PTPtPtPRC0S10Q0gPtPtQ0hC0S11'gS12Q0uPePjPiPlPkPnPmPoPhPGfV,;DS0uQ0u#>Re,1qS13PGPqQ0LQ0uPe%DeEYfPDXS0uQ13fW,;DRe#WS14%>e#8S15PbPwPdPxPyP4p-0RePfPz1~:7S16?U7p9Up8S17P|P}Q07,j:Q0Q'\9F}~S07P=P}1o}0S18Q0R=G}~S19Q075S}1o}2S1:5s}5s},w}S1;P=Q0R9F}~S1<FKP>PJb;b=b>X0:X?:X<eW@1C8QS1=,25PTP8P81C7QS1>C0=^90Pu[127T[[^0:^?:^<e^@eP5Q0gQ0q,4CS1?Q1?Q0hC0S1@Q1?/2TQ0|Q0\Q0b,4CS1AQ1AQ0]DQXA3,[3'6S1APMQ1?Q0ZfHS1BO6b2b3b4b5b6b1b7b9b:b8P3Q0}PPA=3P`%iPPtPt%kPC0S0}A53^PA=3PHA53aPQ0{9=3PA531PQ0z9=3PA53PPQ0y9=3P1a3P3M3L3L3LPjPiPlPkPnPmPoPhQ0uQ13Q14Q15PbPwPdPxPyP4PfPzQ17P|P}P}P}%:ORPP~Q1<DT,w}S17P=P}%:B=G}~S0yP=P}Q07P=P}Q1;P=P}Q0yP}207~PCxFKFKP>PJb;b=b>X0:X?:X<eX@ePOP5P5PTC0Pu[11B81C9Q,27S0yPTP9P91C0QC0S1;=^2APu[PBP0P0POC0[[[[^0:^?:^<e^@eP5Q1@Q1APMQ1?P]Q0AQ0ZQ1BO8b2b3b4b5b6b1b7b9b:b8Q0}eCRCnCR3MO1WLP5O1Q01/pOP]Q0~Q12Q10Q11PjPiPlPkPnPmPoPhQ0uQ13Q14Q15PbPwPdPxPyP4PfPzQ16?U8pS15P|P}P:P~g025_PPCf-0r}P=P}Q17P=P}Q04,j:RPQ0Q'\9F}~RBP=Q19=S}BCOFKP>PJb;b=b>X0:X?:1p5O128TS199EO8Pu[Q0yQ1;[[[^0:^?:P5PMQ1?P<P]Q0ZO5b2b3b4b5b6b1b7b9b:b83M3LO1WLP5O1n200110000021110211101bmbEWZWYP8P5O2n2001000000121000000bFWEWDP8P5O2n2001000000121000000WGQ0i#9e20<@9S0ip,7AL_globP0P5O2PgPVPVQ0wC0P714C2RO/2TS12Q0|Q0\14CARBPBQ0]DQXA3S0~,[3S11'6S1011TO12ORQ0gPOPOQ0hC03]S1?Q12Q11PjPiPlPkPnPmPoPhPGQ0VQ0W,1qS0yPGPqQ0LQ0VQ0WQ0W#DEYQ0KDXS1;Q0yQ0q,;DS0q#WS04Q0q#>#8S0qPbPwPdPxPyP4PfPzP{P|P}1o}9S17Q0w#:9F}~S145S}P=Q1<COP>PJb;b=b>X0:X<eQ0w,25S13,68Q19[^0:^<eP511gvPvP<O3b2b3b4b5b6b1b7b9b:b8P3Q0~PaA=3a`%iaPOPO%kaC0S0uA53^aA=3aHA53aaQ0{9=3a1a3a3M3LPjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}P}P}%:gP~Q14DTS14P=Q14COP>PJb;b=b>X0:Q139Eg5PgP8P8Q0wC0[^0:P5PvP<O2S0wb2b3b4b5b6b1b7b9b:b8Q0ueCRCnCR3MO1bDWDQ0i#9e20:@9S0ip,8AL_errnoP0P5O2P;PVPVQ0xC0P7Q10Q1?Q12Q11PjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}Q17Q0x#:9F}~S115S}P=Q1<COP>PJb;b=b>X0:X<eQ0x,25Rg,68Q19[^0:^<eP511;vPvP<O3b2b3b4b5b6b1b7b9b:b8P3Q0~P1A=31`%i1POPO%k1C0S0~A53^1A=31HA53a1Q0{9=31A5311Q0z9=311a313M3L3LPjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}P}P}%:;P~Q11DTR1P=P1COP>PJb;b=b>X0:AE;5gP;P8P8Q0xC0[^0:Q0wb2b3b4b5b6b1b7b9b:b8Q0~eCRCnCR3MO1bKWKQ0i#9eQ0<P812VTR;Q0|Q0\POPOQ0]DQXA3S0i,[3Rg'6S1?PTPVPVPRC0S10Q0gPVPVQ0hC0S0h'gS0gP;PgPjPiPlPkPnPmPoPhPGfIS0~,;DRg%>gR;,1qR1PGPqQ0LPgP;%D;EYPcDXS0wP1Q0V#WS0VQ0W#8S0WPbPwPdPxPyP4PfPzP{P|P}Q17%:sR;Q0;#:606:9F}~Rg5S}P=Q1<COP>PJb;b=b>X0:X<eQ0;,Bs,25Ra,68Q19[^0:^<eP511sXPXP<O3b2b3b4b5b6b1b7b9b:b8P3Q0iP^A=3^`%i^PVPV%k^C0R`A53^^A=3^H1a3^3MPjPiPlPkPnPmPoPhQ0wP1Q0VQ0WPbPwPdPxPyP4PfPzP{P|P}AG};~R;=S}gP=P}P;P}Q0v#:-07~CxCOP>PJb;b=b>X0:AEs5aPsP8P8Q0vC0[^0:P5PXP<O2b2b3b4b5b6b1b7b9b:b8P`eCRCnCR3MO1W\Q0=eQ0@PUPUQ0?C0R`P8Q1?Q0gQ10Q0hPjPiPlPkPnPmPoPhQ0wP1Q0VQ0WPbPwPdPxPyP4PfPzQ15P|P}P}P}Q0>#:,\~R1Q0O'\PPAF}P1DTP=P}Q18Q1:P}P}Q0X:06:~PPQ0P:06:~9F}PDTR~5s}5s},w}P=P~FKP>PJb;b=b>X0:X?:X<eX@eQ0>,C5R~Q0H'CP8P8P~C01B8NP7P71B8?C09^90Pu[1B7NP9P91B7?C0[[^0:^?:^<e^@eP5PTPXPXPRC012XTQ0|Q0\PvPvQ0]DQXA3,[3'6PXPMP<P[O6b2b3b4b5b6b1b7b9b:b83L3LO1Wa%9`eO6bHbHWHXPDQ0[00;6,4CR`#ePSPSP`C0Q0YP8O1=IFEPDQ0A#vR`9uDc#ZQ0^PUPUPSC0XCDP8Q0ePcP`P6PjPiPlPkPnPmPoPhQ0a,|6%V\Q0JQ0aP\%D\R`C{PGQ0a11q\RXPGPqQ0LQ0aP\P`EYQ0YDXPXQ1B,;DRX#W%>X#8PbPwPdPxPyP4Q0MQ0EP5fMRX,;DR`#>R\P2O2b2b3b4b5b6b1Czb7b9b:b8CyEdQ0e,4CR3#ePrPrP3C0PDQ0K#ZQ0^PVPVPSC0XCDP5Q08Q0ZEdQ0fPUPUPMC0PLP0P7O212VZQ0jQ0k'6PcP0O1=IFE3^Q0212OZ1H@21cOcQ0KP2O1=IFE3]Q0NPAO1=IFEROP512BZQ0_PIO1=IFERVPjPiPlPkPnPmPoPhPGQ0cQ0d,1qRUPGPqQ0LQ0cQ0dQ0d#DEYQ0_DXPU%W`%8\PbPwPdPxPyP4Q0S%qGR\#qR`#q,t:1t:`1t:\1t:6605:605:605:g00`F+0q;hfPzQ151~:99Up97U9P|P}Q0C,j:R6=F}PP=P}Q05,j:R\Q0Q'\R`=G}6RUQ1:5S}P=P}Q0R9G}PP=P}Q0T=G}\R\P=P}P\P=1o}ACOFKFKP>PJb;b=b>X0:X?:XO:X<eX@e1275Q1>?E90117TQ0D/10Q0D/12Q0:[[[[[^0:^?:^O:^<e^@eP5Pu12tMPtPMPZP<Q0ZPKQ0KQ0BO:b2b3b4b5b6b1b7b9b:b8+0EWGP5O1Q0lQ0K,cB;]OQ021H@IQ0m'6PVQ0`PLO1=IFERVP51H@LQ0nQ0_#b3`Q00Q0:,H@Q0oQ0`'cQ0~P<O1=IFEP51H@[Q0pQ0U'cQ0bQ0ZO1=IFEP:Q0rQ0sP5PRPcEdQ0tPjPiPlPkPnPmPoPhPGfS,;DRh%>hRo,1qRmPGPqQ0LPhPo%DoEYPXDXPmfT,;DRm#W%>m#8PbPwPdPxPyP4PfPzAU{7pQ169Up77U7P|P}AF}6`P=P}Q189S}UP=Q1:FKP>PJb;b=b>X0:X?:X<eX@e1C5Q,28Q1=?E79P2[[^0:^?:^<e^@eP5PuQ1B,4CRC/2MPCPMP<Q0KO6b2b3b4b5b6b1b7b9b:b8bE+0EWEWDP8P5O2n2001000000121000000WJP5O1P5XGVP5O1n200100000021100010000WJP5O1n200100000021100011000blbIbIWWWIXPDQ06Q03Q0I/1Y%>8,Br/1_P0P9P7P8P5I0pWSWRWkXFDWjP[Q09PWQ0Fp,3AMBp,3a0sp,4path40o$0iQ0AP[PLPIL0hNA0gQ09Q0GP]&0e[H0Ceb^b]b_W[WXWbWTWUW`WeWVWiWfWoWdWcWnWQo"). Qed.

  Lemma env_ok_fcall : forall A M M' vm,
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a : word, ~ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) -> ~ al_globals a -> ~ al_errno_slot a ->
                      ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8)%Z ->
                      ~ (bv_unsigned sp0 - 208 - LEPT_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRunL ()) ["TRunL"] "h04__x1h14__p1h21ah34__p2h44__x2h57__arithh64__ffh76__sat3h86__sat4h96__sat5h:8__varmaph;5__with<5heq_Lh=9heq_callsh>7heq_cfgh?:heq_paylenh@4__p3hA2HahB1HhC2HghD1ohE2HehF3HlthG1AhH2FRhI2H0hJ2H1hK2H2hL3HEahM3HElhN3HErhO2HIhP3HfrhQ3Hg1hR3Hg2hS3HnehT4HtophU1MhV2M'hW2a0hX2vmhY1xhZ1zp%0p&0p;3p;2p;1p;5p;6p;4p;7p;8g01FKk30KTg01GTk30JTg01H]k20:Tg003oj10Tg004Tj1yTg0052j1xTg005Uk109Tg026Fj3fTg027Dj3eTg018Bj28Tg00Q0j21Tg0092j22Tg00;Sj33Tg012hj1ATg00NEj1uTg009NR0j29Tg01W;j5mTg01X>j1@Tg00:\j2TTg01Y6j2bTg01Z9j2rTg01Mfj1PTg01[:j2{Tg00F7j2zTg00BPj1:Tg00:@k60ITg013ck10HTg00;9j2\Tg014Yk10GTg015Pk10FTg016Dk10ETg0176k20DTg013Fk20CTg017^k30BTg018lk20ATg019]k20@Tg00?Hk10?Tg0067k10>Tg00?hj2wTg00MDk10=Tg00@dk10<Tg00ABk10;Tg00Amj2]Tg00PMj3gTg00CXk208Tg00D:k207Tg00Dfk306Tg00EEk405Tg00JTj1YTg00L[j2STg00UFj2_Tg00C5k304Tg000`j6lTg00S4j2ZTg01P7j4sTg00@Fk402Tg00Mbk201Tg00SNj4QTg00T9j7UTg00W6j7[Tg01o:k600Tg00WZj7aTg00VRj6~Tg00X>j8nTg00T]j3}Tg00V2j3|Tf0R1#0#0p=c%01#0#:p=k%:1#:#0#0p=^%01#0#0#0p=;%:1#0p=5%01#0#0#0#0#0#0#Ap=H%:1#:p=6%01#:p=<%01#0#0#Ap=N%:1#0#0#0p=jf3R2f2R3'1f1R4/21'9p=71934/Z1p=?%01#Ap=v11231241'9#Pp=D%01#:#0#0p=Rg00Y@R5?341p=O1241,93#Pp=d%01#0#0#0#0#0#0#0p=q1241,93p=>1Z41,Z3p=I1134/91p=og00XbR6/11p=WP5P3P4P1H02p=C20151p=4P3g00[DR7g00[cR8P8g00\CR9P5P4g00a2R:P1CQg00]JR;FUp==P5P4g00aYR<P1CQp=iP2P7P8P8P9P3P4P7P8P8P9P1P;FUF[p=hP4P7P8P8P9P1J00p=FP3P7P8P8P9P5P4P<P1CQP;FUp=Jf6R=P7P8P8P9f5R>P7P8P8P9P5f4R?P:P2CQP;FUP3P7P8P8P9P5P4P<P1CQP;FUF[p=GP3P7P8P8P9P4P1F[p=MP?P7P8P8P9P2P7P8P8P9P3P4F[P1Fap=VP?P7P8P8P9P2P3P7P8P8P9P4P1FaFap=KP4P7P8P8P9P1E~p=`P=P7P8P8P9P>P?P2P7P8P8P9P3P4P1GnGnp=BA}541p=Lg00_ZR<?|41p=XP2P7P8P8P9P3P4P1Gnp=EP?P7P8P8P9P2P7P8P8P9P5P3P:P4CQP;FUP1F[p=tP3P7P8P8P9P4P1Fap=p1941,Z3p>03p,2ALR7p,2CLR;p,3ASR:0K7;60J7R;+0:g00b@R:#0R@#0RA#0RB#0RC#cRD#yRE#xRF%yB#xRG$09RH[PH^YFg01SXp,3sp0RIp,4mem0RJ;f3P0AeIJ2%k:#^#;#5#HRK18E1RL'1%0:#5#6#;#<#;#6#NRM,2L%0:#5#6#;#j#<#6#NRNPLPL%0:#5#6#;#5#<#5#5#NROC73?RP%k:#^#;#5#<#<#5#vRQ18E4RRPR%k:#^#;#5#<#5#NRRCDRSP=P3O1PJP3O1RT53H[[^2F%cD#;RD#cS00#cRU#ARV/1LRW%0:#R#<#5#;#HS01,2L%0:#R#6#<#j#HRXPLPL%0:#R#6#<#5#;#<#NRYC73?RZP>P4O1%uGRG53H[^2F'9P7P;P>P?P3Dm%@218EIR[%HURU'TR\'O1b71R]%@>7dL1r74#PR^1{73S02#PR_g021cS0318E2R`P`Q03%ABRB'zS04CDRa%::Rb#0#5#NRc,T[S05g022g'TS0618E?RdPdQ05CDRdf;ReP>O1f<RfP>O153H[[[[[^2FAfIJ=[[[P1AeIJ>f9RgP3O1=3HT\S\P^2Ff8RhP4O1=3HG\Z^2F'9P0f:RiP3O1=3HT\S\P^2FPgP4O1=3HG\Z^2FP7P;PgPhP=Dmf7Rj#@/O\%@g9d]Lf?S07P>O1f@RkP>O153H\d\a\_\^[^2FAfIJi[[[P1PfP3O1=3HT\S\P^2FPfP4O1=3HG\Z^2FP7P;PfPePgDm%@i/O\%@f9d]LfBS08P>O1fCS09P>O153H\d\a\_\^[^2Fp,4SPloR^%:bRb#:#6#6#6#6#6#6#q#q#q#HRa/1[11[LS0:%0:#R#6#5#;#HRd9>WL;IPS0;P?P31b7318E3RW%@k3>S0<P01b72fAS0=#@,2`g01ERRkP11b7>18E=fDS0>#@'2p,8AL_grantPjP4O2%ADRD18EjRLPVPLPL%0:#5#^#5#;#HRLCD3oP018EhR0,1DPVP0P0PLCDPkP118EiR0,1DPV18EeRDPDPLCDP5fJ#@f=S0?,8E/21XZ5P>P\Q07J0I18EfRD/2\p,4dataR\$0HR],\5p,5calls/O]R]eR;P]&0G\Rl,\5p,6paylen/OlRleRmPl&0F\Rn,\5p,3cfg/OnRneRoPn&0E\R\,\5p,1L/O\R\eRpP\%A@Rq%:@S0@#:#vRr+0DRs126q%Wr20CqrRt,26[[Ru%WqRvg01EoRwB0Bqr4UWARr%Wt\w^AvRv%ACRC-0A[Rw%W[%WC20@[C#W[[RCp-0Rt&0?<Rq&0><R<1w54Rx&0=5Ry7C31w53Rz9Cy37C3S0A&0<5R{&0;5R|P|%4VS0B1]5bRb5=|R}P|%4L,ibCh,F|%u8R8P|1]5ARA%4U5g59J|bP8P|P|P|%4QS0CPbP|Pb%4RS0DFGS0E,F|S0FP8P|P|A=|AbS0GP|%4dR~9J|bS0H9M|}P|P|%4KS0I==|b%4MS0J9J|bS0KP|P|%4NS0LPbP|Pb%4OS0MFGS0NDVDKP81`|?R}FBFB208|9R9P1P3g00beS0Og00cES0P'\Q0O20713Q0P33dB06564H05R6b6b:b;X05X45W111V4S0P?>4LPk[1T4U,23122RS0O9oQ2Pk[112?PVP?P?PdC711K?12?MPNP?P?POC73?3IP=[[[[^05^45^1tP1PkfE,8EP[PgPhQ09Q0>O7b5b7b8b9b<b>b?b=bFWRWQP4P1O2n2001000000121000000bWWFWCP4P1O2n2001000000121000000WIQ0<#Pe1r73S0<p,7AL_globP2P1O2POP`P`%0:#5#^#R#<#HR7C7P;P]PmPlPoPnPpP\PsPuPrPvPwPCg00ceRU#YS0>#YRL#YS0Q#YS0R,S5S0S1S5LS0T1S5US0U'L'Lg00`FRU'_/XqS0VP<Q0AP{P|P|P|Q0MPbP|Pb%47FGP8P|Q0FP8P|P|Q0GP|Q0H9M|}P|P|1`|>RbQ0KQ0NDVDKP8P|%4aRL==|ARAP8P|PAP81`|=R=CEFBFBP9P6b6b:b;X05X45X1tX3tX@tPOP4P4P7C7PQP3P3PRC7Pk[1132A>?2d122MPNP2P2POC75?>3I11a2R711a?Pg[[[[[^05^45^1t^3t^@tP1Pk11KD11VDPDP[PhPiPeQ0?P^O:b5b7b8b9b<b>b?b=bCWCQ0<#PeQ02p,8AL_errnoP2P1O2PQP`P`PRC7P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<ACy4x9Cy4P{P|Q0EP8P|Q0FP81`|2R`FBP9P6b6b:b;X05X1tPQP1P1PRC7S0F11Q4S0E?>4RPk[RAP2[[^05^1tP1PkPDPhPiO4b5b7b8b9b<b>b?b=bEWEP_eP;P]PmPlPoPnPpP\PsPuPrPvPwPCQ0VP<ACz3y9Cy4S0VP{P|P|Q0@,]5R_1]5:Ri5=|S0@P|P|P}P|1ii~ChP|P|Q0I==|iPbP|P|Q0LPiP=DtDVDKP8P|A=|L_R_P8P|P_P8P|P|%0:#R#6#6#j#6#<#NR:#4R=PiP|Pi%4B:045=FG,F|CEFBP9P6b6b:b;X05X45X1tX3tX@t1141S02A>31d11K1S0<11N1S0?/9?7?23I11a3RaP:P2P21z:BC7Pk[\7[[^05^45^1t^3t^@tP1120O120M11V0R:P[P0PgPeP^O8b5b7b8b9b<b>b?b=Q03PWPWQ04CDeP;P]PmPlPoPnPpP\PsPuPrPvPwPCQ0SQ0TQ0>,S5RB'LR='L/_URDQ0R#Y,S5/L=/_U/Xq,XD,XD'XP<ACz4yS0RP{P|P|P|Q0C1]5@R@P|P@Q0DFG,F|P8P|P|A=|i@RzP|AJ|@~S0S9M|}P|P|PbQ0J9J|@S0JP|P|Q0LP@P|P@Q0MFGR~DVDKP8P|A=|LiRLP8P|PLP8P|P|%4c9g5iRLQ00#ARD#45g5P@P|P@PLFG,F|FBFBP9P6b6b:b;X05X45X1tX3t1143RLA>23d123MR=PNP3P3POC75??3I1T?cRc/TDP>P>PcC7Pk[\7\a[\A^05^45^1t^3tP111K0P:P0P[PhPgPeP^O8b5b7b8b9b<b>b?b=Q06PWPWQ05CDeO6XSSWAX2FQ0;Q0=P3O1Q08P3O1RW53H\S[^2FQ079eIJS07A3HWT\S\P^2FRIQ0=P4O1Rc=3HG\Z^2FRD'9Q0:PHQ08P4O1S08A3H1TXDHPfP4P1O2PcP3P4P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<Q0RP{P|PzP8P|PzP|P}P|P|Q0IP@Q0JDtRz=p|bDKCEP9P6b6b:b;X05X45X1tX3t111411K3??=?9IL2[^05^45^1t^3tP1PN18EgREPEPOC7RL11VER=?>EdPEP[PhO5b5b7b8b9b<b>b?b=P;P]PmPlPoPnPpP\PsPuPrPvPwPCQ0Q,S5Q0U,LB'L/_U/XqP<Q0VP{P|Q0@P8P|P_P8P|P_P8Q0D9J|iR_9M|},F|CEFBP9P6b6b:b;X05X45X1tQ02Q0O,9>Pk[\7\a[^05^45^1tP111QEP[PEPhPeP^O6b5b7b8b9b<b>b?b=O3ElWAX2FQ07ePIPDPHQ09P3O1PJP2O193H1XDHPgP3P4P1O3PWP2P3P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<ACx4yRyP{P|Ap|z~R~P8P|P`P|P}P~DKCEP9P6b6b:b;X05X1tX3tQ0<121MQ0??>1O3?PKP4P4PMC7RM11N4124O4039I32[^05^1t^3tP1A>:0d11[0P0PgO4b5b7b8b9b<b>b?b=P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<PxP{P|Q0C==|iRg=M|_,F|R_P8P_CEP9P6b6b:b;X05Q0FPk[PA[^05P1P0PhO2b5b7b8b9b<b>b?b=O3ElXKSXJPX2FPHQ08A3H1GXDHPjP4P1O2PcP3P4P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<PyP{P|P|P|Q0B==|@RyQ01#4Rc9J|@P|P|%4XP@P|P@%4YR@FGDVP8P|P`P|Q0S9M|yAp|z}DKCEP9P6b6b:b;X05X1tX3t11V1Q01,21RV121YRY9oX13?Q0P?>4d1ZM25I3[^05^1t^3tP1PL11[EPEPhO4b5b7b8b9b<b>b?b=P;P]PmPlPoPnPpP\PsPuPrPvPwPCPqP<PxP{P|P|P|P`AJ|icP|P}P|1ii@ChDVP8AM|gb,F|CEP9P6b6b:b;X05X1tX3tX@t193Y9?4VQ0E/9?Pk[[^05^1t^3t^@tP112ER11XEP=PEPhO5b5b7b8b9b<b>b?b=O3ElXAZX2FCsCsbHbBWPWTWOWNWMP4P1O2n2101000010121000000WBWLP4P1O2n2011000010121000000WBWXWVWUWGo"). Qed.

  Lemma paylen_factsL : (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z ->
    (0 <= paylen < 2 ^ 26)%Z /\ Z.of_nat (length payload) = paylen /\ (0 <= cfg < 32768)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRunL ()) ["TRunL"] "p;1p;2p;5g00BPj12Tg003oj11Tg012hj10Tg00F7j23Tg00Q0j27Tg013Fj26Tg0092j25Tg028>j54Tg00b@R0#2#1R1#0p,3cfg'3p,1LR2'7%10#0%21#1#0'6,52p,3sp0p,4Hvspp,4dataf1f0D4UUo"). Qed.

  (* [comment removed for export] *)
  Definition A_INCB : Z := 0x137f14.   (* [comment removed for export] *)
  Lemma incb_block : forall A vm M buf cap owned aligned E (v : expr),
    (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z -> ev E 0 = sp0 ->
    sideT A vm M buf cap owned -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
    sideT A vm (mem_denot E M [SE (SA (ELit 0) 0x137f14) 1 v]) buf cap owned
    /\ copyP (mem_denot E M [SE (SA (ELit 0) 0x137f14) 1 v]) aligned owned
    /\ bytes_at (mem_denot E M [SE (SA (ELit 0) 0x137f14) 1 v]) (bv_unsigned buf) data
    /\ (forall x : word, bv_unsigned x <> 0x137f14%Z -> mem_denot E M [SE (SA (ELit 0) 0x137f14) 1 v] x = M x).
  Proof.
    intros A vm M buf cap owned aligned E v HLc HL26 HE0 HS HC HB.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
    destruct (paylen_factsL HLc HL26) as (Hpl & Hplen & Hcr).
    assert (OUT : forall x : word, bv_unsigned x <> 0x137f14%Z -> mem_denot E M [SE (SA (ELit 0) 0x137f14) 1 v] x = M x).
    { intros x Hx. pose proof (u64_range x) as Hxr. cbn [mem_denot]. unfold adenot, v_addi. cbn [a_base a_off edenot].
      rewrite ?(u_small 0) by lia. rewrite ?Z.add_0_l.
      rewrite MemSplit.wbytes_outside; [reflexivity | |];
        rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat]; rewrite u_small by lia; lia. }
    destruct (sideT_block A vm M buf cap owned E [SE (SA (ELit 0) 0x137f14) 1 v] HS ltac:(reflexivity) HE0) as [HS' _].
    destruct HS as ((HI & Hl & Hvl & Htop & Hisp & Hres & HEnv & Hc0) & Hlo' & Hln).
    split; [exact HS'|]. split; [|split; [|exact OUT]].
    - destruct HC as [HC1 HC0]. split; [|exact HC0].
      intros Hp. destruct (HC1 Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [|split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A M vm owned paylen HI (Hlo' Hp) Hp Htop) as W.
      intros i Hi. assert (Hi2 : (0 <= i < paylen)%Z) by (rewrite <- Hplen; exact Hi).
      rewrite OUT; [exact (HBp i Hi)|]. rewrite Hao. rewrite u_small by lia. lia.
    - intros i Hi. assert (Hd : (Z.of_nat (length data) < 2 ^ 26)%Z) by exact HL26.
      pose proof (u64_range buf) as Hbr.
      rewrite OUT; [exact (HB i Hi)|]. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem fz_call : forall (fxp : FPState) (K : TSet) A vm vals R M buf cap aligned owned (rem : Z) kn,
    frm_zero (@fp_csr fxp) ->
    length vals = 50%nat -> slotsL vals buf aligned owned rem ->
    regs_ok (ENV vals) tl_sr1 R -> know_ok RSEGS (ENV vals) M kn -> kn_vars_lt 50 kn = true ->
    existsb (is_kimg_cov A_EMPTY 16) kn = true -> existsb (is_kimg_cov A_LEPT_SEV 8) kn = true ->
    existsb (is_kimg_cov A_LEPT_PMM 16) kn = true -> existsb (is_kimg_cov A_MORPH_BC 4) kn = true ->
    existsb (is_kimg_cov A_GOT_LO (A_GOT_HI - A_GOT_LO)) kn = true ->
    existsb (is_kwr_cov (EVar 0) (-6144513) 6144513) kn = true ->
    sideT A vm M buf cap owned -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
    (L < cap)%Z -> (cap <= 67108864)%Z -> (6 + cfg <= L)%Z ->
    (* [comment removed for export] *)
    (1 <= rem)%Z -> roomT A vm rem ->
    (forall (fx' : FPState) A' vm' M' R',
        frm_zero (@fp_csr fx') ->
        regs_ok (ENV (vals ++ junk_vals R')) tl_sr2i R' -> know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_fcall kn) ->
        sideT A' vm' M' buf cap owned -> copyP M' aligned owned -> bytes_at M' (bv_unsigned buf) data ->
        (forall a : word, (0x158890 <= bv_unsigned a < 0x159000)%Z -> M' a = M a) ->
        roomT A' vm' (rem - 1) ->
        realizes RSEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x634dc) M' (seg_rom RSEGS)) (model2 vm')) K) ->
    realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x635e0) M (seg_rom RSEGS)) (model2 vm)) K.
  Proof.
    intros fxp K A vm vals R M buf cap aligned owned rem kn FRM HL SL HR HK VLK Xe Xs Xp Xm Xg Xw HS HC HB HcapL Hcap26 HLc Hrem1 HRT HKONT.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    destruct (paylen_factsL HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    destruct HC as [HC1 HC0].
    unfold model2, V23ReadLoop.model2.
    assert (R10 : getr R 10 = aligned) by (regv HR (10 : reg); cbn [edenot ev ENV V23Open.ENV]; exact P14).
    assert (R11 : getr R 11 = Z_to_bv 64 paylen) by (regv HR (11 : reg); cbn [edenot ev ENV V23Open.ENV]; rewrite P9; reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x634dc) by (regv HR (1 : reg); reflexivity).
    assert (R3 : getr R 3 = Z_to_bv 64 0x10800) by (regv HR (3 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x1381d0) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V23Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    assert (KW : forall (d : Z) (m : nat), (-6144513 <= d)%Z -> (d + Z.of_nat m <= -6144513 + 6144513)%Z ->
                 store_ok RSEGS M (adenot (ENV vals) (SA (EVar 0) d)) m = true).
    { apply existsb_exists in Xw as (Kw & Hin & Hc). apply In_nth_error in Hin as [iw Hiw].
      destruct Kw as [| | | | | |[bw kw] nw|]; try discriminate Hc.
      cbn [is_kwr_cov] in Hc. apply andb_prop in Hc as [Hc Hn]. apply andb_prop in Hc as [Hb Hk].
      apply expr_eqb_eq in Hb. apply Z.leb_le in Hk. apply Z.leb_le in Hn. subst bw.
      intros d m Hd Hm. apply (kwr_store_ok RSEGS (ENV vals) M kn iw (EVar 0) kw nw d m HK Hiw); lia. }
    assert (EQcfg : @mkst fxp R (Z_to_bv 64 0x635e0) M (seg_rom RSEGS) = @mkst fxp R (Z_to_bv 64 PC_FUZZ) M al_rom) by (rewrite AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC V23Open.fds0 vm stdin0 fs0 None (Some tid) None).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (fuzz_margin_bound paylen Hpl) as HFM.
    destruct (fuzz_step FUZZ_CALLS FUZZ_BMAX rem) as (EK & EB).
    destruct (fuzz_nonneg FUZZ_CALLS FUZZ_BMAX (rem - 1) HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hrem1; lia)) as (HK0 & HB0).
    eapply (FZ fxp A M md R aligned paylen payload (Z_to_bv 64 0x634dc) sp0 [a0s; path] envv K FRM HI).
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
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V23Open.ENV] in Hst. rewrite P0 in Hst.
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
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_MORPH_BC (A_MORPH_BC + 4) HK); [| exact Ha].
      replace (A_MORPH_BC + 4 - A_MORPH_BC)%Z with 4%Z by lia. exact Xm.
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
      assert (IMGFR : forall a : word, (0x123000 <= bv_unsigned a < 0x159000)%Z -> ~ (0x1584d0 <= bv_unsigned a < 0x158880)%Z ->
                       ~ (0x13812c <= bv_unsigned a < 0x138130)%Z -> ~ (0x127c68 <= bv_unsigned a < 0x127c70)%Z -> m' a = M a).
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
        intros i Hi. unfold V23TRun.L in *. rewrite <- (HB i Hi). pose proof (Hlm buf cap i Hl ltac:(lia)) as Hq. unfold at_ in Hq. exact Hq.
      + intros a Ha. apply IMGFR; lia.
      +
        unfold roomT. apply (aroom_mono A' vm' _ _ _ _ Hroom'); clear -EK EB HK0 HB0 HFM; lia.
  Qed.
End TRunL.
