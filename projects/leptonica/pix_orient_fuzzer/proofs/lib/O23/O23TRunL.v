(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibKnowXfer LibTail SymCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2 RefPrintfLib LibWritevG.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib Frame.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Room.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23ExitBase O23StdioDefs O23Exit O23Startup O23StartupDefs O23StartupFacts O23MainEntry O23LibStdioCall O23OpenFail_defs O23OpenFail_tail O23OpenFail_tail2 O23Open_defs O23Open O23Oom_defs O23Oom O23MemPreds O23Malloc65536 O23DirRead_defs O23MemcpyBase O23Memcpy O23ReadLoop_defs O23ReadLoop O23Grow O23Hdr_defs O23Hdr O23FuzzIface O23TRun_defs O23TRun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac FPSteps.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23TRunL () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List<length_skipnK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3O23;O23MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3subC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9nth_skipnK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;is_kimg_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC59OSSVerify5KrLib3O23;O23MemPreds9img_clearC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3O237O23TRun5callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun6paylenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun1LC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun5sideWC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop6in_winC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3O23;O23ReadLoop7in_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun;sideW_blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ReadLoop7DATA_RSC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3O23;O23ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs8kn_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface>A_LEPT_HANDLERC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface:LEPT_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs5LGLOBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib3O23>O23Malloc655366env_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open9above_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun<paylen_factsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib9micromega;ZifyClasses3injC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun:bufW_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedc59OSSVerify5KrLib3O238O23TRunL=paylen_factsLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O238O23TRunL;sideT_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun7payloadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23>O23Malloc65536:live_whereC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib3O23<O23FuzzIface7A_EMPTYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O238O23TRunL6slotsLC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:is_kwr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun5roomTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr6slotsRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr7hdr_cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr7hdr_b1sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O236O23Hdr6hdr_b2C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<In_nth_errorC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28expr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIfaceAfuzz_margin_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface;fuzz_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room9fuzz_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room;fuzz_nonnegC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O238O23TRunL;kimg_clearLC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC59OSSVerify5KrLib6Common8VmLedger;init_sp_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23TRun=ownedA_rangeTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open3ENVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23>O23Malloc65536>regs_ok_same10C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O238O23TRunL@know_after_fcallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O238O23TRunL<env_ok_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:aroom_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs7tl_sr2iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23TRun_defs6tl_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8PropExec7FPState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface:A_LEPT_SEVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface:A_LEPT_PMMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface:A_MORPH_BCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface8A_GOT_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIface8A_GOT_HIC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3O23<O23FuzzIface7PC_FUZZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open4fds0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3O23<O23FuzzIfaceAfuzz_calls_nonnegC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC59OSSVerify5KrLib3O23?O23MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23MallocLayout6LS17okC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
(* [comment removed for export] *)

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
ltac2:(KReplay.run1 (kr_t_O23TRunL ()) [] "h04__x1h14__x2h24__x3h31xh44__p1h54__x4h62H1h73Hi0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2z1h?2Hih@4__p2hA4__x5hB1nhC1yhD1HhE2H2hF2H3hG2HBhH1MhI1ahJ1bhK2bshL1ihM1khN1mhO1ohP1zhQ2z2hR2z3p&0p;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7p10000p4p70g000`R0p4p710R1p8p1001>p4p70P1p8p1001lp4p7210P1p8p1002Xp4p70P1p8g003NR2p4p710P1p8g003oj1HTg004Tj1wTg0052j1gTg005Uj1~Tg0067j1uTg006Wj3qTg007Tj3KTg0082j25Tg008RR1j10Tg0092R3j23Tg009Nj26Tg009ij2YTP2k30ITg00:@j6sTg00:\j28Tg00;9j2>Tg00;Sj37j1nTg00;mj3_Tg00<Sk10>Tg00=1j6^Tg00=Zj4\Tg00>Aj1TTg00>fj2PTg00?Hj1|Tg00?hj2XTg00@Fj4LTg00@dj1yTg00ABj1xTg00Amj2JTg00BPj1cTg00C5j3QTg00CXk20HTg00D:k20GTg00Dfk30FTg00EEj4rTg00F7R2j21Tg00FTj2aTg00G:R4j1VTg00GZj4Nj3pj2ok10ATg00H6j2Wk10DTg00HXk20ETg00Hok20@Tg00IRk30?Tg00Iol<lTg00JTj1CTg00K3k10<Tg00KQk20;Tg00L2j3iTg00L[j2hTg00MDk108Tg00Mbk205Tg00NEk104Tg00Ngk403Tg00ORj8RTg00Ook502TP0j6eTg00PMk307Tg00Q0j2tTg00QLk200Tg00QilBkTg00ROl<dTg00S4j2}Tg00SNj4UTg00T9j7[Tg00T]j3`Tg00UFj2MTg00V2j3ITg00VRk60BTg00W6k70CTg00WZj7{Tg00X>j8zTg00XbR0f0R5'tp=920005p=2g00Y@R6/>5p=;g00Y^R7P7P7P6P6P6g00Z=P1P1P1f6R8g00Z]f5R9f4R:f3R;f2R<f1R=P5MBkp=jP7P6P6P6P1P1P9P:P;P<P=P5M<dp=bP6P6P3f7R>P3P8P9P:P;P<P=P5M<lp=Z1305p==1t50p=<A7650p=BA76;<,6:16=5'}p=?P<g00[DR3g00[cR?P?g00\CR@P6P=g00\cRAP5CUg00]JRBF[p=vA76=5p=OP6P7P6P6P4P:P1P;g00]jP<P=P5M<dp=mP7P7P7P6P6P6g00^WP1P1P1P2g00_7P9P:P;P<P=P5MBkp>0=1h65p=AA`6=5p=4g00_ZR2g00`FR4,M=;I5p>0:A`6<=/M4=I25p=E1M<41M=4=I255I2p>09P=P3P?P?P@P5J0Bp=fP6P=PAP5CUp=GP;P3P?P?P@P<P=P3P?P?P@P5PBF[K0Cp=:P6P=g00a2P5CUp=FP=P3P?P?P@P5PBF[p=DP<P3P?P?P@P=P5F{p=]P6P=g00aYP5CUp=SP;P3P?P?P@P<P=P5Gzp=@A`6=5/M4p>01AI2=59I2<p>06g00b@R4#HR3#HRB#HRA#H#H#H#wRC#g%wARA#gRD#~RE[%uDRFAq;<=%95AKD<;,5D#0,35'6P7AKD;:,5D%9<RG%05RH,3<'6XB7P515D:/Y;RIB0ID;:Es%9=RJ%0I,3='615D9RI/Y:RK#0RL,3<RM,6G%0IRN%0:RO'8#2,3<,6GRPPGPMPGP5X36RM18=5#2XN6XB6RQPNPOO2RRO1RS,3<p-0RT/>GA7TGGe9_GGPM13=5$0>XC6X36RGP<P<%;<PLPSPMPM%;HX37RSPKPRPQPIPN%;NP:PO%;OFjEbGZE^P5C\PP%T9%09RP#915D>RN#T%0N#9f8RN,5DRI#0RR%0>'8RK,P0%=K%2KRLPK%<K%BLD?f9RL,5D#0%0N'8RK#2RUP6%|2RV%u2R2P61X6<P=1X6;RWCL%y6RX%x6RY1J64RZ1J63R[%c4,J6R\5Q6R]5Q6AQ6Z[R^=Q6\3v20HY@R@P5P<g00beR_g00cER`'>Ra20G5<=7_`dB0F60=R`CrR_b9b:b;X06X16X2611=<,15115=/1<'O^06^16^26P5PNf:Rb#0Rcf<RdO3b8b>b6b=b<b711O<,18118O/1<'OP611P;RO,1>RePL1aC5O1PD%V:AKD8>1aA0RACN,WDRf57EXP6PEPD%VORgP8PACNRh,WDA7E5fXOEPDPD%V;Rf-0E9RiP8PACNRjPD%08Rk/1:#VP>PACN,WD1WD557EXJDPDPE&0DDRlPlPhPjPE\D/>lPDPDApDg8ApDi8PAPAPFPD\DRl1oDg1oDiP8P8P7Pl\FRl&0ADREPEPgPiPl\7/>EA77gi%2ORE%2;Rl,1PRj'OP7P6%n7P1%n6%0=R1/OHA77=520@=540?XC7X37PgPEPM%25X36REPOPO%;ODmPiPjP9PP%;PRjPfPlPMPEP;P;%;;REDmJ0=M<l%9;Rl15D8Ri/Y9Rg#0RH,3;Rh'6Rm%0iRn/8P#2Ro,3;Rp,6lRqPlPhPlPMPQPnPPO2RrO1Rs,3;1>TlRtA7Tlle9_llPMPGP;P;PEPHPsPMPMPSPgPrPQPiPn%;nP9PPPjFjRjEbGZE^P=C\Pq%T8Rn%9kRk%TIRI%9RRR1P08%=8%28RiP8%<8%BiD?%2>P611cNRc,P0%=c%2cRiPc%<c%BiD?f;#0Ri/1L#2P6f=Rc,5D#0%0d'8RQ,P0%=Q%2QRrPQ%<Q%BrD?f>,5D#0%0c'8#2P6g00ceRr#CRQ#CRs#CRu#CRv#CRw#CRx#C#ARy&0<4-0;6R4%AxRx5i6Rz%AvRv%AsRs1h6rRr'4R{'4'4R|Ai64vR4%AuRu/4r'4R}%AwRw/4}14vr,4zRz144rR4,4x14w420:|V5Ex609z5Ey5Ex5Ex3EP2P6P61X6:P<&086RxCLRyP=P61X69P;PxCLCLPXPYPY1fY>RxPY1J6BRB9Q6[Rz,GZC:PY20560R|,Fz,DYPY1GZ|C:5]Y&04?R?PYPY1S|B,DYPY1G\BC:PY1FB|,DYPY1G\|C:5]YP?PY1F|[,DYRzP?PYPY1F|B,DYPY%c3,J6,SBC:P?AvYZ]C@C@C@C@P@P_b9b:b;X06X16X26X56XA6X4TP9P511=;R_%<_%B5D?%=:P;P:%<:%B;R_D?%98138>'61198,O:[\l[[^06^16^26^56^A6^4TP5f?#0R]/1c#=P=PcP9P]P;P:P8PNPLO:b8bRbFbQbEb>b6b=b<b7H03GR1>F8GR1>DAGRGRPDPfAKD98PACNPDP9P8PfPAI02EePN1aCeO1P:POPmPqPlPhPlPpA_lltPMPGP;P;PEPHPoPMPMPSPgPoPjEbGZE^P=C\PqPnPkPIPR1P0K%=KPUPK%<K%BUD?15Db#0%0L'8#2P6%AQRQ,4s-01vRs14QrAEu{V5Ev806sP2P6PyP=PWCLPXPYPY1fY8PYB076\Z,GBC:PYPxPY1GB|C:5]YP?PY1F|Z,DYP?PYPYPzPY1S[BC:P?PY1F|^,DYPY1S^\C:C@C@C@P@P5P<PaP`Crb9b:b;X06X16X26X56X4TX@TP:P;18<5P9P_D?13;9,6l11;:Rl#913l9'6[\J[^06^16^26^56^4T^@TP515Dd#0Rd/8iRT#<%=TP=PdPLPiP<P:P9O9b8b>b6b=b<b7O2Ee11>P/1;P5EsbDb?W?XL611;1AKD=<5q:eWGXM7WKXI6WHo"). Qed.

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
ltac2:(KReplay.run1 (kr_t_O23TRunL ()) ["TRunL"] "p'0h01Hh12Hch23Hinh31xi001xh41ih51ni011nh61ai021ah71ei031eh81mi041mh91Ah:2H1h;2H2h<2Hah=3Hexh>4__x1h?4__x2h@4__x3hA4__x4hB4__x5hC4__x6hD1fhE3hi0hF1lhG3lo0hH1EhI2HKhJ3HKKhK2HihL2HnhM1KhN1MhO2_HhP3_H0hQ7__arithhR4__ffhS6__sat3hT6__sat4hU6__sat5hV8__varmaphW5__withX2a1i052a1hY2a2i062a2hZ2e0h[5heq_Lh\9heq_callsh]7heq_cfgh^:heq_paylenh_2hii072hih`1ki081kha2knhb2loi092lohc2n1i0:2n1hd2n2i0;2n2he1vi0<1vhf1wi0=1wi0>1bp&0p;1p;4p;2p;3p;6p;7p;8g003oj14Tg004Tj1aTg0052j1_Tg005Uk108Tg0067j1XTg00dDj4xTg00:\j21Tg00eTj2ej3=Tg00f_R0j3ZTg00g;j3KTg009NR1j2>Tg00gRR2j2NTg00glk306Tg00hOj36Tg00iMj3QTg00jXj2TTg00k7j2[Tg00lBj3RTg00mMj2VTg00nXj2<Tg00F7j2HTg00o5j3mTg00Q0j25Tg00oXj2jTg0108j3`j4PTg011Jj3^Tg011kj3iTg012Mj6hTg012hj1DTg013Fj2]Tg0092j29Tg00FTk207Tg00NEj1fTg00;Sj37Tg013ck105Tg00;9j2JTg014Yk104Tg015Pk102Tg016Dk101Tg00BPj1:Tg0176j2~Tg017^j3}Tg018Bj2|Tg018lj2{Tg019]j2zTg00JTj1GTg00L[j2ITg00T]j3MTg00UFj2dTg00?Hj1wTg00V2j3cTg00MDj1vTg00?hj2UTg00@Fj4ETg00@dj1uTg00ABj1tTg00Amj2BTg00SNj4STg00PMj3sTg00C5j3rTg00Mbj2qTg00CXj2pTg00D:j2oTg00Dfj3yTg00EEj4nTg01:=j2WTg01;Hj3\Tg01<Sj2OTg01=^j4YTg00:@k600Tg00T9j7lTg00W6j7kTg00X>k803Tf0R3#4#4p=gg00beR4g00cER5773p=2g01>iR6f1R7;K3p=0f2R8?=73=745p=3P4P8P7g01@4P5P3J00p=Ag00XbR9/53p=;1587/>3p=8g00Y@R:P7g00a2P3CSp=FP7g00[DR;g00[cR<P<g00\CR=P3g00]JFlp=@P8P;P<P<P=P7P3Fkp=b%:3#:p=C%43#4#4#4p=?f3R>P;P<P<P=P8P7P3L03p=Lg01@Pg00b@R;#4R?#4R@#4RA#4RB#gRC#aRD#_%aA#_RA$08RE[%X6g01AXRFf4RGP>P8Cx1178,e8=Z6>#2P0p4p710R0P4\3RH%X7RIP1AZ873#2AKG38P>P3O1#2'>X3>,N>[RJAK>37P8P3O1#2'>X38,N8AZ>87#2RK[f5RL?K3>PGP3O1#2'>X3G,NG\KB06873P7n2001000000120000000WFWDW9PJ^FI^DH^90P3P611>G,eGPLP7O4f6R0,0311GL=3L3'>X36,N6P2P6f7R2,0311L0=303'>X36f8RH?60LP3f9RI,03112H=3H3'>P1f:R2,0711HI=3I7f<RJ?62IP310>Jf;RK/1J=3JGP6f?RM,03f>RN/1M=3M7fBROf@RP;6M]1]2PLg01C?RQg00Y^RRg01DIRSAQ873fDRT'0fCRU/1TRVAQ>8753TfERW11TWRXAQG>83=P4p-0P3g01ERRYg01EoRZn0110>00020000R[X74R\;A3PYfHR]fFR^;6W/T3R_b0W1W2WeWfW6P8P7P3O31[73/0OfAR`/1ORa1[8753O11OURb1[>85=U?A\3PYA6^TU/T3Rcb0W1W2X5SX6QP7P3O2AR873/0TAR>8793TVARG>89=WX?A\3PYP_b0W1W2X`RX5SX6QP8P7P3O31V73/0O1V8793Oa1<>URR1HUb/<8Rd;m3%2R%2d'>P11<GT#21HTV/<>#2fGRd?6WTP31<0^#211^dRR,Hd/<0#2P11<73#21587[Re15731<87#2Rf[15>8\f1j73P7n2001000000120000000X8:X5:RfPe^8:^5:ReP3PIfIRgP8O315IgPfPeP3fKRefJRf/1e'HReP2P>O315e2fORefNRg5`FRhfMRi5^6103ePFfRRjfQRkP7CP[^36[103gPFPkfPRlP7CP[^36A`Fle=^6g[Ai6hiPf1VJKRKP2EhPFPePgPKCPP1f=RK#;%D?RF%DC']RC193K98N3Pk207D7RNO1%fARA57E[^4:58JA6lgiP3%;M193P98`3fTRlPNO1=7EA[^4:98MCP115PC193`98O3fUR`PNO1=7EA[^4:A6ljkP315OC193T98W3fXPNO1=7EA[^4:fV193`783P8P7p,4dataRA$05RE,J:p,5calls=7:EREePE&04ARE,J:p,6paylen=7:EREePE&02ARE,J:p,3cfg=7:EREePE&01ARA,J:p,1L=7:ARAePA%:?RA#:#4#DRE,~F199F%;E1]FERN,99[[%;FRCA}FE7VZW<%;N\Z^<Cp,3sp0,|DRD%DBRB'{%;D%;B1zDB#;[[g00_ZRBg00ceRC#G#GRZ#GRN#GRE#G,I:1I:Z1I:CRC5M:5M:g00`FRZ'd1I:E1I:N=M:C5M:/dZ%wB5cB3c%XBP:P:%v:RBP8P:1U:0P0PBCECEP7P:P:1U:LP0PBCEP>1U:GCECE%u:%t:RB%:@,B:R@1B:?R?'F,@BP:P?g00aYRZ%4A,B:RACS,@B5bB%f<R<PBAs:A@9r:@%:;RA,B:RC'F,@BP<PB1B:;R;/F@,@BP<PB%:ARA#:#C#C#C#C#C#C#4#g#?#?#?#?#?#?#?#DR@,q:1B:A'F,@BP<1F;?,@BP:P?PZPCCS,@B5bBCLCLCLCL1pB=P3P81J451o38#2dAy:97CnbRbVbWX>:X?:X@:XA:XB:XC:197L98G7110L,HL/5>158015@019L098GL[[[[^>:^?:^@:^A:^B:^C:P3f^f_PDPgPIPePHPUPWp,4SPloO:bQbSbTbUb[b]b^b\O2WKX4:fW?6`leWLWPP7P3O2n2001000000121000000W0WOP7P3O2n2001000000121000000bJb;b0b:b0W;W:P7P3O2n2001000000121000000b1W1W2XE:XG:P7P3O21W73/0O1W8793Oa1W>89=UbP[XZ4R4;A3PYPcb0W1W2X8:X7SP7P3O2A\873/0TA\>8793TVA\G>89=WX?A43PYP_b0W1W2XE:XG:X7SP8P7P3O31O73/0O1O8793Oa1O>89=Ub?A\3PYPcb0W1W2X5:X6QP7P3O2P>P8P7P3CY/0^11W^PGP>P8P7CY53^PLPGP>P8CY9=dR?A\3PYA6f]d/T3b0W1W2Xd:XYQXc:XXQP>P8P7P3O4n0110800083010210=10<2010210130102101108211091072010310430103109107201021014010510:10610;P7P3O2W1W2P7P3O2n2001000000121000000W0XM6P7P3O2n2001000000121100000b=b0W=WIX_:Xb:WaWNWHo"). Qed.

  Lemma sideT_block : forall A vm M buf cap owned E log,
    sideT A vm M buf cap owned -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    sideT A vm (mem_denot E M log) buf cap owned
    /\ forall x : word, ~ O23ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRunL ()) ["TRunL"] "h01xh11qh21Hh31Ah41Eh53HE0h62HWh73HW'h83Hlnh93Hloh:4Hlogh;1Mh<3OUTh=1ah>3bufh?3caph@3loghA5ownedhB2vmp;3p;2p;1p;;p;4p;Hg01FKj3LTg01GTj3KTg01H]j2FTg003oj16Tg004Tj1?Tg0052j1>Tg005Uj1=Tg0067j1ETg01I^l;7Tg014Yj1BTg0092j2ATg00H6j2@Tg00NEj1JTg009NR0j24Tg01JTj28Tg00;Sj30Tg01KYj33j45Tg01Lkj2GTg01Mfj1:Tg01N?j1DTg01O;lHCTg01P7j4<Tg01PRj4HTg01QUj3ITf5R1f4R2f3R3f2R4f1R5CHf0R630p=2A0456#:p=1g00ceR7g01R\;I6p=;g00beg00cE706p=9p,2ALR8p,2CLR9p,3ASRR:9L895K8R;'Fg01SXg00b@#6#6#6R<#6#6#6#?#>R=%?<#>#=R<[g00Y@R>g01@Pg01TO#Ep,5sideTR?f7R@f6RAP1P2P3P4O6P0P8P9P:p,3sp0R3p,4mem0RBp,3limRCf8RDP@PAP1P2M;7Tp/C59OSSVerify5KrLib3O237O23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limf8f7f6f5f4O<g00Xbp,4data#BRE'ARF%=>RGP8P;f9RHP21@>EREE2[A1=6AA1=4A\FPGP8P;f;RIP4%J>R>E2[[^1='4%;4#91827=0=3P?PIf:RJA31H2PDP@PAO61G36#:R2%D5#:R1PDf<RKP@P4C5PKP4O150<[[^0='4[[P6P8P9P:P3PBPCPJPHPDP@PAM;7Tp/C59OSSVerify5KrLib3O237O23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limf:f9f8f7f6O<PGP8P;PKP@PEE2\FA1=6HA1=4H\FPGP8P;f>RLP4P>E2[[^1='4P0PGP8P;f=RMPDPEE2\FA1=6JA1=4J\FPGP8P;f?RNP4P>E2[[^1=%;A#918D7=0=3P?PNPLA3HMDPKPIPJO6PKf@RAPIP4C5PAP4O150<\1\2^0='4[[P6PGP8P;PNPJPEE2\FA1=6MA1=4M\FPGP8P;fBRJP4P>E2[[^1=%;H#918I7=0=3p,3AMBP8P9P:P3p,3tidPBp,3fs0p,6stdin0PCp,4Hvspp,4Htidp,7AL_globp,8AL_grantPJfAR7PAPNPLPKPIP@P5P6MHCP8P9P:P3PBPCPJP7A3KAIPNPLM;7Tp/C59OSSVerify5KrLib3O237O23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limfBfAp/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotf<f@f;O3f?f>O<PNfCRIPLP4C5PIP4O150<\1\2^0='4P0P8P9P:P3PBPCPIPJA3M7KPAPNM;7Tp/C59OSSVerify5KrLib3O237O23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limfCfBp/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotf=fAf<O3f@f?O<PAfDRKPNP4C5PKP4O150<\1\2^0=P?PKPIA3LJMP7PAPNO6P7fERMPAP4C5PMP4O150<\1\2^0='4P6P8P9P:P3PBPCPMPKA3NILPJP7M;7Tp/C59OSSVerify5KrLib3O237O23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limfEfDp/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotf?fCf>O3fBfAO<PIfGRNPJP4C5PNP4O150<\1\2^0=P?PNfFR?A37MAR7PKPIPJO6PKfHRJPIP4C5PJP4O150<\1\2^0=P8P9P:P3PBPCPNP?P7PKPIM;7Tp/C59OSSVerify5KrLib3O237O23TRun5sideWp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,4mem0p,3limfGfFp/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotfAfEf@O3fDfCO<PGP8P;PJPIPEE2\FREA1=6MA1=4M\FPGP8P;fJP4P>E2[[^1=R>'4P5PEP>PDP@C<C<P6C<W<W7P5P6O2n2001000000121000000b=W5W:W8W9P5P6O2n2001000000121000000W2W6P5P6O2n2001000000121000000W2W@W4XA=W?X>=W;WBW3o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_O23TRunL ()) ["TRunL"] "p'0h04__x1h14HLv0h27__arithh36__sat3h46__sat4h56__sat5h64cstrh75heq_Lh89heq_callsh97heq_cfgh::heq_paylenh;4__ffh<4__p1h=8__varmaph>5__with?4__x2h@4__p2hA1rhB2HahC1bhD2HghE4Hlt'hF1ahG1HhH3HnthI2HxhJ2H0hK2HehL2HlhM6__sat6hN6__sat7hO4__x3hP1xhQ1AhR2H1hS2H2hT2HIhU2HKhV3HLvhW2HMhX3HfrhY3Hg1hZ3Hg2h[3Hgrh\2Hhh]3Hhih^3Hihh_3Hloh`3Hltha2Hshb4Htophc1Mhd2M'he2P0hf2R'hg6__sat8hh6__sat9hi2knhj1mhk1nhl1ohm1si001shn4valsho2vmhp1zi011gi021lp%0p%1p&0p;3p;2p;1p;4p;5p;6p;8p;Ap;<p;7g01FKk30vTg01GTk30uTg01H]k20YTg003oj12Tg004Tj1lTg0052k10DTg0067k100Tg005Uk10UTg00BPj1=Tg001lk20NTg00JTj1qTg0082j2:Tg01UZR0k20HTg00;Sj35Tg01V4k20bTg00dDk40ETg01W;k50\Tg01X>j1bTg018Bj24Tg012hj1@Tg00:\j2ATg01Y6j2ITg01Mfj19Tg01Z9k20?Tg01[:k20=Tg00F7j2>Tg00NEk10:Tg01\>k10KTg0092R1j23Tg00Q0R2j21Tg01]@j1wTg01^Hj3vTg00K3k10hTg013Fk205Tg013ck10aTg014Yk10_Tg015Pk10^Tg016Dk10]Tg008RR3j1<Tg00>Aj1OTg0176k203Tg017^k302Tg018lk20[Tg019]k20ZTg00?Hk10BTg00?hk201Tg00@dk10XTg00ABk10WTg00Amj2jTg01^ek30ATg00CXk20VTg00;9j2`Tg00D:k20TTg00Dfk30STg00EEk40RTg000`k60@Tg01_HR4j2~Tg00Mbk20>Tg00Ngj4|Tg01_`j4{Tg01JTk20<Tg00MDk10QTg01`mk20PTg01aPk10;Tg009NS00j26Tg01amk60MTg01c2k20LTg00g;j3;Tg00gRj2YTg00:@j6cTg01cRk20JTg01d9j2pTg01dUS01k20ITg00V2j3iTg00S4S02j2mTg01e5j3JTg01eOj3MTg01P7j4RTg01eij4xTg00SNj4eTg00C5k308Tg00L[j2tTg00T]k307Tg00UFk20sTg00jXk20GTg01fCk50qTg01gEk30pTg01hAk10oTg01iHk80kTg01jTmA0jTg01k^k10iTg01l\k20gTg00Iom<0FTg00=Zk40fTg00T9j7nTg00W6k704Tg00X>k806Tg00PMk30eTg01m`k30dTg01n=k30lTg01nZk40cTg00@Fk40mTg00VRk60nTg00WZk70`Tg01o:k60rTf0R5#2#2p=Gg00ceR6-0g5p=U%25#2#2#2p=af2R7f1R8/35'6p=]f3R9/171385'6p=0%25#=p=CA5785#9p=H1m85,m7p=[%=5#=#=#=p=f%25#2#2#2#2#2#2#2p=_%25#2#2#@p=L%=5#2#2#2p=Z%=5#2p=?%=5#=p=u1178/65p=Eg00Y@R:/`5p=Bg00Y^S03P:P0P3P2g01o^f5R2f4R0P9P7P8P5N<0Fp=T20H09P7P8P5H0fp=Xg00XbR;/15p=713;5p=V%25#@p>0C20>:5p=8P7g00[DR<g00[cR=P=g00\CR>P:P8g00a2R?P5Ceg00]JR@Fnp=FP0P<P=P=P>P9P<P=P=P>P:P7P?P8CeP@FnP5K04p=Qf6RAP<P=P=P>P2P0P9P<P=P=P>P7P8P5L06L06p=KQ03P:P4P3P1g020@P6P;P9P7P8P5N<0Fp=}P7P<P=P=P>P:P8g00aYR1P5CeP@Fnp=DP9P<P=P=P>P7P8P5L06p=NB0e:85p=^g020bR3,A5p=dP:P8P?P5Cep>0OP9P<P=P=P>P7P8P<P=P=P>P5P@FnK04p=zB0d::5p=hB0l::5p=k11971385'6,60p=S1678/m5p=\%b5,38p=gP:P:P8P5H0cp=rP:P7P8P5H0mp=PP8P<P=P=P>P5J0np=oP7P<P=P=P>P8P5K04p=WP7P<P=P=P>P8P5K0`p=sP8P<P=P=P>P5J0rp=yP:P8P1P5Cep>09P8P<P=P=P>P5P@Fnp>0tp,2ALR@p,2CLR<p,3ASR:0v@<60u@R<+0Yg00b@R1#2S04#2S05#2R?#2R4#GRB#lRC$0DRD$00%l?$0DRE$0URF\DS06Q06g01SXQ04#=S07#l00NDg01>i$00%q6RG1:D2+0H%UAp,3sp0S0855Dg00beRHf7RI,:D00b7g00cERJ35g01AXS09p,3ENVRKf8RLO1PIP9H0EP@P<f:R<PLPAI0\%bIQ08,4CRM%GB#aRB#GRN#GRO#2#G#aRP#@RQ'ARR55:1I@514C5RSf9S0:#b3]#920?@8#920=@7#9g021cRT14C9RUPU%@?S0;,>TC0S0<#9S0=%=1RT#C#aRV#@S0>,AMS0?g022g'AS0@14C0RWPWQ0?C0#9f?S0AP2O1f@RXP2O155F[[[[[^FDf<RYP5O1&0:ERE5HF14C8RZ&0K@R['31I@8f;R\#b7]ZPYP8O1=HFE3[[^FDp,4SPloS0B%=TS0C#=#f#f#f#a#_#_#_#LS0D/1Mp,4SPhiS0E%2P#a#_#_#LRP,1Mp,5AL_hi%21#Z#?#?#_#LRT,1[Q09PK%wYS0F9vDXR]O1S0GQ0Af>R^g023gR_&0hVRV%@NS0H'ARNPVg024bR`%??#C#?#_#LS0IPD%UXS0JQ04#@R?Q07#2#GRa#@Rb+05RcQ07#=Rd#uRe#@Rf-05?Rg,1S7ESXCDRhPDQ08Php,4dataRh$0aRi#Bp,5calls=5:iRieRjPi&0_hRk#Bp,6paylen=5:kRkeRlPk&0^hRm#Bp,3cfg=5:mRmeRnPm&0]hRh#Bp,1L=5:hRheRoPhPGfDS0K,:DRp%@1Rq%<pRr'1RsPGPq%BqS0LPpPr%BrS0METP^DXRtPsfES0N,:DRu#ORv%<u#7Ru203?f%V?Rw%7f%Vg[[%7?Rxg01EoRyB02?f8UWB%7g\y^Bx203?bS0O%7b%Vc[\wS0PB02?b8VyXBxS0Q%7c\y^BxS0R&0CdRd-03?Rb%7d205?dRf#V[\wRwB02?d8VyXBxRd%7f\y^BxRx%@4R4-0[MRy%7M%7420ZM4#7[[R4g00_ZS0S$0BRfQ0S$00Rz201:8R{&0X:R|&0W:R}1j:1R~%8P5F}&0:=R=P}Q0D#8S0T=F}~P=P}P}%8?R?%la60A:RaP~%le:0A:?9F}~DQFK20V}>R>P5P71`HJ20T57=5HJdB0S:;8H0RRJb;b=b>X0:115PQ0D/18117g9Ec7[[^0:P5PMQ0EQ0BO3b2b3b4b5bMbNbgbhb6b1b7b9b:b8Q0JQ0:J0@%U]PXQ0FP6PjPiPlPkPnPmPoPh1~6p%Vr1`:;S0JPpPrQ0MC}PtPsPvPuPbPwPdPxPyP4PfPzP{P|P}%8q=F}~P=20>:;Rr=D}~CNP>PJb;b=b>X0:S0M11q5%V8[^0:S0EP5fJS0U,:DS0V#<S0WP2O2b2b3b4b5b6b1C|b7b9b:b8C{J0@Q0G00<6,4CRp11pg5EcePjPiPlPkPnPmPoPhPtPsPvPuQ0OQ0PQ0QQ0RPbPwPdPxPyP4PfPz&0Q:RpP|P}P}Pr%8TS0RQ0R%8QS0Q,^a5D}DQP>PJb;b=b>%7T1AcQ7]TP5b2b3b4b5bMbNb6b1b7b9b:b8P;P`P`%dcC0ePjPiPlPkPnPmPoPhPtPsPvPuPbPwPdPxPyP4PfPzPpP|P}P}P}Q0Q-0P:%8VS0PQ0H#8S0O'^S0XQ0XQ0P5F}DQP}Q0P00OrCzP>PJb;b=b>&0;Q11NVRr7EN11V;R;'6P5b2b3b4b5b6b1b7b9b:b8&0;3?ENr/6;ePKfAS0Yf=S0Z#w5vDO1S0[P_PNPVP`PSJ0M#9PDfBRK%w^R;5vD#U14C7Rr/3`20L::R3A;35_R_%h5S0\PUPU%k5S0]DSXA3'Y'6Ru11`rRv%dSS0^7]r1>SNRsPrPr1>SVRtC03[#9XCDP5%UKRcPKP;P6PjPiPlPkPnPmPoPhfFS0_,:DR;,~6%<;Ra#VQ0JP;Pa%BaRgC}PGP;11qaR]PGPqQ0LP;PaPgETPXDXP]fGS0`,:DS0a#OQ0a#<R]#7PbPwPdPxPyP4Q0MQ0EP5fLS0b,:DS0c#<S0dP2O2b2b3b4b5b6b1C|b7b9b:b8C{Ec13Z`P_Q0\PrPrQ0]DSXA3,Y311`Z14CcRc#d,3Z1>cNPZPZ1>cVC03\3\#9PDfCRc#US0e13U`P_Q0\PWPWQ0]DSXA3,Y311`UQ0^,3UPsPUPUPtC03\3\#9XCDP5Q08PYEc%dMS0f9]vr1>MNS0gPrPr1>MVS0hC05[u#9PLP91I@9Q0Y#b7]US0iQ001I@0S0j1gWKS0kg01ERRuP51I@AS0l14CIQ0N'gS0mp,8AL_grantPLP8O2%@BRB14CLS0n%@OROQ0nQ0nPTC0#93EQ00Q0:,4CS0o,1BPOQ0oQ0oPTC0#9PuP514C\,1BPO14CYS0pQ0pPTC0#9P:fKS0q#bS0r14C^RY/35Xp:S0sP2PRPcEcQ0Z,4C/3RS0t20JYO13YO1pYO+0IQ01Q0A,4CRv/3O1pvOPuP514CXS01/3OP^Q0Y,4CRt/3TS0u%21#G#?#C#?#f#Z#LRs%21#G#?#C#?#f#?#C#LS0v'rR_%21#Z#Z#a#C#G#LRg%21#Z#Z#C#u#?#?#LS0w'rRa%21#C#G#C#u#Z#f#?$0CR;%21#C#G#C#u#?#C#a#LS0x'rR11rBORP&0B3S0y5i3S0z5i3S0{5i3RH5i3R?9;35S0|Q0\14CKRePeQ0]DSXA3S0},Y3Re'6S0~PTPtPtPRC0S10Q0gPtPtQ0hC0S11'mS12Q0uPePjPiPlPkPnPmPoPhPGfV,:DS0uQ0u#<Re,1qS13PGPqQ0LQ0uPe%BeETfPDXS0uQ13fW,:DRe#OS14%<e#7S15PbPwPdPxPyP4p-0RePfPz201:7S16?P7p9Pp8S17P|P}Q07,j:Q0Q'^9D}~S07P=P}1o}0S18Q0R=F}~S19Q075W}1o}2S1:5s}5s},y}S1;P=Q0R9D}~S1<FKP>PJb;b=b>X0:X?:X<eW@1A8QS1=,35PTP8P81A7QS1>C0=[90Pu[137T[[^0:^?:^<e^@eP5Q0gQ0q,4CS1?Q1?Q0hC0S1@Q1?/3TQ0|Q0\Q0b,4CS1AQ1AQ0]DSXA3,Y3'6S1APMQ1?Q0ZfHS1BO6b2b3b4b5b6b1b7b9b:b8P3Q0}PPA;3P?%hPPtPt%kPC0S0}A53_PA;3PHA53aPQ0{9;3PA531PQ0z9;3PA53PPQ0y9;3P1`3P3J3M3M3MPjPiPlPkPnPmPoPhQ0uQ13Q14Q15PbPwPdPxPyP4PfPzQ17P|P}P}P}%8ORPP~Q1<DQ,y}S17P=P}%8B=F}~S0yP=P}Q07P=P}Q1;P=P}Q0yP}209~PCzFKFKP>PJb;b=b>X0:X?:X<eX@ePOP5P5PTC0Pu[11B81A9Q,37S0yPTP9P91A0QC0S1;=[2APu[PBP0P0POC0[[[[^0:^?:^<e^@eP5Q1@Q1APMQ1?P^Q0AQ0ZQ1BO8b2b3b4b5b6b1b7b9b:b8Q0}eCRCxCR3JO1WLP5O1Q01/pOP^Q0~Q12Q10Q11PjPiPlPkPnPmPoPhQ0uQ13Q14Q15PbPwPdPxPyP4PfPzQ16?P8pS15P|P}P:P~g025_PPCe-0t}P=P}Q17P=P}Q04,j:RPQ0Q'^9D}~RBP=Q19=W}BCNFKP>PJb;b=b>X0:X?:1p5O138TS199EO8Pu[Q0yQ1;[[[^0:^?:P5PMQ1?P<P^Q0ZO5b2b3b4b5b6b1b7b9b:b83J3MO1WLP5O1n200110000021110211101bmbEWZWYP8P5O2n2001000000121000000bFWEWDP8P5O2n2001000000121000000WGQ0i#9e20?@9S0ip,7AL_globP0P5O2PgPWPWQ0wC0P714C2RO/3TS12Q0|Q0\14CARBPBQ0]DSXA3S0~,Y3S11'6S1011TO13ORQ0gPOPOQ0hC03\S1?Q12Q11PjPiPlPkPnPmPoPhPGQ0VQ0W,1qS0yPGPqQ0LQ0VQ0WQ0W#BETQ0KDXS1;Q0yQ0q,:DS0q#OS04Q0q#<#7S0qPbPwPdPxPyP4PfPzP{P|P}1o}9S17Q0w#89D}~S145W}P=Q1<CNP>PJb;b=b>X0:X<eQ0w,35S13,68Q19[^0:^<eP511gvPvP<O3b2b3b4b5b6b1b7b9b:b8P3Q0~PaA;3a?%haPOPO%kaC0S0uA53_aA;3aHA53aaQ0{9;3a1`3a3J3MPjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}P}P}%8gP~Q14DQS14P=Q14CNP>PJb;b=b>X0:Q139Eg5PgP8P8Q0wC0[^0:P5PvP<O2S0wb2b3b4b5b6b1b7b9b:b8Q0ueCRCxCR3JO1bDWDQ0i#9e20=@9S0ip,8AL_errnoP0P5O2P;PWPWQ0xC0P7Q10Q1?Q12Q11PjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}Q17Q0x#89D}~S115W}P=Q1<CNP>PJb;b=b>X0:X<eQ0x,35Rg,68Q19[^0:^<eP511;vPvP<O3b2b3b4b5b6b1b7b9b:b8P3Q0~P1A;31?%h1POPO%k1C0S0~A53_1A;31HA53a1Q0{9;31A5311Q0z9;311`313J3M3MPjPiPlPkPnPmPoPhQ1;Q0yQ04Q0qPbPwPdPxPyP4PfPzP{P|P}P}P}%8;P~Q11DQR1P=P1CNP>PJb;b=b>X0:AE;5gP;P8P8Q0xC0[^0:Q0wb2b3b4b5b6b1b7b9b:b8Q0~eCRCxCR3JO1bKWKQ0i#9eQ0<P813WTR;Q0|Q0\POPOQ0]DSXA3S0i,Y3Rg'6S1?PTPWPWPRC0S10Q0gPWPWQ0hC0S0h'mS0gP;PgPjPiPlPkPnPmPoPhPGfIS0~,:DRg%<gR;,1qR1PGPqQ0LPgP;%B;ETPcDXS0wP1Q0V#OS0VQ0W#7S0WPbPwPdPxPyP4PfPzP{P|P}Q17%8sR;Q0;#8608:9D}~Rg5W}P=Q1<CNP>PJb;b=b>X0:X<eQ0;,>s,35Ra,68Q19[^0:^<eP511sYPYP<O3b2b3b4b5b6b1b7b9b:b8P3Q0iP_A;3_?%h_PWPW%k_C0R?A53__A;3_H1`3_3JPjPiPlPkPnPmPoPhQ0wP1Q0VQ0WPbPwPdPxPyP4PfPzP{P|P}AF};~R;=W}gP=P}P;P}Q0v#8-09~CzCNP>PJb;b=b>X0:AEs5aPsP8P8Q0vC0[^0:P5PYP<O2b2b3b4b5b6b1b7b9b:b8P?eCRCxCR3JO1W\Q0=eQ0@PUPUQ0?C0R?P8Q1?Q0gQ10Q0hPjPiPlPkPnPmPoPhQ0wP1Q0VQ0WPbPwPdPxPyP4PfPzQ15P|P}P}P}Q0>#8,^~R1Q0O'^PPAD}P1DQP=P}Q18Q1:P}P}Q0X:08:~PPQ0P:08:~9D}PDQR~5s}5s},y}P=P~FKP>PJb;b=b>X0:X?:X<eX@eQ0>,A5R~Q0H'AP8P8P~C01>8NP7P71>8VC09[90Pu[1>7NP9P91>7VC0[[^0:^?:^<e^@eP5PTPYPYPRC013YTQ0|Q0\PvPvQ0]DSXA3,Y3'6PYPMP<P\O6b2b3b4b5b6b1b7b9b:b83M3MO1Wa%9?eO6bHbHWHXPDQ0[00<6,4CR?#dPSPSP?C0Q0YP8O1=HFEPDQ0A#wR?9vDc#UQ0^PUPUPSC0XCDP8Q0ePcP?P6PjPiPlPkPnPmPoPhQ0a,~6%V]Q0JQ0aP]%B]R?C}PGQ0a11q]RYPGPqQ0LQ0aP]P?ETQ0YDXPYQ1B,:DRY#O%<Y#7PbPwPdPxPyP4Q0MQ0EP5fMRY,:DR?#<R]P2O2b2b3b4b5b6b1C|b7b9b:b8C{EcQ0e,4CR3#dPrPrP3C0PDQ0K#UQ0^PWPWPSC0XCDP5Q08Q0ZEcQ0fPUPUPMC0PLP0P7O213W[Q0jQ0k'6PcP0O1=HFE3[Q0213O[1I@21gOcQ0KP2O1=HFE3\Q0NPAO1=HFEROP513B[Q0_PIO1=HFERWPjPiPlPkPnPmPoPhPGQ0cQ0d,1qRUPGPqQ0LQ0cQ0dQ0d#BETQ0_DXPU%O?%7]PbPwPdPxPyP4Q0S%qGR]#qR?#q,t:1t:?1t:]1t:6607:607:607:g00`F+0s;ifPzQ15201:99Pp97P9P|P}Q0C,j:R6=D}PP=P}Q05,j:R]Q0Q'^R?=F}6RUQ1:5W}P=P}Q0R9F}PP=P}Q0T=F}]R]P=P}P]P=1o}ACNFKFKP>PJb;b=b>X0:X?:XO:X<eX@e1375Q1>?E90117TQ0D/10Q0D/12Q0:[[[[[^0:^?:^O:^<e^@eP5Pu13tMPtPMP[P<Q0ZPKQ0KQ0BO:b2b3b4b5b6b1b7b9b:b8+0GWGP5O1Q0lQ0K,gB;\OQ021I@IQ0m'6PWQ0`PLO1=HFERWP51I@LQ0nQ0_#b3]Q00Q0:,I@Q0oQ0`'gQ0~P<O1=HFEP51I@\Q0pQ0U'gQ0bQ0ZO1=HFEP:Q0rQ0sP5PRPcEcQ0tPjPiPlPkPnPmPoPhPGfS,:DRh%<hRo,1qRmPGPqQ0LPhPo%BoETPYDXPmfT,:DRm#O%<m#7PbPwPdPxPyP4PfPzAP{7pQ169Pp77P7P|P}AD}6?P=P}Q189W}UP=Q1:FKP>PJb;b=b>X0:X?:X<eX@e1A5Q,38Q1=?E79P2[[^0:^?:^<e^@eP5PuQ1B,4CRC/3MPCPMP<Q0KO6b2b3b4b5b6b1b7b9b:b8bE+0GWEWDP8P5O2n2001000000121000000WJP5O1P5XGWP5O1n200100000021100010000WJP5O1n200100000021100011000blbIbIWWWIXPDQ06Q03Q0I/1Z%<8,>r/1`P0P9P7P8P5I0qWSWRWkXFDWjP\Q09PXQ0Fp,3AMBp,3a0sp,4path40p$0oQ0AP\PLPIL0kNA0jQ09Q0GP^&0i\H0Eeb^b]b_W[WXWbWTWUW`WeWVWiWfWoWdWcWnWQo"). Qed.

  Lemma env_ok_fcall : forall A M M' vm,
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a : word, ~ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) -> ~ al_globals a -> ~ al_errno_slot a ->
                      ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8)%Z ->
                      ~ (bv_unsigned sp0 - 208 - LEPT_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRunL ()) ["TRunL"] "h04__x1h14__p1h21ah34__p2h44__x2h57__arithh64__ffh76__sat3h86__sat4h96__sat5h:8__varmaph;5__with<5heq_Lh=9heq_callsh>7heq_cfgh?:heq_paylenh@4__p3hA2HahB1HhC2HghD1ohE2HehF3HlthG1AhH2FRhI2H0hJ2H1hK2H2hL3HEahM3HElhN3HErhO2HIhP3HfrhQ3Hg1hR3Hg2hS3HnehT4HtophU1MhV2M'hW2a0hX2vmhY1xhZ1zp%0p&0p;3p;2p;1p;5p;6p;4p;7p;8g01FKk30KTg01GTk30JTg01H]k209Tg003oj10Tg004Tj1yTg0052j1wTg005Uk108Tg026Fj3hTg027Dj3jTg018Bj29Tg00Q0j21Tg0092j22Tg00;Sj34Tg012hj1ETg00BPj13Tg00NEj1xTg009NR0j2:Tg01W;j5oTg01X>j1=Tg00:\j2YTg01Y6j2bTg01Z9j2rTg01Mfj1ZTg01[:k20ITg00F7j2zTg00:@k60HTg013ck10GTg00;9j2aTg014Yk10FTg015Pk10ETg016Dk10DTg0176k20CTg013Fk20BTg017^k30ATg018lk20@Tg019]k20?Tg00?Hk10>Tg0067k10=Tg00?hj2vTg00MDk10<Tg00@dk10;Tg00ABk10:Tg00Amj2`Tg00PMj3iTg00CXk207Tg00D:k206Tg00Dfk305Tg00EEk404Tg00JTj1[Tg00L[j2STg00UFj2cTg00C5k303Tg000`j6mTg00S4j2]Tg01P7j4sTg00@Fk401Tg00Mbk200Tg00SNj4RTg00T9j7WTg00W6j7_Tg01o:j6~Tg00WZj7eTg00VRj6}Tg00X>j8qTg00T]j3|Tg00V2j3{Tf0R1#0#0p=H%01#3p=P%01#0#0#3p=O%31#3p=I%31#0#0#0p=Q%31#0p=6%01#0#0#Ep=7%31#3#3#0p=M%31#3#3#3p=^%01#0#0#0p=\%01#3#0#0p=lf3R2f2R3'1f1R4/21':p=81:34/]1p=>%01#Ep=u11231241':#Zp=F%01#0#0#0#0#0#0#0p=Vg00Y@R5?441p=J1241,:3#Zp=g1241,:3p=;1]41,]3p=G1134/:1p=pg00XbR6/11p=XP5P3P4P1H01p=?20051p=5P3g00[DR7g00[cR8P8g00\CR9P5P4g00a2R:P1CRg00]JR;FWp=<P5P4g00aYR<P1CRp=kP2P7P8P8P9P3P4P7P8P8P9P1P;FWF_p=fP4P7P8P8P9P1E~p=BP3P7P8P8P9P5P4P<P1CRP;FWp=Df6R=P7P8P8P9f5R>P7P8P8P9P5f4R?P:P2CRP;FWP3P7P8P8P9P5P4P<P1CRP;FWF_p=CP3P7P8P8P9P4P1F_p=NP?P7P8P8P9P2P7P8P8P9P3P4F_P1Fep=UP?P7P8P8P9P2P3P7P8P8P9P4P1FeFep=KP4P7P8P8P9P1E}p=dP=P7P8P8P9P>P?P2P7P8P8P9P3P4P1GqGqp=@A|541p=Lg00_ZR<?{41p=TP2P7P8P8P9P3P4P1Gqp=AP?P7P8P8P9P2P7P8P8P9P5P3P:P4CRP;FWP1F_p=tP3P7P8P8P9P4P1Fep=n1:41,]3p>02p,2ALR7p,2CLR;p,3ASR:0K7;60J7R;+09g00b@R:#0R@#0RA#0RB#0RC#HRD#yRE#wRF%yB#wRG$08RH[PH^YFg01SXp,3sp0RIp,4mem0RJ;h3P0AjIJ2%0:#P#O#I#Q#6#6#7RK19E1RL'1%0:#6#O#M#6#I#P#7RM,2L%0:#6#O#I#^#O#7RNPLPL%0:#Q#Q#\#l#7ROC83>RP%0:#P#O#I#Q#I#M#uRQ19E4RRPR%0:#P#O#M#P#\#7RRCFRSP=P3O1PJP3O1RT54H[[^2F%HD#\RD#HS00#HRU#ERV/1LRW%3C#M#V#7S01,2L%0:#H#6#l#M#6#I#7RXPLPL%0:#H#6#l#M#I#H#7RYC83>RZP>P4O1%xGRG54H[^2F':P7P;P>P?P3Do%=219EIR[%\U#7RU'YR\'J1b71R]%=>7gL1r74#ZR^20I73S02#ZR_g021cS0319E2R`P`Q03%EBRa'zS04CFRb%3:Rc#0#6#7Rd,Y[S05g022g'YS0619E?RePeQ05CFRef;RfP>O1f<RgP>O154H[[[[[^2FAhIJ=[[[P1AjIJ>f9RhP3O1=4HT\S\P^2Ff8RiP4O1=4HG\Z^2F':P0f:RjP3O1=4HT\S\P^2FPhP4O1=4HG\Z^2FP7P;PhPiP=Dof7Rk#=/J\%=h9g]Lf?S07P>O1f@RlP>O154H\e\b\_\^[^2FAhIJj[[[P1PgP3O1=4HT\S\P^2FPgP4O1=4HG\Z^2FP7P;PgPfPhDo%=j/J\%=g9g]LfBS08P>O1fCS09P>O154H\e\b\_\^[^2Fp,4SPloR^%3cRc#3#^#^#^#\#V#V#V#7Rb/1[11[LS0:%6B#P#6#V#7RB9;WL;GPS0;P?P31b7319E3RW%=l3;S0<P01b72fAS0=#=,2`g01ERRlP11b7>19E=fDS0>#='2p,8AL_grantPkP4O2%EDRD19EkRLPVPLPL%0:#Q#6#6#V#7RLCF3pP019EiR0,1DPVP0P0PLCFPlP119EjR0,1DPV19EfRDPDPLCFP5fJ#=f=S0?,9E/21XZ5P>P\Q07J0H19EgRD/2\p,4dataR\$0GRe,a5p,5calls/JeReeR]Pe&0F\R;,a5p,6paylen/J;R;eRmP;&0E\Rn,a5p,3cfg/JnRneRoPn&0D\R\,a5p,1L/J\R\eRpP\%E@Rq%3@S0@#3#uRr+0CRs126q%Xr20BqrRt,26[[Ru%XqRvg01EoRwB0Aqr4UWARr%Xt\w^AvRv%ECRC-0@[Rw%X[%XC20?[C#X[[RCp-0Rt&0><Rq&0=<R<1v54Rx&0<5Ry7?31v53Rz9?y37?3S0A&0;5R{&0:5R|P|%5VS0B1`5cRc5<|R}P|%5L,kcCf,B|%x8R8P|1`5ARA%5U5i59D|cP8P|P|P|%5QS0CPcP|Pc%5RS0DFCS0E,B|S0FP8P|P|A<|AcS0GP|%5BR~9D|cS0H9N|}P|P|%5KS0I=<|c%5MS0J9D|cS0KP|P|%5NS0LPcP|Pc%5OS0MFCS0NDUDKP81d|?R}F@F@207|9R9P1P3g00beS0Og00cES0P'aQ0O20613Q0P34dB05564H04R6b6b:b;X05X45W111V4S0P?;4LPl[1Y4U,23122RS0O9pQ2Pl[112?PVP?P?PBC811K?12?MPNP?P?POC83>3GP=[[[[^05^45^1tP1PlfE,9EP[PhPiQ09Q0>O7b5b7b8b9b<b>b?b=bFWRWQP4P1O2n2001000000121000000bWWFWCP4P1O2n2001000000121000000WIQ0<#Ze1r73S0<p,7AL_globP2P1O2POP`P`%0:#Q#6#O#M#6#7R7C8P]PePmP;PoPnPpP\PsPuPrPvPwPCg00ceRU#[S0>#[RL#[S0Q#[S0R,S5S0S1S5LS0T1S5US0U'L'Lg00`FRU'c/TqS0VP<Q0AP{P|P|P|Q0MPcP|Pc%57FCP8P|Q0FP8P|P|Q0GP|Q0H9N|}P|P|1d|>RcQ0KQ0NDUDKP8P|%5bRL=<|ARAP8P|PAP81d|=R=CAF@F@P9P6b6b:b;X05X45X1tX3tX@tPOP4P4P7C8PQP3P3PRC8Pl[1132A;?2B122MPNP2P2POC85>>3G11b2R711b?Ph[[[[[^05^45^1t^3t^@tP1Pl11KD11VDPDP[PiPjPfQ0?P^O:b5b7b8b9b<b>b?b=bCWCQ0<#ZeQ02p,8AL_errnoP2P1O2PQP`P`PRC8P]PePmP;PoPnPpP\PsPuPrPvPwPCPqP<A?y4x9?y4P{P|Q0EP8P|Q0FP81d|2R`F@P9P6b6b:b;X05X1tPQP1P1PRC8S0F11Q4S0E?;4RPl[RAP2[[^05^1tP1PlPDPiPjO4b5b7b8b9b<b>b?b=bEWEP_eP]PePmP;PoPnPpP\PsPuPrPvPwPCQ0VP<A?z3y9?y4S0VP{P|P|Q0@,`5R_1`5:Rj5<|S0@P|P|P}P|1kj~CfP|P|Q0I=<|jPcP|P|Q0LPjP=DtDUDKP8P|A<|L_R_P8P|P_P8P|P|%0:#H#6#P#6#^#Q#7R:#5R=PjP|Pj%5a:035=FC,B|CAF@P9P6b6b:b;X05X45X1tX3tX@t1141S02A;31B11K1S0<11N1S0?/:?7>23G11b3RbP:P2P21z:aC8Pl[\7[[^05^45^1t^3t^@tP1120O120M11V0R:P[P0PhPfP^O8b5b7b8b9b<b>b?b=Q03PWPWQ04CFeP]PePmP;PoPnPpP\PsPuPrPvPwPCQ0SQ0TQ0>,S5Ra'LR='L/cURDQ0R#[,S5/L=/cU/Tq,TD,TD'TP<A?z4yS0RP{P|P|P|Q0C1`5@R@P|P@Q0DFC,B|P8P|P|A<|j@RzP|AD|@~S0S9N|}P|P|PcQ0J9D|@S0JP|P|Q0LP@P|P@Q0MFCR~DUDKP8P|A<|LjRLP8P|PLP8P|P|%5d9i5jRLQ00#ERD#55i5P@P|P@PLFC,B|F@F@P9P6b6b:b;X05X45X1tX3t1143RLA;23B123MR=PNP3P3POC85>?3G1Y?dRd/YDP>P>PdC8Pl[\7\b[\A^05^45^1t^3tP111K0P:P0P[PiPhPfP^O8b5b7b8b9b<b>b?b=Q06PWPWQ05CFeO6XSSWAX2FQ0;Q0=P3O1Q08P3O1RW54H\S[^2FQ079jIJS07A4HWT\S\P^2FRIQ0=P4O1Rd=4HG\Z^2FRD':Q0:PHQ08P4O1S08A4H1TXDHPgP4P1O2PdP3P4P]PePmP;PoPnPpP\PsPuPrPvPwPCPqP<Q0RP{P|PzP8P|PzP|P}P|P|Q0IP@Q0JDtRz=n|cDKCAP9P6b6b:b;X05X45X1tX3t111411K3?>=?9GL2[^05^45^1t^3tP1PN19EhREPEPOC8RL11VER=?;EBPEP[PiO5b5b7b8b9b<b>b?b=P]PePmP;PoPnPpP\PsPuPrPvPwPCQ0Q,S5Q0U,La'L/cU/TqP<Q0VP{P|Q0@P8P|P_P8P|P_P8Q0D9D|jR_9N|},B|CAF@P9P6b6b:b;X05X45X1tQ02Q0O,:>Pl[\7\b[^05^45^1tP111QEP[PEPiPfP^O6b5b7b8b9b<b>b?b=O3EmWAX2FQ07ePIPDPHQ09P3O1PJP2O194H1XDHPhP3P4P1O3PWP2P3P]PePmP;PoPnPpP\PsPuPrPvPwPCPqP<A?x4yRyP{P|An|z~R~P8P|P`P|P}P~DKCAP9P6b6b:b;X05X1tX3tQ0<121MQ0??;1O3>PKP4P4PMC8RM11N4124O4029G32[^05^1t^3tP1A;:0B11[0P0PhO4b5b7b8b9b<b>b?b=P]PePmP;PoPnPpP\PsPuPrPvPwPCPqP<PxP{P|Q0C=<|jRh=N|_,B|R_P8P_CAP9P6b6b:b;X05Q0FPl[PA[^05P1P0PiO2b5b7b8b9b<b>b?b=O3EmXKSXJPX2FPHQ08A4H1GXDHPkP4P1O2PdP3P4P]PePmP;PoPnPpP\PsPuPrPvPwPCPqP<PyP{P|P|P|Q0B=<|@RyQ01#5Rd9D|@P|P|%5XP@P|P@%5YR@FCDUP8P|P`P|Q0S9N|yAn|z}DKCAP9P6b6b:b;X05X1tX3t11V1Q01,21RV121YRY9pX13>Q0P?;4B1]M25G3[^05^1t^3tP1PL11[EPEPiO4b5b7b8b9b<b>b?b=P]PePmP;PoPnPpP\PsPuPrPvPwPCPqP<PxP{P|P|P|P`AD|jdP|P}P|1kj@CfDUP8AN|hc,B|CAP9P6b6b:b;X05X1tX3tX@t1:3Y9>4VQ0E/:?Pl[[^05^1t^3t^@tP112ER11XEP=PEPiO5b5b7b8b9b<b>b?b=O3EmXAZX2FCsCsbHbBWPWTWOWNWMP4P1O2n2101000010121000000WBWLP4P1O2n2011000010121000000WBWXWVWUWGo"). Qed.

  Lemma paylen_factsL : (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z ->
    (0 <= paylen < 2 ^ 26)%Z /\ Z.of_nat (length payload) = paylen /\ (0 <= cfg < 32768)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRunL ()) ["TRunL"] "p;1p;2p;5g00BPj12Tg003oj11Tg012hj10Tg00F7j23Tg00Q0j27Tg013Fj26Tg0092j25Tg028>j54Tg00b@R0#2#1R1#0p,3cfg'3p,1LR2'7%10#0%21#1#0'6,52p,3sp0p,4Hvspp,4dataf1f0D4UUo"). Qed.

  (* [comment removed for export] *)
  Definition A_INCB : Z := 0x123a64.   (* [comment removed for export] *)
  Lemma incb_block : forall A vm M buf cap owned aligned E (v : expr),
    (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z -> ev E 0 = sp0 ->
    sideT A vm M buf cap owned -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
    sideT A vm (mem_denot E M [SE (SA (ELit 0) 0x123a64) 1 v]) buf cap owned
    /\ copyP (mem_denot E M [SE (SA (ELit 0) 0x123a64) 1 v]) aligned owned
    /\ bytes_at (mem_denot E M [SE (SA (ELit 0) 0x123a64) 1 v]) (bv_unsigned buf) data
    /\ (forall x : word, bv_unsigned x <> 0x123a64%Z -> mem_denot E M [SE (SA (ELit 0) 0x123a64) 1 v] x = M x).
  Proof.
    intros A vm M buf cap owned aligned E v HLc HL26 HE0 HS HC HB.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
    destruct (paylen_factsL HLc HL26) as (Hpl & Hplen & Hcr).
    assert (OUT : forall x : word, bv_unsigned x <> 0x123a64%Z -> mem_denot E M [SE (SA (ELit 0) 0x123a64) 1 v] x = M x).
    { intros x Hx. pose proof (u64_range x) as Hxr. cbn [mem_denot]. unfold adenot, v_addi. cbn [a_base a_off edenot].
      rewrite ?(u_small 0) by lia. rewrite ?Z.add_0_l.
      rewrite MemSplit.wbytes_outside; [reflexivity | |];
        rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat]; rewrite u_small by lia; lia. }
    destruct (sideT_block A vm M buf cap owned E [SE (SA (ELit 0) 0x123a64) 1 v] HS ltac:(reflexivity) HE0) as [HS' _].
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
        (forall a : word, (0x1443e0 <= bv_unsigned a < 0x145000)%Z -> M' a = M a) ->
        roomT A' vm' (rem - 1) ->
        realizes RSEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x62eb8) M' (seg_rom RSEGS)) (model2 vm')) K) ->
    realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x62fbc) M (seg_rom RSEGS)) (model2 vm)) K.
  Proof.
    intros fxp K A vm vals R M buf cap aligned owned rem kn FRM HL SL HR HK VLK Xe Xs Xp Xm Xg Xw HS HC HB HcapL Hcap26 HLc Hrem1 HRT HKONT.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    destruct (paylen_factsL HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    destruct HC as [HC1 HC0].
    unfold model2, O23ReadLoop.model2.
    assert (R10 : getr R 10 = aligned) by (regv HR (10 : reg); cbn [edenot ev ENV O23Open.ENV]; exact P14).
    assert (R11 : getr R 11 = Z_to_bv 64 paylen) by (regv HR (11 : reg); cbn [edenot ev ENV O23Open.ENV]; rewrite P9; reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x62eb8) by (regv HR (1 : reg); reflexivity).
    assert (R3 : getr R 3 = Z_to_bv 64 0x10800) by (regv HR (3 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x123d20) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV O23Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    assert (KW : forall (d : Z) (m : nat), (-6144513 <= d)%Z -> (d + Z.of_nat m <= -6144513 + 6144513)%Z ->
                 store_ok RSEGS M (adenot (ENV vals) (SA (EVar 0) d)) m = true).
    { apply existsb_exists in Xw as (Kw & Hin & Hc). apply In_nth_error in Hin as [iw Hiw].
      destruct Kw as [| | | | | |[bw kw] nw|]; try discriminate Hc.
      cbn [is_kwr_cov] in Hc. apply andb_prop in Hc as [Hc Hn]. apply andb_prop in Hc as [Hb Hk].
      apply expr_eqb_eq in Hb. apply Z.leb_le in Hk. apply Z.leb_le in Hn. subst bw.
      intros d m Hd Hm. apply (kwr_store_ok RSEGS (ENV vals) M kn iw (EVar 0) kw nw d m HK Hiw); lia. }
    assert (EQcfg : @mkst fxp R (Z_to_bv 64 0x62fbc) M (seg_rom RSEGS) = @mkst fxp R (Z_to_bv 64 PC_FUZZ) M al_rom) by (rewrite AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC O23Open.fds0 vm stdin0 fs0 None (Some tid) None).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (fuzz_margin_bound paylen Hpl) as HFM.
    destruct (fuzz_step FUZZ_CALLS FUZZ_BMAX rem) as (EK & EB).
    destruct (fuzz_nonneg FUZZ_CALLS FUZZ_BMAX (rem - 1) HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hrem1; lia)) as (HK0 & HB0).
    eapply (FZ fxp A M md R aligned paylen payload (Z_to_bv 64 0x62eb8) sp0 [a0s; path] envv K FRM HI).
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
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV O23Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LS16)) in Hw by (cbn; lia). exact Hw.
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
      assert (IMGFR : forall a : word, (0x10f000 <= bv_unsigned a < 0x145000)%Z -> ~ (0x144020 <= bv_unsigned a < 0x1443d0)%Z ->
                       ~ (0x123c7c <= bv_unsigned a < 0x123c80)%Z -> ~ (0x1137c0 <= bv_unsigned a < 0x1137c8)%Z -> m' a = M a).
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
        intros i Hi. unfold O23TRun.L in *. rewrite <- (HB i Hi). pose proof (Hlm buf cap i Hl ltac:(lia)) as Hq. unfold at_ in Hq. exact Hq.
      + intros a Ha. apply IMGFR; lia.
      +
        unfold roomT. apply (aroom_mono A' vm' _ _ _ _ Hroom'); clear -EK EB HK0 HB0 HFM; lia.
  Qed.
End TRunL.
