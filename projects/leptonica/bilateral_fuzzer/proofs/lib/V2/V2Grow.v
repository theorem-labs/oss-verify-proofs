(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy). *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec Room.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2ExitBase V2Startup V2StartupDefs V2StartupFacts V2MainEntry V2LibStdioCall V2OpenFail_defs V2OpenFail_tail2 V2Open_defs V2Open V2Oom_defs V2MemPreds V2Malloc65536 V2DirRead_defs V2MemcpyBase V2Memcpy V2ReadLoop_defs V2ReadLoop V2ReadErr_defs V2ReadErr V2Refused_defs V2Refused V2Grow_defs V2FuzzIface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Grow () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib6Common9CliDriver8SymDrive?nth_map_seq_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib2V2:V2MemPreds8bytes_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Peano2ltC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib2V2=V2Malloc65536<ownedA_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib2V2=V2Malloc65536=kept_al_savedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib6Common9CliDriver8SymDrive?regs_after_callC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs7KEPT_ALC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc65536;kept_al_no0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4ainvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC69OSSVerify5KrLib6Common8Mallocng9AllocBase5ownedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib6Common9CliDriver7SymCall7touchedC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib2V26V2Grow=ownedA_rangeGC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2V2:V2ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall<know_ok_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs4GLOBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs5A_SLOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2Oom_defs5A_SHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2ReadErr_defs3IHIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2V2=V2Malloc655366env_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open9above_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;is_kimg_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsC59OSSVerify5KrLib2V2:V2MemPreds9img_clearC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop5slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V26V2Open3ENVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop4sideC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib2V2;V2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop6modelkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop9buf_factsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop4fdskC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1Z8div_sameC47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_srl64C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib2V2:V2MemPreds>stack_writableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Grow;kimg_clearGC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC69OSSVerify5KrLib6Common9CliDriver6SymRun=ext_val_zx_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2MemPreds4cellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb6a_drawC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2StartupDefsBlength_guard_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2StartupDefs;guard_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_lC59OSSVerify5KrLib2V29V2Refused@ref_refused_tailC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2V2>V2ReadErr_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs6STOPSGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2ReadLoop_defs4sr_FC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2ReadLoop_defs5kn_MLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec;msg_refusedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C59OSSVerify5KrLib2V29V2ReadErr6re_ivsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib2V2:V2ReadLoop5al_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop5vm_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega:ZMicromega;ZArithProof03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9div_smallC59OSSVerify5KrLib2V2?V2OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC59OSSVerify5KrLib2V2:V2ReadLoop8md_mul_ZC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_malloc_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIfaceAfuzz_margin_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface;fuzz_marginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure?alloc_margin_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure<alloc_marginC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_wview_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsc59OSSVerify5KrLib2V26V2Grow<env_ok_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase<ai_live_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7round16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop:round16_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc65536;live_big_loC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=length_firstnC69OSSVerify5KrLib6Common8Mallocng9AllocBase@ai_live_disjointC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop9slots_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2GrowAregs_after_allocGC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC59OSSVerify5KrLib6Common7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2GrowAknow_after_allocGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Grow<bytes_at_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V28V2Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2Malloc65536Aainv_frame_driverC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes?pair_equal_specC59OSSVerify5KrLib6Common:AllocIface:al_free_pcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC56Stdlib6ZArith6BinInt1Z6eq_decC69OSSVerify5KrLib6Common9CliDriver4Room9need_growC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib6Common9CliDriver4Room7need_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:aroom_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:pow_succ_rC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib2V2:V2ReadLoop;vals_ev_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer2rvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4emapC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer<regs_ok_xferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ReadLoop7kwr_bufC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXferDknow_ok_xfer_entailsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb=with_vmmaps_CC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure9ai_free_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure>ai_malloc_sureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Room6need_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib2V2;V2FuzzIface:FUZZ_CALLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2FuzzIface9FUZZ_BMAXC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib2V2;V2Grow_defs5g_sr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs6g_sr1tC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib2V2;V2Grow_defs5g_sr2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_sr3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2ReadLoop_defs4sr_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2ReadErr_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs6g_kn3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C59OSSVerify5KrLib2V2;V2Grow_defs7g_itin1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_r1nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs6cap2_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_r1tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_kn1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_knMC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2V2;V2FuzzIfaceAfuzz_calls_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure9ROOM_NMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2MallocLayout4LU16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2MallocLayout6LU17okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs6g_knOKC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib2V2;V2Grow_defs7g_itin2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs4g_r2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs6g_sr3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs7g_itin3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs4g_r3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_kn3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_knLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Grow_defs5g_srLC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPSG scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSG scr NX true.

(* [comment removed for export] *)
Lemma bytes_at_rdn : forall M (a : Z) (bs : list byte),
  (0 <= a)%Z -> (a + Z.of_nat (length bs) < 2 ^ 64)%Z ->
  bytes_at M a bs -> rdn RSEGS M (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Grow ()) [] "h04__x1h14__x2h27__arithh34__x3h44cstrh54__ffh66__sat1h78__varmaph85__with91zh:3Hj0h;5cstr0h<6__sat2h=2Hah>1oh?1xh@6__sat0hA4__x4hB2H1hC2H2hD2HBhE2HjhF3HnwhG1MhH6__sat3hI6__sat4hJ1ahK2bshL1jhM1yhN2z1hO2z2p&0p;1p;2p;3p;4p;<p;8p;6p;5p;7p10000p4p70g000`R0p4p710R1p8p1001>p4p70P1p8p1001lp4p7210P1p8p1002Xp4p710P1p8p1003fp4p70P1p8g004\j1GTg005Aj1oTg005_j1bTg006Bj1jTg006dj1nTg007Dj2CTg007dR1j13Tg008Dj21Tg008aj1lTg009?j2wTg009\R2j20Tg00:8j3qTg00;3j2;Tg00;Yk30Bj4gTg00<Sj4kTg00=Kj35j1mTg00=eR3j2hTg00>=j2KTg00>gj29Tg00?DR4j1DTg00?dj4Fj3cj2_j1{Tg00@@j2Ek102Tg00@bj2=Tg00A<j2tTg00A_j3sTg00B<l<]Tg00Baj4pTg00CHj1TTg00Cmj2\Tg00DOj22Tg00Djj26Tg00EFj2QTg00E`k20ATg00FHk30@Tg00Flk10?Tg00GJk20>Tg00Gkj1OTg00HJj2ITg00I3j3iTg00I\j2MTg00JHk10=Tg00Jhj2XTg00KFk10<Tg00Kdj4PTg00LBk10;Tg00L`k10:Tg00MKj2fTg00Mnj1eTg00NSj2RTg00O6k104Tg00OXj3UTg00P;k303Tg00P^k201Tg00Q@k200Tg00Qlj3~Tg00RKj4`Tg00S=j4}Tg00Shj8NTP0j6WTg00TEj3|Tg00Thj2VTg00V8j6zTg00W:k605Tg00XCk506Tg00YEj6yTg00Yak207Tg00Z>m<08Tg00Zcj3xTg00[Lk309Tg00[lj4ZTg00\Wj7YTg00];j7vTg00]_j7uTg00^Cj8[Tg00^gR0f0R5'6p=420705p=>g00_ER6f1R7;55p=AP6g00_cR8P6P6P4f4R4P1f3R9g00`Bf2R:P7P5N<08p=^P8P6P3P1P2g00`of5R2P4P9P:P7P5M<]p=r1005p=HA5650p=SAx675p=:g00aQR3@0975p=BP:g00b=R;g00b\R<P<g00c<R=P6P7g00c\P5CZg00dCR>FYp=7P6P7g00dcP5CZp=LP7P;P<P<P=P5P>FYp=JP:P;P<P<P=P7P5Fvp=<P:P;P<P<P=P6P7g00eJP5CZP>FYp=8P:P;P<P<P=P7P5Fup=df6R>P;P<P<P=P2P4P9P;P<P<P=P:P7P5G[G[p=?P6P4P9P:P7P5EWp=@P9P;P<P<P=P:P7P5G[p=ag00f1R;#GR?#G#GR@#G#G#GRA#oRB#b%o@R@#bRC#jRD[%nCRE%47RF1CC7#3,1:%l?RG%lARA'wRH'0Aq49:%jERIg00fVRJ1;B4RK>0B29RLPK1CC9RMCkPJP>1;B21CC4RNCk=5I5X>IPJP2PLPMPK1h5NP>f8RL%3:RI,15,;BROO1PLf7RP,;BRQP>POCg55DX96PDPC%37RO,1>RR,;BRS,KBRT1;B>RU,KBRV'9#DP21;@0R@CF,ECPL11PIRW,;BRXO1RY=5D5X>DPRPC1KBQ,95#DP>P@CF,EC95DYX96P>PC19W5#DP>P@CF,EC95DYX96PDPC%DORYP2P@CFRQ,ECPC19WP#DP>P@CF,EC95D5X>DPCPD&02CRWPWPQPC19R>RQ#DRZP2P@CFPD\C/=WPCPCAcCY2AcCZ2P@P@PEPC\CRW1_CY1_CZP2P2P8PW\ERW%{CRDPDPYPZPW\8/=DA58YZ%>ORD%>QRW'AP8P6%m8P1%m6%35,AOA58751t753sXM8X?8PYPDP5X?6RD%>5X?6RYPOPO1=6OR1D^PZPWPDPYPQPQ1=6QD^M<]1CC2RQ,h7%3QRY,0ORDP7POP1PQPY1=6YErP5CpRYPD%T:RQ%4IRI1CCPR1#TRW%31R1#4RZf9R[%34'1/9[R\,\0%H\%>\R]/A\'216\0%S]'2'Qf:R]%32'1/9]#>P6%3>R\,\0%H\%>\R^/A\'216\0%S^'2'Q%3PR^#>P620AGAR\%HG%4A%HH[[R_%4GR`g00ghRaB0@GA7UW=RA%4H\a^=`R`&0?;-0>6Rag00hDRb#ORc#ORd#ORe,I6Rf5i61I6cRc1I6bRb':Rg':g00hcRh'MRiAi6ac/:b,:f/MhRc&0=3Ra,Bc,Bi'B'B%n3R3P61X6:RiP7P61X64P9&0<6RcCPCP&0;6Rj&0:6Rk1f60Rl%e?,R6Rm57k1R6;Rn/Lm,Jk5<kA8kml1Lnl,Jk5<k5dk&04<R<Pk%e;,R6R;=U6m>036;Rm97kl1R6?R?/Lm,Jk5<kA8kml1L?l,Jk5<k5dkP<1Ln?,JkF?201k=R=P5P:g00iORmg00ioRo'=Rp2005:=5modA~607RoC`Rmb5b7b8X06X16X36XA6%H91A59'21690%S5'2'Q1194/99Rq#H1A:q'216q0%S:'2'Q1A:9[[^06^16^36^A6P5f;Rq#3f@P2P9P4P>O6b2bHbIbObCbNbBb;b4b:C}GN1=E2GN1=C@GNGNPPPSO1P:POPYPDPQPIPWPZP\P_PAP`PaP3P6PiP7PcCPRcPjPkA8klnROP<PkA7kn?R@P<A<kO@F?P=P5P:PpPoC`b5b7b8X06X16%45107:%4:Ro10:9Rp'2[[^06^16P51CCq#3RqP^P4P2O4b2b6b<b;b4b:O2EWPVPYPDPQPIPWPZP\P_PAP`%Oe,I6Re1I6d/:b,:fRf':/Mh/BaP3P6PiP71X69CPRiPjPkA8kl;P<PkA7k;?P<PkAU6n?Rb1f6G=|6BRG57kRdP<PkPOP<A7knG9<kOF?R@F?P=Pmb5b7b8X06X16X36109:11:9R0/0H%49Rr%44104H'2[[[\o^06^16^36P5P^Pqf<RsP4P2P[P]O7b2b6b<b;b4b:,V>RtD@PTPYPDPQPIPWPZP\P_PAP`1:eg/Mh1Mfh/BaRf'BP3PiPjPkA8kl?RhP<PkA7k?;R?P<PkAU6n;R;=7kGP<PkPOP<A8klb=<kdF?F?P=Pmb5b7b8X06X16X3611:4Rl/0H1142RO#410OH'2\r[\p\F^06^16^36P5PqP^PsP4P2P[P]O7b2b6b<b;b4b:,VRR]D@PPPUP2PSCgP2PPPUPSP>1CC>#3RC,15RS/6HX96PYPDPQPIPWPZP\P_PAP`PaP3PcPjPkPdP<A8kbGCaP=Pmb5b7b8X06X16RG1157/0H117:R7/6H[^06^16RdP5PqPsP[O3b2b6b<b;b4b:PVPtD@P>1KBXRX,6510XS'2X96PR16P511PC,05'2X96PYPDPQPIPWPZP\P_PAP`PaP3PiPjPkPhP<PkP?P<A8knbA7kb;5<kF?P=Pmb5b7b8X06X16X3616:0100l'2\p\F^06^16^36P5PqP^PsP4P2O5b2b6b<b;b4b:PTP]D@PVPtD@EzEWPVPtD@WEXL8J051EE9PJP9P2PKP4%3N,15/6HX96%TMRN%3M#4RMP\P_PAP`PGPdP5P1PLP2O3b2b@b6b41KBKPNPMP\P_PAP`PfP3PcPjPkPhP<P@CaP=Pmb5b7b8X06X16107H109H,2r\o[\F^06^16P5P1PLP9P2P>O5b2b@b6b4,V4D@I06EyWDWFW=WKXJ6WGo"). Qed.

Definition is_kblob_at (a : Z) (K : kentry) : bool :=
  match K with KBlob (SA (ELit 0) k) _ _ => (k =? a)%Z | _ => false end.

Section Grow.
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
  (* [comment removed for export] *)
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

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V2Open.ENV a0s path.
  Let L : Z := Z.of_nat (length data).
  Let modelk := modelk path tid fs0 stdin0.
  Let at_loop := at_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim data.
  Let at_full := at_full sp0 a0s path envv tid mem0 fs0 stdin0 lim data.
  Let side := side sp0 mem0 lim.
  Let slots := slots sp0 a0s path envv tid.

  Lemma ownedA_rangeG : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x76568 <= bv_unsigned a < 0x76918)%Z
                 \/ ((0x77000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Grow ()) ["Grow"] "p;7g00jOj70Tp,2ALp,2CLp,3ASRp,3sp0p,4Hvspp,7AL_globp,8AL_grantF0o"). Qed.

  (* [comment removed for export] *)
  Lemma regs_after_allocG : forall vals sr R R',
    sr_vars_lt (length vals) sr = true -> regs_ok (ENV vals) sr R ->
    (forall r, callee_saved r -> getr R' r = getr R r) ->
    regs_ok (ENV (vals ++ junk_vals R')) (sr_after_call_j sr KEPT_AL (length vals)) R'.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Grow ()) ["Grow"] "h03H32h12HLh22HRh32Hch43Hcsh52Hih61Rh72R'h81ah91ih:1rh;2srh<4valsp;1p;2p;3p;4p;:g004\j11Tg005Aj1<Tg005_j1;Tg006dj19Tg00Mnj1GTg001lj2CTg007Dj2ATg00kQj2@Tg00=Kj38Tg00lXj3>Tg00mhj16Tg00nkj22Tg00odj3=Tg010^j1FTg011ej3ETg012<j2DTg00=ej23Tg007dj15Tg00;3j24Tg00DOR0j2:Tg013?j4BTg013Zl:?Tg00Gkj17Tf0R1#7#7#7#7p=0g00f1#1R2#1#1#1#1#1#<#;R3#9g014h#9%G2#<R2/C3R4g00iOf3R5,A3f2R6'@g00io38p,3ENVf4R7O1?>56%;2%61f1R8,27f5R9/28583[]:f6R:p,3AMBp,3a0sp,4path3=#FP9P7P5g0161R;P6P8g00_cR<AE<1;1D81g00hD#0#0#0#0#0#0#0#0R<,38%58,42#6':P0136<%56,42#6135<f7R6%55,42R5'2f8/25583':P1137<%59,42#613:<f:%5:,42R2'2f;/22583P8P6P2P1O2CBW3W0P8P1O2n2001000000120000000b8W5W9g016kM:?W4W2W1X74W6W;W<o"). Qed.

  Lemma know_after_allocG : forall (A A' : AS) vals (M M' : word -> option byte) vm vm' R' kn,
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> kn_vars_lt (length vals) kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 128 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 128)%Z -> M' a = M a) ->
    (forall a, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ owned A a \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_acall kn).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Grow ()) ["Grow"] "h04__x1h14HLv0h27__arithh36__sat1h46__sat2h56__sat3h64cstrh75cstr0h85heq_Lh94__ffh:8__varmaph;5__with<4__p1h=4__x2h>4__p2h?1rh@2HahA1bhB1HhC2H0hD4__p3hE1ohF3HnthG2HxhH1ahI2HehJ2HohK4__p4hL6__sat4hM6__sat5hN4__x3hO1xhP1AhQ2A'hR2H1hS2H2hT2HIhU3HIAhV2HKhW3HLvhX2HMhY3HfrhZ2Hgh[3Hgrh\2Hhh]3Hhih^2Hlh_3Hloh`3Hltha2Hshb4Htophc5HtopAhd1Mhe2M'hf2P0hg2R'hh6__sat6hi6__sat7hj2knhk1mhl1nhm4valshn2vmho3vm'p%0p%1p&0p;3p;2p;1p;4p;5p;6p;7p;8p;Ap;<g017lk30jTg0195k30iTg01:>k20STg004\j13Tg005Aj1dTg005_k10?Tg006dj1|Tg006Bk10QTg00Mnj1ATg001lk20ITg00Gkj1gTg007Dj27Tg01;?R0k20FTg00=Kj3=Tg01;Yk20\Tg01<`k40DTg01>0k50BTg01?3k10ATg00>=j24Tg008aj1DTg00>gj2@Tg01?kj4GTg01@oj1?Tg01AHk20;Tg00O6k109Tg01BLk10JTg009\R1j22Tg00DjR2j20Tg01CNj1lTg01DVj3pTg009?k205Tg007dR3j1:Tg00CHj1JTg00E`k202Tg00FHk301Tg01E3k20[Tg01Edk20ZTg00JHk10CTg00Jhk200Tg00LBk10YTg00L`k10XTg00NSj2nTg00TEk30@Tg00P^k20WTg00@bj2ZTg00Q@k20VTg00Qlk30UTg00RKk40RTg000`k60>Tg00=eR4j2zTg00MKk20=Tg00S=j4xTg01FDj4wTg01GQk20<Tg00KFk10PTg01HVk20OTg00Flk10NTg01I9k10:Tg00DOj25Tg01IVk60LTg01J[k20KTg011ej3BTg01K;j2STg008Dj2>Tg00YEj6hTg01KUj7uTg00[Lj3fTg01LQj3VTg013?j4YTg01Lkj4rTg00EFS00j2MTg00Kdj4aTg01MEj3XTg00OXk307Tg01M_k60HTg00HJj2mTg00Zcj3{Tg00I\k206Tg01NCj2~Tg01Nbk50GTg00odk30TTg010^k10hTg01Obk80gTg01PnmA0fTg01R8k10dTg01S3k20cTg00B<m<0ETg00Bak40`Tg00[lj4eTg00\Wj7oTg00];k703Tg00^Ck804Tg00P;k30_Tg01T7k30^Tg01TTk30aTg01U1k40bTg01UQk60]Tg00]_k70eTf0R5#3#3p=8g00hDR6-0c5p=U%35#3#3#3p=^f3R7f2R8'0f1R9/25'5p=1A=895#?p=F1M95,M8p=b%A5#Ap=9%35#3#3#3#3#3#3#3p=W%35#Dp=K%A5#3p=<1089/55p=Eg00_ER:/Z5p=Cg00_cS01P:P0P3P2g01V5f5R2f4R0P7P8P9P5N<0Ep=O20F07P8P9P5H0`p=Ng00^gR;/05p=612;5p=P20=:5p=;P8g00b=R<g00b\R=P=g00c<R>P:P9g00eJR?P5Ceg00dCR@Fop=TP0P<P=P=P>P7P<P=P=P>P:P8P?P9CeP@FoP5K03p=Lf6RAP<P=P=P>P2P0P7P<P=P=P>P8P9P5L04L04p=[Q01P:P4P3P1g00`oP6P;P7P8P9P5N<0Ep=yP8P<P=P=P>P:P9g00c\R1P5CeP@Fop=HP7P<P=P=P>P8P9P5L04p=IB0_:95p=]1295,58p=vg01VWS02,@5p=\P:P9P?P5Cep>0MP7P<P=P=P>P8P9P<P=P=P>P5P@FoK03p=kB0^::5p=jB0a::5p=i10781295'5,50p=Q1289,57/M5p=R1589/M5p>08%35#Ap=t1595,M8p=cP:P:P9P5H0bp=sP9P<P=P=P>P5J0]p=`P8P<P=P=P>P9P5K03p=_P8P<P=P=P>P9P5K0ep=qP:P9P1P5Cep=}p,2ALR1p,2CLR@p,3ASR:0j1@60i1R@+0SS03Q03g00f1R?#3R3#8R4#3RB#8RC#dRD$0?RE#|%d4$0?R4$0QRF\ES04Q04g01WXS05Q05%A3RG#d00IEg01XO#|%g6RH17EA+0Ff7RI#Up,3sp0S065=Eg00iORJf8RK,7E00\8g00ioRL3=g00fVS07p,3ENVRMf9RNO1PKP7H0DP1P@f<ROPNPII0B&0AKQ06,4DRP%3CRC#3#8RQ#8S08#^S09#3#8#^RR#DRS'@RT5=:P1P@f=S0:f:S0;PKI0B&0AN==:TP1P@fARUP5CG#?P1P@PUP9CG#?20;18#?%DCS0<,@PRVg01YZ'@14D7RWPWPVC1S0=#?S0>PUP0O1fBRVP0O15=F[[[[^HEf?S0?P5O1&094RX5FF14D9RY&0J1RZ'2P1P@fCS0@P9CGQ0?P9O1=FFX3b[^HEp,4SPloS0A%A?S0B#AS0C#A#9#9#9#9#9#9#8#^#W#W#W#KR[/0Pp,4SPhiS0D%3R#8#^#W#W#KRR,0PQ07PMQ0:#lS0E9pEVR\O1S0FPUf@R]g01Z\R^g01[SR_g01\KR`g01]CRa%3?#8#<#<#8#W#KS0GPE%UVS0H%D3Rb%3G#8Rc#DRd+05Re14D5Rf%AGRG#9Rg#DRh-05bRi,0f3EXAERjPEQ06Pjp,4data,74R4#:Rj#Cp,1L==:jRkeRlPkPHQ0@,7ERm%D?Rn%:mRo'0RpPHPn%CnRqPmPo%CoS0IEOPODNRrPpfDRs,7ERt#JRu%:t#6Rt%J4R4%6jRj202bh%PbRv%6h%Pi[[%6bRwg00ghRxB01bh9UW@%6i\x^@w202bdS0J%6d%Pe[\vS0KB01bd9VxX@wS0L%6e\x^@wS0M%KGRG-02bRd%6G205bGRh#P[\vRvB01bG9VxX@wRG%6h\x^@wRw%DBRB-0[PRx%6P%6B20ZPB#6[[RBg00aQS0N$0CRhQ0N#|Ry200:9Rz&0Y:R{&0X:R|1n:?R}%;R5T|&09=R~P|%;[S0O=T|}P~P|P|%;bRb%dc60@:RcP}%dg:0@:b9T|}DLF[20W|>RbP5P81ZJL20V58==JLdB0U:;9H0RRLb9b:b;X0:105R10[9108i9Ee8[[^0:P5PPQ0DQ0AO3b2b3b4b5bLbMbhbib7b6b1b8Q0HQ0;J0>%U\PVQ0EP6PlPk1z6m%Po1Z:;S0HPmPoQ0ICyPrPpPuPtP4PjPdPvPGPwPxPBPhPyPzP{P|%;n=T|}P~20=:;Ro=H|}CIPbPLb9b:b;X0:S0I10n5%P9[^0:S0DP5fJS0P,7ES0Q#:S0RPAO2b2b3b4b5b7b6b1Cxb8CwJ0>Q0F00<6,4DRm10mi5EeePlPkPrPpPuPtP4PjQ0JQ0KQ0LQ0MPdPvPGPwPxPBPhPy&0P:S0MP{P|P|Po%A?#<#9#<#8#W#KRm#;S0LQ0L%;SS0K,]c5H|DLPbPLb9b:b;%6m1@eS7vmP5b2b3b4b5bLbMb7b6b1b8P;PaPa%\eC1ePlPkPrPpPuPtP4PjPdPvPGPwPxPBPhPyQ0MP{P|P|P|Q0K-0O:&0NCRC#;S0J%DQS0S#;S0T']S0UQ0UQ0J5T|DLP|Q0J00MoCkPbPLb9b:b;&0:SQ0S,@CRo10oC3E10C;'5P5b2b3b4b5b7b6b1b8Q02$0:10_`7E_10`;'5ePMQ0@f>S02#l5pEO1S0VP^P_P`PaPfJ0L#?PEQ0?#lRM9pEs#U14D8R;/2a20K::RQABQ5^R^%j5S0WPWPW%i5S0XDQX?Q'S'5Rt10a;Ru%\fS0Y7v;1>f_RpP;P;1>f`RrC13b#?XAEP5%UsRePsPMP6PlPkfERM,7ERc,z6%:cRi#PQ0HPcPi%CiR\CyPHPc10niRRPHPnPqPcPiP\EOQ02DNPRfFS0Z,7ES0[#JQ0[#:RR#6P4PjPdPvPGPwPxPBQ0IQ0DP5fLS0\,7ES0]#:S0^PAO2b2b3b4b5b7b6b1Cxb8CwEh12YaP^Q0WP;P;Q0XDQX?Q,SQ10aYPY14DeRe#\1>e_PYPY1>e`C1CR408#?PE%UMS0_12WaP^Q0W14D0R^P^Q0XDQX?Q,SQ10aWPWQ0YPpPWPWPrC1CR408#?XAEP5Q06Q0:Eh%\PS0`9vu;1>P_P;P;1>P`C15bt#?PIP7P1P@fHS0aP7CGS0bfIS0cQ0ZPsP0POf;S0dP5Fu%A?#<#9#8#<#<#9#t#8#KRt/0^P^%A?#<#9#t#8#<#8#9#8#KR`PmP^P^PTC1S0eQ08#DR_/0^Q09#DRu,2^3cCRS09Q00Pt14D2RrPrP`C1PmPrPrPTC1S0810_r12ru3cg01^=S0fP5Pt14DARpPpP`C1P014DIRe/2mR\1st`Ri%3?#<#9#^#9#<#t#<#KRc%3?#<#9#^#9#<#<#8#KS0g'sR?1s_uRJ&0CQS0h5fQS0i5fQS0j5fQS0k9BQ5S0lQ0W14DKS0mQ0mQ0XDQX?QS0n,SQRg'5PmPePePTC1S0o1>PoS0p/0e1>PCS0q,2e3cP\PgPlPkPHfKS0r,7ERg%:gR\,0nS0sPHPnPqPgP\%C\EOPsDNS0tQ0sQ0]#JS0uQ0^#6S0vP4PjPdPvPGPwPxPBp-0R\PhPyPzP{P|1`|7S0w%;`S0x9H|}S0y5_|P~Q0L9H|}S0zCIPbPLb9b:b;X0:W<125`S0{,59129mS0|[^0:^<\P5Q0?,4DRg,0tPgPKO3b2b3b4b5b7b6b1b8PQQ0nPiQ0k9BQi%jiPePe%iiC1S0nA=QiiQ0j9BQi1ZQi3VPlPkQ0tQ0sQ0uQ0vP4PjPdPvPGPwPxPBPhPyPzP{P|P|P|%;tP}Q0yDLS0yP~Q0yCIPbPLb9b:b;X0:Q0{9Et5129`S0{9Et9[^0:P5PgPKO2b2b3b4b5b7b6b1b8Q0neCYCrCY3VO1WZP5O110mpPpPTP_PpPpPuC1CRQ00Q0oP_PePePuC1Q0fP5PmQ0mQ0mPTC1PA14DNRe/2mS0oQ0lQ0WQ0;,4DRgPgQ0XDQX?QS0n,SQS0y'5S0vPmPePePTC1S0uQ0pPePeQ0qC1S0s'MS0tQ0uQ0sPlPkPHfMS0},7ES0~Q0~#:S10,0nS11PHPnPqQ0~Q10Q10#CEOQ0ZDNS12Q11fNS13,7ES14#JS15Q14#:#6S14P4PjPdPvPGPwPxPBPhPyP:200:8S16P9Q0MCaS17P{P|P|P|Q0LP}1n:3R3Q0K']9H|}DLS18P~Q18CIPbPLb9b:b;X0:X=:PmP5P51@9SS18C1PmP9P91@8SC1[^0:^=:P5PP14DUS19PKO3b2b3b4b5b7b6b1b83V3XO1W\P5O1P_Q0mQ0mPuC1PAQ0vQ0tQ0oQ0yPlPkQ12Q11Q15Q14P4PjPdPvPGPwPxPBPhPyPzP{P|Q0w%;uS0y9H|}S0o5_|P~Q0zCIPbPLb9b:b;X0:X<\125uS0m,59Q0|[^0:^<\P5Q19,0_Q19PKO3b2b3b4b5b7b6b1b8PQQ0nPJQ0k9BQJ%jJPePe%iJC1S0nA=QiJQ0j9BQJA=Q?JQ0i9BQJA=QJJQ0h9BQJ1ZQJ3V3X3XPlPkQ12Q11Q15Q14P4PjPdPvPGPwPxPBPhPyPzP{P|P|P|%;_P}Q0oDLRJP~PJCIPbPLb9b:b;X0:Q0m9E_5129uS0m9E_9[^0:P5Q19PKO2b2b3b4b5b7b6b1b8Q0neCYCrCY3VO1W^P5O1n200100000021100011000WBP5O1n200100000021100011000S0tbEWJQ0b#?eP1P@fGS0bP7CGRJQ0aPMQ0@P0Q0;PNP5FuQ09Q0tbEWJ%?Je20;17S0tp,8AL_errnoP0P5O2PcP^P^Q0gC1P812rmS09Q0lQ0WPpPpQ0XDQX?QS0;,SQRJ'5Q08Q0p/0rQ0q,2r3cQ09PJPlPkPHQ0c,7ES09Q09#:RJ,0nS08PHPnPqQ09PJ%CJEOPVDNS0vQ08Q0Q#JS0QQ0R#6S0RP4PjPdPvPGPwPxPBPhPyPzP{P|Q0wQ0g#;9H|}S0n5_|P~Q0zCIPbPLb9b:b;X0:X<\Q0g,25S0z,59Q0|[^0:^<\P5Q0:,4DS0:,0cQ0:PKO3b2b3b4b5b7b6b1b8PQQ0;P?Q0k9BQ?%j?PrPr%i?C1S0kA=Qi?Q0j9BQ?A=Q??Q0i9BQ?1ZQ?3V3XPlPkQ0vQ08Q0QQ0RP4PjPdPvPGPwPxPBPhPyPzP{P|P|P|%;cP}Q0nDLR?P~P?CIPbPLb9b:b;X0:Q0z9Ec5PcP9P9Q0gC1[^0:P5Q0:PKO2b2b3b4b5b7b6b1b8Q0keCYCrCY3VO1bIWIQ0t#?eQ0=P912^mQ0lQ0WPrPrQ0XDQX?Q,SQ'5Q0eQ0pP^P^Q0qC1Rc'MQ0ePlPkPHQ0a,7ER?%:?Ri,0nS0qPHPnPqP?Pi%CiEOPUDNQ0qQ09#J%6JP4PjPdPvPGPwPxPBPhPyQ17P{P|P|P|Q0<#;,]}RJQ0T']P3AH|3JDLP~P|P|P<P=P=P>1`|0R>1`|2R=P|P|Q0U:07:}P3Q0J:07:}9H|3DLR}5q|5q|J0HP~P}F[PbPLb9b:b;X0:X=:X<\X>\Q0<,@5R}Q0S'@P9P9P}C11>9oP8P81>9CC19b70Q0f[1>8oP7P71>8CC1[[^0:^=:^<\^>\P5Pm14DORCPCPTC112CmQ0lQ0WQ0:Q0:Q0XDQX?Q,SQ'5PCPPPKPNO6b2b3b4b5b7b6b1b87Xc3XO1WaQ0>eO5bFbFWFXOEQ0V00<6,4DRc#\PfPfPcC1Q0@P9O1=FFXPE%l]Rc9pEM#UQ0YPWPWPfC1XAEP9Q0_PMPcP6PlPkQ0[,z6%PRQ0HQ0[PR%CRRcCyPHQ0[10nRRCPHPnPqQ0[PRPcEOQ0?DNPCQ0b,7ERC#J%:C#6P4PjPdPvPGPwPxPBQ0IQ0DP5Q10PAO2b2b3b4b5b7b6b1Cxb8CwEhQ0_,4DRC#\P;P;PCC1PEQ0Z#UQ0YP^P^PfC1XAEP5Q06Q02EhQ0`PWPWPPC1PIP0P8O212^ZP1P@Q0cP0CGPMP0O1=FFX3bQ0012rZP1P@Q0PP2CGQ0ZP2O1=FFX'MQ0bPAO1=FFXRrP512pZp,5AL_hi10ZmQ0cPKO1=FFXRpPlPkPHQ0]Q0^,0nR^PHPnPqQ0]Q0^Q0^#CEOPMDNP^Q0~#JQ10#6P4PjPdPvPGPwPxPBQ0N%gHR^#gRM#g,m:1m:M1m:^1m:65{:5{:R65{:g00hcR^+06;fhPyP:PzP7P:Q0MP8200:7CaCaP{P|Q0L9T|3P~P|Q0C,n:Rz=H|3P~P|Q0B,n:R3Q0K']RM=T|zRW=_|=P~P|Q0O=T|3R3P~P|P3P~1`|ARfCIF[RCF[PbPLb9b:b;X0:X=:XN:X<\X>\105m12791@7S?E0210[010[2PN[[[[[^0:^=:^N:^<\^>\P5Q0f14D]Rc/2PPcPPPZPKPNPOPVQ0AO:b2b3b4b5b7b6b1b8'~bCWBP5O1P1P@Q0rPACG/MrQ00P1P@Q0\PICGQ0aPIO1=FFXPpP5P1P@Q0}PKCGQ13Q0rQ0cPNPUP]P5Fu10tePeP`Q0u10_e12eu3cCRQ00PtPgPgP`C110mgPgPTP_PgPgPuC1CRQ0\Q0dO1=FFXP5PtQ0d,4DRgPgP`C1Q0}POO1=FFXRXPlPkPHfP,7ERF%:FR`,0nRePHPnPqPFP`%C`EOQ0cDNR`PefQ,7ERF#JRq%:F#6RFP4PjPdPvPGPwPxPBQ0N2066^;fhRhPyP:Q0MP8P:Q0MP9Q16CaCaR^P{P|P|P>P|Q0x,}zCkP~PCCIPbPLb9b:b;X0:X=:X<\X>\XD\Q0{,58Q18/08RC/5010[8R610[7R[PK[[[[^0:^=:^<\^>\^D\P5Q0f14DsRs/2PRD10tsPsPPPKP]Q0ZQ0AO9b2b3b4b5b7b6b1b8'~WCP5O110mgPgPTP_PgPgPuC1CRPlPkP`PePqPFP4PjPdPvPGPwPxPBPhPyP^P{P|P|P>P|1}zMCkP|P=P|Q0y,}zCk5q|P~P|A_|WfP~P|P3P~P|P3P~1`|IF[F[PbPLb9b:b;X0:X=:X<\X>\XD\XK\P8P91@5SQ0m,57CR15C2PN\[\6[[^0:^=:^<\^>\^D\^K\P5Q0fPD10_s10msPsPPPKP]Q0ZQ0AO:b2b3b4b5b7b6b1b8,~XWCP5O1n200100000021100011000bEWBP5O1P5XBpP5O1n200100000021100010000WCP5O1n200100000021100011000bEbGbGWXWGXOEQ04Q01Q0G/0Y%:9,>;/0aP0P7P8P9P5I0GWSWRWlXHEWkPOQ07PVQ0Ep,3AMBp,3a0sp,4path40T$0hPUPOPNPKL0gNA0fQ07Q0FP]&0dOH0Deb]b_W[WYWbWTWcWUWVW`WfWWWjWgWoWnWeWdWmWQWPo"). Qed.

  (* [comment removed for export] *)
  Lemma env_ok_alloc : forall A A' M M' vm vm',
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 128 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 128)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Grow ()) ["Grow"] "h04__x1h14__p1h21ah37__arithh44__ffh56__sat3h68__varmaph75__with84__x2h94cstrh:5heq_Lh;6__sat1h<6__sat2h=4__p2h>2Hah?1oh@1HhA2H0hB2HehC2HohD4__p3hE6__sat4hF6__sat5hG1AhH2A'hI2FRhJ2H1hK2H2hL3HEahM3HElhN3HErhO2HIhP3HIAhQ3HfrhR3HnehS4HtophT5HtopAhU1MhV2M'hW2vmhX3vm'p%0p&0p;3p;2p;1p;5p;4p;7p;6p;8g017lk30ATg0195k30@Tg01:>k200Tg004\j10Tg005Aj1pTg005_j1mTg006Bj1~Tg01^Zj3^Tg01_Vj3dTg00>=j2>Tg009\j24Tg00Mnj15Tg01@oj19Tg00=Kj33Tg008aj1CTg00Djj21Tg00O6j1qTg00DOR0j2;Tg01>0j5LTg01?3j1KTg00>gj2ITg01?kj4ATg01AHj2sTg01KUj7gTg007Dk20?Tg007dk10>Tg00@bj2rTg00CHk10=Tg00E`k20<Tg009?k20;Tg00FHk30:Tg01E3k209Tg01Edk208Tg00Gkj1YTg00HJj2UTg00I\j2eTg00JHk107Tg00[Lj3bTg006dk104Tg00KFk103Tg00Jhj2lTg00LBk102Tg00L`k101Tg00NSj2VTg00P^j2}Tg00Q@j2|Tg00Qlj3{Tg00RKj4zTg00P;j3_Tg00EFR1j2STg000`j6aTg013?j4nTg00Zcj3wTg00Kdk405Tg00MKk206Tg00[lj4\Tg00\Wj7[Tg00];j7ZTg01UQj6uTg00]_j7hTg00^Cj8]Tg01M_j6tTf0R2#0#0p=@%52#0#5#5p=O%02#0#0#0p=J%52#5p=7%02#5p=:%02#0#0#Cp=<%52#0p=2%52#5#0#0p=cf2R3f1R4'1/;2p=kf3R5/13/;4/S2p=E%02#Cp=j11531442';p=8%02#0#0#0#0#0#0#0p=P1434,;5/S2p=vg00_ER6?342p=G1;42,S3p=Qg00^gR7/12p=HAw642p=NP6P3P4P2H05p=B20662p=6P6P4g00eJR8P2C\p=TP3g00b=R9g00b\R:P:g00c<R;P6P4g00c\R<P2C\g00dCR=F[p=?P5P9P:P:P;P3P9P:P:P;P4P=F[P2FZp=WP3P9P:P:P;P6P4P8P2C\P=F[p==P4P9P:P:P;P2Eup=`f4R8P9P:P:P;P5P3P9P:P:P;P4P2FZFhp=Df6R>P9P:P:P;f5R?P8P5P9P:P:P;P3P4P2G]G]p=M1442,;3p=XP4P9P:P:P;P2Etp=RP5P9P:P:P;P3P4P2G]p=FP3P9P:P:P;P4P2Fhp=yP3P9P:P:P;P4P2FZp=fP6P4P<P2C\p=iP5P9P:P:P;P3P4P9P:P:P;P2P=F[FZp=o1;34/S2p=xp,2ALR=p,2CLR9p,3ASR:0A=960@=R9+00S00Q00g00f1R<#0R@#0S01#0RA#0RB#@RC#pRD#mRE%pA#mRA#~RF[S02Q02g01WXS03Q03p,3sp0RGp,4mem0RH;^5P0AdGH8%0<#O#J#7#:#@#<S041>D2RI%0<#2#c#:#:#7#7#<RJ,4I%5<#2#c#2#:#2#2#<S05%5<#2#c#2#O#:#<RK,4IRL7kICERM%0<#O#J#7#2#:#2#jRN1>D4ROPO%0<#O#J#7#2#2#<ROC8#9RPf7RQP3O1PHP3O1RR53F[[^2E%0CRC#0#@S06#@RS#JRT#CRU/1IRVPI%0<#@#2#@#P#<RW%0<#@#2#:#7#:#2#:#<RXPIPI%0<#@#2#:#7#:#2#2#<RYC8CvRZP>P4O1%qAR[53F[^2E';P=P9PQP?P5DL%K81>DGR\%JT#<RT'IR]'GP=P9f8R^P>P8DL%K?/G]P=P9f<R_P2CA#9P=P9P_P4CA#91s=3S07#9R`%CCRC,I\S08g01YZ'IS091>D5RaPaQ08C8#9Rbf=RcP8O1f>S0:P8O153F[[[[^2Ef9Rd9^GH[[[[[P2AdGH>f:ReP3O1=3FR\P\M^2EPdP4O1=3F[\Z^2E';P0f;R0P3O1=3FR\P\M^2EPeP4O1=3F[\Z^2EP=P9P0PdPQDL%K^/G]P=P9P_PeP^DL%Kd/G]P=P9f@RfP2CA#9P=P9PfP4CA#9fAP8O1fBS0;P8O153F\b\`[[^2EA^GHc[[[[[P2PcP3O1=3FR\P\M^2EPcP4O1=3F[\Z^2EP=P9Q0:P_PeDL%K0/G]P=P9f?PcP0DL%K_/G]P=P9fCS0<P2CA#9P=P9Q0<P4CA#9fDRfP8O1fES0=P8O153F\b\`[[^2Ep,4SPloRb%5<Rg#5Rh#5#7#7#7#7#7#7#J#P#P#P#<Ri/1\11\IS0>?QVLS0?P8P3P=P9fGS0@P3CAS0AfHfFS0BPfP5PdP^P2FgPKPa%5<#O#:#@#2#@#7#<RV,4a%5<#O#2#P#<RLPa14a]%CSRSPaPaPUC8CECES0CP1PK1>D8R1P1PVC8PLP1141]PSP1P1PUC8CEg01^=R1P2PK1>D?RIPIPVC8p,4data-0?ARA$0>Rj,r6p,1L/GjRkeRlPk&0=ARA%HjRj%C@Rm%7@#jRn+0<Ro147m%Hn20;mnRp,47[[Rq%HmRrg00ghRsB0:mn4UW>Rn%Hp\s^>rRr%CBRB-09\Rs%H\%HB208\B#H[[RBp-0Rpg00aQRmg00hDRt#YS0D#YRu#YS0E,U6S0F1U6uS0G1U6tS0H'N'Ng00hcRt'e&07mRu3bS0I&04mRv&036Rw1l63Rx9Bw47B3S0J&026Ry&016RzPzPz%6KR{1V6hRh'T%6V9?zhCW%q:R:PzPz1V6gRg==zhS0KPz1`z8R|A?zh{S0LDDP:Pz%6iR}==zgR~P:PzP~P:1`z?S0MFMS0NFM1}z;R;P2P3g00iOS0Og00ioR~'rQ0O1|23;3~dA{674CzR7b4b6b7X06X86X1pW=PKP4P4PVC81143RV143KS0O7Q511i3R~11i5S0PPQ[[S0Q[[^06^86^1p^=pP2P11>D_R_,1UP_P\P>P0PcPbO8b3b;b<b5b9b:WAP2O1PLPI14I]PSPIPIPUC8CEPlPkPAPjPoPqPnPrPsPBQ0IPvQ0JPyPzPzPzPz%6L/Th%6T9_6g9?zhCWPzP|%6URg9?zhDDP:PzPzQ0KPzA=zghQ0LDDP:Q0NFMP;P7b4b6b7X06X86X1pX=pPLP41I2T,44AX34UCE11U3Q0O5QVQ0Q[[^06^86^1p^=pP2P111S_P_P\P>P0PcPbO8b3b;b<b5b9b:WAP2O1n200100000021100011000Rcb?WCQ0A#9eP=P9Q0BP3CAR9Q0@Q0=Q0<P5PQP>P2FgQ0CPcb?WC%99eQ07p,8AL_errnoP5P2O2PNPaPaPOC8PlPkPAPjPoPqPnPrPsPBPuPv1l64Ra9Bw49Bw4PyPzPzPz%6NR9/Th%6ORc9?zhCWRhP:Pz1RzhP:1`z5RhFMP;P7b4b6b7X06X1pPNP2P2POC8R=11N4R_?X4OP1[S0CP5[[^06^1pP2P11>DeP>P^O4b3b;b<b5b9b:bBWBP`ePlPkPAPjPoPqPnPrPsPBQ0E#Y,U6Q0GQ0D,U6R`'N'N/et=bmuPvABx4wRePyPzPz1V6<R<1V6@R@5=zRSPzP|A?z@{R{DDP:PzA=z}<RTP:PzPTP:PzPz%6C9_6<RTQ06#CRL#65_6/T@A?z@TCW,RzCFFMP;P7b4b6b7X06X86X1p1124RT144KRI7Q311i41I5CRC/ILP8P8PCC8P1[\~[[^06^86^1pP21>D^R^,1UP^P\PQPdPbO6b3b;b<b5b9b:Q091>D3RCPCQ08C8#9eO5XRPW>X2EQ0?PfP3O1Q0=P3O1RC53F\P[^2EQ0;9dGHRGA3FCR\P\M^2ERLPfP4O1Rf=3F[\Z^2ERi';Q0>PFQ0=P4O1R]A3F2RX?FQ0:P4P2O2PfP3P4PlPkPAPjPoPqPnPrPsPBPuPvPePyPzPSP:AyzS|CFP;P7b4b6b7X06X86X1p1SV5\T^06^86^1pP21>DQRD,1URT?XDKPDP\P>O4b3b;b<b5b9b:PlPkPAPjPoPqPnPrPsPBQ0FQ0H,N`'N/et=bmuPvABx3w?B4wPyPzQ01,V6Rx==z<P:PzA=z}xRxP:PzPxP:A?z<cRc9fz|,RzCFFMP;P7b4b6b7X06X86X1p1142Q0PAX?5OP1[[\~[^06^86^1pP211NDP\PDP>PdPbO6b3b;b<b5b9b:O3EaW>X2EPGePLPiPFQ0BP3O1PHP5O193F2X?FP0P3P4P2O3PCP5P3PlPkPAPjPoPqPnPrPsPBPuPvABa4wRwPyPzPzPzPzQ04#6/T@%6J9?z@CWPzQ05#6==z@P{DDP:PzPhPzA=zg@RgP{DDR{CFP;P7b4b6b7X06X1pQ04P2142JQ05P2P2PKC8CE11U4=Q3IRI[^06^1pP211\^P^PQO3b3b5bEbFb9b:PlPkPAPjPoPqPnPrPsPBPuPvPaPyPzA=z9<R9=fzc,RzRcP:PcCFP;P7b4b6b7X06P1\=Q0C[^06P2P^P>O2b3b5bEbFb9b:O3EaXKPXJMX2EPFP]A3F2[X?FPdP4P2O2PfP3P4PlPkPAPjPoPqPnPrPsPBPuPvPwPyPzPzPzPgPz%6WRg,i@CoPz%6X==z@%6YRw9?z@DDP:P{CFP;P7b4b6b7X06X1pPUP2142WRW142YRY9kX2CEPI[^06^1pP211\DPDP>O3b3b;b<b5b9b:PlPkPAPjPoPqPnPrPsPBPuPvPaPyPzPzPzPhPz1i<gCoPzP|A?z<wDDP:Q0M9fz9,RzCFP;P7b4b6b7X06X1pX=pXDp1;3Y9x4W1;_8P1[[^06^1p^=p^DpP214DO11XDPTPDP>O5b3b;b<b5b9b:O3EaX>ZX2ECnCnbIb@WQWSWOWTWPWNWMP4P2O2n2101000010121000000W@WLP4P2O2n2011000010121000000W@WXWWWVWUWHWGo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kimg_clearG : forall E M kn lo hi,
    know_ok RSEGS E M kn -> existsb (is_kimg_cov lo (hi - lo)) kn = true -> img_clear M lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Grow ()) ["Grow"] "p'0h01Hh12Hch23Hinh31xi001xh41ih51ni011nh61ai021ah71ei031eh81mi041mh91Ah:2H1h;2H2h<2Hah=3Hexh>4__x1h?4__x2h@4__x3hA4__x4hB4__x5hC4__x6hD1fhE3hi0hF1lhG3lo0hH1EhI2HKhJ3HKKhK2HihL2HnhM1KhN1MhO2_HhP3_H0hQ7__arithhR4__ffhS6__sat3hT6__sat4hU6__sat5hV8__varmaphW5__withX2a1i052a1hY2a2i062a2hZ4cstrh[2e0h\5heq_Lh]2hii072hih^1ki081kh_2knh`2loi092loha2n1i0:2n1hb2n2i0;2n2hc1vi0<1vhd1wi0=1wi0>1bp&0p;1p;4p;2p;3p;6p;7p;8g004\j14Tg005Aj1`Tg005_j1^Tg006Bk107Tg006dj1WTg01<`j4vTg00>gj21Tg01`Nj2dj3=Tg01aYR0j3YTg011ej3ITg00DOR1j2:Tg01K;R2j2MTg01b5k305Tg01bXj36Tg01cTj3OTg01NCj2STg01d_j2RTg01ejj3TTg01g5j2VTg01h@j2<Tg008Dj2FTg01h]j3mTg00Djj25Tg01i@j2jTg01i`j3_j4NTg01k2j3]Tg01kSj3iTg01l5j6hTg008aj1HTg009?j2\Tg009\j27Tg00;3k206Tg00O6j1fTg00=Kj3@Tg007Dk204Tg007dk103Tg00@bj2eTg00CHk102Tg00E`k201Tg00FHj3}Tg00>=j2|Tg01E3j2{Tg01Edj2yTg00Gkj1GTg00HJj2ETg00Zcj3LTg00I\j2cTg00JHj1xTg00[Lj3bTg00Jhj2UTg00KFj1uTg00Kdj4CTg00LBj1tTg00L`j1sTg00NSj2BTg00Mnj1JTg00[lj4ZTg00P;j3rTg00OXj3qTg00MKj2pTg00P^j2wTg00Q@j2oTg00Qlj3nTg00RKj4zTg01lPj2PTg01m[j3[Tg01nfj2QTg0201j4XTg00YEj6~Tg00\Wk700Tg00];j7lTg00^Cj8kTf0R3#4#4p=gg00iOR4g00ioR57@3p=2g01XOR6f1R7;I3p=0f2R8?=73=@45p=3P4P8P7g021<P5P3E~p=Ag00^gR9/53p=91587/:3p=8%J3#Jp=;g00_ER:P7g00eJP3CZp=DP7g00b=R;g00b\R<P<g00c<R=P3g00dCK00p=>P8P;P<P<P=P7P3Flp=a%43#4#4#4p=?f3R>P;P<P<P=P8P7P3Gkp=Kg021Xg00f1R;#4R?#4R@#4RA#4RB#gRC#`RD#^%`A#^RE$07RF[%W6g00fVRGf4RHP>P8Cv1178,d8=Y6>#2P0p4p710R0P4\3RI%W7RJP1AY873#2AIH38P>P3O1#2':X3>,M>[RKAI>37P8P3O1#2':X38,M8AY>87#2RL[f5RM?I3>PHP3O1#2':X3H,MH\LB05873P7n2001000000120000000WFWDW9PK^FJ^DI^90P3P611>H,dHPMP7O4f6R0,0311HM=3M3':X36,M6P2P6f7R2,0311M0=303':X36f8RI?60MP3f9RJ,03112I=3I3':P1f:RK,0711IJ=3J7f<RI?6KJP310>If;RL/1I=3IHP6f?RN,03f>RO/1N=3N7fBRPf@RQ;6N]1]2PMg022`RRg00_cRSg014hRTAO873fDRU'0fCRV/1URWAO>8753UfERX11UXRYAOH>83=P4p-0P3g01^=RZg00ghR[n0110>00020000R\X74R];A3PZfHR^fFR_;6X/S3R`b0W1W2WcWdW6P8P7P3O31R73/0PfARa/1PRb1R8753P11PVRc1R>85=V?A]3PZA6_UV/S3Rdb0W1W2X5TX6RP7P3O2AT873/0UAT>8793UWATH>89=XY?A]3PZP`b0W1W2X^SX5TX6RP8P7P3O31V73/0P1V8793Pb1<>VRS1FVc/<8Re;m3%2S%2e':P11<HU#21FUW/<>#2fGRe?6XUP31<0_#211_eRS,Fe/<0#2P11<73#21587[Rf15731<87#2Rg[15>8\g1j73P7n2001000000120000000X8:X5:RgPf^8:^5:RfP3PJfIRhP8O315JhPgPfP3fKRffJRg/1f'FRfPKP>O315fKfORffNRh5_GRJfMRi5]6103fPGfRRjfQRkP7CN[^36[103hPGPkfPRlP7CN[^36A_Glf=]6h[Ai6JiPg1VILRLPKEhPGPfPhPLCNP1f=RL#9%H?Rf%HC'\RC173L98O3Pk206D7ROO1%fERL5@F[^4:58IA6lhiP3%9N173Q98a3fTRlPOO1=@FL[^4:98NCP115QC173a98P3fURQPOO1=@FL[^4:A6ljkP315PC173U98X3fXPOO1=@FL[^4:fV173Q783P8P7p,4data-04ERE$03RL,e:p,1L=@:LRFePF&02E%9L%;?#4#HRL-01f179f%9L1\fLRE,79[[%9fRFA}fL7V[W<%9E\[^<Fp,3sp0,|DRD%HBRB'{%9D%9B1yDB#9[[g00aQRBg00hDRF#G#GR[#GRE#GRL#G,E:1E:[1E:FRF5L:5L:g00hcR['c1E:L1E:E=L:F5L:/c[%xB5bB3b%WBP:P:P:1U:MP0%u:RBCCP81U:HCCP7P:P:1U:0P0PBCCP>PBCCCC%t:%s:RB1B:ARA1B:?R?'D,>BP:P?g00c\R[%J@,B:R@CZ,>B5aB%f<R<PBAr:@A9q:A%J;R@,B:RF'D,>BP<PB1B:;R;/DA,>BP<PB%;@#;#;#;#;#;#;#4#g#?#?#?#?#?#?#?#HRA,p:%4@,B:'D,>BP<1D;?,>BP:P?P[PFCZ,>B5aBCKCKCKCK1wB=P3P81e451o38#2dAn:97CzbRbVbWX>:X?:X@:XA:XB:XC:177M98H7110M,FM/5>158015A017M098HM[[[[^>:^?:^@:^A:^B:^C:P3f\f]PDfLP2PiP0PaPVp,4SPloO:bQbSbTbUbZb\O2WKX4:fW?6QleWLWPP7P3O2n2001000000121000000W0WOP7P3O2n2001000000121000000bJb;b0b:b0W;W:P7P3O2n2001000000121000000b1W1W2XE:XG:P7P3O21P73/0P1P8793Pb1P>89=VcP\X[4R4;A3PZPdb0W1W2X8:X7TP7P3O2A[873/0UA[>8793UWA[H>89=XY?A43PZP`b0W1W2XE:XG:X7TP8P7P3O31Q73/0P1Q8793Pb1Q>89=Vc?A]3PZPdb0W1W2X5:X6RP7P3O2P>P8P7P3CX/0_11X_PHP>P8P7CX53_PMPHP>P8CX9=eS?A]3PZA6g^e/S3b0W1W2Xb:XYRXa:XXRP>P8P7P3O4n0110800083010210=10<2010210130102101108211091072010310430103109107201021014010510:10610;P7P3O2W1W2P7P3O2n2001000000121000000W0XM6P7P3O2n2001000000121100000b=b0W=WIX]:X`:W_WNWHo"). Qed.

  Theorem full_refused : forall j buf cap, (2 ^ 26 <= cap)%Z -> at_full (t_die msg_refused fs0) j buf cap.
  Proof.
    intros j buf cap Hcap A vm vals R M HL SL HR HK HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    unfold V2ReadLoop.modelk.
    run_blk_keep (SCR [true] [] []) 41%nat.
    { cbn [sc_denot branch_taken edenot ev ENV V2Open.ENV]. unfold bv_eqb. rewrite u_srl64. rewrite P8, !u_small by lia.
      change (26 mod 64)%Z with 26%Z. apply (f_equal negb (y := false)). apply Z.eqb_neq.
      intros H0. pose proof (Z.div_le_mono (2 ^ 26) cap (2 ^ 26) ltac:(lia) Hcap) as Hd. rewrite Z.div_same in Hd by lia. lia. }
    cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    change fs0 with (m_fs (mkModelC (fdsk path cap) vm stdin0 fs0 None (Some tid) None)).
    lazymatch type of HR with regs_ok _ _ ?Rc => lazymatch type of HK with know_ok _ _ ?Mc _ =>
      apply (ref_refused_tail sp0 (blobs0 a0s path) (mkModelC (fdsk path cap) vm stdin0 fs0 None (Some tid) None) Hvsp eq_refl eq_refl eq_refl a_reader (bv_unsigned tid) Rc Mc) end end.
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV V2Open.ENV].
      rewrite P0. first [reflexivity | f_equal; lia].
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ (-6144513 + d) m HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V2Open.ENV] in Hst. rewrite P0 in Hst.
      replace (bv_unsigned sp0 + (-6144513 + d))%Z with (bv_unsigned sp0 - 6144513 + d)%Z in Hst by lia. exact Hst.
    - unfold re_ivs. repeat (apply Forall_cons; [eapply kimg_clearG; [exact HK | vm_compute; reflexivity] |]). apply Forall_nil.
    - unfold cell. krd HK 0x561c8%Z 4%nat Htc. rewrite Htc. cbn [edenot ev ENV V2Open.ENV]. rewrite P5.
      rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact Htid.
    - unfold cell. krd HK 0x561a8%Z 8%nat Hsf. rewrite Hsf. reflexivity.
    - unfold cell. krd HK 0x76528%Z 8%nat Hpg. rewrite Hpg. reflexivity.
    - cbn. apply (length_guard_bytes a_draw).
    - lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kblob_at 0x764d8) in exact i) _ HK eq_refl) as KB end.
      cbn [kentry_ok] in KB. destruct KB as (_ & _ & KB). unfold elenZ, estart in KB. cbn [a_base a_off edenot eb ENV V2Open.ENV blobs_ev blobs0 nth] in KB.
      rewrite (u_small 8), (u_small 0) in KB by lia.
      intros i Hi. change (nth 2 (blobs0 a0s path) []) with (guard_bytes a_draw) in Hi |- *.
      rewrite Z.add_0_l in KB. apply KB. rewrite length_guard_bytes in Hi. exact Hi.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem full_grow : forall K j buf cap,
    (cap < 2 ^ 26)%Z ->
    (forall nb, at_loop K (S j) nb (2 * cap) cap) ->
    at_full K j buf cap.
  Proof.
    intros K j buf cap Hcap26 HLOOP A vm vals R M HL SL HR HK HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0. destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    assert (Hj : (Z.of_nat j <= 9)%Z).
    { destruct (Z_lt_ge_dec (Z.of_nat j) 10) as [|Hge]; [lia|]. exfalso.
      pose proof (Z.pow_le_mono_r 2 10 (Z.of_nat j) ltac:(lia) ltac:(lia)). change (2 ^ 10)%Z with 1024%Z in *. lia. }
    unfold V2ReadLoop.modelk.
    (* [comment removed for export] *)
    run_blk_keep (SCR [false] [] []) 41%nat.
    { cbn [sc_denot branch_taken edenot ev ENV V2Open.ENV]. unfold bv_eqb. rewrite u_srl64. rewrite P8, !u_small by lia.
      change (26 mod 64)%Z with 26%Z. rewrite Z.div_small by lia. reflexivity. }
    cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    destruct g_itin1 as (_ & _ & CAP2 & _ & _ & _ & VLK1 & KNM).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (R10 : getr Rc 10 = Z_to_bv 64 (2 * cap)) by (regv HR (10 : reg); cbn [edenot ev ENV V2Open.ENV]; rewrite P8; apply md_mul_Z);
      assert (R1 : getr Rc 1 = Z_to_bv 64 0x17910) by (regv HR (1 : reg); reflexivity);
      assert (R4 : getr Rc 4 = Z_to_bv 64 0x56270) by (regv HR (4 : reg); reflexivity);
      assert (R2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 128))
        by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V2Open.ENV];
            rewrite P0; first [reflexivity | f_equal; lia])
    end.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (EQcfg : mkst Rc (Z_to_bv 64 0x3c370) M (seg_rom RSEGS) = mkst Rc al_malloc_pc M al_rom)
        by (rewrite AL_malloc, AL_rom; reflexivity); rewrite EQcfg; clear EQcfg end.
    rewrite <- AL_segs.
    set (md := mkModelC (fdsk path cap) vm stdin0 fs0 None (Some tid) None).
    pose proof (Z.pow_le_mono_r 2 (Z.of_nat j) 9 ltac:(lia) Hj) as HP9. change (2 ^ 9)%Z with 512%Z in HP9.
    assert (Hcap25 : (cap <= 2 ^ 25)%Z) by (rewrite Hcapj; clear -HP9; lia).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (alloc_margin_le (2 * cap)) as HMG.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (ai_malloc_sure fx0 A M md Rc (2 * cap) (need_k FUZZ_CALLS j) (need_b FUZZ_BMAX j cap)
              (Z_to_bv 64 0x17910) sp0 [a0s; path] envv K HI) end.
    - constructor; reflexivity.
    - change (m_kernel md) with a_kernel. change (m_vmmaps md) with vm.
      exact (vm_resv_incl _ _ vm Hres Hisp).
    - apply AL_env. exact HE.
    - exact R10.
    - clear -Hcap25 Hc0. lia.
    - change (m_vmmaps md) with vm. exact Hroom.
    - unfold need_k. clear -Hj HFC0. lia.
    - unfold need_b. clear -Hcap25 Hc0 HMG Hj HFB0. lia.
    - unfold ROOM_NMAX. clear -Hcap25. lia.
    - exact R1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite R4. symmetry. exact AL_tp.
    - rewrite R2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, R2, u_small by lia. lia.
    - rewrite R2, u_small by lia. lia.
    - (* [comment removed for export] *)
      intros a Ha. rewrite R2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V2Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeG A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - (* [comment removed for export] *)
      intros A' m' vm' regs' res HI' Ha0 Hcs Hnz Hl0 Hl1 Hlq' Hnew Hfr Hlm Hgr Hvl' Htop' Hisp' Hres' Hmb' Hroom'.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop', Hvl', Hisp', Hres', Hmb'. rewrite Htop in Htop'.
      unfold md. rewrite with_vmmaps_C. clear md.
      pose proof (u64_range res) as Hrr. pose proof (u64_range buf) as Hbr0.
      (* [comment removed for export] *)
      assert (Hbr : buf <> res) by (intros Heq; rewrite <- Heq in Hl0; rewrite Hl in Hl0; discriminate Hl0).
      assert (Hlbuf' : live A' buf = Some cap) by (rewrite (Hlq' buf Hbr); exact Hl).
      assert (HE' : env_ok sp0 mem0 m').
      { apply (env_ok_alloc A A' M m' vm vm' HE HI Htop HI' Htop'). intros a H1 H2 H3 H4. apply Hfr; try assumption.
        rewrite R2, u_small by lia. exact H4. }
      destruct (ai_live_hull A' m' vm' res (2 * cap) HI' Hl1) as (_ & Hres16 & Hend & HbytesN).
      pose proof (round16_ge (2 * cap)) as Hr2.
      assert (Hres31 : (0x77000 <= bv_unsigned res)%Z) by (apply (live_big_lo sp0 Hvsp AL_grant A' m' vm' res (2 * cap) HI' Hl1); lia).
      assert (HsomeN : forall x : word, (bv_unsigned res <= bv_unsigned x < bv_unsigned res + 2 * cap)%Z -> m' x <> None).
      { intros x Hx. destruct (HbytesN (bv_unsigned x - bv_unsigned res)%Z ltac:(lia)) as (_ & Hs & _ & _).
        unfold at_ in Hs. replace (bv_unsigned res + (bv_unsigned x - bv_unsigned res))%Z with (bv_unsigned x) in Hs by lia.
        rewrite Z_to_bv_bv_unsigned in Hs. exact Hs. }
      assert (Hfl : Z.of_nat (length (firstn (Z.to_nat cap) data)) = cap) by (rewrite length_firstn; unfold L in HcapL; lia).
      assert (HB' : bytes_at m' (bv_unsigned buf) (firstn (Z.to_nat cap) data)).
      { intros i Hi. rewrite Hfl in Hi. unfold bytes_at in HB. rewrite <- (HB i ltac:(rewrite Hfl; exact Hi)).
        pose proof (Hlm buf cap i Hl ltac:(lia)) as Hq. unfold at_ in Hq. exact Hq. }
      pose proof (ai_live_disjoint A' m' vm' res (2 * cap) buf cap HI' Hl1 Hlbuf' ltac:(intros Heq; apply Hbr; symmetry; exact Heq)) as Hdisj.
      pose proof (round16_ge cap) as Hr1.
      (* [comment removed for export] *)
      set (vals2 := vals ++ junk_vals regs').
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (A51 : vals_ev vals2 51 = res).
      { subst vals2. replace 51%nat with (length vals + 10)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r.
        unfold junk_vals, vals_ev. rewrite (nth_map_seq_gen _ 32 0 10) by lia. cbn [Nat.add]. rewrite <- Ha0. reflexivity. }
      assert (SL2 : slots vals2 buf cap cap) by (subst vals2; apply (slots_app sp0 a0s path envv tid data vals); [rewrite HL; lia | exact SL0]).
      destruct SL2 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG vals sr Rc regs' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs) as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2. change (sr_after_call_j g_sr1 KEPT_AL 41) with g_srM in HR2. clear HR. rename HR2 into HR.
      assert (HK2 : know_ok RSEGS (ENV vals2) m' g_knOK).
      { unfold g_knOK. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]]].
        * cbn [kentry_ok edenot ev ENV V2Open.ENV]. rewrite A51. lia.
        * cbn [kentry_ok edenot ev ENV V2Open.ENV]. rewrite A51. split; [lia | exact Hres16].
        * cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot ev ENV V2Open.ENV]. rewrite A51. split; [lia|].
          intros d m Hd Hm. apply store_ok_of_all; [rewrite u_small by lia; lia|].
          intros x Hx. rewrite u_small in Hx by lia. unfold wview.
          destruct (m' x) eqn:EM; [discriminate | exfalso; exact (HsomeN x ltac:(lia) EM)].
        * cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev ENV V2Open.ENV].
          rewrite Q0, A51. right. lia.
        * rewrite <- KNM. subst vals2.
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            eapply (know_after_allocG A A' vals M m' vm vm' regs' kn ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK1) HK HI Htop HI' Htop') end.
          -- intros a H1 H2 H3 H4. apply Hfr; try assumption. rewrite R2, u_small by lia. exact H4.
          -- exact Hgr. }
      clear HK. rename HK2 into HK. clearbody vals2. clear KW R10 R1 R4 R2.
      (* [comment removed for export] *)
      run_blk_keep (SCR [false; false] [] []) 73%nat.
      { cbn [sc_denot branch_taken edenot ev ENV V2Open.ENV]. rewrite Q8. unfold bv_eqb. rewrite !u_small by lia. apply Z.eqb_neq. lia. }
      cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      (* [comment removed for export] *)
      set (bs0 := firstn (Z.to_nat cap) data) in *.
      assert (MC : mcH m' res buf cap bs0).
      { constructor; try lia.
        - apply (bytes_at_rdn m' (bv_unsigned buf) bs0 ltac:(lia) ltac:(lia)) in HB'. rewrite Z_to_bv_bv_unsigned in HB'. exact HB'.
        - apply store_ok_of_all; [lia|]. intros x Hx. unfold wview.
          destruct (m' x) eqn:EM; [discriminate | exfalso; exact (HsomeN x ltac:(lia) EM)]. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = Z_to_bv 64 0x1792c) by (regv HR (1 : reg); reflexivity);
        assert (B10 : getr Rc 10 = res) by (regv HR (10 : reg); cbn [edenot ev ENV V2Open.ENV]; exact A51);
        assert (B11 : getr Rc 11 = buf) by (regv HR (11 : reg); cbn [edenot ev ENV V2Open.ENV]; exact Q6);
        assert (B12 : getr Rc 12 = Z_to_bv 64 cap) by (regv HR (12 : reg); cbn [edenot ev ENV V2Open.ENV]; exact Q8);
        destruct (ref_memcpy m' res buf cap bs0 (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x1792c)
                    ltac:(apply ret_ok_even; reflexivity) A1 B10 B11 B12) as (Rm & Hms & Hkeep);
        clear A1 B10 B11 B12
      end.
      replace (Z_to_bv 64 275580) with (0x4347c : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
      set (M2 := wbytes m' res bs0).
      assert (OUT2 : forall x : word, ~ (bv_unsigned res <= bv_unsigned x < bv_unsigned res + cap)%Z -> M2 x = m' x).
      { intros x Hx. subst M2. apply wbytes_outside; lia. }
      assert (HI2 : ainv A' M2 vm').
      { apply (ainv_frame_driver sp0 Hvsp AL_glob AL_grant A' m' M2 vm' HI' Htop'); [| apply wbytes_grows |].
        - intros a Ha. right; right. exists res, (2 * cap)%Z. split; [exact Hl1|].
          destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res)); [exfalso; apply Ha; apply OUT2; lia|].
          destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res + cap)); [lia | exfalso; apply Ha; apply OUT2; lia].
        - intros a Ha HM2. destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res)); [rewrite <- OUT2 by lia; exact HM2|].
          destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res + cap)); [apply HsomeN; lia | rewrite <- OUT2 by lia; exact HM2]. }
      assert (HE2 : env_ok sp0 mem0 M2).
      { destruct HE' as (E1 & E2 & E3). split; [|split].
        - intros a Ha. rewrite OUT2 by lia. apply E1. exact Ha.
        - intros a H1 H2. rewrite OUT2 by lia. apply E2; assumption.
        - intros a Ha. rewrite OUT2 by lia. apply E3. exact Ha. }
      assert (HBres : bytes_at M2 (bv_unsigned res) bs0).
      { intros i Hi. subst M2. rewrite wbytes_inside by (rewrite ?u_small by lia; lia). rewrite !u_small by lia. do 2 f_equal. lia. }
      (* [comment removed for export] *)
      destruct g_itin2 as (_ & _ & VLB & _ & SR3 & KN3 & VLK3).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path)) sr Rc Rm callee_kept ltac:(rewrite HL2; exact VLB) HR Hkeep callee_kept_no0) as HR3 end.
      rewrite HL2 in HR3. lazymatch type of HR3 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR3 end.
      clear HR Hkeep.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_ok_call RSEGS (ENV vals2) m' M2 [] 0 0 IHI 0x45000) as KC;
        specialize (KC ltac:(cbn [ev ENV V2Open.ENV]; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
        specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HK3; clear KC
      end.
      specialize (HK3 ltac:(intros x Hnt; apply OUT2; unfold touched, IHI, WIN in Hnt; cbn [ev ENV V2Open.ENV] in Hnt; rewrite Q0 in Hnt; lia)
                      ltac:(intros x _ Hx; apply (wbytes_grows bs0 m' res); exact Hx)
                      ltac:(intros m a k H1 H2; apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2])).
      lazymatch type of HK3 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK3 end. clear HK.
      pose proof (env_app_know RSEGS vals2 (junk_vals Rm) (blobs_ev (blobs0 a0s path)) M2 _ ltac:(rewrite HL2; exact VLK3) HK3) as HK. clear HK3.
      rename HR3 into HR.
      set (vals3 := vals2 ++ junk_vals Rm) in *.
      assert (HL3 : length vals3 = 105%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (SL3 : slots vals3 buf cap cap) by (subst vals3; apply (slots_app sp0 a0s path envv tid data vals2); [rewrite HL2; lia | repeat split; assumption]).
      assert (R51 : vals_ev vals3 51 = res) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact A51).
      clearbody vals3. clear Q0 Q1 Q2 Q5 Q6 Q7 Q8. destruct SL3 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
      change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
      clearbody M2. clear MC HB'.
      (* [comment removed for export] *)
      run_blk_keep scr0 105%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      destruct g_itin3 as (_ & _ & VLK4 & KNL & IDL). apply pair_equal_spec in IDL as [MIS MISS].
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (F10 : getr Rc 10 = buf) by (regv HR (10 : reg); cbn [edenot ev ENV V2Open.ENV]; exact Q6);
        assert (F1 : getr Rc 1 = Z_to_bv 64 0x17934) by (regv HR (1 : reg); reflexivity);
        assert (F4 : getr Rc 4 = Z_to_bv 64 0x56270) by (regv HR (4 : reg); reflexivity);
        assert (F2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 128))
          by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V2Open.ENV];
              rewrite Q0; first [reflexivity | f_equal; lia])
      end.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals3) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                        _ _ _ d m HK eq_refl Hd Hm) as KW end.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (EQcfg : mkst Rc (Z_to_bv 64 0x3c230) M2 (seg_rom RSEGS) = mkst Rc al_free_pc M2 al_rom)
          by (rewrite AL_free, AL_rom; reflexivity); rewrite EQcfg; clear EQcfg end.
      rewrite <- AL_segs.
      set (md := mkModelC (fdsk path cap) vm' stdin0 fs0 None (Some tid) None).
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      eapply (ai_free_l fx0 A' M2 md Rc buf (Z_to_bv 64 0x17934) sp0 [a0s; path] envv K HI2) end.
      + constructor; reflexivity.
      + change (m_kernel md) with a_kernel. change (m_vmmaps md) with vm'.
        exact (vm_resv_incl _ _ vm' (vm_resv_step _ _ _ _ Hres Hres' Hmb') (eq_trans Hisp' Hisp)).
      + apply AL_env. exact HE2.
      + exact F10.
      + right. exists cap. exact Hlbuf'.
      + exact F1.
      + apply AL_ret. apply ret_ok_even. reflexivity.
      + rewrite F4. symmetry. exact AL_tp.
      + rewrite F2. rewrite u_small by lia.
        replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
      + change (m_vmmaps md) with vm'. rewrite Htop', F2, u_small by lia. lia.
      + rewrite F2, u_small by lia. lia.
      + intros a Ha. rewrite F2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
        * pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
          unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V2Open.ENV] in Hst. rewrite Q0 in Hst.
          replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
          rewrite Z_to_bv_bv_unsigned in Hst.
          pose proof (store_ok_all RSEGS M2 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
          rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
        * intros Ho. destruct (ownedA_rangeG A' M2 vm' a HI2 Htop' Ho); lia.
        * intros Hro. apply AL_ro in Hro. lia.
        * intros Hrw. apply AL_rw in Hrw. lia.
      + (* [comment removed for export] *)
        intros A'' m'' vm'' regs'' HI'' Hcs'' Hlbuf'' Hlq'' Hfr'' Hlm'' Hgr'' Hvl'' Htop'' Hisp'' Hres'' Hmb'' Hvlb'' Hroom''.
        rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm' in Htop'', Hvl'', Hisp'', Hres'', Hmb'', Hvlb'', Hroom''. rewrite Htop' in Htop''.
        unfold md. rewrite with_vmmaps_C. clear md.
        assert (Hlres'' : live A'' res = Some (2 * cap)%Z) by (rewrite (Hlq'' res ltac:(intros Heq; apply Hbr; symmetry; exact Heq)); exact Hl1).
        assert (HS'' : side A'' vm'' m'' res (2 * cap) (S j)).
        { split; [|split; [|split]].
          - split; [exact HI''|]. split; [exact Hlres''|]. split.
            + intros q Hq. destruct (Z.eq_dec (bv_unsigned q) (bv_unsigned buf)) as [Heq|Hne].
              * assert (q = buf) by (apply bv_eq; exact Heq). subst q. exact Hlbuf''.
              * assert (Hqb : q <> buf) by (intros HH; apply Hne; rewrite HH; reflexivity).
                rewrite (Hlq'' q Hqb), (Hlq' q Hq). apply Hlq. exact Hqb.
            + (* [comment removed for export] *)
              destruct (need_grow FUZZ_CALLS FUZZ_BMAX j cap) as (EK & EB).
              pose proof (need_lo FUZZ_CALLS FUZZ_BMAX (S j) (2 * cap) HFC0 ltac:(clear -HFB0; lia)
                            ltac:(rewrite Nat2Z.inj_succ; clear -Hj; lia) ltac:(clear -Hcap25 Hc0; lia)) as (HK1 & HB1).
              apply (aroom_mono A'' vm'' _ _ _ _ (Hroom'' _ _ Hroom')); clear -EK EB HK1 HB1 HMG HFC0 HFB0; lia.
          - split; [rewrite Hvl'', Hvl'; exact Hvl|]. split; [exact Htop''|]. split; [rewrite Hisp'', Hisp'; exact Hisp|].
            exact (vm_resv_step _ _ _ _ (vm_resv_step _ _ _ _ Hres Hres' Hmb') Hres'' Hmb'').
          - apply (env_ok_alloc A' A'' M2 m'' vm' vm'' HE2 HI2 Htop' HI'' Htop''). intros a H1 H2 H3 H4. apply Hfr''; try assumption.
            rewrite F2, u_small by lia. exact H4.
          - split; [rewrite Hcapj, Nat2Z.inj_succ, Z.pow_succ_r by lia; lia | rewrite Nat2Z.inj_succ; lia]. }
        assert (HB'' : bytes_at m'' (bv_unsigned res) (firstn (Z.to_nat cap) data)).
        { intros i Hi. fold bs0. fold bs0 in Hi. rewrite <- (HBres i Hi).
          pose proof (Hlm'' res (2 * cap)%Z i Hlres'' ltac:(subst bs0; lia)) as Hq. unfold at_ in Hq. exact Hq. }
        (* [comment removed for export] *)
        set (vals4 := vals3 ++ junk_vals regs'').
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (regs_after_allocG vals3 sr Rc regs'' ltac:(rewrite HL3; vm_compute; reflexivity) HR Hcs'') as HR4 end.
        rewrite HL3 in HR4. fold vals4 in HR4.
        lazymatch type of HR4 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR4 end.
        clear HR. rename HR4 into HR.
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          pose proof (know_after_allocG A' A'' vals3 M2 m'' vm' vm'' regs'' kn ltac:(rewrite HL3; lia) Q0 ltac:(rewrite HL3; exact VLK4) HK HI2 Htop' HI'' Htop'') as HK4 end.
        specialize (HK4 ltac:(intros a H1 H2 H3 H4; apply Hfr''; try assumption; rewrite F2, u_small by lia; exact H4)
                        ltac:(intros a Ha; destruct (Hgr'' a Ha) as [Ho|Hs]; [right; left; exact Ho | right; right; exact Hs])).
        lazymatch type of HK4 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK4 end.
        fold vals4 in HK4. clear HK. rename HK4 into HK.
        assert (HL4 : length vals4 = 137%nat) by (subst vals4; rewrite length_app, junk_vals_length, HL3; reflexivity).
        assert (SL4 : slots vals4 buf cap cap) by (subst vals4; apply (slots_app sp0 a0s path envv tid data vals3); [rewrite HL3; lia | repeat split; assumption]).
        assert (S51 : vals_ev vals4 51 = res) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact R51).
        clearbody vals4. clear Q0 Q1 Q2 Q5 Q6 Q7 Q8. destruct SL4 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
        apply (HLOOP res A'' vm'' (map (edenot (ENV vals4)) g_rvl) regs'' m'').
        * rewrite length_map. reflexivity.
        * unfold V2ReadLoop.slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth g_rvl rvl9 app tl cap2_x edenot ev ENV V2Open.ENV].
          rewrite Q8, md_mul_Z. repeat split; assumption || reflexivity.
        * change (ENV (map (edenot (ENV vals4)) g_rvl)) with (xenv (ENV vals4) g_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals4) g_rvl idb _ (fun k => eq_refl) srb sr_L _ HR eq_refl eq_refl)) end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * change (ENV (map (edenot (ENV vals4)) g_rvl)) with (xenv (ENV vals4) g_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals4) g_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply (kwr_buf sp0 mem0 lim Hvsp data AL_grant A'' vm'' m'' res (2 * cap) (S j) _ (EVar 51) HS'').
          cbn [edenot ev ENV V2Open.ENV]. exact S51.
        * exact HS''.
        * exact HB''.
        * lia.
        * exact HcapL.
  Qed.
End Grow.
