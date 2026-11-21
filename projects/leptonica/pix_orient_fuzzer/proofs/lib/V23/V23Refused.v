(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the m_channel_reader premise; the recorded proofs of rf_segH, rf_segG, rf_segF, rf_segE, rf_segD, rf_segC and rf_segB, made over the old 8 MiB launch stack window, replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped; the memcpy tactics' call and return addresses corrected to this binary's; the exit record's last fields proved in this unit's field order). *)
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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibTail.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare SpecConsts MmapSim AllocSim FileSim AgentLib SymExec ShapeLaws LibWritev RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23ExitBase V23StdioDefs V23Exit V23LibStdioCall V23MemcpyBase V23Memcpy V23MainEntry V23MemPreds V23ReadErr_defs V23ReadErr_tail V23ReadErr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Refused_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Refused () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib3V23:V23Refused5PRE14C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused4DIG8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused5SUF16C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic8f_equal2K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgKTgt_pix_orient_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~____________________I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23ReadErr_tail3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3V23<V23StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib3V23;V23ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib3V23<V23StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX>edenot_add_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib6Common9CliDriver6SymRun=ext_val_zx_idC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3V23<V23StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K59OSSVerify5KrLib3V23<V23StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib3V237V23Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V237V23Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib6Common9CliDriver8SymDrive5kreadC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib6Common9CliDriver8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23ReadErr_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23ReadErr_defs5STOPSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23ReadErr_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4srH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4knH0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs3knHC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:flat_introC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib6Common9CliDriver7LibTail9rdn_app_ZC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_wZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_varC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_addC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;ShapeLawsV2>t_exit_has_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused7rf_segHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23LibStdioCall@stdio_call_soundC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib3V238V23Reloc9v23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23RelocImg8v23_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs3srGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs3knGC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3V23?V23Refused_defs4srG0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4knG0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused;SUF16_wordsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused9DIG8_wordC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused;PRE14_wordsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec;msg_refusedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23RefusedAmsg_refused_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs<itinerary_rfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs2rBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs2rCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs2rDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs2rEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs2rFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs2rGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4scRFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs2rHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:SpecConstsArw_bytes_max_ge17C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib:wbytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs5logM1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs5logM4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs5logM5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX8kimg_rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V239V23Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun;carry_afterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused=memcpy5_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused7rf_segGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib3V23?V23Refused_defs4srF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4knF0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused9suf16_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs3knFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused=memcpy4_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused7rf_segFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4srE0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs3knDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused:DIG8_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs3knEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused7rf_segEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4srD0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs3knCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused7rf_segDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4srC0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs4knC0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused=memcpy1_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused7rf_segCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs5srRF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23ReadErr_defs5knRE0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused9pre14_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23Refused_defs3knBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23:V23ReadErr9evRE_junkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC4ELinuxProcessSemantics5Riscv3Sem5alu64C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC59OSSVerify5KrLib6Common8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib6Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib3V23<V23MainEntry@regs_ok_by_indexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry8all_regsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib3V23:V23ReadErr6valsREC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23:V23ReadErr:valsRE_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23:V23ReadErr9know_okREC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused7rf_segBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23:V23Refused9regs_okRFC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition PRE14 : list byte := s2b "cli: input >= "%string.
Definition DIG8 : list byte := s2b "67108864"%string.
Definition SUF16 : list byte := s2b " bytes, refused"%string ++ [Z_to_bv 8 10].

Section VP1.
Lemma msg_refused_split : msg_refused = PRE14 ++ DIG8 ++ SUF16.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP1"] "p;1p;3p;2p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000np4p710p1001Kp4p710p8g001ij10Tg002Nj15Tg002lj13Tg003Oj12Tg003oj31Tg004Lj24Tg004f#0#0#0#5#3R1#2g005Kg006Dg007<511511'4o"). Qed.
End VP1.

Section VP2.
Lemma PRE14_words :
  word_to_le_bytes 8 (Z_to_bv 64 8101528366825958499) ++ word_to_le_bytes 4 (Z_to_bv 64 1042314357)
  ++ word_to_le_bytes 2 (Z_to_bv 64 8253) = PRE14.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP2"] "h01Hh12b1h22b2h31np;1p;3p;2p;:g001ij17Tg002Nj1DTg002lj1=Tg003Oj1JTg0085j1Hj30Tg008Uj19Tg009:j12Tg009Xj1ITg00:8j3>Tg00:Rj2?Tg00;<j3GTg004Lj2ETg00;`l:6Tg00<>j1<Tg00<]j2@Tg00=Cj2ATg003oj3CTg00>Kj2BTg00?>j3FTf0R0#7#7p=1%90#9p=:%70#9p=4%90#7p=3f3R1f2R2f1R3/B03Fp=5%20,B39F12p=;g00?aR41?30'Ep=8g004fR5#7#1R6#DR7#=R8%J8R9P9%H8R:P7%95R5#7R;#1#:#2R<P7%95R5#7R=#7#1R>#4#3#:#3R?#4#3#3#4R@#1#3#1#1RA#1#:#3#3RB#4#3#3#4RC#4#3#:#1RD#4#3#1#:#2REC5RFP7P<P7P<C5R<P7%9;R;#9RG#1#2RHP7PDC;RDP7%7;#4#2R;P7PCC;RCP7%3=R=#2RIP7PBC;RBP7%16R6#2RJP7PAC;RAP7P;P7P@C;R@P7%3G#2RGP7P?C;R?P7%2>R>P7P>C5R>P7%9=#2RKP7%95R5#3RL#1#3#1#1RM#4#:#4#1RN#4#:#4#4#2ROC5RPP7%7=#2R=P7PNC;RNP7PJP7PMC;RMP7%2LRLP7PLC5RLP7%45#2R5P7%76R6#7#:#:#4#2RQC5RRP7PJP7PJC5RJ%I8RS508RT508RU508RV508RW508RX508RY508RZ508R[508R\508R]508R^508R_508P7PHP7PHC5RHP7P;P7P;C5R;P7PIP7PIC5RIP7PGP7PGC5RGP7PKP7PKC5RKP7P=P7P=C5R=P7P5P7P5C5R5=08TR`908LRa908JRb508Rc508Rd908>Re508Rf908;Rg908JRh508Ri508Rj508g00@?Rk%=0Rl%=3Rmg00@]%=2?>301?121?135>4Rn[1?231?205>4%=1?>23[R4f4#=?>12\nAG230P0n2001000000120000000W2W1W3R3P4^2m^1l^3kRkP0P7PFP<187<O4b0P8P9P9P:PDPHP_PjP3PkP0P7PDPH187HO4b0P8P9P9P:PCP;P^PiP3PkP0P7PCP;187;RCO4b0P8P9P9P:PBPIP]PhP3PkP0P7PBPI187IO4b0P8P9P9P:PAPJP\PgP3PkP0P7PAPJ187JRAO4b0P8P9P9P:P@P;P[PfP3PkP0P7P@P;PCO4b0P8P9P9P:P?PGPZPeP3PkP0P7P?PG187GO4b0P8P9P9P:P>P>PYPdP3PkP0P7P>P>187>O4b0P8P9P9P:PPPKPXPcP3PkP0P7PPPK187KO4b0P8P9P9P:PNP=PWPbP3PkP0P7PNP=187=O4b0P8P9P9P:PMPJPVPaP3PkP0P7PMPJPAO4b0P8P9P9P:PLPLPUP`P3PkP0P7PLPL187LO4b0P8P9P9P:PRP5PTPTP3PkP0P7PRP51875O4b0P8P9P9P:PJPJPSPSP3PkP0P7PJPJPAO4b01E9SM:6M:6M:6M:6M:6M:6M:6M:6M:6M:6M:6M:6M:6M:6g00A8#<#<RS#<#<RA#<#<#<#<%D6R6/@E'A1@6O,AA1@6Q,AS5C85C8g005K5>9do"). Qed.
End VP2.
Section VP3.
Lemma DIG8_word : word_to_le_bytes 8 (Z_to_bv 64 3762256352692483894) = DIG8.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP3"] "h01Hh12b1h22b2h31np;1p;3p;2p;:g001ij16Tg002Nj1?Tg002lj1:Tg003Oj1HTg0085j1Gj31Tg008Uj15Tg009:j12Tg009Xj1ATg00:8j3<Tg00:Rj24Tg00;<j3FTg004Lj2@Tg00;`l:9Tg00<>j18Tg00<]j2DTg00=Cj2CTg00>Kj2BTg00?>j3ETf0R0#6#6p=0%50#5p=7%60#5p=>%50#6p==f3R1f2R2f1R3/B03Ep=3g00?aR4/@0p=;g004fR5#6#0R6#?R7#:R8%H8R9P9%G8R:P7%55R5#6R;#5R<#5R=#6#2R>P7%0<R<#0#7#>#=R?#0#7#=#0R@#0#7#=#0RA#0#7#0#0RB#0#7#0#>RC#0#7#>#7RD#0#7#>#=#2REC3RFP7P>P7P>C3RGP7%5=#2R=P7%2DC3RDP7%0;R;#5#2RHP7%2CC3RCP7%6;#2R;P7%2BC3RBP7%=5#0#2R5P7%2AC3RAP7P5P7%2@C3R@P7P>P7%2?C3R?P7%2<R<P7P<C3R<%A8R>518RI518RJ518RK518RL518RM518RN518P7P=P7P=C3R=P7PHP7PHC3RHP7P;P7P;C3R;P7P5P7P5C3R5A18GIRO9185RP518RQ518RR518RS518g00@?RT%:0RU%:3RVg00@]%:2?<30141214135<4RW[142314205<4%:1?<23[R4f4#:?<12\WAF230P0n2001000000120000000W2W1W3R3P4^2V^1U^3TRTP0P7PFPG147G#;RFO4b0P8P9P9P:PDP=PNPSP3PTP0P7PDP=147=#;O4b0P8P9P9P:PCPHPMPRP3PTP0P7PCPH147H#;O4b0P8P9P9P:PBP;PLPQP3PTP0P7PBP;147;#;O4b0P8P9P9P:PAP5PKPPP3PTP0P7PAP51475#;RAO4b0P8P9P9P:P@P5PJPOP3PTP0P7P@P5PAO4b0P8P9P9P:P?PGPIPIP3PTP0P7P?PGPFO4b0P8P9P9P:P<P<P>P>P3PTP0P7P<P<147<#;O4b01@9>M:9M:9M:9M:9M:9M:9M:9M:9g00A8#8#8#8#8#8#8#8#8%66#0#?/DE'Cg006D5<9do"). Qed.
End VP3.
Section VP4.
Lemma DIG8_bytes :
  word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 55) ++ word_to_le_bytes 1 (Z_to_bv 64 49)
  ++ word_to_le_bytes 1 (Z_to_bv 64 48) ++ word_to_le_bytes 1 (Z_to_bv 64 56) ++ word_to_le_bytes 1 (Z_to_bv 64 56)
  ++ word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 52) = DIG8.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP4"] "h01Hh12b1h22b2h31np;1p;2p;3p;:g001ij12Tg002Nj1?Tg002lj15Tg003Oj1ETg0085j1Cj34Tg008Uj1;Tg009:j19Tg00>Kj27Tg00?>j36Tg009Xj1ATg00:8j3:Tg00:Rj20Tg00;<j3DTg004Lj2@Tg00;`l:1Tg00<>j1BTg00<]j28Tg00=Cj2<Tg003oj33Tf0R0#2#2p=>g00?aR1/@0p==g004fR2#2#>R3#?R4#5R5%E5R6P6%C5R7%;2R2#2R8#;R9#;R:#2#9R;174;564R<P<%;:#9R:174:564R=%>8R8#;#9R>174>564R?%28#9R81748564R@%;2#2#>#9R21742564RA%>9#9R91749564RB%A5RC545RD945<RE945ARF545RG545RH545RI545RJPJg00@?RJ%50RKf1RL#5RMg00@]f2RN#5?:L0f3RO/0N10OL5:1RP[10NL10N05:1%5O?:NL[R1f4#5?:ON\PADNL0P0n2001000000120000000W2W1W3RNP1^2M^1K^3JRJP0P4P<P<104<#=O4b0RKP5P6P6P7P=P=PIPIPNPJP0P4P=P=104=#=O4b0P5P6P6P7P?P?PHPHPNPJP0P4P?P?104?#=O4b0P5P6P6P7P@P@PGPGPNPJP0P4P@P@104@#=O4b0P5P6P6P7PAPAPFPFPNPJP0P4PAPA104A#=O4b0RFP5P6P6P7PAPAPEPEPFP5P6P6P7P<P<PDPDPKP5P6P6P7PBPBPCPCPNPJP0P4PBPB104B#=O4b01@6CM:1M:1M:1M:1M:1M:1M:1M:1g00A8#BRC%23#>#?R3/8;'<R;183:,<C183>,<C1838,<C1832,<CR21839,<C935;9352535535535535535g006D5:6do"). Qed.
End VP4.
Section VP5.
Lemma SUF16_words :
  word_to_le_bytes 8 (Z_to_bv 64 2318354787771965984) ++ word_to_le_bytes 8 (Z_to_bv 64 748834984615634290) = SUF16.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP5"] "h01Hh12b1h22b2h31np;1p;3p;2p;:g001ij13Tg002Nj1CTg002lj1>Tg003Oj1LTg0085j1Jj30Tg009:j1<Tg008Uj15Tg009Xj1KTg00:8j3@Tg00:Rj2ATg00;<j3ITg004Lj2GTg00;`l:2Tg00<>j1=Tg00<]j2ETg00=Cj2DTg003oj3HTg00>Kj2FTg00?>j3BTf0R0#3#3p=8%50#3p=?%50#5p=9%30#5p=1%50#3#3#5p=;%30#<p=:f3R1f2R2f1R3/F03Bp=4%<0,F39B12p=7g00?aR41A30'Gp=6g004fR5#3R6#8R7#CR8#>R9%L9R:P:%J9R;P8%87R7#<R<P8%37R7#3#?#9#8R=#1#9#8#9R>#1#;#1R?#1#9#1#8R@#1#9#;RA#1#?#8#?RB#3#1#8#8#:RCC4RDP8P<P8P<C4R<P8%55R5#8RE#1#:RFP8PBC7RBP8%55R5#;#<RGP8PAC7RAP8%35R5#?RH#:RIP8P@C7R@P8%5ERE#3RJ#5#<RKP8P?C7R?P8%15R5#5#<RLP8P>C7R>P8%56R6#?#:RMP8P=C7R=P8%:5R5P8%36R6#1#;#8RN#1#;#1RO#1#9#8#9RP#1#9#1#1RQ#1#;#?RR#1#;#1RS#3#9#;#:RTC4RUP8PKP8PSC7RSP8%5E#:REP8PRC7RRP8%5H#<RHP8PQC7RQP8PLP8PPC7RPP8PKP8POC7ROP8%:JRJP8PNC7RNP8%<6R6P8P6C4R6%K9RV509RW509RX509RY509RZ509R[509R\509R]509R^909<R_509R`509Ra509Rb509Rc509Rd509P8PFP8PFC4RFP8PGP8PGC4RGP8PIP8PIC4RIP8PKP8PKC4RKP8PLP8PLC4RLP8PMP8PMC4RMP8P5P8P5C4R5P8PEP8PEC4REP8PHP8PHC4RHP8PJP8PJC4RJ=09WRe909KRf909LRg509Rh509Ri909KRj509Rk909<Rl509Rm509Rn509Ro509Rp509Rq509g00@?Rr%>0Rs%>3Rtg00@]%>2?@301A121A135@4Ru[1A231A205@4%>1?@23[R4f4#>?@12\uAI230P0n2001000000120000000W2W1W3R3P4^2t^1s^3rRrP0P8PDP<168<RDO4b0P9P:P:P;PBPFPdPqP3PrP0P8PBPF168FO4b0P9P:P:P;PAPGPcPpP3PrP0P8PAPG168GO4b0P9P:P:P;P@PIPbPoP3PrP0P8P@PI168IO4b0P9P:P:P;P?PKPaPnP3PrP0P8P?PK168KR?O4b0P9P:P:P;P>PLP`PmP3PrP0P8P>PL168LR>O4b0P9P:P:P;P=PMP_PlP3PrP0P8P=PM168MO4b0P9P:P:P;P<P<P^PkP3PrP0P8P<P<PDO4b0P9P:P:P;PUP5P]PjP3PrP0P8PUP51685O4b0P9P:P:P;PSPKP\PiP3PrP0P8PSPKP?O4b0P9P:P:P;PRPEP[PhP3PrP0P8PRPE168EO4b0P9P:P:P;PQPHPZPgP3PrP0P8PQPH168HO4b0P9P:P:P;PPPLPYPfP3PrP0P8PPPLP>O4b0P9P:P:P;POPKPXPeP3PrP0P8POPKP?O4b0P9P:P:P;PNPJPWPWP3PrP0P8PNPJ168JO4b0P9P:P:P;P6P6PVPVP3PrP0P8P6P61686O4b01G:VM:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2M:2g00A8#=#=#=#=#=#=#=#=RV%C7R7/EC'D1E7T,DV5H9g007<5@:do"). Qed.
End VP5.
Section VP6.
Lemma pre14_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x17cb1) 14 = Some PRE14.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP6"] "p;1p;2p;3p;4p100AWp4p70R0p100BEp4p7210p8P0p100Bap4p710p8g001ij11Tg002Nj1<Tg002lj1:Tg003Oj1FTg00C=j1DTg008Uj10Tg009:j12Tg00>Kj23Tg009Xj1?Tg0085j37Tg00C_j2>Tg004Lj2ETg00DAj1CTg00<]j2BTg00Dcj4@Tg00:8j3ATg00?>j3=Tg00<>j1;Tf0R0#1#1p=4f3R1f2R2f1R3/303=p=8f4R4A=123;70p=5A72309741p=9%;0#;p=6g004fR0#1#4R4#<R1#:R3#FR2#DR5P3P1%00R6#1R7#4#0#0#2R81318P3P1%07R7#0R8#4#2R91319P3P1%47#0#2R7P1P7C8R7P3P1%06R6#1R9#0#1R:#2R;P1P;C8P3P1%44R4#2R;P1P;C8R;P3P7P3P1%08#1#2R81318P3P1%19#4#2R91319P3P1%0:#2R91319P3P1%1:#2R:131:P3P;P3P1%06R6#0#1#2R:P1P:C8P3P1%16#0#2R61316%?3973;D5D9D5D5D5D5D9D9D5D5,>2'Eg00E[%14#<R4#:%C3U%10#0#0#0#0#0#4#0#1#0#0#1#4#0#2,B4g00A8#6#6#6#6#6#6#6C@g005K,>25A5do"). Qed.
End VP6.
Section VP7.
Lemma suf16_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x17cc1) 16 = Some SUF16.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP7"] "p;1p;2p;4p;3g001ij11Tg002Nj1<Tg002lj1:Tg003Oj1FTg00C=j1CTg009:j12Tg008Uj10Tg00>Kj25Tg009Xj1?Tg00C_j2>Tg004Lj2ETg00DAj1DTg00<]j2BTg00Dcj4ATg00:8j3@Tg00?>j3=Tg0085j39Tg00<>j1;Tf0R0#1#1p=3f3R1f2R2f1R3/503=p=7f4R4A=123;90p=6A92309941p=8%;0#;p=4g004fR0#1R4#3R1#<R3#:R2#FR5#CR6P2P3%31R1#2R7P3P7C7R7P2P3%00R8#3R9#1#0#1#2R:P3P:C7P2P3%08R8#0#3#0#2R:153:P2P3%18R8#0#1R:#1#2R;153;P2P3%09R9#1R;#0#2R<P3P<C7R<P2P3%18#0R8#0#2R=P3P=C7R=P2P3%04R4#0#3#2R>153>P2P7P2P3%18#2R8P3P8C7P2P<P2P3%09#1#2R9P3P9C7P2P3%0:#2R:153:P2P=P2P<P2P3%1;#2R;153;P2P3%14#2R41534%?2D6D6D8D6D8D8D6D8D6D6D8,>5'Eg00E[%11#<R1#:%D2U%10#0#0#0#0#0#3#0#0#1#3#3#0#2,B1g00A8#4#4#4#4#4#4#4#4CAg007<,>55@6do"). Qed.
End VP7.
Section VP8.
Lemma PRE14_len : length PRE14 = 14%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP8"] "p;2p;1g004Lj22Tg00<>j11Tf0#1#1p=0g00GBg00A8#0#0#0#0#0#0#0'2o"). Qed.
End VP8.
Section VP9.
Lemma DIG8_len : length DIG8 = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP9"] "p;1p;2g00<>j10Tg004Lj21Tg00GBg00A8#0#0#0#0#0#0#0#0'1o"). Qed.
End VP9.
Section VP10.
Lemma SUF16_len : length SUF16 = 16%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["VP10"] "p;2p;1g004Lj22Tg00<>j11Tf0#1#1p=0g00GBg00A8#0#0#0#0#0#0#0#0'2o"). Qed.
End VP10.

Section Refused.
  Variable sp0 : word.
  Ltac at_addr k H :=
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (bv_unsigned sp0 + k)%Z by lia; exact H end.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Hypothesis Hrd2 : m_channel_reader model = true.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let T : TSet := t_emit (W 2 msg_refused) (t_exit (exit_code 2) (m_fs model)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segH : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH0 R -> know_ok RSEGS (ENV BL vals) M knH0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x114be0) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knH ltac:(let i := kidx knH (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x1381d0), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [|split; [exact Hh|split; [exact Hlazy|]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knH ltac:(let i := kidx knH (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (1278416 - 168)%Z with 0x138128%Z.
        krd HK 0x138128%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * eexists; krd_solve HK.
      * atexit_solve ltac:(idtac; krd_solve HK).
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segG : forall vals R M,
    length vals = 199%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srG0 R -> know_ok RSEGS (ENV BL vals) M knG0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1143c4) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 199%nat.
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 4%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-548)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-546)%Z 8%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-538)%Z 8%nat Hw4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-530)%Z 8%nat Hw5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    assert (MSG : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + -560)) ((8 + (4 + 2)) + (8 + (8 + 8)))
                  = Some msg_refused).
    { rewrite msg_refused_split, <- PRE14_words, <- DIG8_word, <- SUF16_words.
      apply rdn_app_Z; [ | | lia | lia].
      - apply rdn_app_Z; [exact Hw0 | | lia | lia].
        apply rdn_app_Z; [at_addr (-552)%Z Hw1 | at_addr (-548)%Z Hw2 | lia | lia].
      - apply rdn_app_Z; [at_addr (-546)%Z Hw3 | | lia | lia].
        apply rdn_app_Z; [at_addr (-538)%Z Hw4 | at_addr (-530)%Z Hw5 | lia | lia]. }
    (* [comment removed for export] *)
    unfold T.
    replace (W 2 msg_refused) with (map (WriteEv (Z_to_bv 64 2)) (msg_refused ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_rf as (_ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG knG Rc Mc model scRF msg_refused []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG knG) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRF];
      change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. reflexivity.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      change 38%nat with ((8 + (4 + 2)) + (8 + (8 + 8)))%nat. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hrd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (rf_segH (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE14.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["Refused"] "h04__x1h17__arithh24__ffh38__varmaph45__with51xh61nh71yh82Hah96__sat3h:6__sat4h;1zh<1Hh=2H0h>1Mh?2P0h@1bhA1lhB1mhC1ohD4valsp%0p&0p;1p;2p;3p;4p;<p;8p;6p;Bp;7g001ij10Tg002Nj1dTg002lj1aTg003Oj1_Tg00C=k104Tg00Hmj2hTg00:8j3Fk108Tg009:j18Tg00:Rj27Tg00MMR0j2MTg00<>j1@Tg00<]j29k109Tg00=Cj2<Tg003oj3gTg00J1j2fTg00gLj3eTg008Uj1LTg017oj2[Tg03DiR1j31j2Qj1WTg00HMj2bTg01?OR2j1PTg03Ecj2lTg00Mij1oTg00O2j1ZTg00Qbj2YTg01:^j2KTg00OPj1XTg019Uj2;Tg01;gR3j24Tg004Lj2=Tg01M@j1^Tg01M^k407Tg01gZl<VTg009Xk103Tg01B;k202Tg01BYk101Tg01C7k100Tg01Cbj2~Tg01k6j3UTg01DEj3}Tg01P8j4OTg01Dhj2|Tg01EJj2{Tg01F6j3zTg01FUj4yTg01NAj4RTg03FXj8ETg00DAj1vTg01ILj2cTg01HKj2uTg01GoR4j2GTg01GGj2xTg01Hhj3tTg01Ioj3sTg02Y^j3jTg001Kj6HTg03G5j2kTg01eIj1\Tg01fRj1]Tg03H=j4iTg00Baj6rTg01ikl<qTg01jPlBpTg01h?k705Tg01hck806Tf0R5#0#0p=:%L5#Lp=2%L5#0p=5%05#0#0#0p=N%05#0#0#0#0#0#0#0p=>%05#Lp=6f4R6f3R7f2R8f1R9;153Fp=CA1678?195p=J1989=175p=`1495,98p=3g00?aR:?F95p=I1=:5p=Ag00GBR;P:P:P:P2P2f5R2P6P7P8P9P5M<qp=nP:P:P:P:P:P:P3P5P9P8P3P7P6P2f6f7f8f9MBpp=m1c:5p=?P9g025DR3g025cR<P<g026CR=P5g027JK05p=Bg024fR>/M5p=DP:P:P0P2P0P6P>P>P7P8P9P5M<Vp=wP:P9g026cP5COp=TP7P3P<P<P=P8P9P5L06p=Sg004fR3#0R0#0R?#0R@#0#:RA#dRB#aRC#_%d@#aRD$04\CREg00A8RF,h9p,3sp0RG5FCp,4SPloS00%23RH#2RI#2#2#2#2#2#5#:#N#>#>#>#8RJ17BGRK'Mp,4SPhiS01%0ARL#>#>#>#>#>#8RM,MK%_DRN%@F#@RO#@#@RP#@#@#@#@RQ%NH#6#5#2#5#6#5#5#6#:#5#:#N#2#5#5#6#5#5#6#6#5#2#:#6#5#:#2#8RH,9BRR'<RS%0I#:#5#N#6#2#6#:#6#2#6#6#8RI,9BRT,<PRU%2L#2#6#8RL,9B,<ORV5gDRW5gDRXPEp,2BLRY/f2R2g03I@RZ7e6P6%L@R[#L#NR\#8R],[KR^,9BR_P5DCXANPEA17_SR`1bDSS02#PRa,l_Rb;1WS03%oFRc%Z\R\'YRd,K2%XHRH,;2,<Q516%0[R[#5#:#ZRe,YcRf,K2%XIRI,;2,<P%6[#:#ZR[,YcRc,K2%XLRL,;2,<ODJ=FE5XCER2PEP`PbPU1bDUS04#PRD,lbPVDJRgP2PCPGPEP6PB17B5RG/4\PSC`A3BGePUA3BG[PVDJA16_SRG17B_R2=3BaRa;1U17Ba=3BDS05PVDCX@CP;PQPEA3BK\R\=16S14KeRh,9BRiPU14K[Rj,9BRkPVDJRl%P5Rm93B2Rn=1GU17Bn=3BDPVDCX6;P;PPPEPl%PQRD93B2Rn=1GU17BnRo=3BmPVDCX6;P:P^PEPlA3B5DRp=1GU17Bp%PPRp53BPVDCX;:P:14^DRqPEPl19BqRl=1GUA3B5pPVDCX;:PNPEA17\SR\?1iURG/QkA1`lURr14qpRs,9BRt'QPVPVPCPE\NRu%WG%WrPkPtPEPu\CRtP1P1PGPrPt\E/=1PNPE1Q\i1Q`lPUPUPCPu%W\%W`R\PiPl1=t\P:PC&09BR\P\PhPqPC\:/=\Rt1Ihq%8@R@,4^Ri,IhP:P:&08:RuP5X5:R1Pu1I95#^X7:X5:RrPhPh%AhPqPiP1P1P1P:P:g02G<1495H07#AXB:X6:RhP^P^%A^PDP@P1P1%AmX5;R;PQP@%A@EnM:mRmM<Vg02F4RD$03Rv%_DRD202:9Rw&01:Rx&00:RyP:1~:3R3%?e5U:g02G`Rz%?]9}:3R{%?@5U:R|CO'B1|y=R=P5P8g027jR}g028JR~'=1{58=F}~dAz:>9CyR~b2b3b4X0:145e1[5]/4@Re'I^0:P5PKO1R}b1CRGEGE1=NUGEGEP:PCP\P\PjPsPt1Ijs%8?R?,4iRt,IjP:P:PuP1PuPrPjPj%AjPsPtP1P1P1PhPqPiPmPpP?P1P1P;PPP?%A?EnM:mM<VPvPDPwPxP:%?[9U:3Pz%??9U:|CO,ByP=P~b2b3b4X0:145[14e?'I^0:P}b1CRGEGE1=NVGE17Bl%Dq%DiP11M95#^X7:X5:1=:>PqPiPmEwPvPDPwPxPy%?J/T3,ByRl%v<R<1c:>RN/T|,ByCSP=P~b2b3b4X0:1MJ5RJ1[9]R]/4@R@#D[^0:P5PKQ00O2R}b1CR%80R0%8ARA'uR?,Gq1Gi?P:P:P4P1P41G95#^X7:X5:PqPiPmP?P?%A?M<V1x0ARm1G>0%DA1G>?[[R>%D0Rig02F`R4At0A9UW8RA%D?\4^8iRiPvPDPwPxPy%?M,T3,ByR3P<P:P|g028jR|%?0=s:BR0CO,ByCSP=P~b2b3b4X0:1M5MRM1G@?[^0:P5PKQ01O2RKb1b9b:CR5jqEHP2PvPDPwPxPyPlP<1TN{,ByCSP=P~b2b3b4X0:%D]\J^0:P}b1PmP>PAPiPvPDPwPxPyP3P<P:P{P|P0CO,ByCSP=P~b2b3b4X0:1G]?\M^0:PKb1b9b:5j^EHPEA1GkVA1`nUA3BopPVDCeQ041kPTEHQ021kQREH1h6FP8EHPEP7PB1fY6RY%\d';,7B%]d'41;YH,<QRQC`%\f,;Y,7B%]f53B1;YI,<PRP%\c,;Y,7B%]c53B1;YL,<ORODJA1`aUQ05PVDCe1KYd=17Q1KYfPP1KYcPODJ=FEgeQ03PUPVP`PbCiEHA17_XRXPSPWP7P_CiEHAeY7Z=FEXeg005Kg035nErb=b<W?W>WDo"). Qed.
  Lemma memcpy4_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM4 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 546)) DIG8.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["Refused"] "h01Hh12H0h21Mh32P0h41bh51lh64valsp;1p;2p;3p;6g001ij10Tg002Nj1ATg002lj1>Tg003Oj1GTg00C=j1STg00Hmj2ETg00:8j38Tg008Uj16Tg009:j1<Tg00:Rj2=Tg00MMj2FTg00<>j13Tg00<]j2;Tg00=Cj2DTg00J1j2CTg00gLj3BTg017oj2RTg03Dij37Tg00O2j1QTg01;gj2@Tg004Lj2OTg001Kj6NTg00Mij1MTg00Qbj2LTg01eIj1KTg019Uj2?Tg01fRj1JTg00OPj1ITg01:^j2HTg00Baj6PTf0R0#0#0p=2%60#6p=1%60#0p=5%00#0#0#0p=:%00#0#0#0#0#0#0#0p=4%00#6p=9g004fR1#0#2R2#0#2R3#AR4#>R5#G%A2#>R6#S\5R7f1g00A8R8'Ep,3sp0R9585p,4SPlo%61R1#6#1#1#1#1#1#1#5#2#:#4#4#4#<1=49R:'Fp,4SPhi%03#4#4#4#4#4#<,F:%G6R6%38#3#3#3#3#3#3#3R3%91#:#1#9#5#2#1#5#:#1#5#:#1#2#:#1#2#9#2#1#9#1#2#1#9#5#<R1,;4'DR;p,2BLR<f5'Cf4R=g03J>R>3B%52#2#5R2#<,R:,;4R:=7=0587X56P5P91=40%Q2R2'@,;4=7=;A7=:;587X45f3R5?7:;R:,O71E=8f2EN1C<=R=%M8/L2R2#K'?,=4%J2'@,;4%I1,?=,D3R3575=87:e1H=2=753=87:eAB=5>=87:eg006Dg0351EPb1b0W3W2W6o"). Qed.
  Lemma memcpy5_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM5 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 538)) SUF16.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["Refused"] "h04__x1h17__arithh24__ffh38__varmaph45__with51xh62Hah71nh81Hh92H0h:1Mh;2P0h<6__sat3h=6__sat4h>1bh?1lh@1mhA1ohB4valshC1yhD1zp&0p;1p;2p;3p;4p;<p;8p;6p;Bp;7g001ij10Tg002Nj1^Tg002lj1VTg003Oj1OTg00C=j1vTg00Hmj2[Tg00:8j33k103Tg009:j1:Tg00:Rj2FTg00MMj2<Tg00<>j1;Tg00<]j2Ck104Tg00=Cj2BTg003oj3iTg00J1j2XTg00gLj3]Tg008Uj16Tg017oj2NTg03Dij31j2Pj1STg00HMj2bTg01?OR0j1JTg03Ecj2aTg00Mij1`Tg00O2j1TTg00Qbj2RTg01:^j2GTg00OPj1QTg019Uj2@Tg01;gR1j2=Tg004Lj27Tg01M@k102Tg01M^k401Tg01gZl<yTg009Xj1xTg01B;j2uTg01BYj1tTg01C7j1rTg01Cbj2qTg01k6j3\Tg01DEj3pTg01P8j4MTg01Dhj2oTg01EJj2nTg01F6j3mTg01FUj4kTg01NAj4jTg03FXj8LTg00DAj1lTg01ILj2WTg01GGj2hTg01Goj2ITg01HKj2gTg01Hhj3fTg01Ioj3sTg02Y^j3eTg001Kj6HTg03G5j2wTg01eIj1YTg01fRj1_Tg03H=j4dTg00Baj6cTg01ikl<{Tg01jPlB|Tg01h?j7}Tg01hcj8~Tf0R2#0#0p=4%62#6p=2%62#0p=5%02#0#0#0p=U%02#0#0#0#0#0#0#0p=9%02#6p=>%62#0#0#6p=?%02#6#0#6p=Ef2R3f1R4/=2'Cp=8g00GBR5g00?aR6P6P6P0P0f5R0f4R7f3R8P3P4P2M<{p>00P6P6P6P6P6P6P1P2P4P3P1P8P7P0f6f7f8f9MB|p=z1W62p=AP4g025DR1g025cR9P9g026CR:P2g027JF}p=DP6P4g026cP2CMp=KP8P1P9P9P:P3P4P2G~p=Zg004fR1#0R;#4R<#0R=#4R>#^R?#VR@#O%^<#VRA#v\@RBg00A8RC,[4p,3sp0RD53@p,4SPloRE%21#2#2#2#2#2#2#5#4#U#9#9#9#:RF1F?DRG'<p,4SPhiRH%0>RI#9#9#9#9#9#:RJ,<G%OARK%;C#;#;#;#;#;#;#;RL%5I#2#4#>#2#4#2#>#?#E#2#>#4#>#2#5#E#5#4#5#4#5#U#:RI,C?RM'BRN%?;#?#4#>#?#E#2#4#2#>#2#>#E#?#?#?#E#2#4#5#:RO,C?,BLRP5iARQp,2BLRR/X0R0g03K<RS7]7%6=R=#5#5RT#:RU,NGRV,C?RW=17253BX?KPBA18WNRX1bANRA#JRY,aW;1PRZ%`CR[%TTRT'RR\,G0%QIRI,@0,BL517%4=#5#TR=,R[R[,G0%QORO,@0,BL31=3B2XABP@PD1F?2RD=8?T=17NA8?D=;1PA17WNRD1F?WR0=8?YRY;1P53BX>@P5PLA8?GTRT=17N1=G=R],C?R^;1PR_%J2R`98?0=1DP53BX75P6PV%JLRa98?2=1DP93B_XD6PKPBA18TNRT/P^1=VaR_,C?RD,PXPPPPP@PB\KRb%ST%SXRcP^PDPb\@/7cP6P@&04?RcPcP]P_P@\6/7cA36]_%:<R<,=VRc936]P6P6&036R@P2X56RbP@A3642$02XC6X56P]P]176]P_PcPbPbPbP6P6g02G<1=42H01,76X@6X76PVPV176VPaP<PbPb176`X55PLP<176<J00M:zM<yg02F4R5#xR`%O5R51u64Rb%t6Rc%r6R_P61q61R1%A=5\6g02G`%AU9p61R]%A<5\6CM'D1o_:R:P2P3g027jR@g028JRD'71n23=3@Ddg024fRD=m64CkR@b2b3b4X061=2=1N2U/=<536^06P2PGO1b1CjGLGL17KPGLP0P`P5PbPcP_%AF/K1,D_%l9R91W6D/K],D_CZP:P@b2b3b4X061<F21N4URU,<D[^06P2PGPEO2b1%:;R;%:>R>'h1ID;1<D>1g;>RE,ID[[1<D;RFg02F`RKAf;>4UW61<DE\K^6FP`P5PbPcP_%AJ,K1,D_P9P6P]g028j%A;=s6?CM,D_CZP:P@b2b3b4X061<2J1IUE[^06P2PGPHO2b1b<b=5eVEHA1T^PA8?0a=1XP53BePA1wLMEH1[7CP3EH1XR7RR%Y\'@,F?%_\58?1@RI,BLRI518%Y[,@R,F?%_[58?1@RO,BLRL31A1XYP53Be1GR\=18I1GR[;1L=3BZeA18WQRQPNPPP8PWCdEHA]R8S=3BQeg007<g0342Ecb9b8W;W:WBo"). Qed.

  (* [comment removed for export] *)
  Ltac after_memcpy HL Hms Hkeep :=
    replace (Z_to_bv 64 1171796) with (0x11e154 : word) by (apply bv_eq; reflexivity);
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]; clear Hms;
    replace (0x1143c4 : word) with (Z_to_bv 64 0x1143c4) by (apply bv_eq; reflexivity);
    lazymatch goal with H : regs_ok ?E ?sr ?Rc |- realizes _ (mkCfg (mkst ?R2 _ _ _) _) _ =>
      pose proof (regs_after_keeps _ (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) H Hkeep callee_kept_no0) as HR2;
      rewrite HL in HR2; clear H Hkeep; rename HR2 into HR
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segF : forall vals R M,
    length vals = 167%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knF0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1143c4) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 167%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 538)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x17cc1) 16 = Some SUF16).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x17cc1 16) in exact i)
                 _ _ 0x17cc1 16 HK eq_refl) by (cbn; lia). apply suf16_img. }
    assert (Hdst : store_ok RSEGS M dst 16 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-538) 16) in exact i)
                    _ _ _ (-538) 16 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 538)%Z with (bv_unsigned sp0 + -538)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x17cc1) 16 SUF16).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x1143c4 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x17cc1) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 16) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x17cc1) 16 _ (seg_rom RSEGS) MC Rc (0x1143c4 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst SUF16) knG0).
    { subst dst. rewrite <- (memcpy5_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM5 knF [] knG0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM5].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst SUF16) knG0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segG vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segE : forall vals R M,
    length vals = 135%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srE0 R -> know_ok RSEGS (ENV BL vals) M knD ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1143c4) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 135%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546)).
    set (src := Z_to_bv 64 (bv_unsigned sp0 - 952)).
    (* [comment removed for export] *)
    krdv HK 0%nat (-952)%Z 1%nat Hd0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-951)%Z 1%nat Hd1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-950)%Z 1%nat Hd2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-949)%Z 1%nat Hd3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-948)%Z 1%nat Hd4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-947)%Z 1%nat Hd5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-946)%Z 1%nat Hd6. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-945)%Z 1%nat Hd7. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    cbn [a_base a_off edenot ev ENV] in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    rewrite P0 in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    assert (Hsrc : rdn RSEGS M src (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) = Some DIG8).
    { subst src. replace (bv_unsigned sp0 - 952)%Z with (bv_unsigned sp0 + -952)%Z by lia. rewrite <- DIG8_bytes.
      apply rdn_app_Z; [exact Hd0 | | lia | lia].
      apply rdn_app_Z; [at_addr (-951)%Z Hd1 | | lia | lia].
      apply rdn_app_Z; [at_addr (-950)%Z Hd2 | | lia | lia].
      apply rdn_app_Z; [at_addr (-949)%Z Hd3 | | lia | lia].
      apply rdn_app_Z; [at_addr (-948)%Z Hd4 | | lia | lia].
      apply rdn_app_Z; [at_addr (-947)%Z Hd5 | | lia | lia].
      apply rdn_app_Z; [at_addr (-946)%Z Hd6 | at_addr (-945)%Z Hd7 | lia | lia]. }
    assert (Hdst : store_ok RSEGS M dst 8 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knE ltac:(let i := kidx knE (is_kwr_cov (EVar 0) (-546) 8) in exact i)
                    _ _ _ (-546) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 546)%Z with (bv_unsigned sp0 + -546)%Z by lia. exact Hst. }
    assert (MC : mcH M dst src 8 DIG8).
    { constructor; subst dst src; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x1143c4 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = src)
        by (regv HR (11 : reg); subst src; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A12 : getr Rc 12 = Z_to_bv 64 8) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC Rc (0x1143c4 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst DIG8) knF0).
    { subst dst. rewrite <- (memcpy4_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM4 knE [] knF0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM4].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst DIG8) knF0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 167%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segF vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  Ltac memcpy0_step HL P0 srcZ :=
    let dst := fresh "dst" in
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546));
    lazymatch goal with HR : regs_ok _ _ ?Rc |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
      assert (MC : mcH Mc dst (Z_to_bv 64 srcZ) 0 [])
        by (constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity);
      assert (A1 : getr Rc 1 = (0x1143c4 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 srcZ) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy Mc dst (Z_to_bv 64 srcZ) 0 _ (seg_rom RSEGS) MC Rc (0x1143c4 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12 MC;
      after_memcpy HL Hms Hkeep;
      change (wbytes Mc dst []) with Mc
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segD : forall vals R M,
    length vals = 103%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srD0 R -> know_ok RSEGS (ENV BL vals) M knC ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1143c4) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 103%nat.
    memcpy0_step HL P0 0x1081a%Z.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knD ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
      clear HK; rename HK2 into HK;
      set (vals1 := vals ++ junk_vals R2) in *
    end.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segE vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segC : forall vals R M,
    length vals = 71%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srC0 R -> know_ok RSEGS (ENV BL vals) M knC0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1143c4) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 71%nat.
    memcpy0_step HL P0 0x17cbf%Z.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knC ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
      clear HK; rename HK2 into HK;
      set (vals1 := vals ++ junk_vals R2) in *
    end.
    assert (HL1 : length vals1 = 103%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segD vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segB : forall vals R M,
    length vals = 39%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srRF0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x63388) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 39%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x17cb1) 14 = Some PRE14).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x17cb1 14) in exact i)
                 _ _ 0x17cb1 14 HK eq_refl) by (cbn; lia). apply pre14_img. }
    assert (Hdst : store_ok RSEGS M dst 14 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 14) in exact i)
                    _ _ _ (-560) 14 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x17cb1) 14 PRE14).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x1143c4 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x17cb1) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 14) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x17cb1) 14 _ (seg_rom RSEGS) MC Rc (0x1143c4 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst PRE14) knC0).
    { subst dst. rewrite <- (memcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst PRE14) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segC vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (tid : Z) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x1381d0.
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0x138128 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0x138108 8 0x138108.
  Hypothesis Mpagesz : cell M 0x158490 8 4096.
  (* [comment removed for export] *)
  Hypothesis HBL2 : length (nth 2 BL []) = 8%nat.
  Hypothesis Mguard : bytes_at M 0x158440 (nth 2 BL []).

  Let E : env := ENV BL (valsRE sp0 sp0 tid R).

  Lemma evRF_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["Refused"] "h02Hih11ip;2p;7p;1g02eOj23Tg04>^j72Tg00<>j11Tf0R0#1#1#1#1p=0g00GBg00A8#0#0#0#0#0#0#0#0,30p,3sp0R1p,2BLP1p,3tidp,1Rf1P0F2W0W1o"). Qed.

  Ltac reg_caseRF :=
    cbn [nth srRF0 all_regs];
    first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRF_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRF : regs_ok E srRF0 R.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["Refused"] "p'0h02Hih11ni001nh21zh32Hah44__p1h54__x1h61bh72b1h82b2h91ih:1xh;1Hh<2H0h=2H1h>4HBL0h?3Hi0h@7__arithhA4__ffhB6__sat3hC6__sat4hD8__varmaphE5__withF4cstrhG5cstr0hH1yp%0p&0p;1p;2p;3p;4p;6p;<p;7p;8g008Uj1;Tg001ij14Tg009:j17Tg002Nj1TTg00:Rj2>Tg00MMj2QTg00<>R0j10Tg02eOR1j21Tg002lj1@Tg00?>j3NTg00OPj1MTg04?[j4ITg019Uj2FTg017oj2yTg00<]j2RTg01T<j2]Tg00O2j1oTg04@7j3mTg00:8j38j1bTg02Xdj2YTg00;<j3hTg01;gj2:Tg04@_j2GTg01HKj2ZTg04AEj2DTg004Lj2BTg04Aej3gTg04BLj1PTg04CNj2OTg04D=j2fTg001Kj6STg01=Rj2XTg00Mik104Tg01c5k303Tg01?OR2j1HTg01GoR3j2KTg01@oj4eTg003Oj1dTg009Xj1cTg00HMk200Tg01?oj2~Tg01@Rj3|Tg01gZl<`Tg01AVj1[Tg01GGj2{Tg01Hhj3zTg01Lbj1xTg01B;j2wTg04E9j4tTg01BYj1rTg01C7j1qTg01ILj2VTg01Cbj2pTg01P8j4\Tg00DAj1nTg01W=j6sTg01Dhj2uTg01EJj2vTg01F6j3lTg01FUj4kTg04EWj4jTg01ikl<aTg01h?j7}Tg01k6j3LTg01hcj8iTf0R4#;#;p==%44#4p=J%44#4#4#4p=W%44#4#4#4#4#4#4#4p=<f7f6S00f5R5f4R6g04F]R7f3R8CI'Xf2R9g021GR:f1R;g04:iR<P4CI'F38p=21];4,B9p=31X9;=884p=Ug00?aR=?8;4p=9P=P6P8P9P;P4ESp=C1F;49889p>021:68/:9/:;/:4p=6g00GBR>P>P=P=P0P2P2Q00g04G[R?P5P6P>P>P=P=P0P2P2P8P?P9P;P4M<aM<ap=5P>P=P1P2P3g031VP5P6P8P9P;P4M<`p>01g024fR5/Q4p=EP;g025DS01g025cR3P3g026CR1P4g027JF}p=^AL=68=L=9=L=;=L=4p=?P8Q01P3P3P1P9P;P4Gip=_%04#0#0#0p=Ap,4SPlog004fR?#;R0#=#=#=#=#=#=#=#4#J#W#<#<#<#7%4?R@#4RA#4RB#4RC#4RD#4RE#TRFp,3sp0RG'>RH'Qp,4SPhi%4ERI#<#<#<#<#<#7,QHp,1ERJP<p,1RRKg00A8RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl,14RmP>%@FRnPK%;@Ro#TRp#@RqP;g02EXRr9Np5RsPJP;%M5RtG2^0mP;11LlA3nJRPnPKPqPLP7PsCIP:PLP<PtCI,FJCUeW0P>%04R</1lPnPKPq%0;R:PsPJP:PtG2]0P411MlA3nJSPnPKPqPMPsPJPMPtG2eW0P>%0<R</1lPnPKPq%0:RMPsPJPMPtG2]0P411NlPn%7I,yHR7,RFRmg020[Ru1]JLRv%oIRI,RFRw3mS0298n4X6nPn1YvwA8nm4X6ng00@?Rx%@4Ry%@;Rzg00@]%@9?8;41>891>8;'9R{[1>9;1>94'9%@8?89;[R|%@6?889\{Ah9;4P4n2001000000120000000W8W7W1P|^8z^7y^1xP4PFPm1>FwS03,:HRx,RFRy1GF7Rz1>FyS04,94X2=1GFx19z4X2=1GFIRy1:H4R|,GF,9zX2=%7@R@%7E'ZRE,D7R{1:HyR},GFS05,94X2=1D}E19{4X2=S061DIER~1D|E,9{X2=1:HI/DER{Q061B={1:H~/DEAgIHEDCPy%PIDCQ05%P}DCPz%P7DCQ031OFIDCQ041OFxDC1>Fm1OF7DCO4b=1YGw98nmeQ021fvwESANp@r,XKRwp,3RspESPnPwPJ&04L%MI603uH02ePnPKPqPNPsPJPNPtG2eW0P>%0<R</1lPnPKPq%0MRuPsPJPuPtG2]0P411Olp,3RgpPnPK%70=Npr%;C#4#J#<#7#M,FJCUePnPKPqPOPsPJPOPtG2eW0P>%0<R</1lPnPKPq%0uROPsPJPOPtG2]0P411Plp,3RtpPnPK%7A=Npr%J?#;#=#J#W#;#=#4#;#W#7#M,FJCUePnPKPqPPPsPJPPPtG2eW0P>%0<R</1lPnPKPq%0ORPPsPJPPPtG2]0P411QlA3nJWPnPKPqPQPsPJPQPtG2eW0P>%0<R</1lPnPKPq%0PRQPsPJPQPtG2]0P411RlA3nJXPnPKPqPRPsPJPRPtG2eW0P>%0<R</1lPnPKPq%0QRRPsPJPRPtG2]0P411SlA3nJYPnPKPqPSPsPJPSPtG2eW0P>%0<R</1lPnPKPq%0RRSPsPJPSPtG2]0P411TlA3nJZPnPKPqPTPsPJPTPtG2eW0P>%0<R</1lPnPKPq%0SRrPsPJPrPtG2]0P411UlA3nJ[PnPKPqPUPsPJPUPtG2eW0P>%0<R</1lPnPKPq%0rRUPsPJPUPtG2]0P411VlA3nJ\PnPKPqPVPsPJPVPtG2eW0P>%0<R</1lPnPKPq%0URVPsPJPVPtG2]0P411WlA3nJ]PnPKPqPWPsPJPWPtG2eW0P>%0<R</1lPnPKPq%0VRWPsPJPWPtG2]0P411XlA3nJ^PnPKPqPXPsPJPXPtG2eW0P>%0<R</1lPnPKPq%0WRXPsPJPXPtG2]0P411YlA3nJ_PnPKPqPYPsPJPYPtG2eW0P>%0<R</1lPnPKPq%0XRYPsPJPYPtG2]0P411ZlA3nJ`PnPKPqPZPsPJPZPtG2eW0P>%0<R</1lPnPKPq%0YRZPsPJPZPtG2]0P411[lA3nJaPnPKPqP[PsPJP[PtG2eW0P>%0<R</1lPnPKPq%0ZR[PsPJP[PtG2]0P411\lA3nJbPnPKPqP\PsPJP\PtG2eW0P>%0<R</1lPnPKPq%0[R\PsPJP\PtG2]0P411]lA3nJcPnPKPqP]PsPJP]PtG2eW0P>%0<R</1lPnPKPq%0\R]PsPJP]PtG2]0P411^lA3nJdPnPKPqP^PsPJP^PtG2eW0P>%0<R</1lPnPKPq%0]R^PsPJP^PtG2]0P411_lA3nJePnPKPqP_PsPJP_PtG2eW0P>%0<R</1lPnPKPq%0^R_PsPJP_PtG2]0P411`lA3nJfPnPKPqP`PsPJP`PtG2eW0P>%0<R</1lPnPKPq%0_R`PsPJP`PtG2]0P411alA3nJgPnPKPqPaPsPJPaPtG2eW0P>%0<R</1lPnPKPq%0`RaPsPJPaPtG2]0P411blA3nJhPnPKPqPbPsPJPbPtG2eW0P>%0<R</1lPnPKPq%0aRbPsPJPbPtG2]0P411clA3nJiPnPKPqPcPsPJPcPtG2eW0P>%0<R</1lPnPKPq%0bRcPsPJPcPtG2]0P411dlA3nJjPnPKPqPdPsPJPdPtG2eW0P>%0<R</1lPnPKPq%0cRdPsPJPdPtG2]0P411elA3nJkPnPKPqPePsPJPePtG2eW0P>%0<R</1lPnPKPq%0dRePsPJPePtG2]0P411flA3nJlPnPKPqPfPsPJPfPtG2eW0P>%0<R</1lPnPKPq%0eRfPsPJPfPtG2]0P411gl%0lRp93nJPnPKPqPgPsPJPgPtG2eW0P>%0<R</1lPnPKPq%0fRgPsPJPgPtG2]0P411hl%0pRp93nJPnPKPqPhPsPJPhPtG2eW0P>%0<R</1lPnPKPq%0gRhPsPJPhPtG2]0P411il%0pRp93nJPnPKPqPiPsPJPiPtG2eW0P>%0<R</1lPnPKPq%0hRiPsPJPiPtG2]0P411jl%0pRp93nJPnPKPqPjPsPJPjPtG2eW0P>%0<R</1lPnPKPq%0iRjPsPJPjPtG2]0P411kl%0p93nJPnPKPqPkPsPJPkPtG2eW0%0</1l%0jR</1l%H;Rk%7?R?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6%7DRD'KS02P<1:4?X:=R<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<P<PkO1S04O1S03O1S05O1S06O1S07O1S08O1S09O1S0:O1S0;O1S0<O1S0=O1RpO1RAO1RCO1RIO1RLO1RwO1RvO1RmO1RGO1R7O1RFO1RxO1RzO1R}O1RyO1REO1RHO1R~O1R{O1R|O1P<PjP|P<PiP{P<PhP~P<PgPHP<PfPEP<PePyP<PdP}P<PcPzP<PbPxP<PaPFP<P`P7P<P_PGP<P^PmP<P]PvP<P\PwP<P[PLP<PZPIP<PYPCP<PXPAP<PWPpP<PVQ0=P<PUQ0<P<PrQ0;P<PSQ0:P<PRQ09P<PQQ08P<PPQ07P<POQ06P<PuQ05P<PMQ03P<P:Q04P<P;Pk1B=kF5F5F5F5F5F5F5F5F5F5F5F5F5F5F5F5PlPD1B=DJ01P4CeQ02%TB#@Rl%dlPNp,2BL%clCI+00Rl=8>T%HlRN%7BRB'9R<P>P=%b>P2%b=%H4,9kA8>;41~;43|XH>X:>PlPN1B=NPTPB1B=BM<`p,4HBL2CeP<%[8%H8#E%[l%EN%;o#4#7Ro,{@1K5@%Eo1Z@oRN,K5[[%E@Rlg02F`R<Az@o;UW3%EN\<^3lp-0Rlg02F4R<#c%d<P=%x=P;1w=;Ct%r=%q=R<P=1V=5g026c1p=0R0C\,^<%n3RNP<P=P01V=?R0P0P0P0D?P0P0P0P0D?P0P0P0P0D?P0P0P0P0D?P0P0P0P0D?P0P0P0P0D?P0P0P0P0D?P0P0P0P0D?g028j1V=DC\,^<PNP<Q01P3P3P1P8EsC_C_1u<1P4P9g027jR<g028JR1'B1v49=8<1dAl=5;CkbAbDbEX5=W4%E4P;P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6P?P?P?P?D6/KDP8[[^5=^4lP4PnPKPqf8Rq#A#A#A#A#A#A#A#ARKPsPJPKPtG2%HqP6Q00O4b@bBbCbGbFb>b?W0X9>P4O1n0110001020111100X1>P4O1n0110001020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020111100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020011100X1>P4O1n0110000020111100X1>P4O1n0110000020011100X1>P4O1n0110000020011100P4O1W0X9>Cjb<b;o"). Qed.

  Theorem ref_refused_tail :
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x63388) M (seg_rom RSEGS)) model)
               (t_die msg_refused (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused ()) ["Refused"] "h04__x1h14HBL0h22Hah37__arithh44__ffh56__sat3h66__sat4h78__varmaph85__with94cstrh:1Hh;2H0h<1xh=1yp;1p;2p;4p;3p;<p;Ap;7p;5g008Uj17Tg001ij10Tg009:j16Tg002Nj1<Tg00:Rj2STg00MMj22Tg04H?j4ITg04I9j4GTg002lj1?Tg00Hmj2eTg004Lj29Tg003Oj1BTg00<>j13Tg009Xj1DTg04?[j4XTg00HMj2WTg00:8j38j1@Tg01?OR0j1:Tg01?oj2VTg01@Rj3UTg01gZl<RTg01@oj4QTg01AVj1PTg01GGj2JTg01Goj2;Tg01HKj2KTg01Hhj3HTg01B;j2LTg01BYj1MTg01C7j1NTg01Cbj2OTg01P8j4=Tg01Dhj2FTg01EJj2TTg01F6j3dTg01FUj4cTg01ILj2ETg01k6j3CTg01;gj2ATg04J7lA`Tg04K4j7^Tg00<]j2]Tg00\Hj1\Tg00h^j5[Tg00iWj2ZTg00^Hj1_Tg04Koj2YTg01b6j3aTg01h?j7bTf0R1#7#7p=1%01#0p=5%01#0#0#0p=f%01#0#0#0#0#0#0#0p=4f1R2g025Dg025cR3P3g026CR3P1g027JFbp=>p,4SPlog004fR4#7#1#1#1#1#1#1#1#0#5#f#4#4#4#6%04R5#5R6#0#5R7#<R8p,3sp0R9'SR:'2p,4SPhi%47#4R7#0#4#4#4#6,2:P9P9p,3tidR;p,1RR<CIR=P<p,1MR>P9P9P;P<CG%?8g00A8R?,e='9g04LoP9p,2BLR=p,4HvspP9P;P<P>p,6Mstackp,4Mimgp,4Mtidp,4Htidp,5Mselfp,7Mpageszp,4HBL2R;p,6Mguardg00GBR9%<6#?R@%B@%3?#3R?P=%D@CX'WR@%3?#3#3#3#3#3R?38g00?aR=%:@RA%66R638RBP9P=%@9P0%@=%:2%:158=A89211V213UX=9X<9P@PA19=AP?P619=6M<RP;CQR;PB%P@R@g024fR?/2ARA%65R9%15#0#6R5'JR01;?912?51K95RC,;?[[RD12?9REg02F`RFAH952UW2R512?C\F^2EREg02F4RF#DRC%BFRF1L=2R9%M=RG%N=RHP=1O=4RIg026cRJPIC='>1FH3R3P1f2RKg027jRLg028JRM'91T1K=8LMdAd=?2CcR?b4b7b8X0=1211^0=P1P:O1R:b3b5b6b9b1P;PBP@PAP0PDP5PEPCPFP9PGP=1E=69C=IPJ%67R7,E=9C=IC=,>HP3P?b4b7b8X0=1A161A17'2^0=P:b3b5b6b9b1MA`F^g00E[R:g02:3P<%74#0#5#1#5#7#1#0#5#7#0#5#6,]8P>%\:D[p,5modelR:'Zg036m%_:'Y3aeb;b:o"). Qed.
End Refused.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
