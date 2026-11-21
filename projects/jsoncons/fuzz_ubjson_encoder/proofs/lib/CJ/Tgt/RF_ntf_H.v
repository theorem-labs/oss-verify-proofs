(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; addresses and numbers. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_F F_ntf_H MallocKit_A3 MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_free_A RF_ntf_A RF_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_ntf_H () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B35mw_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3?meta_word_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_wordC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~K47Corelib7Numbers7BinNums8positive01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_freeableC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_sizeclassC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8m_maplenC13~~~I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z9div_smallC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z7div_addC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateAunsigned_lit_wrapC13~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_H8eh_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_H8eh_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3<lor_sxv_zeroC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free3sxvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9sxv_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;lor_range64C13~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H8rmid_ctxC13~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~K47Corelib7Numbers7BinNums1Z03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_A:rntf_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_H8ntf_condC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H;rentry_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C56Stdlib6ZArith6BinInt1Z3lorC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep5rmrepC13~~~C47Corelib4Init5Logic3iffC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_H7eh_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_BArmeta_slot_boundsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2geC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics5Riscv7Prelude4tree00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z4landC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeAunsigned_lit_landC13~~~C46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H<rentry_casesC13~~~I47Corelib4Init5Logic2ex00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H3RATC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~K47Corelib4Init5Logic2or01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:F_syscalls5rsegsC13~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep:RSSP_GUARDC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H<rmaskw_rangeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H;rmaskw_zeroC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep4RCTXC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3bitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9mask_uptoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<okay_to_freeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_H:entry_hyps00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7bouncesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5usageC13~~~C47Corelib4Init9Datatypes4andbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_H?ntf_cond_unfoldC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_C>rconc_meta_injC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep@rmrep_meta_chunkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge6zr_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBinr64_unsigned_litC13~~~C47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr09C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_slliC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_slliC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_BArmrep_active_readC13~~~C35stdpp7tactics<f_equal_helpK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01I4ELinuxProcessSemantics5Riscv3Sem4core00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3@meta_word_lt4096C13~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK4ELinuxProcessSemantics5Riscv5Instr5instr02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_auipcC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7b_auipcC13~~~C56Stdlib6ZArith6BinInt1Z3lebC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_strideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:size_classC13~~~C47Corelib4Init9Datatypes3orbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8optr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;is_bouncingC13~~~C56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega5Tauto8GFormula02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_H:okf_unfoldC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H8rntf_fgeC13~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep@size_class_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le2C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRepBrsize_classes_readC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_andiC13~~~C45stdpp9bitvector;definitions7bv_wrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_andiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_srliC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_srliC13~~~K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4zx16C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@zext_extract_le2C13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8aptr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<aptr_eqb_neqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free=optr_eqb_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc?sc_in_seq_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_F>seq_range_testC13~~~C47Corelib4Init5Logic5proj2C46Stdlib4Bool4Bool=andb_true_iffC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_BBrmrep_bounces_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3zxbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemAzext_extract_byteC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_B@rmrep_usage_readC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H;rntf_notallC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6zxb_b8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7zx16_wzC13~~~C46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt9RF_free_A=meta_word_sc2C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_luiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5b_luiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_andC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_andC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt9RF_free_A<meta_word_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;land_pgmaskC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3@meta_word_maplenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3Bmeta_word_last_idxC13~~~K46Stdlib9micromega5Tauto8GFormula09K46Stdlib9micromega5Tauto8GFormula0:C47Corelib4Init5Logic6eq_symK46Stdlib9micromega5Tauto4kind02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4UNITC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep=RSIZE_CLASSESC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_shadowC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:canary_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_carveC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z9add_assocC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~C46Stdlib9micromega;ZifyClasses8or_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6W_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRepDrmrep_transport_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4sx32C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@sext_extract_le4C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_sllwC13~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6w_sllwC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_orC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6alu_orC13~~~C45stdpp9bitvector;definitions8bv_swrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addwC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6w_addwC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_addiwC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7w_addiwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free=free_all_testC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H:rntf_okchkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free=addiw_m1_wordC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H?meta_word_mod32C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free:sllw2_wordC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9addw_wordC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_H>meta_word_sc52C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3Bmeta_word_freeableC13~~~C56Stdlib6ZArith6BinInt1Z8lor_commC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3:sllw1_wordC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;sx32_wz_sxvC13~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib5Lists7ListDef5skipnC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cb_split_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~K46Stdlib9micromega5Tauto8GFormula06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep6RMLOCKC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;RNEED_LOCKSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep:RPAGE_SIZEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep8RGOT_SSPC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop09".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs).

Definition rentry_cases (ms' : machine_state) : Prop :=
  (* [comment removed for export] *)
  (ntf_cond st g i = false /\ mask <> 0 /\
   exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
     RAT 0xa0298 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = false /\ mask = 0 /\
   exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
     RAT 0xa007c (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ m_next mr = None /\
   exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0xa0140 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
   exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0xa00d4 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ sc < 48 /\
   exists nx, m_next mr = Some nx /\ nx <> g /\
   exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0xa0050 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m1 junk,
    rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ stk rsegs m1 lo (bv_unsigned sp + -96)
    /\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
    /\ rmrep st m1.

(* [comment removed for export] *)
Lemma meta_word_sc52 mr : mw_ok mr ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof.
  intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof.
  intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

(* [comment removed for export] *)
Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
  munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
  /\ stk rsegs m1 lo (bv_unsigned sp + -96) /\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.

Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. apply lor_range64; apply sxv_range. Qed.

Ltac rpost_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].


(* [comment removed for export] *)
Lemma rntf_notall : forall (t0 t1 t2 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> ntf_cond st g i = false ->
  evt rsegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa0074) fc None m1 (seg_rom rsegs)).
Proof.
  intros until junk. intros (MU & WM & MI & ST & FR & MR) HC.
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). pose_ceil. pose_ceil.
  st1. rewrite ?(unsigned_lit (conc st g)) by lia.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
  -
    rpost_common MU WM MI ST FR MR m1 junk.
    left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
    do 14 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  -
    assert (M0 : mask = 0) by (apply MZ; lia).
    rpost_common MU WM MI ST FR MR m1 junk.
    right; left. split; [exact HC|]. split; [exact M0|].
    do 12 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rntf_fge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> okay_to_free st g = true ->
  evt rsegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa002c) fc None m1 (seg_rom rsegs)).
Proof.
  intros until junk. intros (MU & WM & MI & ST & FR & MR) HALL OKT.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
  (pose_ceil; unfold RCTX in *).
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
  assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
  { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _). pose_ceil.
    split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
  rmeta_chunk MR MSL CH.

  st1. clear CH.
  destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
  - destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
    specialize (G50 HC ltac:(congruence)).

    st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }

    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
    replace (wa (970704 + 80 + 8 * sc)) with (Z_to_bv 64 (970704 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.

    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    + pose proof (NINJ ltac:(lia)) as ->.
      rpost_common MU WM MI ST FR MR m1 junk.
      do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
      do 12 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
    + assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
      rpost_common MU WM MI ST FR MR m1 junk.
      do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
      do 11 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  - st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
    rpost_common MU WM MI ST FR MR m1 junk.
    do 2 right; left. split; [exact HC|]. split; [exact NX|].
    do 14 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rntf_okchk : forall (t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> m_freeable mr <> 0 ->
  evt rsegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 (Z_to_bv 64 (meta_word mr)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ff7c) fc None m1 (seg_rom rsegs)).
Proof.
  intros until junk. intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
  pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose_ceil.
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).

  st1. st1. st1.
  st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  {
    eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
    rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  assert (SC48 : sc < 48) by lia. clear K2.
  assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
  specialize (USG SC48).
  pose proof (size_class_range sc ltac:(lia)) as SZ.
  assert (RS' : ov_read_bytes rsegs m1 (Z_to_bv 64 (110528 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (110528 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
    apply rsize_classes_read; [assumption| lia]. }

  st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.

  assert (K690 : forall (t0' : word),
    m_maplen mr <> 0 ->
    evt rsegs POST
      (MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 110528) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 970704) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ffd0) fc None m1 (seg_rom rsegs))).
  { intros t0' MLNZ.
    assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
    assert (GSR : 0 < get_stride mr < 2^64).
    { unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }

    st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
    replace (110528 + sc * 2) with (110528 + 2 * sc) by lia.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    { eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
    assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
    assert (OKF : okay_to_free st g =
              if negb (optr_eqb (m_next mr) (Some g)) then true
              else if negb (is_bouncing sc st) then true
              else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
    { rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }

    rmeta_chunk MR MSL CH.
    st1. clear CH.
    assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
    { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _). pose_ceil.
      split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
    destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
    2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
        eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
    destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
    { assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
      cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
    pose proof (NINJ ltac:(lia)) as Enx. subst nx.
    rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.

    st1. rewrite ?(unsigned_lit sc) by lia. st1.
    st1. if_cases K7; zify_cond K7.
    { assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
      unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
    unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.

    st1.
    pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
    pose proof (BND (sc - 7)) as BR.
    replace (Z_to_bv 64 (970704 + 880 + (sc - 7))) with (Z_to_bv 64 (970704 + (sc + -7) + 880)) in RDB by (f_equal; lia).
    st1. clear RDB. st1.
    st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
    { replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.

    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    replace (wa (970704 + 464 + 8 * sc)) with (Z_to_bv 64 (970704 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.

    st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
    { replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
    replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.

    st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
    - replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
    - replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }

  assert (K678 :
    (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt rsegs POST
      (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 110528) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 970704) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ffb8) fc None m1 (seg_rom rsegs))).
  { intros COND.
    assert (STR : get_stride mr = 16 * size_class sc).
    { unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

    st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

    st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
    - eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
    - replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
      apply K690. lia. }

  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  { apply K678. left. lia. }

  st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
  { apply K678. right. lia. }

  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
  st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
  replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
  2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
  apply K690. lia.
Qed.

(* [comment removed for export] *)
Lemma rntf_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rmrep st m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ff18) fc None m (seg_rom rsegs)).
Proof.
  intros until t6. intros MR ST.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof rmaskw_range as MWR'.
  pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & _) & _).
  (pose_ceil; unfold RGOT_SSP, RSSP_GUARD in *). unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.

  st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.

  st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
  clear MR G4 G5.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  rmeta_chunk MR1 MSL CH.

  st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
  st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
  st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  st1. rewrite (meta_word_freeable _ MW).
  st1. rewrite (meta_word_sc52 _ MW).
  clear CH.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.

  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }

  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
  rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
  st1. rewrite addiw_m1_word.

  pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
  st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
  - assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
      apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
  -
    apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
    eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed.
End ENTRY.
End CEIL_WRAP_1.

