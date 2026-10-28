(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_initds () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit5le64vC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedI47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit<le64_lbu_rawK46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC56Stdlib6ZArith6BinInt1Z9add_assocK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr03K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallK4ELinuxProcessSemantics5Riscv5Instr5aluop02K46Stdlib9micromega:ZMicromega;ZArithProof01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell03I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface7bitd_okI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9read_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp>reload_dstreamC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_ifaceDfse_init_dstate_postC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_contC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6bd_ptrC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9skip_bitsC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_zeroK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD01C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z<pos_div_euclC57Corelib7BinNums6PosDef3Pos4iterC57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kit7mask_rdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64K4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas6u32_idC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8K4ELinuxProcessSemantics5Riscv5Instr5instr05C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC46Stdlib4Bool4Bool>negb_false_iffK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8readLE64C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit;readLE64_okK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_initds7fast_ldC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_gtC57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK46Stdlib9micromega:ZMicromega;ZArithProof03c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_initds7part_ldC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface;bitdz_cellsC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kit=neg_shift_modC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kitAzx32_unsigned_litC5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit2:sx32_smallC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kit8zx16_litC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega5Tauto8GFormula0:C47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvK46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz05I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus00K46Stdlib9micromega5Tauto4kind02C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface<BIT_MASK_TABK46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5aluop01K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus04K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus01K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus02C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC56Stdlib6ZArith6BinInt1Z4div2K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize03C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface<ZEROFILLED_FC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop07K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes:comparison01C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_ifaceDfse_init_dstate_stmt".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section LE64.
  Variables (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bs : list Z) (POST : machine_state -> Prop).
  Hypothesis SRC : bytes_at usegs m S (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.

  Notation ST pc x3 x4 x5 x6 x7 y5 y6 y7 :=
    (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 a0 a1 a2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Ltac ldb0 p k :=
    let RX := fresh "RX" in
    pose proof (src_rd usegs m S bs (p + k) SRC ltac:(lia)) as RX;
    rewrite ?Z.add_assoc, ?Z.add_0_r in RX;
    zstep; cbv beta; clear RX.

  (* [comment removed for export] *)
  Lemma fast_ld : forall (p E : Z) (x3 x4 x6 x7 y5 y6 y7 : word),
    0 <= p -> p + 8 <= zlen bs -> E = S + p ->
    (forall (z4 z5 z6 z7 w5 : word),
       evt usegs POST (ST 0x20c70 (Z_to_bv 64 (le64v bs p)) z4 z5 z6 z7 w5 y6 y7)) ->
    evt usegs POST (ST 0x20c18 x3 x4 (Z_to_bv 64 E) x6 x7 y5 y6 y7).
Proof.
  intros p E x3 x4 x6 x7 y5 y6 y7 P0 P8 EE K. subst E.
  assert (BYn : forall i, 0 <= i < zlen bs -> 0 <= Znth i bs < 256) by (intros; apply byte_Znth; auto).
  ldb0 p 1. ldb0 p 2. ldb0 p 3. ldb0 p 0. do 4 zstep. ldb0 p 4. ldb0 p 5. zstep. ldb0 p 6. ldb0 p 7. do 9 zstep.
  rewrite le64_lbu_raw by (apply BYn; lia).
  apply K.
Qed.
  (* [comment removed for export] *)
  Lemma part_ld : forall (p E : Z) (x3 x4 x5 x7 y5 y6 y7 : word),
    0 <= p -> p + 8 <= zlen bs -> E = S + p ->
    (forall (z4 z5 z6 z7 w5 : word),
       evt usegs POST (ST 0x20c70 (Z_to_bv 64 (le64v bs p)) z4 z5 z6 z7 w5 y6 y7)) ->
    evt usegs POST (ST 0x20b9c x3 x4 x5 (Z_to_bv 64 E) x7 y5 y6 y7).
Proof.
  intros p E x3 x4 x5 x7 y5 y6 y7 P0 P8 EE K. subst E.
  assert (BYn : forall i, 0 <= i < zlen bs -> 0 <= Znth i bs < 256) by (intros; apply byte_Znth; auto).
  ldb0 p 1. ldb0 p 2. ldb0 p 3. ldb0 p 0. do 4 zstep. ldb0 p 4. ldb0 p 5. zstep. ldb0 p 6. ldb0 p 7. do 10 zstep.
  rewrite le64_lbu_raw by (apply BYn; lia).
  apply K.
Qed.
End LE64.

(* [comment removed for export] *)
Ltac ldb S p k :=
  let RX := fresh "RX" in
  lazymatch goal with SRC : bytes_at usegs ?mg S (map (Z_to_bv 8) ?bs) |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
    pose proof (src_rd usegs mg S bs (p + k) SRC ltac:(lia)) as RX end;
  rewrite ?Z.add_assoc, ?Z.add_0_r in RX;
  zstep; cbv beta; clear RX.

(* [comment removed for export] *)
Ltac part_tail S p :=
  eapply (part_ld _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S); [eassumption| eassumption| lia| lia| lia| lia| lia|];
  intros z6 z7 w5 w6 w7;
  do 6 zstep;
  apply evt_done; unfold fse_init_dstate_post;
  do 13 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].

Lemma nullx_ok : forall p q, 0 < p -> 0 <= q -> q <> p ->
  Z.lxor (Z.b2z (0 <? p)) (Z.b2z (Z.lxor p q <? 1)) = 0 -> False.
Proof.
  intros p q P Q N H. rewrite (proj2 (Z.ltb_lt 0 p) P) in H.
  assert (X : Z.lxor p q <> 0) by (intro E; apply N; symmetry; apply Z.lxor_eq; exact E).
  assert (X0 : 0 <= Z.lxor p q) by (apply Z.lxor_nonneg; split; intros; lia).
  rewrite (proj2 (Z.ltb_ge (Z.lxor p q) 1) ltac:(lia)) in H. discriminate H.
Qed.
Lemma ids_mod : forall n, 0 <= n < 2^31 ->
  ((0 - n) mod 18446744073709551616) mod 64 = FseNCount.u32 (64 - n) mod 64.
Proof. intros n N. unfold FseNCount.u32. Z.div_mod_to_equations. lia. Qed.
Lemma ids_v : forall c b t, 0 <= b < 2^30 -> 0 <= t <= 12 ->
  Z.land (Z.shiftr c ((bv_swrap 32 (0 - bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 b)) + t) mod 18446744073709551616)
                       mod 18446744073709551616) mod 64))
         (bv_unsigned (zx32 (Z_to_bv 64 (2 ^ t - 1))))
  = Z.land (Z.shiftr c (FseNCount.u32 (64 - b - t) mod 64)) (2 ^ t - 1).
Proof.
  intros c b t B T.
  assert (P : 1 <= 2^t <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 t ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  rewrite (sx32_small b) by lia. rewrite (unsigned_lit b) by lia.
  rewrite (FseWalkKit.swrap32_small (b + t)) by lia.
  rewrite (Z.mod_small (b + t) 18446744073709551616) by lia.
  rewrite (FseWalkKit.swrap32_small (0 - (b + t))) by lia.
  rewrite (zx32_unsigned_lit (2^t - 1)) by lia.
  rewrite (ids_mod (b + t)) by lia.
  replace (64 - (b + t)) with (64 - b - t) by lia. reflexivity.
Qed.
Lemma ids_b : forall b t, 0 <= b < 2^30 -> 0 <= t <= 12 ->
  bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 b)) + t) = b + t.
Proof.
  intros b t B T. rewrite (sx32_small b) by lia. rewrite (unsigned_lit b) by lia.
  apply FseWalkKit.swrap32_small. lia.
Qed.
Ltac zn1 H := match type of H with
  | context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) in H by lia
  | context [zx16 (Z_to_bv 64 ?x)] => rewrite (zx16_lit x) in H by lia
  | context [bv_unsigned (zx32 (Z_to_bv 64 ?x))] => rewrite (zx32_unsigned_lit x) in H by lia
  | context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) in H by lia
  | context [bv_wrap 32 ?x] => unfold bv_wrap in H; change (bv_modulus 32) with (2^32) in H
  | context [bv_swrap 32 ?x] => rewrite (swrap32_small x) in H by lia
  | context [Z.shiftl ?x ?n] => rewrite (Z.shiftl_mul_pow2 x n) in H by lia
  | context [Z.shiftr ?x ?n] => rewrite (Z.shiftr_div_pow2 x n) in H by lia
  | context [?x mod ?y] => rewrite (Z.mod_small x y) in H by lia
  | context [2 ^ ?k] => is_Zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v in H
  | context [?x * ?c / ?c] => is_Zlit c; rewrite (Z.div_mul x c) in H by lia
  end.
Ltac zn H := repeat zn1 H.
Ltac znG1 := match goal with
  | |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by lia
  | |- context [zx16 (Z_to_bv 64 ?x)] => rewrite (zx16_lit x) by lia
  | |- context [bv_unsigned (zx32 (Z_to_bv 64 ?x))] => rewrite (zx32_unsigned_lit x) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
  | |- context [bv_wrap 32 ?x] => unfold bv_wrap; change (bv_modulus 32) with (2^32)
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by lia
  | |- context [Z.shiftl ?x ?n] => rewrite (Z.shiftl_mul_pow2 x n) by lia
  | |- context [Z.shiftr ?x ?n] => rewrite (Z.shiftr_div_pow2 x n) by lia
  | |- context [?x mod ?y] => rewrite (Z.mod_small x y) by lia
  | |- context [2 ^ ?k] => is_Zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v
  | |- context [?x * ?c / ?c] => is_Zlit c; rewrite (Z.div_mul x c) by lia
  end.
Ltac znG := repeat znG1.
Ltac arith_only := repeat match goal with
  | H : ?T |- _ => lazymatch type of T with Prop =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | not (@eq Z _ _) => fail
      | and _ _ => fail | or _ _ => fail | @eq bool _ _ => fail
      | _ => clear H end end end.
Lemma div8_le : forall a, 0 <= a <= 64 -> 0 <= a / 8 <= 8.
Proof. intros a H. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.
Ltac gen_div8 := repeat match goal with |- context [?a / 8] =>
  let H := fresh "D8" in let q := fresh "q" in let E := fresh "E" in
  assert (H : 0 <= a / 8 <= 8) by (apply div8_le; lia); remember (a / 8) as q eqn:E; clear E end.
Ltac refute U := exfalso; arith_only; first [ lia
  | (zn U; revert U; gen_div8; intros U; lia)
  | (zn U; lia)
  | (eapply nullx_ok; [ | | | exact U]; znG; gen_div8; lia)
  | (change 1 with (Z.ones 1) in U; rewrite Z.land_ones in U by lia; change (2^1) with 2 in U; lia)
  | (change 7 with (Z.ones 3) in U; rewrite Z.land_ones in U by lia; change (2^3) with 8 in U; lia)
  | (zn U; Z.div_mod_to_equations; lia) ].
Ltac is_uim pc := let b := eval vm_compute in (existsb (Z.eqb pc) [134300]) in lazymatch b with true => idtac end.
Ltac side_uim := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => is_uim pc end.
Ltac side_alive U := let U2 := fresh "U2" in pose proof U as U2; (try zn U2); let T := type of U2 in idtac "ALIVE" T; clear U2.
Ltac side U := first [ side_uim; first [refute U | side_alive U] | try (exfalso; first [lia | zn U; lia]) ].
Lemma land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac zeq := first [ reflexivity | lia
  | (rewrite ids_v by lia; reflexivity) | (rewrite ids_b by lia; first [reflexivity | lia])
  | (znG; first [ reflexivity | lia | (gen_div8; znG; lia)
                | (rewrite ?land7; arith_only; Z.div_mod_to_equations; lia) ])
  | (idtac "ZEQ_FAIL"; match goal with |- ?G => idtac G end) ].
Ltac el := first [ reflexivity
  | lazymatch goal with
    | |- C8 (Z_to_bv 64 ?a) = C8 (Z_to_bv 64 ?b) => replace b with a; [reflexivity | zeq]
    | |- C4 (Z_to_bv 64 ?a) = C4 (Z_to_bv 64 ?b) => replace b with a; [reflexivity | zeq]
    | |- ?G => idtac "EL_OTHER" G
    end ].
Ltac lst := repeat (lazymatch goal with |- cons _ _ = cons _ _ => f_equal end).
Ltac cells_to := lazymatch goal with |- rw_cells usegs ?mm ?A ?l2 =>
  lazymatch goal with H : rw_cells usegs mm A ?l1 |- _ =>
    refine (eq_ind l1 (fun l => rw_cells usegs mm A l) H l2 _) end end; lst; el.
Ltac ids_post := apply evt_done; unfold fse_init_dstate_post, bitdz_cells; cbn [bd_cont bd_bits bd_ptr bd_zero];
  do 13 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; cells_to.
Ltac ideq := first [lia | (znG; lia) | (znG; gen_div8; znG; lia) | idtac "IDEQ_FAIL"].
Ltac chk := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  lazymatch c with
  | true => cbv iota
  | false => cbv iota
  | _ => let U := fresh "U" in if_cases U; zify_cond U; [side U | side U]
  end end.
Ltac norm := rewrite ?zx16_lit by lia; try (rewrite ?Z.shiftl_mul_pow2 by lia).
Ltac notuim := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif is_uim pc then fail else idtac end.
Ltac notat T := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let b := eval vm_compute in (Z.eqb pc T) in lazymatch b with true => fail | false => idtac end end.
Ltac walk := repeat (first [chk | notuim; zstep; norm]).
Ltac walk_to T := repeat (first [chk | notat T; notuim; zstep; norm]).
Ltac pcoff := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let d := eval vm_compute in (pc - 0x20ac0) in idtac "PCOFF" d | |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PCNONLIT" | |- _ => idtac "NOTEVT" end.
Ltac showcells := pcoff; lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => idtac "REGS" R | _ => idtac end; repeat match goal with H : rw_cells usegs _ _ ?cs |- _ => idtac "CELLS" H cs; revert H end; intros.
Ltac post := first [ids_post | (idtac "POST_FAIL"; pcoff)].
Lemma sids_q : forall b t, 0 <= b < 2^30 -> 0 <= t <= 12 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 b)) + t) mod 18446744073709551616)) 3)
    mod 18446744073709551616 = (b + t) / 8.
Proof.
  intros b t B T.
  rewrite (ids_b b t) by lia.
  rewrite (Z.mod_small (b + t) 18446744073709551616) by lia.
  unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  rewrite (Z.mod_small (b + t) 4294967296) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (Q : 0 <= (b + t) / 8 <= b + t) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (FseWalkKit.swrap32_small ((b + t) / 8)) by lia.
  apply Z.mod_small. lia.
Qed.
Lemma sids_bits : forall b t k, 0 <= b < 2^30 -> 0 <= t <= 12 -> -2147483648 <= b + t - k * 8 < 2147483648 ->
  bv_swrap 32 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 b)) + t) mod 18446744073709551616 - k * 8) = b + t - k * 8.
Proof.
  intros b t k B T R. rewrite (ids_b b t) by lia.
  rewrite (Z.mod_small (b + t) 18446744073709551616) by lia.
  apply FseWalkKit.swrap32_small. lia.
Qed.
Lemma sids_sh32 : forall k, 0 <= k -> Z.shiftr (k * 4294967296) 32 = k.
Proof. intros k K. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. apply Z.div_mul. lia. Qed.
Ltac sids_fix := repeat match goal with
  | H : context [bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 ?b)) + ?t)
                                         mod 18446744073709551616)) 3) mod 18446744073709551616] |- _ =>
      rewrite (sids_q b t) in H by lia
  | H : context [bv_swrap 32 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 ?b)) + ?t) mod 18446744073709551616 - ?k * 8)] |- _ =>
      rewrite (sids_bits b t k) in H by lia
  | H : context [Z.shiftr (?k * 4294967296) 32] |- _ => rewrite (sids_sh32 k) in H by lia
  end.
Ltac sids_noor := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac sids_refute U := exfalso; arith_only; sids_noor; first [ lia | (zn U; lia)
  | (zn U; revert U; gen_div8; intros U; lia)
  | (eapply nullx_ok; [ | | | exact U]; znG; gen_div8; lia)
  | (change 1 with (Z.ones 1) in U; rewrite Z.land_ones in U by lia; change (2^1) with 2 in U; lia)
  | (change 7 with (Z.ones 3) in U; rewrite Z.land_ones in U by lia; change (2^3) with 8 in U; lia)
  | (zn U; Z.div_mod_to_equations; lia) ].
Ltac sids_side U := first [ side_uim; first [sids_refute U | side_alive U]
  | try (exfalso; arith_only; sids_noor; first [lia | zn U; lia]) ].
Ltac sids_chk := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  lazymatch c with
  | true => cbv iota
  | false => cbv iota
  | _ => let U := fresh "U" in if_cases U; zify_cond U; [sids_side U | sids_side U]
  end end.
Ltac sids_walk_to T := repeat (first [sids_chk | notat T; notuim; zstep; norm]).
Ltac sids_walk := repeat (first [sids_chk | notuim; zstep; norm]).
Lemma fse_init_dstate_proof : fse_init_dstate_stmt.
Proof.
  unfold fse_init_dstate_stmt, PFSE_INIT_DSTATE.
  intros until lo.
  intros HDS HBD HDT SRC BY TLR BOK RB RL DS0 DS8 BD0 BD8 DT0 DT2 DT4 S8 SHI J1 J2 J3 J4 J5 STK LDS LBD MI -> -> ->.
  pose proof (munch_refl [(DS, DS + 16); (BD, BD + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (mask_rd m tl MI ltac:(lia)) as MK. unfold BIT_MASK_TAB in MK.
  destruct BOK as (BC0 & BB0 & BP0 & BP8 & BPS & BZ).
  pose proof (rw_cells_bound _ _ _ _ HDS) as BDS. pose proof (rw_cells_bound _ _ _ _ HBD) as BBD.
  pose proof (rw_cells_bound _ _ _ _ HDT) as BDT. cbn in BDS, BBD, BDT.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_map in BS.
  unfold read_bits, look_bits, bit_mask in RB.
  destruct ((0 <=? tl) && (tl <? 32)) eqn:TB; [|discriminate]. cbn in RB. injection RB as EV ED1. subst v d1.
  unfold skip_bits in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
  replace (FseNCount.u32 (bd_bits d + tl)) with (bd_bits d + tl) in RL by (unfold FseNCount.u32; rewrite Z.mod_small; lia).
  assert (P2 : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  unfold bitdz_cells in HBD.
  unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
  destruct (bd_zero d) eqn:BZd.
  { specialize (BZ eq_refl).
    replace (64 <? bd_bits d + tl) with true in RL by (symmetry; apply Z.ltb_lt; lia).
    cbv beta iota in RL. injection RL as <- <-.
    walk. idtac "CASE_Z". all: pcoff. all: post. }
  rewrite ?BZd in RL.
  destruct (Z_lt_le_dec 64 (bd_bits d + tl)) as [OV|OV].
  { replace (64 <? bd_bits d + tl) with true in RL by (symmetry; apply Z.ltb_lt; lia).
    cbv beta iota in RL. injection RL as <- <-.
    walk. idtac "CASE_OV". all: pcoff. all: post. }
  replace (64 <? bd_bits d + tl) with false in RL by (symmetry; apply Z.ltb_ge; lia).
  pose proof (Z.div_mod (bd_bits d + tl) 8 ltac:(lia)) as QD. pose proof (Z.mod_pos_bound (bd_bits d + tl) 8 ltac:(lia)) as QM.
  destruct (Z_le_gt_dec 8 (bd_ptr d)) as [FP|FP].
  { replace (8 <=? bd_ptr d) with true in RL by (symmetry; apply Z.leb_le; lia).
    cbv beta iota zeta in RL. rewrite Z.shiftr_div_pow2 in RL by lia. change (2^3) with 8 in RL.
    rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
    walk_to 134168.
    eapply fast_ld with (p := bd_ptr d - (bd_bits d + tl) / 8); [eassumption | eassumption | lia | lia | ideq | intros].
    do 80 (try (first [chk | notuim; zstep; norm])).
    all: post. }
  replace (8 <=? bd_ptr d) with false in RL by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.eq_dec (bd_ptr d) 0) as [P0|P0].
  { replace (bd_ptr d =? 0) with true in RL by (symmetry; apply Z.eqb_eq; lia).
    cbv beta iota in RL. injection RL as <- <-.
    walk. idtac "CASE_START". all: pcoff. all: post. }
  replace (bd_ptr d =? 0) with false in RL by (symmetry; apply Z.eqb_neq; lia).
  assert (N8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [L|L]; [specialize (BPS L); lia | lia]).
  cbv beta iota zeta in RL. rewrite Z.shiftr_div_pow2 in RL by lia. change (2^3) with 8 in RL.
  destruct (Z_lt_le_dec (bd_ptr d - (bd_bits d + tl) / 8) 0) as [PB|PB].
  { replace (bd_ptr d - (bd_bits d + tl) / 8 <? 0) with true in RL by (symmetry; apply Z.ltb_lt; lia).
    cbv beta iota zeta in RL. replace (bd_ptr d - bd_ptr d) with 0 in RL by lia.
    rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
    sids_walk_to 0x20b9c.
    eapply part_ld with (p := 0); [eassumption | eassumption | lia | lia | ideq | intros].
    sids_walk; sids_fix; post. }
  { replace (bd_ptr d - (bd_bits d + tl) / 8 <? 0) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    cbv beta iota zeta in RL.
    rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
    sids_walk_to 0x20b9c.
    all: try (exfalso; lia).
    all: eapply part_ld with (p := bd_ptr d - (bd_bits d + tl) / 8);
      [eassumption | eassumption | lia | lia | ideq | intros].
    all: sids_walk. all: sids_fix. all: post. }
Qed.
