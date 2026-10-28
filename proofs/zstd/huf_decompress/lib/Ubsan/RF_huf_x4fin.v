(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3 STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4fin () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3mulK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfK47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin>cells_bytes_C8c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin=cells_size_C8I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic3and00c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin;cells_wf_C8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission3Lib5Image:ro_bytes_bK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission3Lib5Image>ro_cells_imageK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib4Step8ro_cellsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib5Lists4List>nth_error_nth'C46Stdlib5Lists4List=nth_error_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Arr9u8ro_readC47Corelib5Lists7ListDef3nthK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin7CTZ_TABC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_divC35stdpp7tactics<f_equal_helpI47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_DEC_STACKc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin3X4MC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin<C8_of_u64arrc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin7x4m_stkc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin6x4_epiC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin;shr53_boundC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C47Corelib5Lists7ListDef6firstnK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2:x1_cell_rdC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX19x1_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX17x1_byteC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u8arr_sbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le1C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas;Zupd_lengthC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC46Stdlib4Bool4Bool>negb_false_iffC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64arr_readc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin;land_m2_shrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z6shiftlC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin8x4f_tailC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin7x4f_t7cK4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin7x4f_t78c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin7x4f_tfcC47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdK4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin8x4f_joinC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC56Stdlib6ZArith6BinInt1Z:mul_div_leK46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z4lxorK46Stdlib9micromega=RingMicromega5Psatz05K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma cells_bytes_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fin ()) [] "h02wsh12IHh21lh31wp;1p;3p;2p;6p;5p;4p10000p4p710p1000Mp4p710p8p1000ip4p7210g001UR0p4p710R1p8p10023p4p7210P1p8g002Pj14Tg0035j1?Tg003Sj1>Tg0046j1:Tg004Vj18Tg005Pj15Tg006Aj37Tg006[j1=Tg007;j2<Tg007Uj2;Tg008?j21Tg008ej1@Tg009Cj20TP0j6CTg009cj36Tg00:Cj5BTg00:ej4ATf1R0g00;Ag00<6f0R1CAp=9f4f3R2f2R3?60136p=31130=621p=2g00<k#4#4#4R4#4#4#4#?R5#>R6#:R7P6%?4R8#>R9#:R:1961#8%5137R;X07%=9,<:%=6R<,96#8%5<57:eP:%50R<P91;52R2,18R=P9%@4R4,02R2,18R>P91024R2,18R?P91024R2,18R@P91024R2,18RAP91024R2,18RBP91024R2,18RCP91024,18R2P1D3D3D3D3P9P=P9P>P9P?P9P@P9PAP9PBP9PCP9P2%53D3D3D3D357:X2:P9P81;53R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054P<C2C2C2C2C2C2C2C2,<:1960#8P1ECA6630R3,96#8%5357:eX1;X07X36P1DBW0o"). Qed.
Lemma cells_size_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fin ()) [] "h02wsh14__x1h21xh32IHh43IH0h57__arithh64__ffh78__varmaph85__with94cstrh:5cstr0h;1nh<1wh=1yp;1p;2p;3p;4p;7p;6p;5p;Bp;<g002Pj1>Tg0035j1eTg003Sj1XTg0046j1ETg00=Pj1@Tg00>Ij28Tg00>ij2ATg007;j2<Tg006[j1GTg00?@R0j11Tg00?_j25Tg008ej1JTg00@6R1j19Tg00@VR2j2KTg00A3R3j20Tg006Aj3=j1ITg00APj2YTg00B3j3WTg00BPj4STg00C7j1FTg00C\j2DTg00D8j2QTg00DVj1PTg00E4j1OTg00E_j2BTg00FBj2NTg00Fej3RTg00GHj4MTg00H3j7TTg00HWj2dTg00I9j2cTg00Iej3bTg00JDj4aTg00K6j4`Tg001Uj6_Tg009cj3^Tg00:Cj5]Tg00:ej4\Tg00KalBCTg00LGl<[Tg00Lll<ZTg00MQj3LTf1R4g00;Ag00<6f0R5C\p=?%15#1p=6g00N4R6?=45p=;1545#1p=7P6P6P6g00NSR7P7P7g00O1P1P1P1P2g00OQf5R2f4R8f3R9f2R:P4P5MBCp=VP6P6P7P7P0P1P1P9g00P4P:P4P5M<[p=2P6P6P6P7P7P7g00PXR0P1P1P1P3g00Q8R;P9P:P4g00Q[R<g00R:R=P5MBCp=UP6P6P6P7P7P7P0P1P1P1P3P;P2P8P9P:P4P5MBCp=:P6P7P5P1P4P:P9P8P2f6f7f8M<Zp=HAL7:4=L75p=310:4/05p=4g00<kR8#>#>#>R1#>#>#>#e#XR;#ER3P;1?;5#@%6<#6#6#6R018;5'A';R>X031<6<%G;R?,?;#@18;?,A0';eP618;4R?,A0R@%65#6#6#618;:RA17A<,7A,7A,7A,7A,7A,7A'7';X;6%1@RA#1RB#1RC#1RD#1RE#1RF#1RG#1RH15?<R<#1RI,5?RJ#1RK,5?RL#1RM,5?RN#1RO,5?RP#1RQ,5?RR#1RS,5?RT#1RU,5?RV#1RW';%J1R1%9?RX'KRY%J8RZ'0R[/0ZR\/0ZR]/0ZR^/0ZR_/0ZR`/0ZRa/0ZRb10X=Rc/0ZRd,0XRe/0ZRf,0XRg/0ZRh,0XRi/0ZRj,0XRk/0ZRl,0XRm/0ZRn,0XRo/0ZRp,0XRq/0ZRr5=7%I6Rs%I7Rt%94%955=71;451Y453WX=6X26R6PHPb105ZX27RbPGPaPbPFP`PbPEP_PbPDP^PbPCP]PbPBP\PbPAP[PbP@PYP0P11<71P?PX1<7XR[EVRAC2C2C2C2C2C2C2C2PWPrPbPVPqP?PXP[PUPpPbPTPoP?PXP[PSPnPbPRPmP?PXP[PQPlPbPPPkP?PXP[POPjPbPNPiP?PXP[PMPhPbPLPgP?PXP[PKPfPbPJPeP?PXP[PIPdPbP<PcP?PXP[1<7=CUC2E:C2E:C2E:C2E:C2E:C2E:C2E:C2M9H1?;4#@R[/;@%9[RX==7YR?PsPtP6P[PX1<7XP@PYPAM9HP5CSP?1?;:#@R?#F%9?,D=18;9R9#F%99,D=g00RXR9#G%E91Q74%P7%O7R9g00SDg00ScR?P?g00TCR?P71B711N78R85R71B7ZRA;3A?3AA?3AA?3AAg00Tc1B7==38A=38A=38A=38A=38A=38A=38A=38ACMg00UJFT1d9?P5P:g00UjR?g00VJR9'<1c5:==?9dAb7=4Cab6b7b8X171K15?4ZZ?4ZZ?4ZZ?4ZZA45=Z=45Z=45Z=45Z=45Z=45Z=45Z=45Z5=7^17P518;2#9O1b5b:b9b4C`P[P5E_A^;:4R:,?;#@18;:,A0';eX3>X03X<;P5D]W0o"). Qed.
Lemma cells_wf_C8 : forall ws, cells_wf (map C8 ws).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fin ()) [] "h02wsh12IHh21wp;1p;4p;3p;5g002Pj10Tg0035j1:Tg003Sj14Tg0046j13Tg00Vjj11Tg006[j19Tg00Waj45Tg009cj36Tg00:Cj57Tg00:ej48Tf1R0g00;Ag00<6f0R1C8p=2g00<k#0#0#0#0#0#0#:#4R2#3R3P21221#1R4X03g00X<R5%92,22#1eg00XX1220#1P5P1C5f2=620,22#1eX14X03X22P1D7W0o"). Qed.

Lemma u64arr_of_C8 : forall segs m A ws, rw_cells segs m A (map C8 ws) -> u64arr segs m A ws.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fin ()) [] "h02Hwh11Hh22Hbh31Ah42_Hh51lh61mh71nh84segsh92wsh:1zp;1p;4p;6p;2g0046j18Tg002Pj14Tg0035j1@Tg003Sj1<Tg00Y4j1JTg00YVj4HTg00ZLj4>Tg00=Pj16Tg00@6j12Tg00[Cj41Tg00\5j4;Tg00Vjj1:Tg004Vj19Tg00\hj45Tg005Pj1BTg00]]j1ITg000Mj67Tg00?@j13Tg00>Ij2?Tg00>ij2=Tg00^cj1GTg008ej1ETg00@Vj2ATg00OQj2DTg00Waj4CTg00:ej4FTf1R0g00;Ag00<6f0R1CFp=0g00_h#8g00<k#4#4#4R2#4#4#4#@#<R3%@2#<R4#J[g00NSR5%83f3R6f2R7P01031CHg00`gR8f4R9P6P71030R:C>P9P6P7%6:#2C1f5R:P9P6P7C;P1f6R7P:P91036C>P81039R9#:f7R8P7P:%99C5f8R9P8P7103:#6#2C1f9R:P9P8P7C;[P11037#:f:R7P:P91038#9C5f;R8P7P:1039#6#2C1%84R4103:#9f=R9f<R6P8P1C5X54P0%B:R4%I:E7P6P8P7P4C5g00N4R41037#6f>R:P9P6%21C1X74P0g00Q[#3#3#3#3#3#3#3#3R41?37'=R;%G7E7P9P6P8%2;C1P:P9P6%B8C5P:P9P6%E21?38R8#2R3'AC1P0P51=48#2f?P:P9P1C1X:5P1%24/A3R31D48E7P:P9P6P3C1P1b0CCb0b2W0W2W4P0P1O2n2001000000121000000W1P0P1O2n2001000000121000000W1W9W3W6W8o"). Qed.
Lemma C8_of_u64arr : forall segs m A ws, u64arr segs m A ws -> rw_cells segs m A (map C8 ws).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fin ()) [] "h01Ah11Hh22Hbh32Hwh41lh51mh61nh74segsh82wsh91zp;1p;4p;2p;6g0046j19Tg002Pj12Tg0035j1;Tg003Sj1:Tg00Y4j1JTg00\5j4ETg005Pj16Tg00\hj44Tg008ej1>Tg00>Ij27Tg00@6j11Tg00@Vj25Tg00[Cj43Tg00:ej4=Tg00YVj4ITg00ZLj4HTg00=Pj1DTg00Vjj1CTg004Vj1BTg00aBj1@Tg00]]j1ATg001Uj68Tg00Waj4<Tg00?@j10Tg00>ij2?Tg00OQj2FTg00^cj1GTg00_h#9g00<k#2#2#2R0#2#2#2#;#:R1%;0#:R2#J[g00NSR3%91f3R4f2R5f1R6f0R7CEg00`gf4R8P4P5%66C4P8P4P5%>0R01716#1'5C3f5R9P8P4P1g00;AR:g00<6R;P5C=CIP7f6R5P9P8%64C4f7R4P5P91718#1,50C3f8R0P4P5P1P:P;P9C=R;CHP0P4P5%D;R:#1C3%C;P0P4P5%B;R;C4%@9%92R2%69f9R5P0P4P7C4X42P6P;%A9E8C<g00N4R;g00Q[#0#0#0#0#0#0#0#0R21719R1'?R8P5P0P4%17C3X6;P3%12%11'5P5P0P4P7C3X93P7%181F21E8P:%G9E8C<W3W2P6P7O2n2001000000121000000W1W8W0W5W7o"). Qed.

(* [comment removed for export] *)
Definition CTZ_TAB : list Z :=
  [0; 1; 2; 7; 3; 13; 8; 19; 4; 25; 14; 28; 9; 34; 20; 40; 5; 17; 26; 38; 15; 46; 29; 48; 10; 31; 35; 54; 21; 50; 41; 57;
   63; 6; 12; 18; 24; 27; 33; 39; 16; 37; 45; 47; 30; 53; 49; 56; 62; 11; 23; 32; 36; 44; 52; 55; 61; 22; 43; 51; 60; 42; 59; 58].

Lemma ctz_tab_rd : forall m1 i, mem_inv usegs m1 -> 0 <= i < 64 ->
  ov_read_bytes usegs m1 (Z_to_bv 64 (66784 + i)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat i) CTZ_TAB 0)].
Proof.
  intros m1 i MI Hi.
  assert (RB : ro_bytes_b usegs 66784 (map (Z_to_bv 8) CTZ_TAB) = true) by (vm_compute; reflexivity).
  assert (BA : bytes_at usegs m1 66784 (map (Z_to_bv 8) CTZ_TAB))
    by (apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn; lia | apply ro_bytes_b_sound; exact RB]).
  exact (src_rd usegs m1 66784 CTZ_TAB i BA ltac:(cbn; lia)).
Qed.

Lemma ctz_tab_range : forall i, 0 <= i < 64 -> 0 <= nth (Z.to_nat i) CTZ_TAB 0 < 64.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fin ()) [] "h01Hh14__x1h21mh31nh42H1h52H2h67__arithh74__ffh88__varmaph95__with:2b1h;2b2h<2H0h=2Hih>1ih?2i0p;2p;1p;3p;4p;6p;7p;8g00C\j22Tg002Pj17Tg008ej1GTg00c9j24Tg00`gR0j23Tg01<?j26Tg01<\j25Tg01=9j2:Tg007;j2CTg00j>j1=Tg01=Wj3@Tg006[j1WTg0046j1VTg00D8j2UTg00DVj1RTg00E4j1QTg00E_j2>Tg00FBj2LTg00GHj4;Tg011nj1FTg00MQj3ETg00HWj2DTg00I9j2HTg00Iej3ITg00JDj4JTg00A3j2KTg01>Tj6BTg01?Tj2ATg01@5j2MTg01@Uj2NTg015:j4OTg006Aj3PTg00H3j7?Tg016:j7STg016^j8TTg00NSR1f0R2#=g017ig00R:R3COp=1g00UjR4g00VJR57P2p=0f1R6g00SDR7g00ScR8P8g00TCR9P2g00UJF?p=9f2R:P7P8P8P9P6P2FSp=<f3R;P7P8P8P9P:P6P2GTp=81232g00<kR7#7#7#7#7#7#7#GR<,42R='3R>%12R?,6315?<':X?1R?P3P<1C45R5%=<9@?3#0dP6g00RXR@#WRA%V@R@1U16RB%R1RC%Q1RDP11>13REg017B1L17R7C;,9DRFP1P7g01;XRG1>1<RHC;,9DRI5<DRJ%F8R8P1P7PGAE1EHC;,9D9<DFC81DD9R9P2P:P51H2:#0dAI136CJR5b7b8b9X111236RH1K3<,46'3\>^11P2P:P6O2b6EBP?P6O1#0P01:62#0%0:R?%06R>'3[RE%02,3>1::6#0R>[%0;/3?\>1A62P6n2001000000120000000X;4X:4PE^;4^:4P2%1;R4,63RE154<R4P6O3%0E%04'3P0f4#1R4,63#0154<#0f5#1R4,23144<'3P2f6#1,63#0f7#1/5<#0P01662#012:6[R4126216:6#0RE[12;:\E1M62P6n2001000000120000000X21X31P4^21^31P2P3f9#1R4P:O31234P01562#014:6[R0146215:6#0R4[14;:\41N62P6n2001000000120000000X21X31P0^21^31P2f;#1R0P<P;O3140<PAP@PBPCPDPIP8PDPFP8PJC8C8P9P5b7b8b9X11123:14:<'3\H\=^11P2f=#1P6P;O3b6b5b0b4b0W5W4P6P2O2n2001000000121000000b0b<b0W=X>1o"). Qed.

(* [comment removed for export] *)
Lemma land_m2_shr : forall X, 0 <= X < 2^64 -> Z.land (X ≫ 52) 18446744073709551614 = 2 * (X ≫ 53).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fin ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh64__p1h71nh81Bh91Hh:1ah;1mh<2HXh=1Xh>1Yh?1yp;1p;2p;6p;3p;4p;5p;8p;7g002Pj17Tg008ej1:Tg00f4j2JTg00c9j25Tg00`gR0j2;Tg00cUj10Tg009Cj22Tg01A5j2UTg006[j1OTg0046j1NTg00D8j2MTg00DVj1lTg00E4j1jTg00E_j2@Tg00FBj2_Tg015Vj6[Tg011nj1YTg00HWj2XTg007;j2CTg00I9j2WTg00Iej3VTg00JDj4TTg01A\j21Tg00e3j1RTg0035j1LTg00eQj3KTg00Fej3PTg00@Vj29j1`Tg01B9j5QTg01Bej3BTg001Uj6=Tg00Waj4STg01CNj2ITg01Clj2HTg00j>j1iTg01=Wj3hTg00MQj3cTg00A3j2bTg01>Tj6aTg01DIj2^Tg00GHj4ETg01Dij6]Tg006Aj3GTg01EMj5\Tg01Enj8dTg00C\j2eTg00H3j7ZTg016:j7fTg016^j8gTg00R:R1f0R2'ep=4%72#7p=>g00NSR3f1R4g017BP2CEp=FP4g00SDR5g00ScR6P6g00TCR7P2g00UJFZp=3f2R8P5P6P6P7P4P2Ffp=Af3R9P5P6P6P7P8P4P2Ggp=Dg00UjR:g00VJR;7G2p=?P3P4g01;XP2CEp=<%02#0#0#0p=k%02#0#0#0#0#0#0#0p=8AG342p=6%42R<g00<kR=#7R>#:R?%7>#>#>R>#:'JR@,52RA';%0=RB#7#0#7RC#7RD#:RE,24RF#4RG%>>#>#>#:RH,5FRIP01242#4%48RJ[%44RK1284#4[RL1298#4\J1U42P2n2001000000120000000X73X:3PL^73^:3P2P8PEp-0RLg00RXRM#ORN%NMRM1M34RO%l3RP%j3RQ1@31RR1_3=R='F,3QRSPQP5P6P6P7P9E[RT5AQ%Y6RUPSCD1XQ7RVP2P81C:;R;1W28#?dAV314CTR:b1b2b3X43W61;<4PK[^43^6LP2159@P9P8O3b0O3b9P31J?ER@,14152HRWX53P4P@PHPNPM%R3RXPP1@3?RY%LD5K3RD,<R,3QPVP:b1b2b3151@P2b0PNPMPOPPPQ%L>9K3Y,<=,3Q9AQTPU1@3HRT9P3D,<=,3QCDPVP:b1b2b3X43X6L1;4A19@H,54[^43^6LP2PJP8P4O3b0DQPFPNPMPXPP1@3E,FR,3QPVP:b1b2b3%4EP2b0RF9B4EE=CS1;GI%0B#k#8#8#8#8#8#8#8#7#:RB,I2112?RI,9?'HX?3RGP1PHP;%iH9hG1#?d128ER;PNPMPOPPPQ1<=T,3Q9AQSPUAc3RT,<=,3Q9AQSCDPVP:b1b2b3X431;<W1b1H,54,;K[^43P2129EP4O2b0EaPGP;O1#?P01H42#?1684[R016421H84#?R;[1698\;1^42P4n2001000000120000000X;3X73P0^;3^73P2f4/2ER0/IBR;110?,9?R0P4O316;0P3f5R0/2ER;/1?R4,9?f6R9%0C#:RC'2R8,9?,62X53P3P3%`?RGPGP4120CR4P3\3/CGP3110@RG16I8X53P31J?CR8,10RI119@/1?/62X53P319@?,101198,62X531C3I11G?P0P@P?PNPMPXPPPQP5P6P6P7P3PDg00TcPRCE,3QE]PVP:b1b2b3AG3@1g01FK[P2b0PNPMPXPP1<RY,3QPVP:b1b2b3151?P2b0D\E=P4PNPMPXPP1@3C,FR,3QPVP:b1b2b3%4CP2b09B0CE=P;AB0EFE=Gd1I;BP2E=b8b9b8b>W<X=3o"). Qed.

Lemma shr53_bound : forall X, 0 <= X < 2^64 -> 0 <= X ≫ 53 < 2048.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fin ()) [] "h07__arithh14__ffh24__p1h38__varmaph45__with54__x1h61ah71nh81Hh92HXh:1Xh;1zp;1p;2p;4p;6p;3p;5p;7p;8g002Pj11Tg008ej14Tg00f4j2@Tg00c9j22Tg00`gR0j28Tg00cUj19Tg009Cj25Tg01A5j2DTg006[j1CTg0046j1BTg00D8j2ATg00DVj1[Tg00E4j1VTg00E_j27Tg00FBj2UTg00GHj4;Tg015Vj6NTg011nj1MTg00HWj2GTg007;j2FTg00I9j2ETg006Aj3HTg00Iej3ITg00JDj4JTg01A\j2KTg00e3j1LTg0035j1<Tg00eQj3=Tg00Fej3OTg00@Vj2PTg01B9j5QTg01Bej3RTg001Uj6STg00Waj4TTg00C\j2ZTg00H3j7YTg016:j7XTg016^j8WTg00R:R1f0R2'Zp=0%12#1p=6f1R3g00SDR4g00ScR5P5g00TCR6P2g00UJFYp=3f2R7P4P5P5P6P3P2FXp=?f3R8P4P5P5P6P7P3P2GWp=>g00NSR9P3g01;XP2C;p=:%02R:g00<kR;#1R<#4R=%1<#6#6R<#4'@R>,22R?'8%9;#1#9#1#9R@#4RA,53RB#0%1<#6#6#4RC,2BP01532#0%07R0[%03RD1573#0[RE1587#0\01D32P2n2001000000120000000X79X69PE^79^69P2P7PAp-0REg00RXRF#CRG%BFRF1A93RH%[9RI%V9RJP91791RKg017BRL1U9;R;C;,3JRMPJP4P5P5P6P8ENR45?J%M5R5PMC>1GJ6R6P2P7g00UjRMg00VJRN'F1E27=HMNdAI913CJRNb1b3b4X59W218:3PD[^59^2EP2128>P8P7O3b0O3b8P91@=AR8,K3122CX;9P3P8PCPGPF%L9R>PI179=R=%<@5=9R@,:K,3JP6PNb1b3b41218P2b0PGPFPHPIPJ%<<9=9=,:;,3J9?J4P5179C9O9@,:;,3JC>P6PNb1b3b4X59X2E183?1P8C,23[^59^2EP2P0P7P3O3b0DQPBPGPFP>PIP9PKPL179AC;,3JP6PNb1b3b4%0AP2b09R3AESCTW9X:9o"). Qed.


Definition fw_is_uim (segs : list Segment) (a : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 a) with Some w => Z.eqb (bv_unsigned w) 3221229683 | None => false end.

Definition fw_is_chk (segs : list Segment) (pc : Z) : bool :=
  fw_is_uim segs pc ||
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => match decode_any w with
              | Some (Jal rd imm, _) => Z.eqb (bv_unsigned rd) 0 && fw_is_uim segs (pc + bv_signed imm)
              | _ => false end
  | None => false end.

Lemma fw_idx_bound : forall c b, 0 <= (c ≪ b mod 2^64) ≫ 53 < 2^11.
Proof.
  intros c b. pose proof (Z.mod_pos_bound (c ≪ b) (2^64) ltac:(lia)) as M.
  pose proof (shr53_bound (c ≪ b mod 2^64) M) as B. change (2^11) with 2048. exact B.
Qed.

Lemma fw_shl1 : forall v, v ≪ 1 = 2 * v.
Proof. intros v. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma fw_srl3 : forall x, 0 <= x < 2^32 -> bv_swrap 32 (bv_wrap 32 x ≫ 3) mod 18446744073709551616 = x / 8.
Proof.
  intros x H. rewrite srliw_val by lia. rewrite (Z.mod_small x) by lia. change (2^3) with 8.
  apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma fw_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma fw_shr58 : forall X, 0 <= (X mod 2^64) ≫ 58 < 64.
Proof.
  intros X. pose proof (Z.mod_pos_bound X (2^64) ltac:(lia)). rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Ltac x4open XM :=
  destruct XM as ((buf & OUT & LB) & SRC & CBS & ST & (j0 & J0) & SPS & LS & WS & LW & FA & LF & FR & MI & MU & WM).

Ltac weq := first [ reflexivity | f_equal; lia ].

Ltac fw_idx :=
  lazymatch goal with |- context [Z.shiftr (Z.modulo (Z.shiftl ?c ?b) ?M) 53] =>
    let v := fresh "v" in let EV := fresh "EV" in let VR := fresh "VR" in
    remember (Z.shiftr (Z.modulo (Z.shiftl c b) M) 53) as v eqn:EV;
    assert (VR : 0 <= v < 2^11) by (subst v; apply fw_idx_bound);
    clear EV end.

Ltac fw_cell DT cells cbs ECB TOK :=
  lazymatch goal with
  | VR : 0 <= ?v < 2^11, CE : bytes_at usegs ?mm (DT + 4) cbs |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | _ : ov_read_bytes usegs mm (Z_to_bv 64 (DT + 4 + 2 * v)) 1 = _ |- _ => fail
    | |- _ =>
      let RC0 := fresh "RC" in let RC1 := fresh "RC" in
      let TK := fresh "TK" in pose proof TOK as TK;
      let TLEN := fresh "TLEN" in let TCK := fresh "TCK" in
      destruct TK as (_ & TLEN & TCK); unfold FseNCount.Zlength in TLEN;
      destruct (x1_cell_rd usegs mm (DT + 4) cells 4096 v ltac:(rewrite <- ECB; exact CE) ltac:(lia) ltac:(lia)
                  ltac:(change (2^11) with 2048 in TLEN; lia))
        as [RC0 RC1];
      let c := fresh "c" in let EC := fresh "EC" in
      remember (nth (Z.to_nat v) cells x1_default) as c eqn:EC;
      let NB := fresh "NB" in let BY := fresh "BY" in
      destruct (TCK v ltac:(lia)) as (NB & BY); rewrite <- EC in NB, BY; clear EC TCK TLEN
    end
  end.

Ltac fw_byte :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 8 (x1_nbBits ?c))] => rewrite (byte_lit (x1_nbBits c)) by lia
  | |- context [bv_unsigned (Z_to_bv 8 (x1_byte ?c))] => rewrite (byte_lit (x1_byte c)) by lia
  end.

Ltac fw_store DST :=
  lazymatch goal with OUT : u8arr _ _ DST _ |- _ =>
    let a := cur_mem_addr in let E := addr_expr a in
    u8_sok OUT (E - DST); zstep; u8_store_same OUT (E - DST) end.

Ltac fw_ctzv :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 8 (nth (Z.to_nat ?i) CTZ_TAB 0))] =>
    let CR := fresh "CR" in
    pose proof (ctz_tab_range i ltac:(first [apply fw_shr58 | lia])) as CR;
    rewrite (byte_lit (nth (Z.to_nat i) CTZ_TAB 0)) by lia;
    let cz := fresh "cz" in let EZ := fresh "EZ" in
    remember (nth (Z.to_nat i) CTZ_TAB 0) as cz eqn:EZ; clear EZ end.

Ltac fw_shl_lit :=
  repeat match goal with |- context [Z.shiftl ?x ?c] =>
    is_Zlit c; rewrite (Z.shiftl_mul_pow2 x c) by lia;
    let p := eval vm_compute in (2 ^ c) in change (2 ^ c) with p end.

Ltac fw_shr_lit :=
  repeat match goal with |- context [Z.shiftr ?x ?c] =>
    is_Zlit c; rewrite (Z.shiftr_div_pow2 x c) by lia;
    let p := eval vm_compute in (2 ^ c) in change (2 ^ c) with p end.

Ltac fw_sh_in H :=
  repeat match type of H with
  | context [Z.shiftl ?x ?c] => is_Zlit c; rewrite (Z.shiftl_mul_pow2 x c) in H by lia;
      let p := eval vm_compute in (2 ^ c) in change (2 ^ c) with p in H
  | context [Z.shiftr ?x ?c] => is_Zlit c; rewrite (Z.shiftr_div_pow2 x c) in H by lia;
      let p := eval vm_compute in (2 ^ c) in change (2 ^ c) with p in H
  end.

Ltac fw_norm :=
  try fw_idx; rewrite ?fw_shl1; fw_shl_lit; rewrite ?fw_land7; rewrite ?fw_srl3 by lia; fw_shr_lit;
  rewrite ?wrap32_small by lia; rewrite ?swrap32_small by lia; fw_byte; fw_ctzv.

Ltac fw_ltb H :=
  repeat match type of H with context [?a <? ?b] =>
    first [ replace (a <? b) with true in H by (symmetry; apply Z.ltb_lt; lia)
          | replace (a <? b) with false in H by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z] in H;
  repeat match type of H with context [Z.lxor ?a ?b] =>
    is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H end.

Ltac fw_hnorm H :=
  rewrite ?fw_srl3 in H by lia; fw_sh_in H; rewrite ?wrap32_small in H by lia; rewrite ?swrap32_small in H by lia.

Ltac fw_refute H := exfalso; fw_hnorm H; try fw_ltb H; lia.

Ltac fw_gen src :=
  repeat match goal with |- context [Z_to_bv 64 ?E] =>
    lazymatch E with context [Znth _ src] =>
      let w := fresh "w" in let EW := fresh "EW" in
      remember (Z_to_bv 64 E) as w eqn:EW; clear EW;
      lazymatch goal with |- context [Z_to_bv 64 E] => fail 1 | _ => idtac end end end.

Ltac fw_clear_rd src := repeat match goal with
  | H : ov_read_bytes _ _ _ 8 = Some (le8 _) |- _ => clear H
  | H : ov_read_bytes _ _ _ _ = Some [Z_to_bv 8 (Znth _ src)] |- _ => clear H
  | H : ov_read_bytes _ _ _ _ = Some [Z_to_bv 8 (x1_nbBits _)] |- _ => clear H
  | H : ov_read_bytes _ _ _ _ = Some [Z_to_bv 8 (x1_byte _)] |- _ => clear H end.

Ltac fw_cell_at E DT cells cbs ECB TOK :=
  lazymatch E with
  | DT + 4 + 2 * ?v + 1 => idtac
  | DT + 4 + 2 * ?v => idtac
  end; fw_cell DT cells cbs ECB TOK.

Ltac fw_src_at E SS src :=
  lazymatch goal with SRC : bytes_at usegs ?mm SS (map (Z_to_bv 8) src) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let R := fresh "RS" in
    pose proof (src_rd usegs mm SS src (E - SS) SRC ltac:(lia)) as R;
    replace (SS + (E - SS)) with E in R by lia end.

Ltac fw_ctz_at E :=
  lazymatch E with
  | 66784 + ?i =>
    lazymatch goal with MI : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let R := fresh "RZ" in
      pose proof (ctz_tab_rd mm i MI ltac:(first [apply fw_shr58 | lia])) as R end
  end.

Ltac fw_frame_at E :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with
    | W : u64arr usegs mm ?A ?ws, N : nth_error ?ws (Z.to_nat ?i) = Some ?w |- _ =>
        let EQ := fresh "EQ" in assert (EQ : E = A + 8 * i) by ring;
        let R := fresh "RF" in
        pose proof (u64arr_read usegs mm A ws i w (Z_to_bv 64 E) W N ltac:(lia) ltac:(unfold wa; rewrite EQ; reflexivity)) as R;
        clear EQ
    | W : u64arr usegs mm ?A ?ws, N : nth_error ?ws ?j = Some ?w |- _ =>
        let i := eval vm_compute in (Z.of_nat j) in
        let EQ := fresh "EQ" in assert (EQ : E = A + 8 * i) by ring;
        let R := fresh "RF" in
        pose proof (u64arr_read usegs mm A ws i w (Z_to_bv 64 E) W N ltac:(lia) ltac:(unfold wa; rewrite EQ; reflexivity)) as R;
        clear EQ
    end end.

Ltac fw_frame_st E :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with
    | W : u64arr usegs mm ?A ?ws, N : nth_error ?ws (Z.to_nat ?i) = Some _ |- _ =>
        let EQ := fresh "EQ" in assert (EQ : E = A + 8 * i) by ring; clear EQ;
        let a := cur_mem_addr in
        let SOK := fresh "SOK" in
        pose proof (u64arr_store_ok usegs mm A ws i a W ltac:(rewrite ?upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
        zstep;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?a2 (le8 ?v)) _) =>
          let E2 := addr_expr a2 in
          let W' := fresh "W" in
          assert (W' : u64arr usegs (write_to_mem mm (wa E2) (le8 v)) A (upd ws (Z.to_nat i) v));
          [ replace (wa E2) with (wa (A + 8 * i)) by (unfold wa; f_equal; lia);
            apply (u64arr_write usegs mm A ws i v W); rewrite ?upd_length; lia
          | clear W; store_done; rename W' into W ]
        end
    end end.

Ltac fw_memop :=
  lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ _ _, _) => constr:(false)
    | Some (Store _ _ _ _, _) => constr:(true)
    end end end.

Ltac fw_mem sp DT cells cbs ECB TOK SS src DST :=
  let st := fw_memop in
  let a := cur_mem_addr in let E := addr_expr a in
  lazymatch st with
  | true => first [ fw_store DST | fw_frame_st E | zstep ]
  | false =>
      lazymatch E with
      | context [bv_unsigned sp] => first [ fw_frame_at E; zstep | zstep ]
      | _ => first [ fw_cell_at E DT cells cbs ECB TOK; zstep | fw_ctz_at E; zstep | fw_src_at E SS src; zstep | zstep ]
      end
  end; fw_clear_rd src.

Ltac fw_one sp DT cells cbs ECB TOK SS src DST :=
  fw_norm; first [ fw_mem sp DT cells cbs ECB TOK SS src DST | zstep ]; fw_gen src.

Ltac fw_step stops sp DT cells cbs ECB TOK SS src DST :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (fw_is_chk usegs pc)) with
      | true => fail
      | false => fw_one sp DT cells cbs ECB TOK SS src DST
      end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "B" in if_cases H; zify_cond H;
      try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
             lazymatch eval vm_compute in (fw_is_chk usegs pc) with
             | true => solve [fw_refute H]
             end end)
  end.

Ltac fwalk stops sp DT cells cbs ECB TOK SS src DST := repeat (fw_step stops sp DT cells cbs ECB TOK SS src DST).

Section CANSEC1. Context {rc : runConstT}.
Section X4F.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells 11.
  Hypothesis ECB : cbs = firstn 4096 (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 4096.
  Hypothesis D8 : 8 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4096 <= lo.
  Hypothesis DJ1 : DT + 4 + 4096 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition X4M (mm : fmem) (sps ws fa : list word) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ stk usegs mm lo (SP + -512)
    /\ (exists j0, rw_cells usegs mm (SP + -512) [CB 56 j0])
    /\ u64arr usegs mm (SP + -456) sps /\ length sps = 10%nat
    /\ u64arr usegs mm (SP + -376) ws /\ length ws = 19%nat
    /\ u64arr usegs mm (SP + -224) fa /\ length fa = 15%nat
    /\ rw_cells usegs mm (SP + -104) FRS
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  (* [comment removed for export] *)
  Lemma x4_epi : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk usegs mm lo (SP + -104) -> rw_cells usegs mm (SP + -104) FRS ->
    mem_inv usegs mm -> munch DW m0 mm -> wmono usegs m0 mm ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1826c) fc None mm (seg_rom usegs)).
Proof using All.
    intros until xra. intros ST FR MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 14 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Ltac rel_arr H ST hi :=
    apply C8_of_u64arr in H;
    eapply stk_release in H; [ | exact ST | lia ];
    clear ST; rename H into ST; rewrite cells_size_C8 in ST;
    lazymatch type of ST with stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia end.

  Lemma x4m_stk : forall mm sps ws fa, X4M mm sps ws fa -> stk usegs mm lo (SP + -104).
Proof using All.
    intros mm sps ws fa (BUF & SRC & CBS & ST & (j0 & J0) & SPS & LS & WS & LW & FA & LF & FR & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    release_frame J0 ST (SP + -456).
    rel_arr SPS ST (SP + -376).
    rel_arr WS ST (SP + -224).
    rel_arr FA ST (SP + -104).
    exact ST.
  Qed.

  (* [comment removed for export] *)
  Lemma x4_err : forall mm sps ws fa (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    X4M mm sps ws fa ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x18268) fc None mm (seg_rom usegs)).
Proof using All.
    intros until xra. intros XM.
    pose proof (x4m_stk _ _ _ _ XM) as STK.
    destruct XM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & MI & MU & WM).
    zstep.
    eapply x4_epi; eassumption.
  Qed.

  (* [comment removed for export] *)
  Ltac x4pack OUT LB :=
    split; [eexists; split; [exact OUT| rewrite ?Zupd_length; exact LB]|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eexists; eassumption|];
    repeat (split; [eassumption|]); eassumption.


  Ltac fwk stops := fwalk stops sp DT cells cbs ECB TOK SS src DST.
  Ltac fwf := fw_one sp DT cells cbs ECB TOK SS src DST.

  (* [comment removed for export] *)
  Section STREAM.
  Variables (k SE OPk : Z) (sps ws fa : list word).
  Hypothesis K4 : 0 <= k < 4.
  Hypothesis HSE : DST <= OPk <= SE.
  Hypothesis HSE2 : SE <= DST + dcap.
  Hypothesis WOP : nth_error ws (Z.to_nat (4 + k)) = Some (Z_to_bv 64 OPk).


  (* [comment removed for export] *)
  Notation T6 := (Z_to_bv 64 (SP + -344 + 8 * k)).
  Notation SEND pc mm xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x23 x24 x27 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 2) x8 x9 (Z_to_bv 64 66784) (Z_to_bv 64 k) a2 a3 a4 a5
             (Z_to_bv 64 (- DT - 5)) a7 x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 x23 x24 (Z_to_bv 64 SE) (Z_to_bv 64 (SE - OPk)) x27
             (Z_to_bv 64 (-1)) (Z_to_bv 64 ((dcap + 3) / 4)) (Z_to_bv 64 64) T6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Hypothesis CONT : forall mm (xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x23 x24 x27 : word),
    X4M mm sps ws fa -> evt usegs POST (SEND 0x17804 mm xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x23 x24 x27).

  (* [comment removed for export] *)
  Notation TL pc mm ra3 ra5 ra7 xra t0 t1 x8 x9 a2 a4 x18 x19 x20 x22 x23 x24 x27 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 2) x8 x9 (Z_to_bv 64 66784) (Z_to_bv 64 k) a2
             ra3 a4 ra5 (Z_to_bv 64 (- DT - 5)) ra7 x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 x23 x24
             (Z_to_bv 64 SE) (Z_to_bv 64 (SE - OPk)) x27 (Z_to_bv 64 (-1)) (Z_to_bv 64 ((dcap + 3) / 4)) (Z_to_bv 64 64) T6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma x4f_tail : forall (N : nat) cnt p mm (ra3 ra5 ra7 xra t0 t1 x8 x9 a2 a4 x18 x19 x20 x22 x23 x24 x27 : word),
    ra3 = Z_to_bv 64 cnt -> ra5 = Z_to_bv 64 p -> ra7 = Z_to_bv 64 p ->
    X4M mm sps ws fa -> cnt <= Z.of_nat N -> OPk <= p -> p + cnt = SE -> 0 < cnt ->
    evt usegs POST (TL 0x177c4 mm ra3 ra5 ra7 xra t0 t1 x8 x9 a2 a4 x18 x19 x20 x22 x23 x24 x27).
  Proof using All.
    induction N as [|N IH]; intros cnt p mm ra3 ra5 ra7 xra t0 t1 x8 x9 a2 a4 x18 x19 x20 x22 x23 x24 x27 -> -> -> XM P0 P1 P2 P3; [lia|].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    x4open XM.
    fwf.
    fwk [0x177c4; 0x17804].
    - eapply IH; first [ weq | x4pack OUT LB | lia ].
    - eapply CONT. x4pack OUT LB.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation L4 pc mm rra rs0 rs2 rs6 rs7 rs8 rs9 rs10 rs11 ra5 ra7 rt6 t0 t1 x9 a2 a3 a4 x19 x20 :=
    (MS (mkR rra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 2) rs0 x9 (Z_to_bv 64 66784)
             (Z_to_bv 64 k) a2 a3 a4 ra5 (Z_to_bv 64 (- DT - 5)) ra7 rs2 x19 x20
             (Z_to_bv 64 (DT + 4)) rs6 rs7 rs8 rs9 rs10 rs11 (Z_to_bv 64 (-1)) (Z_to_bv 64 ((dcap + 3) / 4)) (Z_to_bv 64 64) rt6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).


  (* [comment removed for export] *)
  Lemma x4f_loop4 : forall (fuel : nat) ptr bc p mm (rra rs0 rs2 rs6 rs7 rs8 rs9 rs10 rs11 ra5 ra7 rt6 t0 t1 x9 a2 a3 a4 x19 x20 : word),
    rra = Z_to_bv 64 ptr -> rs0 = Z_to_bv 64 SS -> rs2 = Z_to_bv 64 (SS + 8) -> rs6 = Z_to_bv 64 SE -> rs7 = Z_to_bv 64 (SE - 3) ->
    rs8 = Z_to_bv 64 (p + 3) -> rs9 = Z_to_bv 64 SE -> rs10 = Z_to_bv 64 (SE - OPk) -> rs11 = Z_to_bv 64 bc ->
    ra5 = Z_to_bv 64 p -> ra7 = Z_to_bv 64 p -> rt6 = T6 ->
    X4M mm sps ws fa -> OPk <= p <= SE -> SE - p < 4 * Z.of_nat fuel ->
    SS <= ptr -> ptr + 8 <= SS + n -> 0 <= bc <= 64 ->
    evt usegs POST (L4 0x174fc mm rra rs0 rs2 rs6 rs7 rs8 rs9 rs10 rs11 ra5 ra7 rt6 t0 t1 x9 a2 a3 a4 x19 x20).
  Proof using All.
    induction fuel as [|fuel IH]; intros ptr bc p mm rra rs0 rs2 rs6 rs7 rs8 rs9 rs10 rs11 ra5 ra7 rt6 t0 t1 x9 a2 a3 a4 x19 x20
      -> -> -> -> -> -> -> -> -> -> -> -> XM P1 P2 Q1 Q2 Q3; [lia|].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    x4open XM.
    fwf.
    fwk [0x174fc; 0x177c4; 0x17804].
    all: first [ (eapply IH; try first [ weq | x4pack OUT LB | lia ]); first [ weq | x4pack OUT LB | lia ]
               | eapply (x4f_tail (Z.to_nat dcap)); first [ weq | x4pack OUT LB | lia ]
               | eapply CONT; x4pack OUT LB ].
  Qed.

  End STREAM.

End X4F.
End CANSEC1.
