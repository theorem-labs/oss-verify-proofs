(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_y4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4fin () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3mulK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfK47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4finAy4_cells_bytes_C8C47Corelib4Init5Logic6eq_indc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin@y4_cells_size_C8I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic3and00c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin>y4_cells_wf_C8C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z=shiftr_nonnegK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_divC35stdpp7tactics<f_equal_helpK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_DEC_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast3Y4MC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin?y4_C8_of_u64arrc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin7y4m_stkc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin6y4_epiC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast3SPSC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64arr_readK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u64arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC46Stdlib5Lists4List:length_mapK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:upd_lengthC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin6y4_errC46Stdlib4Bool4Bool>negb_false_iffC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5aluop02I46Stdlib;setoid_ring<Ring_polynom3Mon00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_gec5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin8y4f_nextC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin>y4_shr53_boundC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_seqC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX29x2_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_lenC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3:x2_cell_rdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u8arr_sbC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le1C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas;Zupd_lengthc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin>y4_land_m4_shrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z6shiftlI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5msize01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2C45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin8y4f_lastC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litC47Corelib4Init9Datatypes7nat_indK4ELinuxProcessSemantics5Riscv5Instr5msize02c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin8y4f_tailK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin9y4f_t5dc8C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin9y4f_join2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr03C56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin9y4f_loop2c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin7y4f_ph2".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma y4_cells_bytes_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fin ()) [] "h02wsh12IHh21lh31wp;1p;3p;2p;6p;5p;4p10000p4p7210g000\R0p4p710p8g001:j14Tg001_j1?Tg002=j1>Tg002`j1:Tg003@j18Tg004:j15Tg004kj37Tg005Ej1=Tg005ej2<Tg006?j2;Tg006ij21Tg007Oj1@Tg007mj20TP0j6CTg008Mj36Tg008mj5BTg009Oj4ATf1R0g009kg00:`f0R1CAp=9f4f3R2f2R3?60136p=31130=621p=2g00;U#4#4#4R4#4#4#4#?R5#>R6#:R7P6%?4R8#>R9#:R:1961#8%5137R;X07%=9,<:%=6R<,96#8%5<57:eP:%50R<P91;52R2,18R=P9%@4R4,02R2,18R>P91024R2,18R?P91024R2,18R@P91024R2,18RAP91024R2,18RBP91024R2,18RCP91024,18R2P1D3D3D3D3P9P=P9P>P9P?P9P@P9PAP9PBP9PCP9P2%53D3D3D3D357:X2:P9P81;53R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054P<C2C2C2C2C2C2C2C2,<:1960#8P1ECA6630R3,96#8%5357:eX1;X07X36P1DBW0o"). Qed.
Lemma y4_cells_size_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fin ()) [] "h02wsh14__x1h21xh32IHh43IH0h57__arithh64__ffh78__varmaph85__with94cstrh:5cstr0h;1nh<1wh=1yp;1p;2p;3p;4p;7p;6p;5p;Bp;<g001:j1>Tg001_j1eTg002=j1XTg002`j1ETg00<:j1@Tg00=3j28Tg00=Sj2ATg005ej2<Tg005Ej1GTg00=jR0j11Tg00>Ij25Tg007Oj1JTg00>`R1j19Tg00?@R2j2KTg00?]R3j20Tg004kj3=j1ITg00@:j2YTg00@]j3WTg00A:j4STg00Aaj1FTg00BFj2DTg00Bbj2QTg00C@j1PTg00C^j1OTg00DIj2BTg00Dlj2NTg00EOj3RTg00F2j4MTg00F]j7TTg00GAj2dTg00Gcj2cTg00HOj3bTg00Hnj4aTg00I`j4`Tg000\j6_Tg008Mj3^Tg008mj5]Tg009Oj4\Tg00JKlBCTg00K1l<[Tg00KVl<ZTg00L;j3LTf1R4g009kg00:`f0R5C\p=?%15#1p=6g00L^R6?=45p=;1545#1p=7P6P6P6g00M=R7P7P7g00M[P1P1P1P2g00N;f5R2f4R8f3R9f2R:P4P5MBCp=VP6P6P7P7P0P1P1P9g00N^P:P4P5M<[p=2P6P6P6P7P7P7g00OBR0P1P1P1P3g00ObR;P9P:P4g00PER<g00PdR=P5MBCp=UP6P6P6P7P7P7P0P1P1P1P3P;P2P8P9P:P4P5MBCp=:P6P7P5P1P4P:P9P8P2f6f7f8M<Zp=HAL7:4=L75p=310:4/05p=4g00;UR8#>#>#>R1#>#>#>#e#XR;#ER3P;1?;5#@%6<#6#6#6R018;5'A';R>X031<6<%G;R?,?;#@18;?,A0';eP618;4R?,A0R@%65#6#6#618;:RA17A<,7A,7A,7A,7A,7A,7A'7';X;6%1@RA#1RB#1RC#1RD#1RE#1RF#1RG#1RH15?<R<#1RI,5?RJ#1RK,5?RL#1RM,5?RN#1RO,5?RP#1RQ,5?RR#1RS,5?RT#1RU,5?RV#1RW';%J1R1%9?RX'KRY%J8RZ'0R[/0ZR\/0ZR]/0ZR^/0ZR_/0ZR`/0ZRa/0ZRb10X=Rc/0ZRd,0XRe/0ZRf,0XRg/0ZRh,0XRi/0ZRj,0XRk/0ZRl,0XRm/0ZRn,0XRo/0ZRp,0XRq/0ZRr5=7%I6Rs%I7Rt%94%955=71;451Y453WX=6X26R6PHPb105ZX27RbPGPaPbPFP`PbPEP_PbPDP^PbPCP]PbPBP\PbPAP[PbP@PYP0P11<71P?PX1<7XR[EVRAC2C2C2C2C2C2C2C2PWPrPbPVPqP?PXP[PUPpPbPTPoP?PXP[PSPnPbPRPmP?PXP[PQPlPbPPPkP?PXP[POPjPbPNPiP?PXP[PMPhPbPLPgP?PXP[PKPfPbPJPeP?PXP[PIPdPbP<PcP?PXP[1<7=CUC2E:C2E:C2E:C2E:C2E:C2E:C2E:C2M9H1?;4#@R[/;@%9[RX==7YR?PsPtP6P[PX1<7XP@PYPAM9HP5CSP?1?;:#@R?#F%9?,D=18;9R9#F%99,D=g00QBR9#G%E91Q74%P7%O7R9g00Qng00RMR?P?g00RmR?P71B711N78R85R71B7ZRA;3A?3AA?3AA?3AAg00SM1B7==38A=38A=38A=38A=38A=38A=38A=38ACMg00T4FT1d9?P5P:g00TTR?g00U4R9'<1c5:==?9dAb7=4Cab6b7b8X171K15?4ZZ?4ZZ?4ZZ?4ZZA45=Z=45Z=45Z=45Z=45Z=45Z=45Z=45Z5=7^17P518;2#9O1b5b:b9b4C`P[P5E_A^;:4R:,?;#@18;:,A0';eX3>X03X<;P5D]W0o"). Qed.
Lemma y4_cells_wf_C8 : forall ws, cells_wf (map C8 ws).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fin ()) [] "h02wsh12IHh21wp;1p;4p;3p;5g001:j10Tg001_j1:Tg002=j14Tg002`j13Tg00UTj11Tg005Ej19Tg00VKj45Tg008Mj36Tg008mj57Tg009Oj48Tf1R0g009kg00:`f0R1C8p=2g00;U#0#0#0#0#0#0#:#4R2#3R3P21221#1R4X03g00VfR5%92,22#1eg00WB1220#1P5P1C5f2=620,22#1eX14X03X22P1D7W0o"). Qed.
Lemma y4_u64arr_of_C8 : forall segs m A ws, rw_cells segs m A (map C8 ws) -> u64arr segs m A ws.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fin ()) [] "h02Hwh11Hh22Hbh31Ah42_Hh51lh61mh71nh84segsh92wsh:1zp;1p;4p;6p;2g002`j18Tg001:j14Tg001_j1@Tg002=j1<Tg00W^j1JTg00X@j4HTg00Y6j4>Tg00<:j16Tg00>`j12Tg00Ymj41Tg00Z_j4;Tg00UTj1:Tg003@j19Tg00[Rj45Tg004:j1BTg00\Gj1ITg00]Pj67Tg00=jj13Tg00=3j2?Tg00=Sj2=Tg00]lj1GTg007Oj1ETg00?@j2ATg00N;j2DTg00VKj4CTg009Oj4FTf1R0g009kg00:`f0R1CFp=0g00_4#8g00;U#4#4#4R2#4#4#4#@#<R3%@2#<R4#J[g00M=R5%83f3R6f2R7P01031CHg00`3R8f4R9P6P71030R:C>P9P6P7%6:#2C1f5R:P9P6P7C;P1f6R7P:P91036C>P81039R9#:f7R8P7P:%99C5f8R9P8P7103:#6#2C1f9R:P9P8P7C;[P11037#:f:R7P:P91038#9C5f;R8P7P:1039#6#2C1%84R4103:#9f=R9f<R6P8P1C5X54P0%B:R4%I:E7P6P8P7P4C5g00L^R41037#6f>R:P9P6%21C1X74P0g00PE#3#3#3#3#3#3#3#3R41?37'=R;%G7E7P9P6P8%2;C1P:P9P6%B8C5P:P9P6%E21?38R8#2R3'AC1P0P51=48#2f?P:P9P1C1X:5P1%24/A3R31D48E7P:P9P6P3C1P1b0CCb0b2W0W2W4P0P1O2n2001000000121000000W1P0P1O2n2001000000121000000W1W9W3W6W8o"). Qed.
Lemma y4_C8_of_u64arr : forall segs m A ws, u64arr segs m A ws -> rw_cells segs m A (map C8 ws).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fin ()) [] "h01Ah11Hh22Hbh32Hwh41lh51mh61nh74segsh82wsh91zp;1p;4p;2p;6g002`j19Tg001:j12Tg001_j1;Tg002=j1:Tg00W^j1JTg00Z_j4ETg004:j16Tg00[Rj44Tg007Oj1>Tg00=3j27Tg00>`j11Tg00?@j25Tg00Ymj43Tg009Oj4=Tg00X@j4ITg00Y6j4HTg00<:j1DTg00UTj1CTg003@j1BTg00`Nj1@Tg00\Gj1ATg000\j68Tg00VKj4<Tg00=jj10Tg00=Sj2?Tg00N;j2FTg00]lj1GTg00_4#9g00;U#2#2#2R0#2#2#2#;#:R1%;0#:R2#J[g00M=R3%91f3R4f2R5f1R6f0R7CEg00`3f4R8P4P5%66C4P8P4P5%>0R01716#1'5C3f5R9P8P4P1g009kR:g00:`R;P5C=CIP7f6R5P9P8%64C4f7R4P5P91718#1,50C3f8R0P4P5P1P:P;P9C=R;CHP0P4P5%D;R:#1C3%C;P0P4P5%B;R;C4%@9%92R2%69f9R5P0P4P7C4X42P6P;%A9E8C<g00L^R;g00PE#0#0#0#0#0#0#0#0R21719R1'?R8P5P0P4%17C3X6;P3%12%11'5P5P0P4P7C3X93P7%181F21E8P:%G9E8C<W3W2P6P7O2n2001000000121000000W1W8W0W5W7o"). Qed.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma y4_land_m4_shr : forall X, 0 <= X < 2^64 -> Z.land (X ≫ 51) 18446744073709551612 = 4 * (X ≫ 53).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fin ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh64__p1h71nh81Bh91Hh:1ah;1mh<2HXh=1Xh>1Yh?1yp;1p;2p;6p;3p;4p;5p;8p;7g001:j15Tg007Oj18Tg00aTj2JTg00b1j27Tg00`3R0j2=Tg00bMj10Tg007mj22Tg00c2j2PTg005Ej1NTg002`j1MTg00Bbj2mTg00C@j1jTg00C^j1fTg00DIj2>Tg00Dlj2]Tg00cYj6YTg00d=j1XTg00GAj2WTg005ej2CTg00Gcj2UTg00HOj3TTg00Hnj4STg00d_j21Tg00e<j1OTg001_j1LTg00eZj3KTg00EOj3QTg00?@j2;j1`Tg00f=j5RTg00fij3BTg000\j6?Tg00VKj4lTg00gRj2ITg00h0j2ETg00hMj1iTg00hmj3eTg00L;j3cTg00?]j2bTg00ijj6_Tg00jjj2^Tg00F2j4GTg00kJj6aTg004kj3FTg00knj5\Tg00lOj8dTg00BFj2[Tg00F]j7ZTg00llj7gTg00mPj8hTg00PdR1f0R2'[p=4%52#5p=:%02#0p=Vg00M=R3f1R4g00n4P2CGp=HP4g00QnR5g00RMR6P6g00RmR7P2g00T4FZp=3f2R8P5P6P6P7P4P2Fgp=Af3R9P5P6P6P7P8P4P2Ghp=Dg00TTR:g00U4R;7F2p=@P3P4g00n[P2CGp=<%02#0#0#0p=k%02#0#0#0#0#0#0#0p=9AF342p=6%42R<g00;UR=#5R>#8R?%5>R>#:#:R@#8'JRA,72RB'=%0=RC#5RD#5#VRE#8RF,24RG#4RH%5@#:#:#:#8RI,7GRJP01242#4%48RK[%44RL1284#4[RM1298#4\K1P42P2n2001000000120000000X73X:3PM^73^:3P2P8PFp-0RMg00QBRN#NRO%MNRN1m34RP%j3RQ%f3RR1>31RS1]3=R='H,3RRTPRP5P6P6P7P9EYRU5AR%X6RVPTCD1WR7RWP2P81C:;R;1U28#@dAT314CSR:b1b2b3X43W61=<4PL[^43^6MP2179AP9P8O3b0O3b9P31J?FRA,14172IRXX53P4PAPIPOPN%O3RYPQ1>3?RZ%LE5K3RE,<S,3RPWP:b1b2b3171AP2b0POPNPPPQPR%L@9K3Z,<=,3R9ARUPV1>3IRU9Q3E,<=,3RCDPWP:b1b2b3X43X6M1=4B1;AI,74[^43^6MP2PKP8P4O3b0DRPGPOPNPYPQ1>3F,HS,3RPWP:b1b2b3%4FP2b0RG9B4FE?Cl1=HJ%kC#9#9#9#9#9#9#9#:#8RC,I2%8>R>112>RJ';'EX?3RHP1PIP;%iI9eH1#@d128FR;POPNPPPQPR1<=U,3R9ARTPVAc3SU,<=,3R9ARTCDPWP:b1b2b3X431=<X1b1I,74,=L[^43P2129FP4O2b0E_PHP;O1#@P01E42#@1684[R016421E84#@R;[1698\;1^42P4n2001000000120000000X;3X73P0^;3^73P2f4/2FR0/ICR;110>,;>R0P4O316;0P3f5R0/2FR;/1>R4,;>f6R9%0D#5#0#8RD'2R8,;>,62X53P3P3%`>RHPHP4120DR4P3\3/CHP3110ARH16J8X53P31J?DR?,10R8119A/1>/62X53P31;A>,10119?,62X531C3811H>P0PAP>POPNPYPQPRP5P6P6P7P3PEg00SMPSCG,3REaPWP:b1b2b3AF3A1g00oB[P2b0POPNPYPQ1>3>,<S,3RPWP:b1b2b3171>P2b0D\E?P4POPNPYPQ1>3D,HS,3RPWP:b1b2b3%4DP2b09B0DE?P;AB0FGE?Gd1I;CP2E?b8b9b8b>W<X=3o"). Qed.

Lemma y4_shr53_bound : forall X, 0 <= X < 2^64 -> 0 <= X ≫ 53 < 2048.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fin ()) [] "h07__arithh14__ffh24__p1h38__varmaph45__with54__x1h61ah71nh81Hh92HXh:1Xh;1zp;1p;2p;4p;6p;3p;5p;7p;8g001:j11Tg007Oj14Tg00aTj2@Tg00b1j22Tg00`3R0j28Tg00bMj19Tg007mj25Tg00c2j2DTg005Ej1CTg002`j1BTg00Bbj2ATg00C@j1[Tg00C^j1VTg00DIj27Tg00Dlj2UTg00F2j4;Tg00cYj6NTg00d=j1MTg00GAj2GTg005ej2FTg00Gcj2ETg004kj3HTg00HOj3ITg00Hnj4JTg00d_j2KTg00e<j1LTg001_j1<Tg00eZj3=Tg00EOj3OTg00?@j2PTg00f=j5QTg00fij3RTg000\j6STg00VKj4TTg00BFj2ZTg00F]j7YTg00llj7XTg00mPj8WTg00PdR1f0R2'Zp=0%12#1p=6f1R3g00QnR4g00RMR5P5g00RmR6P2g00T4FYp=3f2R7P4P5P5P6P3P2FXp=?f3R8P4P5P5P6P7P3P2GWp=>g00M=R9P3g00n[P2C;p=:%02R:g00;UR;#1R<#4R=%1<#6#6R<#4'@R>,22R?'8%9;#1#9#1#9R@#4RA,53RB#0%1<#6#6#4RC,2BP01532#0%07R0[%03RD1573#0[RE1587#0\01D32P2n2001000000120000000X79X69PE^79^69P2P7PAp-0REg00QBRF#CRG%BFRF1A93RH%[9RI%V9RJP91791RKg00n4RL1U9;R;C;,3JRMPJP4P5P5P6P8ENR45?J%M5R5PMC>1GJ6R6P2P7g00TTRMg00U4RN'F1E27=HMNdAI913CJRNb1b3b4X59W218:3PD[^59^2EP2128>P8P7O3b0O3b8P91@=AR8,K3122CX;9P3P8PCPGPF%L9R>PI179=R=%<@5=9R@,:K,3JP6PNb1b3b41218P2b0PGPFPHPIPJ%<<9=9=,:;,3J9?J4P5179C9O9@,:;,3JC>P6PNb1b3b4X59X2E183?1P8C,23[^59^2EP2P0P7P3O3b0DQPBPGPFP>PIP9PKPL179AC;,3JP6PNb1b3b4%0AP2b09R3AESCTW9X:9o"). Qed.

(* [comment removed for export] *)
Ltac y4_u64_sok ARR i :=
  lazymatch type of ARR with u64arr ?segs ?mx ?A ?ws =>
    let a := cur_mem_addr in
    pose proof (u64arr_store_ok segs mx A ws i a ARR ltac:(rewrite ?upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK
  end.
Ltac y4_u64_store ARR i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le8 ?v)) _) =>
    lazymatch type of ARR with u64arr ?segs mx ?A ?ws =>
      let E := addr_expr a in
      let ARR' := fresh "ARR" in
      assert (ARR' : u64arr segs (write_to_mem mx (wa E) (le8 v)) A (upd ws (Z.to_nat i) v));
      [ replace (wa E) with (wa (A + 8 * i)) by (unfold wa; f_equal; lia);
        apply (u64arr_write segs mx A ws i v ARR); rewrite ?upd_length; lia
      | clear ARR; store_done; rename ARR' into ARR ]
    end
  end.

Lemma y4_byte_bound : forall src i, Forall (fun c => 0 <= c < 256) src -> 0 <= i < zlen src -> 0 <= Znth i src < 256.
Proof.
  intros src i H Hi. rewrite Forall_forall in H. apply H. unfold Znth. apply nth_In. unfold zlen in Hi.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id; [exact (proj2 Hi) | exact (proj1 Hi)].
Qed.

Lemma y4_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma y4_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma y4_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma y4_srl3 : forall x, 0 <= x < 2^32 -> bv_swrap 32 (bv_wrap 32 x ≫ 3) = x / 8.
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  assert (E1 : 2 ^ Z.of_N 32 = 4294967296) by reflexivity. rewrite !E1.
  assert (E2 : Z.div 4294967296 2 = 2147483648) by reflexivity. rewrite E2.
  rewrite (Z.mod_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= x / 8 < 536870912) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma y4_swrap_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  assert (E1 : 2 ^ Z.of_N 32 = 4294967296) by reflexivity. rewrite !E1.
  assert (E2 : Z.div 4294967296 2 = 2147483648) by reflexivity. rewrite E2.
  change (2 ^ 31) with 2147483648 in H.
  rewrite Z.mod_small by lia. lia.
Qed.
Ltac y4pz U := zify_cond U; rewrite ?byte_lit in U by lia; rewrite ?unsigned_lit in U by lia;
  rewrite ?Z.shiftr_div_pow2 in U by lia; cbn [Z.pow Z.pow_pos Pos.iter] in U;
  rewrite ?Z.mod_small in U by (try split; try apply Z.div_pos; lia).
Ltac y4pbU U := repeat match type of U with
  | context [Z.ltb ?a ?b] => revert U; destruct (Z.ltb_spec a b); intro U
  | context [Z.eqb ?a ?b] => revert U; destruct (Z.eqb_spec a b); intro U
  | context [Z.leb ?a ?b] => revert U; destruct (Z.leb_spec a b); intro U end;
  cbn [Z.b2z] in U;
  repeat match type of U with context [Z.lxor ?a ?b] =>
    is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in U end.
Ltac y4bnd := rewrite ?byte_lit by lia; rewrite ?Z.shiftr_div_pow2 by lia; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in *; lia.
Ltac y4src :=
  lazymatch goal with SRC : bytes_at usegs ?m ?S (map (Z_to_bv 8) ?src), BY : Forall _ ?src |- _ =>
    let a := cur_mem_addr in
    lazymatch a with Z_to_bv 64 ?e =>
      let RS := fresh "RSRC" in let bx := fresh "bx" in let BX := fresh "BX" in
      pose proof (src_rd usegs m S src (e - S) SRC ltac:(y4bnd)) as RS;
      replace (S + (e - S)) with e in RS by ring;
      pose proof (y4_byte_bound src (e - S) BY ltac:(y4bnd)) as BX;
      set (bx := Znth (e - S) src) in RS, BX; clearbody bx
    end
  end.
Ltac y4clr := repeat match goal with H : ov_read_bytes _ _ _ _ = Some [Z_to_bv 8 ?b] |- _ => is_var b; clear H end.
Ltac y4clrt := repeat match goal with
  | H : ov_read_bytes _ _ _ _ = Some (le2 (Z_to_bv 64 (x2_seq _))) |- _ => clear H
  | H : ov_read_bytes _ _ _ _ = Some [Z_to_bv 8 (x2_nbBits _)] |- _ => clear H
  | H : ov_read_bytes _ _ _ _ = Some [Z_to_bv 8 (x2_len _)] |- _ => clear H
  | H : ov_read_bytes _ _ _ _ = Some [Z_to_bv 8 (x2_seq _)] |- _ => clear H end.
Ltac y4gen := repeat match goal with
  | |- context [Z_to_bv 64 (Z.lor ?x ?y)] =>
      lazymatch x with context [Z.shiftl _ 32] => idtac end;
      let cw := fresh "cw" in set (cw := Z_to_bv 64 (Z.lor x y)) in *; clearbody cw end.
Ltac y4cell :=
  lazymatch goal with |- context [Z.land (?Y ≫ 51) _] =>
    rewrite (y4_land_m4_shr Y) by (first [apply Z.mod_pos_bound; lia | lia]);
    let VR := fresh "VR" in let v := fresh "v" in let EV := fresh "EV" in
    pose proof (y4_shr53_bound Y ltac:(first [apply Z.mod_pos_bound; lia | lia])) as VR;
    remember (Y ≫ 53) as v eqn:EV; clear EV;
    lazymatch goal with TOK : x2_table_ok ?cells 11, ECB : ?cbs = _, CE : bytes_at usegs ?mm (?DT + 4) ?cbs |- _ =>
      let c0 := fresh "cl" in let EC := fresh "EC" in
      remember (nth (Z.to_nat v) cells x2_default) as c0 eqn:EC;
      let SQ := fresh "SQ" in let NB := fresh "NB" in let LN := fresh "LN" in
      destruct (proj2 (proj2 TOK) v ltac:(change (2^11) with 2048; lia)) as (SQ & NB & LN); rewrite <- EC in SQ, NB, LN;
      let RC0 := fresh "RC" in let RC2 := fresh "RC" in let RC3 := fresh "RC" in let RCB := fresh "RC" in
      destruct (x2_cell_rd usegs mm (DT + 4) cells (Z.to_nat (4 * 2^11)) v c0 ltac:(rewrite <- ECB; exact CE)
                  ltac:(lia) ltac:(destruct TOK as (_ & TLN & _); unfold FseNCount.Zlength in TLN; cbn; lia)
                  ltac:(destruct TOK as (_ & TLN & _); unfold FseNCount.Zlength in TLN; lia) EC SQ)
        as (RC0 & RC2 & RC3 & RCB)
    end
  end.
Ltac y4bufgen := lazymatch goal with ARR : u8arr usegs ?m ?D (map (Z_to_bv 8) (Zupd ?i ?x ?b0)), LB : zlen ?b0 = ?L |- _ =>
  let LB' := fresh "LB" in assert (LB' : zlen (Zupd i x b0) = L) by (rewrite Zupd_length; exact LB); clear LB;
  let nb := fresh "buf" in set (nb := Zupd i x b0) in *; clearbody nb end.
Ltac y4dst := lazymatch goal with ARR : u8arr usegs _ ?D _ |- _ =>
  let a := cur_mem_addr in lazymatch a with Z_to_bv 64 ?e =>
    u8_sok ARR (e - D); zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      lazymatch w with Z_to_bv 64 _ => idtac | _ => rewrite <- (Z_to_bv_lit_self w) end end;
    u8_store_same ARR (e - D); y4bufgen end end.
Ltac y4cellre := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with TOK : x2_table_ok ?cells 11, ECB : ?cbs = _, CE : bytes_at usegs m (?DT + 4) ?cbs,
                  EC : ?c0 = nth (Z.to_nat ?v) ?cells x2_default, SQ : 0 <= x2_seq ?c0 < _ |- _ =>
    y4clrt;
    destruct (x2_cell_rd usegs m (DT + 4) cells (Z.to_nat (4 * 2^11)) v c0 ltac:(rewrite <- ECB; exact CE)
                ltac:(lia) ltac:(destruct TOK as (_ & TLN & _); unfold FseNCount.Zlength in TLN; cbn; lia)
                ltac:(destruct TOK as (_ & TLN & _); unfold FseNCount.Zlength in TLN; lia) EC SQ)
      as (? & ? & ? & ?); zstep
  end end.
Ltac y4st := try (rewrite ?y4_srl3 by lia);
  first [zstep | y4src; zstep; y4clr | y4clrt; y4cell; zstep | y4cellre | y4dst]; try y4gen.
Ltac y4show := lazymatch goal with
  | |- evt _ _ (MS ?r _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let o := eval vm_compute in (pc - 88684) in idtac "PROBE-AT" o "REGS" r
  | |- evt _ _ (MS ?r _ ?pc _ _ _ _) => idtac "PROBE-IF" pc "REGS" r
  | |- ?g => idtac "NOTE-OTHER" g end.
Ltac y4tgt pc := lazymatch pc with 93784 => idtac | 93720 => idtac | 93748 => idtac | 93768 => idtac end.
Ltac y4idxb U := repeat match type of U with context [?Y ≫ 53] =>
  let VB := fresh "VB" in let vi := fresh "vi" in
  pose proof (y4_shr53_bound Y ltac:(first [apply Z.mod_pos_bound; lia | lia])) as VB;
  set (vi := Y ≫ 53) in U, VB; clearbody vi end.
Ltac y4br U := try (rewrite ?zb_lxor_ones in U by lia); try (rewrite ?y4_land_m4_shr in U by (first [apply Z.mod_pos_bound; lia | lia]));
  try (y4idxb U); try (y4pz U); rewrite ?y4_land1, ?y4_land3, ?y4_land7 in U;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      tryif y4tgt pc then (exfalso; y4pbU U; lia) else (try (exfalso; y4pbU U; lia))
  | _ => idtac end.
Ltac y4go1 p1 := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p1) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 93548) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif y4tgt pc then fail else y4st
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let U := fresh "U" in if_cases U; y4br U
  | _ => y4st end).
Ltac y4go2 p1 p2 := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p1) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p2) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 93548) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif y4tgt pc then fail else y4st
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let U := fresh "U" in if_cases U; y4br U
  | _ => y4st end).
Ltac y4go3 p1 p2 p3 := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p1) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p2) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p3) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 93548) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif y4tgt pc then fail else y4st
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let U := fresh "U" in if_cases U; y4br U
  | _ => y4st end).

Section CANSEC1. Context {rc : runConstT}.
Section Y4F.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Hypothesis TOK : x2_table_ok cells 11.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 8192.
  Hypothesis D8 : 8 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis SG : 3 * seg < dcap.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis DTA : DT mod 4 = 0.
  Hypothesis CBL : DT + 4 + 8192 <= lo.
  Hypothesis DJ1 : DT + 4 + 8192 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation Y4M := (RF_huf_y4s_iface.Y4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation SPS4 := (RF_huf_y4s_iface.SPS4 DST dcap SS DT src).

  Lemma y4_seg_le : 0 <= seg <= dcap.
  Proof using All. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.

  Lemma y4_epi : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk usegs mm lo (SP + -104) -> rw_cells usegs mm (SP + -104) FRS ->
    mem_inv usegs mm -> munch DW m0 mm -> wmono usegs m0 mm ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x16d70) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros ST FR MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 14 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  Ltac y4rel H L ST hi :=
    eapply stk_release in H; [ | exact ST | rewrite ?y4_cells_size_C8, ?L; cbn [cells_size csize Nat.add Nat.mul]; lia ];
    clear ST; rename H into ST;
    rewrite ?y4_cells_size_C8, ?L in ST; cbn [cells_size csize Nat.add Nat.mul] in ST;
    lazymatch type of ST with stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia end.

  Lemma y4m_stk : forall mm sps ws ops ips bts, Y4M mm sps ws ops ips bts -> stk usegs mm lo (SP + -104).
  Proof using All.
    intros mm sps ws ops ips bts (BUF & SRC & CBR & ST & SPA & SPL & WSA & WSL & (jo & JO) & OPA & OPL & IPA & IPL & BTA & BTL & FR & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    apply y4_C8_of_u64arr in SPA, WSA, OPA, IPA, BTA.
    y4rel SPA SPL ST (SP + -384).
    y4rel WSA WSL ST (SP + -232).
    y4rel JO WSL ST (SP + -200).
    y4rel OPA OPL ST (SP + -168).
    y4rel IPA IPL ST (SP + -136).
    y4rel BTA BTL ST (SP + -104).
    exact ST.
  Qed.

  Lemma y4_err : forall mm sps ws ops ips bts (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    Y4M mm sps ws ops ips bts ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x16d6c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros Y.
    pose proof (y4m_stk _ _ _ _ _ _ Y) as STK.
    destruct Y as (BUF & SRC & CBR & ST & SPA & SPL & WSA & WSL & JO & OPA & OPL & IPA & IPL & BTA & BTL & FR & MI & MU & WM).
    zstep.
    eapply y4_epi; eassumption.
  Qed.

  Notation NDT := (Z.lxor (DT + 4) 18446744073709551615).
  Notation KH pc mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 prev) x9 (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 64)
             (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Section STREAM.
  Variables (k SE OPk : Z) (sps ws ops ips bts : list word).
  Hypothesis K4 : 0 <= k < 4.
  Hypothesis HSE : DST <= OPk <= SE.
  Hypothesis HSE2 : SE <= DST + dcap.
  Hypothesis SPD : nth_error sps 15 = Some (Z_to_bv 64 (DT + 4)).
  Hypothesis WOP : nth_error ws (Z.to_nat (4 + k)) = Some (Z_to_bv 64 OPk).

  Notation STL pc mm p x22 c x1 x7 x17 x18 x19 x20 x21 x23 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22
             x23 (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Hypothesis CONT : forall mm (x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
    Y4M mm sps (upd ws (Z.to_nat (4 + k)) (Z_to_bv 64 SE)) ops ips bts ->
    evt usegs POST (KH 0x16d28 mm k SE x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31).

  Ltac y4mpack :=
    unfold RF_huf_y4s_iface.Y4M;
    lazymatch goal with ARR : u8arr usegs ?m DST (map (Z_to_bv 8) ?bf), LB : zlen ?bf = dcap |- _ =>
      split; [exists bf; split; [exact ARR | exact LB] |] end;
    repeat (split; [first [eassumption | rewrite ?upd_length; eassumption | eexists; eassumption] |]);
    eassumption.

  Lemma y4f_last : forall mm p (bw c x1 x7 x17 x18 x19 x20 x21 x23 x26 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p <= SE ->
    evt usegs POST (STL 0x16cd0 mm p bw c x1 x7 x17 x18 x19 x20 x21 x23 x26 x27).
  Proof using All.
    intros until x27. intros Y HP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof y4_seg_le as SGL.
    pose proof (bv_unsigned_in_range 64 c) as RC. unfold bv_modulus in RC. cbn in RC.
    pose proof (bv_unsigned_in_range 64 bw) as RBW. unfold bv_modulus in RBW. cbn in RBW.
    destruct Y as ((buf & ARR & LB) & SRC & CBR & ST & SPA & SPL & WSA & WSL & (jo & JO) & OPA & OPL & IPA & IPL & BTA & BTL & FR & MI & MU & WM).
    y4go2 0x16d00 0x16d20.
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x16d00) _ _ _ _) => idtac end;
      lazymatch goal with WSA : u64arr usegs ?m (SP + -384) ws |- _ =>
        pose proof (u64arr_read usegs m (SP + -384) ws (4 + k) (Z_to_bv 64 OPk) (wa (SP + -384 + 8 * (4 + k))) WSA WOP
                      ltac:(lia) eq_refl) as RWOP end;
      y4go1 0x16d20).
    all: y4_u64_sok WSA (4 + k); zstep; y4_u64_store WSA (4 + k).
    all: zstep; let UE := fresh "UE" in if_cases UE; try (y4pz UE).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16d6c) _ _ _ _) =>
          eapply y4_err; y4mpack
      | |- _ =>
          lazymatch goal with WSA : u64arr usegs _ _ (upd ws _ ?v) |- _ =>
            replace v with (Z_to_bv 64 SE) in WSA by (f_equal; lia) end;
          eapply CONT; y4mpack
      end.
  Qed.

  Notation ST pc mm p ptr bits c x1 x7 x17 x21 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 SE) (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation L2 pc mm p ptr bits c x1 x7 x17 x21 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 (SE + -2)) (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation TS pc mm p c x1 x7 x17 x18 x19 x20 x21 x22 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22
             (Z_to_bv 64 (SE + -2)) (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac y4open Y := destruct Y as ((buf & ARR & LB) & SRC & CBR & STK & SPA & SPL & WSA & WSL & (jo & JO) & OPA & OPL & IPA & IPL & BTA & BTL & FR & MI & MU & WM);
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof y4_seg_le as SGL.
  Ltac y4spd := lazymatch goal with SPA : u64arr usegs ?m (SP + -512) sps |- _ =>
    pose proof (u64arr_read usegs m (SP + -512) sps 15 (Z_to_bv 64 (DT + 4)) (wa (SP + -512 + 8 * 15)) SPA SPD ltac:(lia) eq_refl) as RSPW end.
  Ltac y4sw := repeat match goal with |- context [bv_swrap 32 ?x] => rewrite (y4_swrap_small x) by lia end.
  Ltac y4nrm := rewrite ?byte_lit by lia; rewrite ?y4_land7; y4sw.
  Ltac y4bnd2 := rewrite ?Z.shiftl_mul_pow2 by lia; try (change (2 ^ 3) with 8); y4sw; lia.

  Lemma y4f_tail : forall (fuel : nat) mm p (c x1 x7 x17 x18 x19 x20 x21 x22 x26 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p -> p + 2 <= SE -> SE - p < Z.of_nat fuel ->
    evt usegs POST (TS 0x16c88 mm p c x1 x7 x17 x18 x19 x20 x21 x22 x26 x27).
  Proof using All.
    induction fuel as [|fuel IH]; intros until x27; intros Y HP HP2 FU; [lia|].
    pose proof (bv_unsigned_in_range 64 c) as RC. unfold bv_modulus in RC. cbn in RC.
    pose proof (bv_unsigned_in_range 64 x22) as RX. unfold bv_modulus in RX. cbn in RX.
    y4open Y. y4spd.
    zstep. y4go2 0x16c88 0x16cd0.
    all: y4nrm.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16c88) _ _ _ _) => eapply IH; [y4mpack | lia | lia | lia]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16cd0) _ _ _ _) => eapply y4f_last; [y4mpack | lia]
      end.
  Qed.

  Lemma y4f_t0 : forall mm p (c x1 x7 x17 x18 x19 x20 x21 x22 x26 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p <= SE ->
    evt usegs POST (TS 0x16c84 mm p c x1 x7 x17 x18 x19 x20 x21 x22 x26 x27).
  Proof using All.
    intros until x27. intros Y HP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    zstep. y4go2 0x16c88 0x16cd0.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16c88) _ _ _ _) => eapply (y4f_tail (S (Z.to_nat (SE - p)))); [exact Y | lia | lia | lia]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16cd0) _ _ _ _) => eapply y4f_last; [exact Y | lia]
      end.
  Qed.

  Lemma y4f_loop2 : forall (fuel : nat) mm p ptr bits (c x1 x7 x17 x21 x26 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p <= SE -> SE - p < Z.of_nat fuel ->
    SS <= ptr -> ptr + 8 <= SS + n -> 0 <= bits <= 64 ->
    evt usegs POST (L2 0x16b80 mm p ptr bits c x1 x7 x17 x21 x26 x27).
  Proof using All.
    induction fuel as [|fuel IH]; intros until x27; intros Y HP FU HP1 HP2 HB; [lia|].
    pose proof (bv_unsigned_in_range 64 c) as RC. unfold bv_modulus in RC. cbn in RC.
    y4open Y. y4spd.
    zstep. y4go2 0x16b80 0x16c84.
    all: y4nrm.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16b80) _ _ _ _) => eapply IH; [y4mpack | lia | lia | lia | lia | y4bnd2]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16c84) _ _ _ _) => eapply y4f_t0; [y4mpack | lia]
      end.
  Qed.

  Lemma y4f_j : forall mm p ptr bits (c x1 x7 x17 x21 x26 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p <= SE -> (bits <= 64 -> SS <= ptr /\ ptr + 8 <= SS + n) -> 0 <= bits < 2^64 ->
    evt usegs POST (ST 0x16b70 mm p ptr bits c x1 x7 x17 x21 x26 x27).
  Proof using All.
    intros until x27. intros Y HP HPT HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (Z.le_gt_cases bits 64) as [HB64 | HB64]; [destruct (HPT HB64) as [HP1 HP2] |].
    all: zstep; y4go2 0x16b80 0x16c84.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16b80) _ _ _ _) => eapply (y4f_loop2 (S (Z.to_nat (SE - p)))); [exact Y | lia | lia | lia | lia | lia]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16c84) _ _ _ _) => eapply y4f_t0; [exact Y | lia]
      end.
  Qed.

  End STREAM.

End Y4F.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
