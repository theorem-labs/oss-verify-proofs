(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_dx1 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx14DINVI47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01K4ELinuxProcessSemantics5Riscv5Instr5instr08I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK46Stdlib9micromega7EnvRing5PExpr01C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_DEC_STACKK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_xorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_xorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05c5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx16x1_retC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_wordK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_lxorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultC47Corelib4Init5Peano2ltC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx1<x1_idx_boundK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2:x1_cell_rdC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX19x1_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX17x1_byteC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u8arr_sbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le1C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas;Zupd_lengthK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx16x1_endC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx17x1_tailC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>neg_desc_shiftK4ELinuxProcessSemantics5Riscv5Instr5aluop02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx18x1_tail0K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4Znthc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx1<x1_tailentryC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:swrap32_eqK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK46Stdlib9micromega7EnvRing5PExpr06C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:signed_litK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx17x1_joinC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z:mul_div_leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zK47Corelib4Init5Logic2or01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_dx18x1_loop4".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Lemma x1_zbv_eqm : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. exact H. Qed.

Ltac x1_modg := first [ reflexivity
                      | rewrite ?zb_lxor_ones by lia; rewrite ?neg_desc_shift by lia;
                        first [ reflexivity | f_equal; lia | apply Z.mod_small; lia | rewrite Z.mod_small by lia; lia ] ].

Section CANSEC1. Context {rc : runConstT}.
Section DX1.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).     (* [comment removed for export] *)
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.                  (* [comment removed for export] *)
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.                 (* [comment removed for export] *)
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis DPOS : 0 < dcap -> 0 < DST.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).

  (* [comment removed for export] *)
  Definition DINV (mm : fmem) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ stk usegs mm lo (SP + -48)
    /\ rw_cells usegs mm (SP + -48) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0]
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  (* [comment removed for export] *)
  Lemma x1_idx_bound : forall c b, 0 <= c < 2^64 -> 0 <= (c ≪ (b mod 64) mod 18446744073709551616) ≫ ((64 - tl) mod 64) < 2^tl.
Proof using All.
ltac2:(KReplay.run1 (kr_t_RF_huf_dx1 ()) ["CANSEC1"; "DX1"] "h07__sat18h17__sat20h27__sat22h37__sat24h41ah51Hh62Hah74__x1h82H0h97__arithh:4__ffh;7__sat17h<7__sat19h=7__sat21h>7__sat23h?7__sat25h@8__varmaphA5__withB4cstrhC5cstr0hD1bhE4__p1hF1zhG1nhH2HchI2TLhJ2_HhK1chL1ihM1xp%0p;1p;2p;4p;3p;6p;5p;7p;8g001:j11Tg008Ej16Tg00\fj2:Tg00COj22Tg007PR0j23Tg00okj28Tg01n<j2]Tg01o7j1ZTg01oWj4XTg0203j2UTg00[^j24Tg0215j2@Tg00<=j2CTg021Uj2<Tg0225j2gTg022\j3dTg006Pj2PTg00ZHj1QTg0070j1KTg001_j1JTg002=j1^Tg009@j2\Tg00Zmj2[Tg00\>j2>j4MTg00]Cj3?Tg00GIj1ITg00]gj2YTg00Foj2HTg00;=j1WTg004<j1VTg00mDj1TTg00^fj1STg00_Dj1RTg00gCj2;Tg00`Rj2tTg00a4j2sTg00HZj3FTg00a`j3rTg00b?j4qTg023Cj2pTg00^Hj2oTg023`j6nTg00_oj2kTg00?2j1hTg00n@j3fTg008cj2LTg01F6j3eTg01FYj4DTg01Ghj6NTg024Dj2cTg024aj5iTg025Dj5bTg0260j3jTg000\j6OTg011?j4aTg026Yj3lTg01GDj7mTg00ncj7`Tg00oGj8_Tg01K\R1f0R2'8p=0%12#1p=G%12#1#1#1#1#1#1#1p=71212p=9g01ITR3f1R4g01mUP2CDp=BP4g01RFR5g01ReR6P6g01SER7P2g01SeFmp=5P3P4g01TEP2CDp==f2R8P5P6P6P7P4P2F`p=Af3R9P5P6P6P7P8P4P2G_p=E%04R:g01TlR;#1R<#6R=%G<R<#1R>#1R?#1R@#6RA':RB,24'3p,3TOK%6;RCp,2tlRD'8REg027<,8D'3RF1:=DRGg028DRHp,5cellsRI']'8%02122GRJ'3PH%Z4PIg029DCX,UD[^L3'3RI'3P0PFPIf4149A'@%G@#7#7#7#7#7#7#7#6RH'41CADRK/4AS00'<RL#012LG'3P2P3PKf8RLf7RM/4A'@/4HRN/<2RO#012OG'3XF3f6RO/4A,@M/4HRM/<KRP#012PGP01<42#0%08RQ[1<84#0\:RR1<98#0\Q1g42P2n2001000000120000000XG3X43PR^G3^43P2PNPK%92RRP01484RQ#0S0112Q4S021498S03#0Ad842S04P4n2001000000120000000UXD3X43Q01\R^D3^43P2f9RQ14LA'@RLPHp,3src,P3RS#QRT%KS#0RS%J<#^p,3cbs'PR<#QRU%K<#0R<%J@p,2sp'\R@%6>R>'[RV%0@%0>14@>#0[[R>%6?R?,>=R@%9=RW%0?1:=?RX#9[RY[RZ%0=R[g01WaR\A?=?4UW6R?%0X\\^6[R]1>=AR^%0AS05%9B[R_\WR`A?=A4V\X6[Ra%0B\\^6[Rb%I;#1Rc#I#1#6Rd,>=Re%0d1:=dRf#9[Rg\WRhA?=d4V\X6[Rd%0f\\^6[Rf1>=DRi%0DS06%9G[Rj\WRkA?=D4V\X6[Rl%0G\\^6[R[p,2DCR\p,4dcapRm#0Rn12mXRm'3RXP0PnPm%9HRoP2POg01X=1Y1='HPWeROO1RpPjPQPOO1RQPgf<POO1RqP_f?POO1ROPYg01XcRr#WRs%VrRr%T3S07%S3Rt%R3Ru1;31Rv1;3H'B'51tu7RwP2P8g01MARxg01OYRy'H1s28=FxydAr314CqR1b:b@bAPoP2b9b3b2b1b0X8mX5nP4P2O2n2001000000121000000b4b;b0b<b1b=b2b>b3b?bCbBO3b5O3b5P31:=KRo,pMPJXF3PMPoPGP=PKPTPSPUP<PVP>P@PZP?P]P^P`PaPbPePhPdPfPiPkPlP[P\PXP0PnPmPWP2PpPjPQPgPqP_POPYPsPrQ07Pt1;3=,Bv,5uPwP1b:b@bAPWP2b9b3b2b1b0X8mX5nP4P2O2n2001000000121000000b4b;b0b<b1b=b2b>b3b?bCbBS08PTPSPUP<PVP>P@PZP?P]P^P`PaPbPePhPdPfPiPkPlP[P\PXP0PnPm%0KS09P2PpPjPQPgPqP_POPYp-0RWPsPr1o34RJPtPuPuP5P6P6P7P9EnR91k3;R;%1c#6Rc,;3'=,5uR75Au%h6R61;3AR5=f3;Ry,=v,5uRxCEPwP1b:b@bAX73WE182cRz,341CA4R{#0R|[^73^EWP2PEPDfFREO3b9b3b2b1b0X8mX5nP4P2O2n2001000000121000000b4b;b0b<b1b=b2b>b3b?bCbBR}CMP31LKDR~,:=12N2XF3PTPSPUP<PVP>P@PZP?P]P^P`PaPbPePhPdPfPiPkPlP[P\PXP0PnPmAF3A~RNP2PpPjPQPgPqP_POPYPsPrPJPtP3P5g01Q_Ae3y;CD,5uPwP1b:b@bAX731CA2/L29F3A^73P2PDO1b9b3b2b1b0X8mX5nP4P2O2n2001000000121000000b4b;b0b<b1b=b2b>b3b?bCbBPNP3PA14LH1:=2'2XF3P0Q01Q02Q03/28Q04P2n2001000000120000000VRXD3X43Q02\R^D3^43P2PLPBP=PAQ08PTPSPUP<PVP>P@PZP?P]P^P`PaPbPePhPdPfPiPkPlP[P\PXP0PnPmQ05P2PpPjPQPgPqP_POPYPsPrQ07Pt1=v5,5uPwP1b:b@bAQ05P2b9b3b2b1b0X8mX5nP4P2O2n2001000000121000000b4b;b0b<b1b=b2b>b3b?bCbBCMO3b5P~P2ENb51coGP=PKPDP}PTPSPUP<PVP>P@PZP?P]P^P`PaPbPePhPdPfPiPkPlP[P\PXP0PnPmQ06P2PpPjPQPgPqP_POPYPsPrPJPtPu1;3C/=;,5uR==Au9P61=v;,5uCEPwP1b:b@bAX73XEW18C2RC/34P:[^73^EWP218DcPDPEO3b9b3b2b1b0X8mX5nP4P2O2n2001000000121000000b4b;b0b<b1b=b2b>b3b?bCbBDiENDbPPAjMK}EOCaQ00PTPSPUP<PVP>P@PZP?P]P^P`PaPbPePhPdPfPiPkPlP[P\PXP0PnPmQ0912KA'3P2PpPjPQPgPqP_POPYPsPrPJPtPuAAu=7P61By5,5u9AuxCEPwP1b:b@bAX7313Cz12{A,3|[^73P2PDPEO2b9b3b2b1b0X8mX5nP4P2O2n2001000000121000000b4b;b0b<b1b=b2b>b3b?bCbB9lKAEOXJIXIFP4P2O2n2001000010121000000bMWHXD3XK3o"). Qed.

  Definition DINVU (mm : fmem) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ stk usegs mm lo (SP + -136)
    /\ rw_cells usegs mm (SP + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  Definition BDC (mm : fmem) (cw bw : word) (pad : list byte) (pw : word) : Prop :=
    rw_cells usegs mm (SP + -136) [C8 cw; C4 bw; CB 4 pad; C8 pw; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 (SS + 8))].

  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * mtl)) x21 x22 x23 x24 x25 x26 s11
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma x1_err : forall mm cs (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINVU mm -> rw_cells usegs mm (SP + -136) cs -> cells_size cs = 40%nat ->
    evt usegs POST (ST 0x159f4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof using All.
    intros mm cs x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI BD SZ.
    destruct DI as (OUT & SRCB & CBB & STK & FR & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (stk_of_rw_cells usegs mm _ _ BD) as HB. rewrite SZ in HB. change (Z.of_nat 40) with 40 in HB.
    replace (SP + -136 + 40) with (SP + -96) in HB by lia.
    assert (STK2 : stk usegs mm lo (SP + -96)) by (eapply stk_merge; [exact STK | exact HB | lia]).
    clear STK HB BD. rename STK2 into STK.
    do 14 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold huf_dec_post.
    do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact STK.
  Qed.

  Lemma x1_end : forall mm cw bw pad pw (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINVU mm -> BDC mm cw bw pad pw ->
    evt usegs POST (ST 0x159d4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof using All.
    intros mm cw bw pad pw x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI BD.
    unfold BDC in BD.
    do 5 zstep. zstep. if_cases K.
    all: zto 0x159f4.
    all: eapply x1_err; [exact DI | exact BD | reflexivity].
  Qed.

  Ltac dinvu_close :=
    unfold DINVU; split; [eexists; split; [eassumption | rewrite ?Zupd_length; assumption] |];
    repeat (split; [eassumption|]); eassumption.

  Lemma x1_tail : forall (k : nat) mm j p q cnt nd c62 sh c2 cw bw pad pw
                    (x1 x5 x6 x7 x8 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINVU mm -> BDC mm cw bw pad pw -> 0 <= j < dcap -> dcap - j = Z.of_nat k ->
    p mod 2^64 = (DST + j) mod 2^64 -> q mod 2^64 = (DST + j) mod 2^64 -> cnt mod 2^64 = (dcap - j) mod 2^64 ->
    nd mod 2^64 = (2^64 - 1 - (DT + 4)) mod 2^64 -> c62 mod 2^64 = 2^62 -> sh mod 2^64 = 64 - tl -> c2 mod 2^64 = 2 ->
    evt usegs POST (ST 0x1597c mm x1 x5 x6 x7 x8 (Z_to_bv 64 p) (Z_to_bv 64 nd) (Z_to_bv 64 cnt) (Z_to_bv 64 c62)
                      (Z_to_bv 64 sh) (Z_to_bv 64 c2) (Z_to_bv 64 q) x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof using All.
    pose proof TOK as (TL & TLEN & TCK). unfold HUF_TABLELOG_MAX in TL.
    assert (CL : 2^tl <= Z.of_nat (length cells)) by exact TLEN.
    assert (PT : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    induction k as [|k IH]; intros mm j p q cnt nd c62 sh c2 cw bw pad pw x1 x5 x6 x7 x8 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      DI BD J K EP EQ EC END E62 ESH E2.
    { exfalso; lia. }
    rewrite (x1_zbv_eqm p (DST + j)) by exact EP. rewrite (x1_zbv_eqm q (DST + j)) by exact EQ.
    rewrite (x1_zbv_eqm cnt (dcap - j)) by exact EC. rewrite (x1_zbv_eqm nd (2^64 - 1 - (DT + 4))) by exact END.
    rewrite (x1_zbv_eqm c62 (2^62)) by (rewrite E62; reflexivity).
    rewrite (x1_zbv_eqm sh (64 - tl)) by (rewrite ESH; symmetry; apply Z.mod_small; lia).
    rewrite (x1_zbv_eqm c2 2) by (rewrite E2; reflexivity).
    clear p q cnt nd c62 sh c2 EP EQ EC END E62 ESH E2.
    assert (DP : 0 < DST) by (apply DPOS; lia).
    pose proof DI as DI'. destruct DI' as ((buf & ARR & LB) & SRCB & CBB & STK & FR & MI & MU & WM).
    unfold BDC in BD.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ((Z.shiftl (bv_unsigned ?c) ?b) mod ?M) ?sh)] =>
      remember (Z.shiftr ((Z.shiftl (bv_unsigned c) b) mod M) sh) as v eqn:EV;
      assert (VR : 0 <= v < 2^tl) by (subst v; apply x1_idx_bound; apply bv_unsigned_in_range);
      clear EV end.
    zstep. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2. try replace (v * 2) with (2 * v) by ring.
    zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
    zstep. zstep. if_cases U2; zify_cond U2; [exfalso; lia|].
    zstep.
    destruct (x1_cell_rd usegs mm (DT + 4) cells (Z.to_nat (2 * 2^tl)) v ltac:(rewrite <- ECB; exact CBB)
                ltac:(lia) ltac:(lia) ltac:(lia)) as [RC0 RC1].
    destruct (TCK v VR) as (NBc & BYc).
    zstep. zstep. clear RC0 RC1.
    zstep. zstep. zstep.
    zstep. if_cases U3; zify_cond U3; [exfalso; lia|].
    zstep. zstep.
    u8_sok ARR j. zstep. u8_store ARR j (x1_byte (nth (Z.to_nat v) cells x1_default)); [rewrite byte_lit by lia; reflexivity|].
    zstep. zstep. if_cases K2; zify_cond K2.
    - eapply (IH _ (j + 1)); [dinvu_close | unfold BDC; eassumption | lia | lia | x1_modg ..].
    - zstep. zstep.
      eapply x1_end; [dinvu_close | unfold BDC; eassumption].
  Qed.

  Lemma x1_tset : forall mm j p q cw bw pad pw
                    (x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINVU mm -> BDC mm cw bw pad pw -> 0 <= j <= dcap ->
    p mod 2^64 = (DST + j) mod 2^64 -> q mod 2^64 = (DST + j) mod 2^64 ->
    evt usegs POST (ST 0x15958 mm x1 x5 x6 x7 x8 (Z_to_bv 64 p) x10 x11 (Z_to_bv 64 q) x13 x14 x15 x16 x17
                      x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof using All.
    intros mm j p q cw bw pad pw x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      DI BD J EP EQ.
    pose proof TOK as (TL & TLEN & TCK). unfold HUF_TABLELOG_MAX in TL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rewrite (x1_zbv_eqm p (DST + j)) by exact EP. rewrite (x1_zbv_eqm q (DST + j)) by exact EQ.
    clear p q EP EQ.
    zstep. if_cases K; zify_cond K.
    - eapply x1_end; [exact DI | exact BD].
    - do 8 zstep.
      eapply (x1_tail (Z.to_nat (dcap - j)) mm j); [exact DI | exact BD | lia | lia | x1_modg ..].
  Qed.

End DX1.
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
