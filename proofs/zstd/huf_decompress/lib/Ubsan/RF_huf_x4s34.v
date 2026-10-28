(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_x4s RF_huf_y4s31_kit RF_huf_x4s31_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s34 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions8bv_swrapK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s4SPL3C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le4C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s<x4_idx_boundK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2:x1_cell_rdC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX19x1_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX17x1_byteC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u8arr_sbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le1C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas;Zupd_lengthK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s7x4s_endC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03C47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C47Corelib5Lists7ListDef3nthC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics5Riscv3Sem5alu64C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXK4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K4ELinuxProcessSemantics5Riscv5Instr5msize01I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s348x34_tailC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>neg_desc_shiftK4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s:x4s_end7d4C56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s348x34_tsetK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s348x34_x860C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s348x34_x6f8C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4K47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s348sx32_litc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s348zx32_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma zx32_lit : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4s34 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh62Hxh71xp;2p;1p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j2ATg001Vj10Tg002;j14Tg002Yj2>Tg0036j27Tg003Rj26Tg003mj1<Tg004Kj1LTg004nj2:Tg005Nj22Tg0064j31Tg006Nj2@Tg006hj1BTg007Hj1TTg007hj2STg008Fj1RTg008dj1OTg009Oj2=Tg00:2j2NTg00:Uj43Tg00;@j38Tg00;cj1KTg00<Ej2ITg00<gj2HTg00=Sj3GTg00>2j4FTg00>dj3JTP0j6?Tg00?Gj2ETg00@1j2DTg00@mj1MTg00A^j7CTg00BBj7PTg00Bfj8QTf1R0g00CJR1g00CiR2P2g00DIR3f0R4g00DiFCp=5f2R5P1P2P2P3P0P4FPp=;f3P1P2P2P3P5P0P4GQp=9g00EIR1g00EgR6/A4g00FER7#0R8#4R9%08#0#0#0R8#4'>R:,74'6R;P1P0%08R<#<R=#LR>1:4:,2=12=5R?31X51P1P012=4=1>?X5112=0R?,@>1:0:g00FjR@#BRA%T@R@1S10RB%R1RC%O1RDP11=16g00GV1N17R7C3,5DREP1P7g00H=RF1=19RG%<8581C3,5D5;DR8%K2R2P8C91ID3R3P4P5g00HdRHg00IDRI'@1H45=1HIdAG160CFRIb2b3b4X011A60R6170:'6\;^01P4P5P0O2R5b19J0:E?1E=?PAP@PBPCPDP8P2P1P7PFA81G=C3,5D9;DEC9P3PIb2b3b4X01%4<,>9,70,66\;^01P5b1,D0E?%M?=1>?eW6W7o"). Qed.

(* [comment removed for export] *)
Lemma sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4s34 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh62Hxh71xp;2p;1p;3p;4p;6p;7p;8g001:j2=Tg001Vj10Tg002;j13Tg00Idj17Tg002Yj2DTg0036j2<Tg003Rj2;Tg003mj19Tg004Kj1ITg00JIj2BTg005Nj26Tg0064j35Tg006Nj2CTg006hj1WTg007Hj1VTg007hj2UTg008Fj1TTg008dj1QTg009Oj24Tg00:2j2OTg00:Uj4>Tg00;@j3@Tg00;cj1MTg00K0j1LTg00<Ej2JTg00<gj2KTg00=Sj3HTg00>2j4GTg00KNj2NTg000\j6ATg00?Gj2FTg00@1j2PTg00LRj1ETg00A^j7RTg00BBj7STg00Bfj8XTf0R0#0#0#0#0p=1f1R1g00CJR2g00CiR3P3g00DIR4P0g00DiFRp=2g00EIR5P1g00H=P0C>p=:f2R6P2P3P3P4P1P0FSp=8f3P2P3P3P4P6P1P0GXp=?g00EgR2/=0g00FER7#0R8#3R9%77#7#7#7R:#3'D,<0';R;P5P1%18R8#0R<#9R=#IR>%98R8/B0,6=16=6R?35X55P5P116=0=5>?X5516=1R?,C>1B81g00FjR8#WR@%V8R81U51RA%T5RB%Q5RCP51452g00GVRD1O57R7C>,2CRE1459RF%9:5@5,:7,2C58CR:%M3R3P5%0<#1#1#1#1#1#1RG#LRH,45PDP7C>,2C%3GRG,45,:7,2C58CC?1JC4R4P0P6g00HdRDg00IDRI'C1K06=5DIdAH521CGRIb2b3b4X051=H11<1G';\;^05P0P6P1O2R6b1,N1EA1F=?P@P8PAPBPCP:P3A@5F=,:7,2C98CEC?P4PIb2b3b4X051=21%3<,D9,<1';\;^05P6b1,P1EA%E?=5>?eW6X75o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X4S34.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation XB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation X4F' mm spl b1 b2 b3 b4 := (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b1 b2 b3 b4).

  (* [comment removed for export] *)
  Variables (O4 L4 SEG Q2 v8 v16 v24 v32 v40 v48 v56 v104 v128 : Z) (j0 j96 j120 : list byte) (bd1 bd2 bd3 : list cell).
  Hypothesis HL4 : 6 <= O4 /\ 1 <= L4 /\ O4 + L4 <= n.
  Hypothesis DC0 : 0 < dcap.
  Notation SPL := (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + Q2) v104 DST v128 j0 j96 j120).

  Notation ST4 pc mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x21 x22 x23 x24 x26 t3 t4 t5 t6 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (2^62)) x21 x22 x23 x24 (Z_to_bv 64 (DT + 4))
             x26 (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Hypothesis CONT : forall mm c4 b4 p4 jp4 (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x21 x22 x23 x24 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 bd2 bd3 (BD4 c4 b4 p4 (SS + O4) jp4) ->
    evt usegs POST (ST4 105636 mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x21 x22 x23 x24 x26 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Ltac xpack OUT LB :=
    split; [eexists; split; [exact OUT| rewrite ?Zupd_length; exact LB]|];
    repeat (split; [first [eassumption | eexists; eassumption]|]); first [eassumption | eexists; eassumption].

  (* [comment removed for export] *)
  Ltac x4open H :=
    destruct H as ((buf & OUT & LB) & SRC & CBS & STK & SPC & L0 & BDa & LBa & (jj & JJ) & BDd & LDd & BDc & LDc & BDb & LDb
                   & FR & MI & MU & WM);
    change (zlen buf) with (Z.of_nat (length buf)) in LB;
    pose proof TOK as (TL1 & TLN & TCK); cbv [HUF_TABLELOG_MAX] in TL1; cbv [FseNCount.Zlength] in TLN;
    pose proof (DP ltac:(lia)) as D8; pose proof (length_map (Z_to_bv 8) src) as LMS; unfold SPL3, BD4 in *;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  Ltac x4pack H := ubdnorm H; unfold X4F, SPL3, BD4; upack.

  (* [comment removed for export] *)
  Ltac xgen := repeat match goal with |- context [Z_to_bv 64 ?E] =>
    lazymatch E with context [Znth _ src] =>
      let w := fresh "w" in let EW := fresh "EW" in remember (Z_to_bv 64 E) as w eqn:EW; clear EW end end.
  Ltac xwalkg stops TCK OUT LB SRC := repeat (xwalk1 stops tl DT cells cbs ECB TCK OUT LB SRC; try xgen).

  (* [comment removed for export] *)
  Lemma x34_tail : forall (k : nat) q pa pb c4 b4 p4 jp4 mm (xra t0 t1 t2 x8 x9 a4 a5 a6 a7 x18 x22 x23 x24 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 bd2 bd3 (BD4 c4 b4 p4 (SS + O4) jp4) -> 0 <= q < dcap -> dcap - q <= Z.of_nat k -> pa = DST + q -> pb = DST + q ->
    evt usegs POST (ST4 105560 mm xra t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)) (Z_to_bv 64 (64 - tl))
                       (Z_to_bv 64 2) (Z_to_bv 64 pa) a4 a5 a6 a7 x18 (Z_to_bv 64 pb) x22 x23 x24 x26 t3 t4 t5 t6).
  Proof using All.
    induction k as [|k IH]; intros until t6; intros XF QR KR -> ->; [lia|].
    x4open XF.
    zstep. xwalk [105560; 105636] tl DT cells cbs ECB TCK OUT LB SRC.
    all: first [ solve [eapply (IH (q + 1)); [x4pack BDd | lia | lia | lia | lia]] | solve [eapply CONT; x4pack BDd] ].
  Qed.

  (* [comment removed for export] *)
  Definition PINV (P : Z) : Prop := P = SS + O4 \/ (SS + O4 < P /\ P + 8 <= SS + O4 + L4).

  Lemma x34_land7 : forall x, Z.land x 7 = x mod 8.
  Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac xside := unfold PINV in *;
    rewrite ?x34_land7, ?Z.shiftl_mul_pow2, ?swrap32_eq by lia;
    repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
    try change (Z.lxor (Z.b2z true) 1) with 0; try change (Z.lxor (Z.b2z false) 1) with 1;
    Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Ltac xbn1 :=
    first [ match goal with |- context [zx32 (Z_to_bv 64 ?x)] =>
              lazymatch x with context [zx32] => fail | _ => rewrite (xk_zx32 x) by llia end end
          | match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
              lazymatch x with context [zx32] => fail | _ => rewrite (unsigned_lit x) by llia end end ].
  Ltac xbn BD := repeat xbn1; revert BD; repeat xbn1; intro BD; rewrite ?sx32_small by llia.

  Ltac xslia := repeat match goal with H : context [bv_signed (Z_to_bv 64 ?z)] |- _ => rewrite (signed_lit z) in H by lia end;
    lia.

  (* [comment removed for export] *)
  Notation HEADS4 mm xra b P c4 jp4 pa pc3 t0 t1 t2 x8 x9 x18 x21 x22 x23 x24 x26 t3 t4 t5 t6 :=
    (X4F' mm SPL bd1 bd2 bd3 (BD4 c4 b P (SS + O4) jp4) ->
     evt usegs POST (ST4 104740 mm xra t0 t1 t2 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 pc3) (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615))
                       (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 pa) (Z_to_bv 64 b)
                       x18 x21 x22 x23 x24 x26 t3 t4 t5 t6)) (only parsing).

  (* [comment removed for export] *)
  Lemma x34_body : forall q P b st c4 jp4 mm (xra t2 x8 x9 x18 x22 x23 x24 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 bd2 bd3 (BD4 c4 b P (SS + O4) jp4) ->
    0 <= q -> q <= dcap -> SS + O4 <= P -> P + 8 <= SS + O4 + L4 ->
    (st = 1 /\ 0 <= b <= 7) \/ (st = 0 /\ 0 <= b <= 64) ->
    (forall P' b' c' jp' mm' pa pc3 (xra' t0' t1' t2' x8' x9' x18' x21' x22' x23' x24' x26' t3' t4' t5' t6' : word),
       q + 4 <= dcap -> PINV P' -> 0 <= b' <= 64 -> pa = DST + q + 4 -> pc3 = DST + q + 7 ->
       HEADS4 mm' xra' b' P' c' jp' pa pc3 t0' t1' t2' x8' x9' x18' x21' x22' x23' x24' x26' t3' t4' t5' t6') ->
    evt usegs POST (ST4 104920 mm xra (Z_to_bv 64 st) (Z_to_bv 64 P) t2 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + q + 3))
                       (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1))
                       (Z_to_bv 64 (DST + q)) (Z_to_bv 64 b) x18 (Z_to_bv 64 (DST + q)) x22 x23 x24 x26 t3 t4 t5 t6).
  Proof using All.
    intros until t6; intros XF Q0 Q4 PL PH SB HD.
    assert (BB : 0 <= b <= 64) by lia.
    x4open XF.
    xwalkg [104740; 105532; 105560; 105636] TCK OUT LB SRC.
    all: try xbn BDd.
    all: first [ solve [eapply CONT; x4pack BDd]
               | solve [eapply (x34_tail (Z.to_nat dcap) q); [x4pack BDd | xslia ..]]
               | solve [eapply (x34_tail (Z.to_nat dcap) (q + 4)); [x4pack BDd | xslia ..]]
               | solve [eapply (HD P); [xslia | unfold PINV; lia | xslia | xslia | xslia | x4pack BDd]]
               | solve [exfalso; xslia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x34_loop : forall (k : nat) q P c4 b4 jp4 mm pa pc3 (xra t0 t1 t2 x8 x9 x18 x21 x22 x23 x24 x26 t3 t4 t5 t6 : word),
    0 <= q -> q <= dcap -> dcap - q < 4 * Z.of_nat k -> PINV P -> 0 <= b4 <= 64 ->
    pa = DST + q -> pc3 = DST + q + 3 ->
    HEADS4 mm xra b4 P c4 jp4 pa pc3 t0 t1 t2 x8 x9 x18 x21 x22 x23 x24 x26 t3 t4 t5 t6.
  Proof using All.
    induction k as [|k IH]; intros until t6; intros Q0 Q4 KR PI BR -> -> XF; [lia|].
    x4open XF. unfold PINV in PI.
    zstep. xwalkg [104740; 104920; 105532; 105560; 105636] TCK OUT LB SRC.
    all: first [ solve [eapply CONT; x4pack BDd]
               | solve [eapply (x34_tail (Z.to_nat dcap) q); [x4pack BDd | xslia ..]]
               | solve [eapply x34_body; [x4pack BDd | xslia | xslia | xside | xside | xside
                                         | intros until t6'; intros QQ PI' BB' EA EC XF';
                                           eapply (IH (q + 4)); [lia | lia | lia | exact PI' | lia | lia | lia | exact XF']]] ].
  Qed.

End X4S34.
End CANSEC1.
