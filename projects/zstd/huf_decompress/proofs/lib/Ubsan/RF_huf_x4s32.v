(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_x4s RF_huf_y4s31_kit RF_huf_x4s31_kit RF_huf_y4_kit_reload.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s32 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5Ubsan:RF_huf_x4s4SPL3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_huf_x4s3BD4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_huf_x4s3X4FC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5Ubsan>RF_huf_h_iface<huf_dec_postC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib4Spec=HufPure_HufX1;x1_table_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount7ZlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX1:x1_cell_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6moduloK4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec5v_sllC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec7alu_sllC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib3Lib8PropExec5v_srlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_srlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_huf_x4s<x4_idx_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib6Common;HufWalkKit29x1_bytes'C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Common;HufWalkKit2:x1_cell_rdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX19x1_nbBitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX17x1_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib3MemAzext_extract_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr>u8arr_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C59OSSVerify5KrLib3Lib4Step>store_bytes_1'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8FseRdKit8byte_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkMem8u8arr_sbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem:length_le1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas;Zupd_lengthC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z9add_assocC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C47Corelib5Lists7ListDef3nthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec=HufPure_HufX16deltX100C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX1:x1_defaultC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums8positive03C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib4Spec=HufPure_HufX1@HUF_TABLELOG_MAXC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0=C59OSSVerify5KrLib3Lib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec6w_subwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RF_huf_x4s328x32_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;HufWalkKit2>neg_desc_shiftC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c59OSSVerify5KrLib5Ubsan<RF_huf_x4s328x32_tsetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5msize04C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>negb_false_iffK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C59OSSVerify5KrLib3Lib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorc59OSSVerify5KrLib5Ubsan<RF_huf_x4s328x32_x120C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib8PropExec6v_addwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6w_addwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib6Common:FseWalkKit:swrap32_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RF_huf_x4s327x32_x74C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib3Lib7ZBridge:zr_mod_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge5zr_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib3Lib7ZBridge:zb_shl_shrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit6src_rdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr5instr0<C59OSSVerify5KrLib3Lib8PropExec7v_srliwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7w_srliwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic2or02c59OSSVerify5KrLib5Ubsan<RF_huf_x4s328x32_joinC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC59OSSVerify5KrLib6Common:FseWalkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib6Common:FseWalkKit<wrap32_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RF_huf_x4s327x32_xacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zC59OSSVerify5KrLib3Lib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:mul_div_leC59OSSVerify5KrLib3Lib7ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section X4S32.
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
  Variables (O2 L2 Q2 SEG v8 v16 v24 v32 v40 v48 v56 v80 v104 v128 : Z) (j0 j96 j120 : list byte) (bd1 bd3 bd4 : list cell).
  Variables (y5 y6 y8 : word).
  Hypothesis HL2 : 6 <= O2 /\ 1 <= L2 /\ O2 + L2 <= n.
  Hypothesis HQ2 : 0 < SEG <= Q2 /\ Q2 <= dcap.
  Notation SPL := (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) v80 (DST + Q2) v104 DST v128 j0 j96 j120).

  (* [comment removed for export] *)
  Notation ST pc mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (2^62)) y5 y6 x23 y8 (Z_to_bv 64 (DT + 4)) x26
             (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Hypothesis CONT : forall mm c2 b2 p2 jp2 (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 (BD4 c2 b2 p2 (SS + O2) jp2) bd3 bd4 ->
    evt usegs POST (ST 103732 mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6).

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
  Definition PINV (P : Z) : Prop := P = SS + O2 \/ (SS + O2 < P /\ P + 8 <= SS + O2 + L2).

  (* [comment removed for export] *)
  Lemma x32_tail : forall (k : nat) q pa pb c2 b2 p2 jp2 mm (xra t0 t1 t2 x8 x9 a4 a5 a6 a7 x18 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 (BD4 c2 b2 p2 (SS + O2) jp2) bd3 bd4 -> 0 <= q < Q2 -> Q2 - q <= Z.of_nat k -> pa = DST + q -> pb = DST + q ->
    evt usegs POST (ST 103652 mm xra t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)) (Z_to_bv 64 (64 - tl))
                       (Z_to_bv 64 2) (Z_to_bv 64 pa) a4 a5 a6 a7 x18 (Z_to_bv 64 pb) x26 t3 t4 t5 t6).
  Proof using All.
    induction k as [|k IH]; intros until t6; intros XF QR KR -> ->; [lia|].
    x4open XF.
    zstep. xwalk [103652; 103732] tl DT cells cbs ECB TCK OUT LB SRC.
    all: first [ solve [eapply (IH (q + 1)); [x4pack BDb | lia | lia | lia | lia]] | solve [eapply CONT; x4pack BDb] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x32_rl : forall q pt c2 b2 jp2 mm (xra t0 t1 t2 x8 x9 a0 a3 a4 a5 a6 a7 x18 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 (BD4 c2 b2 (SS + O2 + pt) (SS + O2) jp2) bd3 bd4 -> 0 <= q <= Q2 ->
    8 <= pt -> pt + 8 <= L2 -> 0 <= b2 <= 64 ->
    evt usegs POST (ST 103616 mm xra t0 t1 t2 x8 x9 a0 (Z_to_bv 64 (SS + O2 + pt)) (Z_to_bv 64 (SS + O2 + 8))
                       a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (DST + q)) x26 t3 t4 t5 t6).
  Proof using All.
    intros until t6. intros XF QR P8 PL BR. x4open XF.
    zstep. zstep.
    eapply evt_cut;
    [ eapply y4_reload_proof with (BD := SP + -144) (S := SS + O2) (n := zlen src - O2) (c := c2) (bc := b2)
        (p := SS + O2 + pt) (pad := jp2) (sqb := skipn (Z.to_nat O2) (map (Z_to_bv 8) src));
      first [ assumption | unfold y4_bd; assumption | apply u_bytes_skipn; [rewrite length_map; lia | assumption]
            | rewrite length_skipn, length_map; lia | lia ]
    | post_call usegs mm; lazymatch goal with H : rw_cells _ _ (SP + -144) _ |- _ => unfold y4_bd in H; rename H into BDb end ].
    xwalkg [103652; 103732] TCK OUT LB SRC.
    all: first [ solve [eapply CONT; x4pack BDb] | solve [eapply (x32_tail (Z.to_nat Q2) q); [x4pack BDb | lia ..]] ].
  Qed.


  (* [comment removed for export] *)
  Ltac xside := unfold PINV in *;
    rewrite ?xk_land7, ?Z.shiftl_mul_pow2, ?swrap32_eq by lia;
    repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
    try change (Z.lxor (Z.b2z true) 1) with 0; try change (Z.lxor (Z.b2z false) 1) with 1;
    Z.div_mod_to_equations; lia.
  Ltac xbn1 :=
    first [ match goal with |- context [zx32 (Z_to_bv 64 ?x)] =>
              lazymatch x with context [zx32] => fail | _ => rewrite (xk_zx32 x) by llia end end
          | match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
              lazymatch x with context [zx32] => fail | _ => rewrite (unsigned_lit x) by llia end end ].
  Ltac xbn BD := repeat xbn1; revert BD; repeat xbn1; intro BD; rewrite ?sx32_small by llia.
  Ltac xslia := repeat match goal with H : context [bv_signed (Z_to_bv 64 ?z)] |- _ => rewrite (signed_lit z) in H by lia end;
    lia.

  (* [comment removed for export] *)
  Notation HEADS mm xra b bt P c2 jp2 pa pc t1 t2 x8 x9 x18 x23 x26 t3 t4 t5 t6 :=
    (X4F' mm SPL bd1 (BD4 c2 b P (SS + O2) jp2) bd3 bd4 -> bt = b ->
     evt usegs POST (ST 102820 mm xra (Z_to_bv 64 bt) t1 t2 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + Q2 + -3))
                       (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)) (Z_to_bv 64 pc) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
                       (Z_to_bv 64 (-1)) (Z_to_bv 64 pa) x18 x23 x26 t3 t4 t5 t6)) (only parsing).

  (* [comment removed for export] *)
  Lemma x32_body : forall q P b st c2 jp2 mm (xra x8 x9 x18 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 (BD4 c2 b P (SS + O2) jp2) bd3 bd4 ->
    0 <= q -> q <= Q2 -> SS + O2 <= P -> P + 8 <= SS + O2 + L2 ->
    (st = 1 /\ 0 <= b <= 7) \/ (st = 0 /\ 0 <= b <= 64) ->
    (forall P' b' bt' c' jp' mm' pa pc (xra' t1' t2' x8' x9' x18' x23' x26' t3' t4' t5' t6' : word),
       q + 4 <= Q2 -> PINV P' -> 0 <= b' <= 64 -> pa = DST + q + 4 -> pc = DST + q + 7 ->
       HEADS mm' xra' b' bt' P' c' jp' pa pc t1' t2' x8' x9' x18' x23' x26' t3' t4' t5' t6') ->
    evt usegs POST (ST 103000 mm xra (Z_to_bv 64 b) (Z_to_bv 64 st) (Z_to_bv 64 P) x8 x9 (Z_to_bv 64 64)
                       (Z_to_bv 64 (DST + Q2 + -3)) (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)) (Z_to_bv 64 (DST + q + 3))
                       (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + q)) x18
                       (Z_to_bv 64 (DST + q)) x26 t3 t4 t5 t6).
  Proof using All.
    intros until t6; intros XF Q0 Q4 PL PH SB HD.
    assert (BB : 0 <= b <= 64) by lia.
    x4open XF.
    xwalkg [102820; 103616; 103652; 103732] TCK OUT LB SRC.
    all: try xbn BDb.
    all: first [ solve [eapply CONT; x4pack BDb]
               | solve [eapply (x32_tail (Z.to_nat Q2) q); [x4pack BDb | xslia ..]]
               | solve [eapply (x32_tail (Z.to_nat Q2) (q + 4)); [x4pack BDb | xslia ..]]
               | solve [eapply (HD P); cycle 5; [x4pack BDb | reflexivity | xslia | unfold PINV; lia | xslia | xslia | xslia]]
               | solve [eapply (HD P); cycle 5; [xk_bnorm_in BDb tl; x4pack BDb | reflexivity | xslia | unfold PINV; lia | xslia | xslia | xslia]]
               | solve [exfalso; xslia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x32_loop : forall (k : nat) q P c2 b2 bt jp2 mm pa pc (xra t1 t2 x8 x9 x18 x23 x26 t3 t4 t5 t6 : word),
    0 <= q -> q <= Q2 -> Q2 - q < 4 * Z.of_nat k -> PINV P -> 0 <= b2 <= 64 ->
    pa = DST + q -> pc = DST + q + 3 ->
    HEADS mm xra b2 bt P c2 jp2 pa pc t1 t2 x8 x9 x18 x23 x26 t3 t4 t5 t6.
  Proof using All.
    induction k as [|k IH]; intros until t6; intros Q0 Q4 KR PI BR -> -> XF EB; [lia|]. subst bt.
    x4open XF. unfold PINV in PI.
    zstep. xwalkg [103000; 102820; 103616; 103652; 103732] TCK OUT LB SRC.
    all: first [ solve [eapply CONT; x4pack BDb]
               | solve [eapply (x32_tail (Z.to_nat Q2) q); [x4pack BDb | xslia ..]]
               | solve [eapply x32_body; [x4pack BDb | xslia | xslia | xside | xside | xside
                                         | intros P' b' bt' c' jp' mm' pa' pc' xra' t1' t2' x8' x9' x18' x23' x26' t3' t4' t5' t6'
                                             QQ PI' BB' EA EC XF' EB';
                                           eapply (IH (q + 4) P' c' b'); [lia | lia | lia | exact PI' | exact BB'
                                                                        | subst pa'; lia | subst pc'; lia | exact XF' | exact EB']]] ].
  Qed.

  (* [comment removed for export] *)
End X4S32.
End CANSEC1.
