(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_y4s RF_huf_y4s_iface RF_huf_y4_kit_reload RF_huf_y4s31_kit RF_huf_y4s33_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4s34c () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s4SPLYC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K47Corelib4Init5Logic2eq01K4ELinuxProcessSemantics5Riscv5Instr5instr0:I47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s<y4_idx_boundK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z3mulI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_seqC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX29x2_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_lenC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le1K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteK4ELinuxProcessSemantics5Riscv5Instr5instr06C56Stdlib6ZArith6BinInt1Z9add_assocK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s34;y4_sx32_litC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC47Corelib5Lists7ListDef3nthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3:x2_cell_rdC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u8arr_sbC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas;Zupd_lengthC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5msize02K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes3nat01K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib;setoid_ring<Ring_polynom3Mon00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5msize03C56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4s34b8y34_c39cC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4s34b8y34_covfc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4s34c8y34_dec5C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC45stdpp9bitvector;definitions7bv_wrapK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4s34c9y34_join5C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr03C56Stdlib6ZArith6BinInt1Z:mul_div_leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section Y4S34C.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation YB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation Y4F' mm spl b4 b3 b2 b1 :=
    (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).

  (* [comment removed for export] *)
  Variables (O4 L4 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 : Z) (j0 jp j3 j2 j1 : list byte).
  Variables (c3 bc3 p3 st3 c2 bc2 p2 st2 c1 bc1 p1 st1 : Z).
  Hypothesis HL4 : 6 <= O4 /\ 1 <= L4 /\ O4 + L4 <= n.
  Hypothesis HD4 : 2 <= dcap.
  Notation desc := (tl + 256 * mtl).
  Notation SPL := (SPLB v8 v16 v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88 v96 v104 v112 (DST + dcap) (DT + 4) j0).
  Notation F4 mm c bc ptr := (Y4F' mm SPL (BD4 c bc ptr (SS + O4) jp) (BD4 c3 bc3 p3 st3 j3) (BD4 c2 bc2 p2 st2 j2)
                                (BD4 c1 bc1 p1 st1 j1)).
  Notation PTI ptr := (exists pt, ptr = SS + O4 + pt /\ 0 <= pt /\ (pt = 0 \/ pt + 8 <= L4)).

  Notation CS pc mm q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -912)) gp tp x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (2^61)) x20 x21 x22 x23 x24 (Z_to_bv 64 desc) (Z_to_bv 64 dcap)
             (Z_to_bv 64 tl) x28 x29 x30 (Z_to_bv 64 (DST + dcap)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation H5 pc mm q x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 :=
    (CS pc mm q x1 x5 x7 x8 (Z_to_bv 64 64) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (DST + dcap + -9)) x21 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (18446744073709551615 - (DT + 4))) x24 x28 x29 x30).

  Hypothesis K2R : forall q c bc ptr mm (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> 0 <= q -> q + 2 <= dcap -> 0 <= bc < 2^31 -> (bc <= 64 -> PTI ptr) ->
    evt usegs POST (CS S4_L2RP mm q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30).
  Hypothesis KLAST : forall mm c bc ptr q (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> dcap - 2 < q <= dcap ->
    evt usegs POST (CS S4_LAST mm q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30).

  (* [comment removed for export] *)
  Ltac frsh OUT LB :=
    lazymatch type of OUT with u8arr _ _ _ (map (Z_to_bv 8) ?l) =>
      let b := fresh "buf" in let E := fresh "EB" in let L := fresh "LBx" in
      remember l as b eqn:E; assert (L : zlen b = dcap) by (subst b; rewrite ?Zupd_length; exact LB); clear E LB; rename L into LB
    end.

  (* [comment removed for export] *)
  Ltac xpk OUT LB :=
    split; [eexists; split; [exact OUT| rewrite ?Zupd_length; exact LB]|];
    repeat (split; [first [reflexivity | eassumption | eexists; eassumption]|]); first [eassumption | eexists; eassumption].

  (* [comment removed for export] *)

  Ltac x2cell4 v :=
    lazymatch goal with |- context [Z_to_bv 64 (((?cc ≪ ?b) mod 18446744073709551616) ≫ ?sh)] =>
      let EV := fresh "EV" in let VR := fresh "VR" in
      remember (((cc ≪ b) mod 18446744073709551616) ≫ sh) as v eqn:EV;
      assert (VR : 0 <= v < 2^tl)
        by (subst v; apply y4_idx_bound; [lia| first [apply bv_unsigned_in_range | apply Z.mod_pos_bound; lia | lia]|
                                           first [reflexivity | apply Z.mod_small; lia | lia]]);
      clear EV end.

  (* [comment removed for export] *)
  Ltac xpack OUT LB :=
    split; [eexists; split; [exact OUT| rewrite ?Zupd_length; exact LB]|];
    repeat (split; [first [eassumption | eexists; eassumption]|]); first [eassumption | eexists; eassumption].

  (* [comment removed for export] *)
  Ltac x2cell :=
    lazymatch goal with |- context [Z_to_bv 64 (((bv_unsigned ?c ≪ ?b) mod 18446744073709551616) ≫ ?sh)] =>
      let v := fresh "v" in let EV := fresh "EV" in let VR := fresh "VR" in
      remember (((bv_unsigned c ≪ b) mod 18446744073709551616) ≫ sh) as v eqn:EV;
      assert (VR : 0 <= v < 2^tl)
        by (subst v; apply y4_idx_bound; [lia| apply bv_unsigned_in_range| first [reflexivity | apply Z.mod_small; lia | lia]]);
      clear EV end.

  Ltac x2rd v c EC :=
    lazymatch goal with CE : bytes_at usegs ?mm (DT + 4) cbs, SQ : 0 <= x2_seq c < 65536 |- _ =>
      let RC0 := fresh "RC" in let RC2 := fresh "RC" in let RC3 := fresh "RC" in let RCB := fresh "RC" in
      destruct (x2_cell_rd usegs mm (DT + 4) cells (Z.to_nat (4 * 2^tl)) v c ltac:(rewrite <- ECB; exact CE)
                  ltac:(lia) ltac:(lia) ltac:(lia) EC SQ) as (RC0 & RC2 & RC3 & RCB) end.

  Ltac x2c v c EC :=
    lazymatch goal with TCK : forall i, 0 <= i < 2^tl -> _, VR : 0 <= v < 2^tl |- _ =>
      remember (nth (Z.to_nat v) cells x2_default) as c eqn:EC;
      let SQ := fresh "SQ" in let NB := fresh "NB" in let LN := fresh "LN" in
      destruct (TCK v VR) as (SQ & NB & LN); rewrite <- EC in SQ, NB, LN end.

  Notation Y34 l := (YB l O4 L4 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 j0 jp j3 j2 j1
                       c3 bc3 p3 st3 c2 bc2 p2 st2 c1 bc1 p1 st1 HL4 HD4) (only parsing).

  Ltac ss := k3_step DST dcap SS src DT cells cbs tl ECB.
  Ltac srunL L := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        let b := eval vm_compute in (existsb (Z.eqb pc) L) in
        lazymatch b with true => fail | false => ss end
    | _ => ss end).
  Ltac opn INV :=
    destruct TOK as (TL & TLN & TCK); unfold FseNCount.Zlength in TLN; unfold HUF_TABLELOG_MAX in TL;
    assert (P12 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia);
    assert (P0 : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia);
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    destruct INV as ((buf & ARR & LB) & SRC & CE & STK & SPLc & SPLs & B4c & B4s & B3c & B3s & B2c & B2s & B1c & B1s
                     & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SAV) & (jl & JL) & FR & MI & MU & WM);
    unfold SPLB in SPLc; unfold BD4 in B4c;
    assert (LBm : Z.of_nat (length (map (Z_to_bv 8) buf)) = dcap) by (rewrite length_map; exact LB).
  Ltac fixq :=
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let r := getreg 18 in
      lazymatch r with Z_to_bv 64 ?E =>
        lazymatch E with
        | DST + ?q => idtac
        | _ => replace E with (DST + (E - DST)) by lia
        end end end.
  Ltac nlx := rewrite ?zb_lxor_ones by lia.
  Ltac pack4 :=
    try (match goal with H : rw_cells _ _ (SP + -776) _ |- _ => ubdnorm H end);
    unfold Y4F, SPLB, BD4;
    lazymatch goal with ARRx : u8arr usegs ?m DST (map (Z_to_bv 8) ?b), LBx : Z.of_nat (length ?b) = dcap |- _ =>
      split; [exists b; split; [exact ARRx | exact LBx]|] end;
    repeat (split; [first [eassumption | reflexivity | do 12 eexists; eassumption | eexists; eassumption]|]); eassumption.
  Ltac pti_tac :=
    lazymatch goal with |- exists pt, ?P = _ /\ _ =>
      exists (P - (SS + O4)); split; [lia | split; [lia | first [left; lia | right; lia]]] end.
  Ltac rcall :=
    k3_at [PHUF_RELOAD]; pose proof (length_map (Z_to_bv 8) src) as LMS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [ eapply (y4_reload_proof) with (S := SS + O4) (n := L4)
                          (sqb := map (Z_to_bv 8) (firstn (Z.to_nat L4) (skipn (Z.to_nat O4) src))) | post_call usegs m ] end;
    [ assumption | first [eassumption | unfold y4_bd; eassumption] | lia | apply k3_bytes_at_sub; [eassumption | lia | lia | lia]
    | rewrite length_map, length_firstn, length_skipn; lia | lia | lia | lia | lia | lia | lia | lia | lia | ];
    unfold y4_bd in *.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma y34_dec5 : forall q c bc ptr mm (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> PTI ptr -> 0 <= q -> q + 10 <= dcap -> 0 <= bc <= 64 ->
    (forall q' bc' mm' (y1 y5 y7 y8 y11 y12 y13 y14 y15 y16 y17 y21 y24 y28 y29 y30 : word),
       F4 mm' c bc' ptr -> q < q' <= dcap -> 0 <= bc' <= 64 ->
       evt usegs POST (H5 S4_L5H mm' q' y1 y5 y7 y8 (Z_to_bv 64 bc') y11 y12 y13 y14 y15 y16 y17 y21 y24 y28 y29 y30)) ->
    evt usegs POST (H5 S4_D5 mm q x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30).
Proof using All.
    intros q c bc ptr mm x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 INV PI Q0 QE B0 KH.
    opn INV.
    Time srunL [S4_L5H; S4_L2RP; S4_LAST].
    all: k3_nrm; nlx; fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L5H) _ _ _ _) =>
             eapply KH; [pack4 | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2RP) _ _ _ _) =>
             eapply K2R; [pack4 | lia | lia | lia | intros; first [exact PI | exfalso; lia | pti_tac]]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_LAST) _ _ _ _) =>
             eapply KLAST; [pack4 | lia]
         | |- _ => k3_pg; fail
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma y34_join5 : forall q c bc ptr mm (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> PTI ptr -> 0 <= q <= dcap -> 0 <= bc <= 64 ->
    (forall q' bc' mm' (y1 y5 y7 y8 y11 y12 y13 y14 y15 y16 y17 y21 y24 y28 y29 y30 : word),
       F4 mm' c bc' ptr -> q < q' <= dcap -> 0 <= bc' <= 64 ->
       evt usegs POST (H5 S4_L5H mm' q' y1 y5 y7 y8 (Z_to_bv 64 bc') y11 y12 y13 y14 y15 y16 y17 y21 y24 y28 y29 y30)) ->
    evt usegs POST (H5 S4_L5J mm q x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30).
Proof using All.
    intros q c bc ptr mm x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 INV PI Q0 B0 KH.
    opn INV.
    Time srunL [S4_D5; S4_L2RP; S4_LAST].
    all: k3_nrm; nlx; fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_D5) _ _ _ _) =>
             eapply y34_dec5; [pack4 | exact PI | lia | lia | lia | exact KH]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2RP) _ _ _ _) =>
             eapply K2R; [pack4 | lia | lia | lia | intros; first [exact PI | exfalso; lia | pti_tac]]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_LAST) _ _ _ _) =>
             eapply KLAST; [pack4 | lia]
         | |- _ => k3_pg; fail
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma y34_loop5 : forall (fuel : nat) q c bc ptr mm (x1 x5 x7 x8 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> PTI ptr -> 0 <= q <= dcap -> 0 <= bc <= 64 -> dcap - q < Z.of_nat fuel ->
    evt usegs POST (H5 S4_L5H mm q x1 x5 x7 x8 (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30).
Proof using All.
    induction fuel as [|fuel IH]; intros q c bc ptr mm x1 x5 x7 x8 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 INV PI Q0 B0 FU; [lia|].
    destruct PI as (pt & -> & PT0 & PTL).
    opn INV.
    ss. Time srunL [PHUF_RELOAD; S4_L5J; S4_L2RP; S4_LAST].
    all: k3_nrm.
    all: try (rcall; ss; srunL [S4_L5J]; k3_nrm).
    all: nlx; fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L5J) _ _ _ _) =>
             eapply y34_join5; [pack4 | pti_tac | lia | lia |
               intros; eapply IH; [eassumption | pti_tac | lia | lia | lia]]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2RP) _ _ _ _) =>
             eapply K2R; [pack4 | lia | lia | lia | intros; pti_tac]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_LAST) _ _ _ _) =>
             eapply KLAST; [pack4 | lia]
         | |- _ => k3_pg; fail
         end.
  Qed.

End Y4S34C.
End CANSEC1.
