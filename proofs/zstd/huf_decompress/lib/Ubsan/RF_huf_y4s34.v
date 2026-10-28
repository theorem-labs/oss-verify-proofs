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
Ltac2 kr_t_RF_huf_y4s34 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions8bv_swrapK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s4SPLYC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s7y4s_endC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s<y4_idx_boundK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_seqC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX29x2_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_lenC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3:x2_cell_rdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u8arr_sbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le1C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas;Zupd_lengthK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwK4ELinuxProcessSemantics5Riscv5Instr5instr03C56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3>neg_desc_mod64C5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC47Corelib5Lists7ListDef3nthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_framec5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s348y34_lastC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5msize02c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s34:y34_l2bodyK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s349y34_loop2C56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_donec5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s348y34_c4c0c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s34;y4_sx32_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma y4_zx32_lit : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s34 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh62Hxh71xp;2p;1p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j2ATg001Vj10Tg002;j14Tg002Yj2>Tg0036j27Tg003Rj26Tg003mj1<Tg004Kj1LTg004nj2:Tg005Nj22Tg0064j31Tg006Nj2@Tg006hj1BTg007Hj1TTg007hj2STg008Fj1RTg008dj1OTg009Oj2=Tg00:2j2NTg00:Uj43Tg00;@j38Tg00;cj1KTg00<Ej2ITg00<gj2HTg00=Sj3GTg00>2j4FTg00>dj3JTP0j6?Tg00?Gj2ETg00@1j2DTg00@mj1MTg00A^j7CTg00BBj7PTg00Bfj8QTf1R0g00CJR1g00CiR2P2g00DIR3f0R4g00DiFCp=5f2R5P1P2P2P3P0P4FPp=;f3P1P2P2P3P5P0P4GQp=9g00EIR1g00EgR6/A4g00FER7#0R8#4R9%08#0#0#0R8#4'>R:,74'6R;P1P0%08R<#<R=#LR>1:4:,2=12=5R?31X51P1P012=4=1>?X5112=0R?,@>1:0:g00FjR@#BRA%T@R@1S10RB%R1RC%O1RDP11=16g00GV1N17R7C3,5DREP1P7g00H=RF1=19RG%<8581C3,5D5;DR8%K2R2P8C91ID3R3P4P5g00HdRHg00IDRI'@1H45=1HIdAG160CFRIb2b3b4X011A60R6170:'6\;^01P4P5P0O2R5b19J0:E?1E=?PAP@PBPCPDP8P2P1P7PFA81G=C3,5D9;DEC9P3PIb2b3b4X01%4<,>9,70,66\;^01P5b1,D0E?%M?=1>?eW6W7o"). Qed.

Lemma y4_sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s34 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh62Hxh71xp;2p;1p;3p;4p;6p;7p;8g001:j2=Tg001Vj10Tg002;j13Tg00Idj17Tg002Yj2DTg0036j2<Tg003Rj2;Tg003mj19Tg004Kj1ITg00JIj2BTg005Nj26Tg0064j35Tg006Nj2CTg006hj1WTg007Hj1VTg007hj2UTg008Fj1TTg008dj1QTg009Oj24Tg00:2j2OTg00:Uj4>Tg00;@j3@Tg00;cj1MTg00K0j1LTg00<Ej2JTg00<gj2KTg00=Sj3HTg00>2j4GTg00KNj2NTg000\j6ATg00?Gj2FTg00@1j2PTg00LRj1ETg00A^j7RTg00BBj7STg00Bfj8XTf0R0#0#0#0#0p=1f1R1g00CJR2g00CiR3P3g00DIR4P0g00DiFRp=2g00EIR5P1g00H=P0C>p=:f2R6P2P3P3P4P1P0FSp=8f3P2P3P3P4P6P1P0GXp=?g00EgR2/=0g00FER7#0R8#3R9%77#7#7#7R:#3'D,<0';R;P5P1%18R8#0R<#9R=#IR>%98R8/B0,6=16=6R?35X55P5P116=0=5>?X5516=1R?,C>1B81g00FjR8#WR@%V8R81U51RA%T5RB%Q5RCP51452g00GVRD1O57R7C>,2CRE1459RF%9:5@5,:7,2C58CR:%M3R3P5%0<#1#1#1#1#1#1RG#LRH,45PDP7C>,2C%3GRG,45,:7,2C58CC?1JC4R4P0P6g00HdRDg00IDRI'C1K06=5DIdAH521CGRIb2b3b4X051=H11<1G';\;^05P0P6P1O2R6b1,N1EA1F=?P@P8PAPBPCP:P3A@5F=,:7,2C98CEC?P4PIb2b3b4X051=21%3<,D9,<1';\;^05P6b1,P1EA%E?=5>?eW6X75o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Y4S34.
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
  Notation L2S pc mm q x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 :=
    (CS pc mm q x1 x5 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (64 - tl)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (18446744073709551615 - (DT + 4))) x21 (Z_to_bv 64 64) x23 x24 x28 x29 x30).
  Notation S4_L2B := 0x1daf4 (only parsing).

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
  Lemma y34_last : forall mm c bc ptr q (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> dcap - 2 < q <= dcap ->
    evt usegs POST (CS S4_LAST mm q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30).
Proof using All.
    intros mm c bc ptr q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 INV Q0.
    opn INV.
    Time srunL [YEND].
    all: k3_nrm.
    all: eapply (YB y4s_end); pack4.
  Qed.

  Lemma y34_l2b : forall (fuel : nat) q c bc ptr mm (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> 0 <= q -> q + 2 <= dcap -> dcap - q < Z.of_nat fuel ->
    evt usegs POST (L2S S4_L2B mm q x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30).
Proof using All.
    induction fuel as [|fuel IH]; intros q c bc ptr mm x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 INV Q0 Q1 FU; [lia|].
    opn INV.
    ss. Time srunL [S4_L2B; S4_LAST].
    all: k3_nrm; nlx; fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2B) _ _ _ _) =>
             eapply IH; [pack4 | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_LAST) _ _ _ _) =>
             eapply (y34_last); [pack4 | lia]
         | |- _ => k3_pg; fail
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma y34_l2body : forall (fuel : nat) q c bc ptr mm (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> 0 <= q -> q + 2 <= dcap -> dcap - q < Z.of_nat fuel ->
    evt usegs POST (L2S S4_L2H mm q x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30).
Proof using All.
    intros fuel q c bc ptr mm x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 INV Q0 Q1 FU.
    opn INV.
    ss. Time srunL [S4_L2B; S4_LAST].
    all: k3_nrm; nlx; fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2B) _ _ _ _) =>
             eapply (y34_l2b fuel); [pack4 | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_LAST) _ _ _ _) =>
             eapply (y34_last); [pack4 | lia]
         | |- _ => k3_pg; fail
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma y34_loop2 : forall q c bc ptr mm (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> 0 <= q <= dcap ->
    evt usegs POST (L2S S4_L2T mm q x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30).
Proof using All.
    intros q c bc ptr mm x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 INV Q0.
    opn INV.
    Time srunL [S4_L2H; S4_LAST].
    all: k3_nrm; nlx; fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2H) _ _ _ _) =>
             eapply (y34_l2body (S (Z.to_nat (dcap - q)))); [pack4 | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_LAST) _ _ _ _) =>
             eapply (y34_last); [pack4 | lia]
         | |- _ => k3_pg; fail
         end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma y34_join2 : forall q c bc ptr mm (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 : word),
    F4 mm c bc ptr -> PTI ptr -> 0 <= q <= dcap -> 0 <= bc <= 64 ->
    (forall q' bc' mm' (y1 y5 y7 y11 y12 y13 y14 y15 y16 y17 y21 y23 y24 y28 y29 y30 : word),
       F4 mm' c bc' ptr -> q < q' <= dcap -> 0 <= bc' <= 64 ->
       evt usegs POST (L2S S4_L2RH mm' q' y1 y5 y7 (Z_to_bv 64 bc') y11 y12 y13 y14 y15 y16 y17 y21 y23 y24 y28 y29 y30)) ->
    evt usegs POST (L2S S4_L2RJ mm q x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30).
Proof using All.
    intros q c bc ptr mm x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 INV PI Q0 B0 KH.
    destruct PI as (pt & -> & PT0 & PTL).
    opn INV.
    Time srunL [S4_L2RH; S4_L2T; S4_L2H; S4_LAST].
    all: k3_nrm; nlx; fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2RH) _ _ _ _) =>
             eapply KH; [pack4 | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2T) _ _ _ _) =>
             eapply (y34_loop2); [pack4 | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_L2H) _ _ _ _) =>
             eapply (y34_l2body (S (Z.to_nat (dcap - q)))); [pack4 | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S4_LAST) _ _ _ _) =>
             eapply (y34_last); [pack4 | lia]
         | |- _ => k3_pg; fail
         end.
  Qed.

End Y4S34.
End CANSEC1.
