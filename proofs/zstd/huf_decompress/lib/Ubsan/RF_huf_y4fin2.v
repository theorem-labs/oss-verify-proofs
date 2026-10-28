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
  RF_huf_y4s_iface RF_huf_y4s33_kit RF_huf_y4fin.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4fin2 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast3SPSC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast3Y4MC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6moduloK4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K47Corelib4Init5Logic2eq01K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllC56Stdlib6ZArith6BinInt1Z6shiftlI4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin>y4_shr53_boundC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_seqC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX29x2_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_lenC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C47Corelib5Lists7ListDef6firstnK46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le1C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin>y4_land_m4_shrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC47Corelib5Lists7ListDef3nthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr09C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3:x2_cell_rdC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List:length_mapC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u8arr_sbC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas;Zupd_lengthC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5msize02K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4fin7y4f_be0C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fin28y4f_dec5C56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fin29y4f_join5C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z:mul_div_leK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zK47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z4lxorK46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section Y4F2.
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

  Notation NDT := (Z.lxor (DT + 4) 18446744073709551615).
  Section STREAM2.
  Variables (k SE OPk : Z) (sps ws ops ips bts : list word).
  Hypothesis K4 : 0 <= k < 4.
  Hypothesis HSE : DST <= OPk <= SE.
  Hypothesis HSE2 : SE <= DST + dcap.
  Hypothesis SPD : nth_error sps 15 = Some (Z_to_bv 64 (DT + 4)).
  Notation ST pc mm p ptr bits c x1 x7 x17 x21 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 SE) (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation STL pc mm p bits c x1 x7 x17 x18 x19 x20 x21 x23 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 (Z_to_bv 64 bits)
             x23 (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Hypothesis K56 : forall mm p ptr bits (c x1 x7 x17 x21 x26 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p <= SE -> (64 < bits \/ SS <= ptr /\ ptr + 8 <= SS + n) -> 0 <= bits < 2^64 ->
    evt usegs POST (ST 0x16b70 mm p ptr bits c x1 x7 x17 x21 x26 x27).
  Hypothesis K08 : forall mm p bits (c x1 x7 x17 x18 x19 x20 x21 x23 x26 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p <= SE ->
    evt usegs POST (STL 0x16cd0 mm p bits c x1 x7 x17 x18 x19 x20 x21 x23 x26 x27).

  (* [comment removed for export] *)
  Ltac y5pack :=
    unfold RF_huf_y4s_iface.Y4M;
    lazymatch goal with ARR : u8arr usegs ?m DST (map (Z_to_bv 8) ?bf), LB : zlen ?bf = dcap |- _ =>
      split; [exists bf; split; [exact ARR | exact LB] |] end;
    repeat (split; [first [eassumption | rewrite ?upd_length; eassumption | eexists; eassumption] |]);
    eassumption.
  Ltac y5nb := repeat (rewrite k3_nb_val by lia).
  Ltac y5sw := repeat (lazymatch goal with |- context [bv_swrap 32 ?x] => rewrite (k3_swrap32_small x) by lia end).
  Ltac y5bl := repeat match goal with
    | |- context [bv_unsigned (Z_to_bv 8 (x2_len ?c))] => rewrite (byte_lit (x2_len c)) by lia
    | |- context [bv_unsigned (Z_to_bv 8 (x2_nbBits ?c))] => rewrite (byte_lit (x2_nbBits c)) by lia end.
  Ltac y5sp15 := lazymatch goal with SPA : u64arr usegs ?m (?S + -512) ?l, SP15 : nth_error ?l 15 = Some ?w |- _ =>
    let a := cur_mem_addr in lazymatch a with Z_to_bv 64 (S + -392) =>
      let R := fresh "RSPS" in
      pose proof (u64arr_read usegs m (S + -512) l 15 w (wa (S + -512 + 8 * 15)) SPA SP15 ltac:(lia) eq_refl) as R;
      replace (S + -512 + 8 * 15) with (S + -392) in R by lia end end.
  Ltac y5spc := repeat match goal with H : ov_read_bytes _ _ _ 8 = Some (le8 (Z_to_bv 64 (_ + 4))) |- _ => clear H end.
  Ltac y5x2 := match goal with
    | ECx : ?cc = nth (Z.to_nat ?v) ?cl x2_default, SQx : 0 <= x2_seq ?cc < _, TK : x2_table_ok ?cl 11,
      EB : ?cb = _, CE : bytes_at usegs ?mm (?D + 4) ?cb |- _ =>
        destruct (x2_cell_rd usegs mm (D + 4) cl (Z.to_nat (4 * 2^11)) v cc ltac:(rewrite <- EB; exact CE)
                    ltac:(lia) ltac:(destruct TK as (_ & TLN & _); unfold FseNCount.Zlength in TLN; cbn; lia)
                    ltac:(destruct TK as (_ & TLN & _); unfold FseNCount.Zlength in TLN; lia) ECx SQx) as (? & ? & ? & ?);
        zstep; y4clrt end.
  Ltac y5st := first [y4st | unfold sx16 in *; y4dst | y5x2 | y5sp15; zstep; y5spc]; try y5nb; try y5bl.
  Ltac y5br U := try (rewrite ?k3_nb_val in U by lia); try (rewrite ?zb_lxor_ones in U by lia);
    try (rewrite ?y4_land_m4_shr in U by (first [apply Z.mod_pos_bound; lia | lia]));
    try (y4idxb U); try (y4pz U);
    try (repeat (lazymatch type of U with context [bv_swrap 32 ?x] => rewrite (k3_swrap32_small x) in U by lia end));
    try (rewrite ?Z.mod_small in U by lia);
    rewrite ?y4_land1, ?y4_land3, ?y4_land7 in U;
    try (exfalso; y4pbU U; lia).
  Ltac y5go stop := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif stop pc then fail else tryif y4tgt pc then fail else y5st
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let U := fresh "U" in if_cases U; y5br U
    | _ => y5st end).

  (* [comment removed for export] *)
  Ltac y5s512 pc := lazymatch pc with 0x16824 => idtac | 0x16b70 => idtac | 0x16cd0 => idtac | 0x16d6c => idtac end.
  Ltac y5s588 pc := lazymatch pc with 0x16870 => idtac | 0x16824 => idtac | 0x16b70 => idtac | 0x16cd0 => idtac | 0x16d6c => idtac end.
  Ltac y5s692 pc := lazymatch pc with 0x168d8 => idtac | 0x16824 => idtac | 0x16b70 => idtac | 0x16cd0 => idtac | 0x16d6c => idtac end.
  Ltac y5mods := repeat match goal with |- context [?x mod ?M] => rewrite (Z.mod_small x M) by lia end.
  Ltac y5side := rewrite ?y4_land7 in *; try y5nb;
    rewrite ?Z.shiftl_mul_pow2 by lia; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in *;
    try y5mods; try y5sw; try y5mods;
    repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
    cbn [Z.b2z]; try (change (Z.lxor 1 1) with 0); try (change (Z.lxor 0 1) with 1);
    lia.
  Ltac y5exit := first [eapply K56 | eapply K08]; [y5pack | y5side ..].
  Ltac y5init :=
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    assert (SGL : 0 <= seg <= dcap) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  Ltac y5open Y :=
    destruct Y as ((buf & ARR & LB) & SRC & CBR & ST & SPA & SPL & WSA & WSL & (jo & JO) & OPA & OPL & IPA & IPL & BTA & BTL & FR & MI & MU & WM).

  (* [comment removed for export] *)
  Lemma y4f_dec5 : forall mm p ptr bits (c x1 x7 x17 x21 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p -> p + 10 <= SE -> SS <= ptr -> ptr + 8 <= SS + n -> 0 <= bits <= 7 ->
    (forall mm' p' bits' (c' x1' x7' x17' x21' x27' : word), Y4M mm' sps ws ops ips bts -> p < p' <= SE -> 0 <= bits' <= 64 ->
       evt usegs POST (ST 0x16824 mm' p' ptr bits' c' x1' x7' x17' x21' (Z_to_bv 64 (SE + -9)) x27')) ->
    evt usegs POST (ST 0x168d8 mm p ptr bits c x1 x7 x17 x21 (Z_to_bv 64 (SE + -9)) x27).
  Proof using All.
    intros mm p ptr bits c x1 x7 x17 x21 x27 Y HP HP0 HP1 HP2 HB H512.
    y5init. y5open Y.
    y5st. y5go y5s692.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16824) _ _ _ _) => eapply H512; [y5pack | y5side | y5side]
      | |- _ => y5exit
      end.
  Qed.

  (* [comment removed for export] *)
  Lemma y4f_join5 : forall mm p ptr nb bits flag (x1 x7 x17 x21 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p <= SE -> 9 <= SE -> 0 <= nb <= 8 -> SS <= ptr - nb -> ptr + 8 <= SS + n ->
    0 <= bits <= 64 -> (flag = 0 \/ flag = 1 /\ bits <= 7) ->
    (forall mm' p' bits' (c' x1' x7' x17' x21' x27' : word), Y4M mm' sps ws ops ips bts -> p < p' <= SE -> 0 <= bits' <= 64 ->
       evt usegs POST (ST 0x16824 mm' p' (ptr - nb) bits' c' x1' x7' x17' x21' (Z_to_bv 64 (SE + -9)) x27')) ->
    evt usegs POST (ST 0x16870 mm p ptr bits (Z_to_bv 64 nb) x1 x7 x17 x21 (Z_to_bv 64 (SE + -9)) (Z_to_bv 64 flag)).
  Proof using All.
    intros mm p ptr nb bits flag x1 x7 x17 x21 Y HP H9 HN HP1 HP2 HB HF H512.
    y5init. y5open Y.
    y5st. y5go y5s692.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x168d8) _ _ _ _) =>
          eapply y4f_dec5; [y5pack | y5side | y5side | y5side | y5side | y5side |
                            first [exact H512 | intros; eapply H512; eassumption]]
      | |- _ => y5exit
      end.
  Qed.

  (* [comment removed for export] *)
  Lemma y4f_loop5 : forall (fuel : nat) mm p ptr bits (c x1 x7 x17 x21 x27 : word),
    Y4M mm sps ws ops ips bts -> OPk <= p <= SE -> 9 <= SE -> SE - p < Z.of_nat fuel ->
    SS <= ptr -> ptr + 8 <= SS + n -> 0 <= bits <= 64 ->
    evt usegs POST (ST 0x16824 mm p ptr bits c x1 x7 x17 x21 (Z_to_bv 64 (SE + -9)) x27).
  Proof using All.
    induction fuel as [|fuel IH]; intros mm p ptr bits c x1 x7 x17 x21 x27 Y HP H9 HF HP1 HP2 HB; [lia|].
    y5init. y5open Y.
    y5st. y5go y5s588.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16870) _ _ _ _) =>
          eapply y4f_join5; [y5pack | y5side .. |
                             intros mm' p' bits' c' x1' x7' x17' x21' x27' Y' HP' HB'; eapply IH; [exact Y' | y5side ..]]
      | |- _ => y5exit
      end.
  Qed.

  End STREAM2.

End Y4F2.
End CANSEC1.
