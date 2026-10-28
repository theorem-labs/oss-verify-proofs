(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_fa_iface RF_huf_y4s RF_huf_y4s_iface RF_huf_y4s0 RF_huf_bitinit RF_huf_y4s01 RF_huf_y4s1 RF_huf_y4s04.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require RF_huf_x2t_fr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4s04m () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List7map_appC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface6jt_lenK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s015Y0HDIC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01C47Corelib4Init3Nat3subC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing3Pol01C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List<length_skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subI4ELinuxProcessSemantics5Riscv7Prelude4tree00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface=bit_init_postC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_bitinit>bit_init_proofC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<init_dstreamC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_zeroC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface:bitd_cellsC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6bd_ptrC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_contC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s04Ey4_init_dstream_shapeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s049y4s04_chkC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>negb_false_iffC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32K4ELinuxProcessSemantics5Riscv5Instr5instr06K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s04:y4s04_loopC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>neg_desc_shiftC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s04;y4_sx32_litK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s04Iy4_init_dstream_err_rangeC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s7y4s_epiK46Stdlib9micromega7EnvRing5PExpr06K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission3Lib6ExElim9ex_elim_9C5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C46Stdlib5Lists4List:length_mapC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z7inj_minI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init5Logic4True00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultI47Corelib4Init9Datatypes:comparison00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib5Lists4List6Exists00K4ELinuxProcessSemantics5Riscv5Instr5aluop02C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface=PHUF_BIT_INITI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section Y4S04M.
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
  Hypothesis DT4 : DT mod 4 = 0.

  (* [comment removed for export] *)
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation YB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation Y4F' mm spl b4 b3 b2 b1 :=
    (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).
  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation Y4S' mm := (Y4S ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm).
  Notation L1 := (jt_len src 0). Notation L2 := (jt_len src 2). Notation L3 := (jt_len src 4).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Notation SEG := ((dcap + 3) / 4).
  Notation desc := (tl + 256 * mtl).
  (* [comment removed for export] *)
  Notation SPL436 j0 j112 :=
    [CB 96 j0; C8 (Z_to_bv 64 (DST + SEG)); C8 (Z_to_bv 64 (DST + 2 * SEG)); CB 8 j112;
     C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (DT + 4))].
  Notation BS1 := (firstn (Z.to_nat L1) (skipn (Z.to_nat 6) src)).
  Notation BS2 := (firstn (Z.to_nat L2) (skipn (Z.to_nat O2) src)).
  Notation BS3 := (firstn (Z.to_nat L3) (skipn (Z.to_nat O3) src)).
  Notation BS4 := (firstn (Z.to_nat (n - O4)) (skipn (Z.to_nat O4) src)).
  Notation L4 := (n - (6 + L1 + L2 + L3)).

  Notation SPLL w64 k4 k2 p2 k1 j0 :=
    (SPLB desc (DST + 3 * SEG) dcap (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (DST + dcap - 7) w64 k4 k2
          (SS + O2 + p2) (DST + SEG) (DST + 2 * SEG) k1 (DST + dcap) (DT + 4) j0).
  Notation SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0 :=
    (SPLB desc (DST + 3 * SEG) v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88
          (DST + SEG) (DST + 2 * SEG) v112 (DST + dcap) (DT + 4) j0).
  Notation BDS c b p O jp := (BD4 c b (SS + O + p) (SS + O) jp).

  Hypothesis LOOP : (1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n) -> (0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG) -> 2 <= SEG ->
    forall q1 q2 q3 q4 b1 b2 b3 b4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4
                           (xt2 xs0 xa0 xa2 xa3 xa4 xs5 xs6 xs8 xs10 xt5 : word),
    Y4F' mm (SPLL w64 c4 c2 p2 c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    Y1OPS SEG q1 q2 q3 q4 -> q4 + 8 <= dcap ->
    Y1HDI L1 p1 b1 -> Y1HDI L2 p2 b2 -> Y1HDI L3 p3 b3 -> Y1HDI L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 -> 0 <= w64 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            xt2 xs0 (Z_to_bv 64 b1) xa0 (Z_to_bv 64 (DST + q1)) xa2 xa3 xa4 (Z_to_bv 64 (2^61))
                            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 (DST + q4)) (Z_to_bv 64 c3)
                            (Z_to_bv 64 (DST + q3)) xs5 xs6 (Z_to_bv 64 b3) xs8 (Z_to_bv 64 b4) xs10 (Z_to_bv 64 (DST + q2))
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 0x1aaf4) fc None mm (seg_rom usegs)).

  Hypothesis EXIT : (1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n) -> (0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG) -> 2 <= SEG ->
    forall q1 q2 q3 q4 b1 b2 b3 b4 p1 p2 p3 p4 st1 st2 st3 st4 c1 c2 c3 c4
                           v24 v32 v40 v48 v64 v72 v80 v88 v112 mm j0 jp1 jp2 jp3 jp4
                           (xra xt0 xt2 xs0 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 : word),
    Y4F' mm (SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0)
         (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    0 <= q1 <= dcap -> 0 <= q2 <= dcap -> 0 <= q3 <= dcap -> 0 <= q4 <= dcap ->
    Y1AFT L1 p1 b1 st1 -> Y1AFT L2 p2 b2 st2 -> Y1AFT L3 p3 b3 st3 -> Y1AFT L4 p4 b4 st4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp xt0 (Z_to_bv 64 (DT + 4)) xt2 xs0 xs1 xa0
                            (Z_to_bv 64 (DST + q1)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DST + q4)) xs3 (Z_to_bv 64 (DST + q3))
                            xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + q2)) xt3 xt4 xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 0x1b41c) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma y4m_hdi : forall bs d, Forall (fun c => 0 <= c < 256) bs -> init_dstream bs = Ok d ->
    1 <= zlen bs /\ Y1HDI (zlen bs) (bd_ptr d) (bd_bits d) /\ 0 <= bd_cont d < 2^64.
  Proof.
    intros bs d BY ED.
    pose proof (y4_init_dstream_shape bs d BY ED) as SH.
    pose proof (init_dstream_ok bs) as INI0.
    first [pose proof (INI0 (Forall_all_bytes _ BY)) as INI | pose proof INI0 as INI]; clear INI0.
    destruct INI as [(e & EE) | (d' & ED' & BOK & _ & _)].
    - rewrite ED in EE; discriminate.
    - rewrite ED in ED'; injection ED' as <-.
      split; [lia | split; [unfold Y1HDI; lia | exact (proj1 BOK)]].
  Qed.
  (* [comment removed for export] *)
  Lemma y4m_cb8_c8 : forall m A pre b post, rw_cells usegs m A (pre ++ CB 8 b :: post) ->
    exists v, rw_cells usegs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
  Proof.
    intros m A pre b post H.
    assert (L : length b = 8%nat).
    { destruct H as [[WF _] _]. clear -WF. induction pre as [|c pre IH]; cbn in WF.
      - exact (proj1 WF).
      - exact (IH (proj2 WF)). }
    exists (bv_unsigned (le_bytes_to_word b)). rewrite Z_to_bv_bv_unsigned.
    apply RF_huf_x2t_fr.rw_cells_cb8_c8; assumption.
  Qed.
  (* [comment removed for export] *)
  Ltac y4m_cb8_at H k :=
    lazymatch type of H with rw_cells _ ?m ?A ?cs =>
      let pre := eval cbn [firstn] in (firstn k cs) in
      let post := eval cbn [skipn] in (skipn (S k) cs) in
      let c := eval cbn [nth] in (nth k cs (C1 (Z_to_bv 8 0))) in
      lazymatch c with Cells.CB 8 ?b =>
        let v := fresh "v" in let H' := fresh "H" in
        destruct (y4m_cb8_c8 m A pre b post H) as (v & H'); clear H; cbn [app] in H'; rename H' into H end end.
  Ltac y4m_frame :=
    lazymatch goal with H : rw_cells usegs ?m (SP + -912) (SPL436 ?j0 ?j112) |- _ =>
      apply (rw_cells_split_CB usegs m (SP + -912) [] 96 j0 _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in H; [|reflexivity];
      cbn [app mk_CB_cells] in H;
      y4m_cb8_at H 1%nat; y4m_cb8_at H 2%nat; y4m_cb8_at H 3%nat; y4m_cb8_at H 4%nat; y4m_cb8_at H 5%nat;
      y4m_cb8_at H 6%nat; y4m_cb8_at H 7%nat; y4m_cb8_at H 8%nat; y4m_cb8_at H 9%nat; y4m_cb8_at H 10%nat;
      y4m_cb8_at H 11%nat; y4m_cb8_at H 14%nat end.
  (* [comment removed for export] *)
  Ltac y4m_y4f :=
    unfold Y4F; repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | reflexivity | (eexists; split; eassumption) | (eexists; eassumption)
          | (do 12 eexists; unfold PY4_RET; eassumption) ].
  Ltac y4m_call D S BS L :=
    assert (ZLB : Z.of_nat (length BS) = L) by (apply y4_sub_len; lia);
    assert (LMB : Z.of_nat (length (map (Z_to_bv 8) BS)) = L) by (rewrite length_map; exact ZLB);
    call (bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D S BS _ lo);
    repeat match goal with E : bv_unsigned (Z_to_bv 64 _) = _ |- _ => rewrite E end;
    try (first [eassumption | lia | reflexivity | (rewrite ZLB; reflexivity) | (rewrite ZLB; lia) | (apply y4_bytes_sub; exact BYS) | (f_equal; lia)]).
  Ltac y4m_after BS :=
    let INI0 := fresh "INI0" in let INI := fresh "INI" in
    pose proof (init_dstream_ok BS) as INI0;
    first [pose proof (INI0 (Forall_all_bytes _ ltac:(apply y4_bytes_sub; exact BYS))) as INI | pose proof INI0 as INI]; clear INI0;
    let e := fresh "e" in let EE := fresh "EE" in let d := fresh "d" in let ED := fresh "ED" in
    destruct INI as [(e & EE) | (d & ED & ? & ? & ?)];
    [ lazymatch goal with H : context [match init_dstream BS with _ => _ end] |- _ =>
        rewrite EE in H; cbn iota in H; let RET := fresh "RET" in destruct H as (RET & ? & ?);
        lazymatch type of RET with ?r = _ => subst r end end;
      pose proof (y4_init_err _ e EE)
    | lazymatch goal with H : context [match init_dstream BS with _ => _ end] |- _ =>
        rewrite ED in H; cbn iota in H; let RET := fresh "RET" in destruct H as (RET & ? & ? & ?);
        lazymatch type of RET with ?r = _ => subst r end end ];
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end).

  (* [comment removed for export] *)
  Lemma y4s04_call4 : forall mm j0 j112 jb4 d1 jp1 d2 jp2 d3 jp3
      (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Y4F' mm (SPL436 j0 j112) [CB 40 jb4] (bitd_cells (SS + O3) d3 jp3) (bitd_cells (SS + O2) d2 jp2) (bitd_cells (SS + 6) d1 jp1) ->
    init_dstream BS1 = Ok d1 -> init_dstream BS2 = Ok d2 -> init_dstream BS3 = Ok d3 ->
    6 <= dcap -> 10 <= n -> O4 <= n ->
    t1 = Z_to_bv 64 (DST + dcap) -> x8 = Z_to_bv 64 DST -> x9 = Z_to_bv 64 (SS + O3) ->
    a0 = Z_to_bv 64 (SP + -776) -> a1 = Z_to_bv 64 (SS + O4) -> a2 = Z_to_bv 64 (n - O4) ->
    x18 = Z_to_bv 64 L3 -> x19 = Z_to_bv 64 (-120) -> x20 = Z_to_bv 64 L2 -> x21 = Z_to_bv 64 O4 ->
    x22 = Z_to_bv 64 n -> x23 = Z_to_bv 64 (-120) -> x24 = Z_to_bv 64 desc -> x25 = Z_to_bv 64 (DST + 2 * SEG) ->
    x26 = Z_to_bv 64 dcap -> x27 = Z_to_bv 64 (DST + 3 * SEG) ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1aa3c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros mm j0 j112 jb4 d1 jp1 d2 jp2 d3 jp3 xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6
      XF ED1 ED2 ED3 D6 N10 NO4 E6 E8 E9 E10 E11 E12 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27.
    subst t1 x8 x9 a0 a1 a2 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27.
    destruct XF as (BUF & SRC & CBS & ST & SPC & LS0 & B4 & LB4 & B3 & LB3 & B2 & LB2 & B1 & LB1 & SV & (jl & JL) & FR & MI & MU & WM).
    destruct SV as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SV). unfold PY4_RET in SV.
    destruct BUF as (buf & OUT & LBUF).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TOK as (TL1 & _). unfold HUF_TABLELOG_MAX in TL1.
    assert (Y0 : 0 <= Znth 0 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y1 : 0 <= Znth 1 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y2 : 0 <= Znth 2 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y3 : 0 <= Znth 3 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y4 : 0 <= Znth 4 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y5 : 0 <= Znth 5 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (HL1 : 0 <= L1 < 2^16) by (unfold jt_len; change (0 + 1) with 1; lia).
    assert (HL2 : 0 <= L2 < 2^16) by (unfold jt_len; change (2 + 1) with 3; lia).
    assert (HL3 : 0 <= L3 < 2^16) by (unfold jt_len; change (4 + 1) with 5; lia).
    assert (LMS : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    pose proof (y4m_hdi BS1 d1 (y4_bytes_sub src 6 L1 BYS) ED1) as (KL1 & HD1 & CC1).
    pose proof (y4m_hdi BS2 d2 (y4_bytes_sub src O2 L2 BYS) ED2) as (KL2 & HD2 & CC2).
    pose proof (y4m_hdi BS3 d3 (y4_bytes_sub src O3 L3 BYS) ED3) as (KL3 & HD3 & CC3).
    rewrite (y4_sub_len src 6 L1) in KL1, HD1 by lia.
    rewrite (y4_sub_len src O2 L2) in KL2, HD2 by lia.
    rewrite (y4_sub_len src O3 L3) in KL3, HD3 by lia.
    pose proof (y4_src_sub usegs mm SS src O4 (n - O4) SRC ltac:(lia) ltac:(lia) ltac:(lia)) as SB4.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -912)) = SP + -912)
      by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    zstep.
    y4m_call constr:(SP + -776) constr:(SS + O4) constr:(firstn (Z.to_nat (n - O4)) (skipn (Z.to_nat O4) src)) constr:(n - O4).
    y4m_after constr:(firstn (Z.to_nat (n - O4)) (skipn (Z.to_nat O4) src)).
    all: y4z_walk 0x1aa48 0x1dc54 SS src SRC.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1dc54) _ _ _ _) => eapply (YB y4s_epi); y4m_y4f
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1aa48) _ _ _ _) =>
             first [ solve [exfalso; first [lia | (Z.div_mod_to_equations; lia)]]
                   | solve [exfalso; match goal with B : - ?e mod ?M <= _, EB : 0 < ?e < 120 |- _ =>
                              clear - B EB; Z.div_mod_to_equations; lia end]
                   | lazymatch goal with ED4 : init_dstream BS4 = Ok ?d4 |- _ =>
                       pose proof (y4m_hdi BS4 d4 (y4_bytes_sub src O4 (n - O4) BYS) ED4) as (KL4 & HD4 & CC4);
                       rewrite (y4_sub_len src O4 (n - O4)) in KL4, HD4 by lia;
                       y4m_frame;
                       eapply (y4s04_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                                 TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DT4 LOOP EXIT
                                 _ (bd_cont d1) (bd_cont d2) (bd_cont d3) (bd_cont d4) (bd_bits d1) (bd_bits d2) (bd_bits d3) (bd_bits d4)
                                 (bd_ptr d1) (bd_ptr d2) (bd_ptr d3) (bd_ptr d4));
                       first [ solve [unfold SPLB; y4m_y4f] | lia | eassumption ]
                     end ]
         end.
  Qed.

End Y4S04M.
End CANSEC1.
