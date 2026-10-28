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
  RF_huf_fa_iface RF_huf_y4s RF_huf_y4s_iface RF_huf_y4s0 RF_huf_bitinit RF_huf_y4s01.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4s03 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface6jt_lenK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s015Y0HDII47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s7y4s_epiC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s6y4s_m1C56Stdlib6ZArith6BinInt1Z7add_0_rC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm1C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm3C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit3nsmC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_aC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_bC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_cK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_dK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_le_monoK47Corelib4Init5Logic3and01K4ELinuxProcessSemantics5Riscv5Instr5instr03K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics5Riscv5Instr5instr0:K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop03K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section Y4S03.
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

  (* [comment removed for export] *)
  Hypothesis HC516 : forall mm j0 j112 jb4 d1 jp1 d2 jp2 d3 jp3
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

  (* [comment removed for export] *)
  Ltac y4s03_y4f :=
    unfold Y4F; repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | reflexivity | (eexists; split; eassumption) | (eexists; eassumption)
          | (do 12 eexists; unfold PY4_RET; eassumption) ].
  (* [comment removed for export] *)
  Ltac y4s03_call D S BS L :=
    assert (ZLB : Z.of_nat (length BS) = L) by (apply y4_sub_len; lia);
    assert (LMB : Z.of_nat (length (map (Z_to_bv 8) BS)) = L) by (rewrite length_map; exact ZLB);
    call (bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D S BS _ lo);
    repeat match goal with E : bv_unsigned (Z_to_bv 64 _) = _ |- _ => rewrite E end;
    try (first [eassumption | lia | reflexivity | (rewrite ZLB; reflexivity) | (rewrite ZLB; lia) | (apply y4_bytes_sub; exact BYS) | (f_equal; lia)]).
  (* [comment removed for export] *)
  Ltac y4s03_after BS :=
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
  Lemma y4s03_call3 : forall mm j0 j112 jb4 jb3 d1 jp1 d2 jp2
      (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Y4F' mm (SPL436 j0 j112) [CB 40 jb4] [CB 40 jb3] (bitd_cells (SS + O2) d2 jp2) (bitd_cells (SS + 6) d1 jp1) ->
    init_dstream BS1 = Ok d1 -> init_dstream BS2 = Ok d2 ->
    6 <= dcap -> 10 <= n -> O4 <= n ->
    t1 = Z_to_bv 64 (DST + dcap) -> x8 = Z_to_bv 64 DST -> x9 = Z_to_bv 64 (SS + O3) ->
    a0 = Z_to_bv 64 (SP + -736) -> a1 = Z_to_bv 64 (SS + O3) -> a2 = Z_to_bv 64 L3 ->
    x18 = Z_to_bv 64 L3 -> x19 = Z_to_bv 64 (SS + O2) -> x20 = Z_to_bv 64 L2 -> x21 = Z_to_bv 64 O4 ->
    x22 = Z_to_bv 64 n -> x23 = Z_to_bv 64 (-120) -> x24 = Z_to_bv 64 desc -> x25 = Z_to_bv 64 (DST + 2 * SEG) ->
    x26 = Z_to_bv 64 dcap -> x27 = Z_to_bv 64 (DST + 3 * SEG) ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1aa20) fc None mm (seg_rom usegs)).
  Proof using All.
    intros mm j0 j112 jb4 jb3 d1 jp1 d2 jp2 xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6
      XF ED1 ED2 D6 N10 NO4 E6 E8 E9 E10 E11 E12 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27.
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
    pose proof (y4_src_sub usegs mm SS src O3 L3 SRC ltac:(lia) ltac:(lia) ltac:(lia)) as SB3.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -912)) = SP + -912)
      by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    zstep.
    y4s03_call constr:(SP + -736) constr:(SS + O3) constr:(firstn (Z.to_nat L3) (skipn (Z.to_nat O3) src)) constr:(L3).
    y4s03_after constr:(firstn (Z.to_nat L3) (skipn (Z.to_nat O3) src)).
    all: y4z_walk 0x1aa3c 0x1dc54 SS src SRC.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1dc54) _ _ _ _) => eapply (YB y4s_epi); y4s03_y4f
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1aa3c) _ _ _ _) =>
             first [ solve [exfalso; first [lia | (Z.div_mod_to_equations; lia)]]
                   | (eapply HC516; first [ y4s03_y4f | eassumption | lia | reflexivity | (f_equal; lia) ]) ]
         end.
  Qed.

End Y4S03.
End CANSEC1.
(* [comment removed for export] *)
