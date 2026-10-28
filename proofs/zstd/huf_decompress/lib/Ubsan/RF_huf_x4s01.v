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
  RF_huf_x4s RF_huf_x4s01s RF_huf_x4s02s RF_huf_x4s03s RF_huf_x4s04.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s01 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface6jt_lenC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s7x4s_epiC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8I47Corelib4Init5Logic2or00C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm1C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm3K4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit3nsmC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_aC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_bC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_cK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_dK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_le_monoK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s13HDIC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameK4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop03K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Section X4S01.
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
  Hypothesis DTA : DT mod 4 = 0.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation X4F' mm spl bd1 bd2 bd3 bd4 :=
    (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl bd1 bd2 bd3 bd4).
  Notation J1 := (Znth 0 src + 256 * Znth 1 src).
  Notation J2 := (Znth 2 src + 256 * Znth 3 src).
  Notation J3 := (Znth 4 src + 256 * Znth 5 src).
  Notation SG := ((dcap + 3) ≫ 2).
  Notation BS1 := (firstn (Z.to_nat J1) (skipn (Z.to_nat 6) src)).
  Notation BS2 := (firstn (Z.to_nat J2) (skipn (Z.to_nat (6 + J1)) src)).
  Notation BS3 := (firstn (Z.to_nat J3) (skipn (Z.to_nat (6 + J1 + J2)) src)).
  Notation BS4 := (skipn (Z.to_nat (6 + J1 + J2 + J3)) src).
  Notation BDC S d jp := [C8 (Z_to_bv 64 (bd_cont d)); C4 (Z_to_bv 64 (bd_bits d)); CB 4 jp; C8 (Z_to_bv 64 (S + bd_ptr d));
                          C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].

  (* [comment removed for export] *)
  Hypothesis LOOPK : forall (L1 L2 L3 L4 SEG : Z),
    1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n ->
    0 < SEG /\ 3 * SEG <= dcap /\ 4 <= dcap ->
    forall q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 mm j0 j96 j120 jp1 jp2 jp3 jp4
           (t2 x8 x9 a0 a2 a4 x21 x22 x27 t4 : word),
    X4F' mm (SPL3 (DST + 3 * SEG) (tl + 256 * mtl) (SS + (6 + L1 + L2 + L3) + 8) (SS + (6 + L1 + L2) + 8) (SS + (6 + L1) + 8)
                  (3 * SEG) (2 * SEG) (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + 2 * SEG) dcap DST
                  (SS + (6 + L1 + L2 + L3) + p4) j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + (6 + L1) + p2) (SS + (6 + L1)) jp2)
            (BD4 c3 b3 (SS + (6 + L1 + L2) + p3) (SS + (6 + L1 + L2)) jp3)
            (BD4 c4 b4 (SS + (6 + L1 + L2 + L3) + p4) (SS + (6 + L1 + L2 + L3)) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    (0 <= p1 /\ (p1 = 0 \/ p1 + 8 <= L1) /\ 0 <= b1 <= 64 /\ (8 <= p1 -> b1 <= 8)) ->
    (0 <= p2 /\ (p2 = 0 \/ p2 + 8 <= L2) /\ 0 <= b2 <= 64 /\ (8 <= p2 -> b2 <= 8)) ->
    (0 <= p3 /\ (p3 = 0 \/ p3 + 8 <= L3) /\ 0 <= b3 <= 64 /\ (8 <= p3 -> b3 <= 8)) ->
    (0 <= p4 /\ (p4 = 0 \/ p4 + 8 <= L4) /\ 0 <= b4 <= 64 /\ (8 <= p4 -> b4 <= 8)) ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + (6 + L1) + p2)) (Z_to_bv 64 (SS + (6 + L1 + L2) + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1) a4
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) x21 x22 (Z_to_bv 64 c4)
                           (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c1) t4 (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 0x17ad0) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma x4s01_loop : forall mm (d1 d2 d3 d4 : bitD) buf j0 j96 j120 jj jp1 jp2 jp3 jp4
                            (t2 x8 x9 a0 a2 a4 x21 x22 x27 t4 : word),
    init_dstream BS1 = Ok d1 -> init_dstream BS2 = Ok d2 -> init_dstream BS3 = Ok d3 -> init_dstream BS4 = Ok d4 ->
    6 <= dcap -> 10 <= n -> 6 + J1 + J2 + J3 <= n -> 3 * SG + 8 <= dcap ->
    u8arr usegs mm DST (map (Z_to_bv 8) buf) -> zlen buf = dcap ->
    bytes_at usegs mm SS (map (Z_to_bv 8) src) -> bytes_at usegs mm (DT + 4) cbs ->
    stk usegs mm lo (bv_unsigned (Z_to_bv 64 (SP + -512))) ->
    rw_cells usegs mm (SP + -512)
      [CB 8 j0; C8 (Z_to_bv 64 (DST + SG + SG + SG)); C8 (zx16 (Z_to_bv 64 (tl + 256 * mtl)));
       C8 (Z_to_bv 64 (SS + 6 + J1 + J2 + J3 + 8)); C8 (Z_to_bv 64 (SS + 6 + J1 + J2 + 8)); C8 (Z_to_bv 64 (SS + 6 + J1 + 8));
       C8 (Z_to_bv 64 (SG ≪ 1 + SG)); C8 (Z_to_bv 64 (SG ≪ 1)); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (DST + SG));
       C8 (Z_to_bv 64 (DST + dcap + -3)); C8 (Z_to_bv 64 (DST + SG + SG)); CB 8 j96; C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST);
       CB 8 j120; C8 (Z_to_bv 64 (SS + 6 + J1 + J2 + J3 + bd_ptr d4))] ->
    rw_cells usegs mm (SP + -376) (BDC (SS + 6) d1 jp1) ->
    rw_cells usegs mm (SP + -336) [CB 112 jj] ->
    rw_cells usegs mm (SP + -224) (BDC (SS + 6 + J1 + J2 + J3) d4 jp4) ->
    rw_cells usegs mm (SP + -184) (BDC (SS + 6 + J1 + J2) d3 jp3) ->
    rw_cells usegs mm (SP + -144) (BDC (SS + 6 + J1) d2 jp2) ->
    rw_cells usegs mm (SP + -104) FRS -> mem_inv usegs mm -> munch DW m0 mm -> wmono usegs m0 mm ->
    evt usegs POST (MS (mkR (sx32 (Z_to_bv 64 (bd_bits d2))) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + 6 + J1 + bd_ptr d2)) (Z_to_bv 64 (SS + 6 + J1 + J2 + bd_ptr d3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)) a2 (sx32 (Z_to_bv 64 (bd_bits d1))) a4
                           (Z_to_bv 64 4611686018427387904)
                           (Z_to_bv 64 (Z.land (bv_swrap 32 (0 - bv_unsigned (zx16 (Z_to_bv 64 (tl + 256 * mtl)))) mod 18446744073709551616) 63))
                           (Z_to_bv 64 (-1))
                           (sx32 (Z_to_bv 64 (bd_bits d4))) (sx32 (Z_to_bv 64 (bd_bits d3))) (Z_to_bv 64 (bd_cont d2)) x21 x22
                           (Z_to_bv 64 (bd_cont d4))
                           (Z_to_bv 64 DST) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SG) x27
                           (Z_to_bv 64 (bd_cont d1)) t4 (Z_to_bv 64 (SS + 6 + bd_ptr d1)) (Z_to_bv 64 (bd_cont d3)))
                       F (Z_to_bv 64 0x17ad0) fc None mm (seg_rom usegs)).
  Proof using All.
    intros mm d1 d2 d3 d4 buf j0 j96 j120 jj jp1 jp2 jp3 jp4 t2 x8 x9 a0 a2 a4 x21 x22 x27 t4
      I1 I2 I3 I4 FD FN0 FN FS UA UL SRC CBS STK SPC B1 JJ B4 B3 B2 FR MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TOK as (TL1 & _). unfold HUF_TABLELOG_MAX in TL1.
    assert (SGE : SG = (dcap + 3) / 4) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (Y0 : 0 <= Znth 0 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y1 : 0 <= Znth 1 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y2 : 0 <= Znth 2 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y3 : 0 <= Znth 3 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y4 : 0 <= Znth 4 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y5 : 0 <= Znth 5 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    pose proof (x4_ids_ok _ _ (x4_bytes_sub src 6 J1 BYS) I1) as (C1 & G1 & N1 & P1 & Q1 & R1).
    pose proof (x4_ids_ok _ _ (x4_bytes_sub src (6 + J1) J2 BYS) I2) as (C2 & G2 & N2 & P2 & Q2 & R2).
    pose proof (x4_ids_ok _ _ (x4_bytes_sub src (6 + J1 + J2) J3 BYS) I3) as (C3 & G3 & N3 & P3 & Q3 & R3).
    pose proof (x4_ids_ok _ _ (x4_bytes_tail src (6 + J1 + J2 + J3) BYS) I4) as (C4 & G4 & N4 & P4 & Q4 & R4).
    rewrite x4_sub_len in N1, Q1 by lia. rewrite x4_sub_len in N2, Q2 by lia. rewrite x4_sub_len in N3, Q3 by lia.
    rewrite x4_tail_len in N4, Q4 by lia.
    assert (A6 : Z.land (bv_swrap 32 (0 - (tl + 256 * mtl)) mod 18446744073709551616) 63 = 64 - tl).
    { rewrite <- (neg_desc_shift2 tl mtl) by lia. rewrite (Z.mod_small (tl + 256 * mtl)) by lia. reflexivity. }
    rewrite (x4_uzx16 (tl + 256 * mtl)) by lia. rewrite A6. clear A6.
    rewrite !sx32_small by lia.
    rewrite x4_m1.
    change (Z_to_bv 64 4611686018427387904) with (Z_to_bv 64 (2^62)).
    change (Z.lxor (DT + 4) 18446744073709551615) with (Z.lxor (DT + 4) (2^64 - 1)).
    replace (SS + 6 + J1 + bd_ptr d2) with (SS + (6 + J1) + bd_ptr d2) by lia.
    replace (SS + 6 + J1 + J2 + bd_ptr d3) with (SS + (6 + J1 + J2) + bd_ptr d3) by lia.
    replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
    rewrite (x4_zx16 (tl + 256 * mtl)) in SPC by lia.
    rewrite Z.shiftl_mul_pow2 in SPC by lia. change (2 ^ 1) with 2 in SPC.
    rewrite unsigned_lit in STK by lia.
    assert (HL : 1 <= J1 /\ 1 <= J2 /\ 1 <= J3 /\ 1 <= n - (6 + J1 + J2 + J3) /\ 6 + J1 + J2 + J3 + (n - (6 + J1 + J2 + J3)) <= n) by lia.
    assert (HQ : 0 < SG /\ 3 * SG <= dcap /\ 4 <= dcap) by lia.
    eapply (LOOPK J1 J2 J3 (n - (6 + J1 + J2 + J3)) SG HL HQ 0 (bd_ptr d1) (bd_ptr d2) (bd_ptr d3) (bd_ptr d4)
              (bd_bits d1) (bd_bits d2) (bd_bits d3) (bd_bits d4) (bd_cont d1) (bd_cont d2) (bd_cont d3) (bd_cont d4)
              mm j0 j96 j120 jp1 jp2 jp3 jp4).
    all: try lia.
    unfold X4F, SPL3, BD4.
    repeat match goal with |- _ /\ _ => split end.
    all: first [ assumption | reflexivity | (exists buf; split; assumption) | (exists jj; exact JJ)
               | (eapply x4_cells_conv; [eassumption | x4_cells_eq]) ].
  Qed.
End X4S01.
End CANSEC1.
