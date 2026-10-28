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
  RF_huf_x4s RF_huf_y4s31_kit RF_huf_x4s31_kit RF_huf_y4_kit_reload RF_huf_x4s1 RF_huf_x4s1c.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s1b () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s15LOOPKK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s13AFTC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s13BEFC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K47Corelib4Init5Logic2eq01K4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7compareI46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeK47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics5Riscv7Prelude4tree00C45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s17x4s1_r3C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s17x4s1_n3C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4onesC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s1b7x4s1_n2c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s1b7x4s1_r2c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s1b7x4s1_n1c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s1b7x4s1_r1".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section X4S1.
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
  Notation XB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DTA) (only parsing).
  Notation X4F' mm spl bd1 bd2 bd3 bd4 :=
    (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl bd1 bd2 bd3 bd4).

  Variables (L1 L2 L3 L4 SEG : Z).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Hypothesis HL : 1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n.
  Hypothesis HQ : 0 < SEG /\ 3 * SEG <= dcap /\ 4 <= dcap.
  Hypothesis CHK : forall (L1 L2 L3 L4 SEG Q2 Q3 : Z),
    1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n ->
    0 < SEG <= Q2 /\ Q2 <= Q3 /\ Q3 <= dcap /\ 4 <= dcap ->
    forall q1 q2 q3 q4 pt1 pt2 pt3 pt4 c1 b1 c2 b2 c3 b3 c4 b4 v8 v16 v24 v32 v40 v48 v56 v128 mm j0 j96 j120
           jp1 jp2 jp3 jp4 (xra t0 t1 x8 x9 a0 a1 a2 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word),
    X4F' mm (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + Q2) dcap DST v128 j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + pt1) (SS + 6) jp1) (BD4 c2 b2 (SS + (6 + L1) + pt2) (SS + (6 + L1)) jp2)
            (BD4 c3 b3 (SS + (6 + L1 + L2) + pt3) (SS + (6 + L1 + L2)) jp3)
            (BD4 c4 b4 (SS + (6 + L1 + L2 + L3) + pt4) (SS + (6 + L1 + L2 + L3)) jp4) ->
    0 <= q1 -> 0 <= q2 -> 0 <= q3 -> 0 <= q4 <= dcap ->
    DST + q1 < 2^64 -> DST + q2 < 2^64 -> DST + q3 < 2^64 ->
    0 <= pt1 -> (pt1 = 0 \/ pt1 + 8 <= L1) -> 0 <= pt2 -> (pt2 = 0 \/ pt2 + 8 <= L2) ->
    0 <= pt3 -> (pt3 = 0 \/ pt3 + 8 <= L3) -> 0 <= pt4 -> (pt4 = 0 \/ pt4 + 8 <= L4) ->
    0 <= b1 < 2^31 -> 0 <= b2 < 2^31 -> 0 <= b3 < 2^31 -> 0 <= b4 < 2^31 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 DST) x8 x9 a0 a1 a2 (Z_to_bv 64 (DST + SEG))
                           a4 a5 a6 a7 (Z_to_bv 64 (DST + q1)) (Z_to_bv 64 (tl + 256 * mtl)) x20 (Z_to_bv 64 (DST + q4))
                           (Z_to_bv 64 (DST + q3)) (Z_to_bv 64 (DST + q2)) (Z_to_bv 64 (DST + Q3)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 SEG) (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x18cfc) fc None mm (seg_rom usegs)).
  Notation A1 l := (XB l L1 L2 L3 L4 SEG HL HQ) (only parsing).
  Notation LOOPK' q := (LOOPK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG q).

  Definition X4D1 : Prop :=
    forall q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 mm j0 j96 j120 jp1 jp2 jp3 jp4 (t2 x8 x9 a0 x27 : word),
    LOOPK' q ->
    X4F' mm (SPL3 (DST + 3 * SEG) (tl + 256 * mtl) (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (3 * SEG) (2 * SEG)
                  (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + 2 * SEG) dcap DST (SS + O4 + p4) j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    BEF L1 p1 b1 -> BEF L2 p2 b2 -> BEF L3 p3 b3 -> BEF L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) (Z_to_bv 64 (SS + 14)) (Z_to_bv 64 b1)
                           (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) (Z_to_bv 64 3)
                           (Z_to_bv 64 (DST + q + 2 * SEG + 3)) (Z_to_bv 64 c4)
                           (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c1) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 0x17f18) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Notation SPL1 st1 c1 v128 j0 :=
    [CB 8 j0; C8 (Z_to_bv 64 (DST + 3 * SEG)); C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (SS + O4 + 8));
     C8 (Z_to_bv 64 (SS + O3 + 8)); C8 (Z_to_bv 64 (SS + O2 + 8)); C8 (Z_to_bv 64 (3 * SEG)); C8 (Z_to_bv 64 (2 * SEG));
     C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (DST + SEG)); C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 (DST + 2 * SEG));
     C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 v128)].

  Ltac x4open H :=
    destruct H as ((buf & OUT & LB) & SRC & CBS & STK & SPC & L0 & BDa & LBa & (jj & JJ) & BDd & LDd & BDc & LDc & BDb & LDb
                   & FR & MI & MU & WM);
    change (zlen buf) with (Z.of_nat (length buf)) in LB;
    pose proof TOK as (TL1 & TLN & TCK); cbv [HUF_TABLELOG_MAX] in TL1; cbv [FseNCount.Zlength] in TLN;
    pose proof (DP ltac:(lia)) as D8; pose proof (length_map (Z_to_bv 8) src) as LMS; unfold SPL3, BD4 in *;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  Ltac x4pack H := ubdnorm H; unfold X4F, SPL3, BD4; upack.

  Ltac xrl A S p b :=
    rewrite <- (Z.add_sub_assoc S p (b / 8)) in *;
    match goal with H : rw_cells _ _ A (C8 (Z_to_bv 64 ?w) :: _) |- _ => rewrite <- (Z_to_bv_lit_self (Z_to_bv 64 w)) in * end.

  Ltac xside := first [ assumption | lia
                      | match goal with |- 0 <= bv_unsigned ?w < _ =>
                          let R := fresh "R" in pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; cbn in R; lia end
                      | unfold AFT, BEF in *; lia ].

  Notation X4R3' q := (X4R3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG q).
  Notation X4N3' q := (X4N3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG q).

  Section X4S1B.
  Hypothesis R3 : forall q, LOOPK' q -> X4R3' q.
  Hypothesis N3 : forall q, LOOPK' q -> X4N3' q.

  (* [comment removed for export] *)
  Lemma x4s1_n2 : forall q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 mm j0 jp1 jp2 jp3 jp4
                         (t2 x8 x9 a0 a2 x22 x23 x27 : word),
    LOOPK' q ->
    X4F' mm (SPL1 st1 c1 (SS + O4 + p4) j0)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    AFT L1 p1 b1 st1 -> AFT L2 p2 b2 st2 -> BEF L3 p3 b3 -> BEF L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1)
                           (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) (Z_to_bv 64 st2) x22 x23
                           (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c4) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 0x1806c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until x27. intros LK XF Q0 QD A1 A2 B3 B4 C1 C2 C3 C4. x4open XF.
    xwalk [0x18078; 0x18250] tl DT cells cbs ECB TCK OUT LB SRC.
    all: first [ solve [pose proof (R3 q LK) as R; unfold X4R3 in R; eapply R; [x4pack BDa | xside ..]]
               | solve [pose proof (N3 q LK) as R; unfold X4N3 in R; eapply R; [x4pack BDa | xside ..]] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x4s1_r2 : forall q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 mm j0 jp1 jp2 jp3 jp4
                         (t2 x8 x9 a0 a2 x20 x21 x22 x23 x27 : word),
    LOOPK' q ->
    X4F' mm (SPL1 st1 c1 (SS + O4 + p4) j0)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    AFT L1 p1 b1 st1 -> BEF L2 p2 b2 -> 8 <= p2 -> BEF L3 p3 b3 -> BEF L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1)
                           (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) x20 x21 x22 x23
                           (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c4) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 0x17fcc) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until x27. intros LK XF Q0 QD A1 B2 P8 B3 B4 C1 C2 C3 C4. x4open XF.
    unfold BEF in B2. destruct B2 as (P20 & P2D & B2R & B2S).
    assert (P2H : p2 + 8 <= L2) by lia. assert (B56 : b2 <= 56) by lia. clear P2D B2S.
    xwalk [0x1806c] tl DT cells cbs ECB TCK OUT LB SRC.
    all: xrl (SP + -144) (SS + O2) p2 b2.
    all: eapply x4s1_n2; [exact LK | x4pack BDa | xside ..].
  Qed.

  (* [comment removed for export] *)
  Lemma x4s1_r1 : forall q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 mm j0 j96 j120 jp1 jp2 jp3 jp4
                         (t2 x8 x9 a0 a2 x22 x27 t3 : word),
    LOOPK' q ->
    X4F' mm (SPL3 (DST + 3 * SEG) (tl + 256 * mtl) (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (3 * SEG) (2 * SEG)
                  (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + 2 * SEG) dcap DST (SS + O4 + p4) j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    BEF L1 p1 b1 -> 8 <= p1 -> BEF L2 p2 b2 -> BEF L3 p3 b3 -> BEF L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1)
                           (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) (Z_to_bv 64 3) x22 (Z_to_bv 64 c4)
                           (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           t3 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 0x17f1c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t3. intros LK XF Q0 QD B1 P8 B2 B3 B4 C1 C2 C3 C4. x4open XF.
    unfold BEF in B1. destruct B1 as (P10 & P1D & B1R & B1S).
    assert (P1H : p1 + 8 <= L1) by lia. assert (B56 : b1 <= 56) by lia. clear P1D B1S.
    xwalk [0x17fcc; 0x1806c] tl DT cells cbs ECB TCK OUT LB SRC.
    all: xrl (SP + -376) (SS + 6) p1 b1.
    all: first [ solve [eapply x4s1_r2; [exact LK | x4pack BDa | xside ..]]
               | solve [eapply x4s1_n2; [exact LK | x4pack BDa | xside ..]] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x4s1_n1 : forall q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 mm j0 j96 j120 jp1 jp2 jp3 jp4
                         (t2 x8 x9 a0 a2 x22 x27 : word),
    LOOPK' q ->
    X4F' mm (SPL3 (DST + 3 * SEG) (tl + 256 * mtl) (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (3 * SEG) (2 * SEG)
                  (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + 2 * SEG) dcap DST (SS + O4 + p4) j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    BEF L1 p1 b1 -> BEF L2 p2 b2 -> BEF L3 p3 b3 -> BEF L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1)
                           (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) (Z_to_bv 64 3) x22 (Z_to_bv 64 c4)
                           (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c1) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 0x18234) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until x27. intros LK XF Q0 QD B1 B2 B3 B4 C1 C2 C3 C4. x4open XF.
    xwalk [0x17fcc; 0x1806c] tl DT cells cbs ECB TCK OUT LB SRC.
    all: first [ solve [eapply x4s1_r2; [exact LK | x4pack BDa | xside ..]]
               | solve [eapply x4s1_n2; [exact LK | x4pack BDa | xside ..]] ].
  Qed.

  Lemma x4s1_d1_gen : X4D1.
  Proof using All.
    intros q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 mm j0 j96 j120 jp1 jp2 jp3 jp4 t2 x8 x9 a0 x27
           LK XF Q0 QD B1 B2 B3 B4 C1 C2 C3 C4.
    pose proof XF as XF0. x4open XF0.
    xwalk [0x17f1c; 0x18234] tl DT cells cbs ECB TCK OUT LB SRC.
    all: first [ solve [eapply x4s1_r1; [exact LK | exact XF | xside ..]]
               | solve [eapply x4s1_n1; [exact LK | exact XF | xside ..]] ].
  Qed.
  End X4S1B.

  (* [comment removed for export] *)
  Lemma x4s1_d1 : X4D1.
  Proof using All.
    exact (x4s1_d1_gen ((A1 x4s1_r3k) CHK) ((A1 x4s1_n3k) CHK)).
  Qed.
End X4S1.
End CANSEC1.
