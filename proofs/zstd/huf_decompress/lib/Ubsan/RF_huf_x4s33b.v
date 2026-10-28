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
  RF_huf_x4s RF_huf_y4s31_kit RF_huf_x4s31_kit RF_huf_y4_kit_reload RF_huf_x4s33.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s33b () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s4SPL3C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib4Init5Logic2eq01K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genK47Corelib4Init5Logic3and01I4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s338x33_tsetC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I47Corelib4Init5Logic2or00c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4s33b8x33_x890C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z3lorc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4s33b8x33_x47cC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s338x33_x404C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s338x33_x3f4C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz04K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4s33b8x33_elseC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4s338x33_loopC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>neg_desc_shiftC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section X4S33.
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
  Variables (O3 L3 Q3 q4 SEG Q2 v8 v16 v24 v32 v40 v48 v56 v80 v104 v128 : Z) (j0 j96 j120 : list byte)
            (bd1 bd2 bd4 : list cell).
  Hypothesis HL3 : 6 <= O3 /\ 1 <= L3 /\ O3 + L3 <= n.
  Hypothesis HQ3 : 0 < Q3 <= dcap.
  Notation SPL := (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) v80 (DST + Q2) v104 DST v128 j0 j96 j120).

  Notation ST pc mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x24 x26 t3 t4 t5 t6 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + q4)) x22 x23 x24 (Z_to_bv 64 (DT + 4))
             x26 (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Hypothesis CONT : forall mm c3 b3 p3 jp3 (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x24 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 bd2 (BD4 c3 b3 p3 (SS + O3) jp3) bd4 ->
    evt usegs POST (ST 104688 mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x24 x26 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Notation X33 l := (XB l O3 L3 Q3 q4 SEG Q2 v8 v16 v24 v32 v40 v48 v56 v80 v104 v128 j0 j96 j120 bd1 bd2 bd4
                       HL3 HQ3 CONT) (only parsing).

  (* [comment removed for export] *)
  Ltac x4open H :=
    destruct H as ((buf & OUT & LB) & SRC & CBS & STK & SPC & L0 & BDa & LBa & (jj & JJ) & BDd & LDd & BDc & LDc & BDb & LDb
                   & FR & MI & MU & WM);
    change (zlen buf) with (Z.of_nat (length buf)) in LB;
    pose proof TOK as (TL1 & TLN & TCK); cbv [HUF_TABLELOG_MAX] in TL1; cbv [FseNCount.Zlength] in TLN;
    pose proof (DP ltac:(lia)) as D8; pose proof (length_map (Z_to_bv 8) src) as LMS; unfold SPL3, BD4 in *;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  Ltac x4pack H := ubdnorm H; unfold X4F, SPL3, BD4; upack.

  Ltac xgen := repeat match goal with |- context [Z_to_bv 64 ?E] =>
    lazymatch E with context [Znth _ src] =>
      let w := fresh "w" in let EW := fresh "EW" in remember (Z_to_bv 64 E) as w eqn:EW; clear EW end end.
  Ltac xwalkg stops TCK OUT LB SRC := repeat (xwalk1 stops tl DT cells cbs ECB TCK OUT LB SRC; try xgen).
  Ltac xslia := repeat match goal with H : context [bv_signed (Z_to_bv 64 ?z)] |- _ => rewrite (signed_lit z) in H by lia end;
    lia.

  (* [comment removed for export] *)
  Lemma x33_rl : forall q pt c3 b3 jp3 mm (xra t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 bd2 (BD4 c3 b3 (SS + O3 + pt) (SS + O3) jp3) bd4 -> 0 <= q <= Q3 ->
    8 <= pt -> pt + 8 <= L3 -> 0 <= b3 <= 64 ->
    evt usegs POST (ST 104584 mm xra t0 t1 t2 x8 x9 (Z_to_bv 64 (SP + -184)) a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (DST + q)) x23 (Z_to_bv 64 (DST + Q3)) x26
                       t3 t4 t5 t6).
  Proof using All.
    intros until t6. intros XF QR P8 PL BR. x4open XF.
    zstep.
    eapply evt_cut;
    [ eapply y4_reload_proof with (BD := SP + -184) (S := SS + O3) (n := zlen src - O3) (c := c3) (bc := b3)
        (p := SS + O3 + pt) (pad := jp3) (sqb := skipn (Z.to_nat O3) (map (Z_to_bv 8) src));
      first [ assumption | unfold y4_bd; assumption | apply u_bytes_skipn; [rewrite length_map; lia | assumption]
            | rewrite length_skipn, length_map; lia | lia ]
    | post_call usegs mm; lazymatch goal with H : rw_cells _ _ (SP + -184) _ |- _ => unfold y4_bd in H; rename H into BDc end ].
    xwalkg [104612; 104688] TCK OUT LB SRC.
    all: first [ solve [eapply CONT; x4pack BDc] | solve [eapply (X33 x33_tail (Z.to_nat Q3) q); [x4pack BDc | xslia ..]] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x33_entry : forall q3 pt3 c3 b3 jp3 mm (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 bd2 (BD4 c3 b3 (SS + O3 + pt3) (SS + O3) jp3) bd4 ->
    0 <= q3 <= Q3 -> 0 <= pt3 -> (pt3 = 0 \/ pt3 + 8 <= L3) -> 0 <= b3 < 2^31 ->
    evt usegs POST (ST 103732 mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (DST + q3)) x23
                       (Z_to_bv 64 (DST + Q3)) x26 t3 t4 t5 t6).
  Proof using All.
    intros until t6. intros XF QR P0 PL BR. x4open XF.
    zstep. xwalkg [103792; 104584; 104612; 104688] TCK OUT LB SRC.
    all: first [ solve [eapply CONT; x4pack BDc]
               | solve [eapply (X33 x33_tail (Z.to_nat Q3) q3); [x4pack BDc | xslia ..]]
               | solve [eapply (x33_rl q3 pt3); [x4pack BDc | xslia ..]]
               | solve [eapply (X33 x33_loop (Z.to_nat Q3) q3 (SS + O3 + pt3)); [xslia | xslia | xslia | unfold PINV; lia | xslia | xslia | xslia
                                                              | x4pack BDc]] ].
  Qed.

End X4S33.
End CANSEC1.
