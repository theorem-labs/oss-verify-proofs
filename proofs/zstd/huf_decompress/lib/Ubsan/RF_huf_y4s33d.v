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
  RF_huf_y4s RF_huf_y4s_iface RF_huf_y4_kit_reload RF_huf_y4s31_kit RF_huf_y4s33_kit
  RF_huf_y4s33 RF_huf_y4s33b RF_huf_y4s33c.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4s33d () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s4SPLYC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr02C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s338y33_c60cC56Stdlib6ZArith6BinInt1Z6ltb_geC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C45stdpp9bitvector;definitions7bv_wrapK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC45stdpp9bitvector;definitions8bv_swrapC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3lorK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s339y33_closeC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC46Stdlib4Bool4Bool>negb_false_iffC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s338y33_c5e4C56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr03C56Stdlib6ZArith6BinInt1Z:mul_div_leK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvI47Corelib4Init5Logic2or00C47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4s33d8y33_elseK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4s33c9y33_loop4C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>neg_desc_shiftC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4s33b9y33_loop5C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z8inj_succC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_default".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section Y4S33D.
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
  Variables (O3 L3 Q3 q4 v8 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 : Z) (j0 jp : list byte) (b4 b2 b1 : list cell).
  Hypothesis HL3 : 6 <= O3 /\ 1 <= L3 /\ O3 + L3 <= n.
  Hypothesis HQ3 : 0 < Q3 <= dcap.
  Hypothesis HQ4 : 0 <= q4 <= dcap.
  Notation desc := (tl + 256 * mtl).
  Notation SPL := (SPLB v8 (DST + Q3) v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88 v96 v104 tl (DST + dcap) (DT + 4) j0).
  Notation F3 mm c bc ptr := (Y4F' mm SPL b4 (BD4 c bc ptr (SS + O3) jp) b2 b1).
  Notation PTI ptr := (exists pt, ptr = SS + O3 + pt /\ 0 <= pt /\ (pt = 0 \/ pt + 8 <= L3)).

  Notation CS pc mm q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -912)) gp tp x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DST + q4)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DST + Q3))
             x22 x23 x24 (Z_to_bv 64 desc) (Z_to_bv 64 dcap) (Z_to_bv 64 tl) x28 x29 x30 (Z_to_bv 64 (DST + dcap)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation T4S mm x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -912)) gp tp x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DST + q4)) (Z_to_bv 64 (2^61)) x20 x21 x22 x23 x24 (Z_to_bv 64 desc) (Z_to_bv 64 dcap)
             (Z_to_bv 64 tl) x28 x29 x30 (Z_to_bv 64 (DST + dcap)))
        F (Z_to_bv 64 S4_ENTRY) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Hypothesis CONT : forall mm c bc ptr (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 : word),
    F3 mm c bc ptr ->
    evt usegs POST (T4S mm x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30).

  (* [comment removed for export] *)
  Notation ES pc mm q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -912)) gp tp x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DST + q4)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DST + Q3)) x22 x23 x24 (Z_to_bv 64 desc)
             (Z_to_bv 64 dcap) x27 x28 x29 x30 (Z_to_bv 64 (DST + dcap)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac ss := k3_step DST dcap SS src DT cells cbs tl ECB.
  Ltac srunL L := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        let b := eval vm_compute in (existsb (Z.eqb pc) L) in
        lazymatch b with true => fail | false => ss end
    | _ => ss end).
  Ltac opn INV :=
    destruct TOK as (TL & TLN & TCK); unfold FseNCount.Zlength in TLN; unfold HUF_TABLELOG_MAX in TL;
    assert (P12 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia);
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    destruct INV as ((buf & ARR & LB) & SRC & CE & STK & SPLc & SPLs & B4c & B4s & B3c & B3s & B2c & B2s & B1c & B1s
                     & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SAV) & (jl & JL) & FR & MI & MU & WM);
    unfold SPLB in SPLc; unfold BD4 in B3c;
    assert (LBm : Z.of_nat (length (map (Z_to_bv 8) buf)) = dcap) by (rewrite length_map; exact LB).
  Ltac fixq :=
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let r := getreg 20 in
      lazymatch r with Z_to_bv 64 ?E =>
        lazymatch E with
        | DST + ?q => idtac
        | _ => replace E with (DST + (E - DST)) by lia
        end end end.
  Ltac pack3 :=
    try (match goal with H : rw_cells _ _ (SP + -736) _ |- _ => ubdnorm H end);
    unfold Y4F, SPLB, BD4;
    lazymatch goal with ARRx : u8arr usegs ?m DST (map (Z_to_bv 8) ?b), LBx : Z.of_nat (length ?b) = dcap |- _ =>
      split; [exists b; split; [exact ARRx | exact LBx]|] end;
    repeat (split; [first [eassumption | reflexivity | do 12 eexists; eassumption | eexists; eassumption]|]); eassumption.
  Ltac pti_tac :=
    lazymatch goal with |- exists pt, ?P = _ /\ _ =>
      exists (P - (SS + O3)); split; [lia | split; [lia | first [left; lia | right; lia]]] end.
  Ltac rcall :=
    k3_at [PHUF_RELOAD]; pose proof (length_map (Z_to_bv 8) src) as LMS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [ eapply (y4_reload_proof) with (S := SS + O3) (n := L3)
                          (sqb := map (Z_to_bv 8) (firstn (Z.to_nat L3) (skipn (Z.to_nat O3) src))) | post_call usegs m ] end;
    [ assumption | first [eassumption | unfold y4_bd; eassumption] | lia | apply k3_bytes_at_sub; [eassumption | lia | lia | lia]
    | rewrite length_map, length_firstn, length_skipn; lia | lia | lia | lia | lia | lia | lia | lia | lia | ];
    unfold y4_bd in *.

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

  Notation Y33 l := (YB l O3 L3 Q3 q4 v8 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 j0 jp b4 b2 b1 HL3 HQ3 HQ4) (only parsing).

  (* [comment removed for export] *)
  Lemma y33_else : forall mm c bc pt q (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30 : word),
    F3 mm c bc (SS + O3 + pt) -> 0 <= q <= Q3 -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L3) -> 0 <= bc < 2^31 ->
    evt usegs POST (ES S3_ELSE mm q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30).
Proof using All.
    intros mm c bc pt q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30 INV Q0 PT0 PTL B0.
    opn INV.
    Time srunL [PHUF_RELOAD; S3_L2RP; S3_LAST].
    all: k3_nrm.
    all: try (rcall; ss; srunL [S3_L2RP; S3_LAST]; k3_nrm).
    all: fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S3_L2RP) _ _ _ _) =>
             eapply (Y33 y33_cd10 CONT); [pack3 | lia | lia | lia | intros; first [pti_tac | exfalso; lia]]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S3_LAST) _ _ _ _) => eapply (Y33 y33_last CONT); [pack3 | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma y33_entry : forall mm c bc pt q (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x27 x28 x29 x30 : word),
    F3 mm c bc (SS + O3 + pt) -> 0 <= q <= Q3 -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L3) -> 0 <= bc < 2^31 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -912)) gp tp x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 (DST + q4)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + q)) x21 x22 x23 x24 (Z_to_bv 64 desc)
                            (Z_to_bv 64 dcap) x27 x28 x29 x30 (Z_to_bv 64 (DST + dcap)))
                       F (Z_to_bv 64 S3_ENTRY) fc None mm (seg_rom usegs)).
Proof using All.
    intros mm c bc pt q x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x27 x28 x29 x30 INV Q0 PT0 PTL B0.
    opn INV.
    Time srunL [S3_ELSE; S3_L4H; S3_L5H; S3_L2RP; S3_LAST].
    all: k3_nrm; fixq.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S3_ELSE) _ _ _ _) => eapply y33_else; [pack3 | lia | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S3_L5H) _ _ _ _) =>
             eapply (Y33 y33_loop5 (Y33 y33_cd10 CONT) (Y33 y33_last CONT) (S (Z.to_nat (Q3 - q))));
               [pack3 | exists pt; split; [reflexivity | split; [exact PT0 | exact PTL]] | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S3_L4H) _ _ _ _) =>
             eapply (Y33 y33_loop4 (Y33 y33_cd10 CONT) (Y33 y33_last CONT) (S (Z.to_nat (Q3 - q))));
               [pack3 | exists pt; split; [reflexivity | split; [exact PT0 | exact PTL]] | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S3_L2RP) _ _ _ _) =>
             eapply (Y33 y33_cd10 CONT); [pack3 | lia | lia | lia | intros; first [pti_tac | exfalso; lia]]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 S3_LAST) _ _ _ _) => eapply (Y33 y33_last CONT); [pack3 | lia]
         end.
  Qed.

End Y4S33D.
End CANSEC1.
