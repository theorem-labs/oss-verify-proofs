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
  RF_huf_y4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4s1 () := "c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s15Y1AFTK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s15Y1HDIK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission3Lib8PropExecDbytes_le_to_Z_nonnegC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C45stdpp9bitvector;definitions@Z_to_bv_unsignedC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib5Bytes?lor_shiftl8_addC47Corelib4Init9Datatypes8list_indK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega3Op205I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExecCbytes_le_to_Z_boundC56Stdlib6ZArith6BinInt1Z6of_natc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s1Ey4_Z_to_le_bytes_to_ZC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions=bv_wrap_smallC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init9Datatypes6option00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv3Sem5low32K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib3Tac>rw_cells_mergeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s1?y4_le8_of_bytesC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_recastC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s4SPLYC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s38y4s3_allC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib7Numbers7BinNums1N01c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s13HQ3c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s17Y1LOOPKc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s15Y1OPSK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_gec5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s19y4s1_exitC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s1:y1_aft_hdiC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s15Y1BEFC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4onesc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s19y4s1_backC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteK4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s17y4s1_r4K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s17y4s1_c4K4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s17y4s1_n3c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s17y4s1_r3".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Definition Y1BEF (L p bits : Z) : Prop := 0 <= p /\ (p = 0 \/ p + 8 <= L) /\ 0 <= bits <= 112 /\ (8 <= p -> bits <= 56).
Definition Y1AFT (L p bits st : Z) : Prop := 0 <= p /\ (p = 0 \/ p + 8 <= L) /\ 0 <= bits <= 112 /\ ((st = 0 /\ bits <= 7) \/ st = 3).
Definition Y1HDI (L p bits : Z) : Prop := 0 <= p /\ (p = 0 \/ p + 8 <= L) /\ 0 <= bits <= 64 /\ (8 <= p -> bits <= 8).

Lemma y1_aft_hdi : forall L p bits, Y1AFT L p bits 0 -> Y1HDI L p bits.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s1 ()) [] "p'0h04__x1h11Hh27__arithh34__ffh48__varmaph55__with64__p1h74__x2h82B7h92BBh:1Eh;1Lh<2P0h=2PNh>2_Hh?4bitsh@1ehA1pi001zp;4p;1p;2p;3p;7p;6p;8g0000j4XTg000lj15Tg001Qj1<Tg001oj29Tg002Lj20Tg002hR0j22Tg003Bj1ATg003gj3=Tg004AR1j23Tg004\j3:Tg005Xj1WTg0068j1UTg006Xj2CTg0076j1RTg007Tj1QTg008?j2>Tg008bj2BTg009Ej1OTg009gj2NTg00:Ij2MTg00:cj2LTg00;Oj3KTg00;nj4HTg00<`j1ITg00=>j4JTg00=\j4@Tg00>Gj3GTg00>jj7FTg00?Nj6ETg00@2j7PTg00@Vj4?Tg00A1j6DTg00AMj2STg00Alj7TTg00BPj8VTg00C4R2f0R3'0p=4g00CRR4?=32p=6f2R5f1R6/03'3p=1P4P6g00D0P3C@p=;P6g00DWR7g00E6R8P8g00EVR9P3g00F6FTp=7f3R:P7P8P8P9P5P6P3GVp=8P5P6P3P2CXP1%45%65g00FVR;#5R<#5#5R=#<R>,95/0:'2R?%46R@%A;RA#ARB#5#5#5#5#<RC716A=422RD%<BRB716%<ARA9=42RE'2'3'3f4RF?::5P3%4FRGf5RH#619H>f6RI'0'2A1GFCA1DFB/2E'3'3P1%6I19I>f7RF'0'2%4H?1HCA1DHB/2E'3f8RH?:FIP3%6H19H>f9RF'0'2%4H?1HCA1DHB/2E'3P1%4F?1FCA1DFB/2Ef<RFf;RIf:3:P3%4I?1ICA1DFB/2EP0f==1DBPEf@R0f?RIf>RG3:P3A1DGBP1PD10IBfBRIfA;:0R1P310IBfDRI#4%6I19I>fERG'0'2RJfCRK#4RL%5=#5#5#<R=,0KRM'3RN10>IRO10I>[RP'3RQ'3g00G;RR#WRS%URRR1C46RT%R4RU%Q4RV1>42RW1B4;R;';,7VRX%O8RYPXC81NV9RZP3P5g00GgR[g00HGR\'M1L35==[\dAK426CHR\b3b4b5X04%43R[P@[^04P3PGP0O2b2PJPQPSPRP41C45P6%I4CJPUPVPVP7P8P8P9P4P;g00HgPWC@,7V1>4>RW9G4;1B4<';,7VFFR<PYPVPXPYP<C8C8PZP\b3b4b5X04X74%63193>/06'2P?\@[^04^74P3fFPGPFP0O4b2PNPPPLPMp-0RMPSPRPTPUPVPVP7P8P8P9PXPVP7P8P8P9P:EEFPPYPXC8PZP\b3b4b5X04W613[6P@[^04^6MP310ICPIPHO3b2PSPRPTPUPV1>4B,;;,7VRHPY1>4=,;;,7VC8PZP\b3b4b5X04103BRB106=[^04P3PIP6O2b2C?PSPRPTPUPVPHPY1;;W,7VC8PZP\b3b4b5X04106>\B^04P3PGP5O2b2VOC?C?C?A:GIKeW8X>DP6P3O2n2001000000121000000W1P3O1P4P2P4PMP3g00INg00IjRMPMn011000003001000010000X@4g00JGPAP3EDPM1S13b1X:EP3O1n200100000021100010000W1W9P6P3O2n2001000000121000000W1W=P6P3O2n2001000000121000000W1W<P6P3O2n2001000000121000000W1X?4XA4X;4o"). Qed.

(* [comment removed for export] *)
Definition Y1OPS (SEG q1 q2 q3 q4 : Z) : Prop :=
  0 <= q1 /\ q1 <= 2 * (q4 - 3 * SEG) /\ SEG <= q2 /\ q2 - SEG <= 2 * (q4 - 3 * SEG) /\
  2 * SEG <= q3 /\ q3 - 2 * SEG <= 2 * (q4 - 3 * SEG) /\ 3 * SEG <= q4.
Definition Y1MID (L p bits : Z) : Prop := 0 <= p /\ (p = 0 \/ p + 8 <= L) /\ 0 <= bits <= 88 /\ (8 <= p -> bits <= 32).

(* [comment removed for export] *)
Lemma y4_Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s1 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51Hh62H0h74__x2h84__x3h94__x4h:1zh;2bsh<2H1h=2H2h>2H3h?2b1h@2b2hA1nhB1qhC1rhD2HRhE2HbhF2IHhG1bp&0p;1p;2p;3p;4p;6p;8p;5p;7p100Jcp4p7210g00KOR0p4p710p8g000lj1;Tg00Kmk108Tg00LKj1ATg0068j1]Tg00Lnj2FTg00MNj13Tg00NKj2@Tg003gj35Tg005Xj1\Tg00:Ij2NTg00OHj2fTg00P;j20Tg00Pek107Tg00QNj24Tg004AR1j29Tg00Qjk100Tg001Qj1UTg00S0j2QTg00SVj2_Tg00T6j3=j2^j1pTg00TVj3mTg00U:j2kTg00U`j2bTg00VAj1gTg00VZj2>Tg00W7j2CTg00WTj2<Tg001oj2DTg00X4j2[Tg00X[j2ZTg002Lj2OTg00YBj2YTg00Yhj2XTg00ZNj2eTg00Zok106Tg00[Mk205Tg00[nj1BTg00\Mj3dTg00]6j2cTg00]_k203Tg00^Hk302Tg00_1j2LTg00_]j2TTg006Xj2STg00<`j1~Tg00=>j4aTg0076j1}Tg007Tj1wTg008?j2RTg008bj2GTg009Ej1vTg00`Ij6uTg003Bj1tTg00`mj3JTg00>Gj3MTg009gj2qTg00:cj2oTg00;Oj3rTg00;nj4sTg00aPj2nTP0j6PTg00b?j8`Tg00b\j2lTg00A1j6xTg00c9j3yTg00cbj2zTg00dBj2{Tg00d_j4|Tg00e]j5jTg00f?k301Tg00=\j4VTg00Alj7iTg00@2j7hTg00BPk804Tg00C4R0f0R2'Op=:f2R3f1R4/C2'Dp=7g00CRR5?542p=6A5520p=W1c52p=?B01542p=1P5P4g00D0P2CVp=EP4g00DWR6g00E6R7P7g00EVR8P2g00F6Fip=2P5P4g00fhP2CVp=HP3P6P7P7P8P4P2Fhp=KP5P4g00HgP2CVp=If3R9P6P7P7P8P3P4P2L04p=8g00FVR:#;R;#;R<#;R=$08R>#AR?#]R@P?1F?2%32'@=5@2RAX;@%\?,N@1f>310>3RB#:&07>,4B'9&003%33#:P5f4RB,0>RC%;=#;#;#;#;#URD%39RE37RF1Q>21F?BRG%U=R=,_2'@5=?f5RH==?B55@X:5P@P@1Q>FRI,^?1^?B1F?91_F=RJ'@P9P?P@\@RK%p?RLPLPIPBPK\?/NLg00gORL%A2RK%A4RIP1%A3?54210931094'6R1[10341032'6%A9?534[RM%AB?593\1Am342P2n2001000000120000000W@W?WAPM^@I^?K^ALP2P>10>HRL%3BRK77DRI,Q>RMPHP51k>If6R1,0>RN,62X:51bID%WDRO#gRP%3H97NDRN1>ND,CD1<NDRQ'D'6[1[ND140DRRf7RS,0>%3177DR1/<DRT#:14TD'9[1Z1D14D0RUf8RV,0>%3S77DRS/<DRW,4D1OW0'9[1YSDf9RW,0>%3V77DRX/>DRY#W\O1XXDf:RZ,0>%3W77DRW/<DR[/6W\O1>WDP5f;RW,0>%3Z77D/<DP5PHg00gm1e0D'NPReO1R\%:2R]142D'9R^g00G;R_&06:-055R`g00hSRa#BRb#BRc#BRd#?Re5d5Rf1c5aRa'12035D>025aRg%BdRd#BRh#?Ri%?dRd/1e'1'1g00i2Rj'L'T11ea%Bh#?Ad5`d%?cRc'1'1,1g/Lj'T%\_R`5=_3=%]_RhP5P51S5BP3%~5RkCaP41S59CaRl%}5Rm%w5Rn1R50Ro1G5:Rp'E,2nRq1R5DRr,Hp,2n5KnRs%v7RtPnPnPnP6P7P7P81Iro,2nEuR7Pt1G5;R6%t:,G5R:9J5r5M51G5<R<9J5r=M5p'I,2nC8PtPn1Eo6,2n1H6r,2n5KnPt1Ip6,2nRuC8C8C81qn8R8P2P3g00GgRvg00HGRw'N1o23=5vwdAr504CsRwb2b3b4X05X75X85X95g00Ij\ORvA79DB1CDH/D3'6[%:9149D'9Rx169BRy[[\^^05^75^85^95P2P9f=Rz#3f>,0>P3P4PVPWO7b1b6bCbBb>b=b<b6b510>M1n>IEPO4b5G`P5%U;/l=,>F1@G2=5@BX:51bFD1>IDRG,CD1<ID'D,6I\P1[ID%:Q14QD'9\R1ZND14DT1OT0'9\U1Y1D1>SD#W\O1XSD1<XD/6X\OPYP5P[P5P\P^11cg,1e,1d/Lj%?bRb,1f,1i11ab/Lj'T==_`5=_PhPlPmPn1Eo<,2n1H<r,2n5KnPtPnPnP7PtAJ5rp9M5:AJ5r6=M5<'I,2nC8PtPn1Eo:,2n1H:r,2n5KnPtPuC8C8C8P8Pwb2b3b4X05X75X85X95A7BD31CD9/DH'6\v%:B14BD'9Py[[\x^05^75^85^95P2P310>zP9f<#3P4PVPZO7b1b6bCbBb>b=b<b6b51>FD,6EP5PK1F?H/@2=5@HX:5P9PGP2Exb5PJP`PhPkPm1R5=,Eo,2nP8Pwb2b3b4%:=P2b19yF=EPG`1zE=,{CPCPEP`Ph1S54REPmPnPsPtPsC8P8Pwb2b3b4X05%:4Rs144D'9\^^05P2PLP3O2b1P`PhPEPmPnPqPtPqC8P8Pwb2b3b4X05Ps\]^05P2PKP4O2b1C|EPbDbEA=?34R4,F?%34'@=5@4eXFAX;@XG?P2DjW;o"). Qed.

Lemma y4_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s1 ()) [] "h01xh11nh22HRh34__x1h41yh52H0h62HLh73HL0h87__arithh94__ffh:8__varmaph;5__with<2bsh=4cstrh>1mh?1zp;1p;2p;3p;6p;4p;<p;7p;Bp;8g000lj15Tg00Kmj1ATg00LKj1YTg0068j1?Tg00Lnj29Tg00[nj12Tg003gj30j1>Tg00i^j1XTg00MNj17Tg001Qj1;Tg00jcR0j16Tg00W7j2<Tg00b\R1j24Tg00QNR2j21Tg00Qjj1oTg002Lj28Tg00A1j6DTg00U:j2_Tg00NKj2GTg00kCj1]Tg00lOR3j1CTg004Aj2:Tg00:Ij2=Tg00lmj3WTg00mSj1VTg00n1j4UTg00nTl<@Tg00o9j6NTg00obj2MTg010Ej3LTg010bj4KTg011Ij1PTg005Xj1QTg006Xj2JTg0076j1RTg007Tj1STg008?j2ITg008bj2pTg00=\j4HTg009Ej1nTg011nj3mTg00@2j7lTg009gj2kTg00:cj2eTg00;Oj3dTg00;nj4cTg012Qj4`Tg00Pej1aTg013<j3bTg00KOj6BTg00S0j2^Tg00P;j2fTg00aPj2\Tg013hj1gTg014hj1hTg015Xl<[Tg016=lBiTg00Alj7jTg00BPj8ZTg00CRR4f0R5'=p=3g00gOR6P4P4P4P3P3f5R3f4R7f3R8f2R9f1R:P5M<[p=TP4P4P4P4P4P4P1P5P:P9P1P8P7P3f6f7R1f8f9MBip=OP:g00DWR;g00E6R<P<g00EVR=P5g00F6Fjp=FP8P;P<P<P=P9P:P5GZp=Eg00FVR>#5R?#5#5R@#A#YRA#?RBg016cRC19A5g00hS#2#2#2#2#2#2#2#2RD30%X:%7:%;?R?%;@RE19A:#6'<'4'1%o9g00C4RF%79'8PC19A8%77RG%65RH,<E,4?'1X1CP:PDP9ED%78%6D,<E,4?'1P4%5@#5#5R@#ARI/_GRJ1GD5=0B3X?4RKP4PGPKPC19A7RK%73,G5=0B3X1C%]7PDP8EDPJ18FGRJ%CIRL,4?RM,1GRN':%;@R@,4?RO,1GRP,:JPJPNPJPPp-0/=J9WJJP4P4P2P5X04RPP211:5#VX44X04PGPG%3GPMPOPPPPPPP4P4g017B14:5CU#3X>4X14P?P?%3?PLP@PPPP%C5#3X06PIP@%3@ETM:OM<@ENA0CKD%6KR@=04ER6PCP4%>CP0%>4%6:=04HA0C:51M:53LX4CX0CPKP@%3@PDPE%3EM<@P8CKP619A3RA#P%6A,8Fg00G;RA#Q%?A1J4:%R4%S4RAP41I4Fg00D01p4>R>CH,FAR3%n<R6PAP4P>g00fh1I4?=m4ICH,FAR?P6PAP;P<P<P=P3P?FlCECE1kA=P5P9g00GgRAg00HGR='=1e59=0A=dAd4F:Ccb9b:b;X3418F511:O18F9119O':[[^34P5%71P7P8O3b8b=b7C`%aI,1G,:Je9bIGEB1^IG,fI1\IGEBb2b5b2%g:#h=0B:eW6W<o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Y4S1.
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

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation Y4F' mm spl b4 b3 b2 b1 :=
    (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).

  Variables (L1 L2 L3 L4 SEG : Z).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Hypothesis HL : 1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n.
  Hypothesis HQ : 0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG.
  Hypothesis HQ2 : 2 <= SEG.
  Notation desc := (tl + 256 * mtl).
  Lemma HQ3 : 0 < SEG <= 2 * SEG /\ 2 * SEG <= 3 * SEG /\ 3 * SEG <= dcap.
  Proof using All. destruct HQ as (? & ? & ?). lia. Qed.

  (* [comment removed for export] *)
  Notation SPLL w64 k4 k2 p2 k1 j0 :=
    (SPLB desc (DST + 3 * SEG) dcap (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (DST + dcap - 7) w64 k4 k2
          (SS + O2 + p2) (DST + SEG) (DST + 2 * SEG) k1 (DST + dcap) (DT + 4) j0).
  Notation SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0 :=
    (SPLB desc (DST + 3 * SEG) v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88
          (DST + SEG) (DST + 2 * SEG) v112 (DST + dcap) (DT + 4) j0).
  Notation BDS c b p O jp := (BD4 c b (SS + O + p) (SS + O) jp).

  (* [comment removed for export] *)
  Definition Y1HEAD (Q0 : Z) : Prop :=
    forall q1 q2 q3 q4 b1 b2 b3 b4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4
           (xt2 xs0 xa0 xa2 xa3 xa4 xs5 xs6 xs8 xs10 xt5 : word),
    Q0 < q4 ->
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

  (* [comment removed for export] *)
  Definition Y1EXIT : Prop :=
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
  Definition Y1REL (Q0 : Z) : Prop :=
    forall o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4
           (xt2 xs0 xa4 xs5 xs8 xs10 xt5 : word),
    Q0 < o4 + l4 - DST ->
    Y4F' mm (SPLL w64 c4 c2 p2 c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    Y1BEF L1 p1 b1 -> Y1BEF L2 p2 b2 -> Y1BEF L3 p3 b3 -> Y1BEF L4 p4 b4 ->
    1 <= l1 <= 2 -> 1 <= l2 <= 2 -> 1 <= l3 <= 2 -> 1 <= l4 <= 2 ->
    DST <= o1 -> DST <= o2 -> DST <= o3 -> DST <= o4 ->
    Y1OPS SEG (o1 + l1 - DST) (o2 + l2 - DST) (o3 + l3 - DST) (o4 + l4 - DST) -> o4 + l4 <= DST + dcap ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 -> 0 <= w64 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            xt2 xs0 (Z_to_bv 64 b1) (Z_to_bv 64 l1) (Z_to_bv 64 o1) (Z_to_bv 64 l2) (Z_to_bv 64 l3) xa4
                            (Z_to_bv 64 (2^61)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 o4) (Z_to_bv 64 c3)
                            (Z_to_bv 64 o3) xs5 (Z_to_bv 64 l4) (Z_to_bv 64 b3) xs8 (Z_to_bv 64 b4) xs10 (Z_to_bv 64 o2)
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 0x1b07c) fc None mm (seg_rom usegs)).

  Definition Y1R2 (Q0 : Z) : Prop :=
    forall r1 r2 r3 r4 l1 l2 l3 l4 b1 b2 b3 b4 bb1 bb2 bb3 bb4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4
           (xra xt2 xa0 xs7 xs8 : word),
    Q0 < r4 + l4 - DST ->
    Y4F' mm (SPLL w64 c4 c2 p2 c1 j0) (BDS c4 bb4 p4 O4 jp4) (BDS c3 bb3 p3 O3 jp3) (BDS c2 bb2 p2 O2 jp2) (BDS c1 bb1 p1 6 jp1) ->
    Y1MID L1 p1 b1 -> Y1MID L2 p2 b2 -> Y1MID L3 p3 b3 -> Y1MID L4 p4 b4 ->
    1 <= l1 <= 2 -> 1 <= l2 <= 2 -> 1 <= l3 <= 2 -> 1 <= l4 <= 2 ->
    DST <= r1 -> DST <= r2 -> DST <= r3 -> DST <= r4 ->
    Y1OPS SEG (r1 + l1 - DST) (r2 + l2 - DST) (r3 + l3 - DST) (r4 + l4 - DST) -> r4 + l4 + 4 <= DST + dcap ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 -> 0 <= w64 < 2^64 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            xt2 (Z_to_bv 64 l4) (Z_to_bv 64 l1) xa0 (Z_to_bv 64 r1) (Z_to_bv 64 b1) (Z_to_bv 64 b2) (Z_to_bv 64 b3)
                            (Z_to_bv 64 (2^61)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 r4) (Z_to_bv 64 c3)
                            (Z_to_bv 64 r3) (Z_to_bv 64 l2) (Z_to_bv 64 l3) xs7 xs8 (Z_to_bv 64 b4) (Z_to_bv 64 c4) (Z_to_bv 64 r2)
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c2) (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 0x1adb4) fc None mm (seg_rom usegs)).

  Lemma y1ops_step : forall q1 q2 q3 q4 d1 d2 d3 d4,
    Y1OPS SEG q1 q2 q3 q4 -> 0 <= d1 <= 2 * d4 -> 0 <= d2 <= 2 * d4 -> 0 <= d3 <= 2 * d4 -> 0 <= d4 ->
    Y1OPS SEG (q1 + d1) (q2 + d2) (q3 + d3) (q4 + d4).
  Proof using All. unfold Y1OPS. intros. lia. Qed.

  Lemma y1ops_le : forall q1 q2 q3 q4, Y1OPS SEG q1 q2 q3 q4 -> q4 <= dcap ->
    0 <= q1 <= dcap /\ 0 <= q2 <= dcap /\ 0 <= q3 <= dcap /\ 0 <= q4.
  Proof using All. unfold Y1OPS. destruct HQ as (? & ? & ?). intros. lia. Qed.

End Y4S1.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
