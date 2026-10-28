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
  RF_huf_x4s RF_huf_x4s31_kit RF_huf_y4_kit_reload RF_huf_y4s31_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s1 () := "c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s13AFTK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s13HDIK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr07C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List:length_mapK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C4ELinuxProcessSemantics5Riscv3Sem5low32K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s2<spl1_to_spl3C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s4SPL3K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s28x4s2_chkC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize03c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s14HQ23c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s15LOOPKC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_gec5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s19x4s1_exitC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s17aft_hdiC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s13BEFC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4onesc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s19x4s1_backC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s17x4s1_r4K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Definition BEF (L p bits : Z) : Prop := 0 <= p /\ (p = 0 \/ p + 8 <= L) /\ 0 <= bits <= 112 /\ (8 <= p -> bits <= 56).
(* [comment removed for export] *)
Definition AFT (L p bits st : Z) : Prop := 0 <= p /\ (p = 0 \/ p + 8 <= L) /\ 0 <= bits <= 112 /\ ((st = 0 /\ bits <= 7) \/ st = 3).
(* [comment removed for export] *)
Definition HDI (L p bits : Z) : Prop := 0 <= p /\ (p = 0 \/ p + 8 <= L) /\ 0 <= bits <= 64 /\ (8 <= p -> bits <= 8).

Lemma aft_hdi : forall L p bits, AFT L p bits 0 -> HDI L p bits.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4s1 ()) [] "p'0h04__x1h11Hh27__arithh34__ffh48__varmaph55__with64__p1h74__x2h81Bh92B7h:1Eh;1Lh<2P0h=2PNh>2_Hh?4bitsh@1ehA1pi001zp;4p;1p;2p;3p;7p;6p;8g0000j4XTg000jj15Tg001Oj1<Tg001mj29Tg002Jj20Tg002fR0j22Tg003@j1ATg003ej3=Tg004?R1j23Tg004Zj3;Tg005Tj1WTg0064j1UTg006Tj2CTg0072j1RTg007Pj1QTg008;j2>Tg008^j2BTg009Aj1OTg009cj2NTg00:Ej2MTg00:_j2LTg00;Kj3KTg00;jj4HTg00<\j1ITg00=:j4JTg00=Xj4@Tg00>Cj3GTg00>fj7FTg00?Jj6ETg00?nj7PTg00@Rj4?Tg00@mj6DTg00AIj2STg00Ahj7TTg00BLj8VTg00C0R2f0R3'0p=4g00CNR4?=32p=6f2R5f1R6/03'3p=1P4P6g00ClP3C@p=:P6g00DSR7g00E2R8P8g00ERR9P3g00F2FTp=7f3R:P7P8P8P9P5P6P3GVp=8P5P6P3P2CXP1%45%65g00FRR;#5R<#5#5R=#<R>,95/0:'2R?%46R@%A;RA#ARB#5#5#5#5#<RC716A=422RD%<BRB716%<ARA9=42RE'2'3'3f4RF?;:5P3%4FRGf5RH#619H>f6RI'0'2A1GFCA1DFB/2E'3'3P1%6I19I>f7RF'0'2%4H?1HCA1DHB/2E'3f8RH?;FIP3%6H19H>f9RF'0'2%4H?1HCA1DHB/2E'3P1%4F?1FCA1DFB/2Ef<RFf;RIf:3;P3%4I?1ICA1DFB/2EP0f==1DBPEf@R0f?RIf>RG3;P3A1DGBP1PD10IBfBRIfA;;0R1P310IBfDRI#4%6I19I>fERG'0'2RJfCRK#4RL%5=#5#5#<R=,0KRK'3RM10>IRN10I>[RO'3RP'3g00G7RQ#WRR%UQRQ1C46RS%R4RT%Q4RU1>42RV1B4;R;':,7URW%O8RXPWC81NU9RYP3P5g00GcRZg00HCR['M1L35==Z[dAK426CHR[b3b4b5X04%43RZP@[^04P3PGP0O2b2PJPPPRPQP41C45P6%I4CJPTPUPUP7P8P8P9P4P;g00HcPVC@,7U1>4>RV9G4;1B4<':,7UFFR<PXPUPWPXP<C8C8PYP[b3b4b5X04X74%63193>/06'2P?\@[^04^74P3fFPGPFP0O4b2PMPOPLPKp-0RKPRPQPSPTPUPUP7P8P8P9PWPUP7P8P8P9P:EEFPPXPWC8PYP[b3b4b5X04W613Z6P@[^04^6KP310ICPIPHO3b2PRPQPSPTPU1>4B,:;,7URHPX1>4=,:;,7UC8PYP[b3b4b5X04103BRB106=[^04P3PIP6O2b2C?PRPQPSPTPUPHPX1:;V,7UC8PYP[b3b4b5X04106>\B^04P3PGP5O2b2VNC?C?C?W9X>DP6P3O2n2001000000121000000W1P3O1P4P2P4PKP3g00IJg00IfRKPKn011000003001000010000X@4g00JCPAP3EDPK1S13b1X:EP3O1n200100000021100010000W1W8P6P3O2n2001000000121000000W1W=P6P3O2n2001000000121000000W1W<P6P3O2n2001000000121000000W1X?4XA4X;4o"). Qed.

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
  Lemma HQ23 : 0 < SEG <= 2 * SEG /\ 2 * SEG <= 3 * SEG /\ 3 * SEG <= dcap /\ 4 <= dcap.
Proof using HQ.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4s1 ()) ["CANSEC1"; "X4S1"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__witp;1p;2p;4p;3p;8p;7g005Tj1NTg0064j1MTg006Tj2ATg00<\j1>Tg00=:j4LTg0072j1JTg007Pj1GTg008;j25Tg008^j29Tg00=Xj4;Tg003@j1=Tg001Oj16Tg00J_j3<Tg000jj18Tg009Aj1ITg00BLj8HTg009cj2FTg00:Ej2ETg00:_j2BTg003ej3@Tg00;Kj3CTg00;jj4DTg00KBj2:Tg00K^j27Tg002Jj21Tg004?j20Tg00Ahj7?Tg00?nj7KTf1R0g00DSR1g00E2R2P2g00ERR3f0R4g00F2F?p=3g00CNR5P0g00ClP4C;p=4f2R6P1P2P2P3P0P4FKp=2g00G7R7#N%M7P51A56P0%>5CL%J5%G5R7P1P2P2P3P5g00C0R1,55g00L;g00FRR8,95R9C;,37R:%=8#6R;,55=<59R<%88R8,95R='4,37%88#6R>,55/4=,37527R=527%I2%68R8,55=<59R2,49,37927:142<,37=27=527GH1F73P4P6g00GcR7g00HCR3'E1B46=@73dAC510CDb3b4b5X05X151:1417;4/1011>0'0'01:101780R8,10'017;0R;,1811;611>6'0'0'0[^05^15P4p,4dcapp,3SEGp,2HQO3b2o"). Qed.
  Notation A2 l := (XB l L1 L2 L3 L4 SEG (2 * SEG) (3 * SEG) HL HQ23) (only parsing).

  (* [comment removed for export] *)
  Notation SPL1 st1 c1 v128 j0 :=
    [CB 8 j0; C8 (Z_to_bv 64 (DST + 3 * SEG)); C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (SS + O4 + 8));
     C8 (Z_to_bv 64 (SS + O3 + 8)); C8 (Z_to_bv 64 (SS + O2 + 8)); C8 (Z_to_bv 64 (3 * SEG)); C8 (Z_to_bv 64 (2 * SEG));
     C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (DST + SEG)); C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 (DST + 2 * SEG));
     C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 v128)].

  (* [comment removed for export] *)
  Definition LOOPK (q0 : Z) : Prop :=
    forall q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 mm j0 j96 j120 jp1 jp2 jp3 jp4
           (t2 x8 x9 a0 a2 a4 x21 x22 x27 t4 : word),
    q0 < q ->
    X4F' mm (SPL3 (DST + 3 * SEG) (tl + 256 * mtl) (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (3 * SEG) (2 * SEG)
                  (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + 2 * SEG) dcap DST (SS + O4 + p4) j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    HDI L1 p1 b1 -> HDI L2 p2 b2 -> HDI L3 p3 b3 -> HDI L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1) a4
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) x21 x22 (Z_to_bv 64 c4)
                           (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c1) t4 (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 0x17ad0) fc None mm (seg_rom usegs)).

  Definition X4R3 (q : Z) : Prop :=
    forall p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 mm j0 jp1 jp2 jp3 jp4 (t2 x8 a0 a2 x22 x23 x27 t6 : word),
    X4F' mm (SPL1 st1 c1 (SS + O4 + p4) j0)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    AFT L1 p1 b1 st1 -> AFT L2 p2 b2 st2 -> BEF L3 p3 b3 -> 8 <= p3 -> BEF L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 (Z_to_bv 64 3)
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1) (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) (Z_to_bv 64 st2) x22 x23
                           (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c4) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) t6)
                       F (Z_to_bv 64 98424) fc None mm (seg_rom usegs)).

  Definition X4N3 (q : Z) : Prop :=
    forall p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 mm j0 jp1 jp2 jp3 jp4 (t2 x8 a0 a2 x22 x23 x27 : word),
    X4F' mm (SPL1 st1 c1 (SS + O4 + p4) j0)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    AFT L1 p1 b1 st1 -> AFT L2 p2 b2 st2 -> BEF L3 p3 b3 -> p3 < 8 -> BEF L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 (Z_to_bv 64 3)
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1) (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) (Z_to_bv 64 st2) x22 x23
                           (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c4) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 98896) fc None mm (seg_rom usegs)).

  Definition X4R4 (q : Z) : Prop :=
    forall p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 st3 mm j0 jp1 jp2 jp3 jp4 (t2 x8 x9 a0 a2 a7 x27 t3 : word),
    X4F' mm (SPL1 st1 c1 (SS + O4 + p4) j0)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    AFT L1 p1 b1 st1 -> AFT L2 p2 b2 st2 -> AFT L3 p3 b3 st3 -> BEF L4 p4 b4 -> 8 <= p4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1) (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) a7
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 st2) (Z_to_bv 64 st3)
                           (Z_to_bv 64 c2) (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           t3 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 98600) fc None mm (seg_rom usegs)).

  Definition X4BK (q : Z) : Prop :=
    forall p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 st3 st4 mm j0 jp1 jp2 jp3 jp4 (t2 x8 a0 a2 x20 x27 : word),
    X4F' mm (SPL1 st1 c1 (SS + O4 + p4) j0)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    AFT L1 p1 b1 st1 -> AFT L2 p2 b2 st2 -> AFT L3 p3 b3 st3 -> AFT L4 p4 b4 st4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 (SS + O3 + p3)) t2 x8 (Z_to_bv 64 st4)
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1) (Z_to_bv 64 (DST + q + 3 * SEG + 3))
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) x20 (Z_to_bv 64 st2) (Z_to_bv 64 st3)
                           (Z_to_bv 64 c2) (Z_to_bv 64 (DST + q + 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c4) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 98808) fc None mm (seg_rom usegs)).

  Ltac x4open H :=
    destruct H as ((buf & OUT & LB) & SRC & CBS & STK & SPC & L0 & BDa & LBa & (jj & JJ) & BDd & LDd & BDc & LDc & BDb & LDb & FR & MI & MU & WM);
    change (zlen buf) with (Z.of_nat (length buf)) in LB;
    pose proof TOK as (TL1 & TLN & TCK); cbv [HUF_TABLELOG_MAX] in TL1; cbv [FseNCount.Zlength] in TLN;
    pose proof (DP ltac:(lia)) as D8; pose proof (length_map (Z_to_bv 8) src) as LMS; unfold BD4 in *;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  Ltac x4pack := unfold X4F, BD4; upack.

  Lemma x4s1_n3 : forall q, X4R4 q -> X4BK q -> X4N3 q.
  Proof using All.
    intros q R4 BK. unfold X4N3, X4R4, X4BK in *.
    intros until x27. intros XF Q0 QD A1 A2 B3 P3 B4 C1 C2 C3 C4.
    pose proof HL as HL'. pose proof HQ as HQ'.
    x4open XF. unfold AFT, BEF in *.
    zstep. xwalk [98600; 98808] tl DT cells cbs ECB TCK OUT LB SRC.
    all: first [ eapply (R4 p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 3)
               | eapply (BK p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 3 3) ].
    all: first [ solve [x4pack] | unfold AFT, BEF in *; lia ].
  Qed.

  Lemma x4s1_r3 : forall q, X4R4 q -> X4BK q -> X4R3 q.
  Proof using All.
    intros q R4 BK. unfold X4R3, X4R4, X4BK in *.
    intros until t6. intros XF Q0 QD A1 A2 B3 P3 B4 C1 C2 C3 C4.
    pose proof HL as HL'. pose proof HQ as HQ'.
    x4open XF. unfold AFT, BEF in *.
    zstep. xwalk [98600; 98808] tl DT cells cbs ECB TCK OUT LB SRC.
    all: lazymatch goal with H : rw_cells _ _ (SP + -184) [C8 (Z_to_bv 64 ?c); _; _; C8 (Z_to_bv 64 ?pp); _; _] |- _ =>
           assert (EP3 : pp = SS + O3 + (p3 - b3 / 8)) by lia; rewrite EP3 in *; clear EP3;
           rewrite <- (Z_to_bv_mod64 c) in * end.
    all: lazymatch goal with H : rw_cells _ _ (SP + -184) (C8 (Z_to_bv 64 ?c) :: _) |- _ =>
           first [ eapply (R4 p1 p2 (p3 - b3 / 8) p4 b1 b2 (b3 mod 8) b4 c1 c2 c c4 st1 st2 0)
                 | eapply (BK p1 p2 (p3 - b3 / 8) p4 b1 b2 (b3 mod 8) b4 c1 c2 c c4 st1 st2 0 3) ] end.
    all: first [ solve [x4pack] | solve [unfold AFT, BEF in *; lia] | solve [apply Z.mod_pos_bound; lia] ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End X4S1.
End CANSEC1.
