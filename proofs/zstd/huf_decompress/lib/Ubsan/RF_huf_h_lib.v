(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_h_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h_lib () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4list01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_nilC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC46Stdlib5Lists4List7map_appC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appC47Corelib4Init5Logic5proj1C47Corelib5Lists7ListDef3mapI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appI46Stdlib5Lists4List6Exists00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums8positive01C46Stdlib5Lists4List@firstn_length_leK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI47Corelib4Init5Logic2ex00c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib7hC_postC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib=PC_HC_EXIT_RAc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib8PFREE_HCC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC46Stdlib5Lists4List:length_mapc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib2hkC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib?bytes_at_prefixc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib=Forall_prefixc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib;zlen_prefixK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib6hC_endC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_16C5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC56Stdlib6ZArith6BinInt1Z4lxorK46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_DEC_STACKK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface7prod_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission3Lib3Tac7sum_natC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameK46Stdlib9micromega:ZMicromega;ZArithProof03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_rdt_postC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib6hC_decC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz05K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI4ELinuxProcessSemantics5Riscv3Sem4core00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_RDT_STACKK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib;PC_HC_ENTRY".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_HC_ENTRY : Z := 0x1337c.      (* [comment removed for export] *)
Definition PC_HC_EXIT_RA : Z := 0x1347c.    (* [comment removed for export] *)
Definition PFREE_HC : Z := 0x21b30.         (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_null : forall m, rw_cells usegs m 0 [CB 0 []].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_lib ()) [] "h07__arithh14__ffh28__varmaph35__with41xh54__p1h64__x1h71ih82Hih93Hi0h:1mh;1yp;1p;2p;3p;4p;<p;6p;8p;7p10000p4p7210p1000\p4p710p8p1001:p4p7210p1001Wp4p710p8g0023j12Tg002Xj1ETg0036j1>Tg003Yj1ITg004;j1;Tg004[j2ZTg005Pj3VTg0060j4STg006gj1RTg007`R0j19Tg008@j4HTg0092j1GTg009ij1FTg00:cj4hTg00;Xj37Tg00<2j23Tg00<Lj45Tg00<gj1XTg00=Gj1WTg00=ej1UTg00>Cj1TTg00>nj2BTg00?Qj1=Tg00?oj3QTg00@Rj2PTg00A4j2LTg00A`j3KTg00B?j4JTg00C1j20Tg00CMj2MTg00Cjj24Tg00DEj4NTg00E>j2OTg00EUj28Tg00F2R1j21Tg00FNj1ATg00G=j3?Tg00H:j1DTg00H\j1@Tg00I5j3gTg00IXj3fTg00J>j1eTg00J\l<]Tg00KAj6\Tg00Kjj4[Tg00LQj2YTg00Loj2^Tg00MRj4CTg00N=j6_Tg00Naj8`Tg00OEj7aTg00Oij7bTg00PMl<cTg00Q2R2f1R3g00QPf0R4CCp=:P3g00R7R5g00RVR6P6g00S6R7P4g00SVFap=6f2R8P5P6P6P7P3P4Fbp=<g00T6R9P2P2P2P0P0f3R0P8P3g00TUR:g00U4R;P4M<cp=dg00URR<#2R=#2#2R>#2#2#2R?#ER@#>%E>#>R>#IRA[g00V7RBP4P;g00VlRC%;>,Z:%;C3VRCCSPBP4P;%RC#9CHRD%GCREPBP4P;%FCChRCA79::g00Wa139:g00X=C5PEePBP4P;g00XYRE#;RF%XERE%W2RG%U2RH%T2RI1B2;RJ/:J,6IRK%==R=,B2=Q2@R@,:J,6I3<1PI7RLP4P8g00YERMg00YeRN'31L48=7MNdAK2;3CJRNb1b2b310;;RM%=?,M=R=,0;'4P4b0CNPCeC5PM1O::#9RC,8;/0=R?10;4RO114C'4RC18;3#A9?B8%D>R>57A#@[^72RP'4PFPEPGPHPKPLPNb1b2b3PMP4b0P?PPPFPEPGPHAg2JJ/:@,6IPLPNb1b2b318;;/0=P4b0P?e10;3R?%9:R:,13R='4113;,4?R@P?P=P?P4X42R=P;O1RG,13p-0RP/3?A7P??e9f??P2P2P1P=P11134#eX;2X42P3P31323P:PGP=P=%94,32X49132;CdM<]E\P4C[P@PFPE1Y23PHPIP5P6P6P71^2<R<,:J,6IP2P<g00ZEPJCC,6I5<I%D6PIP5P6P6P7P0E_G`PLPNb1b2b3X62X5P114;,4OP8[^62^5PP4f418;0#A5?B=7A>#@P0P3O3b0b9X8CX72C5C5PDeC5W:o"). Qed.

(* [comment removed for export] *)
Lemma bytes_at_prefix : forall m D pl k,
  bytes_at usegs m D (map (Z_to_bv 8) pl) -> bytes_at usegs m D (map (Z_to_bv 8) (firstn k pl)).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_lib ()) [] "h01Hh11mh21ah33bs1h43bs2h52plh64segsh71Dh82H0h91kh:1lp;1p;3p;6p;5p;4p;2g0023j13Tg002Xj1=Tg0036j1<Tg003Yj1@Tg00<gj1;Tg00Zlj1DTg00[Rj39Tg00\1j38Tg00\Oj34Tg00\lj3?Tg000\j6>Tg00]Mj5FTg001Wj6ETg00:cj42Tg00]ij27Tg007`j16Tg00EUj25Tg00CjR0j2:Tg00^Ij5CTg00_Bj3BTg00_]j4ATg00Q2R1f2R2f1R3f0R4CAp=0g00V7R5P2P3P4C2p=1g00UR#3#3#3R6#3#3#3#=#<%=6R6#<R7#@[R8%;1R9g00T6f3R:%D6R6=073712P9P2f5R;f4R<A076431X59P4A9132A8132541R9A?132E>A076991<:%;7R9A912:R=A812:R>5419076f6R??1;4X:9P4A076=A076>547R@P1P7P6P=P>DFEEA1;<@g00`9#;R@P0P<P:P2A4734C2P;P<P:P2C2P;P<1772#6,5:P3C2':[R0P<P:P2P3C2P<P:1773#6,52P4C2':P;P<P:A4723C2R>[P?P;P<P:C2P?P;177:#6,5<P2C2':\>P<P:P2P3P4DCP3n2001000000120000000X49X39X21X18W6P0^49^39^21^18^6@P4P5f7R5P?A91<;9076R@A81<;9076R<P3O6A15?@177@#6,5?=15<':f8R<A91;?9076R@715177@#6,55A81;?907651<;B4b0b8b0b0W0W9W5X71W1o"). Qed.

Lemma Forall_prefix : forall (P : Z -> Prop) pl k, Forall P pl -> Forall P (firstn k pl).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_lib ()) [] "h01Hh11Ph21Ah32l1h42l2h52plh62H0h71kp;1p;3p;6p;2p;4g00<gj14Tg00[Rj33Tg00\1j35Tg00\Oj36Tg00\lj3:Tg000\j69Tg00a8j30Tg00CjR0j22Tg00aYj48Tg00_Bj37Tg00Q2R1f1R2f0R330p=1p-0R4\1%41R5g00T6f2R6/12P5P6f4R7/13X55P3A3126A5126561R5A:126E9f3R8/15g00b8p4p710R5P4\3R4%42R9%46R:P0A68239086A0786A0782'2[R0A0862A0863'2A67629078R;[f5R<?078A0<76'2\;P8P6P2P3C8P2n2001000000120000000W4W3W1W2P0^4:^39^14^25P3P1P<A3187R5A5187R8P2O511<511<8'2f6R8A317<'1A517<,18;73b0b6b0W0W7W5W1o"). Qed.

Lemma zlen_prefix : forall (pl : list Z) k, 0 <= k <= zlen pl -> zlen (firstn (Z.to_nat k) pl) = k.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_lib ()) [] "h04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;4__x3h<4cstrh=2z0h>2Hkh?1kh@1nhA2plhB1yp;1p;2p;<p;3p;4p;6p;7p;8g00<gj1KTg00C1R0j20Tg00]ij2@Tg007`R1j16Tg00Cjj21Tg00bUR2j1eTg00c5j2=Tg00;Xj1Xj3?Tg00J>j1UTg00<2j2;Tg00J\l<LTg00cRj1mTg00d7j2iTg00F2j2ITg00dYj2DTg00e3j1BTg00eRj2>Tg00f;j28Tg00fgj1ZTg00gEj2YTg00gfj3WTg004;j1VTg005Pj39Tg00LQj2FTg00=Gj1TTg00hOj4ETg00=ej1RTg00>Cj1QTg00Loj2ATg0023j1PTg00>nj2STg00H:j1nTg00@Rj2lTg00A4j2kTg00A`j3hTg00B?j4gTg00hmj4JTg00[Rj3dTg00iXR3j2cTg00j2j1_Tg00jWj4`Tg000\j6aTg00PMl<GTg00k<j3^Tg00N=j6fTg00MRj4HTg00OEj7]Tg00Oij7\Tg00kej7[Tg00Naj8jTg00Q2R4f1R5f0R63?p=2P4g00T6R7P4P4P2f4R2P1f3R8g00lIf2R9P5P6M<Gp=OP7P4P4P4P1P1f5R:P2P8P9P5P6M<Gp=NA^456p=3P5g00R7R;g00RVR<P<g00S6R=P6Efp=:P4P5g00m6P6CHp=CP5P;P<P<P=P6g00SVF]p=4P9P;P<P<P=P5P6F\p=5P4P5g00QPP6CHp=<P9P;P<P<P=P5P6F[p=MP8P;P<P<P=P9P5P6Gjp=7P7P4P3P1P0g00m]P:P2P8P9P5P6M<Lp=b%K4g00U4R0/061@45#6,06'1P7%e5R1%66R3/29X@7%61R;/251=05R>/25P4P4%X4R?P6X44R@P?1256#UXB4X44P;P>P@P@1;43X47P1P>P@1=06X44P5P51;45R@DOR7ENP5P5P@M<L1@49R@#mR3%6@R;,00R?1i09RA1I091=09RB/29'11090A?4B0'1'DRB1=08RCP4p-0RDg00XYREg00TURF#BRG#BRH,>4RI1>4G1>4FRF'3RG'3g00n?RJ'8%BH,>4RHg00URRK#Z,Y4=W4I/3FRL'3/8J18LJ%VERL59E59E39%KERMP41F49RNP5%T4CE%R4RO%Q4RP1:P21A4KRQ%PK,A4RR'C,4PRS55P1S40RT,<R,4P1CQT,4PRU55P5MP%n<R<PP1<TR,4PRT1:P:RV55PP<PSC7C71lP=R=P6P9g00YERSg00YeRW';1k69=?SWdAh405CgRWb7b9b:X24X34X0DW11265,191050A?460RS'1'D1009RX/121298[[^24^34^0D^1DP6f6RY,@4#6RZ,0:1I0:R[P:P5P9P2O6b6b=b5b<CJAd419,@4P4P9P11c1@10>;P1P>P7P@P;1;4;EbP3P?PAPBPCP413IF,3H/8J13HG/8J=9EL59EPMP4PNP51F48CEPOPP%_K,A4RK,CQ,4P95PV1:PY=5PU5MPP<PPPTP<PPf7RT,:P1<KR,4P55PP<1<QR,4PC7C7C7P=PWb7b9b:X24X34X;4X0DX1DX8D1269,18112S'D1028,1T1082[\X[^24^34^;4^0D^1D^8DP6100:10:0P[P:PZP5P9P8P2O9b6b=b5b<CJC`EaW>X?4WAo"). Qed.

(* [comment removed for export] *)
Definition hk (P : Prop) : Prop := P.

Section PhaseC.
  Variable dt_ok : fmem -> Z -> Z -> Prop.
  Hypothesis RDT1 : huf_rdt_stmt dt_ok PHUF_RDT_X1.
  Hypothesis RDT2 : huf_rdt_stmt dt_ok PHUF_RDT_X2.
  Hypothesis DEC1 : huf_dec_stmt dt_ok PHUF_DEC_1X.
  Hypothesis DEC4 : huf_dec_stmt dt_ok PHUF_DEC_4X.

  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP P D DT W DST dbs mtl streams symbols rest lo : Z) (pl : list Z) (m0 : fmem).

  Notation WC := [(SP - 4096, SP); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704); (DST, DST + dbs)].

  (* [comment removed for export] *)
  Definition hC_post : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x1 x2 x3 x7 x8 x9 x10 x11 t3 t4 t5 t6 : word) (m' : fmem),
      ms' = MS (mkR (Z_to_bv 64 PC_HC_EXIT_RA) (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) x1 (Z_to_bv 64 DT)
                    a1 a2 a3 a4 a5 a6 a7 x2 x3 (Z_to_bv 64 DT) (Z_to_bv 64 W) (Z_to_bv 64 DST) x7 x8 x9 x10 x11 t3 t4 t5 t6)
               F (Z_to_bv 64 PFREE_HC) fc None m' (seg_rom usegs)
      /\ munch WC m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo SP.

  (* [comment removed for export] *)
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis STR : 0 <= streams <= 1.
  Hypothesis SYM : 0 <= symbols <= 1.
  Hypothesis RS : 0 <= rest <= zlen pl.
  Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
  Hypothesis PLEN : zlen pl < 2^26.
  Hypothesis D16 : 16 <= D.
  Hypothesis DBS : 0 <= dbs < 2^32.
  Hypothesis HDZ : hk ((DST = 0 /\ dbs = 0) \/ (0 < DST /\ DST mod 8 = 0)).
  Hypothesis LO : lo <= SP - 4096.
  Hypothesis SP0 : 0 <= SP.
  Hypothesis SPH : SP < 2^64.
  Hypothesis SPAL : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis P0 : 0 < P.
  Hypothesis PAL : P mod 8 = 0.
  Hypothesis D0 : 0 < D.
  Hypothesis DT0 : 0 < DT.
  Hypothesis DTAL : DT mod 8 = 0.
  Hypothesis W0 : 0 < W.
  Hypothesis WAL : W mod 8 = 0.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DTLO : DT + DTABLE_BYTES mtl <= lo.
  Hypothesis WLO : W + 8704 <= lo.
  Hypothesis DSTLO : DST + dbs <= lo.
  Hypothesis DJ_P_DT : hk (P + 16 <= DT \/ DT + DTABLE_BYTES mtl <= P).
  Hypothesis DJ_D_DT : hk (D + zlen pl <= DT \/ DT + DTABLE_BYTES mtl <= D).
  Hypothesis DJ_D_W : hk (D + zlen pl <= W \/ W + 8704 <= D).
  Hypothesis DJ_D_DST : hk (D + zlen pl <= DST \/ DST + dbs <= D).
  Hypothesis DJ_DT_W : hk (DT + DTABLE_BYTES mtl <= W \/ W + 8704 <= DT).
  Hypothesis DJ_DT_DST : hk (DT + DTABLE_BYTES mtl <= DST \/ DST + dbs <= DT).
  Hypothesis DJ_W_DST : hk (W + 8704 <= DST \/ DST + dbs <= W).

  (* [comment removed for export] *)
  Lemma hC_end : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x1 x2 x3 x7 x8 x9 x10 x11 t3 t4 t5 t6 : word) (m2 : fmem),
    munch WC m0 m2 -> wmono usegs m0 m2 -> mem_inv usegs m2 -> stk usegs m2 lo SP ->
    evt usegs hC_post
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) x1 a0
               a1 a2 a3 a4 a5 a6 a7 x2 x3 (Z_to_bv 64 DT) (Z_to_bv 64 W) (Z_to_bv 64 DST) x7 x8 x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13474) fc None m2 (seg_rom usegs)).
  Proof.
    intros until m2. intros MU WM MI ST.
    zstep. zstep. apply evt_done. unfold hC_post.
    do 22 eexists. exists m2. split; [reflexivity|]. auto.
  Qed.

  Ltac dec_if := first [ if_true | if_false ].
  Ltac step_to pc := repeat (lazymatch goal with
     | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
     | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => dec_if
     | |- evt _ _ (MS _ _ _ _ _ _ _) => zstep end).
  Ltac to_dec := repeat (lazymatch goal with
     | |- evt _ _ (MS _ _ (Z_to_bv 64 0x15a50) _ _ _ _) => fail
     | |- evt _ _ (MS _ _ (Z_to_bv 64 0x154d0) _ _ _ _) => fail
     | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => dec_if
     | |- evt _ _ (MS _ _ _ _ _ _ _) => zstep end).
  Ltac dj H := rewrite ?zlen_prefix by lia; generalize H; unfold hk; lia.
  Ltac pdec :=
    lazymatch goal with
    | |- _ = _ => first [reflexivity | lia | (rewrite unsigned_lit by lia; lia) | (rewrite zlen_prefix by lia; reflexivity)]
    | |- dt_ok _ _ _ => eassumption
    | |- mem_inv _ _ => eassumption
    | |- bytes_at _ _ _ _ => apply bytes_at_prefix; eassumption
    | |- Forall _ _ => apply Forall_prefix; eassumption
    | |- stk _ _ _ _ => rewrite unsigned_lit by lia; eassumption
    | |- (_ = 0 /\ _ = 0) \/ _ =>
        generalize HDZ; unfold hk; intros [[? ?]|[? ?]]; [left; lia | right; split; [lia| split; [lia| eassumption]]]
    | |- _ + DTABLE_BYTES _ <= _ \/ _ => first [dj DJ_DT_DST | dj DJ_D_DT]
    | |- _ \/ _ => dj DJ_D_DST
    | |- context [HUF_DEC_STACK] => unfold HUF_DEC_STACK; rewrite unsigned_lit by lia; lia
    | |- context [bv_unsigned] => rewrite unsigned_lit by lia; lia
    | |- context [zlen (firstn _ _)] => rewrite zlen_prefix by lia; lia
    | |- _ => lia
    end.
  Ltac call_dec fl :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x15a50) _ _ _ _) =>
        eapply evt_cut; [ eapply DEC4 with (DST := DST) (dcap := dbs) (S := D) (src := firstn (Z.to_nat rest) pl)
                            (DT := DT) (mtl := mtl) (lo := lo) (flags := fl); pdec | ]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x154d0) _ _ _ _) =>
        eapply evt_cut; [ eapply DEC1 with (DST := DST) (dcap := dbs) (S := D) (src := firstn (Z.to_nat rest) pl)
                            (DT := DT) (mtl := mtl) (lo := lo) (flags := fl); pdec | ]
    end.
  Ltac after_dec MU WM :=
    let ms := fresh "ms" in let PO := fresh "PO" in
    intros ms PO;
    destruct PO as (?u0 & ?u1 & ?u2 & ?b0 & ?b1 & ?b2 & ?b3 & ?b4 & ?b5 & ?b6 & ?b7 & ?u3 & ?u4 & ?u5 & ?u6 & ?m2
                    & -> & MU2 & WM2 & MI2 & ST2);
    rewrite unsigned_lit in MU2, ST2 by lia;
    rewrite ret_pc_even by (first [lia | reflexivity]);
    step_to 0x13474;
    eapply hC_end;
    [ eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, HUF_DEC_STACK; intros ?x; cbn; intuition lia]
    | eapply wmono_trans; [exact WM | exact WM2] | exact MI2 | exact ST2 ].

  (* [comment removed for export] *)
  Lemma hC_dec : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x3 x9 x10 x11 t3 t4 t5 t6 : word) (r flags : Z) (m1 : fmem) (j0 jd : list byte),
    0 <= r < 2^64 -> (r < 2^64 - 119 -> dt_ok m1 DT mtl) -> 0 <= flags < 64 ->
    bytes_at usegs m1 D (map (Z_to_bv 8) pl) ->
    rw_cells usegs m1 DST [CB (Z.to_nat dbs) jd] ->
    rw_cells usegs m1 SP [CB 8 j0; C8 (Z_to_bv 64 streams); C8 (Z_to_bv 64 symbols)] ->
    munch WC m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 -> stk usegs m1 lo SP ->
    evt usegs hC_post
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 D) (Z_to_bv 64 r)
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 flags) x3 (Z_to_bv 64 DT) (Z_to_bv 64 W) (Z_to_bv 64 DST)
               (Z_to_bv 64 dbs) (Z_to_bv 64 rest) x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13428) fc None m1 (seg_rom usegs)).
  Proof.
    intros until jd. intros RR DTOK FLB PB DB FS MU WM MI ST.
    step_to 0x1342c.
    destruct (Z.ltb_spec r 18446744073709551497) as [RL|RL];
      [change (Z.lxor (Z.b2z true) 1) with 0 | change (Z.lxor (Z.b2z false) 1) with 1].
    - specialize (DTOK ltac:(lia)).
      to_dec. if_cases KS; zify_cond KS; to_dec.
      all: call_dec flags; after_dec MU WM.
    - step_to 0x13474. eapply hC_end; eassumption.
  Qed.
  Ltac chk := let K := fresh "K" in if_cases K; zify_cond K;
    try (exfalso; first [lia | (rewrite Z.mod_small in K by lia; lia)]).
  Ltac walk_to pc := repeat (lazymatch goal with
     | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
     | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [dec_if | chk]
     | |- evt _ _ (MS _ _ _ _ _ _ _) => zstep end).

  Ltac hide H := lazymatch type of H with ?t => change t with (hk t) in H end.

  Ltac flags_ok :=
    repeat (match goal with
            | |- context [Z.b2z (0 <? ?f)] => is_var f;
                let E := fresh "E" in assert (E : f = 0 \/ f = 1) by lia; destruct E as [E|E]; rewrite E
            end);
    (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
  Ltac prdt :=
    lazymatch goal with
    | |- _ = _ => first [reflexivity | lia | (rewrite unsigned_lit by lia; lia) | (rewrite zlen_prefix by lia; reflexivity)]
    | |- 0 <= _ < 64 => flags_ok
    | |- mem_inv _ _ => eassumption
    | |- bytes_at _ _ _ _ => apply bytes_at_prefix; eassumption
    | |- Forall _ _ => apply Forall_prefix; eassumption
    | |- stk _ _ _ _ => rewrite unsigned_lit by lia; eassumption
    | |- rw_cells _ _ _ _ => eassumption
    | |- _ \/ _ => generalize DJ_DT_W DJ_D_DT DJ_D_W; unfold hk; rewrite ?zlen_prefix by lia; lia
    | |- context [HUF_RDT_STACK] => unfold HUF_RDT_STACK; rewrite unsigned_lit by lia; lia
    | |- context [bv_unsigned] => rewrite unsigned_lit by lia; lia
    | |- context [zlen (firstn _ _)] => rewrite zlen_prefix by lia; lia
    | |- _ => lia
    end.
  Ltac call_rdt :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x140d0) _ _ _ _) =>
        eapply evt_cut; [ eapply RDT2 with (DT := DT) (W := W) (S := D) (mtl := mtl) (src := firstn (Z.to_nat rest) pl)
                            (lo := lo); try (lazymatch goal with |- _ = Z_to_bv 64 _ => reflexivity end); prdt | ]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x134d8) _ _ _ _) =>
        eapply evt_cut; [ eapply RDT1 with (DT := DT) (W := W) (S := D) (mtl := mtl) (src := firstn (Z.to_nat rest) pl)
                            (lo := lo); try (lazymatch goal with |- _ = Z_to_bv 64 _ => reflexivity end); prdt | ]
    end.
  Ltac after_rdt MU WM PB DB FS :=
    let ms := fresh "ms" in let PO := fresh "PO" in
    intros ms PO;
    destruct PO as (?u0 & ?u1 & ?u2 & ?b1 & ?b2 & ?b3 & ?b4 & ?b5 & ?b6 & ?b7 & ?u3 & ?u4 & ?u5 & ?u6 & ?r & ?m2
                    & -> & MU2 & WM2 & MI2 & ST2 & RR & DTOK);
    rewrite unsigned_lit in MU2, ST2 by lia;
    rewrite ret_pc_even by (first [lia | reflexivity]);
    walk_to 0x13428;
    eapply hC_dec;
    [ exact RR | exact DTOK | flags_ok
    | eapply bytes_at_transport; [exact PB | exact MU2 |
        cbn [disjoint_from]; rewrite length_map; unfold HUF_RDT_STACK; generalize DJ_D_DT DJ_D_W; unfold hk; lia]
    | eapply rw_cells_transport; [exact DB | exact MU2 | exact WM2 |
        cbn [disjoint_from cells_size csize]; unfold HUF_RDT_STACK; generalize DJ_DT_DST DJ_W_DST; unfold hk; lia]
    | eapply rw_cells_transport; [exact FS | exact MU2 | exact WM2 |
        cbn [disjoint_from cells_size csize Nat.add]; unfold HUF_RDT_STACK; lia]
    | eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU2];
        unfold sub_fp, HUF_RDT_STACK; intros ?x; cbn [outside]; intuition lia]
    | eapply wmono_trans; [exact WM | exact WM2] | exact MI2 | exact ST2 ].

  (* [comment removed for export] *)
  Theorem phaseC_proof : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word) (f1 f2 f3 f4 f5 : Z)
                                (j0 jdt jw jd : list byte),
    0 <= f1 <= 1 -> 0 <= f2 <= 1 -> 0 <= f3 <= 1 -> 0 <= f4 <= 1 -> 0 <= f5 <= 1 ->
    prod_at m0 P D rest ->
    bytes_at usegs m0 D (map (Z_to_bv 8) pl) ->
    rw_cells usegs m0 DT [CB (Z.to_nat (DTABLE_BYTES mtl)) jdt] ->
    rw_cells usegs m0 W [CB (Z.to_nat 8704) jw] ->
    rw_cells usegs m0 DST [CB (Z.to_nat dbs) jd] ->
    rw_cells usegs m0 SP [CB 8 j0; C8 (Z_to_bv 64 streams); C8 (Z_to_bv 64 symbols)] ->
    stk usegs m0 lo SP -> mem_inv usegs m0 ->
    evt usegs hC_post
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 D) (Z_to_bv 64 DST)
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f5) (Z_to_bv 64 mtl) (Z_to_bv 64 DT) (Z_to_bv 64 W) s6
               (Z_to_bv 64 dbs) (Z_to_bv 64 f1) (Z_to_bv 64 f2) (Z_to_bv 64 f3) (Z_to_bv 64 f4) t3 t4 t5 t6)
          F (Z_to_bv 64 PC_HC_ENTRY) fc None m0 (seg_rom usegs)).
  Proof.
    intros until jd. intros F1 F2 F3 F4 F5 PR PB DTC WC0 DB FS ST MI.
    unfold prod_at in PR.
    pose proof (munch_refl WC m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    assert (LA3 : Z.land DT 3 = 0)
      by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
    assert (LP7 : Z.land P 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
    assert (DTB : 12 <= DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES; pose proof (HufHarness.DT_BYTES_range mtl ltac:(unfold HufHarness.HUF_TABLELOG_MAX; lia)); lia).
    assert (DTR : DT < 2^64) by lia. assert (PR64 : P < 2^64) by lia.
    assert (P2 : 2 <= 2^mtl <= 4096)
      by (split; [apply (Z.pow_le_mono_r 2 1 mtl)| apply (Z.pow_le_mono_r 2 mtl 12)]; lia).
    assert (DTN : Z.to_nat (DTABLE_BYTES mtl) = (4 + Z.to_nat (4 * 2^mtl))%nat)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; lia).
    rewrite DTN in DTC.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [4%nat; Z.to_nat (4 * 2^mtl)]) in DTC; [| cbn; lia].
    cbn [mk_CB_cells app] in DTC.
    unfold PC_HC_ENTRY.
    zstep. if_cases KN; zify_cond KN. { exfalso. first [lia | (rewrite Z.mod_small in KN by lia; lia)]. }
    zstep. zstep. zstep. if_cases KA; zify_cond KA. { exfalso. first [lia | (rewrite Z.mod_small in KA by lia; lia)]. }
    walk_to 0x133cc.
    unfold hk in DJ_P_DT, DJ_D_DT, DJ_DT_W, DJ_DT_DST.
    zstep.
    hide DJ_P_DT. hide DJ_D_DT. hide DJ_DT_W. hide DJ_DT_DST.
    walk_to 0x133d8.
    zstep. zstep. zstep.
    repeat (lazymatch goal with
     | |- evt _ _ (MS _ _ (Z_to_bv 64 0x140d0) _ _ _ _) => fail
     | |- evt _ _ (MS _ _ (Z_to_bv 64 0x134d8) _ _ _ _) => fail
     | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [dec_if | chk]
     | |- evt _ _ (MS _ _ _ _ _ _ _) => zstep end).
    all: replace (Z.shiftl mtl 24 + mtl) with (mtl * 16777217) in DTC by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: call_rdt.
    all: after_rdt MU WM PB DB FS.
  Qed.

End PhaseC.
