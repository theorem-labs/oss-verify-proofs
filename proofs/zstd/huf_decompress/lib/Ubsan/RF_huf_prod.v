(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_h_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_prod () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:swrap32_eqC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit9wrap32_eqK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z:land_assocC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer8lor_byteC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z8lxor_lorK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4bool02C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer9draw_loopK47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes3nat00I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod3INVK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface>prod_u32r_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib4Init5Logic3and01I4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_remuwK4ELinuxProcessSemantics5Riscv5Instr5instr0CC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_remuwC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface7prod_atK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas6u32_idC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod<wrap_swrap32C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop08K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef3nthC47Corelib4Init9Datatypes:option_mapC46Stdlib5Lists4List>nth_error_nth'C46Stdlib5Lists4List=nth_error_mapC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem>bytes_at_boundC46Stdlib5Lists4List:length_mapC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib9micromega;ZifyClasses:impl_morphc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod6pl_nthK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Arr9u8ro_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_slliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_slliwC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC46Stdlib4Bool4Bool=negb_true_iffC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC35stdpp7tactics<f_equal_helpC46Stdlib4Bool4Bool>negb_false_iffc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod;draw_loop_0c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod@lor_swrap32_bytec5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod9lor_mod64C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod8byte_litC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod9u32r_tailc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod9u32r_loopK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface:PPROD_U32RC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface:payload_atc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod9u32r_bodyC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface>prod_u32r_stmtC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface>prod_i32r_postC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:signed_litC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_rC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC56Stdlib6ZArith6BinInt1Z6leb_leK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer;uint32RangeK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducerAuint32Range_rangeC5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer:int32RangeC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;swrap32_eqmC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<unsigned_negC56Stdlib6ZArith6BinInt1Z6leb_gtC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_monoK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface:PPROD_I32Rc5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod9i32r_bodyC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface>prod_i32r_stmt".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

(* [comment removed for export] *)
Lemma wrap_swrap32 : forall r, 0 <= r < 2^32 -> bv_wrap 32 (bv_swrap 32 r mod 18446744073709551616) = r.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_prod ()) [] "h02H0h13H10h22H5h32Hah47__sat15h54__x1h64__x2h74__x3h84__x4h94__x5h:4__x6h;4__x7h<1zh=1Hh>2H1h?3H11h@3H12hA3H13hB2H2hC2H3hD2H4hE2H6hF2H7hG2H8hH2H9hI2HrhJ7__arithhK4__ffhL7__sat14hM8__varmaphN5__withO1qhP2q0hQ2q1hR1rhS2r0hT2r1hU2r2p&0p;1p;2p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710R1p8p1001:p4p7210P1p8g001Wj12Tg002<j1DTg002Zk200Tg0037j1tTg003Uj2oTg004<j20Tg004\j2MTg005=j1`Tg005Vj21Tg0063j28Tg006Pj2ATg006mj2PTg007Tj27Tg0080j2RTg008Wj2ITg0093j2LTg009Nj2VTg00:4j2UTg00:Zj2NTg00;;j2HTg00;Uj2gTg00<=j3fTg00<aj1eTg00=?j2dTg00=`j1:Tg00>?j3BTg00>hj2YTg00?Qj2cTg00@:j3~Tg00@cj2bTg00AOj2aTg00B;j1}Tg00B[j3_Tg00C;j1|Tg00C[j2KTg00D9j4WTg00DWj1yTg00E5j1wTg00E`j2ETg00FCj1uTg00Fej3JTg00GHj1TTg00Gmj3STg00HPj3sTg00I3j2\Tg00IVj4CTg00JAj3rTg00Jdj2qTg00KFj2pTg00L2j3QTg00LLj3nTg00Lkj4mTg00M]j2OTg00N:j1lTP0j6]Tg00O;j2kTg00Oaj1vTg00Paj3XTg00QJj7jTg00Qnj6iTg00RRj8zTg00S6j7{Tg00SZR0f0R1'Ip=5%21#2p=Zf2R2f1R3/71'Lp=9%21#2#2#2#2#2#2#2p=<g00T8R4?Q31p=4f3R5/12/03/O1p=3AQ410p=F1023/O1p=x1123/01p=h1Y41p==AX431p=GAX4319X42p=?P4P3g00TVP1CCp=@P3g00U=R6g00U\R7P7g00V<R8P1g00V\Fjp=6P3P6P7P7P8P1Eip=^1\41p=>P5P6P7P7P8P2P3P1Gzp=;P2P6P7P7P8P3P1F{p=[%51R6g00W<R9#2R:#DR;%2:R<#2#ZR=#DR>+00R?791P4%t=R@/o3RA%Z=#<#<#<R=#2RB#<#<#<#<#DRC'0RD%DBRB'01412X<4P4P3%D=R=PBP=C3RE101C/0B/42X<410EC/MB%FBRE#`RF112=RG?xB=/0CRH18HB,AB10HB'1'4[1PHB170BRHP5P=PBP=C3/0CRI/0BRJ#5?9JB[1RIB17B0RIf4RJP=PBP=C3/0CRK/0BRL,7B1IL0'L[1VKBf5RKP=PBP=C3/0CRL/8B#F\E1ULBf6RLP=PBP=C3/0CRM/0B/4M\E18MBP4f7RMP=PBP=C3/0C/0BP4f8RNP=PBP=C3/MC%FCRO#`f9P=PBP=C3RP18PC,AC10PC'1'4[1PPC170CRPf:P=PBP=C3RQ/0CRR#5?9RC[1RQC17C0f;P=PBP=C3RQ/0CRR,7C1IR0'L[1VQCf<P=PBP=C3RQ/8C#F\O1UQCf=RQP=PBP=C3RR/0C/4R\O18RCP4f>RRP=PBP=C3/0CP4f?RS/1=/MBf@RT/1=RU18UB,AB10UB'1'4\F1PUBfA/1=RU/0BRF#5?9FB\H1RUBfB/1=RU/0BRF,7B1IF0'L\I1VUBfC/1=RU/8B#F\E1UUBfDRU/1=RI/0B/4I\E18IBP4fERI?h=BP4PKg00WaRF1N0B'HPHeRHO1A961BPQ1N0C,HFPPeO1%5N?9NCPIPHO1%5T?9TB1g;>170;RT%5>170?[RH[%5;RPg00XGR6Af;>3UW3%5?\6^3PP31N0;,HFPTeO1PHg00XcRH%e9,d4RTg00YORF#:#:RP#:R6#:R>#:RV#:RW#:RX#=RY5B4RZ%=WRW9B4T%=6R69B4T1Y4FRF'G3?1c4B=~4FR[%:X#=RX%=V%=>R>/G65?Y3?g00YnRV'b'a1G6F9?YWAB4TXAB4T>%=P'G9?ZW5?[/bV'a%}H5_H3_%|HP4P41K4JP21K4LCWP3P41K4KP51K4MCWCW%y4%w4R5P51E4BRH1E40RV'@,65,^5R[%u7R7%>:RW1E4=RZ5J4%T9RP#T#>9S4H%T:#>R:5J4'@,65C;P7P5P51E4CR>/@V,65,^5P7As4:Z%2P#>9S4>%>PRP5J4'@,65C;P7P5P4PVg00ZZR>1\49R9CC,65P4P9g00[AR:PHCC,655[5P7P5P5P[P7%><9S4H=J49,@P,65C;P7P5P4PVP>PWCC,65P4PWP:1E4;=r4@CC,655[5P71@9W,65C;C;C;C;C;1q58P1P2g00[hR5g00\HR8'H1p12=Q58dAn403CmbKbMbNX54X64X74X84X94X:4X;4g00\hR0\ERE1ABMR8/1K,4G[P0\O1OL=1ACM/1J'4[%52?92B118J,4L\E%5K?9K?14KL[[[[[^54^64^74^84^94^:4^;4P1PNPSPMfFPRfMPIPQPUPJfKfLO<bJb4bLb4b0b2b1bUbQbAb@b?b1bHbTbPbGbFbEb2bDbSbObCbBb>b0b=PA%l3E]1k@D%vDE]WIXR4o"). Qed.

(* [comment removed for export] *)
Lemma lor_mod64 : forall a b, Z_to_bv 64 (Z.lor (a mod 18446744073709551616) b) = Z_to_bv 64 (Z.lor a b).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_prod ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51ah61bp;1p;2p;6p;3p;4p;7g001Wj10Tg002<j18Tg004<j25Tg00]Ej22Tg002Zj2BTg00]bj1ATg00^@j21Tg00;;j2:Tg00^^j1>Tg000\j69Tg00_Aj3OTg00_ej66Tg00`Aj3=Tg00B;j1NTg00C;j1MTg00`kj1LTg00DWj1KTg00E5j1HTg00E`j2<Tg00IVj4DTg00QJj7ETg00Jdj2FTg00KFj2GTg00L2j3;Tg00LLj3@Tg00Lkj4ITg008Wj2JTg00aIj37Tg00alj3?Tf0R0#0#0#0#0p=P%00#0p=C%00#0#0#0#0#0#0#0p=4g00T8R1f1R2;;0p=3g00W<#0R3#0#PR4#C#4#4#4#4#4#4#4#8,52/201220R5P1%83%84R4'BR3,52R6/20R7%A4R8'1f2R9/22R:/53R;,30X01P11128R<1202/18/3;X01P11158R;1198R=/22/18/30X01P111<8R>1108R?'211:8,30X01P112<?R?11=8/2</30X01P11188R:,12120<12=<R='3X01P1P81190/2</3=X011:1?P:%>8E9P>AO288E6P;A=208E912<0/18A=<08E91553g00XcR<#N%M<%L1%K1%H1R<g00U=g00U\R8P8g00V<R8P1g00SZR;,<1g00ZZ1<14CDg00V\FE1F<8P0P9g00[hR8g00\HR<':1G09=;8<dA@1;2CIb2b3b41J;4P0b1R09754E6P6A7240E61573A7740E63?X61X51o"). Qed.

(* [comment removed for export] *)
Lemma lor_swrap32_byte : forall x b, 0 <= x < 2^24 -> 0 <= b < 256 ->
  Z.lor (bv_swrap 32 (x * 256)) b = bv_swrap 32 (x * 256 + b).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_prod ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h61zh74__x2h81Hh91bh:2H0h;6__sat5h<4__x3h=2Hbh>1si001sh?2H1h@2H2hA2H3hB2HahC6__sat2hD6__sat4hE4__x4hF1ahG1li011lhH1qhI1rhJ1GhK2HkhL2HxhM1LhN4LANDhO2N0hP6__sat1hQ1ei021ehR1khS1xi031np%0p&0p;1p;2p;3p;4p;6p;7p;5p;8g001Wj17Tg002<j1PTg00GHk10;Tg002Zj2]Tg006Pj23Tg005Vj20Tg004<j24Tg00M]j22Tg0037j1iTg003Uj2nTg00bhj2}Tg007Tj21Tg008Wj2:Tg00cOR0j2kTg00B;k10STg00C;k10RTg00C[j2`Tg00DWk10OTg00E5k10NTg00I3j2^Tg00Gmj3dTg00Jdk20:Tg00;;j2ZTg00KFk207Tg00L2j3ETg00LLk304Tg00Lkk403Tg00`kk100Tg00D9j4YTg00E`j2~Tg00FCk10UTg0093S00j2ATg00cok40TTg00=`j1GTg00?Qj2|Tg00>hj2{Tg00@:j3aTg00AOj2FTg00dnj3zTg000\j6Xk70CTg004\j2yTg005=j1_Tg0063j2VTg006mj2wTg0080j2vTg009Nj2uTg00:4j2tTg00:Zj2xTg00;Uk20MTg00<=k30JTg00<ak10ITg00=?k20HTg00>?j3mTg00JAj3rTg00]Ej2qTg00^@j2pTg00eQj25Tg00f2j2[Tg00fPk40FTg00g;k10ETg00g[k20DTg00h;j1UTg00hYk309Tg00i?k50<Tg00ifk50=Tg00jKk408Tg00k4k10>Tg00kTk30?Tg00l7k30@Tg00lZk20ATg00m8k30BTg00mbk306Tg00N:j1oTg00Fek305Tg00HPk30GTg00IVj4gTg00QJj7hTg00nDk60KTg00S6k70LTg00RRj8lTg00_ek602Tg00Paj3jTg00@ck201Tg00B[k30PTg00Qnk60QTg00SZR1f0R2':p=8%72#7p=cf2R3f1R4/12'Ap=6%72#7#7#7p=\g00T8R51q34;E2p==1034/02p=?1~52p=SB05542p=TB0G542p=KP3g00U=R6g00U\R7P7g00V<R8P5P4g00TVP2Cgg00V\R9Fhp=@12429E53p=JP5P4g00ZZP2Cgp=RP4P6P7P7P8P2P9Fhp=QP4P6P7P7P8P2J0Kp=bP3P6P7P7P8P4P2K0Lp=<f3R:P6P7P7P8P3P4P2Glp=>P3P6P7P7P8P5P4g00[AP2CgP9Fhp=9P5f4R9P:P3P4P2J02p=I1{52p=HAj5429j53p=Lg00Yn-012p=Mg00XcR;@0P42p=Of6R<P6P7P7P8f5R=P9P:P6P7P7P8P3P4P2GlGlp=NAj542p=CAE521p=DAE542p=;1112p=WP4P6P7P7P8P2J0Qp=s1234/32p=Bg00[hR6g00nhR>7E2p=fP6P>P:P3P4P2EXp=e%84R?g00W<R@#7RA#PRB&0;@S01#7#cS02#PRC']RD764%7AS03#7RE#cRF#7#cRG#PRH96?4RIP513:HRJ%\G#\#\#\S04#7#c#\RG#PRK'0%7G#PRG'4/2K%iFRF139HRL/0:'n9=2:X65P510J3RM/0K/4G/2K10LKS05/4G/2K?=:2X651}JK11JK1:KJ'kP011LK1:KL13=HRL/0K/4G/2KA?L9K/4G/2K7=9P211LKP513<HRN/0KRO122KRPf7RQ/3HRR/0<RS/0KRT/4GS06/2K7=<X65P5A?N=KRU10RKRV/2KRW?=<PX65&0S;RX&0R;R;1`54RY&0O5RZ&0N5R[1^5@R\%SHR]5d5R^%SKR_,T^R`/K_3@20:[8R8P2P3g00\HRa,Z620723=E6adB04514H03Rab2b3b4X05132HRb10bKS07;JK^05P2PQO1b1AJNOKPRf8RR/3HRN/0QRc/0KRd/2KRe9=2QX65PXP;P51`53P4&005RfCYS08PZ1^5ARA,T^Rg1Tg_Rg/K_5@[P8Pab2b3b4X05X7510b4Rh10hKS09;JK^05^75P2PQPRO2b1AJSTKPcf9Rc/3HRS?=R2X65PRPQp-0RhPXP;PYPZP[1~51Ri/R\,Q[Rj1b[:S0:5<[S0;&0U7R7PjC>P8Pab2b3b4X05W5S0<%82Rk/A4P?[^05^5hS0=P211cDPcPQO3b1PXP;PYPZP[A9[\]S0>9<[jRlP7PlC>P8Pab2b3b4X05112HS0?,AkS0@PI[^05P2PRP<O2b1H0TPeP2DIb8PWP2DIb814UGg00YORW#GRe#GRI#GRl#GRm#HRn1|5HRo1{5WRW5a5Rp%HlRl%HeRe3L#M'FAa5oe=LlW#M/OX'OP;Q08PZP[A9[^_RqP7P[1RiA,Q[S0AA9[A]5<[S0BP7P[1b[99<[jP71Rig,Q[%SGRj99[g5<[C>FNP8Pab2b3b4X05X75X5h11bKRb%83Rr?63H1Ar9A?J9KRs#8?6sG[[[^05^75^5hP211QDRsP<PQP4P9P=O6b19zUGEX14OGS0C%HIRI,CW#M,FW/OXP;PYPZP[PqP7P[Q0;P71Ri`,Q[A9[`j5<[FNP8Pab2b3b4X05X5h1A?3S0D133HRq/0KRU#8?6UG[\b^05^5hP2PsPQP4P=O4b19zOGEXWMP2O11:KL1yOG%DGRs#_S0E1VVG,3G14VGS0F'0,;V[1wVG%WGRb10NKRN/4GRt#8?6tG[1vNG11G1S0G10SKRt/4GRu,1G1:u1'A[1utGf:Ru/3HRv/0KRw/VG#D\s1twGf;Rw/3HRx/0KRy/4G/;y\s1VyGP5f<Ry/3HRz/0K/4GP5P=g00WaR{1x1G'ZPbeO1S0HA6k2GS0I20MBCS0J%WBS0K%8C%WD[R|[S0L%8BR}g00XGR~B0JBC4UWBS0M%8D\~^B}S0NP41x1B,Z{Q0KeO1S0OP|1Cnl1Cpl&0I@-0H5R@%GmRm#HRp5m5R{/CI1CeW#M'F'F'F1ClW1|5G=a5WRe%GmRm#HR}Am5@nAa5oIRI'C3L#M'F/OX'OP;P5P51`5:S0PP3PfCYP4PfCYPZP[Q0AA9[Aj5<[P7P[P[A@[ji,s[S0AP7Q03,^59d5jRo/TA9@[`C>P7P[1R_^,Q[S03P7P[1b[=%SBR^Q02#i5r599[\R~5<[P71K`jS02=@[AFNFNP8Pab2b3b4X05X75X<5X5hA6?4Gg00\hS0Q\sR?13G9/0:,;U[1:KqRUA6<:DQ05/2G/;=[[[[^05^75^<5^5hP2fBR`#8P<P=P`P9PwPyf@RCO8b1b;bDb;b:bIbHbAb@b?b:b812OGQ0C';12VG14dGRV/2K9=PQX651yTGQ0E1VdG,3G/0V,;d[1wdGA?SRKRS/4GRO#8?6OG\b1vSGQ0GA?vcKRv/4GRb,1G1:b1'A[1uvGA?xuKRx/VG#D\s1txGA?zwKRz/4G/;z\s1VzGP5f=Rz/3H??yK/4GP5Q0HQ0IQ0JQ0LQ0MQ0NQ0OP|1CpW%GmRm#G#HAm5@}?LlI5Le#M'F1C{W%HmAL}pn5Le#M'F/OX'OP;P5P51`59P3PfCYP4Q0PCYPZP[Q01,^5Re,Ri,Q[A9[ej5<[P7P[P[Q0AP71Toe9@[gC>P7P[Q03P7P[Q0BP7P[1b[<=<[~P71KgjRj=@[eC>FNFNP8Pab2b3b4X05X75X<5XE5X5hA6r3GA?q:K13G=/09';\?%89?69HA6R9DA?L<K/2G/;Q[[\U[[^05^75^<5^E5^5hP2fCRU#8RQP<P=P`PUP9PwPzPCfARLO:b1b;bDb;b:bIbHbAb@b?b:b812TGQ06';12dG12tG/2KRt?=RPX65PXP;PYPZQ04#PRP#S,K\=d5]R]Q02/K_5@[P8Pab2b3b4X05AB2PHRdQ07/2G;JK^05P2PcO1b1ABRPH12NG;JKABcPHRN12vG/2KRv9=2cX65PXP;Q08PZ1T]A1Kj_5@[P8Pab2b3b4X05X7510d4Q09/2G;JK^05^75P2PcPuO2b110NR12SG;JKABuPHRK/0cABwPHRS/quRG/;2X651pKcRKP6AByPHRN/5415w4'[15139E62X96ABzPH/5315y3'[=E62X96%PERy,}4114yRd1:y4Rj'kP0113y1:y3f>R_?BPH/5:15z:'[#fP211:yf?R]/5=,[2#fX961Z6>12]PR>1]ByRA'3/59P>PyP9PXP;PYPZP[%SyRT99[\RDP7PDC>P8Pab2b3b4X05112yPd[^05P2P=P4O2b1H0FCeWGP2O11:y:ABCPH/5=/[2#fX9613>H/59$0E15_9P_P9Q0<Q0=P211]HP]PzO3b120D_1%D_R_%__'kP0%D]R0%_0%UC/1<P2%DCRCP5P1Q0@%U4/1c]=X951:11%WH'APXP;PYPZP[1RT\,Q[RTP7A9[i\R<C>P8Pab2b3b4X051:y2R0%W4R_[^05P2PcP=O2Rcb1%U1/1ReW=PLP2P]K0CWQP2O1%_CQ001]B4,13%U:/13[RC%U3/141]B3,1:R][%U9/1:\]B09342P4n2001000000120000000V_X95XF5PC\_^95^F5P2P`PRQ0JQ0LQ0MQ0NQ0OP|PXP;PYPZP[A@[\i,s[P7P[Q0;P7P<FNP8Pab2b3b4X05X5h%D2Q0Q[Q0D%W3[[^05^5hP2fFR3/1HP3P=fDO4b1bCbPbCP`PA1]BRPXP;PYPZP[Q0:Q0>5<[P7%iE9r5^99[\C>P8Pab2b3b4X05X5hQ0?,A4114A[^05^5hP2PQPUPLO3b111`AePBPyPRPXP;PfPZA9[i^P8Pab2b3b4Q0KP2b1PXP;PYPZP[PTP7PTC>P8Pab2b3b4X05Pj\0^05Pcb1I0<I0=O4b8WOP2O1n200110000021010211103b>H08CeWGP2O1n200110000021110111101b>1514&0>4Ce1pNw/54B0?Nw4EXXKkXR580@1%DK20ASuRK10Nw,;2X65RN10SuRwPN1Z5wPKB0BSu2DIPGB06Su2DIbNPvP2DIb8PtP2DIb8PVP2DIb8Q0FP2DIb8WJP2O1n200110001021110111101b>1nFM%oMEX1nFJ%oJEXW=WLX95XS5o"). Qed.

Section U32R.
  Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
  Hypothesis PR : prod_at m P D size.
  Hypothesis PL : payload_at m D pl.
  Hypothesis SZ : 0 <= size <= zlen pl.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 16.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis MM : 0 <= mn <= mx.
  Hypothesis MX : mx < 2^31.
  Hypothesis PNZ : 0 < P.
  Hypothesis PAL : P mod 8 = 0.
  Hypothesis DNZ : 0 < D.

  Notation W := [(P + 8, P + 16); (SP - 16, SP)].
  Notation POST := (prod_u32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m).
  Notation range := (mx - mn).

  Definition INV (m1 : fmem) (sz : Z) : Prop :=
    rw_cells usegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 sz)]
    /\ bytes_at usegs m1 D (map (Z_to_bv 8) pl)
    /\ (exists junk8, rw_cells usegs m1 (SP + -16) [CB 8 junk8; C8 ra])
    /\ stk usegs m1 lo (SP + -16)
    /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Notation STpc pc mm x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 mn) x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac inv_close PRx PLx FRx STx MUx WMx MIx :=
    split; [exact PRx|]; split; [exact PLx|]; split; [eexists; exact FRx|]; split; [exact STx|]; split; [exact MUx|]; split; [exact WMx| exact MIx].

  Lemma byte_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_prod ()) ["U32R"] "h02Hah17__sat13h27__sat15h37__sat17h44__x1h51Hh62H0h72Hch87__arithh94__ffh:7__sat12h;7__sat14h<7__sat16h=8__varmaph>5__with?1ah@1chA4cstrhB1zp;1p;2p;3p;4p;8p;6p;7g001Wj12Tg002<j14Tg007Tj21Tg0093R0j23Tg0037j1VTg00O;j2OTg00L2j3<Tg00oHj2DTg00ohj1CTg010Mj1BTg00;Uj2:Tg002Zj25Tg00<=j3;Tg00GHj16Tg00:Zj2WTg00;;j2>Tg00B;j1UTg00C;j1TTg00C[j2NTg00DWj1KTg00E5j1FTg00E`j28Tg00I3j2ETg00IVj49Tg00FCj1GTg00JAj3HTg00RRj8ITg00Jdj2JTg00KFj2ATg00LLj3LTg00Lkj4MTg010mj1@Tg011Kj1PTg0124j3QTg012`j2?Tg013Fj2RTg0140j2STg000\j6[Tg008Wj2ZTg00QJj7YTg00S6j7XTg00SZR1f0R2'Zp=0f1R3g00U=R4g00U\R5P5g00V<R6P2g00V\FYp=7f2R7P4P5P5P6P3P2FXp==g00T8R8%02g00W<R9#2R:#2#2R;#2#2#2R<#2#2#4R=,12'3R>P8%V;R?/O3A<827XB8p,2pl,D8R@#C%B@#0%4:R:%4;R;':111:R@%0;15:;RA,11[RB[%0:RCg00XGRDA;:;3UW0%0A\D^0C%69#6#6#6#4R;,::%0;15:;RE,11[RF\@A;:;3VDX0C%0E\D^0C%4<R<,::%0<15:<RE,11[R;\@A;:<3VDX0C%0E\D^0Cp,3RSPp,2SPRC#0RD11CERC'3P0PDPCf:R0#0110A'3P2f6g00Wa1W1:'>P@eR@O1P;f9P@O1PFf<P@O1PBg00XcRB#U%TB1N83%K8%F8RBP4P5P5P6P81881g00ZZ1E89R9C9,7BR4P8P9g00[AR@188=C9,7B5=B%G5P8P9P@188:=H8?C9,7B9=B4GI1JB6P2P7g00[hRBg00\HR6'>1A27=<B6dAL813CMb9b=b>X48%03R1113A'3\>^48P2fAf@O2b8b3b2b1X6CX5DP3P2O2n2001000000121000000b?b:b1b;b2b<b3bA%@?,5:,13,31e%P?,13,31e9Q?31??3,R?1S?3E[W7W@o"). Qed.

  Lemma draw_loop_0 : forall f sz result, draw_loop f pl sz 0 result = (result, sz).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_prod ()) ["U32R"] "p'0h06resulth12szh21fh32f0i001np;2p;5p;4p;3g014_j24Tg015?j53Tg016?j40Tg00L2j31Tg00;;j22Tg016_R0P0g00T8R11411R2f2p,2plf1R3g00SZf0R4D3P1P1P4P3C0R331^01]1P41223X01X11R1P1X20P4O1n0110000020010100W3o"). Qed.

  (* [comment removed for export] *)
  Lemma u32r_tail : forall m1 result sz (x5 x13 x14 x15 x16 x17 : word),
    0 <= result < 2^32 -> INV m1 sz ->
    (result, sz) = draw_loop 4 pl size range 0 ->
    evt usegs POST (STpc 0x20f5c m1 x5 (Z_to_bv 64 (bv_swrap 32 result)) (Z_to_bv 64 range) x13 x14 x15 x16 x17).
Proof.
  intros m1 result sz x5 x13 x14 x15 x16 x17 RR (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) DL.
  pose proof (wrap_swrap32 result RR) as WS.
  change (2^32) with 4294967296 in RR. change (2^31) with 2147483648 in MX.
  zstep. zstep. unfold v_remuw. zsimp.
  rewrite (wrap32_small (range + 1)) by lia. rewrite WS.
  replace (range + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  assert (RM : 0 <= result mod (range + 1) < range + 1) by (apply Z.mod_pos_bound; lia).
  rewrite swrap32_small by lia.
  zstep. rewrite swrap32_small by lia.
  zstep. zstep. zstep.
  release_frame FR1 ST1 SP.
  apply evt_done. unfold prod_u32r_post, uint32Range.
  rewrite (u32_id range) by (change (2^32) with 4294967296; lia). rewrite <- DL.
  replace (range =? 2^32 - 1) with false by (symmetry; apply Z.eqb_neq; change (2^32) with 4294967296; lia).
  cbn [fst snd]. rewrite (u32_id (mn + result mod (range + 1))) by (change (2^32) with 4294967296; lia).
  replace (result mod (range + 1) + mn) with (mn + result mod (range + 1)) by lia.
  do 14 eexists. exists m1. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact PR1].
Qed.

  Lemma pl_nth : forall i, 0 <= i < zlen pl ->
    nth_error (map (Z_to_bv 8) pl) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i pl)) /\ 0 <= Znth i pl < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_prod ()) ["U32R"] "h02Hah11xh24__p1h34__p2h47__sat14h57__sat16h64__x1h74__x2h84__x3h91oh:1Hh;2H0h<3H12h=2Hih>1Lh?3PLRh@2_HhA7__arithhB4__ffhC7__sat13hD7__sat15hE8__varmaphF5__withG1ahH1chI4cstrhJ1ihK1phL3z12p;2p;1p;4p;3p;7p;5p;6p;<p;8g00oHj2{Tg010MR0j1_Tg007TR1j20Tg0093R2j21Tg001Wj14Tg0037j1cTg017>j1^Tg012`j1Zj2=Tg01:2j4WTg01:Nj4VTg002<j1?Tg02PEj3TTg017aj1RTg02PfR3j1;Tg02QFj3:Tg02Qdj2NTg01AXj25Tg00L2j33Tg02R\R4j2aTg02S4j2<Tg00;;j29Tg00ohj1YTg02SQj2XTg008Wj2BTg02T3j2JTg00GHj17Tg00;Uj2ITg002Zj2HTg00<=j3LTg00:Zj2UTg00=`j1ATg00>hj2@Tg00Paj3>Tg00@cj2FTg00B;j1STg00B[j3GTg00C;j1zTg00`kj1yTg00C[j2xTg00D9j4CTg00DWj1oTg00E5j1nTg00I3j2DTg00IVj46Tg00E`j2jTg02TMj7iTg00FCj1hTg00Jdj2fTg00KFj2eTg00LLj3dTg00Lkj4bTg02U1j4gTg02U\j4KTg02V8j4QTg02V\j5kTg000\j6PTg02W?j5`Tg02Waj3lTg02X8j3mTg02XZj5]Tg02Y5j6pTg01Olj4qTg02YPl<rTg02Z5l<sTg00nDj6tTg00QJj7uTg00S6j7vTg00RRj8wTg00SZR5f0R6'Bp=2g00T8R7g016_R8P7P7P3f4R3P0f3R9g02ZZf2R:f1R;P6M<rp=\P8P7P4P0P1g02[Gf5R1P3P9P:P;P6M<sp=[P;g00U=R0g00U\R4P4g00V<R8P6Etp=OP;P0P4P4P8P6g00V\Fup=8P:P0P4P4P8P;P6Fvp=EP9P0P4P4P8P:P;P6Gwp=M%26R<p,2plR=,{7R>#_R?,06'1p,2PLg02H2p,1mp,1DP7g00W<R@#4RA#4#4RB#cRC#^RD%ZCREP=CWRFCVRG%4B#4#4RB#4#4#?RH,06,1<XH7R<=T7=RI'1P2PGPI%RDRJ%;99:DF1N9=RK,=C,5D33%2K10KH'1'1P6f6RK#;RL/a>RM1<5KRN/0?PLPNP6X171<56X17PKPK197KD\P>P?197?E[%Y>%2?f7R>,X5105>1<5>RN=37>'11B>5A37N5'1'Jf8RN,<5P7%?ARO%7@#7#7#7#?RP'I105ORQ%2P1HOPRR,05[RS[%2ORTg00XGRUALOP;UW0%2R\U^0T%?BRB,IO%2B1HOBRR,05[RP\QALOB;VUX0T%2R\U^0Tp,3RSPp,2SPRT#2RU10TRRT'1P2PUPT10K?P6PKg00Wa1U5O'9PQeRQO1PPf9PQO1PSp-0RSg00XcRQg00YORP#ARO#AR2#A,@7RR1@721@7O1@7P5>7RP5>75>7g00YnRO'FA>7RP/FO%SQ5GQ3G%zQP7P7%y7RQP:P71x79P9PQCCCCP;PQCC%o7%n7RQPQP0P4P4P81OQ1P71D7@R@g00TVR1%7A#4,D7R0C6,8Q5EQ1OQKP7P@P11j75R1C6,8Q5EQFi%h4R4PQP7P1g00ZZP0C6,8QP7P0g00[AR01D7ARAC6,8Q5EQP4P7P@P0PAC6,8QCMCM1fQ8P6P:g00[hRQg00\HR8'91e6:=3Q8dAd75;CbbBbEbFX67X77X87X2SW3A376:,19A3765,13'J%29109:'110:9[[^67^77^87^2S^3SP6fERS/B5105SPSP?f<f=fDO7bAb5b4X;TX:UP;P6O2n2001000000121000000bGbCb4bDb5bLb<bICgPM%;>R>9:DFRMP7P>P=P5CKRU,=C,5DRT53J%2U10UH'1PJP7PDPEA:7=>R?CQP7%;NP=P5CK,=C,5DRN93J6X9J%R7RS157UP7PDPEP6CQ=3JNX9S19JTP?P7P=P>P5P6DkEPPMP7PDPEP>P=D`EPAl76=%2;10;H'1[^17RE\IPI\EAm7<=P;PUP7P>P=P5P6D]EpCqb>A:DFL1NK=RK,=C,5D53J%2K10KH'1'1eX?IX@GP;P6O2n2001000000121000000bKW=XJ7o"). Qed.

  (* [comment removed for export] *)
  Lemma u32r_loop : forall f sz rolling result m1 (x5 x17 : word),
    0 < rolling < 2^(8 * Z.of_nat f) -> 0 <= result < 2^(32 - 8 * Z.of_nat f) -> (f <= 4)%nat ->
    0 <= sz <= zlen pl -> INV m1 sz ->
    (forall m2 (y5 y14 y16 y17 : word), INV m2 (snd (draw_loop f pl sz rolling result)) ->
       0 <= fst (draw_loop f pl sz rolling result) < 2^32 ->
       evt usegs POST (STpc 0x20f4c m2 y5 (Z_to_bv 64 (bv_swrap 32 (fst (draw_loop f pl sz rolling result)))) (Z_to_bv 64 range) (Z_to_bv 64 P) y14 (Z_to_bv 64 1) y16 y17)) ->
    evt usegs POST (STpc 0x20f14 m1 x5 (Z_to_bv 64 result) (Z_to_bv 64 range) (Z_to_bv 64 P) (Z_to_bv 64 sz) (Z_to_bv 64 1) (Z_to_bv 64 rolling) x17).
Proof.
  induction f as [|f IH]; intros sz rolling result m1 x5 x17 RO RE F4 SZ1 (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) K.
  { exfalso. cbn in RO. lia. }
  pose proof (bytes_at_bound _ _ _ _ PL1) as DB. rewrite length_map in DB.
  assert (P8 : 2^(8 * Z.of_nat (S f)) = 256 * 2^(8 * Z.of_nat f)).
  { replace (8 * Z.of_nat (S f)) with (8 + 8 * Z.of_nat f) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  assert (Q8 : 2^(32 - 8 * Z.of_nat f) = 256 * 2^(32 - 8 * Z.of_nat (S f))).
  { replace (32 - 8 * Z.of_nat f) with (8 + (32 - 8 * Z.of_nat (S f))) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  assert (Q24 : 2^(32 - 8 * Z.of_nat (S f)) <= 2^24) by (apply Z.pow_le_mono_r; lia).
  assert (P32 : 2^(8 * Z.of_nat (S f)) <= 2^32) by (apply Z.pow_le_mono_r; lia).
  assert (P0 : 0 < 2^(8 * Z.of_nat f)) by (apply Z.pow_pos_nonneg; lia).
  assert (Q0 : 0 < 2^(32 - 8 * Z.of_nat (S f))) by (apply Z.pow_pos_nonneg; lia).
  assert (DS : D + sz < 2^64) by lia.
  cbn [draw_loop] in K. change (2^8) with 256 in K.
  replace (0 <? rolling) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in K.
  change (2^24) with 16777216 in Q24. change (2^32) with 4294967296 in *. change (2^64) with 18446744073709551616 in *.
  zstep. if_cases B; zify_cond B.
  - subst sz.
    replace (0 <? 0) with false in K by reflexivity. cbn [fst snd] in K.
    rewrite (swrap32_small result) in K by lia.
    apply K; [| lia].
    inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
  - assert (SZP : 0 < sz) by lia.
    replace (0 <? sz) with true in K by (symmetry; apply Z.ltb_lt; lia).
    destruct (pl_nth (sz - 1) ltac:(lia)) as [NTH NR].
    zstep. zstep.
    zstep. if_cases KC1; zify_cond KC1. { exfalso. lia. }
    zstep. if_cases KC2; zify_cond KC2. { exfalso. lia. }
    zstep. if_cases KC3; zify_cond KC3. { exfalso. lia. }
    zstep. if_cases KC4; zify_cond KC4. { exfalso. lia. }
    assert (RD : ov_read_bytes usegs m1 (Z_to_bv 64 (sz + D + -1)) 1 = Some [Z_to_bv 8 (Znth (sz - 1) pl)]).
    { eapply (u8ro_read usegs m1 D _ (sz - 1)); [exact PL1| exact NTH| lia| unfold wa; f_equal; lia]. }
    zstep. cbv beta. rewrite byte_lit by exact NR.
    zstep. zstep.
    zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
    zstep. rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    assert (RD8 : 0 <= rolling / 256 < 2^(8 * Z.of_nat f)).
    { split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    rewrite swrap32_small by lia.
    zstep.
    rewrite lor_mod64. rewrite (lor_swrap32_byte result) by lia.
    set (bt := Znth (sz - 1) pl) in *.
    rewrite (u32_id (result * 256)) in K by (change (2^32) with 4294967296; lia).
    assert (LOR : Z.lor (result * 256) bt = result * 256 + bt) by (apply (lor_byte result); lia).
    rewrite LOR in K.
    zstep.
    if_cases B2; zify_cond B2.
    + assert (F1 : (1 <= f)%nat). { destruct f; [exfalso; cbn in RD8; lia| lia]. }
      assert (Q24' : 2^(32 - 8 * Z.of_nat f) <= 2^24) by (apply Z.pow_le_mono_r; lia).
      change (2^24) with 16777216 in Q24'.
      rewrite (swrap32_small (result * 256 + bt)) by lia.
      replace (sz + -1) with (sz - 1) by lia.
      eapply (IH (sz - 1) (rolling / 256) (result * 256 + bt)); try lia.
      * replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
      * exact K.
    + assert (R0 : rolling / 256 = 0) by lia. rewrite R0 in K. rewrite draw_loop_0 in K. cbn [fst snd] in K.
      apply K; [| lia].
      replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
Qed.

  Lemma u32r_body : evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PPROD_U32R) fc None m (seg_rom usegs)).
Proof.
  pose proof PR as PR0. unfold prod_at in PR0. destruct PL as [PLB PLR].
  pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
  change (2^31) with 2147483648 in MX.
  carve_frame 16%nat ST.
  unfold PPROD_U32R.
  zstep. zstep. zstep.
  if_cases K; zify_cond K. { exfalso. lia. }
  zstep. rewrite swrap32_small by lia. zstep.
  if_cases K2; zify_cond K2.
  - zstep.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (bv_swrap 32 0)) by reflexivity.
    eapply (u32r_tail _ 0 size); [lia| | ].
    + inv_close PR0 PLB FR ST MU WM MI.
    + rewrite K2. reflexivity.
  - assert (K2' : 0 < range) by (Z.div_mod_to_equations; lia).
    assert (LA : Z.land P 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact PAL).
    zstep. zstep. if_cases KN; zify_cond KN. { exfalso. lia. }
    zstep. zstep. if_cases KA; zify_cond KA. { exfalso. lia. }
    zstep. zstep. zstep.
    rewrite LA.
    eapply (u32r_loop 4 size range 0);
      [ change (2^(8 * Z.of_nat 4)) with 4294967296; lia | cbn; lia | lia | lia | | ].
    + inv_close PR0 PLB FR ST MU WM MI.
    + intros m2 y5 y14 y16 y17 I2 R2.
      zstep. zstep. if_cases K3; zify_cond K3.
      * eapply u32r_tail; [exact R2| exact I2| ]. destruct (draw_loop 4 pl size range 0); reflexivity.
      * exfalso. Z.div_mod_to_equations; lia.
Qed.
End U32R.

Lemma prod_u32r_proof : prod_u32r_stmt.
Proof.
  intros until lo. intros PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM MX -> -> ->.
  eapply u32r_body; eassumption.
Qed.

Lemma sub_mod64 : forall a b,
  Z_to_bv 64 (a mod 18446744073709551616 - b mod 18446744073709551616) = Z_to_bv 64 (a - b)
  /\ bv_swrap 32 (a mod 18446744073709551616 - b mod 18446744073709551616) = bv_swrap 32 (a - b).
Proof.
  intros a b.
  assert (E : a mod 18446744073709551616 - b mod 18446744073709551616
              = (a - b) + (b / 18446744073709551616 - a / 18446744073709551616) * 18446744073709551616).
  { rewrite !Z.mod_eq by lia. ring. }
  rewrite E. split.
  - apply Z_to_bv_eqm. change (2^64) with 18446744073709551616. rewrite Z.mod_add by lia. reflexivity.
  - rewrite !swrap32_eq. f_equal.
    replace (a - b + (b / 18446744073709551616 - a / 18446744073709551616) * 18446744073709551616 + 2147483648)
      with ((a - b + 2147483648) + ((b / 18446744073709551616 - a / 18446744073709551616) * 4294967296) * 4294967296) by ring.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma u32r_fst_bound : forall pl size R, 0 <= R < 2147483648 -> 0 <= fst (uint32Range pl size 0 R) <= R.
Proof.
  intros pl size R HR. unfold uint32Range.
  rewrite (u32_id (R - 0)) by (change (2^32) with 4294967296; lia).
  destruct (draw_loop 4 pl size (R - 0) 0) as [r s'].
  replace (R - 0 =? 2^32 - 1) with false by (symmetry; apply Z.eqb_neq; change (2^32) with 4294967296; lia).
  pose proof (Z.mod_pos_bound r (R - 0 + 1) ltac:(lia)) as RB.
  cbn [fst]. rewrite u32_id by (change (2^32) with 4294967296; lia). lia.
Qed.

Lemma swrap32_add64 : forall x, bv_swrap 32 (x + 18446744073709551616) = bv_swrap 32 x.
Proof.
  intros x. rewrite !swrap32_eq. f_equal.
  replace (x + 18446744073709551616 + 2147483648) with ((x + 2147483648) + 4294967296 * 4294967296) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma swrap32_mod64 : forall x, bv_swrap 32 (x mod 18446744073709551616) = bv_swrap 32 x.
Proof.
  intros x. rewrite !swrap32_eq. f_equal. rewrite (Z.mod_eq x 18446744073709551616) by lia.
  replace (x - 18446744073709551616 * (x / 18446744073709551616) + 2147483648)
    with ((x + 2147483648) + (- (x / 18446744073709551616) * 4294967296) * 4294967296) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma int32Range_neg : forall pl size mn mx, mn < 0 ->
  int32Range pl size mn mx = (fst (uint32Range pl size 0 (mx - mn)) + mn, snd (uint32Range pl size 0 (mx - mn))).
Proof.
  intros pl size mn mx H. unfold int32Range. replace (mn <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (uint32Range pl size 0 (mx - mn)); reflexivity.
Qed.

Ltac subfp := unfold sub_fp; intros ?x; cbn; intuition lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section I32R.
  Hypothesis U32R : prod_u32r_stmt.
  Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
  Hypothesis PR : prod_at m P D size.
  Hypothesis PL : payload_at m D pl.
  Hypothesis SZ : 0 <= size <= zlen pl.
  Hypothesis P0 : 0 < P.
  Hypothesis P8 : P mod 8 = 0.
  Hypothesis D0 : 0 < D.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 32.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis MM : - 2^31 <= mn <= mx.
  Hypothesis RG : mx - mn < 2^31.
  Hypothesis MX : mx < 2^31.

  Lemma i32r_body : evt usegs (prod_i32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PPROD_I32R) fc None m (seg_rom usegs)).
Proof.
  pose proof PR as PR0. unfold prod_at in PR0. destruct PL as [PLB PLR].
  pose proof (munch_refl [(P + 8, P + 16); (SP - 32, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold prod_u32r_stmt in U32R.
  change (2^31) with 2147483648 in *.
  carve_frame 16%nat ST.
  unfold PPROD_I32R.
  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K. { exfalso. rewrite !signed_lit in K by lia. lia. }
  zstep. zstep. if_cases K2; zify_cond K2.
  - assert (MN : mn < 0) by (Z.div_mod_to_equations; lia).
    zstep. zstep.
    destruct (sub_mod64 mx mn) as [E1 E2]. rewrite E1, E2. rewrite (swrap32_small (mx - mn)) by lia.
    zstep. if_cases K3; zify_cond K3. { exfalso. lia. }
    zstep. rewrite Z.add_0_r, (swrap32_small (mx - mn)) by lia. zstep. zstep.
    eapply evt_cut.
    { eapply U32R with (SPV := SP + -16) (lo := lo) (size := size) (pl := pl) (D := D) (P := P) (mn := 0) (mx := mx - mn).
      all: try reflexivity. all: try first [exact PR0 | split; [exact PLB| exact PLR] | exact ST | exact MI | exact DP | lia].
      all: fail. }
    intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & PR2).
    replace (ret_pc (Z_to_bv 64 0x20ff4)) with (Z_to_bv 64 0x20ff4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells usegs m2 (SP + -16) [C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn; lia]).
    pose proof (u32r_fst_bound pl size (mx - mn) ltac:(lia)) as RB.
    zstep. zstep. zstep.
    set (r := fst (uint32Range pl size 0 (mx - mn))) in *.
    assert (MM64 : mn mod 18446744073709551616 = mn + 18446744073709551616) by (symmetry; apply (Z.mod_unique _ _ (-1)); lia).
    rewrite MM64. replace (r + (mn + 18446744073709551616)) with ((r + mn) + 18446744073709551616) by ring.
    rewrite swrap32_add64, (swrap32_small (r + mn)) by lia.
    if_cases K4; zify_cond K4. { exfalso. lia. }
    zstep.
    zstep. zstep. zstep. zstep.
    release_frame FR2 ST2 SP. rewrite ?Z.add_0_r. rewrite swrap32_mod64, (swrap32_small (r + mn)) by lia. subst r.
    apply evt_done. unfold prod_i32r_post. rewrite int32Range_neg by lia. cbn [fst snd].
    do 14 eexists. exists m2. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; subfp]|].
    split; [eapply wmono_trans; eassumption|]. split; [exact MI2|]. split; [exact ST2| exact PR2].
  - assert (MN : 0 <= mn) by (Z.div_mod_to_equations; lia).
    zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST SP.
    eapply evt_cut.
    { eapply U32R with (SPV := SP) (lo := lo) (size := size) (pl := pl) (D := D) (P := P) (mn := mn) (mx := mx);
        try reflexivity; first [exact PR0 | split; [exact PLB| exact PLR] | exact ST | exact MI | exact DP | lia]. }
    intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & PR2).
    apply evt_done. unfold prod_i32r_post, int32Range.
    replace (mn <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    do 14 eexists. exists m2. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; subfp]|].
    split; [eapply wmono_trans; eassumption|]. split; [exact MI2|]. split; [exact ST2| exact PR2].
Qed.
End I32R.

Lemma prod_i32r_proof : prod_u32r_stmt -> prod_i32r_stmt.
Proof.
  intros U32R. intros until lo. intros PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM MX RG -> -> ->.
  eapply i32r_body; eassumption.
Qed.
