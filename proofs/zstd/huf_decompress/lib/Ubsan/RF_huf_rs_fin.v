(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun FseRdKit HufWalkKit
  FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_rs_pure RF_huf_rs_cl.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_rs_fin () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C47Corelib5Lists7ListDef6repeatC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats<collect_loopK47Corelib4Init9Datatypes4prod01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl5cl_okC45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure7rs_tailC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure4rresC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romI47Corelib5Lists7ListDef6Forall00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shl32C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6assertC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes3orbC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount9highbit32I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure5sm_ltC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm1C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm2C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm3C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm4I4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z9lt_succ_rC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses;rew_iff_revK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC56Stdlib6ZArith6BinInt1Z4lxorC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoric5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin3nkcC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_aC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_bC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_cK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_dC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit<highbit32_okC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sllwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_sllwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC56Stdlib6ZArith6BinInt1Z9log2_specC56Stdlib6ZArith6BinInt1Z7add_1_rC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC56Stdlib6ZArith6BinInt1Z;le_gt_casesC56Stdlib6ZArith6BinInt1Z7mul_1_lC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>negb_false_iffC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas8zload_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5storeC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas9zstore_okC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storec5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin<upd_app_mid'K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl<nth_map_ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u32arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u32arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_writeC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7upd_natC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;map_upd_natC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas>upd_nat_lengthC46Stdlib5Lists4List;Forall_implC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl>Forall_upd_natC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin:land1_mod2C5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK4ELinuxProcessSemantics5Riscv5Instr5instr03I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List7map_appK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit2:sx32_smallc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin<shl32_shr30'C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_lxorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm5C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure8sm5_onesc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin;srliw_smallc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin9rest_formC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK46Stdlib9micromega5Tauto8GFormula06K4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z3lorC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC56Stdlib6ZArith6BinInt1Z3lebK46Stdlib9micromega5Tauto8GFormula0:C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC46Stdlib5Lists4List:length_mapC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop0:K46Stdlib9micromega5Tauto4kind02I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00K47Corelib4Init5Logic4True01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStatsCHUF_SYMBOLVALUE_MAXK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma srliw_small : forall x k, 0 <= x < 2^31 -> 0 <= k ->
  bv_swrap 32 (bv_wrap 32 x ≫ k) mod 18446744073709551616 = x ≫ k.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_fin ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with64__x2h72Hah81zh96__sat0h:6__sat1h;6__sat2h<6__sat3h=4__x3h>1Hh?2Hkh@2HxhA1RhB1khC1xp;1p;2p;3p;4p;5p;6p;7p;8p10000p4p710p1000Mp4p710p8p1000ip4p7210g001UR0p4p710R1p8p10023p4p7210P1p8g002Pj10Tg0035j1@Tg003Sj1DTg0048j2CTg004Uj24Tg0051j22Tg005Lj1QTg005jj2ATg006Jj2KTg0071j2GTg007Qj3FTg007kj2uTg008Hj2<Tg008dj1rTg009Dj1pTg009dj2NTg00:Bj1fTg00:`j1eTg00;Kj2?Tg00;nj2PTg00<Qj1`Tg00=3j2_Tg00=Uj2^Tg00=oj2]Tg00>[j3\Tg00?:j4ZTg00?lj2Ij4wTg00@Tj3HTg00A8j1YTg00AVj4OTg00B4j4xTg00BUj2XTg00C>j2WTg00C_j4vTg00D@j2tTg00Dij1ETg00EHj2BTg00F1j2VTg00F]j3UTg00G=j5qTg00Gaj3oTg00HDj3nTg00Hgj2mTg00IDj5hTg00J0j4gTg00JKj3iTP0j6MTg00K4j3STg00KWj1jTg00L5j2kTg00M9j2lTg00M_j4RTg00NJj7TTg00Nnj6cTg00ORj7bTg00P6j8JTg00PZj3aTg00QCj3sTg00QlR0f0R1'<p=1%01#0#0#0p=d%01#0p=[%01#0#0#0#0#0#0#0p=9g00RJR2f1R3g00RhP1CRp==P3g00SOR4g00SnR5P5g00TNR6P1g00TnR7FTp=8P3P4P5P5P6P1Ecp=Lf2R8P4P5P5P6P3P1Fbp=5f3R9P4P5P5P6P8P3P1GJp=71401p=:P8P4P5P5P6P2P3g00UNP1CRP7FTp=6Aa231p=3As231p=;f6R7P4P5P5P6f5R:f4R;P9P4P5P5P6P8P3P1GJGJp=>%13R<g00V5R=#0R>#@R?%D=R@#D#D#DRA#@RB'CRC,43'2P2P9%d>RD#QRE1A19'K%[D#9#9#9RD#0RF#9#9#9#9#@RG'G1A;9RH5F2X82P21C?8RI,u9RJ%11RK1<1;'2X82%1J1<J9P9PIp-0RJg00VZRL#rRM%pLRN1N23RO%f2RP%e2RQ1?20RR1P2=RS'=,8QRT1LQ955Q%`5RUPTC71_Q6RVP1P8g00WFRWg00WfRX'^1]18=FWXdA\203CZRXb2b4b5X02W312K3P<[^02^3JP114;CP;P8O3b11I?BRW%:?RY%1B%:C[[RZ%1?R[g00XFR\AH?B3UW7RB%1C\\R]^7[R^1I?;%1:R_1C?7#:[\Yf7R`=H?3V\X7[1C?`Ra#1\\^7[PMPNP2%Y2RbP31N28RcCOPPPQPQ1?2?Rd96QRRePUPQ1P2@,=R,8QR@PUA6QRSC7RfC7PUPfC7PVPXb2b4b5X02X62%18Rf%:8[Rg\YPg[^02^62P1P`PaP8P:O4b1b9b:b;b<RgCxP9PIP9PgP?P8PMPNPbPPPePVPXb2b4b5PYP1b1P1Cw%:IPWPZPBP^1I?:%17%:a[\Yf8Ra=H?3V\X7[1C?aR^#1\\^7[%@DR\,X2RBP2%@=,W2P=1W20Cv,t2g00XbR0#ER=#ERZ#ERW,B2RI'3'3%EW,B2RW1B2=R=,3I/;=RI'31X2?1B20R0,3W'3130I,3B1300,3B';';';';g00YARB'V=ULMPNP2PcP31N29COPPPQPQPePUPQP@PU1P2>R>96QRReF>PUPQPQ1=Rd,8QPUPQPQP4P5P5P6DqPU%QA9o2dRd,=R,8QF>PUPQPePUPQP@PUPQ1LQ:95QTPUAn2>S,=S,8QC7F>F>PVPXb2b4b5X02X62X=2X3J%19%:9R@[\YP]\[%1;/2`1m7:,<:[\_\@[[^02^62^=2^3JP1f9R@/4CPaP^P@P8P9P:P7P`O9b1b9b:b;b<b>DhCg1A98R`PMPNPOPPPQPTPUPTC7PVPXb2b4b5X02P<\K^02P1P9P3O2b19i98EM%1`1<`9'2P2PH1G1G1A:;R75F2X821B2Z1;=0';/VB=ULMRLPNP2PcP3PbCORbPPPQ1=S>,8Q95QTRcPUPQ1LQ;A6Q>d55QR>PU1?2G96QS95QTF>PVPXb2b4b5X02X62X3J1<13,2KRB148C,29R0148G,2f[[^02^62^3JP1P_P:P7P3P9O5R7b19SHG1KEHPLPNPbPPPQPcPUPQP>PU%jDRD,?2/=S,8Q1?2\96QS55QF>PVPXb2b4b5X02X62X3J1<D8148\'2\0\B^02^62^3JP7b1,kHEMbA%@FRF,G9PMPNPOPPPQA6QSd95QTPU1?2F96QS95QTC7PVPXb2b4b5X02141C,2K143F,2<[^02P1P;P8O2b19S9FEM1lE9/A8,KE/GG=F2`eX?<W@XB2XC2o"). Qed.

(* [comment removed for export] *)
Definition nkc (k : Z) : Z := Z.lxor (Z.ones (k + 1)) 18446744073709551615.

(* [comment removed for export] *)
Lemma rest_form : forall k wt, 0 <= k <= 11 -> 2^k <= wt < 2^(k+1) ->
  bv_swrap 32 (bv_swrap 32 (2 ≪ (k mod 32)) mod 18446744073709551616 - wt) = 2^(k+1) - wt.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_fin ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h61zh74__x2h84__x3h91Eh:2Hkh;2Hwh<1Ph=2P0h>1kh?2wtp;2p;1p;3p;4p;5p;7p;6p;8g008Hj20Tg002Pj11Tg003Sj1JTg0035j18Tg0051j22Tg0048j24Tg00Ymj2>Tg004Uj2<Tg005Lj1PTg00ZJj2GTg006Jj2;Tg0071j2CTg00Zjj2:Tg00Hgj2BTg008dj1fTg009Dj1cTg009dj2VTg00:Bj1`Tg00:`j1_Tg00;nj2ITg00HDj3QTg00Gaj3^Tg00M_j4HTg00=3j2]Tg00=Uj2\Tg00=oj2[Tg007Qj3OTg00>[j3ZTg00?:j4YTg00;Kj2NTg00<Qj1WTg00A8j1oTg00[Gj5nTg00[jj3mTg00\Sj3lTg00]6j5LTg00J0j4kTg00Dij1DTg00EHj2FTg00QCj3KTg00F1j2hTg00F]j3gTg00AVj4TTg00KWj1eTg00]]j3dTg00L5j2RTg00K4j3STg00NJj7UTg00Nnj6bTg00ORj7aTg00P6j8iTg001Uj6jTf0R0#1#1p=E%10#1#1#1p=X%10#1#1#1#1#1#1#1p=Ag00RJR1f1R2;O0p=91N10p=7P2g00SOR3g00SnR4P4g00TNR5P0g00TnR6FUp==f2R7P3P4P4P5P1P2g00RhP0CHP6FUp=3P2P3P4P4P5P0Ebp=MP7P3P4P4P5P2P0Fap=5f3R6P3P4P4P5P7P2P0Gip=6P1f4R3P6P7P2P0Ejp=@P1P2g00UNP0CHp=?g00QlR8/02R9g00V5R:#1R;#J#J#8R<,02'2%8;R=/47/02%8:R>,>7,4=,<2'2P6%1;R?#1#ER@#PRA1G=0,;A%1@#E#XRB#1#E#A#ARC#1#A#A#A#A#8RD'C/:6';1>3>RE,4=RF/:6'9X6114=6RG,B=190FX6114=>RH,BG14=3RG,B=/90X61g00VZRI#fRJ%cIRK1V12RL%`1RM%_1RNP1%7=RO1I1:RP5Q1g00^@%P:9^1O9Q1PCH'=1]N5R5P0P7g00WFRQg00WfRR'\1[07=OQRdAZ182CYRRb2b3b4X011B=01B0H'9^01P0PGO1b11>6>,4=RGP=P6P>p-0RHPJPKPLPMPN1N18RQ=3NPRS1MN6RT55NRU%W4R4PSC6P5PRb2b3b4X01W5RV1080RW/22RXP9[^01^5HRYP0103<P3P7O3b1RZPJPK%o1R[PM%7>R\93NQP5PRb2b3b4108>P0b1DnD@1G=6R]Am=6ZD@19]G10=FR]%8BRB,0FRFP=P>PEPJPKP[PM1?QO,=NP5PRb2b3b41<8=P0b1RQPJPKPLPMPNPUP4Al1P\RU93N\C6P5PRb2b3b4X01X5H1>2>RG,0>\X^01^5HP0f5RX/0<PXP6O3b1DLP=PE%J:#E#8R:PQPJPKPLPMPN%7<93NPRE95NTP4%7:93NUC6P5PRb2b3b4X01X5H100<RU,2210G:[^01^5HP0108XPXP6O3b1DLCk12]FP=P8PXPQPVPYP0f6RY/0<PYP3O3b1DL14=X,0>1>Y>,4=R<1;A0/CD/:Y,;Af7RV/>>,4=RQ/:YR8'9X61P<1C0D/:Y,;A/98X61P<1:0Y,;A/98X611:<Xg00XbR8#D#DRF#DR]#D,F11F1]1F1F1F185K15K15K1g00YA'h=gIJPKP1P11V16P7P[CTP2P[CTPMPN1I1?R?93N\P4PN1MNX%7B93NPRX55NP4PN1I1;R;93N?1?;P,=N55NP4%eCR?#7R\Ad1P;R;53N%8CRC#7R[,?;,=N55NC6C6C6P5PRb2b3b4X01X71X81X5H10>7102B,2310361<67'21:63R>,0?1<>C'2[[[^01^71^81^5HP010=Q14=VPYPQP2P7P3O7b1'R1C<DPJPKPLPMPNA3NOP=5NXRXP4%7D,?P,=N95NSC6P5PRb2b3b4X0110=0100B'2RB1<2D,29[^01P0PQP7O2RQb19S<DD@1;A<PJPKPLPMPNPXP4A3N\P1?P[,=N55NC6P5PRb2b3b4X0110?21<2C'2\B^01PQb1,R<D@1G=YP7D@b=b<b9%8@R@,C6PJPKPLPMPNA5NSEP4%7@,?P,=N95NSC6P5PRb2b3b4X0112WU1<2@,29[^01P0P3P7O2b19S6@D@W;W:X?1X>1o"). Qed.

(* [comment removed for export] *)
Lemma shl32_shr30' : forall x, 0 <= x < 2^31 -> (x ≪ 32 mod 18446744073709551616) ≫ 30 = 4 * x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_fin ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh62Hah74__x2h84__x3h91Hh:2H0h;2H1h<2H2h=2H3h>2Hxh?6__sat4h@6__sat5hA1qhB1rhC1xp;1p;2p;3p;4p;6p;7p;8g002Pj10Tg0035j16Tg003Sj1?Tg0048j2MTg004Uj24Tg0051j2<Tg00Hgj21Tg0071j25Tg005jj2QTg007kj2>Tg00^gj2vTg007Qj3ATg00_Hj1qTg00Ymj2TTg00_aj2kTg00`Hj2dTg008Hj2RTg00`oj2aTg00aUj2`Tg00?lj2]Tg00@Tj3\Tg00Dij1GTg00EHj2DTg00F1j2@Tg00b;j2PTg00KWj1[Tg00C>j2ZTg00bgj3YTg00BUj2OTg00PZj3NTg008dj1XTg00F]j3CTg009Dj1WTg009dj2FTg00AVj4VTg00:Bj1xTg00:`j1wTg00;Kj2UTg00<Qj1uTg00;nj2LTg00cPj6pTg00HDj3BTg00\Sj3oTg00=3j2jTg00=Uj2hTg00=oj2eTg00>[j3cTg00?:j4fTg005Lj1gTg00Gaj3bTg00K4j3iTg001Uj6JTg00A8j1lTg00JKj3mTg00ZJj2nTg00[jj3_Tg00QCj3^Tg00M_j4HTg00NJj7rTg00ORj7sTg00P6j8tTg00QlR0f0R1'Rp=3%01#0p=S%01#0#0#0#0#0#0#0p=9g00RJR2f1R3;A1p=8A^231p=:1U21p=7P2P3g00UNP1CHp=EP3g00SOR4g00SnR5P5g00TNR6P1g00TnFrp=2P2P3g00RhP1CHp=;f2R7P4P5P5P6P3P1Fsp=Kf3R8P4P5P5P6P7P3P1Gtp==P2P3g00^@P1CHp=I%31g00V5R9#0R:#6R;%?9R<#?#?R=#?R>#6R?'MR@,41'<RAP2%0:RB#0#SRC#6RD,M;,13RE%0C#9#9#9RC#SRF#9#9#9#9#6RG,51%0=#6R='Q%6BRB/17RH'8X52P215EGRE1M;='>181HX52P2%6FRF,13RI%6CRC,>1/8HX521vICAA2C0RH#q117FRJ1>JC,1C15JC'T'8[1kJC140CRJ118FRK/5CRL#314LC'<[1dKC14C0f4RL/1FRM/5CRN,4C1RN0'<[1aMCf5/1FRM/>C=A20\H1`MCf6/1FRM/5C/8M\H1>MCP2f7/1F/5CP21];?140;%3?140@[[%3;RMg00XFRNA\;?3UW6%3@\N^6Mg00VZRMg00XbRN#GR@#GR?,D21D2@R@':1D2NRN/:@g00YARO'@'P%G?,D2R?%[9,Z2=Y2@1O2C=N2N':':/@O%XMRP5CM3C%WMRQP21F27P31F28CV%x2RR%w2RSPS1U20RT%7CRU'E,2S%u5RV1L2<R<,;T,2S1E<U,2S5KSC=PVPSPSPSP4P5P5P61IUT,2SEpPV1L2:R:%7FR55B21L29R99B2U=o2<'I,2SC=PV%7B=B2:,I9,2SC=C=1jS6R6P1P7g00WFR:g00WfR<'h1e17=A:<dAc203CfR0b1b2b3X42X72X82%38148C'<\Jg00d4\H11C7/TL,8K[11B8,87[[^42^72^82P1P8f;PLf8f9O5b0b?b@bBbAb=b<b;b:b915IG1O2F=N2@/:N/@O1:N?/@O,PN=CMP5CMPQ1F23PRPS1;T9,2S%7;%g>5b2,E9,2S5KSPVAB295R9,;T,2S%7G,E9,2S5KSC=P6P0b1b2b3X42%3I14IG'<\A^42P1P7P3O2b09iIGEJ1QE=PPPQ%l2RIPR%7=,;T,2SP6P0b1b2b3%3=P1b09mE=EJ1n3DPPPQPIPR%7D,;T,2SP6P0b1b2b3%3DP1b09_3DEJW>XC2o"). Qed.

Lemma upd_app_mid' : forall {X} (l1 : list X) x rest y, upd (l1 ++ x :: rest) (length l1) y = l1 ++ y :: rest.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_fin ()) [] "h04resth11xh21yh32l1h42IHh51Xh61lh71zp;1p;3p;2p;4p;6p;5p200R0p1000Mp4p710p8P0g001UR1p4p710p8P0g00dQR2p4p710p8P0g00eAR3p4p710p8P0g00ecR4p4p710p8P0g00fCR5p4p710p8g009Dj12Tg00F]j30TP5j31TP4j23TP2j45Tg007Qj34Tg00=Uj26Tg008dj19TP1j68TP3j57Tf0R3#2f1R1%21f2R2f3R4#2f4R5f5R6#2R7P6A062191641364P3C5A0631916434]2]0]1W3%22R8%25R9A0531R:'6P5%95R;A0521515135;P3C5A15;:549eX24W0X11f6R;#2P;A0;2191;413;4P3C5A0;3191;434^26^09^14f7R9#2R:A0931R<9195R=f8R>#2A0>;3A0>1291>690>;34X6:A096=,6:P9A0921R=91951395P3C5P4P2P1P3O3E8P9A0965R6=19=1396P3C5A196<54:eX2;X07X15W4X38X71P3D7W3X50o"). Qed.

Lemma land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_fin ()) [] "h01Eh17__arithh24__ffh38__varmaph45__with51xp;1p;2p;4p;7p;3g0035j12Tg008dj1ETg009Dj14Tg00A8j13Tg00:Bj1DTg00:`j1;Tg00;Kj20Tg00M_j45Tg00NJj76Tg00=3j27Tg00=Uj28Tg00=oj29Tg007Qj31Tg00>[j3CTg00?:j4BTg008Hj2?Tg00f`j3<Tg00gCj1=Tg00gaj2>Tg002Pj1:Tg0048j2@Tg0071j2ATg00RJR0f0R1g00V5R2#2R3g00VZR4#E%44%30%D0%;0R4g00SOg00SnR5P5g00TNR5P0g00QlR6,00g00Rh1003C5g00TnF61745P1f2R5g00WFR4g00WfR7'81915=147df19C06CBb2b3b41?63P1b13<%=3,>1%:2#2/@3,A1510P1b0W5o"). Qed.

Lemma rsf_lor_lt : forall a j k, 0 <= a < 2^k -> 0 <= j -> 0 <= k -> 0 <= Z.lor a (a ≫ j) < 2^k.
Proof.
  intros a j k Ha Hj Hk.
  assert (S0 : 0 <= a ≫ j) by (apply Z.shiftr_nonneg; lia).
  assert (S1 : a ≫ j <= a) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj); Z.div_mod_to_equations; nia).
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a (a ≫ j)) 0) as [E|NE]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  apply Z.log2_lt_pow2; [pose proof (proj2 (Z.lor_nonneg a (a ≫ j)) (conj (proj1 Ha) S0)); lia|].
  rewrite Z.log2_lor by lia.
  destruct (Z.eq_dec a 0) as [->|NA]; [exfalso; apply NE; rewrite Z.shiftr_0_l; reflexivity|].
  assert (L1 : Z.log2 a < k) by (apply Z.log2_lt_pow2; lia).
  assert (L2 : Z.log2 (a ≫ j) <= Z.log2 a) by (apply Z.log2_le_mono; lia).
  lia.
Qed.

Lemma rsf_land3 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rsf_srw : forall x k, 0 <= x < 2147483648 -> 0 <= k -> bv_swrap 32 (bv_wrap 32 x ≫ k) = x ≫ k.
Proof.
  intros x k Hx Hk.
  rewrite (wrap32_small x) by lia.
  assert (S0 : 0 <= x ≫ k) by (apply Z.shiftr_nonneg; lia).
  assert (S1 : x ≫ k <= x) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); Z.div_mod_to_equations; nia).
  apply swrap32_small. lia.
Qed.

Lemma rsf_shr_lt : forall a j k, 0 <= a < 2^k -> 0 <= j -> 0 <= a ≫ j < 2^k.
Proof.
  intros a j k Ha Hj.
  assert (S0 : 0 <= a ≫ j) by (apply Z.shiftr_nonneg; lia).
  assert (S1 : a ≫ j <= a) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj); Z.div_mod_to_equations; nia).
  lia.
Qed.

Ltac rsf_bnd := first [ change (2^19) with 524288; lia | apply rsf_lor_lt; [rsf_bnd | lia | lia] | apply rsf_shr_lt; [rsf_bnd | lia] ].

Ltac rsf_sr := repeat match goal with |- context [bv_swrap 32 (bv_wrap 32 ?x ≫ ?k) mod ?M] =>
  rewrite (srliw_small x k) by (first [ lia | enough (0 <= x < 2^19) by (change (2^19) with 524288 in *; change (2^31) with 2147483648; lia); rsf_bnd ]) end.

Section FIN.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x22 x23 x24 x25 x26 x27 x30 x31 : word).
  Variables (m : fmem) (HW RK NSP TLP iS : Z) (ws : list Z) (junk : list byte) (nsv tlv : word).
  Variable POST : machine_state -> Prop.
  Hypothesis HWS : 1 <= zlen ws <= 255.
  Hypothesis HWB : Forall (fun c => 0 <= c < 256) ws.
  Hypothesis HIS : 0 <= iS <= 128.
  Hypothesis HJK : zlen junk = 256 - zlen ws.
  Hypothesis HHW : 0 < HW /\ HW + 256 <= 2^64.
  Hypothesis HRK : 0 < RK /\ RK + 52 <= 2^64.
  Hypothesis HNT : 0 < NSP /\ NSP + 4 <= TLP /\ TLP + 4 <= 2^64.
  Hypothesis DHR : HW + 256 <= RK \/ RK + 52 <= HW.
  Hypothesis DHN : HW + 256 <= NSP \/ TLP + 4 <= HW.
  Hypothesis DRN : RK + 52 <= NSP \/ TLP + 4 <= RK.
  Hypothesis ARK : RK mod 4 = 0.
  Hypothesis ANS : NSP mod 4 = 0.
  Hypothesis ATL : TLP mod 4 = 0.

  Notation WF := [(HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4); (TLP, TLP + 4)].

  Lemma rs_fin : forall m1 rank1 wt (x5 x6 x7 x15 x16 x17 x20 x21 x28 x29 : word),
    collect_loop ws (repeat 0 13) 0 = Ok (rank1, wt) -> cl_ok (zlen ws) rank1 wt ->
    u32arr usegs m1 RK (map (Z_to_bv 64) rank1) ->
    u8arr usegs m1 HW (map (Z_to_bv 8) ws ++ junk) ->
    rw_cells usegs m1 NSP [C4 nsv] -> rw_cells usegs m1 TLP [C4 tlv] ->
    munch WF m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    (forall m2 a0v (y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word),
       munch WF m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
       rres HW RK NSP TLP (rs_tail ws (zlen ws) iS) m2 a0v ->
       evt usegs POST (MS (mkR ra sp gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 a0v) y11 y12 y13 y14 y15 y16
                               y17 y18 y19 y20 y21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x1f124) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR ra sp gp tp x5 x6 x7 (Z_to_bv 64 RK) (Z_to_bv 64 HW) (Z_to_bv 64 (-20)) (Z_to_bv 64 NSP)
                            (Z_to_bv 64 (Z.lxor HW (2^64 - 1))) (Z_to_bv 64 TLP) (Z_to_bv 64 wt) x15 x16 x17
                            (Z_to_bv 64 (zlen ws)) (Z_to_bv 64 iS) x20 x21 x22 x23 x24 x25 x26 x27
                            x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1ef58) fc None m1 (seg_rom usegs)).
Proof using All.
  intros m1 rank1 wt x5 x6 x7 x15 x16 x17 x20 x21 x28 x29 CL CO RKA HWA NSC TLC MU WM MI K.
  destruct CO as (RKL & RKB & WTB).
  assert (RT0 : wt = 0 -> rs_tail ws (zlen ws) iS = Err 20).
  { intros E. subst wt. unfold rs_tail. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. rewrite CL. reflexivity. }
  zstep. if_cases K0; zify_cond K0.
  { eapply K; [exact MU | exact WM | exact MI |]. rewrite (RT0 ltac:(lia)). split; [reflexivity | split; reflexivity]. }
  zstep. zstep. zstep. rsf_sr. do 9 (zstep; rsf_sr).
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => let p := eval vm_compute in (bv_key (Z_to_bv 5 15)) in let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end) in lazymatch v with Z_to_bv 64 ?e => change e with (sm5 wt) end end.
  rewrite (sm5_ones wt) by lia.
  assert (HL : 0 <= Z.log2 wt <= 18) by (split; [apply Z.log2_nonneg | assert (Z.log2 wt < 19); [apply Z.log2_lt_pow2; lia | lia]]).
  assert (LSPEC : 2^(Z.log2 wt) <= wt < 2^(Z.log2 wt + 1)) by (pose proof (Z.log2_spec wt ltac:(lia)) as X; replace (Z.succ (Z.log2 wt)) with (Z.log2 wt + 1) in X by lia; exact X).
  remember (Z.log2 wt) as L eqn:EL in *.
  do 21 zstep.
  first [ brute_reg 15 L 0 19 (fun L : Z => L) | brute_reg 15 L 0 19 (fun L : Z => 31 - L) | idtac ].
  first [ brute_reg 16 L 0 19 (fun L : Z => 31 - L) | brute_reg 16 L 0 19 (fun L : Z => L + 1) | brute_reg 16 L 0 19 (fun L : Z => 32 - L) | brute_reg 16 L 0 19 (fun L : Z => L) | brute_reg 16 L 0 19 (fun L : Z => 63 - L) | idtac ].
  step.
  if_cases K1; zify_cond K1.
  { eapply K; [exact MU | exact WM | exact MI |].
    assert (RT1 : rs_tail ws (zlen ws) iS = Err 20).
    { unfold rs_tail. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. rewrite CL. cbn [bind].
      replace (wt =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold highbit32. replace ((0 <? wt) && (wt <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
      cbn [bind]. rewrite <- EL. replace (HUF_TABLELOG_MAX <? L + 1) with true by (symmetry; apply Z.ltb_lt; unfold HUF_TABLELOG_MAX; lia).
      reflexivity. }
    rewrite RT1. split; [reflexivity | split; reflexivity]. }
  step.
  Ltac rsf_ck K := zify_cond K; exfalso; repeat match type of K with context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) in K by lia end; repeat match type of K with context [Z.land ?x 3] => rewrite (rsf_land3 x) in K by lia end; first [ lia | Z.div_mod_to_equations; lia ].
  if_cases K2; [(rsf_ck K2)|].
  step.
  step.
  if_cases K3; [(rsf_ck K3)|].
  step.
  step.
  step.
  step.
  step.
  rewrite (inr64_unsigned_lit L) by (unfold inr64; lia).
  rewrite (inr64_unsigned_lit (31 - L)) by (unfold inr64; lia).
  replace (32 - (31 - L)) with (L + 1) by lia.
  rewrite (shiftl_mod32 2 L) by lia.
  assert (PL : 1 <= 2^L <= 2048) by (split; [pose proof (Z.pow_pos_nonneg 2 L ltac:(lia) ltac:(lia)); lia | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]).
  assert (PE : 2^(L + 1) = 2 * 2^L) by (rewrite Z.pow_add_r by lia; lia).
  rewrite PE in LSPEC.
  remember (2^L) as P eqn:EP.
  rewrite (swrap32_small (2 * P)) by lia.
  step.
  if_cases K4; [(rsf_ck K4)|].
  Ltac rsf_rng e := first [ lia | enough (0 <= e < 2^19) by (change (2^19) with 524288 in *; lia); rsf_bnd ].
  Ltac rsf_un := repeat match goal with
    | |- context [bv_swrap 32 (bv_wrap 32 ?x ≫ ?k)] => rewrite (rsf_srw x k) by rsf_rng x
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_small e) by lia
    | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (inr64_unsigned_lit e) by (unfold inr64; rsf_rng e)
    end.
  step. rsf_un.
  step. rsf_un.
  step. rsf_un.
  remember (2 * P - wt) as rest eqn:EREST.
  assert (RR : 0 <= rest < 524288) by (subst rest; lia).
  do 2 (step; rsf_un).
  do 4 (step; rsf_un).
  do 4 (step; rsf_un).
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => let p := eval vm_compute in (bv_key (Z_to_bv 5 15)) in let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end) in lazymatch v with Z_to_bv 64 ?e => change e with (sm5 rest) end end.
  rewrite (sm5_ones rest) by lia.
  assert (HM : 0 <= Z.log2 rest <= 11) by (split; [apply Z.log2_nonneg | assert (Z.log2 rest < 12); [apply Z.log2_lt_pow2; lia | lia]]).
  assert (MSPEC : 2^(Z.log2 rest) <= rest < 2^(Z.log2 rest + 1)) by (pose proof (Z.log2_spec rest ltac:(lia)) as X; replace (Z.succ (Z.log2 rest)) with (Z.log2 rest + 1) in X by lia; exact X).
  remember (Z.log2 rest) as M eqn:EM in *.
  do 19 (step).
  Ltac rsf_rv n := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end) end.
  time "BR14" ((let v := rsf_rv 14 in lazymatch v with Z_to_bv 64 ?e =>
    replace e with (31 - M) by (clear - HM;
      assert (C : M = 0 \/ M = 1 \/ M = 2 \/ M = 3 \/ M = 4 \/ M = 5 \/ M = 6 \/ M = 7 \/ M = 8 \/ M = 9 \/ M = 10 \/ M = 11) by lia;
      repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity) end)).
  step.
  if_cases K5.
  (rsf_ck K5).
  do 3 (step).
  Ltac rsf_nm n g H X := let v := rsf_rv n in lazymatch v with Z_to_bv 64 ?e => replace e with g by (clear - H;
      assert (C : X = 0 \/ X = 1 \/ X = 2 \/ X = 3 \/ X = 4 \/ X = 5 \/ X = 6 \/ X = 7 \/ X = 8 \/ X = 9 \/ X = 10 \/ X = 11) by lia;
      repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity) end.
  try (rsf_nm 15 (2^M) HM M).
  step.
  if_cases K6.
  { zify_cond K6. eapply K; [exact MU | exact WM | exact MI |].
    assert (RT6 : rs_tail ws (zlen ws) iS = Err 20).
    { unfold rs_tail. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. rewrite CL. cbn [bind].
      try replace (wt =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold highbit32. try replace ((0 <? wt) && (wt <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
      cbn [bind]. try rewrite <- EL. try replace (HUF_TABLELOG_MAX <? L + 1) with false by (symmetry; apply Z.ltb_ge; unfold HUF_TABLELOG_MAX; lia).
      cbn.
      unfold shl32. try replace ((0 <=? L + 1) && (L + 1 <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [bind]. unfold FseNCount.u32. try rewrite Z.mul_1_l. try rewrite PE. try rewrite <- EP. try rewrite (Z.mod_small (2 * P)) by lia. try rewrite (Z.mod_small (2 * P - wt)) by lia. try rewrite <- EREST.
      try replace ((0 <? rest) && (rest <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
      cbn [bind]. try rewrite <- EM. try replace ((0 <=? M) && (M <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [bind]. try rewrite Z.mul_1_l. try rewrite (Z.mod_small (2^M)) by (pose proof (Z.pow_pos_nonneg 2 M ltac:(lia) ltac:(lia)); lia).
      try replace (2^M =? rest) with false by (symmetry; apply Z.eqb_neq; lia).
      reflexivity. }
    rewrite RT6. split; [reflexivity | split; reflexivity]. }
  step.
  if_cases K7; [rsf_ck K7 | ].
  do 4 (step).
  step.
  rewrite (inr64_unsigned_lit (31 - M)) by (unfold inr64; lia).
  replace (32 - (31 - M)) with (M + 1) by lia.
  rewrite (inr64_unsigned_lit (M + 1)) by (unfold inr64; lia).
  replace ((M + 1) ≪ 2) with (4 * (M + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (HLB : (0 <= zlen ws < Z.of_nat (length (map (Z_to_bv 8) ws ++ junk)))%Z) by (rewrite length_app, length_map; lia).
  pose proof (u8arr_store_ok usegs _ HW _ (zlen ws) (wa (HW + zlen ws)) HWA HLB eq_refl) as SOK.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) =>
    let E := addr_expr a in
    assert (HWA2 : u8arr usegs (write_to_mem mx (wa E) bs) HW (map (Z_to_bv 8) (ws ++ [M + 1]) ++ tl junk));
    [ replace (wa E) with (wa (HW + zlen ws)) by (unfold wa; f_equal; lia); rewrite ?le1_lit; apply out_sb; [exact HWA | lia]
    | clear HWA; store_done ]
  end.
  assert (JTL : Z.of_nat (length (tl junk)) = Z.of_nat (length junk) - 1).
  { assert (LTL : forall (l : list byte), (1 <= length l)%nat -> length (tl l) = (length l - 1)%nat)
      by (intros [|a l] H; cbn [tl length] in *; lia).
    rewrite (LTL junk) by lia. lia. }
  remember (map (Z_to_bv 8) (ws ++ [M + 1]) ++ tl junk) as hw2 eqn:EHW2.
  assert (HW2L : Z.of_nat (length hw2) = 256)
    by (subst hw2; rewrite length_app, length_map, length_app; cbn [length]; lia).
  Ltac rsf_chk := let K := fresh "KC" in if_cases K; [rsf_ck K|].
  step. rsf_chk.
  step. rsf_chk.
  pose proof (u32arr_read usegs _ RK (map (Z_to_bv 64) rank1) (M + 1) (Z_to_bv 64 (Znth (M + 1) rank1)) (wa (RK + 4 * (M + 1))) RKA (nth_map_Znth rank1 (M + 1) ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (Forall_Znth _ rank1 (M + 1) RKB ltac:(try unfold zlen in *; lia)) as RKM. cbv beta in RKM.
  step.
  rewrite (sx32_small (Znth (M + 1) rank1)) by lia.
  do 3 (step).
  try rewrite (inr64_unsigned_lit (Znth (M + 1) rank1)) by (unfold inr64; lia).
  assert (HRL : (0 <= M + 1 < Z.of_nat (length (map (Z_to_bv 64) rank1)))%Z) by (rewrite length_map; lia).
  pose proof (u32arr_store_ok usegs _ RK _ (M + 1) (wa (RK + 4 * (M + 1))) RKA HRL eq_refl) as SOK2.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) =>
    let E := addr_expr a in
    assert (RKA2 : u32arr usegs (write_to_mem mx (wa E) bs) RK (map (Z_to_bv 64) (Zupd (M + 1) (Znth (M + 1) rank1 + 1) rank1)));
    [ replace (wa E) with (wa (RK + 4 * (M + 1))) by (unfold wa; f_equal; lia); unfold Zupd; rewrite map_upd_nat; apply u32arr_write; [exact RKA | exact HRL]
    | clear RKA; store_done ]
  end.
  step. rsf_chk.
  step.
  step. rsf_chk.
  remember (Zupd (M + 1) (Znth (M + 1) rank1 + 1) rank1) as rank2 eqn:ERK2.
  assert (RK2L : zlen rank2 = 13) by (subst rank2; rewrite Zupd_length; lia).
  pose proof (Forall_Znth _ rank1 1 RKB ltac:(lia)) as RK1. cbv beta in RK1.
  assert (R1 : 0 <= Znth 1 rank2 <= zlen ws + 1).
  { subst rank2. destruct (Z.eq_dec (M + 1) 1) as [E1|E1].
    - rewrite E1, Znth_Zupd_same by (unfold FseNCount.Zlength; lia). lia.
    - rewrite Znth_Zupd_other by lia. lia. }
  pose proof (u32arr_read usegs _ RK (map (Z_to_bv 64) rank2) 1 (Z_to_bv 64 (Znth 1 rank2)) (wa (RK + 4)) RKA2 (nth_map_Znth rank2 1 ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
  step.
  try rewrite (sx32_small (Znth 1 rank2)) by lia.
  step;
  assert (RTP : forall b, (Znth 1 rank2 <? 2) || (Z.land (Znth 1 rank2) 1 =? 1) = true -> b = true -> rs_tail ws (zlen ws) iS = Err 20).
  { intros b HB _. unfold rs_tail. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. rewrite CL. cbn [bind].
    try replace (wt =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold highbit32. try replace ((0 <? wt) && (wt <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
    cbn [bind]. try rewrite <- EL. try replace (HUF_TABLELOG_MAX <? L + 1) with false by (symmetry; apply Z.ltb_ge; unfold HUF_TABLELOG_MAX; lia).
    cbn.
    unfold shl32. try replace ((0 <=? L + 1) && (L + 1 <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind]. unfold FseNCount.u32. try rewrite Z.mul_1_l. try rewrite PE. try rewrite <- EP. try rewrite (Z.mod_small (2 * P)) by lia. try rewrite (Z.mod_small (2 * P - wt)) by lia. try rewrite <- EREST.
    try replace ((0 <? rest) && (rest <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
    cbn [bind]. try rewrite <- EM. try replace ((0 <=? M) && (M <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind]. try rewrite Z.mul_1_l. try rewrite (Z.mod_small (2^M)) by (pose proof (Z.pow_pos_nonneg 2 M ltac:(lia) ltac:(lia)); lia).
    try replace (2^M =? rest) with true by (symmetry; apply Z.eqb_eq; first [ lia | zify_cond K6; lia ]).
    cbn [negb]. try replace (zlen ws <? HUF_SYMBOLVALUE_MAX + 1) with true by (symmetry; apply Z.ltb_lt; unfold HUF_SYMBOLVALUE_MAX; lia).
    cbn [bind FseNCount.assert]. unfold FseNCount.load, FseNCount.store. try unfold FseNCount.Zlength.
    try replace ((0 <=? M + 1) && (M + 1 <? zlen rank1)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind]. try rewrite (Z.mod_small (Znth (M + 1) rank1 + 1)) by lia. try rewrite <- ERK2.
    try replace ((0 <=? 1) && (1 <? zlen rank2)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind]. try rewrite HB.
    reflexivity. }
  assert (RTO : (Znth 1 rank2 <? 2) || (Z.land (Znth 1 rank2) 1 =? 1) = false ->
    rs_tail ws (zlen ws) iS = Ok (mkHS (ws ++ [M + 1]) rank2 (zlen ws + 1) (L + 1) (iS + 1))).
  { intros HB.
    unfold rs_tail. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. rewrite CL. cbn [bind].
    try replace (wt =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold highbit32. try replace ((0 <? wt) && (wt <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
    cbn [bind]. try rewrite <- EL. try replace (HUF_TABLELOG_MAX <? L + 1) with false by (symmetry; apply Z.ltb_ge; unfold HUF_TABLELOG_MAX; lia).
    cbn.
    unfold shl32. try replace ((0 <=? L + 1) && (L + 1 <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind]. unfold FseNCount.u32. try rewrite Z.mul_1_l. try rewrite PE. try rewrite <- EP. try rewrite (Z.mod_small (2 * P)) by lia. try rewrite (Z.mod_small (2 * P - wt)) by lia. try rewrite <- EREST.
    try replace ((0 <? rest) && (rest <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
    cbn [bind]. try rewrite <- EM. try replace ((0 <=? M) && (M <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind]. try rewrite Z.mul_1_l. try rewrite (Z.mod_small (2^M)) by (pose proof (Z.pow_pos_nonneg 2 M ltac:(lia) ltac:(lia)); lia).
    try replace (2^M =? rest) with true by (symmetry; apply Z.eqb_eq; first [ lia | zify_cond K6; lia ]).
    cbn [negb]. try replace (zlen ws <? HUF_SYMBOLVALUE_MAX + 1) with true by (symmetry; apply Z.ltb_lt; unfold HUF_SYMBOLVALUE_MAX; lia).
    cbn [bind FseNCount.assert]. unfold FseNCount.load, FseNCount.store. try unfold FseNCount.Zlength.
    try replace ((0 <=? M + 1) && (M + 1 <? zlen rank1)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind]. try rewrite (Z.mod_small (Znth (M + 1) rank1 + 1)) by lia. try rewrite <- ERK2.
    try replace ((0 <=? 1) && (1 <? zlen rank2)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind]. try rewrite HB.
    try rewrite (Z.mod_small (zlen ws + 1)) by (unfold HUF_SYMBOLVALUE_MAX in *; lia).
    reflexivity. }
  assert (E1 : forall x, 0 <= x -> Z.land x 1 = x mod 2) by (intros x Hx; change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
  Ltac rsf_ex X KK RT EE := zify_cond X; eapply KK; [eassumption | eassumption | eassumption |]; rewrite (RT true) by (try reflexivity; apply orb_true_iff; first [ left; apply Z.ltb_lt; lia | right; apply Z.eqb_eq; rewrite ?EE in * by lia; Z.div_mod_to_equations; lia ]); split; [reflexivity | split; reflexivity].
  Ltac rsf_br KK RT EE := let KB := fresh "KB" in first [ if_cases KB; [ first [ rsf_ck KB | rsf_ex KB KK RT EE ] | ] | idtac ].
  step. rsf_br K RTP E1.
  do 14 (try (step; rsf_br K RTP E1)).
  match goal with KB1 : bv_ltu (Z_to_bv 64 (Znth 1 rank2)) _ = false |- _ => zify_cond KB1 end.
  match goal with KB2 : negb (bv_eqb (Z_to_bv 64 (Z.land _ 1)) _) = false |- _ => zify_cond KB2 end.
  rewrite ?(inr64_unsigned_lit (Znth 1 rank2)) in * by (unfold inr64; lia).
  assert (HB : (Znth 1 rank2 <? 2) || (Z.land (Znth 1 rank2) 1 =? 1) = false).
  { apply orb_false_iff. split; [apply Z.ltb_ge; lia | apply Z.eqb_neq; rewrite E1 in * by lia; lia]. }
  eapply K; [eassumption | eassumption | eassumption |].
  rewrite (RTO HB). cbn [rres hs_ret hs_weights hs_rank hs_nbSymbols hs_tableLog].
  split; [reflexivity|].
  split; [exists (tl junk); split; [subst hw2; eassumption | lia]|].
  split; [eassumption|].
  split; [eassumption|].
  match goal with H : rw_cells usegs _ TLP [C4 (Z_to_bv 64 ?e)] |- _ =>
    replace e with (L + 1) in H by (rewrite (inr64_unsigned_lit (31 - L)) by (unfold inr64; lia); lia); exact H end.
Qed.
End FIN.
