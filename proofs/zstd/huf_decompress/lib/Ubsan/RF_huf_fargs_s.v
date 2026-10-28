(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_fargs_s () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool<orb_true_iffK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z8lor_specC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3oddC56Stdlib6ZArith6BinInt1Z8bit0_oddC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6divideK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z:mod_divideC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega:ZMicromega=ZTautoCheckerK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z;pow_nonzeroI46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z9mul_reg_rC56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z4succK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z8even_mulC56Stdlib6ZArith6BinInt1Z:pow_succ_rC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z8negb_oddC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2I47Corelib4Init5Logic2eq00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init5Logic4True00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z3maxK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC47Corelib4Init5Logic5proj2K47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes:comparison00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z7mod_modC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z;log2_nonnegI47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface6jt_lenC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s3FAMK47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C47Corelib5Lists7ListDef3mapK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface>fast_args_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr07C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface<fast_args_okC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission3Lib3Tac?rw_cells_forgetC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface?fast_args_cellsC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_oriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_oriK46Stdlib9micromega:ZMicromega;ZArithProof03c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s7lor1_ltC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllC56Stdlib6ZArith6BinInt1Z9mod_smallc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s=Z_to_bv64_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s;fa_sentinelc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s6fa_finC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit<le64_lbu_rawC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm1C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm2C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm3C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit3nsmC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_aC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_bC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_cK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_dK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s9log2_byteC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteK4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromK4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s5fa_s3K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s5fa_s2c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s5fa_s1".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma fa_sentinel : forall x c, 0 <= x -> 0 <= c <= 8 -> (Z.lor x 1 ≪ c mod 18446744073709551616) mod 512 <> 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fargs_s ()) [] "p'0h04__x1h11zh27__arithh35heq_yh44__ffh58__varmaph65__with71Hh84__p1h92EVh:1Eh;1bi001bh<2b1h=2b2h>1yh?2Hch@2HqhA3Hq'hB2HxhC1OhD1PhE1chF1ehG7fv_listhH8hyp_listhI3lmphJ1qhK1xi011xp&0p;1p;2p;3p;6p;4p;5p;7p;8p;:p;<g0000j13Tg000Uj1=Tg0013j2?Tg001OR0j2TTg001jj28Tg002Gj2HTg002hj2BTg003Ej2aTg003_j2iTg004?j2XTg004Yj3UTg0053k309Tg005Uj67Tg0063j1STg006Pk103Tg0072j6>Tg007Nj24Tg007kR1j20Tg008Hj2;Tg008hj1RTg009Aj2]Tg009aj1QTg00:Aj1GTg00:aj1hTg00;?j1gTg00;]j1fTg00<Hj2ATg00<kj2eTg00=Mj3dTg00=lj4cTg00>^k308Tg00?Bk407Tg00?]j1DTg00@BR2j26Tg00@_R3j2JTg00A<k206Tg00AZk205Tg00B=j3bTg00B`j3_Tg00CCk202Tg00Cok600Tg00DSj1~Tg00E5j5}Tg00EXj4|Tg00F=j1yTg00Fgj2PTg00GGj3MTg00Ggj2OTg00HQj3FTg00I;j1vTg00Icj4uTg00JIj7tTg00K8j5sTg00K[j15Tg00L9j1`Tg00LWj3rTg00M1j2YTg00MSj3qTg00N7j1NTg00NUj1wTg00O7j2pTg00OVj4oTg00P0j4zTg00PVj2nTg00Q6j3{Tg00Q_j3LTg00R9j4VTg00Rdj7mTg00SHk601Tg00Slj7lTg00TPj8kTg00U4m:04Tg00Uel<jTg00VRR4f0R5'?p=Cg00W0R6g00WPR77L5p=1%35#3p=\%35#3#3#3p=[%35#3#3#3#3#3#3#3p=@g00X0R8?L54p=<1X85p=9f1R9=L85p=2P8P9g00XNP5CVp=EP9g00Y5R:g00YTR;P;g00Z4R<P5g00ZTFmp=:P9P:P;P;P<P5J01p=WP8P9g00[4P5CVp=If2R=P:P;P;P<P9P5Flp=^f3R>P:P;P;P<P=P9P5Gkp=KP8P4P9P3P1P2g00[[R?g00\8R@g00\URAP5N:04p=xP8P4P=P3P1P2P?P@PAg00]6RAP9P5M<jp=Z%C9R?g00]eR2#3R1#3R3#3RB#=RC,?9,T?P6%=2RD,8>RE/H4RF%15RGX;6RHP61H>41HD4RI'BPHP01B95#1%1=%19R0'aRJ[1a0G1B=9#1[R01B>=#1\J1i95P5n2001000000120000000X=6X<6RJP0^=6^<6R0P5f4RG/H4RKPI%1K%1I1X67RI3UO3b7PFB09>D4E7%SERF&03EE>%1F18GDP8P8%=1RF/4G,05RE%\B#[RB#3#\#[#@#@#@#@#@#@#=RK,;5%=BRB';#<#RX18P81;EBRL%<5#RX18%<LRLf5RM,4F,09RN/;B#<f6RO,4F,0=RP,]B[1]BNRQ1;PB#<[18ODRP#9129Pg00^JRP#QRR%GPRP%h8RS%g8RT%f8RU1A8B1A84RV'E,:U'W1eU<RWP5P=PIAd849R4Ccb4b5b6%<Bg00_6RX[P5b2b3:08NBP5H07PQg00_SP8f7RQ,4F,0>105BRN'2X18PXP5f9RY,4F,0M/2NP8f:RZ%D3#=R3/6ZR['JR\,4F125BX18f;R]/8DR^#912O^R^eR_P^PRPP20689R`PT1A83Ra20582RbAb8abRa5_8'E,:UPWP5P=PI2025=#1dP4CcR4b4b5b6X081635Rc,J5,23^08P5f<RdO1b2b3123\P8P314F5R\/2BX18%9B163]Re,J]P5E>b714FZ14F['0RfPFPZP[P_P^p-0R[PRPPP`PTPU1IVb,:URgPUP:P;P;P<P>J00R<5^U%~;R;PgCKPWP4b4b5b6X08W8Rg%C5/T9P?[^08^8[R?P51?dCPdPZO3b2b3P_P^PRPPP`PTPU1A8CR^,Ib,:U9^U<R<P;1IVa,:UCKPWP4b4b5b6X08X8[1?5C,T9R_1639#C[^08^8[P5%CdPdPZO3b2b3D}E>12fBPQ14FeRe,0=Rf14F]R:PFP]18dDRh#912QhRheRiPhPRPPPSPT1A8F/EV,:U,WUPWP4b4b5b6%<FPX[P5b2b3PiPhPgP?P5f=Rh/?CPhP]O3b2b3C|P810=B163dRi,4FRS,0>Rj14FdRk'0Rl,25X18P810:eRe10>5/2lX18%y8Rl/PlRl#Q%Gl%Q89M8S9M8k9M8>%G8PAP5P91O82RA1O81R1%D2R2,O8R>5F85F8RkAF8A>=F81R1g00_mR>PI1xD9g00`I,P8%v8'P#GP8P@AZD5kAZD51CubI#1dFtbGbH10=e10f:'2ePBP5E>10Q:P9E7Ds12QfP8Pj%55#1X>818hDRj#9f8Rf/2jRjePjPRPPP`PTAb8^bR^1A8D5_8/Ea,:UPWP4b4b5b6X0816C5/JD/2c^08P5f>RcO1b2b316Cd#`/2iP816ChRi#`Rd10M\#5#1X18P814Fi,0FR\10M5#5#1X18P6%5G%5\'BPHPJP0P5%5MRa16Cc,4FRb,0F#5Rj%1a%1jP6%5FRa%5b'BPHPJP0P5Paf?R0,6C,4F#5RJ%1a%1J;rIO3b7Pj1YFbE73UO3b710G\#51YG\E714Fd18cDRc#912YcRcePcPRPPP`PTPUP<P;1IV^,:UCKPWP4b4b5b6X08X8[16C9#C\_^08^8[P5%C0P0PhO3b2b39qFiE7163hP5E>b7PfP5E7%5f#1P6%5YPHP5%SY#NRH%wYE7%1HP6%SZ%N5#1X;6P5P7P]E>%N7R]#1P6P]P6P[P5PXg00a1n0110000020000XF6P>P7P5E>PX1pX5b7b9b9b9bAbDW@XJ8P9P5O2n2001000000121101000b:W:%RLe1;EK/;BPEPKPBP812KNX18%32#D#D#D#=,4FRF10FB#9CoCzE71n5G18MDRM#9125MRMePMPgP?P51?OCPOPGO3b2b39{5GE7b>bCW?WBXE8XK8o"). Qed.

(* [comment removed for export] *)
Ltac fa_popc P r :=
  let p := eval vm_compute in (P + 12) in zto p; brute_reg 11%Z r 1 255 sm1;
  let p := eval vm_compute in (P + 24) in zto p; brute_reg 11%Z r 1 255 sm2;
  let p := eval vm_compute in (P + 32) in zto p; brute_reg 11%Z r 1 255 sm3;
  let p := eval vm_compute in (P + 36) in zto p; brute_reg 11%Z r 1 255 nsm;
  let p := eval vm_compute in (P + 56) in zto p; brute_reg 11%Z r 1 255 (fun r0 => pc_a (nsm r0));
  let p := eval vm_compute in (P + 76) in zto p; brute_reg 11%Z r 1 255 (fun r0 => pc_b (pc_a (nsm r0)));
  let p := eval vm_compute in (P + 84) in zto p; brute_reg 11%Z r 1 255 (fun r0 => pc_c (pc_b (pc_a (nsm r0))));
  let p := eval vm_compute in (P + 104) in zto p; brute_reg 11%Z r 1 255 (fun r0 => pc_d (pc_c (pc_b (pc_a (nsm r0)))));
  let p := eval vm_compute in (P + 108) in zto p; brute_reg 11%Z r 1 255 (fun r0 => 31 - Z.log2 r0);
  let p := eval vm_compute in (P + 112) in zto p; brute_reg 11%Z r 1 255 (fun r0 => Z.log2 r0);
  let p := eval vm_compute in (P + 120) in zto p; brute_reg 11%Z r 1 255 (fun r0 => 8 - Z.log2 r0).

Lemma lor1_lt : forall x, 0 <= x < 2^64 -> 0 <= Z.lor x 1 < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fargs_s ()) [] "p'0h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with66__sat1h71ah81bh91Eh:2Hxh;1Ph<1Qh=1Hh>2Hah?4__p2h@6__sat0hA1si001shB1xhC1NhD1ei011ehE1zi021np;1p;2p;4p;3p;6p;9p;5p;7p;8g0000j19Tg000Uj1?Tg007Nj2KTg00aMj20Tg001OR0j23Tg001jj24Tg00aij2VTg009aj1TTg00:Aj1LTg00A<j2JTg00;?j1ITg00;]j1HTg00<Hj2<Tg00AZj2fTg00R9j4;Tg00DSj1XTg00<kj2WTg004?j2DTg00CCj2UTg00Q_j3CTg00=Mj3STg00=lj4BTg00bMj2@Tg008hj1:Tg00bmR1j2ATg00cMj2MTg00:aj1NTg00d3j2OTg00d[j3PTg00e?j2QTg00SHj6RTg00e`j17Tg00f>j3GTg00fdj2gTg0013j2FTg005Ul9ej6\Tg00gAj1dTg00g_j3cTg00?Bj4`Tg00hBj5_Tg00hfj4]Tg00iHj4[Tg00icj4^Tg00Rdj7ZTg00Coj6aTg00Slj7bTg00TPj8YTg00VRR2f0R3'Fp=2f1R4g00Y5R5g00YTR6P6g00Z4R7P3g00ZTFZp=8P4P5P6P6P7P3Eap=Ef2R8P5P6P6P7P4P3Fbp==f3R9P5P6P6P7P8P4P3GYp=5g00X0R:?C32p=11023p=6P:P4g00j>P3C;p=>%23R;g00]eR<#9R=#?R>%9=#9#9#9#9R=#?R?'KR@,03RA'3RBP01443RC#2%28%24RD'3RE[13D;1484RF#2[RG1498#2\E1V43P3n2001000000120000000X8:X7:PG^8:^7:P3P8%?<RGp-0REg00^JRH#TRI%LHRH1J:4RJ%I:RK%H:RLP:1<:2RMg00[4RN1f:<R<C;,8LRO1EL9RP5=LRQ%X6RRP:PMPN1<:GRNC;,8LRS9=LOC51WL7RTP3P8g00W0RUg00WPRV'DRW1U38=CUVdAS:24RVCBRUb3b4b5X1:W013;4R;%2GRX,3D[^1:^0EP3109@P9P8O3b2O3b=144G#2RY148GRZ#210Z@P31@Z2%1ZR[%:['AP1149GR[#1R\%:\f4R\/4GR]#6P3%1]R^P0%1C%18RC%14R0'3[R_%13R`,30%1FRF[%19R0/3C\F1M43P4n2001000000120000000X8:X7:P_^8:^7:P3f6R_PGP4O3%1_%1GRF'3PIPH%N:RCPKPL1EL8P:PNg00XNRNPMC;,8L5=LPRPPC5PTPUb3b4b5X0EX?E133FP8[^0E^?EP3f8RF/4G#6%1FP4O3b2b9b=W9P3O1%:^1O>?R^%6>RF%2?%6@Ra[Rb[Rc%2>Rdg00a1ReAP>?4UW>Rf%2@\e^>dRdP4g00je1Q2>'DRePFeO1PbPIPHPJPKPLPLP5P6P6P7P:P<PNPMC;,8LERRNPRPLPOPR1>M<,8LR7C5C5PTPUb3b4b5X1:g00_6\`R`%68R6\D[^1:P3f9R5/4GP\f7RFO3b2b6b@b6W9P3O1n200110000021010111102bA%6ZRZ10[@%7]/0?[%7[Rg/0?10]@[AG[?3P:%79R[%7GR]'g103?XE:P[P]P?1@92%:0,A0P1%1\R1%:1f5R1#7/0?P3%11R0P:P210[?^<Z^;Y^:BXB:1F22/3a142GRa#2%6aPIPHPCPK1<:?,>M,8LPTPUb3b4b5%6?P3b2RM%72/0?eW<W;W:P_P3P1P\P9M9eWDP3O1%:010_@%7F/0?[%7_/0?10F@[P^PcPfPdP4PeO1PbPIPHPJPKPLPNPRPLPQPRP7C5C5PTP3P8PWPVCBb3b4b5X1:X0E13D8P6[\`^1:^0EP3f:R`/0@P`P\P5O4b2b6b@b69G_?PIPHPJPKPL1<:>%d=5c:,><,8LR<9=LPPRP<C5PTPUb3b4b5X1:X0E134A104@[^1:^0EP3%2FPFP_O3b2C`WCP3O1n200110000021010111102bAPM10]?eD_PgP9PGPIPHPJPKPLPQPRPOC5PTPUb3b4b5X1:X0EPD\;^1:^0EP310\@P\P9O3b2PIPHPCPKPSPTPUb3b4b5PXP3b2C]E\C[b<C^b;W:XB:o"). Qed.

Lemma Z_to_bv64_mod : forall x, Z_to_bv 64 x = Z_to_bv 64 (x mod 18446744073709551616).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fargs_s ()) [] "h01zh12b1h22b2h31nh41Hh57__arithh64__ffh78__varmaph85__with91xp;1p;3p;2p;4p;7p;6p100kKp4p7210g005UR0p4p710p8g00l7j15Tg00Q_j31Tg00lZj23Tg00mDj3=Tg0000j10Tg00gAj1CTg00mhj27Tg000Uj16Tg008Hj24Tg007Nj2<Tg004?j2;Tg009aj1MTg00:Aj1LTg00:aj1JTg00;?j1ITg00;]j1HTg00<Hj2:Tg00R9j4BTg00Rdj7ATg00SHj6@Tg00<kj2?Tg00CCj2DTg00=Mj3ETg00=lj4FTg00nNj3GTP0j68Tg00noj19Tf0R0#0#0#0#0p=K%00#0p=>%00#0#0#0#0#0#0#0p=2g00X0R1g0100R2%50R3f1R4#5R5g001Of2R6#5?140f3R7/361374511R8[13641360511%57?164[R9f4#5?176\8A=640P0n2001000000120000000W2W1W3P9^25^13^32P0g00]e#0R2#0#KR3#CR51754R9%>3#2#2#2#2#2#2#2#6R8,44R7,75R:P1%62%63'<R3,441468R2,75,359110X01P114731463=110X01P1P7A1120X011;171478g00^JR2#M%L2%J1%I1%H1R2g00Y5R3g00YTR;P;g00Z4R<P2P3P;P;P<P11:18g00XNg00VRR;,:1CBg00ZTFAE@1?2<P0P6g00W0R<g00WPR2';1D06=1<2dAE1;4CFb6b7b8A118;g00_6[P0b59G48E8135:%97E81359%94E8O4b4W9o"). Qed.

Lemma log2_byte : forall r, 1 <= r < 256 -> 0 <= Z.log2 r <= 7.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fargs_s ()) [] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with61Hh72H0h82Hrh91rp;1p;2p;6p;3p;4p;7p;8g000Uj15Tg0013j24Tg0000j11Tg00aMj20Tg001Oj29Tg010Nj1STg00e`j16Tg007Nj2MTg009aj1DTg00:Aj1CTg00A<j2BTg00;?j1@Tg00;]j1?Tg00<Hj23Tg00AZj2TTg00Coj6RTg00DSj1NTg00<kj2LTg004?j2KTg00=Mj3ETg00=lj4<Tg00f>j3FTg00gAj1GTg00g_j3HTg00CCj2ITg00Q_j3JTg00?Bj4ATg00?]j1=Tg00R9j4>Tg00Rdj7OTg00Slj7PTg00TPj8QTg00X0R0f1R1g00[4f0R2C>p=;P1g00Y5R3g00YTR4P4g00Z4R5P2g00ZTFOp=2f2R6P3P4P4P5P1P2FPp=:P0P1g00j>P2C>p=8f3R7P3P4P4P5P6P1P2GQp=7g00]eR8#5R9/42R:%18R;#1#1R<#1#1#1#1#1#5R=,02R>'9%S1g00VRR?%61'4%5;R;%5<R@'MRA,06%67/0@[%66/0@RB107A[p-0RCg00^JRD#DRE%CDRD1B01RF%@0RG%?0RH13091T08RI';,2HPHP3P4P4P5P7ERR35:H%N4R4130?RJ/8I,2HC71LH5R5P2P6g00W0RKg00WPRL'KRMAE0?1RNC<b3b4b5X00W119:110?1[^00^1CP2107=P7P6O3b29F6@PEPDPFPGPH130=,8I,2H9:H3P4130;%G<5H0,8I,2HC7P5P2P6PM1I26=JKLdPNC<RNb3b4b5X00X1C191>101A[^00^1CP21497P7P6O3b2CAPBPEPDPFPGPH130@,8I,2HP4PH1;JI,2HRJP4%=8#=#5R8,30,;I,2H9:HJC7C7P5PNb3b4b5X00102@14?114?61468'9[[^00P2f4#6P1P6O3b2b7b6W8X90o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section FAS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (A DST dcap S DT tl lo : Z) (src : list Z).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation L1 := (jt_len src 0).
  Notation L2 := (jt_len src 2).
  Notation L3 := (jt_len src 4).
  Notation SEG := ((dcap + 3) / 4).
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S0 : 0 < S.
  Hypothesis SL : S + n <= lo.
  Hypothesis LOS : lo <= SP - 16.
  Hypothesis ASP : SP <= A.
  Hypothesis A152 : A + 152 <= 2^64.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis DL : DST + dcap < 2^64.
  Hypothesis SG : 3 * SEG < dcap.
  Hypothesis TL11 : tl = 11.
  Hypothesis H1 : 8 <= L1.
  Hypothesis H2 : 8 <= L2.
  Hypothesis H3 : 8 <= L3.
  Hypothesis H4 : L1 + L2 + L3 + 6 + 8 <= n.

  Notation W := [(SP - 16, SP); (A, A + 152)].
  Notation POST := (fast_args_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A DST dcap S DT src tl lo m0).

  (* [comment removed for export] *)
  Notation FAC c64 c72 c80 c88 c96 c104 c112 :=
    [ C8 (Z_to_bv 64 (S + 6 + L1 - 8)); C8 (Z_to_bv 64 (S + 6 + L1 + L2 - 8)); C8 (Z_to_bv 64 (S + 6 + L1 + L2 + L3 - 8));
      C8 (Z_to_bv 64 (S + n - 8));
      C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + SEG)); C8 (Z_to_bv 64 (DST + 2 * SEG)); C8 (Z_to_bv 64 (DST + 3 * SEG));
      c64; c72; c80; c88; c96; c104; c112;
      C8 (Z_to_bv 64 (S + 6)); C8 (Z_to_bv 64 (S + 6 + L1)); C8 (Z_to_bv 64 (S + 6 + L1 + L2));
      C8 (Z_to_bv 64 (S + 6 + L1 + L2 + L3)) ].

  (* [comment removed for export] *)
  Definition FAM (mm : fmem) (cs : list cell) : Prop :=
    rw_cells usegs mm A cs /\ rw_cells usegs mm (SP + -16) [C8 s1; C8 s0] /\ stk usegs mm lo (SP + -16)
    /\ bytes_at usegs mm S (map (Z_to_bv 8) src) /\ mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm.

  Lemma fa_z64_mod : forall x, Z_to_bv 64 x = Z_to_bv 64 (x mod 2^64).
  Proof. intros x. exact (Z_to_bv64_mod x). Qed.

  Lemma fa_sentinel64 : forall x c, 0 <= x -> 0 <= c <= 8 -> (Z.lor x 1 ≪ c) mod 2^64 mod 512 <> 0.
  Proof. intros x c Hx Hc. exact (fa_sentinel x c Hx Hc). Qed.

  Local Ltac chk := lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 0x1e7b4 else _) _ _ _ _) =>
        let K := fresh "KC" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia | clear K]
    end.

  Local Ltac nonneg_lor := repeat match goal with
    | |- 0 <= Z.lor _ _ => apply Z.lor_nonneg; split
    | |- 0 <= ?a mod ?b => pose proof (Z.mod_pos_bound a b ltac:(lia)); lia
    | |- 0 <= bv_unsigned ?w => pose proof (bv_unsigned_in_range _ w); lia
    end.

  Local Ltac wto pc := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 0x1e7b4 else _) _ _ _ _) => chk
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
    | _ => zstep end).

  Local Ltac fam_close := unfold FAM; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); eassumption.

  Local Ltac fa_stream mm BY P0 OFF NXT :=
    zstep; zstep; zstep; chk;
    pose proof (src_rd usegs mm S src (OFF + 7) BY ltac:(lia)) as R7;
    zstep;
    let RB := fresh "RB" in
    pose proof (byte_Znth src (OFF + 7) BYS ltac:(lia)) as RB;
    let r := fresh "r" in
    remember (Znth (OFF + 7) src) as r eqn:ER;
    zstep; let K := fresh "KZ" in if_cases K; zify_cond K; rewrite (byte_lit _ RB) in K;
    [ idtac | fa_popc P0 r ];
    (let rd k := pose proof (src_rd usegs mm S src (OFF + k) BY ltac:(lia)) in
     rd 0; rd 1; rd 2; rd 3; rd 4; rd 5; rd 6; rd 7);
    wto NXT.

  Local Ltac fa_sent :=
    lazymatch goal with
    | RB : 0 <= ?r < 256, K : ?r = 0 |- _ => apply fa_sentinel64; [nonneg_lor|]; rewrite (byte_lit _ RB); lia
    | RB : 0 <= ?r < 256, K : ?r <> 0 |- _ => pose proof (log2_byte r ltac:(lia));
        apply fa_sentinel64; [nonneg_lor|]; rewrite (Z.mod_small (8 - Z.log2 r)) by lia; rewrite Z.mod_small by lia; lia
    end.

  Local Ltac s3_tail mm BY :=
    let rd k := pose proof (src_rd usegs mm S src (n - 8 + k) BY ltac:(lia)) in
    rd 0; rd 1; rd 2; rd 3; rd 4; rd 5; rd 6; rd 7;
    zto 0x1e77c.

  (* [comment removed for export] *)
  Lemma fa_fin : forall mm b0 b1 b2 b3 j88 j96 j104 j112 (t0 t1 t2 x8 x9 a2 a4 a5 t3 t4 t5 t6 : word),
    FAM mm (FAC (C8 (Z_to_bv 64 b0)) (C8 (Z_to_bv 64 b1)) (C8 (Z_to_bv 64 b2)) (CB 8 j88) (CB 8 j96) (CB 8 j104) (CB 8 j112)) ->
    b0 mod 2^64 mod 512 <> 0 -> b1 mod 2^64 mod 512 <> 0 -> b2 mod 2^64 mod 512 <> 0 -> b3 mod 2^64 mod 512 <> 0 ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 A) (Z_to_bv 64 b3) a2
                           (Z_to_bv 64 S) a4 a5 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap))
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1e77c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros FM M0 M1 M2 M3.
    destruct FM as (CA & CS & ST & BY & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 9 zstep.
    release_frame CS ST (bv_unsigned sp).
    apply evt_done. unfold fast_args_post. do 14 eexists. exists 1. eexists.
    split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [destruct (rw_cells_forget _ _ _ _ CA) as (j' & CA'); exists j'; exact CA'|].
    right; right; split; [reflexivity|].
    unfold fast_args_ok. split; [exact TL11|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [lia|].
    exists (b0 mod 2^64), (b1 mod 2^64), (b2 mod 2^64), (b3 mod 2^64).
    repeat (split; [apply Z.mod_pos_bound; lia|]). repeat (split; [assumption|]).
    unfold fast_args_cells. rewrite <- (fa_z64_mod b0), <- (fa_z64_mod b1), <- (fa_z64_mod b2), <- (fa_z64_mod b3). exact CA.
  Qed.

  (* [comment removed for export] *)
  Lemma fa_s3 : forall mm b0 b1 b2 j88 j96 j104 j112 (t0 t1 t2 x8 x9 a1 a5 t3 t4 t5 t6 : word),
    FAM mm (FAC (C8 (Z_to_bv 64 b0)) (C8 (Z_to_bv 64 b1)) (C8 (Z_to_bv 64 b2)) (CB 8 j88) (CB 8 j96) (CB 8 j104) (CB 8 j112)) ->
    b0 mod 2^64 mod 512 <> 0 -> b1 mod 2^64 mod 512 <> 0 -> b2 mod 2^64 mod 512 <> 0 ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 A) a1 (Z_to_bv 64 (S + n - 8))
                           (Z_to_bv 64 S) (Z_to_bv 64 (S + n)) a5 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap))
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1e690) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros FM M0 M1 M2.
    pose proof FM as FM'. destruct FM' as (CA & CS & ST & BY & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    zstep. zstep. zstep. chk.
    pose proof (src_rd usegs mm S src (n - 1) BY ltac:(lia)) as R7.
    zstep.
    pose proof (byte_Znth src (n - 1) BYS ltac:(lia)) as RB.
    remember (Znth (n - 1) src) as r eqn:ER.
    zstep. let K := fresh "KZ" in if_cases K; zify_cond K; rewrite (byte_lit _ RB) in K.
    - s3_tail mm BY. eapply fa_fin; [exact FM|assumption..|]. fa_sent.
    - fa_popc 0x1e6a4 r. s3_tail mm BY. eapply fa_fin; [exact FM|assumption..|]. fa_sent.
  Qed.

  (* [comment removed for export] *)
  Lemma fa_s2 : forall mm b0 b1 j80 j88 j96 j104 j112 (t1 t2 x8 x9 a1 t3 t4 t5 t6 : word),
    FAM mm (FAC (C8 (Z_to_bv 64 b0)) (C8 (Z_to_bv 64 b1)) (CB 8 j80) (CB 8 j88) (CB 8 j96) (CB 8 j104) (CB 8 j112)) ->
    b0 mod 2^64 mod 512 <> 0 -> b1 mod 2^64 mod 512 <> 0 ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp (Z_to_bv 64 (S + 6 + L1 + L2 + L3)) t1 t2 x8 x9 (Z_to_bv 64 A) a1
                           (Z_to_bv 64 (S + n - 8)) (Z_to_bv 64 S) (Z_to_bv 64 (S + n)) (Z_to_bv 64 (S + 6 + L1 + L2 + L3 - 8))
                           (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1e598) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros FM M0 M1.
    pose proof FM as FM'. destruct FM' as (CA & CS & ST & BY & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    fa_stream mm BY 0x1e5ac (6 + L1 + L2 + L3 - 8) 0x1e690.
    all: eapply fa_s3; [fam_close|assumption|assumption|fa_sent].
  Qed.

  (* [comment removed for export] *)
  Lemma fa_s1 : forall mm b0 j72 j80 j88 j96 j104 j112 (x8 x9 a1 t3 t4 t5 t6 : word),
    FAM mm (FAC (C8 (Z_to_bv 64 b0)) (CB 8 j72) (CB 8 j80) (CB 8 j88) (CB 8 j96) (CB 8 j104) (CB 8 j112)) ->
    b0 mod 2^64 mod 512 <> 0 ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp (Z_to_bv 64 (S + 6 + L1 + L2 + L3)) (Z_to_bv 64 (S + 6 + L1 + L2 - 8))
                           (Z_to_bv 64 (S + 6 + L1 + L2)) x8 x9 (Z_to_bv 64 A) a1
                           (Z_to_bv 64 (S + n - 8)) (Z_to_bv 64 S) (Z_to_bv 64 (S + n)) (Z_to_bv 64 (S + 6 + L1 + L2 + L3 - 8))
                           (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1e4a0) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros FM M0.
    pose proof FM as FM'. destruct FM' as (CA & CS & ST & BY & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    fa_stream mm BY 0x1e4b4 (6 + L1 + L2 - 8) 0x1e598.
    all: eapply fa_s2; [fam_close|assumption|fa_sent].
  Qed.

  (* [comment removed for export] *)
  Lemma fa_s0 : forall mm j64 j72 j80 j88 j96 j104 j112 (x8 x9 a1 t5 t6 : word),
    FAM mm (FAC (CB 8 j64) (CB 8 j72) (CB 8 j80) (CB 8 j88) (CB 8 j96) (CB 8 j104) (CB 8 j112)) ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp (Z_to_bv 64 (S + 6 + L1 + L2 + L3)) (Z_to_bv 64 (S + 6 + L1 + L2 - 8))
                           (Z_to_bv 64 (S + 6 + L1 + L2)) x8 x9 (Z_to_bv 64 A) a1
                           (Z_to_bv 64 (S + n - 8)) (Z_to_bv 64 S) (Z_to_bv 64 (S + n)) (Z_to_bv 64 (S + 6 + L1 + L2 + L3 - 8))
                           (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                           (Z_to_bv 64 (S + 6 + L1 - 8)) (Z_to_bv 64 (S + 6 + L1)) t5 t6)
                       F (Z_to_bv 64 0x1e3a8) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros FM.
    pose proof FM as FM'. destruct FM' as (CA & CS & ST & BY & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    fa_stream mm BY 0x1e3bc (6 + L1 - 8) 0x1e4a0.
    all: eapply fa_s1; [fam_close|fa_sent].
  Qed.

End FAS.
End CANSEC1.
