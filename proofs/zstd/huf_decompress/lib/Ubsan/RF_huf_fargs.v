(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_fa_iface RF_huf_fargs_s.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_fargs () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=testbit_neg_rC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z;shiftr_specK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z<testbit_onesC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z9bits_inj'I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03I46Stdlib;setoid_ring<Ring_polynom3Pol00C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z7add_0_lK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init5Logic6eq_indK46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lorK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit=lor_shift_addC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface>fast_args_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z6eqb_eqI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface<fast_args_okI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2or00C47Corelib5Lists7ListDef5skipnK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib7Numbers7BinNums1Z03C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6ltb_ltC45stdpp9bitvector;definitions5bv_eqC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapK47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=bytes_at_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3>le4_four_bytesC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4K4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC45stdpp9bitvector;definitions8bv_swrapC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>negb_false_iffK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface6jt_lenC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8K4ELinuxProcessSemantics5Riscv3Sem4core01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z9add_assocC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sltC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sltC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s3FAMC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fargs_s5fa_s0C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit28sgtz_andC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9v_slt_b2zc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_fargs<fa_lor_byte2C47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_fargs:fa_desc_tlC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib3Tac?rw_cells_forgetC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop07I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface>fast_args_stmt".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma fa_desc_tl : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 128 ->
  Z.land (a + 256 * b + 65536 * c + 16777216 * d) 16711680 = 65536 * c.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fargs ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with51zh61bi001bh71Hh84__x2h97fv_listh:8hyp_listh;3lmph<1Lh=4__p1h>4__p2h?4__p3h@4__p4hA4__x3hB4__x4hC1yhD1EhE2HahF2HbhG2HchH2HdhI2HihJ2HyhK1ahL2b0hM2b1hN1chO1dhP1ip&0p;1p;2p;3p;4p;6p;7p;8p;:p;<g0000j16Tg000Uj1;Tg0013j23Tg001Oj2<Tg001jj1DTg002Oj2VTg002mR0j22Tg003Jj20Tg003kj21Tg004Ij2]Tg004ck10KTg005Aj2jTg005aj2sTg006>R1j2GTg006[k20=Tg007=j2RTg007Yj2QTg0086R2k308Tg008Zj2TTg0097j2HTg009Wj3KTg00:1j1`Tg00:Qj1ZTg00;1j2UTg00;Ok102Tg00;mk100Tg00<Xj2YTg00=;j2NTg00=^j1xTg00>@j3wTg00>cj2vTg00?Ek20NTg00@1k30MTg00@Pk40LTg00ABj3uTg00Aik10JTg00BIj2kTg00Bfj2tTg00CFR3j27Tg00Ccj3[Tg00DFk40ETg00Dkk10DTg00EIk30CTg00Eoj3qTg00FRk30?Tg00G5k30>Tg00G^j4pTg00HCk30<Tg00Hlk30;Tg00IOk10:Tg00J9j2fTg00JYj2WTg00KCj2eTg00Kmk106Tg00LUk305Tg00M8j6>Tg00MVk404Tg00N7k103Tg00NXj1PTg00O7j2MTg00O`j2aTg00PLj2nTg00Q8j2mTg00Qaj3dTg00RJj3\Tg00Rjj4hTg00SHj3gTg00Skk301Tg00TNj4~Tg00Toj4_Tg00UZj7rTg00V>j8}Tg00Vbk60@Tg00W>j3|Tg00Whk30ATg00XRm:0BTg00YCl<{Tg00Z0j4zTg00ZVk70FTg00[Ej7yTg00[ik60GTg00\Mk30HTg00]6k60ITg00]ZR4f0R5'Rp=?%65#6p>09%65#6#6#6p==f2R6f1R7'T/H5p=Bg00^8R8?K75p=4g00^XR9?K75p=5P9P7g00_6P5C_p=SP7g00_]R:g00`<R;P;g00`\R<P5g00a<R=Frp=Af3R>P:P;P;P<P6P7P5G}p=9g00a\R?9K85p=^P8g00b<R@P>P6P7P5E>p=lP9P7g00b\P5C_p=iP9f4RAP>P6P7P5J0@p=FP6P:P;P;P<P9P7g00cCP5C_P=Frp=:P8PAP>P6P7P5E>p=J1275,76p=8A\975p=EA|975p=@B0A975p=LP9P4P7P3P0P1g00cjR=g00dGRBg00ddRCP5N:0Bp>07P9P4P6P3P0P1P=PBPCg00eERCP7P5M<{p=OP9PBP7P5Czp=cPCPAP>P6P7g00f4P5K0Fp=bP6P:P;P;P<P7P5Fyp=IP7P:P;P;P<P5J0Gp=oB0H975p=CP7P:P;P;P<P5J0Ip=X%?>R:g00fPRC#6RB#6R=#6R1#6R0#6$09R3#6RD#;RE,3>'<RF%;3R3,3>,<:%?5RG%DCRH#D#D#D#D#D#D#=#=#=#=#;RI,V7RJ%=D#=RD#;RK=B7E/2KRL10>710I7'1ABAKE/2K/06,45X681]9I%;1R1$0KRM%;0R0'jRN/5IPNf5RO/0>RP105>RQ'1ABOKE/2K/0>'4X59%;BRR/s0RS=BAERT/j0RU10N>,1P/4QX591G60RQ,0M11P5ABOSE/j0/0>'4X6810TQ1G>0,0M,1P/45X6820=6013601R061Q604081Q>0P8P213A01R0Af8R2f6RP'0RQ1GP0RV,0MRW'11T2SRX/HERY/0VRZ'4P713O0f9R[f7R\'0R]/15AB[SE1G\0R^'0R_'4X68R`145_X68AK8@5X681]8@PZg00g5RZ#`R_%ZZRa1U97Rb&029Rc&009Rd1Y9CRe1N90Rf'S,Ad%x;R;Aw9efRg1N94Rh'S,AdC91vd<R<P5P61]8?R?20N56#^dB0M947H0LRib2b3b4X0913501G70Rj/34[^09P5P\P7O2Rkb1Rl9uYVCl11Q@&0JQClPWAuMVlClW<P5O11R0O1k4V1QV1'1RlP`1t20R`1k4^1Q^1'1RQ,1]R]1H5ER@/0^'4X591V`MRY105^,4]X5910`VRm/1W14]5X68Pl1t[0/0^/15,4]X6817V0Rl,02115Q,4]X68P_PaPbPcA[9gf,ie,AdP<Pib2b3b4X091G50/70,55^09P5P\O1b115PlP\f:Rl/021G20RQ,k41QQ1'1RQ'110l5/1Q'4X591]8]17^0P5DFb7PmP2P0PVP_PaPbPcPdA:dfeP;A:dhgC9P<Pib2b3b4X091R05%?j[^09Pkb1H0EDJPWP_Pa&0D9RkPc1N919:dhP<Pib2b3b4%?1P5b1Rj:0C1VRgDJ10YVAq`MVDJ1sR1,H`B0?`1jDFPXP_PaPkPcA:dhfP<Pib2b3b4%?0P5b1Rf:0>20DFPWPgDJW<P5O1n200210000000021100011000bMbL10U6PTP0P6P_PaPbPcPdA:dheRUP;PUC9P<Pib2b3b4X09%?7Rg\G^09P5P>P6O2b1RWCpDJ10N6PMP0P6PWCpDJ12TSB0<T0fDFPIP5DFb71V>I/07Aq>I7DJXIGXP940;WJXC915JL\G^C9P9A82E\RL12KPRJ'7%=D#=#;RD;8ORf?BKE/2K12K\RT,55X59&0:9R0/f0R0#`RS%Z0R0%`9RW,EP,E\,E2,E[%Z9RMP5P71W9CRN1e9ERX1W9BRj'@'LR`1W9HR11W9=RR,@X'L1e9KRV'@'LRY1@V1,L`1e9D/@R'LRRP?%;CRC0077R1g00ga,f9&069'f#ZRmAOC5YAOC5R'cb;#^dDbb9b:12EORR,7P=8LK/5fRYePYA8[E2RYA8\EPR^;8KR]AB5KE/2K12K2R8'5X59P91TYKRQ/7^12@KR@/58X59RnP9P4175L/HE/2K/58X59P9P^PnPSP01E\W,E2PMP5P71@jX,LNRjP`P?P1PmAOC5jAOC5`'cb;#^dDbb9b:A8\PE/5^R`eP`A82\ER`12K[Rj,5@X59P91H2ER@125K/5jX59RjP9P2PjPSP01E[WPMP5P71@NVRM1@VNRVP?P1PmAOC5MAOC5V'cb;#^dDbb9b:122K/58eP@P_PaPbPcPd1N9ERb,Se,Ad9IdUR@P;P@C9P<Pib2b3b4X09135E,<G137E,<gRg[^09P5P[POO2b1:052EE>1H`EP2P\PEP_PaPkPc1ibh,Ad,odP<Pib2b3b4AK9E4g00hIR`[P5b1H04E>PLP5DFb7174^&03^E>PQg00hfRQ#PRL#PRG,M91M9QRQ'C%PGRG#PR8#P,M9RV,CQg00iERC'a'n1m9ERM1M9GRG5d91M9L/CQRL'C/aC=\Z_5\ZPaP91U96P7PkChPcPd1Y9BRB9:dhRm1SBb,Ad5IdP;PdP@P;Ag9bB9[9eRe9:dh1N9KRB,Se,Ad5IdC9C9P<Pib2b3b4X09X89A86E>Rb#?13bK'<\g\g^09^89P5P[PlPOPPO4b1:01YKE>1T]KPYP^PKP_PaPkPc1iBh,Ad,odP<Pib2b3b4AK9K4P`[P5b1C~E>17YT?8DPP5DFb71VfIP5Pfp-0Rf1m9K=d9V1M989d9M/CG'C,CQ/aC,nL=\Z_PaP9P91U9AP6PkChP71U9>ChPcPd1Y9=R=9:dh1XdP5IdP;Pd1Y9HRH9:dh1Xd\5IdP;Pd1Xd29IdmP;Pd1Xd[9IdUP;Ag9BH9[9e1N9D=g9=5[99:dhC9C9C9C9P<Pib2b3b4X09X89XA9XB9X=fX>fX?fW@1<:A1<:P1<:21<:l17AR/7J?8D\#?[[[[^09^89^A9^B9^=f^>f^?f^@fP513[E132E13\E13P3PPP\P2P[P6P>PAPOO<b1O2E>bDWHXGFXFFWEXO9XN9X69XK9o"). Qed.

(* [comment removed for export] *)
Lemma fa_lor_byte2 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.lor (bv_unsigned (Z_to_bv 8 b1) ≪ 8 mod 18446744073709551616) (bv_unsigned (Z_to_bv 8 b0)) = b0 + 256 * b1.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fargs ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh64__p1h74__x2h82H0h92H1h:2b0h;2b1p;2p;1p;4p;3p;6p;7p;8p100j1p4p7210g00M8R0p4p710p8g007=j2=Tg0000j10Tg000Uj1?Tg0013j28Tg001Oj26Tg005Aj2DTg0097j2>Tg00j]j1VTg00k;j2ATg00kaj2@Tg00lKj27Tg002mj2:Tg00CFj2<Tg005aj2dTg00:1j1`Tg00:Qj1_Tg00;1j2LTg00Dkj1]Tg00Rjj4[Tg00;Oj1ZTg00;mj1YTg00<Xj2KTg00=;j24Tg00lhj3XTg00SHj3CTg00Ccj3JTg00Toj4ETg00>cj2UTg004Ij2TTg00?Ej2STg009Wj3ITg00@1j3RTg00@Pj4QTg00=^j1kTg00]6j6jTg00mKj6iTP0j65Tg00Q8j2hTg00NXj1HTg00O7j2FTg00Qaj3eTg00\Mj3OTg00O`j2MTg00PLj2cTg00RJj3NTg00LUj3aTg00HCj3bTg00nOj2PTg00UZj7fTg00[Ej7^Tg00V>j8gTf0R0#0#0p=\%00#0#0#0p=W%00#0#0#0#0#0#0#0p=1g00^XR1f1R2;I0p=3P2g00_]R3g00`<R4P4g00`\R5P0g00a<Ffp=2P1P2g00cCP0CEp=GP1P2g00_6P0CEp=Bf2R6P3P4P4P5P2P0F^p=;f3R7P3P4P4P5P6P2P0Ggp=9g00]ZR8/=2R9g00fPR:#0R;#\R<#0#WR=#?R>,82'6R?P1P6%?<R@,D0%1=#1#1#1#1#1#1#?R='>%V<R<f4RA,A<'@'71:>7,<ARB'3X51P1P71D7@/>=/70/3BX51P1%?;RC/d@RD,:6RE1>0=/7A/3BX51P1PE170A/3BX51P11<7E130BX51g00g5RB#`RF%_BRGP11L16P2%]1RHC[%Z1RI%Y1RJP11K1:R:1K1;R;141C=X1<RC5C15J1g00b\141>RK=C1;9J1:CE'21UJ5R;P0P6g00^8RLg00a\RM'T1S06=ILMdAR182CQRMb2b3b4X01X711:2DRL,<01:>2,<0'3^01^71P0P7PAO2b117E7P6P@P7PFPGPHPI1418RH141@'G,2JP;PMb2b3b41=8@P0b1RNPFPG1L12ROPIPJ1GH:,2JRP1B:K,2J5;JRK%k4RQ1B:C,2J9;JPC9P;PMb2b3b4X011=80RR180>'6RS182D,69[^01P0PAP6O2RAb1p-0RDPFPGPOPIPJPJP3P4P4P5P7Ej9;JPPQPPC9P;PMb2b3b4X01W616R2P9[^01^6DP0187>P7P2O3b1EiE51>E=1h1>g00hfR>#HRD,F15e11F1>R>5O1g00iER9'M%HD#H,F19O1>/M9,c>=NBF5NBPGPOPIPJPKPQAC1:CRC,GH,2J141=,BC,2J5;JC9P;PMb2b3b4X011=8L18L='6\S^01P0P7P2O2R2b19aE=E51D6@Ab6@NE51A<7,@<PFPGPOPIPJPKPQPKC9P;PMb2b3b4X01RMP?\S^01RSPAb1,P7E51A<6,@<PMPSP2b1,P6E5X9?W8X;1X:1o"). Qed.

(* [comment removed for export] *)
Ltac fa_ret0 r :=
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) => fail | _ => zstep end);
  apply evt_done; unfold fast_args_post; do 14 eexists; exists r; eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [lazymatch goal with RA : rw_cells _ _ ?A _ |- exists _, rw_cells _ _ ?A _ =>
            destruct (rw_cells_forget _ _ _ _ RA) as (j' & RA'); exists j'; exact RA' end|].

Lemma fa_land_le : forall x m, 0 <= x -> 0 <= Z.land x m <= x.
Proof.
  intros x m Hx.
  assert (D : Z.land (Z.land x m) (Z.ldiff x m) = 0).
  { apply Z.bits_inj'; intros k Hk. rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit x k), (Z.testbit m k); reflexivity. }
  assert (X : Z.lxor (Z.land x m) (Z.ldiff x m) = x).
  { apply Z.bits_inj'; intros k Hk. rewrite Z.lxor_spec, Z.land_spec, Z.ldiff_spec.
    destruct (Z.testbit x k), (Z.testbit m k); reflexivity. }
  rewrite <- (Z.add_nocarry_lxor _ _ D) in X.
  assert (0 <= Z.ldiff x m) by (rewrite Z.ldiff_land; apply Z.land_nonneg; left; exact Hx).
  assert (0 <= Z.land x m) by (apply Z.land_nonneg; left; exact Hx).
  lia.
Qed.

Local Ltac land_norm K := repeat match type of K with
  | context [?x ≫ 2] => rewrite (Z.shiftr_div_pow2 x 2) in K by lia; change (2^2) with 4 in K
  | context [Z.land ?x 3] => change (Z.land x 3) with (Z.land x (Z.ones 2)) in K; rewrite (Z.land_ones x 2) in K by lia
  | context [Z.land ?x 7] => change (Z.land x 7) with (Z.land x (Z.ones 3)) in K; rewrite (Z.land_ones x 3) in K by lia
  end.

Local Ltac chk := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 0x1e7b4 else _) _ _ _ _) =>
      let K := fresh "KC" in if_cases K; zify_cond K;
      [exfalso; rewrite ?unsigned_lit in K by lia; rewrite ?zb_lxor_ones in K by lia; land_norm K;
       try (match type of K with context [Z.land ?x ?c] => pose proof (fa_land_le x c ltac:(lia)) end);
       repeat match type of K with context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
       try (simpl Z.b2z in K; match type of K with context [Z.lxor ?a ?b] =>
              let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in K end); lia
      | clear K]
  end.

Local Ltac run := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 0x1e7b4 else _) _ _ _ _) => chk
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1e3a8) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end).

Local Ltac br := let K := fresh "KB" in if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia;
  [ try (exfalso; lia) | try (exfalso; lia) ].

Local Ltac run_ret := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 0x1e7b4 else _) _ _ _ _) => chk
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => br
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end).

Local Ltac fa_close r :=
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned ?sp + -16) _, STK : stk _ _ _ _ |- _ =>
    release_frame FR STK (bv_unsigned sp) end;
  apply evt_done; unfold fast_args_post; do 14 eexists; exists r; eexists;
  split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [ lazymatch goal with RA : rw_cells _ _ ?A _ |- exists _, rw_cells _ _ ?A _ =>
             destruct (rw_cells_forget _ _ _ _ RA) as (j' & RA'); exists j'; exact RA' end |].

Local Ltac fa_ret r := run_ret; fa_close r.

Local Ltac runto pc := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 0x1e7b4 else _) _ _ _ _) => chk
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end).

Section CANSEC1. Context {rc : runConstT}.

Theorem fast_args_proof : fast_args_stmt.
Proof.
  unfold fast_args_stmt, PHUF_FAST_ARGS_INIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         A DST dcap S DT mtl tt tl mtl' src ja lo.
  intros RA A8 DTB MTL TT TLR MTL' SRC BYS NSM S0 D0 DC DL DPOS DT0 DT4 DTL SL STK LOS SP47 ASP A152 MI -> -> -> -> -> ->.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 152)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  carve_frame 16%nat STK.
  run.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (bytes_at_read usegs mm DT _ 0 4 DTB ltac:(lia) ltac:(cbn; lia)) as RDT end.
  change (firstn 4 (skipn (Z.to_nat 0) [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl']))
    with [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl'] in RDT.
  rewrite <- (le4_four_bytes mtl tt tl mtl') in RDT by lia.
  zstep. rewrite sx32_small by lia.
  run.
  let K := fresh "KD" in if_cases K; zify_cond K.
  { apply andb_false_iff in KD. destruct KD as [KD|KD]; apply Z.ltb_ge in KD; [|lia].
    assert (dcap = 0) by lia. subst dcap.
    run. br. fa_ret 0. left; reflexivity. }
  assert (DP : 0 < DST) by (apply DPOS; lia).
  run. br. run.
  let K := fresh "KN" in if_cases K; zify_cond K.
  2: { run_ret. rewrite (fa_z64_mod (-20)). change ((-20) mod 2^64) with (2^64 - 20).
        fa_close (2^64 - 20). right; left; reflexivity. }
  run.
  let K := fresh "KT" in if_cases K; zify_cond K.
  all: rewrite ?unsigned_lit in KT by lia; rewrite fa_desc_tl in KT by lia.
  { fa_ret 0. left; reflexivity. }
  assert (tl = 11) by lia. subst tl.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let rd k := pose proof (src_rd usegs mm S src k SRC ltac:(lia)) in
    rd 0; rd 1; rd 2; rd 3; rd 4; rd 5 end.
  pose proof (byte_Znth src 0 BYS ltac:(lia)). pose proof (byte_Znth src 1 BYS ltac:(lia)).
  pose proof (byte_Znth src 2 BYS ltac:(lia)). pose proof (byte_Znth src 3 BYS ltac:(lia)).
  pose proof (byte_Znth src 4 BYS ltac:(lia)). pose proof (byte_Znth src 5 BYS ltac:(lia)).
  assert (J0 : 0 <= jt_len src 0 < 65536) by (unfold jt_len; change (0 + 1) with 1; lia).
  assert (J2 : 0 <= jt_len src 2 < 65536) by (unfold jt_len; change (2 + 1) with 3; lia).
  assert (J4 : 0 <= jt_len src 4 < 65536) by (unfold jt_len; change (4 + 1) with 5; lia).
  runto 0x1e244. cbv beta. rewrite (fa_lor_byte2 (Znth 0 src) (Znth 1 src)) by lia.
  change (Znth 0 src + 256 * Znth 1 src) with (jt_len src 0).
  runto 0x1e274. cbv beta. rewrite (fa_lor_byte2 (Znth 2 src) (Znth 3 src)) by lia.
  change (Znth 2 src + 256 * Znth 3 src) with (jt_len src 2).
  runto 0x1e29c. cbv beta. rewrite (fa_lor_byte2 (Znth 4 src) (Znth 5 src)) by lia.
  change (Znth 4 src + 256 * Znth 5 src) with (jt_len src 4).
  run.
  let K := fresh "KL" in if_cases K; zify_cond K.
  { fa_ret 0. left; reflexivity. }
  run. let K := fresh "KL" in if_cases K; zify_cond K.
  { fa_ret 0. left; reflexivity. }
  run. let K := fresh "KL" in if_cases K; zify_cond K.
  { fa_ret 0. left; reflexivity. }
  run. let K := fresh "KL" in if_cases K; zify_cond K.
  { fa_ret 0. left; reflexivity. }
  run. let K := fresh "KS" in if_cases K; zify_cond K.
  { run_ret. rewrite (fa_z64_mod (-20)). change ((-20) mod 2^64) with (2^64 - 20).
    fa_close (2^64 - 20). right; left; reflexivity. }
  run.
  run.
  let K := fresh "KO" in if_cases K; zify_cond K.
  { fa_ret 0. left; reflexivity. }
  land_norm KO.
  run.
  rewrite (Z.shiftr_div_pow2 (dcap + 3) 2) in RA by lia. change (2^2) with 4 in RA.
  replace (DST + (dcap + 3) / 4 + (dcap + 3) / 4 + (dcap + 3) / 4) with (DST + 3 * ((dcap + 3) / 4)) in RA by lia.
  replace (DST + (dcap + 3) / 4 + (dcap + 3) / 4) with (DST + 2 * ((dcap + 3) / 4)) in RA by lia.
  lazymatch type of RA with rw_cells _ _ _ [?c0;?c1;?c2;?c3;?c4;?c5;?c6;?c7; CB 56 ?j; ?c15;?c16;?c17;?c18] =>
    apply (rw_cells_split_CB usegs _ _ [c0;c1;c2;c3;c4;c5;c6;c7] 56 j [c15;c16;c17;c18] [8;8;8;8;8;8;8]%nat) in RA;
    [|reflexivity]; cbn [app mk_CB_cells] in RA
  end.
  eapply fa_s0; try eassumption; try lia.
  all: try (unfold FAM; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); eassumption).
Qed.
End CANSEC1.
