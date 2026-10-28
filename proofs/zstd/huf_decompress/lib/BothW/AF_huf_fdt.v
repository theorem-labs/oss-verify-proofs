(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_pure RF_huf_fdw_fm RF_huf_fdw_st.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AProg_kit ABytes AKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fdw_seg AF_huf_fdw_top1 AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_fdt_defs AF_huf_fdt_f.
Ltac2 kr_t_AF_huf_fdt () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8dt_cellsC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_tableLogK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land63_modC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land64_modC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm3lbfC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm9lbf_rangeC56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt4lbfAK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:decode_symK47Corelib4Init9Datatypes4prod01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_bitsc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt7ftA_invc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt5ftA_KC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm8fdec_invC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_symbolC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_nbBitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dc_newStateC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_contI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC47Corelib4Init3Nat3mulI47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List6concatC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model@fse_cells_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit<zshadow_appWK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4chkZC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbK4ELinuxProcessSemantics5Riscv5Instr5instr06C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit7acc_shZC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit;cell_rd_symC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'I47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit6out_sbC46Stdlib5Lists4List2tlC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm7zlen_tlC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit>unsigned_byte'C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6bd_ptrC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_zeroK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HII5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface>fse_cell_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop02C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4sxb0C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit?unpoisoned_appWC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4chkBC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4svalC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit=le64_lbu_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9land7_modK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBsigned_lit_small64C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8sxb_svalC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit5le64vC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdK4ELinuxProcessSemantics5Riscv5Instr5aluop09K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp>reload_dstreamC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface7bitd_okK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z6leb_leC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8readLE64C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit;readLE64_okC47Corelib4Init5Logic7f_equalK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt7ftA_ld1C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land32_modC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge?zb_shl_shr_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC56Stdlib6ZArith6BinInt1Z6leb_gtC57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppC56Stdlib6ZArith6BinInt1Z;lt_ge_casesK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus00K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus01K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountKZSTD_error_dstSize_tooSmallK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus04K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes:comparison01c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt7ftA_ld2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlC5ARocqVerifyHarness?AgentSubmission6Common7SFModel<mod64_land63C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6de_outC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s1C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_bdC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dstatus_eqbC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s2c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt:ftlA_body2I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec00c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt=ftA_loop_stmtC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_st6res_okC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit:cell_rd_nsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit:cell_rd_nbC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC46Stdlib5Lists4List9app_assocc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt6ftA_x2C5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_stBdecode_sym_not_errK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:C5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_st<reload_factsK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec01c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt=ftailA_loop_Sc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt7bd_regFc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt6ftA_c2c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt6ftA_r2C5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_st>reload_not_errC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_tbl_kit8zx16_litC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9tail_loopK4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K46Stdlib9micromega5Tauto4kind02C5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2;AZEROFILLEDc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt6ftA_x1c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt6ftA_h2c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdt6ftA_r1C47Corelib4Init9Datatypes7nat_ind".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Section CANSEC1. Context {rc : runConstT}.

Section FTA.
  Variables (RNG : footprint) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (x8 x18 x19 : word).
  Variables (m0 : amem) (SP1 S0 DT DST dcap : Z) (bs : list Z) (d : dtable).
  Variable Q : machine_state -> Prop.
  Notation tl := (dt_tableLog d).
  Notation TB := (DT + 4).
  Hypothesis HTL : 5 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells d) = 2^tl.
  Hypothesis HCOK : RF_huf_fdw_sm.cells_ok tl (dt_cells d).
  Hypothesis TBB : bytes_at bsegs m0 TB (concat (map fse_cell_bytes (dt_cells d))).
  Hypothesis FRT2 : rw_cells bsegs m0 (SP1 + 56) [C8 (Z_to_bv 64 TB)].
  Hypothesis HDT : ablk DT (DT + 4 + 4 * 2^tl).
  Hypothesis HDST : ablk DST (DST + dcap).
  Hypothesis DST3 : 3 <= DST.
  Hypothesis DC : 0 <= dcap <= 255.
  Hypothesis SPB : ATOP + 4096 <= SP1 /\ SP1 + 120 <= 2^47.
  Hypothesis DJ1 : DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST.
  Hypothesis ZDT : zshadow m0 DT (4 + 4 * 2^tl).
  Hypothesis ZDST : zshadow m0 DST dcap.
  Hypothesis RDT : rng RNG DT (4 + 4 * 2^tl).
  Hypothesis RDTs : rng RNG (shad DT) (nshad (4 + 4 * 2^tl + DT mod 8)).
  Hypothesis RDST : rng RNG DST dcap.
  Hypothesis RDSTs : rng RNG (shad DST) (nshad (dcap + DST mod 8)).
  Hypothesis RFR : rng RNG (SP1 + 48) 72.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.

  (* [comment removed for export] *)
  Notation WFT := [(SP1 + 80, SP1 + 88); (DST, DST + dcap)].
  Hypothesis AWD : appW WFT.
  Hypothesis SRC : bytes_at bsegs m0 S0 (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis HS0 : ablk S0 (S0 + zlen bs).
  Hypothesis S16 : 16 <= S0.
  Hypothesis USRC : unpoisoned m0 S0 (S0 + zlen bs).
  Hypothesis RS : rng RNG S0 (zlen bs).
  Hypothesis RSs : rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)).
  Hypothesis DJ2 : DST + dcap <= S0 \/ S0 + zlen bs <= DST.
  Hypothesis FRST : rw_cells bsegs m0 (SP1 + 104) [C8 (Z_to_bv 64 S0)].
  Hypothesis FRSH : rw_cells bsegs m0 (SP1 + 16) [C8 (Z_to_bv 64 2147450880)].
  Hypothesis FRDS : rw_cells bsegs m0 (SP1 + 8) [C8 (Z_to_bv 64 DST)].
  Hypothesis RFR0 : rng RNG (SP1 + 8) 24.

  (* [comment removed for export] *)
  Notation FTS pc mm xra t0 t3 t4 t5 t6 a0 a1 a2 a3 a4 a7 s4 s5 s6 s7 s9 s10 :=
    (MS (mkR xra (Z_to_bv 64 SP1) gp tp t0 (Z_to_bv 64 TB) (Z_to_bv 64 64) x8 (Z_to_bv 64 SP1) a0 a1 a2 a3 a4 (Z_to_bv 64 (-70))
             (Z_to_bv 64 (S0 + 8)) a7 x18 x19 s4 s5 s6 s7 (Z_to_bv 64 (DST + dcap - 2)) s9 s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation TX mm a5v y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 :=
    (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 x8 (Z_to_bv 64 SP1) y10 y11 y12 y13 y14 (Z_to_bv 64 a5v) y16 y17 x18 x19
             y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
        FR (Z_to_bv 64 0x960b8) fc None mm (seg_rom bsegs)).

  Ltac zbnd := unfold ABIT_MASK; rewrite ?land64_mod; rewrite ?Z.shiftl_mul_pow2 by lia; (try change (2^2) with 4);
    rewrite ?Z.mod_small by lia; lia.

  (* [comment removed for export] *)
  Ltac zck r ZS0 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch ?W m0 mm |- _ =>
    let v := reg_val r in
    lazymatch v with Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880) =>
      let RDB := fresh "RDB" in
      pose proof (chkZ mm _ _ a (zshadow_appW W m0 mm _ _ ZS0 MU AWD ltac:(unfold ABIT_MASK; lia) ltac:(unfold ABIT_MASK; lia)) ltac:(zbnd) ltac:(zbnd)) as RDB;
      zstep; rewrite ?sxb0; clear RDB
    end end end.

  Ltac pregs := let v5 := reg_val 5%Z in let v6 := reg_val 6%Z in let v7 := reg_val 7%Z in let v12 := reg_val 12%Z in
    let v13 := reg_val 13%Z in let v11 := reg_val 11%Z in let v17 := reg_val 17%Z in let v21 := reg_val 21%Z in
    let v10 := reg_val 10%Z in let v14 := reg_val 14%Z in let v20 := reg_val 20%Z in
    let v22 := reg_val 22%Z in let v23 := reg_val 23%Z in let v26 := reg_val 26%Z in let v27 := reg_val 27%Z in
    let v28 := reg_val 28%Z in let v29 := reg_val 29%Z in let v30 := reg_val 30%Z in let v31 := reg_val 31%Z in
    let v1 := reg_val 1%Z in
    idtac "ra=" v1 " t0=" v5 " t1=" v6 " t2=" v7; idtac " a0=" v10 " a1=" v11 " a2=" v12 " a3=" v13 " a4=" v14 " a7=" v17;
    idtac " s4=" v20 " s5=" v21 " s6=" v22 " s7=" v23 " s10=" v26 " s11=" v27; idtac " t3=" v28 " t4=" v29 " t5=" v30 " t6=" v31;
    lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mm _) => idtac " pc=" pc " mem=" mm end.

  Lemma le1_zxbS : forall b, le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b))) = [Z_to_bv 8 b].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdt ()) ["CANSEC1"; "FTA"] "h02Hah11zh21Hh37__arithh44__ffh57__sat20h67__sat21h77__sat22h87__sat23h97__sat24h:7__sat25h;7__sat26h<8__varmaph=5__with>1bh?4cstrh@5cstr0hA1lp;1p;2p;3p;4p;7p;6p;8p10000p4p710p1000Mp4p710p8p1000ip4p7210g001UR0p4p710p8g0023j10Tg002Xj1ETg0036j1OTg003Yj1LTg0049j29Tg004_j2VTg005Ij1DTg005ij3Cj2Aj1NTg006Ij36Tg006cj2:Tg007=j2eTg007cj15Tg008Aj2>Tg008^j22Tg009>j1XTg00:<j1UTg00;2j2=Tg00;Nj14Tg00<3j2TTg00<Nj1STg00=Rj2HTg00>2j1BTg00>Wj1ITg00?7j2;Tg00?hj2@Tg00@Pj2<Tg00@lj3FTg00APj1PTg00BWj1QTg00C5j1MTg00CSj1RTg00D>j2JTg00Daj4dTg00ELj7cTg00F0j6bTg00FTj2_Tg00G6j2^Tg00Gbj3]Tg00HAj4\Tg00I3j3[TP0j6?Tg00ITj2ZTg00JCj3YTg00K<j8KTg00KYj1`Tg00LIj1aTf0R0#0#0p=7%40#4p=W%40#4#4#4p=3%00#0#0#0p=G%00#0#0#0#0#0#0#0p=8g00MGR1/=0p=1g00MeR2g00NCR3#0R4#7R5#ER6#OR7#LR81960R9,V6R:,96R;%D7R<5C7f1R=,96=C7<9680XA8P8P81A7;1A79P<P<P7P8\8R>%N7R?P?P;P9P>\7/:?P21e60R?%54R7%55R>'>R9,20R;12=9562X12P2%05#7R5#7#5R@,20RA12=@9620X121:2A12A@p,2rcRA#X%W3#3#3#3R3#0#3#3#0#7#G#8#8#5%UARA'=%43#3#3#0#7#G#8#8#5,=A'Tg00Nhp,1dRA#S'HR3#B%I3#1p,2bs,H2R3#B%I3#1p,2S0R3/;>%13%1>RB123>#1[[%34#5R4,@71<17R3%141>74RC,<1[[%17RDg00OkREAF74=UW0%1C\E^0D%PARA,@7%1A1>7ARC,<1[\3AF7A=VEX0D%1C\E^0Dp,3DSTRD/;>%1D12D>#1\B[p,2DTRD/;>%1D12D>#1\B[g00PGRB#D%LB%Q2%M2%R2RBg00Q3RDg00QRR>P>g00R2REPBPDP>P>PEP21J2@g00RR1J21Cdg00S9FcEb1_BEP0f2REg00SYRBg00T9R>':1^0E=6B>dA]21=C\b4b<b=A62@1g00TY[P0b3b5b6b7b8b9b:b;b@b?b29[0@E?12?9=62;eP:1Z60E?9Y:0GK1:8<GK%E5/9:#`%a:E?W>o"). Qed.

  (* [comment removed for export] *)
  Ltac osbA OUTA LJ :=
    let SOK := fresh "SOK" in
    lazymatch type of OUTA with u8arr _ ?mm ?D (map (Z_to_bv 8) ?o ++ ?j) =>
    pose proof (u8arr_store_ok bsegs mm D _ (zlen o) (wa (D + zlen o)) OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) eq_refl) as SOK;
    zstep;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    end;
    rewrite ?le1_zxbS, ?le1_lit;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
      let OUT2 := fresh "OUTA" in
      pose proof (RF_huf_fdw_kit.out_sb bsegs mm D o j v OUTA ltac:(lia)) as OUT2;
      let LO2 := fresh "LO" in
      assert (LO2 : zlen (o ++ [v]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
      let LJ2 := fresh "LJ" in
      assert (LJ2 : zlen (List.tl j) = dcap - zlen (o ++ [v])) by (rewrite RF_huf_fdw_sm.zlen_tl by lia; lia);
      clear OUTA LJ; store_done; rename OUT2 into OUTA; rename LJ2 into LJ
    end end.

  (* [comment removed for export] *)
  Ltac tb_now :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch WFT m0 mm, DJT : disjoint_from _ TB _ |- _ =>
      let TB1 := fresh "TB1" in pose proof (bytes_at_transport bsegs _ m0 mm _ _ TBB MU DJT) as TB1
    end end.

  (* [comment removed for export] *)
  Lemma lbfA : forall c b nb, 0 <= c < 2^64 -> 0 <= b < 2^31 ->
    Z.land (c ≪ Z.land b 63) 18446744073709551615 ≫ Z.land (Z.land (bv_swrap 32 (0 - nb)) 18446744073709551615) 63
    = RF_huf_fdw_fm.lbf c b nb.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdt ()) ["CANSEC1"; "FTA"] "h01zh12Hbh22Hch31bh41ch52nbp;2p;1p;3p;6g00;2j2ITg0023j10Tg007cj17Tg008Aj2ATg00@Pj2>Tg00<3j2=Tg00;Nj11Tg00U6j23Tg00UTj29Tg008^j22Tg002Xj1HTg00V4j2@Tg00VQj2?Tg00W8j24Tg006Ij38Tg006cj2FTg00WXj1<Tg001Uj6:Tg00X\j1;Tg00Y`j3DTf0R0#0#0#0#0p=C%10#1#1#1p=E%00#0p=B%00#0#0#0#0#0#0#0p=5%10#1p=G%10#1#1#1#1#1#1#1p=6g00MeR1g00MGR2f2R3'IR4g00NCR5#0R6#7R7%C6R6#0R8#7R9'A,>3'=%E5R5#7,A7,>3,=4P1f4R4f3R7%15R5#7R:'3R;'9R<%B8#5#5#5#5#5#5#5#7R8'2%H6R61@27'?R=%G5#6#6#6#6#6#6#6#7R5'3/3:R>,40f5R?1249'9/28R@12=8/29'4R=581X01P11279RA19?0/28/4>=81=X01P11@23,?6R6/28R2130:,4@=81=X01P11229R914@0=81=X01194A/28/49,F1132:%<2E:1365R2%;6E:P;%<7E:13<5R5%;<E:132:,45AD473581eW1W2X51X31W4o"). Qed.

  Lemma lbfA2 : forall c b nb, 0 <= c < 2^64 -> 0 <= b < 2^31 ->
    Z.land (Z.land (c ≪ Z.land b 63) 18446744073709551615 ≫ Z.land (Z.land (bv_swrap 32 (0 - nb)) 18446744073709551615) 63)
           18446744073709551615
    = RF_huf_fdw_fm.lbf c b nb.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdt ()) ["CANSEC1"; "FTA"] "h02Hah14__x1h21Hh37__arithh44__ffh57__sat20h67__sat21h77__sat22h87__sat23h97__sat24h:7__sat25h;7__sat26h<7__sat27h=7__sat28h>7__sat29h?7__sat30h@8__varmaphA5__withB4cstrhC5cstr0hD1zhE2HbhF2HchG1bhH1chI2nbp;1p;2p;3p;6p;4p;5p;7p;8g0023j10Tg007cj14Tg008Aj2=Tg00@Pj23Tg00<3j26Tg00Y`j3HTg00;Nj12Tg00U6j27Tg006Ij3BTg008^j2;Tg00Z\j3^Tg00[^j3\Tg00X\j1[Tg001Uj6JTg00UTj2YTg002Xj1@Tg00V4j2XTg00VQj2WTg00W8j2VTg009>j1UTg00:<j1TTg00;2j2>Tg00<Nj1QTg00=Rj2FTg00>2j1ETg00>Wj1DTg00?7j2?Tg00?hj2:Tg00@lj3<Tg00APj1PTg005Ij1OTg003Yj1RTg00\Aj2STg00C5j1iTg00CSj1hTg00D>j2NTg00\_j2gTg00Daj4CTg00]Bj3LTg00]ej1fTg00FTj2]Tg006cj2_Tg00G6j2`Tg00Gbj3aTg00HAj4bTg00^Gj5cTg00ELj7dTg00_Aj7eTg00_ej8ZTg00MGR0f0R1'>p=1%01#0p=8%21#2#2#2p=I%21#2#2#2#2#2#2#2p=5%01#0#0#0#0#0#0#0p=j%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=9%01#0#0#0p=Gf1R2g00Q3R3g00QRR4P4g00R2R5P1g00S9Fdp=Af2R6P3P4P4P5P2P1Fep=Kf3R7P3P4P4P5P6P2P1GZp=Mg00MeR3%16R8g00NCR9#0R:#4R;%8:R<#8R=#0R>#4R?'=R@,36'6%I9RA#4RB,=;RC,36,68P3f4R8?H76RD%2ARE#2#5RF#2#5RG#5#5#5#5#5#4RH,71f5?H87RI5B3XD3P3%8>#j#9#9#9#4RJ,;DAB31IXD3A^8769\DJ17DH%[DEJ%4ERE,77,Y8/7H%@=1X06'W/7H/7E'VP8P7P6p,2rcR7#UR8%0F#5#0#8#G#9#4%T7R7'>%0G#8#G#9#4,>7'6R7g00Nhp,1dRG#Q'FRF#ERE%DF#1RFp,2bs,F3RH#ER=%DH#1RHp,2S0RD%4<R<'?RJ%1D%1<RI1;D<#1[[RD%I:#4R:,:;RK130;RL%1:1=;:RM,30[[RN%1;ROg00OkRPA<;:2UW0R:%1M\P^0ORM%PGRG,:;RQ%1G1=;GRR,30[\LRSA<;G2VPX0ORG%1R\P^0ORR1:;?RT%1?130@[\LRUA<;?2VPX0OR?%1@\P^0ORV1:;BRW%1B130C[\LRLA<;B2VPX0ORB%1C\P^0OROp,3DSTRP/?<RX%1P1;P<#1\I[RPp,2DTRY/?<RZ%1Y1;Y<#1\I[RIg00PGRY#OR<%RYRY1S32R[%i3R\%h3R]P31N30g00`I1g39R9CC,A]R^P3P9g00a0R_1N3;R;%@>5L3CC,A]5K]R>%f4R4P>CM1]]5R5P1P6g00SYR>g00T9R`'_1`16=B>`dAa302CbR0b4b@bAX13%11R`131@'6%12R>132@'6[^13P1fCf@O2b3b5b6b7b8b9b:b;b<b=b>b?bCbBb2P8P7PEPFP=PHPJPDPKPNP:PMPQPSPGPRPWPLPBPOPTPUP?PVPXPPPZPIP<PYP[P\P]P3P9P_%@A9L3;CC,A]9K]^R^P4P^CMP5P0b4b@bAX13131C,6`132C,6>[^13P1fBf?O2b3b5b6b7b8b9b:b;b<b=b>b?bCbBb2DcEJWEWFXI3XG3WHo"). Qed.

  Definition ftlA_body2 (f : nat) (out1 : list Z) (s1a s2 : Z) (d1r : bitD) : res (list Z) :=
    if dcap - 2 <? FseNCount.Zlength out1 then Err ZSTD_error_dstSize_tooSmall
    else
      let! q2 := decode_sym d true s2 d1r in let '(o1, s2a, d2) := q2 in
      let! r2 := reload_dstream bs d2 in let '(st2, d2r) := r2 in
      if dstatus_eqb st2 Overflow then
        let! q3 := decode_sym d true s1a d2r in let '(o2, _, _) := q3 in
        Ok (out1 ++ [o1; o2])
      else tail_loop bs d dcap true f (mkDec (out1 ++ [o1]) s1a s2a d2r).

  Lemma ftailA_loop_S : forall f x, tail_loop bs d dcap true (Datatypes.S f) x =
    if dcap - 2 <? FseNCount.Zlength (de_out x) then Err ZSTD_error_dstSize_tooSmall
    else
      let! q1 := decode_sym d true (de_s1 x) (de_bd x) in let '(o0, s1a, d1) := q1 in
      let! r1 := reload_dstream bs d1 in let '(st1, d1r) := r1 in
      if dstatus_eqb st1 Overflow then
        let! q2 := decode_sym d true (de_s2 x) d1r in let '(o1, _, _) := q2 in
        Ok (de_out x ++ [o0; o1])
      else ftlA_body2 f (de_out x ++ [o0]) s1a (de_s2 x) d1r.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdt ()) ["CANSEC1"; "FTA"] "p'0h01fh12q1i002q1h22q2i012q2h32r1i022r1h41xi031bi042d1i053d1ri062o0i072o1i081pi093s1ai0:3st1i0;1zp;1p;2p;4p;3p;5g003Yj1FTg00bYj1ETg0023j1;Tg007cj16Tg00V4j2DTg04Nhj12Tg04Ojj2<Tg03ZZj2:Tg03hkj29Tg00b9R0j21Tg04Pej17Tg04Qfj18Tg00cRj44Tg03f^j2CTg04Rgj2@Tg04Snj1>Tg005Ij1=Tg005ij30Tg0211j35Tg00e8j2?Tg04?4j43Tg04Toj5ATg006cj2BTg02f;g04Uog00MeR1#FR2#ER3g00SYR4P3p,4dcapg00NC#;#6'Df0R5#2,<1':g04Ch,921111R6g02cXR7'1R8P2p,1dR9g00T9R:%75%85C4P0P6P7P3P5P0P1P1P3f1R;g04@YR</17R=P2p,2bsf2'CP0P<P7P3P5P4P3g04E7,@;P8P2P9P:f8R:#>R9P5C4P0P6P7P3P5P0P1P1P3P;f=#2f9R3%=1R0901;501551,?2n200110800012010710;n2001101000120108103X28C3P3%2:f4=010551f3P9P5DAn0100000020000n200110200012010:105X3=C3n2001108000120106109n2001100000120108104X18C3n0100000020000'BW4W0o"). Qed.

  (* [comment removed for export] *)
  Definition bd_regF (d0 : bitD) : Z := if bd_zero d0 then AZEROFILLED else S0 + bd_ptr d0.
End FTA.

Section FTB.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
            (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte).
  Notation SP1 := (SPAf SPV).
  Notation tl := (dt_tableLog d).
  Notation TB := (DT + 4).
  Notation TBC := (concat (map fse_cell_bytes (dt_cells d))).
  Notation FRC := [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)].
  Hypothesis STK0 : stk bsegs m0 lo SP1.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SP1 - DEC_STACK.
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPH : SPV + 16 <= 2^47.
  Hypothesis ZOBJ : zshadow m0 (SP1 + 80) 72.
  Hypothesis RO : rng RNG (SP1 + 80) 72.
  Hypothesis ROs : rng RNG (shad (SP1 + 80)) 9.
  Hypothesis RO32 : rng RNG (SP1 + 32) 32.
  Hypothesis HTL : 5 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells d) = 2^tl.
  Hypothesis HCOK : RF_huf_fdw_sm.cells_ok tl (dt_cells d).
  Hypothesis FM : dt_fastMode d = 1.
  Hypothesis HDT : ablk DT (DT + 4 + 4 * 2^tl).
  Hypothesis DT4 : DT mod 4 = 0.
  Hypothesis TBB : bytes_at bsegs m0 TB TBC.
  Hypothesis ZDT : zshadow m0 DT (4 + 4 * 2^tl).
  Hypothesis RDT : rng RNG DT (4 + 4 * 2^tl).
  Hypothesis RDTs : rng RNG (shad DT) (nshad (4 + 4 * 2^tl + DT mod 8)).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis NS : zlen bs <= 65536.
  Hypothesis HS0 : ablk S0 (S0 + zlen bs).
  Hypothesis S8 : S0 + 8 <= 2^47.
  Hypothesis S16 : 16 <= S0.
  Hypothesis USRC : unpoisoned m0 S0 (S0 + zlen bs).
  Hypothesis RS : rng RNG S0 (zlen bs).
  Hypothesis RSs : rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)).
  Hypothesis RESOK : dres_ok (decompress_usingDTable bs d dcap true).
  Hypothesis DC : 0 <= dcap <= 255.
  Hypothesis HDST : ablk DST (DST + dcap).
  Hypothesis DST3 : 3 <= DST.
  Hypothesis ZDST : zshadow m0 DST dcap.
  Hypothesis RDST : rng RNG DST dcap.
  Hypothesis RDSTs : rng RNG (shad DST) (nshad (dcap + DST mod 8)).
  Hypothesis DJ2 : DST + dcap <= S0 \/ S0 + zlen bs <= DST.
  Hypothesis DJ1 : DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST.
  Hypothesis DJ3 : S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^tl <= S0.
  Hypothesis MI0 : mem_inv bsegs m0.
  Hypothesis RTC : artcells m0.
  Hypothesis ZMK : zshadow m0 ABIT_MASK 128.
  Hypothesis RSTK : rng RNG lo (SP1 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Notation W0 := [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].
  Notation R := (decompress_usingDTable bs d dcap true).
  Hypothesis K : forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       munch W0 m0 m1 -> wmono bsegs m0 m1 ->
       mem_inv bsegs m1 -> stk bsegs m1 lo SP1 -> rw_cells bsegs m1 (SP1 + 80) [CB 72 j48'] -> rw_cells bsegs m1 (SP1 + 32) FRC ->
       dresA DST dcap R m1 rv -> 0 <= rv < 2^64 ->
       evtF bsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 rv)
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
                  y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             FR (Z_to_bv 64 0x98318) fc None m1 (seg_rom bsegs)).

  (* [comment removed for export] *)
  Notation ftA_inv := (AF_huf_fdt_defs.ftA_inv m0 SPV FF DST dcap S0 DT lo bs d).
  Notation ftA_f1_stmt := (AF_huf_fdt_defs.ftA_f1_stmt RNG Q m0 SPV FF DST dcap S0 DT lo bs d gp tp FR fc).
  Notation ftA_f2_stmt := (AF_huf_fdt_defs.ftA_f2_stmt RNG Q m0 SPV FF DST dcap S0 DT lo bs d gp tp FR fc).

  (* [comment removed for export] *)
  Notation HD mm x j i x1 x13 x14 x20 x21 x22 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (bd_regF S0 (de_bd x))) x13 x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (bd_cont (de_bd x))) x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 (bd_bits (de_bd x))))
        FR (Z_to_bv 64 0x992dc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation P1 mm x j i x1 x13 x14 x22 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (bd_regF S0 (de_bd x))) x13 x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (bd_cont (de_bd x))) (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1))
             x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 (bd_bits (de_bd x))))
        FR (Z_to_bv 64 0x99380) fc None mm (seg_rom bsegs)).
  Notation P2 pc mm x j i x1 x12 x14 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (DST + dcap - 2)) x12 (Z_to_bv 64 (bd_regF S0 (de_bd x))) x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (bd_cont (de_bd x))) (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1))
             (Z_to_bv 64 (S0 + 8)) x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 (bd_bits (de_bd x))))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FN pc mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation RSt pc mm x j i q p' b' x1 x14 x19 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (S0 + q)) (Z_to_bv 64 (S0 + p')) x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1))
             (Z_to_bv 64 (S0 + 8)) x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 b'))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation RSu pc mm x j i p' b' x1 x12 x14 x19 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (DST + dcap - 2)) x12 (Z_to_bv 64 (S0 + p')) x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1))
             (Z_to_bv 64 (S0 + 8)) x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 b'))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation RSt2 pc mm x j i q p' b' x1 x14 x19 x20 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (S0 + p')) (Z_to_bv 64 (S0 + q)) x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 (Z_to_bv 64 (DST + j + i + 1))
             (Z_to_bv 64 (S0 + 8)) x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 b'))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation RSu2 pc mm x j i p' b' x1 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 i) (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (S0 + p')) x13 x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 b'))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition ftA_loop_stmt (f : nat) : Prop :=
    forall x mm jp junk (j i : Z) (x1 x13 x14 x20 x21 x22 x23 x24 x25 x26 : word),
      tail_loop bs d dcap true f x = R -> bitd_ok bs (de_bd x) -> bd_bits (de_bd x) <= 2^29 ->
      Forall (fun c => 0 <= c < 256) (de_out x) ->
      zlen (de_out x) = j + i -> zlen (de_out x) <= dcap - 2 -> 0 <= j -> 0 <= i ->
      ftA_inv mm x jp junk ->
      evtF bsegs RNG Q (HD mm x j i x1 x13 x14 x20 x21 x22 x23 x24 x25 x26).

  Ltac fappW := unfold appW; repeat (apply Forall_cons; [cbn [fst snd]; unfold KHIGH, KLOW; lia |]); apply Forall_nil.
  Ltac ftA_lin :=
    pose proof atop_range as ATR; pose proof (spaf_props SPV SP16) as (SPAB & SPA32);
    pose proof (ablk_lin _ _ HDT) as (HDTa & HDTb & HDTc & HDTd);
    pose proof (ablk_lin _ _ HDST) as (HDSa & HDSb & HDSc & HDSd); pose proof (ablk_lin _ _ HS0) as (HSa & HSb & HSc & HSd);
    unfold AIMG_HI in HDTa, HDSa, HSa; unfold DEC_STACK in LO.

  (* [comment removed for export] *)
  Lemma ftA_cb : forall mm x jp junk, ftA_inv mm x jp junk -> exists j, rw_cells bsegs mm (SP1 + 80) [CB 72 j].
  Proof.
    intros mm x jp junk I. destruct I as (_ & _ & _ & _ & _ & _ & H1 & H2 & _).
    assert (H : rw_cells bsegs mm (SP1 + 80)
                  ([C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)]
                   ++ bitdz_cellsA S0 (de_bd x) jp)).
    { apply (proj2 (ABytes.rw_cells_app bsegs mm (SP1 + 80) _ _)). split; [exact H1|].
      cbn [cells_size csize]. replace (SP1 + 80 + Z.of_nat (8 + (8 + (8 + (8 + 0))))) with (SP1 + 112) by lia. exact H2. }
    destruct (rw_cells_forget bsegs mm _ _ H) as [j Hj]. exists j. exact Hj.
  Qed.

  (* [comment removed for export] *)
  Lemma ftA_art : forall m, munch W0 m0 m -> wmono bsegs m0 m -> artcells m.
  Proof.
    intros m MU WM. ftA_lin. pose proof RTC as A0. unfold artcells in A0 |- *.
    repeat match type of A0 with _ /\ _ => let H := fresh "AC" in destruct A0 as [H A0] end.
    repeat match goal with |- _ /\ _ => split end;
      (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [disjoint_from cells_size csize]; lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma ftA_err : forall mm x jp junk e (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    ftA_inv mm x jp junk -> R = Err e -> 0 < e < 120 ->
    evtF bsegs RNG Q
      (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 (- e))
               y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
               y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          FR (Z_to_bv 64 0x98318) fc None mm (seg_rom bsegs)).
  Proof.
    intros mm x jp junk e y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 I RE E.
    destruct (ftA_cb mm x jp junk I) as [j CB].
    destruct I as (MU & WM & MI & STK & _ & FRC1 & _).
    replace (Z_to_bv 64 (- e)) with (Z_to_bv 64 (2^64 - e))
      by (apply Z_to_bv_eqm; replace (2^64 - e) with (- e + 1 * 2^64) by lia; rewrite Z.mod_add by lia; reflexivity).
    eapply (K mm (2^64 - e) j); try eassumption.
    - rewrite RE. unfold dresA. split; [reflexivity | lia].
    - lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ftA_ok : forall mm x jp junk (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    ftA_inv mm x jp junk -> R = Ok (de_out x) -> zlen (de_out x) <= dcap ->
    evtF bsegs RNG Q
      (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 (zlen (de_out x)))
               y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
               y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          FR (Z_to_bv 64 0x98318) fc None mm (seg_rom bsegs)).
  Proof.
    intros mm x jp junk y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 I RE L.
    destruct (ftA_cb mm x jp junk I) as [j CB].
    destruct I as (MU & WM & MI & STK & _ & FRC1 & _ & _ & OUT & LJ & _).
    eapply (K mm (zlen (de_out x)) j); try eassumption.
    - rewrite RE. unfold dresA. split; [reflexivity | exists junk; split; assumption].
    - lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ftA_inv0 : forall m x jp junk,
    munch W0 m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m lo SP1 ->
    rw_cells bsegs m (SP1 + 32) FRC ->
    rw_cells bsegs m (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)] ->
    rw_cells bsegs m (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
    u8arr bsegs m DST (map (Z_to_bv 8) (de_out x) ++ junk) -> zlen junk = dcap - zlen (de_out x) ->
    bytes_at bsegs m S0 (map (Z_to_bv 8) bs) ->
    ftA_inv m x jp junk.
  Proof.
    intros m x jp junk MU WM MI STK FRC1 FO BD OUT LJ SRC1.
    ftA_lin.
    assert (AW : appW W0) by (pose proof HDST as HDSx; unfold ablk, KLS, AIMG_HI in HDSx; fappW).
    pose proof (ftA_art m MU WM) as ART.
    assert (TBL : zlen TBC = 4 * 2^tl) by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (TB1 : bytes_at bsegs m TB TBC)
      by (eapply bytes_at_transport; [exact TBB | exact MU | cbn [disjoint_from]; rewrite TBL; lia]).
    assert (Z1 : zshadow m (SP1 + 80) 72) by (eapply zshadow_appW; [exact ZOBJ | exact MU | exact AW | lia | lia]).
    assert (Z2 : zshadow m DT (4 + 4 * 2^tl)) by (eapply zshadow_appW; [exact ZDT | exact MU | exact AW | lia | lia]).
    assert (Z3 : zshadow m DST dcap) by (eapply zshadow_appW; [exact ZDST | exact MU | exact AW | lia | lia]).
    assert (Z4 : zshadow m ABIT_MASK 128)
      by (eapply zshadow_appW; [exact ZMK | exact MU | exact AW | unfold ABIT_MASK; lia | unfold ABIT_MASK; lia]).
    assert (U1 : 0 < zlen bs -> unpoisoned m S0 (S0 + zlen bs))
      by (intros NZ; eapply unpoisoned_appW; [exact USRC | exact MU | exact AW | lia | lia]).
    exact (conj MU (conj WM (conj MI (conj STK (conj ART (conj FRC1 (conj FO (conj BD (conj OUT (conj LJ
             (conj SRC1 (conj TB1 (conj Z1 (conj Z2 (conj Z3 (conj Z4 U1)))))))))))))))).
  Qed.

  (* [comment removed for export] *)
  Ltac fzl :=
    repeat match goal with H : ?T |- _ =>
      lazymatch type of T with Prop =>
        lazymatch T with
        | _ <= _ => fail | _ < _ => fail | _ = _ :> Z => fail | _ <= _ <= _ => fail | _ <= _ < _ => fail
        | _ => clear H end end end;
    Z.div_mod_to_equations; lia.
  Ltac fzdec :=
    repeat match goal with
    | |- context [?a =? ?b] =>
        first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; fzl)
              | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; fzl) ]
    | |- context [?a <? ?b] =>
        first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; fzl)
              | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; fzl) ]
    end.
  Ltac fzbr :=
    unfold zx32; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?bv_lts_zero_r, ?bv_lts_zero_l, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?land64_mod, ?Z.shiftl_mul_pow2 by lia; try change (2 ^ 2) with 4;
    rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8;
    repeat match goal with |- context [?a mod 2 ^ ?k] =>
      rewrite (Z.mod_small a (2 ^ k)) by fzl end;
    fzdec; vm_compute; reflexivity.
  Ltac br :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false; [cbv iota | symmetry; fzbr]
            | replace c with true; [cbv iota | symmetry; fzbr] ] end.
  Ltac ftA_zx := repeat match goal with
    | |- context [Z.lxor ?x ?y <? 1] =>
        replace (Z.lxor x y <? 1) with false by
          (symmetry; apply Z.ltb_ge;
           assert (0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); split; intro; Z.div_mod_to_equations; lia);
           assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; Z.div_mod_to_equations; lia); lia)
    end.
  Ltac ftA_norm := repeat match goal with
    | |- context [Z.shiftl ?x 3] => replace (Z.shiftl x 3) with (x * 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia)
    | |- context [Z.land ?x ?M] =>
        lazymatch M with Zpos _ => idtac end;
        replace (Z.land x M) with x
          by (first [change M with (Z.ones 64) | change M with (Z.ones 32)]; rewrite Z.land_ones by lia;
              symmetry; apply Z.mod_small; Z.div_mod_to_equations; lia)
    | |- context [bv_swrap 32 ?x] => rewrite (SysStep.swrap32_small x) by (Z.div_mod_to_equations; lia)
    | |- context [bv_wrap 32 ?x] =>
        replace (bv_wrap 32 x) with x
          by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; symmetry; apply Z.mod_small; Z.div_mod_to_equations; lia)
    end.

  Ltac ftA_acc := lazymatch goal with
    | |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?a 3 + _), 1%nat) =>
        match goal with H : rng R (shad ?A) (nshad (?len + ?A' mod 8)) |- _ =>
          constr_eq A A'; apply (acc_shZ R A len a H); lia end
    | |- acc_in ?R (Z_to_bv 64 ?E, _) =>
        first [ let X := leftmost E in
                match goal with H : rng R ?lo _ |- _ => let Y := leftmost lo in constr_eq X Y; solve_acc_with H end
              | match goal with H : rng R _ _ |- _ => solve_acc_with H end ]
    | |- acc_in ?R _ => match goal with H : rng R _ _ |- _ => solve_acc_with H end
    end.
  Local Ltac acc_hint ::= first [ bdtA_acc_hint | ftA_acc ].

  Ltac pc_in P1 P2 := lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
    | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) =>
    let b := eval vm_compute in (orb (Z.eqb (bv_unsigned pc) P1) (Z.eqb (bv_unsigned pc) P2)) in
    lazymatch b with true => idtac end end.
  Ltac wto P1 P2 := repeat (tryif pc_in P1 P2 then fail else first [ zstep | br ]).
  Local Tactic Notation "wton" int_or_var(n) constr(P1) constr(P2) :=
    do n (tryif pc_in P1 P2 then idtac else first [ zstep | br ]).
  Ltac pcq := lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac "PCIF"
    | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) =>
      let v := eval vm_compute in (bv_unsigned pc - 0x98160) in idtac "PC" v end.
  Ltac wtr n P1 P2 := lazymatch n with
    | O => idtac
    | Datatypes.S ?k => tryif pc_in P1 P2 then idtac else
        (pcq; tryif first [ zstep | br ] then wtr k P1 P2 else idtac "STUCK") end.
  Ltac pcp := lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac "PCIF"
    | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) =>
      let v := eval vm_compute in (bv_unsigned pc - 0x98160) in idtac "PC" v end.

  (* [comment removed for export] *)
  Lemma ftA_e : forall (m : amem) (x : dec) (jp junk : list byte)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    (forall f, ftA_loop_stmt f) ->
    tail_loop bs d dcap true (Datatypes.S (Z.to_nat dcap)) x = R ->
    bitd_ok bs (de_bd x) -> bd_bits (de_bd x) <= 2^29 -> zlen (de_out x) <= dcap -> Forall (fun c => 0 <= c < 256) (de_out x) ->
    munch W0 m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m lo SP1 ->
    rw_cells bsegs m (SP1 + 32) FRC ->
    rw_cells bsegs m (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)] ->
    rw_cells bsegs m (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
    u8arr bsegs m DST (map (Z_to_bv 8) (de_out x) ++ junk) -> zlen junk = dcap - zlen (de_out x) ->
    bytes_at bsegs m S0 (map (Z_to_bv 8) bs) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) x10
               x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + zlen (de_out x)))
               (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
               x26 (Z_to_bv 64 2147450880) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x99288) fc None m (seg_rom bsegs)).
  Proof.
    intros m x jp junk x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31
      LOOP TLX BOK BB LOUT FOUT MU WM MI STK FRC1 FO BD OUT LJ SRC1.
    pose proof (ftA_inv0 m x jp junk MU WM MI STK FRC1 FO BD OUT LJ SRC1) as I.
    ftA_lin.
    pose proof I as Ik.
    destruct Ik as (MU' & WM' & MI' & STK' & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    wto 0x992dc 0x98318.
    destruct (Z.ltb_spec (dcap - 2) (zlen (de_out x))) as [LT|GE].
    - br. wto 0x992dc 0x98318.
      assert (RE : R = Err ZSTD_error_dstSize_tooSmall)
        by (rewrite <- TLX, ftailA_loop_S; unfold FseNCount.Zlength; rewrite (proj2 (Z.ltb_lt _ _) LT); reflexivity).
      eapply (ftA_err m x jp junk ZSTD_error_dstSize_tooSmall); [exact I | exact RE | unfold ZSTD_error_dstSize_tooSmall; lia].
    - br. wto 0x992dc 0x98318.
      unfold bitdz_cellsA in BD2. wto 0x992dc 0x98318.
      rewrite (AKit.sx32_lit (bd_bits (de_bd x))) by (destruct BOK as (_ & HB & _); lia).
      pose proof (LOOP (Datatypes.S (Z.to_nat dcap)) x m jp junk (zlen (de_out x)) 0
                    x1 x13 x14 x20 (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25 x26
                    TLX BOK BB FOUT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) I) as HL.
      unfold mkR, bd_regF in HL. replace (DST + dcap - 2) with (DST + dcap + -2) in HL by lia.
      let v := eval vm_compute in (2^61) in change (2^61) with v in HL. exact HL.
  Qed.

  Lemma ftA_upd : forall (l r : list byte) (y b : byte), upd (l ++ y :: r) (length l) b = l ++ b :: r.
  Proof. induction l as [|a l IH]; intros r y b; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma ftA_byte : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 2^16 ->
    le1 (Z_to_bv 64 (Z.shiftr (Z.lor (Z.shiftl (sy + 256 * nb) 16 mod 2^64) ns) 16)) = [Z_to_bv 8 sy].
  Proof.
    intros sy nb ns H1 H2 H3. rewrite FseWalkKit.le1_lit. f_equal.
    pose proof (hw2_sy (2^16) (2^64) sy nb ns eq_refl eq_refl H1 H2 H3) as E.
    change 255 with (Z.ones 8) in E. rewrite Z.land_ones in E by lia.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite Z.shiftl_mul_pow2 by lia. rewrite E.
    rewrite (Z.mod_small sy); [reflexivity | change (2^8) with 256; lia].
  Qed.

  Lemma ftA_inv_byte : forall m1 x jp junk (o0 s1a : Z) (d1 : bitD) (j i : Z),
    munch W0 m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo SP1 ->
    rw_cells bsegs m1 (SP1 + 32) FRC ->
    rw_cells bsegs m1 (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 s1a); C8 (Z_to_bv 64 TB)] ->
    rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 d1 jp) ->
    u8arr bsegs m1 DST (map (Z_to_bv 8) (de_out x) ++ junk) -> zlen junk = dcap - zlen (de_out x) ->
    bytes_at bsegs m1 S0 (map (Z_to_bv 8) bs) ->
    store_ok bsegs m1 (Z_to_bv 64 (DST + j + i)) 1%nat = true ->
    zlen (de_out x) = j + i -> zlen (de_out x) < dcap -> 0 <= j -> 0 <= i ->
    ftA_inv (write_to_mem m1 (Z_to_bv 64 (DST + j + i)) [Z_to_bv 8 o0]) (mkDec (de_out x ++ [o0]) s1a (de_s2 x) d1) jp
      (List.tl junk).
  Proof.
    intros m1 x jp junk o0 s1a d1 j i MU WM MI STK FRC1 FO BD OUT LJ SRC1 SOK LJI LD J0 I0.
    ftA_lin.
    destruct junk as [|b0 junk0]; [cbn [length] in LJ; lia|]. cbn [List.tl].
    change (Z_to_bv 64 (DST + j + i)) with (wa (DST + j + i)).
    apply ftA_inv0.
    - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | exact SOK].
    - apply stk_write; [exact STK | lia | cbn [length]; lia].
    - apply rw_cells_frame; [exact FRC1 | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
    - apply rw_cells_frame; [exact FO | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
    - apply rw_cells_frame; [exact BD | lia | cbn [length]; lia | unfold bitdz_cellsA; cbn [cells_size csize length]; lia].
    - pose proof (u8arr_write bsegs m1 DST _ (j + i) (Z_to_bv 8 o0) OUT
                    ltac:(rewrite length_app, length_map; cbn [length]; lia)) as U.
      replace (DST + (j + i)) with (DST + j + i) in U by lia.
      replace (Z.to_nat (j + i)) with (length (map (Z_to_bv 8) (de_out x))) in U by (rewrite length_map; lia).
      rewrite ftA_upd in U. cbn [de_out]. rewrite map_app. cbn [map]. rewrite <- app_assoc. exact U.
    - cbn [de_out]. rewrite length_app. cbn [length] in LJ |- *. lia.
    - apply bytes_at_write_other; [exact SRC1 | lia | cbn [length]; lia | rewrite length_map; cbn [length]; lia].
  Qed.

  Lemma ftA_d1 : forall x mm jp junk (j i o0 s1a : Z) (d1 : bitD) (x1 x13 x14 x20 x21 x22 x23 x24 x25 x26 : word),
    decode_sym d true (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
    bitd_ok bs (de_bd x) -> bd_bits (de_bd x) <= 2^29 ->
    zlen (de_out x) = j + i -> zlen (de_out x) <= dcap - 2 -> 0 <= j -> 0 <= i ->
    ftA_inv mm x jp junk ->
    (forall mm' junk' (y13 y14 : word), ftA_inv mm' (mkDec (de_out x ++ [o0]) s1a (de_s2 x) d1) jp junk' ->
       evtF bsegs RNG Q (P1 mm' (mkDec (de_out x ++ [o0]) s1a (de_s2 x) d1) j i x1 y13 y14 x22 x23 x24 x25 x26)) ->
    evtF bsegs RNG Q (HD mm x j i x1 x13 x14 x20 x21 x22 x23 x24 x25 x26).
  Proof.
    intros x mm jp junk j i o0 s1a d1 x1 x13 x14 x20 x21 x22 x23 x24 x25 x26 DS BOK BB LJI LD J0 I0 I KP.
    ftA_lin.
    destruct (RF_huf_fdw_fm.fdec_inv tl [] d ltac:(lia) HCELLS HCOK (de_s1 x) (de_bd x) o0 s1a d1 DS ltac:(destruct BOK as (_ & HB & _); lia))
      as (c & NC & HS1 & CS & CN & CNS & CNS2 & -> & -> & ->).
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2.
    assert (P2T : 2^5 <= 2^tl <= 2^12) by (split; apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in P2T. change (2^12) with 4096 in P2T.
    pose proof (zsh_cell mm DT (4 + 4 * 2^tl) (de_s1 x * 4 + (DT + 4)) Z2 ltac:(lia) ltac:(lia)) as SH2.
    pose proof (zsh_cell mm DT (4 + 4 * 2^tl) (de_s1 x * 4 + (DT + 4) + 3) Z2 ltac:(lia) ltac:(lia)) as SH3.
    pose proof (AProg_kit.shad_lt_KHIGH (de_s1 x * 4 + (DT + 4)) ltac:(lia) ltac:(unfold KEND; lia)) as SB2.
    pose proof (AProg_kit.shad_lt_KHIGH (de_s1 x * 4 + (DT + 4) + 3) ltac:(lia) ltac:(unfold KEND; lia)) as SB3.
    unfold ASHOFF in SH2, SH3, SB2, SB3.
    pose proof (RF_huf_fdw_kit.cell_rd_ns bsegs mm (DT + 4) (dt_cells d) (de_s1 x) c (wa (de_s1 x * 4 + (DT + 4))) TB2 NC ltac:(lia) ltac:(f_equal; lia)) as CR0.
    pose proof (RF_huf_fdw_kit.cell_rd_off bsegs mm (DT + 4) (dt_cells d) (de_s1 x) c 2 2 TB2 NC ltac:(lia) ltac:(lia) ltac:(lia)) as CR2.
    replace (DT + 4 + (4 * de_s1 x + 2)) with (de_s1 x * 4 + (DT + 4) + 2) in CR2 by lia.
    unfold fse_cell_bytes in CR2. rewrite cell_hi_bytes in CR2 by lia.
    wto 0x9930c 0x98318.
    rewrite ?land64_mod, ?Z.shiftl_mul_pow2 by lia; try change (2^2) with 4.
    rewrite ?(Z.mod_small (de_s1 x * 4 + (DT + 4))) by lia.
    pose proof (zsh_cell mm DST dcap (DST + j + i) Z3 ltac:(lia) ltac:(lia)) as SH6.
    pose proof (AProg_kit.shad_lt_KHIGH (DST + j + i) ltac:(lia) ltac:(unfold KEND; lia)) as SB6.
    unfold ASHOFF in SH6, SB6.
    lazymatch type of SB6 with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
    pose proof ATOP_range as AR. unfold ATOP_MIN, ATOP_MAX in AR, KH.
    wto 0x9937c 0x98318.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      lazymatch goal with OU : u8arr bsegs mg DST ?l |- _ =>
        pose proof (u8arr_store_ok bsegs mg DST l (j + i) (Z_to_bv 64 (DST + j + i)) OU
                      ltac:(rewrite length_app, length_map; lia) ltac:(unfold wa; f_equal; lia)) as SOK end end.
    zstep. revert FO2 BD2.
    assert (CW : 0 <= dc_symbol c + 256 * dc_nbBits c < 2^16) by (assert (dc_nbBits c <= 12) by lia; lia).
    replace (bv_unsigned (zx16 (Z_to_bv 64 (dc_symbol c + 256 * dc_nbBits c)))) with (dc_symbol c + 256 * dc_nbBits c)
      by (rewrite AKit.zx16_lit by lia; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; symmetry; apply Z.mod_small; lia).
    pose proof BOK as BOK'. destruct BOK' as (BC & BBt & BP & BP8 & BPZ & BZ).
    try rewrite (land64_mod (bd_cont (de_bd x))), (Z.mod_small (bd_cont (de_bd x))) by lia.
    try rewrite (land64_mod (bd_bits (de_bd x))), (Z.mod_small (bd_bits (de_bd x))) by lia.
    try rewrite (land64_mod (Z.shiftl (dc_symbol c + 256 * dc_nbBits c) 16)).
    let v := eval vm_compute in (2^64) in change v with (2^64).
    rewrite (Z.add_comm (dc_newState c)) in KP.
    try rewrite (hw_nb (dc_symbol c) (dc_nbBits c)) by lia.
    try rewrite (lbfA2 (bd_cont (de_bd x)) (bd_bits (de_bd x)) (dc_nbBits c)) by lia.
    try rewrite (lbfA (bd_cont (de_bd x)) (bd_bits (de_bd x)) (dc_nbBits c)) by lia.
    try rewrite (SysStep.swrap32_small (dc_nbBits c + bd_bits (de_bd x))) by lia.
    try replace (dc_nbBits c + bd_bits (de_bd x)) with (bd_bits (de_bd x) + dc_nbBits c) by lia.
    assert (NS16 : 0 <= dc_newState c < 2^16) by (assert (0 < 2^dc_nbBits c) by (apply Z.pow_pos_nonneg; lia); lia).
    try replace (bv_unsigned (zx16 (Z_to_bv 64 (dc_newState c)))) with (dc_newState c)
      by (rewrite AKit.zx16_lit by lia; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; symmetry; apply Z.mod_small; lia).
    repeat match goal with |- context [Z.land ?y ?M] =>
      lazymatch M with Zpos _ => idtac end;
      let b := eval vm_compute in (M =? Z.ones 16) in lazymatch b with true =>
      replace (Z.land y M) with (y mod 2^16) by (change M with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity) end end.
    try rewrite (hw_ns (dc_symbol c) (dc_nbBits c) (dc_newState c)) by lia.
    intros FO2 BD2. unfold bd_regF in KP |- *. cbn [bd_zero bd_ptr] in KP.
    unfold mkR in KP. cbn [de_bd de_s1 de_s2 de_out bd_cont bd_bits bd_ptr bd_zero] in KP.
    let v := eval vm_compute in (2^61) in change (2^61) with v in KP.
    eapply KP.
    rewrite (ftA_byte (dc_symbol c) (dc_nbBits c) (dc_newState c)) by lia.
    eapply ftA_inv_byte; try eassumption; lia.
  Qed.

  Lemma ftA_src8 : forall mm a, unpoisoned mm S0 (S0 + zlen bs) -> S0 <= a -> a + 8 <= S0 + zlen bs ->
    exists b1 b2, rw_cells bsegs mm (Z.shiftr a 3 + ASHOFF) [C1 b1] /\ Z.shiftr a 3 + ASHOFF + 1 <= KHIGH /\ sval b1 = 0 /\
      rw_cells bsegs mm (Z.shiftr (a + 7) 3 + ASHOFF) [C1 b2] /\ Z.shiftr (a + 7) 3 + ASHOFF + 1 <= KHIGH /\
      (sval b2 = 0 \/ (0 < sval b2 <= 7 /\ (a + 7) mod 8 < sval b2)).
  Proof.
    intros mm a U L H.
    ftA_lin.
    assert (KE : S0 + zlen bs <= KEND) by (unfold KEND; lia).
    destruct (src_sh_cell mm S0 (S0 + zlen bs) (a + 7) U ltac:(lia) ltac:(lia) KE) as (b2 & SS2 & SS2B & GB2).
    assert (A8 : Z.shiftr a 3 = a / 8) by (apply Z.shiftr_div_pow2; lia).
    pose proof U as (U0 & U1 & U2).
    destruct (U2 (Z.shiftr a 3) ltac:(lia) ltac:(rewrite A8; Z.div_mod_to_equations; lia)
                ltac:(rewrite A8; Z.div_mod_to_equations; lia)) as (b1 & MB & GB).
    rewrite A8 in GB. rewrite Z.min_l in GB by (Z.div_mod_to_equations; lia).
    pose proof (gran_ok_full _ _ GB ltac:(lia)) as B0.
    exists b1, b2.
    refine (conj _ (conj _ (conj _ (conj SS2 (conj SS2B GB2))))).
    - apply AProg_kit.c1_of_byte; [rewrite A8; unfold ASHOFF; Z.div_mod_to_equations; lia
                                 | rewrite A8; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia |].
      rewrite Z.add_comm; exact MB.
    - apply AProg_kit.shad_lt_KHIGH; lia.
    - subst b1. reflexivity.
  Qed.

  Lemma ftA_r1t : forall x mm jp junk (j i p' b' : Z) (x1 x12 x14 x19 x23 x24 x25 x26 : word),
    0 <= p' -> p' + 8 <= zlen bs -> 0 <= b' <= 64 ->
    zlen (de_out x) = j + i + 1 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
    ftA_inv mm (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (bd_cont (de_bd x)) b' p' false)) jp junk ->
    (dcap - 2 < zlen (de_out x) -> R = Err ZSTD_error_dstSize_tooSmall) ->
    (zlen (de_out x) <= dcap - 2 ->
       forall mm2 (jp2 : list byte) (y1 y12 y14 y23 y24 y25 y26 : word),
       ftA_inv mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false)) jp2 junk ->
       evtF bsegs RNG Q (P2 0x994a0 mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false))
                           j i y1 y12 y14 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (RSu 0x9943c mm x j i p' b' x1 x12 x14 x19 x23 x24 x25 x26).
  Proof.
    intros x mm jp junk j i p' b' x1 x12 x14 x19 x23 x24 x25 x26 P0 PE B0 LJI LD J0 I0 I RERR KN.
    ftA_lin.
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2. cbn [bd_cont bd_bits bd_ptr bd_zero de_bd de_out de_s1 de_s2] in BD2, FO2, OUT2, LJ2.
    lazymatch goal with SRC' : bytes_at bsegs ?mg S0 (map (Z_to_bv 8) bs) |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      pose proof (src_rd bsegs mg S0 bs (p' + 0) SRC' ltac:(lia)) as RX0;
      pose proof (src_rd bsegs mg S0 bs (p' + 1) SRC' ltac:(lia)) as RX1;
      pose proof (src_rd bsegs mg S0 bs (p' + 2) SRC' ltac:(lia)) as RX2;
      pose proof (src_rd bsegs mg S0 bs (p' + 3) SRC' ltac:(lia)) as RX3;
      pose proof (src_rd bsegs mg S0 bs (p' + 4) SRC' ltac:(lia)) as RX4;
      pose proof (src_rd bsegs mg S0 bs (p' + 5) SRC' ltac:(lia)) as RX5;
      pose proof (src_rd bsegs mg S0 bs (p' + 6) SRC' ltac:(lia)) as RX6;
      pose proof (src_rd bsegs mg S0 bs (p' + 7) SRC' ltac:(lia)) as RX7 end.
    rewrite ?Z.add_assoc, ?Z.add_0_r in RX0, RX1, RX2, RX3, RX4, RX5, RX6, RX7.
    repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep).
    pose proof (fun k => byte_Znth bs k BY) as BZ.
    (let v := reg_val 19%Z in
          assert (EV : v = Z_to_bv 64 (le64v bs p'))
            by (f_equal; unfold le64v; rewrite le64_lbu_land by (apply BZ; lia); rewrite ?Z.add_0_r; ring);
          rewrite EV in *).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      assert (I2 : ftA_inv mg (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false)) jp junk)
        by (apply ftA_inv0; assumption) end.
    destruct (Z.ltb_spec (dcap - 2) (zlen (de_out x))) as [LT|GE].
    all: lazymatch goal with
         | LT : dcap - 2 < zlen _ |- _ =>
             br; wto 0x994a0 0x98318;
             eapply (ftA_err _ _ jp junk ZSTD_error_dstSize_tooSmall);
               [exact I2 | apply RERR; exact LT | unfold ZSTD_error_dstSize_tooSmall; lia]
         | GE : zlen _ <= dcap - 2 |- _ =>
             br; unfold bd_regF in KN; cbn [bd_zero bd_ptr bd_cont bd_bits de_bd de_out de_s1 de_s2] in KN;
             unfold mkR in KN; let v := eval vm_compute in (2^61) in change (2^61) with v in KN;
             eapply (KN GE); exact I2
         end.
  Qed.

  Lemma ftA_r1s : forall x mm jp junk (j i q p' b' : Z) (x1 x14 x19 x23 x24 x25 x26 : word),
    0 <= q <= zlen bs -> 0 <= p' -> p' + 8 <= zlen bs -> 0 <= b' <= 64 ->
    zlen (de_out x) = j + i + 1 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
    ftA_inv mm x jp junk ->
    (dcap - 2 < zlen (de_out x) -> R = Err ZSTD_error_dstSize_tooSmall) ->
    (zlen (de_out x) <= dcap - 2 ->
       forall mm2 (jp2 : list byte) (y1 y12 y14 y23 y24 y25 y26 : word),
       ftA_inv mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false)) jp2 junk ->
       evtF bsegs RNG Q (P2 0x994a0 mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false))
                           j i y1 y12 y14 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (RSt 0x9940c mm x j i q p' b' x1 x14 x19 x23 x24 x25 x26).
  Proof.
    intros x mm jp junk j i q p' b' x1 x14 x19 x23 x24 x25 x26 Q0 P0 PE B0 LJI LD J0 I0 I RERR KN.
    ftA_lin.
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2.
    assert (ZB : 0 < zlen bs) by lia.
    repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep).
    br.
    assert (AW : appW W0) by (pose proof HDST as HDSx; unfold ablk, KLS, AIMG_HI in HDSx; fappW).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      assert (UG : unpoisoned mg S0 (S0 + zlen bs))
        by (eapply unpoisoned_appW; [exact USRC | eassumption | exact AW | lia | lia]);
      destruct (ftA_src8 mg (S0 + p') UG ltac:(lia) ltac:(lia))
        as (b1 & b2 & SS1 & SS1B & B1z & SS2 & SS2B & GB2) end.
    unfold ASHOFF in SS1, SS1B, SS2, SS2B.
    lazymatch type of SS1B with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
    pose proof ATOP_range as AR. unfold ATOP_MIN, ATOP_MAX in AR, KH.
    repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep).
    rewrite sxb_sval, B1z. br.
    repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep).
    rewrite sxb_sval.
    destruct GB2 as [B2z | (B2p & B2lt)];
      [ rewrite B2z; br
      | replace (bv_eqb (Z_to_bv 64 (sval b2)) (Z_to_bv 64 0)) with false
          by (symmetry; rewrite bv_eqb_Z, !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
              apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia);
        br; repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep);
        lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with true
            by (symmetry; unfold bv_lts; rewrite RF_huf_fdw_sm.land7_mod; pose proof (sval_range b2) as SR2;
                rewrite (signed_lit_small64 (sval b2)) by lia;
                rewrite signed_lit_small64 by (pose proof (Z.mod_pos_bound (S0 + p' + 7) 8); lia);
                apply Z.ltb_lt; lia) end;
        cbv iota ].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      assert (I1 : ftA_inv mg (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (bd_cont (de_bd x)) b' p' false)) jp junk)
        by (apply ftA_inv0; assumption) end.
    all: eapply ftA_r1t; [ lia | lia | lia | exact LJI | lia | lia | lia | exact I1 | exact RERR | exact KN ].
  Qed.

  Lemma ftA_r1 : forall x mm jp junk (j i : Z) (st : dstatus) (d1r : bitD) (x1 x13 x14 x22 x23 x24 x25 x26 : word),
    reload_dstream bs (de_bd x) = Ok (st, d1r) ->
    bitd_ok bs (de_bd x) -> zlen (de_out x) = j + i + 1 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
    ftA_inv mm x jp junk ->
    (bd_bits (de_bd x) <= 64 -> dcap - 2 < zlen (de_out x) -> R = Err ZSTD_error_dstSize_tooSmall) ->
    (64 < bd_bits (de_bd x) -> forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
       evtF bsegs RNG Q (FN 0x99bc8 mm j i y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31)) ->
    (bd_bits (de_bd x) <= 64 -> zlen (de_out x) <= dcap - 2 ->
       forall mm2 (jp2 : list byte) (y1 y12 y14 y23 y24 y25 y26 : word),
       ftA_inv mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) d1r) jp2 junk ->
       evtF bsegs RNG Q (P2 0x994a0 mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) d1r) j i y1 y12 y14 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (P1 mm x j i x1 x13 x14 x22 x23 x24 x25 x26).
  Proof.
    intros x mm jp junk j i st d1r x1 x13 x14 x22 x23 x24 x25 x26 RLD BOK LJI LD J0 I0 I RERR KF KN.
    ftA_lin.
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2.
    pose proof BOK as BOK'. destruct BOK' as (BC & BBt & BP & BP8 & BPZ & BZ).
    wto 0x994a0 0x99bc8.
    destruct (Z.ltb_spec 64 (bd_bits (de_bd x))) as [BG|BL].
    - br. wto 0x99bc8 0x98318.
      eapply (KF BG).
    - br.
      assert (BZF : bd_zero (de_bd x) = false)
        by (destruct (bd_zero (de_bd x)) eqn:E; [specialize (BZ eq_refl); lia | reflexivity]).
      replace (bd_regF S0 (de_bd x)) with (S0 + bd_ptr (de_bd x)) by (unfold bd_regF; rewrite BZF; reflexivity).
      wto 0x994a0 0x99bc8.
      assert (WB : bv_wrap 32 (bd_bits (de_bd x)) = bd_bits (de_bd x))
        by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
      assert (SB : bv_swrap 32 (Z.shiftr (bd_bits (de_bd x)) 3) = bd_bits (de_bd x) / 8)
        by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; apply SysStep.swrap32_small; Z.div_mod_to_equations; lia).
      destruct (Z.leb_spec 8 (bd_ptr (de_bd x))) as [P8|P8].
      + br.
        assert (ZB : 0 < zlen bs) by lia.
        repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep).
        rewrite ?WB, ?SB. br. repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep).
        assert (LX : 1 <= Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8)).
        { assert (0 <= Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8))
            by (apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia).
          assert (Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8) <> 0)
            by (rewrite Z.lxor_eq_0_iff; Z.div_mod_to_equations; lia).
          lia. }
        replace (Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8) <? 1) with false
          by (symmetry; apply Z.ltb_ge; exact LX).
        br.
        repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
        unfold reload_dstream in RLD.
        replace (64 <? bd_bits (de_bd x)) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
        replace (8 <=? bd_ptr (de_bd x)) with true in RLD by (symmetry; apply Z.leb_le; lia).
        assert (SH3 : Z.shiftr (bd_bits (de_bd x)) 3 = bd_bits (de_bd x) / 8)
          by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        rewrite SH3 in RLD.
        rewrite (readLE64_ok bs (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) in RLD by (Z.div_mod_to_equations; lia).
        cbn [bind] in RLD. injection RLD as <- <-.
        replace (S0 + bd_ptr (de_bd x) - bd_bits (de_bd x) / 8) with (S0 + (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) by lia.
        eapply (ftA_r1s x mm jp junk j i (bd_ptr (de_bd x)) (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)
                  (Z.land (bd_bits (de_bd x)) 7));
          [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia
          | rewrite RF_huf_fdw_sm.land7_mod; pose proof (Z.mod_pos_bound (bd_bits (de_bd x)) 8); lia
          | lia | lia | lia | lia | exact I | intro; apply RERR; lia | exact (KN BL) ].
      + br. repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep).
        destruct (Z.eq_dec (bd_ptr (de_bd x)) 0) as [PZ|PZ].
        * br.
          unfold reload_dstream in RLD.
          replace (64 <? bd_bits (de_bd x)) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
          replace (8 <=? bd_ptr (de_bd x)) with false in RLD by (symmetry; apply Z.leb_gt; lia).
          replace (bd_ptr (de_bd x) =? 0) with true in RLD by (symmetry; apply Z.eqb_eq; exact PZ).
          injection RLD as _ RD. subst d1r.
          replace (mkDec (de_out x) (de_s1 x) (de_s2 x) (de_bd x)) with x in KN by (destruct x; reflexivity).
          unfold bd_regF in KN. rewrite BZF in KN.
          repeat (tryif pc_in 0x994a0 0x98318 then fail else zstep).
          destruct (Z.ltb_spec (dcap - 2) (zlen (de_out x))) as [LT|GE].
          -- br. wto 0x994a0 0x98318.
             eapply (ftA_err _ x jp junk ZSTD_error_dstSize_tooSmall);
               [exact I | apply RERR; lia | unfold ZSTD_error_dstSize_tooSmall; lia].
          -- br. wto 0x994a0 0x98318.
             eapply (KN BL ltac:(lia)). exact I.
        * assert (PP : 0 < bd_ptr (de_bd x)) by lia.
          br. repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
          rewrite ?WB, ?SB. br.
          repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
          ftA_zx. br.
          repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
          unfold reload_dstream in RLD.
          replace (64 <? bd_bits (de_bd x)) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
          replace (8 <=? bd_ptr (de_bd x)) with false in RLD by (symmetry; apply Z.leb_gt; lia).
          replace (bd_ptr (de_bd x) =? 0) with false in RLD by (symmetry; apply Z.eqb_neq; lia).
          cbv beta iota zeta in RLD.
          assert (SH3 : Z.shiftr (bd_bits (de_bd x)) 3 = bd_bits (de_bd x) / 8)
            by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
          rewrite SH3 in RLD.
          destruct (Z.ltb_spec (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8) 0) as [NB|NB].
          -- replace (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 <? 0) with true in RLD by (symmetry; apply Z.ltb_lt; lia).
             cbv beta iota zeta in RLD.
             rewrite (readLE64_ok bs (bd_ptr (de_bd x) - bd_ptr (de_bd x))) in RLD by lia.
             cbn [bind] in RLD. injection RLD as <- <-.
             br. repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
             replace (S0 + bd_ptr (de_bd x) - S0) with (bd_ptr (de_bd x)) by lia.
             ftA_norm. br.
             repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
             ftA_zx. br.
             repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
             ftA_norm.
             replace (S0 + bd_ptr (de_bd x) - bd_ptr (de_bd x)) with (S0 + (bd_ptr (de_bd x) - bd_ptr (de_bd x))) by lia.
             eapply (ftA_r1s x mm jp junk j i (bd_ptr (de_bd x)) (bd_ptr (de_bd x) - bd_ptr (de_bd x))
                              (bd_bits (de_bd x) - bd_ptr (de_bd x) * 8));
                       [ lia | lia | lia | Z.div_mod_to_equations; lia | lia | lia | lia | lia | exact I
                       | intro; apply RERR; lia | exact (KN BL) ].
          -- replace (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 <? 0) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
             cbv beta iota zeta in RLD.
             rewrite (readLE64_ok bs (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) in RLD by (Z.div_mod_to_equations; lia).
             cbn [bind] in RLD. injection RLD as <- <-.
             br. repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
             ftA_norm. br.
             repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
             ftA_zx. br.
             repeat (tryif pc_in 0x9940c 0x98318 then fail else zstep).
             ftA_norm.
             replace (S0 + bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)
               with (S0 + (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) by lia.
             eapply (ftA_r1s x mm jp junk j i (bd_ptr (de_bd x)) (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)
                              (bd_bits (de_bd x) - bd_bits (de_bd x) / 8 * 8));
                       [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia
                       | lia | lia | lia | lia | exact I | intro; apply RERR; lia | exact (KN BL) ].
  Qed.

  Lemma ftA_inv_byte2 : forall m1 x jp junk (o0 s1a : Z) (d1 : bitD) (j i : Z),
    munch W0 m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo SP1 ->
    rw_cells bsegs m1 (SP1 + 32) FRC ->
    rw_cells bsegs m1 (SP1 + 80) [C8 (Z_to_bv 64 s1a); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)] ->
    rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 d1 jp) ->
    u8arr bsegs m1 DST (map (Z_to_bv 8) (de_out x) ++ junk) -> zlen junk = dcap - zlen (de_out x) ->
    bytes_at bsegs m1 S0 (map (Z_to_bv 8) bs) ->
    store_ok bsegs m1 (Z_to_bv 64 (DST + j + i + 1)) 1%nat = true ->
    zlen (de_out x) = j + i + 1 -> zlen (de_out x) < dcap -> 0 <= j -> 0 <= i ->
    ftA_inv (write_to_mem m1 (Z_to_bv 64 (DST + j + i + 1)) [Z_to_bv 8 o0]) (mkDec (de_out x ++ [o0]) (de_s1 x) s1a d1) jp
      (List.tl junk).
  Proof.
    intros m1 x jp junk o0 s1a d1 j i MU WM MI STK FRC1 FO BD OUT LJ SRC1 SOK LJI LD J0 I0.
    ftA_lin.
    destruct junk as [|b0 junk0]; [cbn [length] in LJ; lia|]. cbn [List.tl].
    change (Z_to_bv 64 (DST + j + i + 1)) with (wa (DST + j + i + 1)).
    apply ftA_inv0.
    - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | exact SOK].
    - apply stk_write; [exact STK | lia | cbn [length]; lia].
    - apply rw_cells_frame; [exact FRC1 | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
    - apply rw_cells_frame; [exact FO | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
    - apply rw_cells_frame; [exact BD | lia | cbn [length]; lia | unfold bitdz_cellsA; cbn [cells_size csize length]; lia].
    - pose proof (u8arr_write bsegs m1 DST _ (j + i + 1) (Z_to_bv 8 o0) OUT
                    ltac:(rewrite length_app, length_map; cbn [length]; lia)) as U.
      replace (DST + (j + i + 1)) with (DST + j + i + 1) in U by lia.
      replace (Z.to_nat (j + i + 1)) with (length (map (Z_to_bv 8) (de_out x))) in U by (rewrite length_map; lia).
      rewrite ftA_upd in U. cbn [de_out]. rewrite map_app. cbn [map]. rewrite <- app_assoc. exact U.
    - cbn [de_out]. rewrite length_app. cbn [length] in LJ |- *. lia.
    - apply bytes_at_write_other; [exact SRC1 | lia | cbn [length]; lia | rewrite length_map; cbn [length]; lia].
  Qed.

  Lemma ftA_d2 : forall x mm jp junk (j i o0 s1a : Z) (d1 : bitD) (x1 x12 x14 x23 x24 x25 x26 : word),
    decode_sym d true (de_s2 x) (de_bd x) = Ok (o0, s1a, d1) ->
    bitd_ok bs (de_bd x) -> bd_bits (de_bd x) <= 2^29 ->
    zlen (de_out x) = j + i + 1 -> zlen (de_out x) <= dcap - 2 -> 0 <= j -> 0 <= i ->
    ftA_inv mm x jp junk ->
    (forall mm' junk' (y12 y14 y23 y24 : word), ftA_inv mm' (mkDec (de_out x ++ [o0]) (de_s1 x) s1a d1) jp junk' ->
       evtF bsegs RNG Q (P2 0x9953c mm' (mkDec (de_out x ++ [o0]) (de_s1 x) s1a d1) j i x1 y12 y14 y23 y24 x25 x26)) ->
    evtF bsegs RNG Q (P2 0x994a0 mm x j i x1 x12 x14 x23 x24 x25 x26).
  Proof.
    intros x mm jp junk j i o0 s1a d1 x1 x12 x14 x23 x24 x25 x26 DS BOK BB LJI LD J0 I0 I KP.
    ftA_lin.
    destruct (RF_huf_fdw_fm.fdec_inv tl [] d ltac:(lia) HCELLS HCOK (de_s2 x) (de_bd x) o0 s1a d1 DS ltac:(destruct BOK as (_ & HB & _); lia))
      as (c & NC & HS1 & CS & CN & CNS & CNS2 & -> & -> & ->).
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2.
    assert (P2T : 2^5 <= 2^tl <= 2^12) by (split; apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in P2T. change (2^12) with 4096 in P2T.
    pose proof (zsh_cell mm DT (4 + 4 * 2^tl) (de_s2 x * 4 + (DT + 4)) Z2 ltac:(lia) ltac:(lia)) as SH2.
    pose proof (zsh_cell mm DT (4 + 4 * 2^tl) (de_s2 x * 4 + (DT + 4) + 3) Z2 ltac:(lia) ltac:(lia)) as SH3.
    pose proof (AProg_kit.shad_lt_KHIGH (de_s2 x * 4 + (DT + 4)) ltac:(lia) ltac:(unfold KEND; lia)) as SB2.
    pose proof (AProg_kit.shad_lt_KHIGH (de_s2 x * 4 + (DT + 4) + 3) ltac:(lia) ltac:(unfold KEND; lia)) as SB3.
    unfold ASHOFF in SH2, SH3, SB2, SB3.
    pose proof (RF_huf_fdw_kit.cell_rd_ns bsegs mm (DT + 4) (dt_cells d) (de_s2 x) c (wa (de_s2 x * 4 + (DT + 4))) TB2 NC ltac:(lia) ltac:(f_equal; lia)) as CR0.
    pose proof (RF_huf_fdw_kit.cell_rd_off bsegs mm (DT + 4) (dt_cells d) (de_s2 x) c 2 2 TB2 NC ltac:(lia) ltac:(lia) ltac:(lia)) as CR2.
    replace (DT + 4 + (4 * de_s2 x + 2)) with (de_s2 x * 4 + (DT + 4) + 2) in CR2 by lia.
    unfold fse_cell_bytes in CR2. rewrite cell_hi_bytes in CR2 by lia.
    wto 0x994d0 0x98318.
    rewrite ?land64_mod, ?Z.shiftl_mul_pow2 by lia; try change (2^2) with 4.
    rewrite ?(Z.mod_small (de_s2 x * 4 + (DT + 4))) by lia.
    pose proof (zsh_cell mm DST dcap (DST + j + i + 1) Z3 ltac:(lia) ltac:(lia)) as SH6.
    pose proof (AProg_kit.shad_lt_KHIGH (DST + j + i + 1) ltac:(lia) ltac:(unfold KEND; lia)) as SB6.
    unfold ASHOFF in SH6, SB6.
    lazymatch type of SB6 with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
    pose proof ATOP_range as AR. unfold ATOP_MIN, ATOP_MAX in AR, KH.
    wto 0x99538 0x98318.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      lazymatch goal with OU : u8arr bsegs mg DST ?l |- _ =>
        pose proof (u8arr_store_ok bsegs mg DST l (j + i + 1) (Z_to_bv 64 (DST + j + i + 1)) OU
                      ltac:(rewrite length_app, length_map; lia) ltac:(unfold wa; f_equal; lia)) as SOK end end.
    zstep. revert FO2 BD2.
    assert (CW : 0 <= dc_symbol c + 256 * dc_nbBits c < 2^16) by (assert (dc_nbBits c <= 12) by lia; lia).
    replace (bv_unsigned (zx16 (Z_to_bv 64 (dc_symbol c + 256 * dc_nbBits c)))) with (dc_symbol c + 256 * dc_nbBits c)
      by (rewrite AKit.zx16_lit by lia; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; symmetry; apply Z.mod_small; lia).
    pose proof BOK as BOK'. destruct BOK' as (BC & BBt & BP & BP8 & BPZ & BZ).
    try rewrite (land64_mod (bd_cont (de_bd x))), (Z.mod_small (bd_cont (de_bd x))) by lia.
    try rewrite (land64_mod (bd_bits (de_bd x))), (Z.mod_small (bd_bits (de_bd x))) by lia.
    try rewrite (land64_mod (Z.shiftl (dc_symbol c + 256 * dc_nbBits c) 16)).
    let v := eval vm_compute in (2^64) in change v with (2^64).
    rewrite (Z.add_comm (dc_newState c)) in KP.
    try rewrite (hw_nb (dc_symbol c) (dc_nbBits c)) by lia.
    try rewrite (lbfA2 (bd_cont (de_bd x)) (bd_bits (de_bd x)) (dc_nbBits c)) by lia.
    try rewrite (lbfA (bd_cont (de_bd x)) (bd_bits (de_bd x)) (dc_nbBits c)) by lia.
    try rewrite (SysStep.swrap32_small (dc_nbBits c + bd_bits (de_bd x))) by lia.
    try replace (dc_nbBits c + bd_bits (de_bd x)) with (bd_bits (de_bd x) + dc_nbBits c) by lia.
    assert (NS16 : 0 <= dc_newState c < 2^16) by (assert (0 < 2^dc_nbBits c) by (apply Z.pow_pos_nonneg; lia); lia).
    try replace (bv_unsigned (zx16 (Z_to_bv 64 (dc_newState c)))) with (dc_newState c)
      by (rewrite AKit.zx16_lit by lia; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; symmetry; apply Z.mod_small; lia).
    repeat match goal with |- context [Z.land ?y ?M] =>
      lazymatch M with Zpos _ => idtac end;
      let b := eval vm_compute in (M =? Z.ones 16) in lazymatch b with true =>
      replace (Z.land y M) with (y mod 2^16) by (change M with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity) end end.
    try rewrite (hw_ns (dc_symbol c) (dc_nbBits c) (dc_newState c)) by lia.
    intros FO2 BD2. unfold bd_regF in KP |- *. cbn [bd_zero bd_ptr] in KP.
    unfold mkR in KP. cbn [de_bd de_s1 de_s2 de_out bd_cont bd_bits bd_ptr bd_zero] in KP.
    let v := eval vm_compute in (2^61) in change (2^61) with v in KP.
    eapply KP.
    rewrite (ftA_byte (dc_symbol c) (dc_nbBits c) (dc_newState c)) by lia.
    eapply ftA_inv_byte2; try eassumption; lia.
  Qed.

  Lemma ftA_r2t : forall x mm jp junk (j i p' b' : Z) (x1 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 : word),
    0 <= p' -> p' + 8 <= zlen bs -> 0 <= b' <= 64 ->
    zlen (de_out x) = j + i + 2 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
    ftA_inv mm (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (bd_cont (de_bd x)) b' p' false)) jp junk ->
    (dcap - 2 < zlen (de_out x) -> R = Err ZSTD_error_dstSize_tooSmall) ->
    (zlen (de_out x) <= dcap - 2 ->
       forall mm2 (jp2 : list byte) (y13 y14 y20 y21 y22 y23 y24 y25 y26 : word),
       ftA_inv mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false)) jp2 junk ->
       evtF bsegs RNG Q (HD mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false)) j (i + 2)
                           x1 y13 y14 y20 y21 y22 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (RSu2 0x995f4 mm x j i p' b' x1 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26).
  Proof.
    intros x mm jp junk j i p' b' x1 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 P0 PE B0 LJI LD J0 I0 I RERR KN.
    ftA_lin.
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2. cbn [bd_cont bd_bits bd_ptr bd_zero de_bd de_out de_s1 de_s2] in BD2, FO2, OUT2, LJ2.
    lazymatch goal with SRC' : bytes_at bsegs ?mg S0 (map (Z_to_bv 8) bs) |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      pose proof (src_rd bsegs mg S0 bs (p' + 0) SRC' ltac:(lia)) as RX0;
      pose proof (src_rd bsegs mg S0 bs (p' + 1) SRC' ltac:(lia)) as RX1;
      pose proof (src_rd bsegs mg S0 bs (p' + 2) SRC' ltac:(lia)) as RX2;
      pose proof (src_rd bsegs mg S0 bs (p' + 3) SRC' ltac:(lia)) as RX3;
      pose proof (src_rd bsegs mg S0 bs (p' + 4) SRC' ltac:(lia)) as RX4;
      pose proof (src_rd bsegs mg S0 bs (p' + 5) SRC' ltac:(lia)) as RX5;
      pose proof (src_rd bsegs mg S0 bs (p' + 6) SRC' ltac:(lia)) as RX6;
      pose proof (src_rd bsegs mg S0 bs (p' + 7) SRC' ltac:(lia)) as RX7 end.
    rewrite ?Z.add_assoc, ?Z.add_0_r in RX0, RX1, RX2, RX3, RX4, RX5, RX6, RX7.
    repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep).
    pose proof (fun k => byte_Znth bs k BY) as BZ.
    (let v := reg_val 19%Z in
          assert (EV : v = Z_to_bv 64 (le64v bs p'))
            by (f_equal; unfold le64v; rewrite le64_lbu_land by (apply BZ; lia); rewrite ?Z.add_0_r; ring);
          rewrite EV in *).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      assert (I2 : ftA_inv mg (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false)) jp junk)
        by (apply ftA_inv0; assumption) end.
    destruct (Z.ltb_spec (dcap - 2) (zlen (de_out x))) as [LT|GE].
    all: lazymatch goal with
         | LT : dcap - 2 < zlen _ |- _ =>
             br; wto 0x992dc 0x98318;
             eapply (ftA_err _ _ jp junk ZSTD_error_dstSize_tooSmall);
               [exact I2 | apply RERR; exact LT | unfold ZSTD_error_dstSize_tooSmall; lia]
         | GE : zlen _ <= dcap - 2 |- _ =>
             br; unfold bd_regF in KN; cbn [bd_zero bd_ptr bd_cont bd_bits de_bd de_out de_s1 de_s2] in KN;
             unfold mkR in KN; let v := eval vm_compute in (2^61) in change (2^61) with v in KN;
             eapply (KN GE); exact I2
         end.
  Qed.

  Lemma ftA_r2s : forall x mm jp junk (j i q p' b' : Z) (x1 x14 x19 x20 x23 x24 x25 x26 : word),
    0 <= q <= zlen bs -> 0 <= p' -> p' + 8 <= zlen bs -> 0 <= b' <= 64 ->
    zlen (de_out x) = j + i + 2 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
    ftA_inv mm x jp junk ->
    (dcap - 2 < zlen (de_out x) -> R = Err ZSTD_error_dstSize_tooSmall) ->
    (zlen (de_out x) <= dcap - 2 ->
       forall mm2 (jp2 : list byte) (y13 y14 y20 y21 y22 y23 y24 y25 y26 : word),
       ftA_inv mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false)) jp2 junk ->
       evtF bsegs RNG Q (HD mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (le64v bs p') b' p' false)) j (i + 2)
                           x1 y13 y14 y20 y21 y22 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (RSt2 0x995c4 mm x j i q p' b' x1 x14 x19 x20 x23 x24 x25 x26).
  Proof.
    intros x mm jp junk j i q p' b' x1 x14 x19 x20 x23 x24 x25 x26 Q0 P0 PE B0 LJI LD J0 I0 I RERR KN.
    ftA_lin.
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2.
    assert (ZB : 0 < zlen bs) by lia.
    repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep).
    br.
    assert (AW : appW W0) by (pose proof HDST as HDSx; unfold ablk, KLS, AIMG_HI in HDSx; fappW).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      assert (UG : unpoisoned mg S0 (S0 + zlen bs))
        by (eapply unpoisoned_appW; [exact USRC | eassumption | exact AW | lia | lia]);
      destruct (ftA_src8 mg (S0 + p') UG ltac:(lia) ltac:(lia))
        as (b1 & b2 & SS1 & SS1B & B1z & SS2 & SS2B & GB2) end.
    unfold ASHOFF in SS1, SS1B, SS2, SS2B.
    lazymatch type of SS1B with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
    pose proof ATOP_range as AR. unfold ATOP_MIN, ATOP_MAX in AR, KH.
    repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep).
    rewrite sxb_sval, B1z. br.
    repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep).
    rewrite sxb_sval.
    destruct GB2 as [B2z | (B2p & B2lt)];
      [ rewrite B2z; br
      | replace (bv_eqb (Z_to_bv 64 (sval b2)) (Z_to_bv 64 0)) with false
          by (symmetry; rewrite bv_eqb_Z, !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
              apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia);
        br; repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep);
        lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with true
            by (symmetry; unfold bv_lts; rewrite RF_huf_fdw_sm.land7_mod; pose proof (sval_range b2) as SR2;
                rewrite (signed_lit_small64 (sval b2)) by lia;
                rewrite signed_lit_small64 by (pose proof (Z.mod_pos_bound (S0 + p' + 7) 8); lia);
                apply Z.ltb_lt; lia) end;
        cbv iota ].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      assert (I1 : ftA_inv mg (mkDec (de_out x) (de_s1 x) (de_s2 x) (mkBD (bd_cont (de_bd x)) b' p' false)) jp junk)
        by (apply ftA_inv0; assumption) end.
    all: eapply ftA_r2t; [ lia | lia | lia | exact LJI | lia | lia | lia | exact I1 | exact RERR | exact KN ].
  Qed.

  Lemma ftA_r2 : forall x mm jp junk (j i : Z) (st : dstatus) (d2r : bitD) (x1 x12 x14 x23 x24 x25 x26 : word),
    reload_dstream bs (de_bd x) = Ok (st, d2r) ->
    bitd_ok bs (de_bd x) -> zlen (de_out x) = j + i + 2 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
    ftA_inv mm x jp junk ->
    (bd_bits (de_bd x) <= 64 -> dcap - 2 < zlen (de_out x) -> R = Err ZSTD_error_dstSize_tooSmall) ->
    (64 < bd_bits (de_bd x) -> forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
       evtF bsegs RNG Q (FN 0x99c04 mm j i y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31)) ->
    (bd_bits (de_bd x) <= 64 -> zlen (de_out x) <= dcap - 2 ->
       forall mm2 (jp2 : list byte) (y13 y14 y20 y21 y22 y23 y24 y25 y26 : word),
       ftA_inv mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) d2r) jp2 junk ->
       evtF bsegs RNG Q (HD mm2 (mkDec (de_out x) (de_s1 x) (de_s2 x) d2r) j (i + 2) x1 y13 y14 y20 y21 y22 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (P2 0x9953c mm x j i x1 x12 x14 x23 x24 x25 x26).
  Proof.
    intros x mm jp junk j i st d2r x1 x12 x14 x23 x24 x25 x26 RLD BOK LJI LD J0 I0 I RERR KF KN.
    ftA_lin.
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2.
    pose proof BOK as BOK'. destruct BOK' as (BC & BBt & BP & BP8 & BPZ & BZ).
    wto 0x992dc 0x99c04.
    destruct (Z.ltb_spec 64 (bd_bits (de_bd x))) as [BG|BL].
    - br. wto 0x99c04 0x98318.
      eapply (KF BG).
    - br.
      assert (BZF : bd_zero (de_bd x) = false)
        by (destruct (bd_zero (de_bd x)) eqn:E; [specialize (BZ eq_refl); lia | reflexivity]).
      replace (bd_regF S0 (de_bd x)) with (S0 + bd_ptr (de_bd x)) by (unfold bd_regF; rewrite BZF; reflexivity).
      wto 0x992dc 0x99c04.
      assert (WB : bv_wrap 32 (bd_bits (de_bd x)) = bd_bits (de_bd x))
        by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
      assert (SB : bv_swrap 32 (Z.shiftr (bd_bits (de_bd x)) 3) = bd_bits (de_bd x) / 8)
        by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; apply SysStep.swrap32_small; Z.div_mod_to_equations; lia).
      destruct (Z.leb_spec 8 (bd_ptr (de_bd x))) as [P8|P8].
      + br.
        assert (ZB : 0 < zlen bs) by lia.
        repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep).
        rewrite ?WB, ?SB. br. repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep).
        assert (LX : 1 <= Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8)).
        { assert (0 <= Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8))
            by (apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia).
          assert (Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8) <> 0)
            by (rewrite Z.lxor_eq_0_iff; Z.div_mod_to_equations; lia).
          lia. }
        replace (Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8) <? 1) with false
          by (symmetry; apply Z.ltb_ge; exact LX).
        br.
        repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
        unfold reload_dstream in RLD.
        replace (64 <? bd_bits (de_bd x)) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
        replace (8 <=? bd_ptr (de_bd x)) with true in RLD by (symmetry; apply Z.leb_le; lia).
        assert (SH3 : Z.shiftr (bd_bits (de_bd x)) 3 = bd_bits (de_bd x) / 8)
          by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        rewrite SH3 in RLD.
        rewrite (readLE64_ok bs (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) in RLD by (Z.div_mod_to_equations; lia).
        cbn [bind] in RLD. injection RLD as <- <-.
        replace (S0 + bd_ptr (de_bd x) - bd_bits (de_bd x) / 8) with (S0 + (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) by lia.
        eapply (ftA_r2s x mm jp junk j i (bd_ptr (de_bd x)) (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)
                  (Z.land (bd_bits (de_bd x)) 7));
          [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia
          | rewrite RF_huf_fdw_sm.land7_mod; pose proof (Z.mod_pos_bound (bd_bits (de_bd x)) 8); lia
          | lia | lia | lia | lia | exact I | intro; apply RERR; lia | exact (KN BL) ].
      + br. repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep).
        destruct (Z.eq_dec (bd_ptr (de_bd x)) 0) as [PZ|PZ].
        * br.
          unfold reload_dstream in RLD.
          replace (64 <? bd_bits (de_bd x)) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
          replace (8 <=? bd_ptr (de_bd x)) with false in RLD by (symmetry; apply Z.leb_gt; lia).
          replace (bd_ptr (de_bd x) =? 0) with true in RLD by (symmetry; apply Z.eqb_eq; exact PZ).
          injection RLD as _ RD. subst d2r.
          replace (mkDec (de_out x) (de_s1 x) (de_s2 x) (de_bd x)) with x in KN by (destruct x; reflexivity).
          unfold bd_regF in KN. rewrite BZF in KN.
          repeat (tryif pc_in 0x992dc 0x98318 then fail else zstep).
          destruct (Z.ltb_spec (dcap - 2) (zlen (de_out x))) as [LT|GE].
          -- br. wto 0x992dc 0x98318.
             eapply (ftA_err _ x jp junk ZSTD_error_dstSize_tooSmall);
               [exact I | apply RERR; lia | unfold ZSTD_error_dstSize_tooSmall; lia].
          -- br. wto 0x992dc 0x98318.
             eapply (KN BL ltac:(lia)). exact I.
        * assert (PP : 0 < bd_ptr (de_bd x)) by lia.
          br. repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
          rewrite ?WB, ?SB. br.
          repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
          ftA_zx. br.
          repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
          unfold reload_dstream in RLD.
          replace (64 <? bd_bits (de_bd x)) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
          replace (8 <=? bd_ptr (de_bd x)) with false in RLD by (symmetry; apply Z.leb_gt; lia).
          replace (bd_ptr (de_bd x) =? 0) with false in RLD by (symmetry; apply Z.eqb_neq; lia).
          cbv beta iota zeta in RLD.
          assert (SH3 : Z.shiftr (bd_bits (de_bd x)) 3 = bd_bits (de_bd x) / 8)
            by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
          rewrite SH3 in RLD.
          destruct (Z.ltb_spec (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8) 0) as [NB|NB].
          -- replace (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 <? 0) with true in RLD by (symmetry; apply Z.ltb_lt; lia).
             cbv beta iota zeta in RLD.
             rewrite (readLE64_ok bs (bd_ptr (de_bd x) - bd_ptr (de_bd x))) in RLD by lia.
             cbn [bind] in RLD. injection RLD as <- <-.
             br. repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
             replace (S0 + bd_ptr (de_bd x) - S0) with (bd_ptr (de_bd x)) by lia.
             ftA_norm. br.
             repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
             ftA_zx. br.
             repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
             ftA_norm.
             replace (S0 + bd_ptr (de_bd x) - bd_ptr (de_bd x)) with (S0 + (bd_ptr (de_bd x) - bd_ptr (de_bd x))) by lia.
             eapply (ftA_r2s x mm jp junk j i (bd_ptr (de_bd x)) (bd_ptr (de_bd x) - bd_ptr (de_bd x))
                              (bd_bits (de_bd x) - bd_ptr (de_bd x) * 8));
                       [ lia | lia | lia | Z.div_mod_to_equations; lia | lia | lia | lia | lia | exact I
                       | intro; apply RERR; lia | exact (KN BL) ].
          -- replace (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 <? 0) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
             cbv beta iota zeta in RLD.
             rewrite (readLE64_ok bs (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) in RLD by (Z.div_mod_to_equations; lia).
             cbn [bind] in RLD. injection RLD as <- <-.
             br. repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
             ftA_norm. br.
             repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
             ftA_zx. br.
             repeat (tryif pc_in 0x995c4 0x98318 then fail else zstep).
             ftA_norm.
             replace (S0 + bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)
               with (S0 + (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) by lia.
             eapply (ftA_r2s x mm jp junk j i (bd_ptr (de_bd x)) (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)
                              (bd_bits (de_bd x) - bd_bits (de_bd x) / 8 * 8));
                       [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia
                       | lia | lia | lia | lia | exact I | intro; apply RERR; lia | exact (KN BL) ].
  Qed.

  Lemma ftA_tl_err : forall f y, tail_loop bs d dcap true f y = R -> dcap - 2 < zlen (de_out y) ->
    R = Err ZSTD_error_dstSize_tooSmall.
  Proof.
    intros [|f] y TL Z.
    - exfalso. pose proof RESOK as RQ. rewrite <- TL in RQ. exact RQ.
    - rewrite <- TL, ftailA_loop_S. unfold FseNCount.Zlength. rewrite (proj2 (Z.ltb_lt _ _) Z). reflexivity.
  Qed.

  Lemma ftA_rl_ovf : forall dd st d', 64 < bd_bits dd -> reload_dstream bs dd = Ok (st, d') -> dstatus_eqb st Overflow = true.
  Proof.
    intros dd st d' B RL. unfold reload_dstream in RL.
    replace (64 <? bd_bits dd) with true in RL by (symmetry; apply Z.ltb_lt; lia).
    injection RL as E1 E2. subst st. reflexivity.
  Qed.

  Lemma ftA_rl_novf : forall dd st d', bd_bits dd <= 64 -> reload_dstream bs dd = Ok (st, d') -> dstatus_eqb st Overflow = false.
  Proof.
    intros dd st d' B RL. unfold reload_dstream in RL.
    replace (64 <? bd_bits dd) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    cbv beta iota zeta in RL.
    destruct (8 <=? bd_ptr dd); cbv beta iota zeta in RL.
    - match type of RL with context [readLE64 ?a ?b] => destruct (readLE64 a b) end;
        cbn [bind] in RL; try discriminate RL. injection RL as E1 E2. subst st. reflexivity.
    - destruct (bd_ptr dd =? 0); cbv beta iota zeta in RL.
      + injection RL as E1 E2. subst st. destruct (bd_bits dd <? 64); reflexivity.
      + destruct (bd_ptr dd - Z.shiftr (bd_bits dd) 3 <? 0); cbv beta iota zeta in RL;
          (match type of RL with context [readLE64 ?a ?b] => destruct (readLE64 a b) end;
           cbn [bind] in RL; try discriminate RL; injection RL as E1 E2; subst st; reflexivity).
  Qed.

  Lemma ftA_rl_ok : forall dd st d', bitd_ok bs dd -> bd_bits dd <= 64 -> reload_dstream bs dd = Ok (st, d') ->
    bitd_ok bs d' /\ bd_bits d' <= 64.
  Proof.
    intros dd st d' BK B RL. pose proof BK as (B1 & B2 & B3 & B4 & B5 & B6).
    unfold reload_dstream in RL.
    replace (64 <? bd_bits dd) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    assert (SH : Z.shiftr (bd_bits dd) 3 = bd_bits dd / 8) by (apply Z.shiftr_div_pow2; lia).
    cbv beta iota zeta in RL. rewrite SH in RL.
    destruct (Z.leb_spec 8 (bd_ptr dd)) as [P8|P8].
    - replace (8 <=? bd_ptr dd) with true in RL by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta in RL.
      rewrite (readLE64_ok bs (bd_ptr dd - bd_bits dd / 8)) in RL by (Z.div_mod_to_equations; lia).
      cbn [bind] in RL. injection RL as E1 E2. subst d'.
      pose proof (RF_huf_fdw_kit.le64v_range bs (bd_ptr dd - bd_bits dd / 8) BY) as LR. unfold le64v in LR.
      rewrite RF_huf_fdw_sm.land7_mod.
      unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero].
      repeat split; first [ intro; discriminate | Z.div_mod_to_equations; lia ].
    - replace (8 <=? bd_ptr dd) with false in RL by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta in RL.
      destruct (Z.eq_dec (bd_ptr dd) 0) as [PZ|PZ].
      + replace (bd_ptr dd =? 0) with true in RL by (symmetry; apply Z.eqb_eq; exact PZ). cbv beta iota zeta in RL.
        injection RL as E1 E2. subst d'. split; [exact BK | exact B].
      + replace (bd_ptr dd =? 0) with false in RL by (symmetry; apply Z.eqb_neq; exact PZ). cbv beta iota zeta in RL.
        destruct (Z.ltb_spec (bd_ptr dd - bd_bits dd / 8) 0) as [NB|NB].
        * replace (bd_ptr dd - bd_bits dd / 8 <? 0) with true in RL by (symmetry; apply Z.ltb_lt; lia).
          cbv beta iota zeta in RL.
          rewrite (readLE64_ok bs (bd_ptr dd - bd_ptr dd)) in RL by lia.
          cbn [bind] in RL. injection RL as E1 E2. subst d'.
          pose proof (RF_huf_fdw_kit.le64v_range bs (bd_ptr dd - bd_ptr dd) BY) as LR. unfold le64v in LR.
          unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero].
          repeat split; first [ intro; discriminate | Z.div_mod_to_equations; lia ].
        * replace (bd_ptr dd - bd_bits dd / 8 <? 0) with false in RL by (symmetry; apply Z.ltb_ge; lia).
          cbv beta iota zeta in RL.
          rewrite (readLE64_ok bs (bd_ptr dd - bd_bits dd / 8)) in RL by (Z.div_mod_to_equations; lia).
          cbn [bind] in RL. injection RL as E1 E2. subst d'.
          pose proof (RF_huf_fdw_kit.le64v_range bs (bd_ptr dd - bd_bits dd / 8) BY) as LR. unfold le64v in LR.
          unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero].
          repeat split; first [ intro; discriminate | Z.div_mod_to_equations; lia ].
  Qed.

  Lemma ftA_dec_ok : forall s dd o s' d', bitd_ok bs dd -> bd_bits dd <= 2^29 -> decode_sym d true s dd = Ok (o, s', d') ->
    bitd_ok bs d' /\ bd_bits d' <= bd_bits dd + 12 /\ 0 <= o < 256.
  Proof.
    intros s dd o s' d' BK B DS. pose proof BK as (B1 & B2 & B3 & B4 & B5 & B6).
    destruct (RF_huf_fdw_fm.fdec_facts tl [] d ltac:(lia) HCELLS HCOK s dd o s' d' DS ltac:(lia)) as (nb & NB & -> & O).
    unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero].
    repeat split; first [ lia | intro HZ; specialize (B6 HZ); lia ].
  Qed.


  Lemma ftA_loop : ftA_f1_stmt -> ftA_f2_stmt -> forall f, ftA_loop_stmt f.
  Proof.
    intros F1 F2.
    induction f as [|f IH]; intros x mm jp junk j i x1 x13 x14 x20 x21 x22 x23 x24 x25 x26 TL BOK BB FOUT LJI LD J0 I0 I.
    - exfalso. pose proof RESOK as RQ. rewrite <- TL in RQ. exact RQ.
    - pose proof TL as TL0. rewrite ftailA_loop_S in TL0.
      replace (dcap - 2 <? FseNCount.Zlength (de_out x)) with false in TL0
        by (symmetry; apply Z.ltb_ge; unfold FseNCount.Zlength; lia).
      destruct (decode_sym d true (de_s1 x) (de_bd x)) as [[[o0 s1a] d1] | e | |] eqn:DS1; cbn [bind] in TL0;
        [ | exfalso; exact (RF_huf_fdw_st.decode_sym_not_err _ _ _ _ _ DS1) | exfalso; pose proof RESOK as RQ; rewrite <- TL0 in RQ; exact RQ | exfalso; pose proof RESOK as RQ; rewrite <- TL0 in RQ; exact RQ ].
      destruct (ftA_dec_ok _ _ _ _ _ BOK BB DS1) as (BOK1 & BB1 & O0).
      eapply (ftA_d1 x mm jp junk j i o0 s1a d1 x1 x13 x14 x20 x21 x22 x23 x24 x25 x26 DS1 BOK BB LJI LD J0 I0 I).
      intros mm1 junk1 y13 y14 I1.
      destruct (reload_dstream bs d1) as [[st1 d1r] | e | |] eqn:RL1; cbn [bind] in TL0;
        [ | exfalso; exact (RF_huf_fdw_st.reload_not_err _ _ _ RL1) | exfalso; pose proof RESOK as RQ; rewrite <- TL0 in RQ; exact RQ | exfalso; pose proof RESOK as RQ; rewrite <- TL0 in RQ; exact RQ ].
      assert (LJ1 : zlen (de_out x ++ [o0]) = zlen (de_out x) + 1) by (rewrite length_app; cbn [length]; lia).
      eapply (ftA_r1 (mkDec (de_out x ++ [o0]) s1a (de_s2 x) d1) mm1 jp junk1 j i st1 d1r x1 y13 y14 x22 x23 x24 x25 x26
                RL1 BOK1 ltac:(cbn [de_out]; lia) ltac:(cbn [de_out]; lia) J0 I0 I1).
      + cbn [de_bd de_out]. intros HB HZ.
        rewrite (ftA_rl_novf _ _ _ HB RL1) in TL0. rewrite <- TL0. cbv iota. unfold ftlA_body2.
        replace (dcap - 2 <? FseNCount.Zlength (de_out x ++ [o0])) with true
          by (symmetry; apply Z.ltb_lt; unfold FseNCount.Zlength; lia).
        reflexivity.
      + cbn [de_bd]. intros HB y1 y5 y6 y7 y10 y11 y12 y13' y14' y15 y16 y17 y19 y22 y23' y24' y25' y26' y28 y29 y30 y31.
        rewrite (ftA_rl_ovf _ _ _ HB RL1) in TL0.
        eapply (F1 (mkDec (de_out x ++ [o0]) s1a (de_s2 x) d1) mm1 jp junk1 j i st1 d1r);
          [ exact RL1 | exact HB | exact BOK1 | cbn [de_out]; lia | cbn [de_out]; lia | exact J0 | exact I0 | exact I1 | ].
        rewrite <- TL0. cbn [de_s2 de_out].
        destruct (decode_sym d true (de_s2 x) d1r) as [[[o1 u1] u2] | | |]; cbn [bind];
          [ rewrite <- !app_assoc; reflexivity | reflexivity | reflexivity | reflexivity ].
      + cbn [de_bd de_out de_s1 de_s2]. intros HB HZ mm2 jp2 z1 z12 z14 z23 z24 z25 z26 I2.
        destruct (ftA_rl_ok _ _ _ BOK1 HB RL1) as (BOK2 & BB2).
        rewrite (ftA_rl_novf _ _ _ HB RL1) in TL0. cbv iota in TL0. unfold ftlA_body2 in TL0.
        replace (dcap - 2 <? FseNCount.Zlength (de_out x ++ [o0])) with false in TL0
          by (symmetry; apply Z.ltb_ge; unfold FseNCount.Zlength; lia).
        destruct (decode_sym d true (de_s2 x) d1r) as [[[o1 s2a] d2] | e | |] eqn:DS2; cbn [bind] in TL0;
          [ | exfalso; exact (RF_huf_fdw_st.decode_sym_not_err _ _ _ _ _ DS2) | exfalso; pose proof RESOK as RQ; rewrite <- TL0 in RQ; exact RQ | exfalso; pose proof RESOK as RQ; rewrite <- TL0 in RQ; exact RQ ].
        destruct (ftA_dec_ok _ _ _ _ _ BOK2 ltac:(lia) DS2) as (BOK3 & BB3 & O1).
        eapply (ftA_d2 (mkDec (de_out x ++ [o0]) s1a (de_s2 x) d1r) mm2 jp2 junk1 j i o1 s2a d2 z1 z12 z14 z23 z24 z25 z26
                  DS2 BOK2); [ cbn [de_bd]; lia | cbn [de_out]; lia | cbn [de_out]; lia | exact J0 | exact I0 | exact I2 | ].
        intros mm3 junk3 w12 w14 w23 w24 I3.
        destruct (reload_dstream bs d2) as [[st2 d2r] | e | |] eqn:RL2; cbn [bind] in TL0;
          [ | exfalso; exact (RF_huf_fdw_st.reload_not_err _ _ _ RL2) | exfalso; pose proof RESOK as RQ; rewrite <- TL0 in RQ; exact RQ | exfalso; pose proof RESOK as RQ; rewrite <- TL0 in RQ; exact RQ ].
        assert (LJ2 : zlen ((de_out x ++ [o0]) ++ [o1]) = zlen (de_out x) + 2)
          by (rewrite !length_app; cbn [length]; lia).
        eapply (ftA_r2 (mkDec ((de_out x ++ [o0]) ++ [o1]) s1a s2a d2) mm3 jp2 junk3 j i st2 d2r z1 w12 w14 w23 w24 z25 z26
                  RL2 BOK3 ltac:(cbn [de_out]; lia) ltac:(cbn [de_out]; lia) J0 I0 I3).
        * cbn [de_bd de_out]. intros HB2 HZ2.
          rewrite (ftA_rl_novf _ _ _ HB2 RL2) in TL0.
          exact (ftA_tl_err f (mkDec ((de_out x ++ [o0]) ++ [o1]) s1a s2a d2r) TL0 HZ2).
        * cbn [de_bd]. intros HB2 y1 y5 y6 y7 y10 y11 y12 y13' y14' y15 y16 y17 y19 y22 y23' y24' y25' y26' y28 y29 y30 y31.
          rewrite (ftA_rl_ovf _ _ _ HB2 RL2) in TL0.
          eapply (F2 (mkDec ((de_out x ++ [o0]) ++ [o1]) s1a s2a d2) mm3 jp2 junk3 j i st2 d2r);
            [ exact RL2 | exact HB2 | exact BOK3 | cbn [de_out]; lia | cbn [de_out]; lia | exact J0 | exact I0 | exact I3 | ].
          rewrite <- TL0. cbn [de_s1 de_out].
          destruct (decode_sym d true s1a d2r) as [[[o2 u1] u2] | | |]; cbn [bind];
            [ rewrite <- !app_assoc; reflexivity | reflexivity | reflexivity | reflexivity ].
        * cbn [de_bd de_out de_s1 de_s2]. intros HB2 HZ2 mm4 jp4 v13 v14 v20 v21 v22 v23 v24 v25 v26 I4.
          destruct (ftA_rl_ok _ _ _ BOK3 HB2 RL2) as (BOK4 & BB4).
          rewrite (ftA_rl_novf _ _ _ HB2 RL2) in TL0.
          eapply (IH (mkDec ((de_out x ++ [o0]) ++ [o1]) s1a s2a d2r) mm4 jp4 junk3 j (i + 2)
                    z1 v13 v14 v20 v21 v22 v23 v24 v25 v26);
            [ exact TL0 | exact BOK4 | cbn [de_bd]; lia | | cbn [de_out]; lia | cbn [de_out]; lia | exact J0 | lia | exact I4 ].
          cbn [de_out]. apply Forall_app; split; [apply Forall_app; split; [exact FOUT |] |];
            repeat apply Forall_cons; try apply Forall_nil; lia.
  Qed.

  Lemma ftA_f1_ok : ftA_f1_stmt.
  Proof.
    unfold AF_huf_fdt_defs.ftA_f1_stmt. intros.
    eapply (AF_huf_fdt_f.ftA_f1 RNG Q m0 SPV FF DST dcap S0 DT lo RLO RHI bs d gp tp FR fc j48 jd); eassumption.
  Qed.

  Lemma ftA_f2_ok : ftA_f2_stmt.
  Proof.
    unfold AF_huf_fdt_defs.ftA_f2_stmt. intros.
    eapply (AF_huf_fdt_f.ftA_f2 RNG Q m0 SPV FF DST dcap S0 DT lo RLO RHI bs d gp tp FR fc j48 jd); eassumption.
  Qed.

  Lemma ftA_main : forall (m : amem) (x : dec) (jp junk : list byte)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    tail_loop bs d dcap true (Datatypes.S (Z.to_nat dcap)) x = R ->
    bitd_ok bs (de_bd x) -> bd_bits (de_bd x) <= 2^29 -> zlen (de_out x) <= dcap -> Forall (fun c => 0 <= c < 256) (de_out x) ->
    munch W0 m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m lo SP1 ->
    rw_cells bsegs m (SP1 + 32) FRC ->
    rw_cells bsegs m (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)] ->
    rw_cells bsegs m (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
    u8arr bsegs m DST (map (Z_to_bv 8) (de_out x) ++ junk) -> zlen junk = dcap - zlen (de_out x) ->
    bytes_at bsegs m S0 (map (Z_to_bv 8) bs) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) x10
               x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + zlen (de_out x)))
               (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
               x26 (Z_to_bv 64 2147450880) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x99288) fc None m (seg_rom bsegs)).
  Proof using All.
    intros. eapply ftA_e; try eassumption. exact (ftA_loop ftA_f1_ok ftA_f2_ok).
  Qed.

End FTB.

Definition ftA_tail_stmtA : Prop :=
  forall (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
         (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte)
         (m : amem) (x : dec) (jp junk : list byte)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    rw_cells bsegs m0 (SPAf SPV + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
    rw_cells bsegs m0 (SPAf SPV + 80) [CB 72 j48] -> stk bsegs m0 lo (SPAf SPV) -> ATOP + 4096 <= lo ->
    lo <= SPAf SPV - DEC_STACK -> SPV mod 16 = 0 -> SPV + 16 <= 2^47 ->
    zshadow m0 (SPAf SPV + 80) 72 -> shclean m0 (SPAf SPV + 112) (SPAf SPV + 152) RLO RHI ->
    rng RNG (shad RLO) (shad RHI - shad RLO) -> rng RNG (SPAf SPV + 80) 72 -> rng RNG (shad (SPAf SPV + 80)) 9 ->
    rng RNG (SPAf SPV + 32) 32 ->
    5 <= dt_tableLog d <= 12 -> zlen (dt_cells d) = 2^(dt_tableLog d) -> RF_huf_fdw_sm.cells_ok (dt_tableLog d) (dt_cells d) ->
    dt_fastMode d = 1 ->
    rw_cells bsegs m0 DT [C2 (Z_to_bv 64 (dt_tableLog d)); C2 (Z_to_bv 64 1)] ->
    bytes_at bsegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells d))) ->
    ablk DT (DT + 4 + 4 * 2^(dt_tableLog d)) -> DT mod 4 = 0 -> zshadow m0 DT (4 + 4 * 2^(dt_tableLog d)) ->
    rng RNG DT (4 + 4 * 2^(dt_tableLog d)) -> rng RNG (shad DT) (nshad (4 + 4 * 2^(dt_tableLog d) + DT mod 8)) ->
    bytes_at bsegs m0 S0 (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs -> zlen bs <= 65536 ->
    ablk S0 (S0 + zlen bs) -> S0 + 8 <= 2^47 -> 16 <= S0 -> unpoisoned m0 S0 (S0 + zlen bs) ->
    rng RNG S0 (zlen bs) -> rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)) ->
    dres_ok (decompress_usingDTable bs d dcap true) ->
    u8arr bsegs m0 DST jd -> zlen jd = dcap -> 0 <= dcap <= 255 -> ablk DST (DST + dcap) -> 3 <= DST ->
    zshadow m0 DST dcap -> rng RNG DST dcap -> rng RNG (shad DST) (nshad (dcap + DST mod 8)) ->
    (DST + dcap <= S0 \/ S0 + zlen bs <= DST) -> (DST + dcap <= DT \/ DT + 4 + 4 * 2^(dt_tableLog d) <= DST) ->
    (S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^(dt_tableLog d) <= S0) ->
    mem_inv bsegs m0 -> artcells m0 -> zshadow m0 ABIT_MASK 128 ->
    rng RNG lo (SPAf SPV - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
    (forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       munch [(lo, SPAf SPV); (SPAf SPV + 80, SPAf SPV + 152); (DST, DST + dcap)] m0 m1 -> wmono bsegs m0 m1 ->
       mem_inv bsegs m1 -> stk bsegs m1 lo (SPAf SPV) -> rw_cells bsegs m1 (SPAf SPV + 80) [CB 72 j48'] ->
       rw_cells bsegs m1 (SPAf SPV + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
       dresA DST dcap (decompress_usingDTable bs d dcap true) m1 rv -> 0 <= rv < 2^64 ->
       evtF bsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 (SPAf SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) (Z_to_bv 64 rv)
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
                  y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             FR (Z_to_bv 64 0x98318) fc None m1 (seg_rom bsegs))) ->
    tail_loop bs d dcap true (Datatypes.S (Z.to_nat dcap)) x = decompress_usingDTable bs d dcap true ->
    bitd_ok bs (de_bd x) -> bd_bits (de_bd x) <= 2^29 -> zlen (de_out x) <= dcap -> Forall (fun c => 0 <= c < 256) (de_out x) ->
    munch [(lo, SPAf SPV); (SPAf SPV + 80, SPAf SPV + 152); (DST, DST + dcap)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
    stk bsegs m lo (SPAf SPV) ->
    rw_cells bsegs m (SPAf SPV + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
    rw_cells bsegs m (SPAf SPV + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m (SPAf SPV + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
    u8arr bsegs m DST (map (Z_to_bv 8) (de_out x) ++ junk) -> zlen junk = dcap - zlen (de_out x) ->
    bytes_at bsegs m S0 (map (Z_to_bv 8) bs) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) x10
               x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + zlen (de_out x)))
               (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
               x26 (Z_to_bv 64 2147450880) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x99288) fc None m (seg_rom bsegs)).

Theorem ftA_tailA : ftA_tail_stmtA.
Proof.
  unfold ftA_tail_stmtA.
  intros RNG Q m0 SPV FF DST dcap S0 DT lo RLO RHI bs d gp tp FR fc j48 jd m x jp junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31.
  intros.
  eapply (ftA_main RNG Q m0 SPV FF DST dcap S0 DT lo RLO RHI bs d gp tp FR fc j48 jd); eassumption.
Qed.

End CANSEC1.
