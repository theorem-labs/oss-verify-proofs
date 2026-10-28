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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_pure RF_huf_fdw_fm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fdw_seg AF_huf_fdw_top1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_fdm () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8dt_cellsC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_tableLogK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_tbl_kitAzx32_unsigned_litK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land63_modC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land64_modC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm3lbfC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm9lbf_rangeC56Stdlib6ZArith6BinInt1Z9mod_smallc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm4lbfAI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_contC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm8fdec_invK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_symbolC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_nbBitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dc_newStateI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_zeroK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6bd_ptrK46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC47Corelib4Init3Nat3mulI47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List6concatC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model@fse_cells_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit<zshadow_appWK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4chkZC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit7acc_shZC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit:cell_rd_nsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit;cell_rd_symC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit:cell_rd_nbC47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses6eq_iffK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit6out_sbC46Stdlib5Lists4List2tlC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm7zlen_tlC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_tbl_kit8zx16_litc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm5lbfA2K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:decode_symK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD01C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC46Stdlib5Lists4List9app_assocC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission6Common7SFModel<mod64_land63C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit>unsigned_byte'I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5msize02C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4sxb0C5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2;AZEROFILLEDK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HII5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface>fse_cell_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5aluop02C56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit?unpoisoned_appWC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4chkBC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4svalC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit5le64vK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm:land_b2z_1C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit=le64_lbu_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9land7_modK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBsigned_lit_small64C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8sxb_svalC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdK4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm6fmA_okC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6de_outc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm7fmA_invc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm5fmA_KC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_bdC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s2C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s1K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec01C5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm8fml_bodyC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface7bitd_okC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm:fdec_factsI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp>reload_dstreamC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_fm<fmain_loop_SC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8readLE64C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC47Corelib4Init5Logic7f_equalc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm7fmA_okrc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm8fmA_dec4K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9main_loopI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus00K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus04K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus01I46Stdlib5Lists4List6Exists00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K46Stdlib9micromega5Tauto4kind02K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus02K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus03C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z6leb_leC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit;readLE64_okK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit;le64v_rangec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm9fmA_afterc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdm6fmA_ldC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land32_modC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge?zb_shl_shr_landC56Stdlib6ZArith6BinInt1Z6leb_gtC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dstatus_eqbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z4lxorC47Corelib4Init9Datatypes7nat_indK4ELinuxProcessSemantics5Riscv5Instr5aluop06".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Section FMA.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
            (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte).
  Notation SP1 := (SPAf SPV).
  Notation tl := (dt_tableLog d).
  Notation FRC := [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)].
  Hypothesis FC32 : rw_cells bsegs m0 (SP1 + 32) FRC.
  Hypothesis FO : rw_cells bsegs m0 (SP1 + 80) [CB 72 j48].
  Hypothesis STK : stk bsegs m0 lo SP1.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SP1 - DEC_STACK.
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPH : SPV + 16 <= 2^47.
  Hypothesis ZOBJ : zshadow m0 (SP1 + 80) 72.
  Hypothesis SHC : shclean m0 (SP1 + 112) (SP1 + 152) RLO RHI.
  Hypothesis RRH : rng RNG (shad RLO) (shad RHI - shad RLO).
  Hypothesis RO : rng RNG (SP1 + 80) 72.
  Hypothesis ROs : rng RNG (shad (SP1 + 80)) 9.
  Hypothesis RO32 : rng RNG (SP1 + 32) 32.
  Hypothesis HTL : 5 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells d) = 2^tl.
  Hypothesis HCOK : RF_huf_fdw_sm.cells_ok tl (dt_cells d).
  Hypothesis FM : dt_fastMode d = 1.
  Hypothesis DTH : rw_cells bsegs m0 DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 1)].
  Hypothesis TBB : bytes_at bsegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells d))).
  Hypothesis HDT : ablk DT (DT + 4 + 4 * 2^tl).
  Hypothesis DT4 : DT mod 4 = 0.
  Hypothesis ZDT : zshadow m0 DT (4 + 4 * 2^tl).
  Hypothesis RDT : rng RNG DT (4 + 4 * 2^tl).
  Hypothesis RDTs : rng RNG (shad DT) (nshad (4 + 4 * 2^tl + DT mod 8)).
  Hypothesis SRC : bytes_at bsegs m0 S0 (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis NS : zlen bs <= 65536.
  Hypothesis HS0 : ablk S0 (S0 + zlen bs).
  Hypothesis S8 : S0 + 8 <= 2^47.
  Hypothesis S16 : 16 <= S0.
  Hypothesis USRC : unpoisoned m0 S0 (S0 + zlen bs).
  Hypothesis RS : rng RNG S0 (zlen bs).
  Hypothesis RSs : rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)).
  Hypothesis OUTA : u8arr bsegs m0 DST jd.
  Hypothesis LJD : zlen jd = dcap.
  Hypothesis DC : 0 <= dcap <= 255.
  Hypothesis HDST : ablk DST (DST + dcap).
  Hypothesis DST3 : 3 <= DST.
  Hypothesis ZDST : zshadow m0 DST dcap.
  Hypothesis RDST : rng RNG DST dcap.
  Hypothesis RDSTs : rng RNG (shad DST) (nshad (dcap + DST mod 8)).
  Hypothesis DJ2 : DST + dcap <= S0 \/ S0 + zlen bs <= DST.
  Hypothesis DJ1 : DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST.
  Hypothesis DJ3 : S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^tl <= S0.
  Hypothesis MI : mem_inv bsegs m0.
  Hypothesis RTC : artcells m0.
  Hypothesis ZMK : zshadow m0 ABIT_MASK 128.
  Hypothesis RSTK : rng RNG lo (SP1 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Notation W0 := [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].

  (* [comment removed for export] *)
  Notation TB := (DT + 4).
  Notation SHF := (Z.shiftr FF 3 + ASHOFF).

  Definition fmA_mem (mm : amem) (out : list Z) (s1 s2 : Z) (dd : bitD) (jp junk : list byte) : Prop :=
    munch W0 m0 mm /\ wmono bsegs m0 mm /\ mem_inv bsegs mm /\ stk bsegs mm lo SP1 /\
    rw_cells bsegs mm (SP1 + 32) FRC /\
    rw_cells bsegs mm (SP1 + 80) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] /\
    rw_cells bsegs mm (SP1 + 112) (bitdz_cellsA S0 dd jp) /\
    u8arr bsegs mm DST (map (Z_to_bv 8) out ++ junk) /\ zlen junk = dcap - zlen out /\
    bytes_at bsegs mm S0 (map (Z_to_bv 8) bs).
  Definition fmA_ok (x : dec) : Prop :=
    bitd_ok bs (de_bd x) /\ bd_bits (de_bd x) <= 64 /\ bd_zero (de_bd x) = false /\ zlen (de_out x) <= dcap
    /\ Forall (fun c => 0 <= c < 256) (de_out x).
  Definition fmA_okr (x : dec) : Prop :=
    bitd_ok bs (de_bd x) /\ bd_bits (de_bd x) <= 2^29 /\ zlen (de_out x) <= dcap /\ Forall (fun c => 0 <= c < 256) (de_out x).

  Notation TST pc mm out x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) x10
             x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + zlen out))
             (Z_to_bv 64 SHF) x19 x20 (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
             x26 (Z_to_bv 64 ASHOFF) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition fmA_K (r : dec) : Prop :=
    forall mm (jp junk : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
      fmA_okr r -> fmA_mem mm (de_out r) (de_s1 r) (de_s2 r) (de_bd r) jp junk ->
      evtF bsegs RNG Q (TST 0x99288 mm (de_out r) x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31).

  Notation HD pc mm out s1 s2 b p x1 x11 x14 x22 x23 x24 x25 x26 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) (Z_to_bv 64 (-3)) (Z_to_bv 64 SPV)
             (Z_to_bv 64 SP1) (Z_to_bv 64 (DST + zlen out)) x11 (Z_to_bv 64 (S0 + p)) (Z_to_bv 64 b) x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 SHF)
             (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 s1) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25 x26
             (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 s2) x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation RL pc mm out s1 s2 b p f x1 x13 x22 x23 x24 x25 x26 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) (Z_to_bv 64 (-3)) (Z_to_bv 64 SPV)
             (Z_to_bv 64 SP1) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 b) (Z_to_bv 64 (S0 + p)) x13 (Z_to_bv 64 f)
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 SHF)
             (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 s1) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25 x26
             (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 s2) x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation DCS pc mm out s1 s2 c b p x1 x13 x14 x22 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) (Z_to_bv 64 (-3)) (Z_to_bv 64 SPV)
             (Z_to_bv 64 SP1) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 b) (Z_to_bv 64 (S0 + p)) x13 x14
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 SHF)
             (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 s1) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25 x26
             (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 s2) (Z_to_bv 64 c))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation SBI pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) x10
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
             (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 DT) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
             (Z_to_bv 64 S0) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac zbnd := unfold ABIT_MASK; rewrite ?land64_mod; rewrite ?Z.shiftl_mul_pow2 by lia; (try change (2^2) with 4);
    rewrite ?Z.mod_small by lia; lia.

  (* [comment removed for export] *)
  Ltac pregs := let v5 := reg_val 5%Z in let v6 := reg_val 6%Z in let v7 := reg_val 7%Z in let v12 := reg_val 12%Z in
    let v13 := reg_val 13%Z in let v11 := reg_val 11%Z in let v17 := reg_val 17%Z in let v21 := reg_val 21%Z in
    let v22 := reg_val 22%Z in let v23 := reg_val 23%Z in let v26 := reg_val 26%Z in let v27 := reg_val 27%Z in
    let v28 := reg_val 28%Z in let v29 := reg_val 29%Z in let v30 := reg_val 30%Z in let v31 := reg_val 31%Z in
    let v1 := reg_val 1%Z in
    idtac "ra=" v1 " t0=" v5 " t1=" v6 " t2=" v7; idtac " a1=" v11 " a2=" v12 " a3=" v13 " a7=" v17;
    idtac " s5=" v21 " s6=" v22 " s7=" v23 " s10=" v26 " s11=" v27; idtac " t3=" v28 " t4=" v29 " t5=" v30 " t6=" v31;
    lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mm _) => idtac " pc=" pc " mem=" mm end.

  Lemma zx32_litS : forall c, 0 <= c < 2^32 -> zx32 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdm ()) ["CANSEC1"; "FMA"] "h02Hah11Hh24__x1h32b1h42b2h51nh61zh72Hch87__arithh94__ffh:7__sat20h;7__sat21h<7__sat22h=7__sat23h>7__sat24h?7__sat25h@7__sat26hA7__sat27hB7__sat28hC7__sat29hD7__sat30hE8__varmaphF5__withG1chH4cstrhI5cstr0p;1p;2p;3p;4p;8p;6p;7p10000p4p710g000MR0p4p710R1p8p1000kp4p7210P1p8g001Wj11Tg002<j14Tg002Zj2:Tg0037j27Tg003SR1j2ATg003nj18Tg004Qj33Tg004kj25Tg005Uj3VTg0069j1ETg006Wj2FTg007=j1eTg007nj2LTg008Hj1`Tg009Fj1XTg00:<j2>Tg00:Xj16Tg00;=j1WTg00<Aj2ITg00<aj1HTg00=Fj1GTg00=fj2BTg00>Wj2@Tg00?7j2=Tg00?_j39Tg00@Cj1UTg00AJj1TTg00Ajj1STg00BJj2RTg00Bhj1QTg00CFj1PTg00D1j2DTg00DTj2OTg00E7j4?Tg00Ebj3NTg00FEj1dTg00Fgj8cTg00GKj2bTg00Gmj2_Tg00HYj3]Tg00I8j4\Tg00Ijj2ZTP0j6KTg00Jfj2^Tg00L1j7YTg00LUj7aTg00M9R0f0R2'>p=0%12#1p=<%62#6p=[%62#6#6#6p=2%12#1#1#1p=J%12#1#1#1#1#1#1#1p=;f1R3g00MWR4g00N6R5P5g00NVR6P2g00O6FYp=Cf2R7P4P5P5P6P3P2Fap=Mg00OVR8%02g00P4R9#1R:#4R;%<:R<#<R=#4R>':R?,72'AR@g00PYRA%82RB%83RCP1%87?332f3R1/571513538RD[15731572538%81?373[REf4#8?317\DAV732P2n2001000000120000000W4W3W5PE^4C^3B^5AP2%1=RA#ERB1FB7RC#eREPCP8P71FB1,5B9382X68P8P7A3812X681L8715BCp,2rcRC#`%[9#2#2#2R1#1#2#2#1#<#J#;#;#4%XCRC'>%61#2#2#1#<#J#;#;#4,>C'Ag00Q7p,1dRC#W'IR1#H%G1#0p,2bs,I8R1#H%G1#0p,2S0R1%4<R<'B%01%0<RD1@1<#0[[1=;>170;R1%0>170?[[%0;RFg00R:RGA9;>3UW0%0?\G^0F%2:#4R:,=;%0:1:;:R?,70[\1A9;:3VGX0F%0?\G^0F%UCRC,=;%0C1:;CR?,70[\1A9;C3VGX0F%0?\G^0F%4ARA,=;%0A1:;AR?,70[\1A9;A3VGX0F%0?\G^0Fp,3DSTRF/B<%0F1@F<#0\D[p,2DTRF/B<%0F1@F<#0\D[g00RVRD#T%SD1R83%Q8%P8RDP4P5P5P6P81D80g00SB1O89R9C?,CDR4P8P9g00SiRF1D8;R;%E=5N8C?,CD5MD%d5P8P9PFAN8;BC?,CD9MD4Gc1bD6P2P7g00TPRDg00U0R6'L1_27=3D6dA]803C\b9bEbFX28%03173?'A\@^28P2fAf@O2b8b:b;b<b=b>b?b@bAbBbCbDbIbHb1,Z7EK15BE1^73EKO4b1W7WGo"). Qed.

  Lemma le1_zxbS : forall b, le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b))) = [Z_to_bv 8 b].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdm ()) ["CANSEC1"; "FMA"] "h02Hah11zh21Hh37__arithh44__ffh57__sat20h67__sat21h77__sat22h87__sat23h97__sat24h:7__sat25h;7__sat26h<8__varmaph=5__with>1bh?4cstrh@5cstr0hA1lp;1p;2p;3p;4p;7p;6p;8g001Wj10Tg0069j1ETg003nj1OTg00Ajj1LTg006Wj29Tg004kj2VTg00AJj1DTg00UPj3Cj2Aj1NTg004Qj36Tg007nj2:Tg00V0j2eTg002<j15Tg002Zj2>Tg00>Wj22Tg008Hj1XTg009Fj1UTg00:<j2=Tg00:Xj14Tg003Sj2TTg00;=j1STg00<Aj2HTg00<aj1BTg00=Fj1ITg00=fj2;Tg00?7j2@Tg0037j2<Tg00?_j3FTg00@Cj1PTg00VVj1QTg00Bhj1MTg00CFj1RTg00D1j2JTg00E7j4dTg00L1j7cTg00W4j6bTg00GKj2_Tg00Gmj2^Tg00HYj3]Tg00I8j4\Tg00WXj3[Tg000Mj6?Tg00X9j2ZTg00Xhj3YTg00Yaj8KTg00Z>j1`Tg00Znj1aTf0R0#0#0p=7%40#4p=W%40#4#4#4p=3%00#0#0#0p=G%00#0#0#0#0#0#0#0p=8g00M9R1/=0p=1g00OVR2g00P4R3#0R4#7R5#ER6#OR7#LR81960R9,V6R:,96R;%D7R<5C7f1R=,96=C7<9680XA8P8P81A7;1A79P<P<P7P8\8R>%N7R?P?P;P9P>\7/:?P21e60R?%54R7%55R>'>R9,20R;12=9562X12P2%05#7R5#7#5R@,20RA12=@9620X121:2A12A@p,2rcRA#X%W3#3#3#3R3#0#3#3#0#7#G#8#8#5%UARA'=%43#3#3#0#7#G#8#8#5,=A'Tg00Q7p,1dRA#S'HR3#B%I3#1p,2bs,H2R3#B%I3#1p,2S0R3/;>%13%1>RB123>#1[[%34#5R4,@71<17R3%141>74RC,<1[[%17RDg00R:REAF74=UW0%1C\E^0D%PARA,@7%1A1>7ARC,<1[\3AF7A=VEX0D%1C\E^0Dp,3DSTRD/;>%1D12D>#1\B[p,2DTRD/;>%1D12D>#1\B[g00RVRB#D%LB%Q2%M2%R2RBg00MWRDg00N6R>P>g00NVREPBPDP>P>PEP21J2@g00[l1J21Cdg00O6FcEb1_BEP0f2REg00TPRBg00U0R>':1^0E=6B>dA]21=C\b4b<b=A62@1g00\S[P0b3b5b6b7b8b9b:b;b@b?b29[0@E?12?9=62;eP:1Z60E?9Y:0GK1:8<GK%E5/9:#`%a:E?W>o"). Qed.

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
    lazymatch goal with MU : munch [(DST, DST + dcap)] m0 mm, DJT : disjoint_from _ TB _ |- _ =>
      let TB1 := fresh "TB1" in pose proof (bytes_at_transport bsegs _ m0 mm _ _ TBB MU DJT) as TB1
    end end.

  (* [comment removed for export] *)
  Lemma lbfA : forall c b nb, 0 <= c < 2^64 -> 0 <= b < 2^31 ->
    Z.land (c ≪ Z.land b 63) 18446744073709551615 ≫ Z.land (Z.land (bv_swrap 32 (0 - nb)) 18446744073709551615) 63
    = RF_huf_fdw_fm.lbf c b nb.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdm ()) ["CANSEC1"; "FMA"] "h01zh12Hbh22Hch31bh41ch52nbp;2p;1p;3p;6g00:<j2ITg001Wj10Tg002<j17Tg002Zj2ATg0037j2>Tg003Sj2=Tg00:Xj11Tg00]0j23Tg00]Nj29Tg00>Wj22Tg0069j1HTg00]nj2@Tg00^Kj2?Tg00_2j24Tg004Qj38Tg007nj2FTg00_Rj1<Tg000Mj6:Tg00`Vj1;Tg00aZj3DTf0R0#0#0#0#0p=C%10#1#1#1p=E%00#0p=B%00#0#0#0#0#0#0#0p=5%10#1p=G%10#1#1#1#1#1#1#1p=6g00OVR1g00M9R2f2R3'IR4g00P4R5#0R6#7R7%C6R6#0R8#7R9'A,>3'=%E5R5#7,A7,>3,=4P1f4R4f3R7%15R5#7R:'3R;'9R<%B8#5#5#5#5#5#5#5#7R8'2%H6R61@27'?R=%G5#6#6#6#6#6#6#6#7R5'3/3:R>,40f5R?1249'9/28R@12=8/29'4R=581X01P11279RA19?0/28/4>=81=X01P11@23,?6R6/28R2130:,4@=81=X01P11229R914@0=81=X01194A/28/49,F1132:%<2E:1365R2%;6E:P;%<7E:13<5R5%;<E:132:,45AD473581eW1W2X51X31W4o"). Qed.

  Lemma lbfA2 : forall c b nb, 0 <= c < 2^64 -> 0 <= b < 2^31 ->
    Z.land (Z.land (c ≪ Z.land b 63) 18446744073709551615 ≫ Z.land (Z.land (bv_swrap 32 (0 - nb)) 18446744073709551615) 63)
           18446744073709551615
    = RF_huf_fdw_fm.lbf c b nb.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdm ()) ["CANSEC1"; "FMA"] "h02Hah14__x1h21Hh37__arithh44__ffh57__sat20h67__sat21h77__sat22h87__sat23h97__sat24h:7__sat25h;7__sat26h<7__sat27h=7__sat28h>7__sat29h?7__sat30h@8__varmaphA5__withB4cstrhC5cstr0hD1zhE2HbhF2HchG1bhH1chI2nbp;1p;2p;3p;6p;4p;5p;7p;8g001Wj10Tg002<j14Tg002Zj2=Tg0037j23Tg003Sj26Tg00aZj3HTg00:Xj12Tg00]0j27Tg004Qj3BTg00>Wj2;Tg00bVj3^Tg00cXj3\Tg00`Vj1[Tg000Mj6JTg00]Nj2YTg0069j1@Tg00]nj2XTg00^Kj2WTg00_2j2VTg008Hj1UTg009Fj1TTg00:<j2>Tg00;=j1QTg00<Aj2FTg00<aj1ETg00=Fj1DTg00=fj2?Tg00?7j2:Tg00?_j3<Tg00@Cj1PTg00AJj1OTg00Ajj1RTg00BJj2STg00Bhj1iTg00CFj1hTg00D1j2NTg00DTj2gTg00E7j4CTg00Ebj3LTg00FEj1fTg00GKj2]Tg007nj2_Tg00Gmj2`Tg00HYj3aTg00I8j4bTg00d;j5cTg00L1j7dTg00LUj7eTg00Fgj8ZTg00M9R0f0R1'>p=1%01#0p=8%21#2#2#2p=I%21#2#2#2#2#2#2#2p=5%01#0#0#0#0#0#0#0p=j%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=9%01#0#0#0p=Gf1R2g00MWR3g00N6R4P4g00NVR5P1g00O6Fdp=Af2R6P3P4P4P5P2P1Fep=Kf3R7P3P4P4P5P6P2P1GZp=Mg00OVR3%16R8g00P4R9#0R:#4R;%8:R<#8R=#0R>#4R?'=R@,36'6%I9RA#4RB,=;RC,36,68P3f4R8?H76RD%2ARE#2#5RF#2#5RG#5#5#5#5#5#4RH,71f5?H87RI5B3XD3P3%8>#j#9#9#9#4RJ,;DAB31IXD3A^8769\DJ17DH%[DEJ%4ERE,77,Y8/7H%@=1X06'W/7H/7E'VP8P7P6p,2rcR7#UR8%0F#5#0#8#G#9#4%T7R7'>%0G#8#G#9#4,>7'6R7g00Q7p,1dRG#Q'FRF#ERE%DF#1RFp,2bs,F3RH#ER=%DH#1RHp,2S0RD%4<R<'?RJ%1D%1<RI1;D<#1[[RD%I:#4R:,:;RK130;RL%1:1=;:RM,30[[RN%1;ROg00R:RPA<;:2UW0R:%1M\P^0ORM%PGRG,:;RQ%1G1=;GRR,30[\LRSA<;G2VPX0ORG%1R\P^0ORR1:;?RT%1?130@[\LRUA<;?2VPX0OR?%1@\P^0ORV1:;BRW%1B130C[\LRLA<;B2VPX0ORB%1C\P^0OROp,3DSTRP/?<RX%1P1;P<#1\I[RPp,2DTRY/?<RZ%1Y1;Y<#1\I[RIg00RVRY#OR<%RYRY1S32R[%i3R\%h3R]P31N30g00SB1g39R9CC,A]R^P3P9g00SiR_1N3;R;%@>5L3CC,A]5K]R>%f4R4P>CM1]]5R5P1P6g00TPR>g00U0R`'_1`16=B>`dAa302CbR0b4b@bAX13%11R`131@'6%12R>132@'6[^13P1fCf@O2b3b5b6b7b8b9b:b;b<b=b>b?bCbBb2P8P7PEPFP=PHPJPDPKPNP:PMPQPSPGPRPWPLPBPOPTPUP?PVPXPPPZPIP<PYP[P\P]P3P9P_%@A9L3;CC,A]9K]^R^P4P^CMP5P0b4b@bAX13131C,6`132C,6>[^13P1fBf?O2b3b5b6b7b8b9b:b;b<b=b>b?bCbBb2DcEJWEWFXI3XG3WHo"). Qed.

  Ltac cell_addr := lazymatch goal with |- context [Z_to_bv 64 (TB + ?x ≪ 2 + ?y ≪ 2)] =>
    replace (TB + x ≪ 2 + y ≪ 2) with (TB + 4 * (x + y)) by (rewrite !Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia) end.

  (* [comment removed for export] *)
Lemma fdmD_zcb : forall l, zlen (concat (map fse_cell_bytes l)) = 4 * zlen l.
Proof.
  induction l as [|c l IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, Nat2Z.inj_add, IH.
  assert (L4 : length (fse_cell_bytes c) = 4%nat) by (unfold fse_cell_bytes; rewrite length_app; reflexivity).
  rewrite L4. cbn [length]. lia.
Qed.
Lemma fdmD_shr0 : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.shiftr x k = 0.
Proof. intros x k Hk Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma fdmD_cb2 : forall ce, firstn 2 (skipn (Z.to_nat 2) (fse_cell_bytes ce)) = [Z_to_bv 8 (dc_symbol ce); Z_to_bv 8 (dc_nbBits ce)].
Proof. intros ce. unfold fse_cell_bytes, le2. cbn [Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. cbn [skipn firstn app]. reflexivity. Qed.
Lemma fdmD_le2 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> [Z_to_bv 8 x; Z_to_bv 8 y] = le2 (Z_to_bv 64 (x + 256 * y)).
Proof.
  intros x y Hx Hy. unfold le2. cbn [Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia.
  f_equal; [|f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
  rewrite ?Z.shiftr_div_pow2 by lia; change (2^8) with 256; Z.div_mod_to_equations; lia.
Qed.
Lemma fdmD_lor16 : forall a b, 0 <= a -> 0 <= b < 65536 -> Z.lor (a * 65536) b = a * 65536 + b.
Proof.
  intros a b Ha Hb. assert (HL : Z.land (a * 65536) b = 0).
  { assert (Hb' : Z.land b (Z.ones 16) = b) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
    rewrite <- Hb'. rewrite (Z.land_comm b), Z.land_assoc, Z.land_ones by lia. change (2^16) with 65536.
    rewrite Z.mod_mul by lia. apply Z.land_0_l. }
  rewrite Z.add_nocarry_lxor by exact HL. symmetry. apply Z.lxor_lor. exact HL.
Qed.
Lemma fdmD_and16 : forall a b, 0 <= a -> 0 <= b < 65536 -> Z.land (a * 65536 + b) 65535 = b.
Proof.
  intros a b Ha Hb. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
  rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma fdmD_shr24 : forall s n, 0 <= s < 256 -> 0 <= n -> Z.shiftr ((s + 256 * n) * 65536) 24 = n.
Proof.
  intros s n Hs Hn. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with (65536 * 256).
  rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. Z.div_mod_to_equations. lia.
Qed.
Lemma fdmD_shr16 : forall a b, 0 <= a -> 0 <= b < 65536 -> Z.shiftr (a * 65536 + b) 16 = a.
Proof.
  intros a b Ha Hb. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536.
  rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma fdmD_lbf : forall c b nb, ((c ≪ Z.land b 63) mod 2^64) ≫ Z.land (bv_swrap 32 (0 - nb) mod 2^64) 63 = RF_huf_fdw_fm.lbf c b nb.
Proof. intros c b nb. unfold RF_huf_fdw_fm.lbf. rewrite !land63_mod. reflexivity. Qed.
Lemma fdmD_b8 : forall s n, Z_to_bv 8 (s + 256 * n) = Z_to_bv 8 s.
Proof.
  intros s n. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  change (2^8) with 256. rewrite Z.mul_comm. apply Z.mod_add. lia.
Qed.
Ltac fdmD_osbB OUTA LJ :=
    let SOK := fresh "SOK" in
    lazymatch type of OUTA with u8arr _ ?mm ?D (map (Z_to_bv 8) ?o ++ ?j) =>
    pose proof (u8arr_store_ok bsegs mm D _ (zlen o) (wa (D + zlen o)) OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) eq_refl) as SOK;
    zstep;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    end;
    rewrite ?le1_zxbS, ?le1_lit; rewrite ?fdmD_b8;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
      let OUT2 := fresh "OUTA" in
      pose proof (RF_huf_fdw_kit.out_sb bsegs mm D o j v OUTA ltac:(lia)) as OUT2;
      let LO2 := fresh "LO" in
      assert (LO2 : zlen (o ++ [v]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
      let LJ2 := fresh "LJ" in
      assert (LJ2 : zlen (List.tl j) = dcap - zlen (o ++ [v])) by (rewrite RF_huf_fdw_sm.zlen_tl by lia; lia);
      clear OUTA LJ; store_done; rename OUT2 into OUTA; rename LJ2 into LJ
    end end.
Lemma fdmD_swrap : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus. cbn [Z.of_N].
  change (2^32/2) with (2^31). rewrite Z.mod_small by lia. lia.
Qed.
Ltac fdmD_nzb := repeat match goal with |- context [Z.b2z (?x <? ?y)] =>
  first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ]; cbn [Z.b2z] end.
Ltac fdmD_nz := wk_land64; rewrite ?Z.shiftl_mul_pow2 by lia; (try change (2^2) with 4); (try change (2^16) with 65536); wk_mods; fdmD_nzb;
  repeat match goal with |- context [Z.shiftr ?x 62] => rewrite (fdmD_shr0 x 62) by lia end;
  rewrite ?fdmD_lor16 by lia; rewrite ?fdmD_and16 by lia; rewrite ?fdmD_shr24 by lia; rewrite ?fdmD_shr16 by lia;
  rewrite ?fdmD_lbf.
Ltac fdmD_zsnow ZS0 HAB SH ZSn :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch goal with MUc : munch _ m0 mm |- _ =>
  lazymatch type of ZS0 with ?P _ ?X ?n =>
    assert (ZSn : P mm X n) by (let Z1 := fresh "Z1" in let a := fresh "a" in let Ha := fresh "Ha" in
      pose proof ZS0 as Z1; hnf in Z1 |- *; intros a Ha; rewrite MUc; [apply Z1; lia | apply (SH X n HAB); lia])
  end end end.
Ltac fdmD_shzB A ZS0 HAB SH a :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    let ZSn := fresh "ZSn" in let RDB := fresh "RDB" in
    replace a with (A + (a - A)) by lia;
    fdmD_zsnow ZS0 HAB SH ZSn;
    pose proof (chkZ mm _ _ (A + (a - A)) ZSn ltac:(lia) ltac:(lia)) as RDB;
    let N := eval cbv delta [ASHOFF] in ASHOFF in
    change (Z.shiftr (A + (a - A)) 3 + ASHOFF) with (Z.shiftr (A + (a - A)) 3 + N);
    zstep; rewrite ?sxb0; clear RDB ZSn; try replace (A + (a - A)) with a by lia end.
Ltac fdmD_shzA r SH := try fold ASHOFF;
  let v := reg_val r in lazymatch v with Z_to_bv 64 (Z.shiftr ?a 3 + ASHOFF) =>
    first [ fdmD_shzB DT ZDT (ablk_sub DT (TB + 4 * 2^tl) DT (DT + (4 + 4 * 2^tl)) HDT ltac:(lia) ltac:(lia)) SH a
          | fdmD_shzB DST ZDST HDST SH a ] end.
Ltac fdmD_wst SH := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => try fdmD_nz; wk_step
  | |- evtF ?segs _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with Some ?w =>
        let dd := eval vm_compute in (decode_any w) in
        lazymatch dd with
        | Some (Load SZ1 _ _ ?rs0 _, _) =>
            let rs := eval vm_compute in (bv_unsigned rs0) in first [fdmD_shzA rs SH | zstep]
        | _ => zstep
        end end end; try fdmD_nz.
Ltac fdmD_wgo SH pcs := repeat (wk_at pcs; fdmD_wst SH).
Ltac fdmD_cellrd r k s ce NE TBH :=
  let v := reg_val r in lazymatch v with Z_to_bv 64 ?e =>
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    let RD := fresh "RDc" in
    lazymatch k with
    | 0 => pose proof (RF_huf_fdw_kit.cell_rd_ns bsegs mm TB (dt_cells d) s ce (Z_to_bv 64 e) TBH NE ltac:(lia)
                         ltac:(unfold wa; f_equal; lia)) as RD
    | 2 => pose proof (RF_huf_fdw_kit.cell_rd_off bsegs mm TB (dt_cells d) s ce 2 2 TBH NE ltac:(lia) ltac:(lia) ltac:(lia)) as RD;
           replace (TB + (4 * s + 2)) with (e + 2) in RD by lia; rewrite fdmD_cb2 in RD;
           rewrite (fdmD_le2 (dc_symbol ce) (dc_nbBits ce)) in RD by lia
    end end end.
Lemma fdmD_rweq : forall m A cs cs', rw_cells bsegs m A cs -> cs = cs' -> rw_cells bsegs m A cs'.
Proof. intros m A cs cs' H E. subst. exact H. Qed.
Lemma fdmD_shw : forall X n, ablk X (X + n) -> 0 <= n -> forall a, X <= a < X + n -> outside W0 (bv_unsigned (wa (shad a))).
Proof.
  intros X n HX Hn a Ha. pose proof (ablk_lin _ _ HX) as HXl. pose proof atop_range as ATR. unfold DEC_STACK in LO.
  pose proof (shad_outside1 X n DST dcap HDST ltac:(lia) ltac:(lia) a Ha) as O1.
  cbv delta [wa]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  cbn [outside] in *. unfold shad in *. rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
  unfold ASHOFF in *. rewrite Z.mod_small by lia.
  split; [lia|]. split; [lia|]. exact O1.
Qed.
Notation fdmD_FB pc mm p x1 x10 x11 x13 x14 x17 x20 x22 x23 x24 x25 x26 x27 x30 x31 :=
  (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) (Z_to_bv 64 (-3)) (Z_to_bv 64 SPV)
           (Z_to_bv 64 SP1) x10 x11 (Z_to_bv 64 (S0 + p)) x13 x14
           (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) x17 (Z_to_bv 64 SHF)
           (Z_to_bv 64 (DST + dcap - 3)) x20 (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25 x26
           x27 (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) x30 x31)
      FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Ltac fdmD_fpre FMM :=
  let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in let STK := fresh "STK" in
  let FRC := fresh "FRC" in let CL := fresh "CL" in let BD := fresh "BD" in let OUT := fresh "OUT" in
  let LJ := fresh "LJ" in let SR := fresh "SR" in
  destruct FMM as (MU & WM & MI & STK & FRC & CL & BD & OUT & LJ & SR);
  unfold bitdz_cellsA in BD; cbn [bd_cont bd_bits bd_ptr bd_zero] in BD;
  try (lazymatch type of OUT with u8arr _ _ _ (map _ (?a ++ ?b) ++ _) => let LA := fresh "LA" in pose proof (length_app a b) as LA; cbn [length] in LA end);
  pose proof (bytes_at_transport _ _ _ _ _ _ TBB MU ltac:(rewrite fdmD_zcb, HCELLS; cbn [disjoint_from];
    pose proof (ablk_lin _ _ HDT); pose proof atop_range; unfold DEC_STACK in LO; lia)) as TB1;
  assert (PT : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia);
  pose proof (ablk_lin _ _ HDT) as HDTl; pose proof (ablk_lin _ _ HDST) as HDSTl; pose proof (ablk_lin _ _ HS0) as HS0l; pose proof atop_range as ATR;
  unfold DEC_STACK in LO.
Ltac fdmD_fdec DS ce NE :=
  let SR := fresh "SR" in let SY := fresh "SY" in let NB := fresh "NB" in let NS := fresh "NS" in let NSB := fresh "NSB" in
  let F := fresh "F" in let P := fresh "P" in
  pose proof (RF_huf_fdw_fm.fdec_inv tl bs d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS ltac:(cbn [bd_bits]; lia)) as F;
  destruct F as (ce & NE & SR & SY & NB & NS & NSB & -> & -> & ->); cbn [bd_cont bd_bits bd_ptr bd_zero] in *;
  pose proof (Z.pow_pos_nonneg 2 (dc_nbBits ce) ltac:(lia) ltac:(lia)) as P.
Ltac fdmD_fswap := repeat match goal with
  | |- context [RF_huf_fdw_fm.lbf ?x ?y ?z + ?w] => rewrite (Z.add_comm (RF_huf_fdw_fm.lbf x y z) w)
  | H : context [RF_huf_fdw_fm.lbf ?x ?y ?z + ?w] |- _ => rewrite (Z.add_comm (RF_huf_fdw_fm.lbf x y z) w) in H end.
Ltac fdmD_fcell := first [ reflexivity | apply f_equal; apply f_equal; lia ].
Ltac fdmD_fcells := repeat (apply (f_equal2 cons); [fdmD_fcell|]); reflexivity.
Ltac fdmD_fmem1 := first [ eassumption
  | lazymatch goal with |- rw_cells _ ?m ?A _ => match goal with H : rw_cells _ m A _ |- _ =>
      eapply (fdmD_rweq _ _ _ _ H); fdmD_fcells end end
  | idtac ].
Ltac fdmD_fmem := repeat match goal with H : context [(?a ++ ?l) ++ [?y]] |- _ =>
    rewrite <- (app_assoc a l [y]) in H; cbn [app] in H end;
  unfold fmA_mem; unfold bitdz_cellsA; cbn [bd_cont bd_bits bd_ptr bd_zero];
  do 9 (split; [fdmD_fmem1|]); fdmD_fmem1.
Ltac fdmD_feq := first [ reflexivity | f_equal; lia | f_equal; rewrite ?length_app; cbn [length]; lia ].

Lemma fdmD_D1 : forall out s1 s2 c b p o0 s1a d1 mm (jp junk : list byte) (x1 x13 x14 x22 x23 x24 x25 x26 : word),
    decode_sym d true s1 (mkBD c b p false) = Ok (o0, s1a, d1) -> 0 <= s2 < 2^tl ->
    0 <= b <= 64 -> 0 <= c < 2^64 -> 0 <= p -> zlen out + 4 <= dcap ->
    fmA_mem mm out s1 s2 (mkBD c b p false) jp junk ->
    (forall mm1 (jp1 junk1 : list byte) (y1 y10 y11 y13 y14 y17 y20 y22 y23 y24 y25 y26 y27 y30 y31 : word),
       y10 = Z_to_bv 64 (DST + zlen out) -> y17 = Z_to_bv 64 (DST + zlen out) -> y13 = Z_to_bv 64 (TB + 4 * s2) ->
       y20 = Z_to_bv 64 s1a -> y22 = Z_to_bv 64 TB -> y23 = Z_to_bv 64 TB -> y24 = Z_to_bv 64 1 -> y25 = Z_to_bv 64 1 ->
       y26 = Z_to_bv 64 (bd_bits d1) -> y27 = Z_to_bv 64 ASHOFF -> y30 = Z_to_bv 64 s2 -> y31 = Z_to_bv 64 c ->
       fmA_mem mm1 (out ++ [o0]) s1a s2 d1 jp1 junk1 ->
       evtF bsegs RNG Q (fdmD_FB 0x98a2c mm1 p y1 y10 y11 y13 y14 y17 y20 y22 y23 y24 y25 y26 y27 y30 y31)) ->
    evtF bsegs RNG Q (DCS 0x98964 mm out s1 s2 c b p x1 x13 x14 x22 x23 x24 x25 x26).
Proof.
  intros out s1 s2 c b p o0 s1a d1 mm jp junk x1 x13 x14 x22 x23 x24 x25 x26 DS S2R HB HC HP HL FMM K.
  fdmD_fpre FMM. fdmD_fdec DS ce1 NE1.
  fdmD_wgo fdmD_shw [0x989bc].
  fdmD_cellrd 13%Z 2 s1 ce1 NE1 TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
  fdmD_cellrd 13%Z 0 s1 ce1 NE1 TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
  fdmD_wgo fdmD_shw [0x98a20].
  match goal with H : u8arr _ _ DST _ |- _ => match goal with LJ : zlen junk = _ |- _ => fdmD_osbB H LJ end end.
  fdmD_wgo fdmD_shw [0x98a2c].
  fdmD_fswap. eapply K; try fdmD_feq. fdmD_fswap. fdmD_fmem.
Qed.

Lemma fdmD_D2 : forall out o0 s1a s2 c b1 p o1 s2a d2 mm (jp junk : list byte) (y1 y11 y14 : word),
    decode_sym d true s2 (mkBD c b1 p false) = Ok (o1, s2a, d2) -> 0 <= s1a < 2^tl ->
    0 <= b1 <= 76 -> 0 <= c < 2^64 -> 0 <= p -> zlen out + 4 <= dcap ->
    fmA_mem mm (out ++ [o0]) s1a s2 (mkBD c b1 p false) jp junk ->
    (forall mm2 (jp2 junk2 : list byte) (z1 z10 z11 z13 z14 z17 z20 z22 z23 z24 z25 z26 z27 z30 z31 : word),
       z10 = Z_to_bv 64 (DST + zlen out) -> z17 = Z_to_bv 64 (DST + zlen out) -> z13 = Z_to_bv 64 (TB + 4 * s1a) ->
       z20 = Z_to_bv 64 s1a -> z22 = Z_to_bv 64 TB -> z23 = Z_to_bv 64 TB -> z24 = Z_to_bv 64 1 ->
       z26 = Z_to_bv 64 (bd_bits d2) -> z30 = Z_to_bv 64 s2a -> z31 = Z_to_bv 64 c ->
       fmA_mem mm2 (out ++ [o0; o1]) s1a s2a d2 jp2 junk2 ->
       evtF bsegs RNG Q (fdmD_FB 0x98acc mm2 p z1 z10 z11 z13 z14 z17 z20 z22 z23 z24 z25 z26 z27 z30 z31)) ->
    evtF bsegs RNG Q (fdmD_FB 0x98a2c mm p y1 (Z_to_bv 64 (DST + zlen out)) y11 (Z_to_bv 64 (TB + 4 * s2)) y14
                        (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 s1a) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1)
                        (Z_to_bv 64 1) (Z_to_bv 64 b1) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 s2) (Z_to_bv 64 c)).
Proof.
  intros out o0 s1a s2 c b1 p o1 s2a d2 mm jp junk y1 y11 y14 DS S1R HB HC HP HL FMM K.
  fdmD_fpre FMM. fdmD_fdec DS ce2 NE2.
  fdmD_wgo fdmD_shw [0x98a6c].
  fdmD_cellrd 13%Z 2 s2 ce2 NE2 TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
  fdmD_cellrd 13%Z 0 s2 ce2 NE2 TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
  fdmD_wgo fdmD_shw [0x98ac0].
  match goal with H : u8arr _ _ DST _ |- _ => match goal with LJ : zlen junk = _ |- _ => fdmD_osbB H LJ end end.
  fdmD_wgo fdmD_shw [0x98acc].
  fdmD_fswap. eapply K; try fdmD_feq. fdmD_fswap. fdmD_fmem.
Qed.

Lemma fdmD_D3 : forall out o0 o1 s1a s2a c b2 p o2 s1b d3 mm (jp junk : list byte) (y1 y11 y14 y25 y27 : word),
    decode_sym d true s1a (mkBD c b2 p false) = Ok (o2, s1b, d3) -> 0 <= s2a < 2^tl ->
    0 <= b2 <= 88 -> 0 <= c < 2^64 -> 0 <= p -> zlen out + 4 <= dcap ->
    fmA_mem mm (out ++ [o0; o1]) s1a s2a (mkBD c b2 p false) jp junk ->
    (forall mm3 (jp3 junk3 : list byte) (z1 z10 z11 z13 z14 z17 z20 z22 z23 z24 z25 z26 z27 z30 z31 : word),
       z10 = Z_to_bv 64 (DST + zlen out) -> z17 = Z_to_bv 64 (DST + zlen out) -> z13 = Z_to_bv 64 (TB + 4 * s2a) ->
       z20 = Z_to_bv 64 s1b -> z22 = Z_to_bv 64 TB -> z23 = Z_to_bv 64 (bd_bits d3) -> z27 = Z_to_bv 64 ASHOFF ->
       z30 = Z_to_bv 64 s2a -> z31 = Z_to_bv 64 c ->
       fmA_mem mm3 (out ++ [o0; o1; o2]) s1b s2a d3 jp3 junk3 ->
       evtF bsegs RNG Q (fdmD_FB 0x98b78 mm3 p z1 z10 z11 z13 z14 z17 z20 z22 z23 z24 z25 z26 z27 z30 z31)) ->
    evtF bsegs RNG Q (fdmD_FB 0x98acc mm p y1 (Z_to_bv 64 (DST + zlen out)) y11 (Z_to_bv 64 (TB + 4 * s1a)) y14
                        (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 s1a) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1)
                        y25 (Z_to_bv 64 b2) y27 (Z_to_bv 64 s2a) (Z_to_bv 64 c)).
Proof.
  intros out o0 o1 s1a s2a c b2 p o2 s1b d3 mm jp junk y1 y11 y14 y25 y27 DS S2R HB HC HP HL FMM K.
  fdmD_fpre FMM. fdmD_fdec DS ce3 NE3.
  fdmD_wgo fdmD_shw [0x98b0c].
  fdmD_cellrd 13%Z 2 s1a ce3 NE3 TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
  fdmD_cellrd 13%Z 0 s1a ce3 NE3 TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
  fdmD_wgo fdmD_shw [0x98b6c].
  match goal with H : u8arr _ _ DST _ |- _ => match goal with LJ : zlen junk = _ |- _ => fdmD_osbB H LJ end end.
  fdmD_wgo fdmD_shw [0x98b78].
  fdmD_fswap. eapply K; try fdmD_feq. fdmD_fswap. fdmD_fmem.
Qed.

Lemma fdmD_D4 : forall out o0 o1 o2 s1b s2a c b3 p o3 s2b d4 mm (jp junk : list byte) (y1 y11 y14 y24 y25 y26 : word),
    decode_sym d true s2a (mkBD c b3 p false) = Ok (o3, s2b, d4) ->
    0 <= b3 <= 100 -> 0 <= c < 2^64 -> 0 <= p -> zlen out + 4 <= dcap ->
    fmA_mem mm (out ++ [o0; o1; o2]) s1b s2a (mkBD c b3 p false) jp junk ->
    (forall mm2 (jp2 junk2 : list byte) (z1 z11 z14 z22 z23 z24 z25 z26 z31 : word),
       fmA_mem mm2 (out ++ [o0; o1; o2; o3]) s1b s2b d4 jp2 junk2 ->
       evtF bsegs RNG Q (HD 0x98c1c mm2 (out ++ [o0; o1; o2; o3]) s1b s2b (bd_bits d4) p z1 z11 z14 z22 z23 z24 z25 z26 z31)) ->
    evtF bsegs RNG Q (fdmD_FB 0x98b78 mm p y1 (Z_to_bv 64 (DST + zlen out)) y11 (Z_to_bv 64 (TB + 4 * s2a)) y14
                        (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 s1b) (Z_to_bv 64 TB) (Z_to_bv 64 b3) y24 y25 y26
                        (Z_to_bv 64 ASHOFF) (Z_to_bv 64 s2a) (Z_to_bv 64 c)).
Proof.
  intros out o0 o1 o2 s1b s2a c b3 p o3 s2b d4 mm jp junk y1 y11 y14 y24 y25 y26 DS HB HC HP HL FMM K.
  assert (K' : forall mm2 (jp2 junk2 : list byte) (z1 z10 z11 z13 z14 z17 z20 z22 z23 z24 z25 z26 z30 z31 : word),
       z10 = Z_to_bv 64 (DST + zlen (out ++ [o0; o1; o2; o3])) -> z17 = Z_to_bv 64 (DST + zlen (out ++ [o0; o1; o2; o3])) ->
       z13 = Z_to_bv 64 (bd_bits d4) -> z20 = Z_to_bv 64 s1b -> z30 = Z_to_bv 64 s2b ->
       fmA_mem mm2 (out ++ [o0; o1; o2; o3]) s1b s2b d4 jp2 junk2 ->
       evtF bsegs RNG Q (fdmD_FB 0x98c1c mm2 p z1 z10 z11 z13 z14 z17 z20 z22 z23 z24 z25 z26 (Z_to_bv 64 ASHOFF) z30 z31)).
  { intros. subst. eapply K. eassumption. }
  clear K.
  fdmD_fpre FMM. fdmD_fdec DS ce4 NE4.
  fdmD_wgo fdmD_shw [0x98bb4].
  fdmD_cellrd 13%Z 2 s2a ce4 NE4 TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
  fdmD_cellrd 13%Z 0 s2a ce4 NE4 TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
  fdmD_wgo fdmD_shw [0x98c08].
  match goal with H : u8arr _ _ DST _ |- _ => match goal with LJ : zlen junk = _ |- _ => fdmD_osbB H LJ end end.
  fdmD_wgo fdmD_shw [0x98c1c].
  repeat match goal with |- context [bv_swrap 32 ?x] => rewrite (fdmD_swrap x) by lia end.
  repeat match goal with H : context [bv_swrap 32 ?x] |- _ => rewrite (fdmD_swrap x) in H by lia end.
  fdmD_fswap. eapply K'; try fdmD_feq. fdmD_fswap. fdmD_fmem.
Qed.

  Lemma fmA_dec4 : forall out s1 s2 c b p o0 s1a d1 o1 s2a d2 o2 s1b d3 o3 s2b d4 mm (jp junk : list byte)
                          (x1 x13 x14 x22 x23 x24 x25 x26 : word),
    decode_sym d true s1 (mkBD c b p false) = Ok (o0, s1a, d1) -> decode_sym d true s2 d1 = Ok (o1, s2a, d2) ->
    decode_sym d true s1a d2 = Ok (o2, s1b, d3) -> decode_sym d true s2a d3 = Ok (o3, s2b, d4) ->
    0 <= b <= 64 -> 0 <= c < 2^64 -> 0 <= p -> zlen out + 4 <= dcap ->
    fmA_mem mm out s1 s2 (mkBD c b p false) jp junk ->
    (forall mm2 (jp2 junk2 : list byte) (y1 y11 y14 y22 y23 y24 y25 y26 y31 : word),
       fmA_mem mm2 (out ++ [o0; o1; o2; o3]) s1b s2b d4 jp2 junk2 ->
       evtF bsegs RNG Q (HD 0x98c1c mm2 (out ++ [o0; o1; o2; o3]) s1b s2b (bd_bits d4) p y1 y11 y14 y22 y23 y24 y25 y26 y31)) ->
    evtF bsegs RNG Q (DCS 0x98964 mm out s1 s2 c b p x1 x13 x14 x22 x23 x24 x25 x26).
Proof.
  intros out s1 s2 c b p o0 s1a d1 o1 s2a d2 o2 s1b d3 o3 s2b d4 mm jp junk x1 x13 x14 x22 x23 x24 x25 x26
    DS1 DS2 DS3 DS4 HB HC HP HL FMM K.
  pose proof (RF_huf_fdw_fm.fdec_inv tl bs d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS1 ltac:(cbn [bd_bits]; lia))
    as (ce1 & _ & _ & _ & NB1 & _ & _ & _ & _ & E1).
  cbn [bd_cont bd_bits bd_ptr bd_zero] in E1. subst d1.
  pose proof (RF_huf_fdw_fm.fdec_inv tl bs d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS2 ltac:(cbn [bd_bits]; lia))
    as (ce2 & _ & S2R & _ & NB2 & _ & _ & _ & _ & E2).
  cbn [bd_cont bd_bits bd_ptr bd_zero] in E2. subst d2.
  pose proof (RF_huf_fdw_fm.fdec_inv tl bs d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS3 ltac:(cbn [bd_bits]; lia))
    as (ce3 & _ & S1aR & _ & NB3 & _ & _ & _ & _ & E3).
  cbn [bd_cont bd_bits bd_ptr bd_zero] in E3. subst d3.
  pose proof (RF_huf_fdw_fm.fdec_inv tl bs d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS4 ltac:(cbn [bd_bits]; lia))
    as (ce4 & _ & S2aR & _ & NB4 & _ & _ & _ & _ & _).
  eapply (fdmD_D1 out s1 s2 c b p o0 s1a _ mm jp junk x1 x13 x14 x22 x23 x24 x25 x26 DS1 S2R HB HC HP HL FMM).
  intros mm1 jp1 junk1 y1 y10 y11 y13 y14 y17 y20 y22 y23 y24 y25 y26 y27 y30 y31
    E10 E17 E13 E20 E22 E23 E24 E25 E26 E27 E30 E31 FM1.
  subst y10 y17 y13 y20 y22 y23 y24 y25 y26 y27 y30 y31. cbn [bd_bits] in *.
  eapply (fdmD_D2 out o0 s1a s2 c _ p o1 s2a _ mm1 jp1 junk1 y1 y11 y14 DS2 S1aR ltac:(lia) HC HP HL FM1).
  intros mm2 jp2 junk2 z1 z10 z11 z13 z14 z17 z20 z22 z23 z24 z25 z26 z27 z30 z31
    F10 F17 F13 F20 F22 F23 F24 F26 F30 F31 FM2.
  subst z10 z17 z13 z20 z22 z23 z24 z26 z30 z31. cbn [bd_bits] in *.
  eapply (fdmD_D3 out o0 o1 s1a s2a c _ p o2 s1b _ mm2 jp2 junk2 z1 z11 z14 z25 z27 DS3 S2aR ltac:(lia) HC HP HL FM2).
  intros mm3 jp3 junk3 w1 w10 w11 w13 w14 w17 w20 w22 w23 w24 w25 w26 w27 w30 w31
    G10 G17 G13 G20 G22 G23 G27 G30 G31 FM3.
  subst w10 w17 w13 w20 w22 w23 w27 w30 w31. cbn [bd_bits] in *.
  exact (fdmD_D4 out o0 o1 o2 s1b s2a c _ p o3 s2b d4 mm3 jp3 junk3 w1 w11 w14 w24 w25 w26 DS4 ltac:(lia) HC HP HL FM3 K).
Qed.

  Lemma land_b2z_1 : forall b, Z.land (Z.b2z b) 1 = Z.b2z b.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdm ()) ["CANSEC1"; "FMA"] "p'0h01bi001bp;1p;2p;3g03NOj10Tg002<j14Tg00]0j23Tg004Qj32Tg007nj21Tg00TPR0P0g00OVR0f0R1#0R2g00P4#4'3;22P1g00U0#0,10g03<[#0,10n0110000020000W0o"). Qed.
  Lemma land_1_b2z : forall b, Z.land 1 (Z.b2z b) = Z.b2z b.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdm ()) ["CANSEC1"; "FMA"] "p'0h01bi001bp;1p;2p;3g002<j14Tg03NOj10Tg00]0j23Tg004Qj32Tg007nj21Tg00TPR0P0g00OVR0g00P4#4f0R1#0R2'3;22P1g00U0#0,10g03<[#0,10n0110000020000W0o"). Qed.

  Ltac ldbS p k :=
    let RX := fresh "RX" in
    lazymatch goal with SRC' : bytes_at bsegs ?mg S0 (map (Z_to_bv 8) bs) |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      pose proof (src_rd bsegs mg S0 bs (p + k) SRC' ltac:(lia)) as RX end;
    rewrite ?Z.add_assoc, ?Z.add_0_r in RX;
    zstep; cbv beta; clear RX.

  (* [comment removed for export] *)
  Lemma fmL_srcT : forall (W : list ivl) (m m1 : amem) (la ha : Z),
    (0 <= la /\ ha <= 2^64 /\ (forall G : Z, la < ha -> la <= 8 * G + 7 -> 8 * G < ha ->
       exists b : byte, m (wa (ASHOFF + G)) = Some b /\ gran_ok (Z.min (8 * G + 8) ha - 8 * G) b)) ->
    munch W m m1 -> appW W -> ha <= 2^47 ->
    (0 <= la /\ ha <= 2^64 /\ (forall G : Z, la < ha -> la <= 8 * G + 7 -> 8 * G < ha ->
       exists b : byte, m1 (wa (ASHOFF + G)) = Some b /\ gran_ok (Z.min (8 * G + 8) ha - 8 * G) b)).
  Proof.
    intros W m m1 la ha (L0 & H64 & HG) MU AW H47. split; [lia|]. split; [lia|].
    intros G LH LG HG2. destruct (HG G LH LG HG2) as (bb & E & GK). exists bb. split; [|exact GK].
    rewrite (MU (wa (ASHOFF + G))); [exact E|].
    pose proof (shad_outside_appW W (8 * G) AW ltac:(lia)) as OS. unfold shad in OS.
    replace ((8 * G) ≫ 3) with G in OS by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8;
      rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite Z.mod_small; [exact OS | unfold ASHOFF; lia].
  Qed.

  Lemma fmL_aw : appW [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].
  Proof.
    pose proof atop_range as ATR. pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    unfold DEC_STACK in LO. pose proof HDST as HD. unfold ablk in HD.
    unfold appW. unfold KLOW, KHIGH, KLS, AIMG_HI in *.
    destruct HD as [HD|HD];
    repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]); apply Forall_nil.
  Qed.

  Ltac fmL_br b := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with b; [cbv iota | symmetry; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      first [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.eqb_eq | apply Z.eqb_neq
            | apply Bool.negb_true_iff, Z.ltb_ge | apply Bool.negb_false_iff, Z.ltb_lt
            | apply Bool.negb_true_iff, Z.eqb_neq | apply Bool.negb_false_iff, Z.eqb_eq]; Z.div_mod_to_equations; lia] end.

  Lemma fmL_lts : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
  Proof.
    intros x y HX HY. unfold bv_lts, bv_signed, bv_swrap, bv_half_modulus. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change (2 ^ 64 / 2) with (2 ^ 63).
    rewrite (Z.mod_small x), (Z.mod_small y), (Z.mod_small (x + 2^63)), (Z.mod_small (y + 2^63)) by lia.
    replace (x + 2^63 - 2^63) with x by lia. replace (y + 2^63 - 2^63) with y by lia. reflexivity.
  Qed.

  Lemma fmL_l7 : forall x, Z.land x 7 = x mod 8.
  Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

  Lemma fmL_t : forall out s1 s2 c b p cn (st : dstatus) mm (jp junk : list byte) (x1 x13 x22 x23 x24 x25 x26 x31 : word),
    0 <= p -> p + 8 <= zlen bs -> readLE64 bs p = Ok cn -> 0 <= b <= 64 -> zlen out <= dcap ->
    fmA_mem mm out s1 s2 (mkBD c b p false) jp junk ->
    (dstatus_eqb st Unfinished && (zlen out <? dcap - 3) = false ->
       forall mm2 (jp2 : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
       fmA_mem mm2 out s1 s2 (mkBD cn b p false) jp2 junk ->
       evtF bsegs RNG Q (TST 0x99288 mm2 out y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31)) ->
    (dstatus_eqb st Unfinished = true -> zlen out < dcap - 3 ->
       forall mm2 (jp2 : list byte) (y1 y13 y14 y22 y23 y24 y25 y26 : word),
       fmA_mem mm2 out s1 s2 (mkBD cn b p false) jp2 junk ->
       evtF bsegs RNG Q (DCS 0x98964 mm2 out s1 s2 cn b p y1 y13 y14 y22 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (RL 0x988fc mm out s1 s2 b p (Z.b2z (dstatus_eqb st Unfinished)) x1 x13 x22 x23 x24 x25 x26 x31).
Proof.
intros out s1 s2 c b p cn st mm jp junk x1 x13 x22 x23 x24 x25 x26 x31 P0 P8 RLE B64 LOUT MM KX KD.
pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as HDSTl.
pose proof MM as (FMU & FWM & FMI & FSTK & FR32 & FR80 & FR112 & FOUT & FLJ & FSRC).
assert (CN : cn = Znth p bs + 2 ^ 8 * Znth (p + 1) bs + 2 ^ 16 * Znth (p + 2) bs + 2 ^ 24 * Znth (p + 3) bs
   + 2 ^ 32 * Znth (p + 4) bs + 2 ^ 40 * Znth (p + 5) bs + 2 ^ 48 * Znth (p + 6) bs + 2 ^ 56 * Znth (p + 7) bs).
{ rewrite (readLE64_ok bs p P0 P8) in RLE. injection RLE. intros E. symmetry. exact E. }
ldbS p 1. ldbS p 2. ldbS p 3. ldbS p 0. zstep. zstep. zstep. zstep. ldbS p 4. ldbS p 5. zstep. ldbS p 6. ldbS p 7.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le64_lbu_land by (apply byte_Znth; [exact BY | lia]). rewrite <- CN.
pose proof (rw_cells_store_ok_at bsegs mm (SP1 + 112) (bitdz_cellsA S0 (mkBD c b p false) jp) 0 (C8 (Z_to_bv 64 c)) 8
  (Z_to_bv 64 (SP1 + 112)) FR112 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
pose proof (rw_cells_write bsegs mm (SP1 + 112) (bitdz_cellsA S0 (mkBD c b p false) jp) 0 (C8 (Z_to_bv 64 c))
  (C8 (Z_to_bv 64 cn)) FR112 eq_refl eq_refl I) as FR112b.
replace (SP1 + 112 + Z.of_nat 0) with (SP1 + 112) in FR112b by lia. cbn [cbytes cell_upd Nat.eqb] in FR112b.
change (rw_cells bsegs (write_to_mem mm (wa (SP1 + 112)) (le8 (Z_to_bv 64 cn))) (SP1 + 112)
  (bitdz_cellsA S0 (mkBD cn b p false) jp)) in FR112b.
zstep. store_done.
let v := reg_val 13%Z in
assert (A3 : v = Z_to_bv 64 (Z.b2z (dstatus_eqb st Unfinished && (zlen out <? dcap - 3)))).
{ f_equal.
  destruct (dstatus_eqb st Unfinished); destruct (Z.ltb_spec (DST + zlen out) (DST + dcap - 3));
    destruct (Z.ltb_spec (zlen out) (dcap - 3)); try lia; reflexivity. }
rewrite A3. clear A3. zstep.
pose proof (conj FMU (conj FWM (conj FMI (conj FSTK (conj FR32 (conj FR80 (conj FR112b (conj FOUT (conj FLJ FSRC)))))))))
  as MM2.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => change (fmA_mem m2 out s1 s2 (mkBD cn b p false) jp junk) in MM2 end.
destruct (dstatus_eqb st Unfinished && (zlen out <? dcap - 3)) eqn:EX.
- cbn [Z.b2z]. fmL_br false. apply andb_true_iff in EX as (EX1 & EX2). apply Z.ltb_lt in EX2.
  eapply KD; [exact EX1 | exact EX2 | exact MM2].
- cbn [Z.b2z]. fmL_br true. eapply KX; [reflexivity | exact MM2].
Qed.

  Lemma fmL_c2 : forall out s1 s2 c b p cn (st : dstatus) mm (jp junk : list byte) (x1 x13 x22 x23 x24 x25 x26 x31 : word),
    0 <= p -> p + 8 <= zlen bs -> readLE64 bs p = Ok cn -> 0 <= b <= 64 -> zlen out <= dcap ->
    fmA_mem mm out s1 s2 (mkBD c b p false) jp junk ->
    (dstatus_eqb st Unfinished && (zlen out <? dcap - 3) = false ->
       forall mm2 (jp2 : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
       fmA_mem mm2 out s1 s2 (mkBD cn b p false) jp2 junk ->
       evtF bsegs RNG Q (TST 0x99288 mm2 out y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31)) ->
    (dstatus_eqb st Unfinished = true -> zlen out < dcap - 3 ->
       forall mm2 (jp2 : list byte) (y1 y13 y14 y22 y23 y24 y25 y26 : word),
       fmA_mem mm2 out s1 s2 (mkBD cn b p false) jp2 junk ->
       evtF bsegs RNG Q (DCS 0x98964 mm2 out s1 s2 cn b p y1 y13 y14 y22 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (RL 0x988e8 mm out s1 s2 b p (Z.b2z (dstatus_eqb st Unfinished)) x1 x13 x22 x23 x24 x25 x26 x31).
Proof.
intros out s1 s2 c b p cn st mm jp junk x1 x13 x22 x23 x24 x25 x26 x31 P0 P8 RLE B64 LOUT MM KX KD.
pose proof MM as (FMU & FWM & FMI & FSTK & FR32 & FR80 & FR112 & FOUT & FLJ & FSRC).
pose proof (ablk_lin _ _ HS0) as HS0l.
pose proof (fmL_srcT _ m0 mm S0 (S0 + zlen bs) USRC FMU fmL_aw ltac:(lia)) as UM.
destruct (AF_fse_rd_base.chkB mm S0 (S0 + zlen bs) (S0 + p + 7) UM ltac:(lia) ltac:(lia)) as (sb & RB & SB & SBR).
zstep. zstep. zstep.
let v := eval unfold ASHOFF in ASHOFF in change (Z_to_bv 64 ((S0 + p + 7) ≫ 3 + ASHOFF)) with (Z_to_bv 64 ((S0 + p + 7) ≫ 3 + v)).
zstep. zstep. rewrite !sxb_sval. destruct SB as [SB | SB].
- fmL_br false.
  eapply (fmL_t out s1 s2 c b p cn st mm jp junk x1 _ _ x23 x24 x25 x26 _ P0 P8 RLE B64 LOUT MM KX KD).
- fmL_br true. zstep. zstep. rewrite fmL_l7, fmL_lts by (pose proof (Z.mod_pos_bound (S0 + p + 7) 8); lia).
  fmL_br true.
  eapply (fmL_t out s1 s2 c b p cn st mm jp junk x1 _ _ x23 x24 x25 x26 _ P0 P8 RLE B64 LOUT MM KX KD).
Qed.

  Lemma fmA_ld : forall out s1 s2 c b p cn (st : dstatus) mm (jp junk : list byte) (x1 x13 x22 x23 x24 x25 x26 x31 : word),
    0 <= p -> p + 8 <= zlen bs -> readLE64 bs p = Ok cn -> 0 <= b <= 64 -> zlen out <= dcap ->
    fmA_mem mm out s1 s2 (mkBD c b p false) jp junk ->
    (dstatus_eqb st Unfinished && (zlen out <? dcap - 3) = false ->
       forall mm2 (jp2 : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
       fmA_mem mm2 out s1 s2 (mkBD cn b p false) jp2 junk ->
       evtF bsegs RNG Q (TST 0x99288 mm2 out y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31)) ->
    (dstatus_eqb st Unfinished = true -> zlen out < dcap - 3 ->
       forall mm2 (jp2 : list byte) (y1 y13 y14 y22 y23 y24 y25 y26 : word),
       fmA_mem mm2 out s1 s2 (mkBD cn b p false) jp2 junk ->
       evtF bsegs RNG Q (DCS 0x98964 mm2 out s1 s2 cn b p y1 y13 y14 y22 y23 y24 y25 y26)) ->
    evtF bsegs RNG Q (RL 0x988d8 mm out s1 s2 b p (Z.b2z (dstatus_eqb st Unfinished)) x1 x13 x22 x23 x24 x25 x26 x31).
Proof.
intros out s1 s2 c b p cn st mm jp junk x1 x13 x22 x23 x24 x25 x26 x31 P0 P8 RLE B64 LOUT MM KX KD.
pose proof MM as (FMU & FWM & FMI & FSTK & FR32 & FR80 & FR112 & FOUT & FLJ & FSRC).
pose proof (ablk_lin _ _ HS0) as HS0l.
pose proof (fmL_srcT _ m0 mm S0 (S0 + zlen bs) USRC FMU fmL_aw ltac:(lia)) as UM.
destruct (AF_fse_rd_base.chkB mm S0 (S0 + zlen bs) (S0 + p) UM ltac:(lia) ltac:(lia)) as (sb & RB & SB & SBR).
zstep. zstep.
let v := eval unfold ASHOFF in ASHOFF in change (Z_to_bv 64 ((S0 + p) ≫ 3 + ASHOFF)) with (Z_to_bv 64 ((S0 + p) ≫ 3 + v)).
zstep. zstep. rewrite !sxb_sval. destruct SB as [SB | SB].
- fmL_br false.
  eapply (fmL_c2 out s1 s2 c b p cn st mm jp junk x1 _ x22 x23 x24 x25 x26 _ P0 P8 RLE B64 LOUT MM KX KD).
- fmL_br true. zstep. zstep. rewrite fmL_l7, fmL_lts by (pose proof (Z.mod_pos_bound (S0 + p) 8); lia).
  fmL_br true.
  eapply (fmL_c2 out s1 s2 c b p cn st mm jp junk x1 _ x22 x23 x24 x25 x26 _ P0 P8 RLE B64 LOUT MM KX KD).
Qed.

  (* [comment removed for export] *)
  Ltac rl_zx := repeat match goal with
      | |- context [Z.lxor ?x ?y <? 1] =>
          replace (Z.lxor x y <? 1) with false by
            (symmetry; apply Z.ltb_ge;
             assert (0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); split; intro; Z.div_mod_to_equations; lia);
             assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; Z.div_mod_to_equations; lia); lia)
      | |- context [0 <? ?a] => replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia)
      end; cbn [Z.b2z Z.lxor].
  Ltac rl_wr := match goal with H : bv_wrap 32 ?x = _ |- context [bv_wrap 32 ?x] => rewrite H
    | H : bv_swrap 32 ?x = _ |- context [bv_swrap 32 ?x] => rewrite H
    | |- context [?a + ?q - ?a] => replace (a + q - a) with q by lia
    | |- context [Z.land ?x 4294967295] =>
        replace (Z.land x 4294967295) with x
          by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; Z.div_mod_to_equations; lia)
    end.
  Ltac rl_norm := repeat match goal with
    | |- context [Z.shiftl ?x 3] => replace (Z.shiftl x 3) with (x * 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia)
    | |- context [Z.land ?x ?M] =>
        replace (Z.land x M) with x
          by (first [change M with (Z.ones 64) | change M with (Z.ones 32)]; rewrite Z.land_ones by lia;
              symmetry; apply Z.mod_small; Z.div_mod_to_equations; lia)
    | |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by (Z.div_mod_to_equations; lia)
    | |- context [?x <? ?y] =>
        first [replace (x <? y) with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia)
              | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia)]
    | |- context [Z.lxor (Z.b2z true) 1] => change (Z.lxor (Z.b2z true) 1) with 0
    | |- context [Z.lxor (Z.b2z false) 1] => change (Z.lxor (Z.b2z false) 1) with 1
    end.
  Ltac rl_wk pcs := repeat (wk_at pcs; first [rl_wr | progress rl_zx | wk_step]).

  Lemma fmA_rl : forall out s1 s2 c b p (st : dstatus) d0 mm (jp junk : list byte) (x1 x11 x14 x22 x23 x24 x25 x26 x31 : word),
    reload_dstream bs (mkBD c b p false) = Ok (st, d0) ->
    bitd_ok bs (mkBD c b p false) -> b <= 64 -> zlen out <= dcap ->
    fmA_mem mm out s1 s2 (mkBD c b p false) jp junk ->
    (p = 0 -> forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
       evtF bsegs RNG Q (TST 0x99288 mm out y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31)) ->
    (0 < p -> forall mm2 (jp2 : list byte) (y1 y13 y22 y23 y24 y25 y26 y31 : word),
       fmA_mem mm2 out s1 s2 (mkBD c (bd_bits d0) (bd_ptr d0) false) jp2 junk ->
       evtF bsegs RNG Q (RL 0x988d8 mm2 out s1 s2 (bd_bits d0) (bd_ptr d0) (Z.b2z (dstatus_eqb st Unfinished))
                           y1 y13 y22 y23 y24 y25 y26 y31)) ->
    evtF bsegs RNG Q (HD 0x98808 mm out s1 s2 b p x1 x11 x14 x22 x23 x24 x25 x26 x31).
Proof.
  intros out s1 s2 c b p st d0 mm jp junk x1 x11 x14 x22 x23 x24 x25 x26 x31 RLD OKd B64 ZO FMm K0 KR.
  pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
  pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as HDSTl.
  pose proof OKd as (Oc & Ob & Op & Op8 & Oz & Ozr). cbn [bd_cont bd_bits bd_ptr bd_zero] in Oc, Ob, Op, Op8, Oz, Ozr.
  pose proof FMm as (MWm & WMm & MIm & STKm & FCm & C80m & BDm & OUTm & LJm & SRCm).
  unfold bitdz_cellsA in BDm. cbn [bd_cont bd_bits bd_ptr bd_zero] in BDm. cbv iota in BDm.
  assert (WB : bv_wrap 32 b = b) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
  assert (SB : bv_swrap 32 (b ≫ 3) = b / 8)
    by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; apply swrap32_small; Z.div_mod_to_equations; lia).
  destruct (Z.leb_spec 8 p) as [P8|P8].
  - rl_wk [0x988d8; 0x99cd8].
    unfold reload_dstream in RLD. cbn [bd_cont bd_bits bd_ptr bd_zero] in RLD.
    replace (64 <? b) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
    replace (8 <=? p) with true in RLD by (symmetry; apply Z.leb_le; lia).
    destruct (readLE64 bs (p - Z.shiftr b 3)) as [cc| | |]; cbn [bind] in RLD; try discriminate RLD.
    injection RLD as <- <-.
    cbn [bd_bits bd_ptr] in KR.
    assert (E : S0 + p - b / 8 = S0 + (p - Z.shiftr b 3)) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    rewrite E in BDm |- *.
    replace (Z.b2z (dstatus_eqb Unfinished Unfinished)) with 1 in KR by reflexivity.
    apply (KR ltac:(lia) m1 jp x1 (Z_to_bv 64 b) x22 x23 x24 x25 x26 (Z_to_bv 64 (S0 + (p - Z.shiftr b 3)))).
    exact (conj MWm (conj WMm (conj MIm (conj STKm (conj FCm (conj C80m (conj BDm (conj OUTm (conj LJm SRCm))))))))).
  - destruct (Z.eq_dec p 0) as [P0|P0].
    + rl_wk [0x99288; 0x98814; 0x99cd8]. eapply (K0 P0).
    + assert (PP : 0 < p) by lia.
      unfold reload_dstream in RLD. cbn [bd_cont bd_bits bd_ptr bd_zero] in RLD.
      replace (64 <? b) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? p) with false in RLD by (symmetry; apply Z.leb_gt; lia).
      replace (p =? 0) with false in RLD by (symmetry; apply Z.eqb_neq; lia).
      assert (SH : Z.shiftr b 3 = b / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SH in RLD.
      destruct (Z.ltb_spec (p - b / 8) 0) as [NB|NB].
      * rl_wk [0x988d8; 0x99cd8]. revert BDm. rl_norm. intros BDm.
        replace (p - b / 8 <? 0) with true in RLD by (symmetry; apply Z.ltb_lt; lia).
        cbn [bind] in RLD.
        destruct (readLE64 bs (p - p)) as [cc| | |]; cbn [bind] in RLD; try discriminate RLD.
        injection RLD as <- <-.
        cbn [bd_bits bd_ptr] in KR.
        replace (Z.b2z (dstatus_eqb EndOfBuffer Unfinished)) with 0 in KR by reflexivity.
        replace (S0 + p - p) with (S0 + (p - p)) in BDm |- * by lia.
        eapply (KR PP).
        exact (conj MWm (conj WMm (conj MIm (conj STKm (conj FCm (conj C80m (conj BDm (conj OUTm (conj LJm SRCm))))))))).
      * rl_wk [0x988d8; 0x99cd8]. revert BDm. rl_norm. intros BDm.
        replace (p - b / 8 <? 0) with false in RLD by (symmetry; apply Z.ltb_ge; lia).
        cbn [bind] in RLD.
        destruct (readLE64 bs (p - b / 8)) as [cc| | |]; cbn [bind] in RLD; try discriminate RLD.
        injection RLD as <- <-.
        cbn [bd_bits bd_ptr] in KR.
        replace (Z.b2z (dstatus_eqb Unfinished Unfinished)) with 1 in KR by reflexivity.
        replace (S0 + p - b / 8) with (S0 + (p - b / 8)) in BDm |- * by lia.
        eapply (KR PP).
        exact (conj MWm (conj WMm (conj MIm (conj STKm (conj FCm (conj C80m (conj BDm (conj OUTm (conj LJm SRCm))))))))).
  Qed.

  (* [comment removed for export] *)
  Lemma fmA_ovf : forall out s1 s2 c b p mm (jp junk : list byte)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    fmA_mem mm out s1 s2 (mkBD c b p false) jp junk ->
    (forall mm2 (jp2 : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
       fmA_mem mm2 out s1 s2 (mkBD c b p true) jp2 junk ->
       evtF bsegs RNG Q (TST 0x99288 mm2 out y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31)) ->
    evtF bsegs RNG Q (TST 0x9927c mm out x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31).
Proof.
intros out s1 s2 c b p mm jp junk x1 x5 x6 x7 x10 x11 x12 x13 x14 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 HM K.
pose proof HM as (MU & WM & MI1 & STK1 & FR1 & DS1 & BD1 & OUT1 & LJ1 & SRC1). clear HM.
pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as HDSTl.
assert (HS : store_ok bsegs mm (wa (SP1 + 128)) 8 = true).
{ replace (SP1 + 128) with (SP1 + 112 + Z.of_nat 16) by lia. eapply rw_cells_store_ok; [exact BD1 | reflexivity | reflexivity]. }
zstep. zstep. zstep.
pose proof (rw_cells_write bsegs mm (SP1 + 112) _ 16 _ (C8 (Z_to_bv 64 AZEROFILLED)) BD1 eq_refl eq_refl I) as BD2.
replace (SP1 + 112 + Z.of_nat 16) with (SP1 + 128) in BD2 by lia.
change (rw_cells bsegs (write_to_mem mm (wa (SP1 + 128)) (le8 (Z_to_bv 64 AZEROFILLED))) (SP1 + 112) (bitdz_cellsA S0 (mkBD c b p true) jp)) in BD2.
clear BD1.
lazymatch goal with |- context [le8 (Z_to_bv 64 ?v)] => change (le8 (Z_to_bv 64 v)) with (le8 (Z_to_bv 64 AZEROFILLED)) end.
store_done.
apply (K _ jp). exact (conj MU (conj WM (conj MI1 (conj STK1 (conj FR1 (conj DS1 (conj BD2 (conj OUT1 (conj LJ1 SRC1))))))))).
Qed.

  Lemma fmG_rl0 : forall c b st d0, b <= 64 -> reload_dstream bs (mkBD c b 0 false) = Ok (st, d0) ->
    dstatus_eqb st Unfinished = false /\ d0 = mkBD c b 0 false.
  Proof.
    intros c b st d0 B RL. unfold reload_dstream in RL. cbn [bd_bits bd_ptr bd_cont bd_zero] in RL.
    replace (64 <? b) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    change (8 <=? 0) with false in RL. change (0 =? 0) with true in RL. cbv iota in RL.
    destruct (b <? 64); injection RL as <- <-; split; reflexivity.
  Qed.

  Lemma fmG_rlp : forall c b p st d0, b <= 64 -> 0 < p -> reload_dstream bs (mkBD c b p false) = Ok (st, d0) ->
    readLE64 bs (bd_ptr d0) = Ok (bd_cont d0).
  Proof.
    intros c b p st d0 B P RL. unfold reload_dstream in RL. cbn [bd_bits bd_ptr bd_cont bd_zero] in RL.
    replace (64 <? b) with false in RL by (symmetry; apply Z.ltb_ge; lia). cbv iota in RL.
    destruct (8 <=? p).
    - destruct (readLE64 bs (p - Z.shiftr b 3)) as [v | e | |] eqn:E; cbn [bind] in RL; try discriminate RL.
      injection RL as <- <-. cbn [bd_ptr bd_cont]. exact E.
    - replace (p =? 0) with false in RL by (symmetry; apply Z.eqb_neq; lia). cbv iota in RL.
      destruct (p - Z.shiftr b 3 <? 0); cbv beta iota zeta in RL;
        lazymatch type of RL with context [readLE64 bs ?q] =>
          destruct (readLE64 bs q) as [v | e | |] eqn:E; cbn [bind] in RL; try discriminate RL end;
        injection RL as <- <-; cbn [bd_ptr bd_cont]; exact E.
  Qed.

  Lemma fmG_rd : forall q v, readLE64 bs q = Ok v -> 0 <= q /\ q + 8 <= zlen bs.
  Proof.
    intros q v H. unfold readLE64 in H.
    destruct ((0 <=? q) && (q + 8 <=? FseNCount.Zlength bs)) eqn:E; [|discriminate H].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2. unfold FseNCount.Zlength in E2. lia.
  Qed.

  Lemma fmG_ovr : forall f out s1 s2 c b p r, 64 < b ->
    main_loop bs d dcap true f (mkDec out s1 s2 (mkBD c b p false)) = Ok r -> r = mkDec out s1 s2 (mkBD c b p true).
  Proof.
    intros f out s1 s2 c b p r B ML. destruct f as [|f]; [discriminate ML|].
    rewrite RF_huf_fdw_fm.fmain_loop_S in ML. unfold reload_dstream in ML. cbn [de_bd bd_bits bd_cont bd_ptr] in ML.
    replace (64 <? b) with true in ML by (symmetry; apply Z.ltb_lt; lia). cbn [bind] in ML.
    unfold RF_huf_fdw_fm.fml_body in ML.
    lazymatch type of ML with context [dstatus_eqb ?s Unfinished] =>
      replace (dstatus_eqb s Unfinished) with false in ML by reflexivity end.
    cbn [andb de_out de_s1 de_s2] in ML. injection ML as <-. reflexivity.
  Qed.

  Lemma fmG_d4 : forall s1 s2 c b p o0 s1a d1 o1 s2a d2 o2 s1b d3 o3 s2b d4,
    decode_sym d true s1 (mkBD c b p false) = Ok (o0, s1a, d1) -> decode_sym d true s2 d1 = Ok (o1, s2a, d2) ->
    decode_sym d true s1a d2 = Ok (o2, s1b, d3) -> decode_sym d true s2a d3 = Ok (o3, s2b, d4) -> 0 <= b <= 64 ->
    exists n, 0 <= n <= 48 /\ d4 = mkBD c (b + n) p false /\ Forall (fun c => 0 <= c < 256) [o0; o1; o2; o3].
  Proof.
    intros s1 s2 c b p o0 s1a d1 o1 s2a d2 o2 s1b d3 o3 s2b d4 D1 D2 D3 D4 B.
    assert (T : 1 <= tl <= 12) by lia.
    destruct (RF_huf_fdw_fm.fdec_facts tl bs d T HCELLS HCOK _ _ _ _ _ D1 ltac:(cbn [bd_bits]; lia)) as (n1 & N1 & -> & O0).
    destruct (RF_huf_fdw_fm.fdec_facts tl bs d T HCELLS HCOK _ _ _ _ _ D2 ltac:(cbn [bd_bits]; lia)) as (n2 & N2 & -> & O1).
    destruct (RF_huf_fdw_fm.fdec_facts tl bs d T HCELLS HCOK _ _ _ _ _ D3 ltac:(cbn [bd_bits]; lia)) as (n3 & N3 & -> & O2).
    destruct (RF_huf_fdw_fm.fdec_facts tl bs d T HCELLS HCOK _ _ _ _ _ D4 ltac:(cbn [bd_bits]; lia)) as (n4 & N4 & -> & O3).
    exists (n1 + n2 + n3 + n4). split; [lia|]. split.
    - cbn [bd_cont bd_bits bd_ptr bd_zero]. f_equal. lia.
    - repeat constructor; lia.
  Qed.

  Lemma fmG_bok : forall c b p b' z', bitd_ok bs (mkBD c b p false) -> 0 <= b' < 2^30 -> (z' = true -> 64 < b') ->
    bitd_ok bs (mkBD c b' p z').
  Proof.
    intros c b p b' z' (H1 & H2 & H3 & H4 & H5 & H6) B Z.
    exact (conj H1 (conj B (conj H3 (conj H4 (conj H5 Z))))).
  Qed.

  Lemma fmA_loop : forall f x r mm (jp junk : list byte) (x1 x11 x14 x22 x23 x24 x25 x26 x31 : word),
    main_loop bs d dcap true f x = Ok r -> fmA_ok x ->
    fmA_mem mm (de_out x) (de_s1 x) (de_s2 x) (de_bd x) jp junk -> fmA_K r ->
    evtF bsegs RNG Q (HD 0x98808 mm (de_out x) (de_s1 x) (de_s2 x) (bd_bits (de_bd x)) (bd_ptr (de_bd x))
                        x1 x11 x14 x22 x23 x24 x25 x26 x31).
Proof.
    induction f as [|f IH]; intros x r mm jp junk x1 x11 x14 x22 x23 x24 x25 x26 x31 ML OK HM K.
    { discriminate ML. }
    destruct x as [out s1 s2 [c b p z]]. cbn [de_out de_s1 de_s2 de_bd bd_bits bd_ptr] in *.
    destruct OK as (BOK & B64 & BZ & LOU & FB). cbn [de_out de_bd bd_bits bd_zero] in BOK, B64, BZ, LOU, FB. subst z.
    rewrite RF_huf_fdw_fm.fmain_loop_S in ML. cbn [de_bd] in ML.
    destruct (reload_dstream bs (mkBD c b p false)) as [[st d0] | e | |] eqn:RL; cbn [bind] in ML; try discriminate ML.
    pose proof (RF_huf_fdw_pure.reload_facts2 bs _ st d0 BY BOK RL) as (OK0 & BB0 & BC0 & Z0 & _).
    destruct (Z0 B64) as [BZ0 _].
    pose proof BOK as (BOc & BOb & BOp & BOp8 & _). cbn [bd_cont bd_bits bd_ptr] in BOc, BOb, BOp, BOp8.
    eapply (fmA_rl out s1 s2 c b p st d0 mm jp junk); [exact RL | exact BOK | exact B64 | exact LOU | exact HM | | ].
    - intros P0 y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31. subst p.
      destruct (fmG_rl0 c b st d0 B64 RL) as [UF ->].
      unfold RF_huf_fdw_fm.fml_body in ML. cbn [de_out de_s1 de_s2] in ML. rewrite UF in ML. cbn [andb] in ML.
      injection ML as <-.
      apply (K mm jp junk).
      + unfold fmA_okr; cbn [de_out de_bd bd_bits]. split; [exact BOK|]. split; [lia|]. split; [exact LOU | exact FB].
      + exact HM.
    - intros P0 mm2 jp2 y1 y13 y22 y23 y24 y25 y26 y31 HM2.
      pose proof (fmG_rlp c b p st d0 B64 P0 RL) as RD.
      destruct d0 as [c0 b0 p0 z0]. cbn [bd_cont bd_bits bd_ptr bd_zero] in *. subst z0.
      pose proof (fmG_rd p0 c0 RD) as (P0a & P0b).
      pose proof OK0 as (O0c & O0b & O0p & _). cbn [bd_cont bd_bits bd_ptr] in O0c, O0b, O0p.
      eapply (fmA_ld out s1 s2 c b0 p0 c0 st mm2 jp2 junk); [lia | lia | exact RD | lia | exact LOU | exact HM2 | | ].
      + intros EX mm3 jp3 z1 z5 z6 z7 z10 z11 z12 z13 z14 z19 z20 z22 z23 z24 z25 z26 z28 z29 z30 z31 HM3.
        unfold RF_huf_fdw_fm.fml_body in ML. cbn [de_out de_s1 de_s2] in ML. unfold FseNCount.Zlength in ML.
        rewrite EX in ML. injection ML as <-.
        apply (K mm3 jp3 junk).
        * unfold fmA_okr; cbn [de_out de_bd bd_bits]. split; [exact OK0|]. split; [lia|]. split; [exact LOU | exact FB].
        * exact HM3.
      + intros UF LT mm3 jp3 z1 z13 z14 z22 z23 z24 z25 z26 HM3.
        unfold RF_huf_fdw_fm.fml_body in ML. cbn [de_out de_s1 de_s2] in ML. unfold FseNCount.Zlength in ML.
        rewrite UF in ML. replace (zlen out <? dcap - 3) with true in ML by (symmetry; apply Z.ltb_lt; lia).
        cbn [andb] in ML.
        destruct (decode_sym d true s1 (mkBD c0 b0 p0 false)) as [[[o0 s1a] e1] | | |] eqn:D1; cbn [bind] in ML;
          try discriminate ML.
        destruct (decode_sym d true s2 e1) as [[[o1 s2a] e2] | | |] eqn:D2; cbn [bind] in ML; try discriminate ML.
        destruct (decode_sym d true s1a e2) as [[[o2 s1b] e3] | | |] eqn:D3; cbn [bind] in ML; try discriminate ML.
        destruct (decode_sym d true s2a e3) as [[[o3 s2b] e4] | | |] eqn:D4; cbn [bind] in ML; try discriminate ML.
        destruct (fmG_d4 s1 s2 c0 b0 p0 o0 s1a e1 o1 s2a e2 o2 s1b e3 o3 s2b e4 D1 D2 D3 D4 ltac:(lia))
          as (n & N & E4 & FOs).
        eapply (fmA_dec4 out s1 s2 c0 b0 p0 o0 s1a e1 o1 s2a e2 o2 s1b e3 o3 s2b e4 mm3 jp3 junk);
          [exact D1 | exact D2 | exact D3 | exact D4 | lia | lia | lia | lia | exact HM3 | ].
        intros mm4 jp4 junk4 w1 w11 w14 w22 w23 w24 w25 w26 w31 HM4.
        subst e4. cbn [bd_bits] in *.
        assert (LO4 : zlen (out ++ [o0; o1; o2; o3]) = zlen out + 4) by (rewrite length_app; cbn [length]; lia).
        assert (FO4 : Forall (fun c => 0 <= c < 256) (out ++ [o0; o1; o2; o3])) by (apply Forall_app; split; assumption).
        zstep.
        destruct (Z.leb_spec (b0 + n) 64) as [BL|BL].
        * wk_if_true.
          apply (IH (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b (mkBD c0 (b0 + n) p0 false)) r mm4 jp4 junk4).
          -- exact ML.
          -- unfold fmA_ok; cbn [de_out de_bd bd_bits bd_zero]. split; [|split; [lia|split; [reflexivity|split; [lia|exact FO4]]]].
             apply (fmG_bok c0 b0 p0); [exact OK0 | lia | discriminate].
          -- exact HM4.
          -- exact K.
        * wk_if_false. zstep.
          apply (fmA_ovf (out ++ [o0; o1; o2; o3]) s1b s2b c0 (b0 + n) p0 mm4 jp4 junk4); [exact HM4|].
          intros mm5 jp5 v1 v5 v6 v7 v10 v11 v12 v13 v14 v19 v20 v22 v23 v24 v25 v26 v28 v29 v30 v31 HM5.
          pose proof (fmG_ovr f _ _ _ _ _ _ _ BL ML) as ->.
          apply (K mm5 jp5 junk4).
          -- unfold fmA_okr; cbn [de_out de_bd bd_bits]. split; [|split; [lia|split; [lia|exact FO4]]].
             apply (fmG_bok c0 b0 p0); [exact OK0 | lia | intros _; lia].
          -- exact HM5.
  Qed.

  (* [comment removed for export] *)
  Ltac fmG_ld H A k n a :=
    let RX := fresh "RX" in
    pose proof (rw_cells_read_at bsegs _ A _ k _ n (wa a) H eq_refl eq_refl ltac:(f_equal; lia)) as RX;
    zstep; clear RX.

  Lemma fmA_main : forall f x r mm (jp : list byte)
                          (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    main_loop bs d dcap true f x = Ok r -> de_out x = [] ->
    bitd_ok bs (de_bd x) -> bd_bits (de_bd x) <= 64 -> bd_zero (de_bd x) = false ->
    munch [(SP1 - DEC_STACK, SP1); (SP1 + 80, SP1 + 152)] m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm lo SP1 -> bytes_at bsegs mm S0 (map (Z_to_bv 8) bs) ->
    rw_cells bsegs mm (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)] ->
    rw_cells bsegs mm (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
    fmA_K r ->
    evtF bsegs RNG Q (SBI 0x987c4 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
Proof.
    intros f x r mm jp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31
      ML OE BOK B64 BZ MU WM MI1 STK1 SRC1 DS1 BD1 K.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO, MU.
    pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as HDSTl.
    destruct x as [out s1 s2 [c b p z]]. cbn [de_out de_s1 de_s2 de_bd bd_bits bd_ptr bd_zero bd_cont] in *. subst out z.
    pose proof BOK as (BOc & BOb & BOp & BOp8 & _). cbn [bd_cont bd_bits bd_ptr] in BOc, BOb, BOp, BOp8.
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FC32 MU WM ltac:(cbn; lia)) as FR1.
    zstep.
    fmG_ld BD1 (SP1 + 112) 8%nat 4%nat (SP1 + 120). cbn [bd_bits] in *. rewrite FseRdKit2.sx32_small by lia.
    zstep. zstep. zstep. zstep.
    fmG_ld FR1 (SP1 + 32) 16%nat 8%nat (SP1 + 48).
    zstep. wk_if_false.
    fmG_ld DS1 (SP1 + 80) 0%nat 8%nat (SP1 + 80).
    fmG_ld DS1 (SP1 + 80) 16%nat 8%nat (SP1 + 96).
    fmG_ld BD1 (SP1 + 112) 16%nat 8%nat (SP1 + 128).
    fmG_ld BD1 (SP1 + 112) 32%nat 8%nat (SP1 + 144).
    zstep. zstep. zstep.
    fmG_ld FR1 (SP1 + 32) 16%nat 8%nat (SP1 + 48).
    zstep.
    assert (MW0 : munch [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)] m0 mm)
      by (eapply munch_weaken; [| exact MU]; intros y HY; cbn [outside] in *; lia).
    pose proof (u8arr_transport bsegs _ _ _ _ _ OUTA MU WM ltac:(cbn; lia)) as OUT1.
    replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + zlen (@nil Z))) by (cbn; f_equal; lia).
    apply (fmA_loop f (mkDec [] s1 s2 (mkBD c b p false)) r mm jp jd).
    - exact ML.
    - unfold fmA_ok; cbn [de_out de_bd bd_bits bd_zero]. split; [exact BOK|]. split; [exact B64|].
      split; [reflexivity|]. split; [cbn; lia | constructor].
    - unfold fmA_mem; cbn [de_out de_s1 de_s2 de_bd map app].
      refine (conj MW0 (conj WM (conj MI1 (conj STK1 (conj FR1 (conj DS1 (conj BD1 (conj OUT1 (conj _ SRC1))))))))).
      cbn; lia.
    - exact K.
  Qed.
End FMA.
End CANSEC1.
