(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_fse_rd_mem AF_huf_fdw_seg AF_huf_fdw_top1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_sdm () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8dt_cellsC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_tableLogK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_tbl_kitAzx32_unsigned_litK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:shr_land64C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land63_modC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land64_modI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_contC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm7dec_invK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_symbolC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_nbBitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dc_newStateC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6bd_ptrC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_zeroK46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit;rng_mask_shC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC47Corelib4Init3Nat3mulI47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List6concatC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model@fse_cells_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit<zshadow_appWC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4chkZC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit7acc_shZC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit:cell_rd_nsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit;cell_rd_symC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit:cell_rd_nbC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit8maskA_rdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le4C47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses6eq_iffK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit6out_sbC46Stdlib5Lists4List2tlC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm7zlen_tlC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm8lowbitsAC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common7SFModel<mod64_land63c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm9zx32_litSC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_tbl_kit8zx16_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_land_lK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:decode_symK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD01C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr09C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC46Stdlib5Lists4List9app_assocC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit>unsigned_byte'K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize03C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4sxb0C5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2;AZEROFILLEDK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HII5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00C5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface29ABIT_MASKI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface>fse_cell_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit?unpoisoned_appWC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4chkBC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4svalC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit5le64vK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm:land_b2z_1C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit=le64_lbu_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9land7_modK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBsigned_lit_small64C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8sxb_svalC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdK4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm6smA_okC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6de_outc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm7smA_invc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm5smA_KC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_bdC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s2C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s1K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec01C5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm7ml_bodyC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface7bitd_okC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm9dec_factsI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp>reload_dstreamC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm;main_loop_SC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8readLE64C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC47Corelib4Init5Logic7f_equalc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm7smA_okrc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm8smA_dec4K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9main_loopI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus00K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus04K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus01I46Stdlib5Lists4List6Exists00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K46Stdlib9micromega5Tauto4kind02K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus02K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus03C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z6leb_leC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit;readLE64_okK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_fdw_kit;le64v_rangec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm7bd_regAc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm9smA_afterc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_sdm6smA_ldC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land32_modC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge?zb_shl_shr_landC56Stdlib6ZArith6BinInt1Z6leb_gtC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dstatus_eqbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5aluop06".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Section SDM.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
            (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte).
  Notation SP1 := (SPAf SPV).
  Notation tl := (dt_tableLog d).
  Hypothesis FC32 : rw_cells bsegs m0 (SP1 + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)].
  Hypothesis FOBJ : rw_cells bsegs m0 (SP1 + 80) [CB 72 j48].
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
  Hypothesis FM : dt_fastMode d = 0.
  Hypothesis DTH : rw_cells bsegs m0 DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 0)].
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
  Hypothesis RESOK : dres_ok (decompress_usingDTable bs d dcap false).
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
  Hypothesis K : forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       munch W0 m0 m1 -> wmono bsegs m0 m1 ->
       mem_inv bsegs m1 -> stk bsegs m1 lo SP1 -> rw_cells bsegs m1 (SP1 + 80) [CB 72 j48'] ->
       rw_cells bsegs m1 (SP1 + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
       dresA DST dcap (decompress_usingDTable bs d dcap false) m1 rv -> 0 <= rv < 2^64 ->
       evtF bsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 rv)
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
                  y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             FR (Z_to_bv 64 0x98318) fc None m1 (seg_rom bsegs)).

  
  Notation SBI pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) x10
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
             (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 DT) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
             (Z_to_bv 64 S0) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SDPRE d0 v1 d1 st1 d1r v2 d2 st2 d2r :=
    (init_dstream bs = Ok d0 /\ read_bits d0 tl = Ok (v1, d1) /\ reload_dstream bs d1 = Ok (st1, d1r) /\
     read_bits d1r tl = Ok (v2, d2) /\ reload_dstream bs d2 = Ok (st2, d2r)).
  Notation SDMEM m3 v1 v2 := (munch W0 m0 m3 /\ wmono bsegs m0 m3 /\ mem_inv bsegs m3 /\ stk bsegs m3 lo SP1 /\
     bytes_at bsegs m3 S0 (map (Z_to_bv 8) bs) /\
     rw_cells bsegs m3 (SP1 + 80) [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 (DT + 4))] /\
     rw_cells bsegs m3 (SP1 + 96) [C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 (DT + 4))]).
  Notation SML pc mm ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (MS (mkR ra (Z_to_bv 64 SP1) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + dcap - 3)) s4 (Z_to_bv 64 (DST + dcap))
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SMH pc mm x ra a0 a1 a4 s7 s8 s9 s10 t3 t6 :=
    (SML pc mm ra (Z_to_bv 64 (DST + zlen (de_out x))) (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) a0 a1
         (Z_to_bv 64 (S0 + bd_ptr (de_bd x))) (Z_to_bv 64 (bd_bits (de_bd x))) a4
         (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
         (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) s7 s8 s9 s10 (Z_to_bv 64 2147450880) t3
         (Z_to_bv 64 (DST + zlen (de_out x))) (Z_to_bv 64 2147450880) t6).

  
  Definition sdm_ok (x : dec) : Prop :=
    0 < zlen bs /\ bitd_ok bs (de_bd x) /\ bd_zero (de_bd x) = false /\ zlen (de_out x) <= dcap /\
    Forall (fun c => 0 <= c < 256) (de_out x).
  Definition sdm_mem (m1 : amem) (out : list Z) (s1 s2 : Z) : Prop :=
    munch W0 m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo SP1 /\
    bytes_at bsegs m1 S0 (map (Z_to_bv 8) bs) /\
    (exists junk, u8arr bsegs m1 DST (map (Z_to_bv 8) out ++ junk) /\ zlen junk = dcap - zlen out) /\
    rw_cells bsegs m1 (SP1 + 80) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4))] /\
    rw_cells bsegs m1 (SP1 + 96) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 (DT + 4))].

  
  Definition sdm_K2936 (x22 x23 x24 x25 : word) : Prop :=
    forall m3 d0 v1 d1 st1 d1r v2 d2 st2 d2r st d3 jp (r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      SDPRE d0 v1 d1 st1 d1r v2 d2 st2 d2r -> reload_dstream bs d2r = Ok (st, d3) -> dstatus_eqb st Overflow = false ->
      bitd_ok bs d3 -> bd_bits d3 <= 64 -> bd_zero d3 = false -> SDMEM m3 v1 v2 ->
      rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d3 jp) ->
      evtF bsegs RNG Q (SBI 0x98cd8 m3 r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  
  Definition sdm_K5528 : Prop :=
    forall (r : dec) (m2 : amem) (jp junk : list byte) (x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    decompress_usingDTable bs d dcap false = tail_loop bs d dcap false (Datatypes.S (Z.to_nat dcap)) r ->
    0 < zlen bs -> bitd_ok bs (de_bd r) -> bd_bits (de_bd r) <= 2^29 -> zlen (de_out r) <= dcap -> Forall (fun c => 0 <= c < 256) (de_out r) ->
    munch W0 m0 m2 -> wmono bsegs m0 m2 ->
    mem_inv bsegs m2 -> stk bsegs m2 lo SP1 -> bytes_at bsegs m2 S0 (map (Z_to_bv 8) bs) ->
    u8arr bsegs m2 DST (map (Z_to_bv 8) (de_out r) ++ junk) -> zlen junk = dcap - zlen (de_out r) ->
    rw_cells bsegs m2 (SP1 + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
    rw_cells bsegs m2 (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SP1 + 96) [C8 (Z_to_bv 64 (de_s1 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SP1 + 112) (bitdz_cellsA S0 (de_bd r) jp) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 (DST + zlen (de_out r))) x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
               x10 x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
               (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + dcap - 3)) x20 (Z_to_bv 64 (DST + dcap))
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x996f8) fc None m2 (seg_rom bsegs)).
  Definition sdm_X5528 (r : dec) : Prop :=
    forall (m2 : amem) (jp junk : list byte) (x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    0 < zlen bs -> bitd_ok bs (de_bd r) -> bd_bits (de_bd r) <= 2^29 -> zlen (de_out r) <= dcap -> Forall (fun c => 0 <= c < 256) (de_out r) ->
    munch W0 m0 m2 -> wmono bsegs m0 m2 ->
    mem_inv bsegs m2 -> stk bsegs m2 lo SP1 -> bytes_at bsegs m2 S0 (map (Z_to_bv 8) bs) ->
    u8arr bsegs m2 DST (map (Z_to_bv 8) (de_out r) ++ junk) -> zlen junk = dcap - zlen (de_out r) ->
    rw_cells bsegs m2 (SP1 + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
    rw_cells bsegs m2 (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SP1 + 96) [C8 (Z_to_bv 64 (de_s1 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SP1 + 112) (bitdz_cellsA S0 (de_bd r) jp) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 (DST + zlen (de_out r))) x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
               x10 x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
               (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + dcap - 3)) x20 (Z_to_bv 64 (DST + dcap))
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x996f8) fc None m2 (seg_rom bsegs)).
  Lemma sdm_X5528_of : sdm_K5528 -> forall r, decompress_usingDTable bs d dcap false = tail_loop bs d dcap false (Datatypes.S (Z.to_nat dcap)) r -> sdm_X5528 r.
  Proof.
    intros KT r DQ m2 jp junk x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    exact (KT r m2 jp junk x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 DQ).
  Qed.

  
  Definition sdm_K2936L (f : nat) (r : dec) : Prop :=
    forall x m3 jp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6 : word),
      main_loop bs d dcap false f x = Ok r -> de_out x = [] -> sdm_ok x -> bd_bits (de_bd x) <= 64 ->
      sdm_mem m3 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q (SBI 0x98cd8 m3 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).
  Definition sdm_K3004 (f : nat) (r : dec) : Prop :=
    forall x m1 jp (ra a0 a1 a4 s7 s8 s9 s10 t3 t6 : word),
      main_loop bs d dcap false f x = Ok r -> sdm_ok x -> bd_bits (de_bd x) <= 64 ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q (SMH 0x98d1c m1 x ra a0 a1 a4 s7 s8 s9 s10 t3 t6).
  Definition sdm_K3124 (f : nat) (r : dec) : Prop :=
    forall x m1 jp (ra a0 a1 a4 s7 s8 s9 s10 t3 t6 : word),
      main_loop bs d dcap false (Datatypes.S f) x = Ok r -> sdm_ok x -> bd_bits (de_bd x) <= 64 -> 8 <= bd_ptr (de_bd x) ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q (SMH 0x98d94 m1 x ra a0 a1 a4 s7 s8 s9 s10 t3 t6).
  Definition sdm_K3180 (f : nat) (r : dec) : Prop :=
    forall x st d0 c m1 jp (ra a0 a3 a4 s7 s8 s9 t3 t6 : word),
      RF_huf_fdw_sm.ml_body dcap bs d f x st d0 = Ok r -> reload_dstream bs (de_bd x) = Ok (st, d0) ->
      (st = Unfinished \/ st = EndOfBuffer) -> sdm_ok x -> bd_bits (de_bd x) <= 64 ->
      bitd_ok bs d0 -> bd_zero d0 = false -> bd_bits d0 <= 64 -> bd_ptr d0 + 8 <= zlen bs -> bd_cont d0 = le64v bs (bd_ptr d0) ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) ->
      rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (mkBD c (bd_bits d0) (bd_ptr d0) false) jp) ->
      evtF bsegs RNG Q
        (SML 0x98dcc m1 ra (Z_to_bv 64 (DST + zlen (de_out x))) (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) a0
             (Z_to_bv 64 (Z.b2z (dstatus_eqb st Unfinished))) (Z_to_bv 64 (S0 + bd_ptr d0)) a3 a4
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
             (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) s7 s8 s9 (Z_to_bv 64 (bd_bits d0)) (Z_to_bv 64 2147450880) t3
             (Z_to_bv 64 (DST + zlen (de_out x))) (Z_to_bv 64 2147450880) t6).
  Definition sdm_K4120 (f : nat) (r : dec) : Prop :=
    forall x m1 jp (ra a1 a4 s7 s8 s9 s10 s11 t3 t6 : word),
      main_loop bs d dcap false f x = Ok r -> sdm_ok x -> bd_bits (de_bd x) <= 2^29 -> 4 <= zlen (de_out x) ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q
        (SML 0x99178 m1 ra (Z_to_bv 64 (DST + zlen (de_out x) - 4)) (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8))
             (Z_to_bv 64 (2^64 - 5)) a1 (Z_to_bv 64 (S0 + bd_ptr (de_bd x))) (Z_to_bv 64 (bd_bits (de_bd x))) a4
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
             (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) s7 s8 s9 s10 s11 t3
             (Z_to_bv 64 (DST + zlen (de_out x) - 4)) (Z_to_bv 64 2147450880) t6).
  Definition sdm_K5516 (f : nat) (r : dec) : Prop :=
    forall x m1 jp (ra t1 t2 a0 a1 a2 a3 a4 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
      main_loop bs d dcap false f x = Ok r -> sdm_ok x -> 64 < bd_bits (de_bd x) <= 2^29 ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q
        (SML 0x996ec m1 ra (Z_to_bv 64 (DST + zlen (de_out x))) t1 t2 a0 a1 a2 a3 a4
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK) s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  
  Definition sdm_segE : Prop := forall f r, sdm_K3004 f r -> sdm_K2936L f r.
  Definition sdm_segH : Prop := forall f r, sdm_K3124 f r -> sdm_K3180 f r -> sdm_X5528 r -> sdm_K3004 (Datatypes.S f) r.
  Definition sdm_segF : Prop := forall f r, sdm_K3180 f r -> sdm_K3124 f r.
  Definition sdm_segD : Prop := forall f r, sdm_K4120 f r -> sdm_X5528 r -> sdm_K3180 f r.
  Definition sdm_segB : Prop := forall f r, sdm_K3004 f r -> sdm_K5516 f r -> sdm_K4120 f r.
  Definition sdm_segX : Prop := forall f r, sdm_X5528 r -> sdm_K5516 f r.

  
  Definition sdm_loopA : Prop := forall f r, sdm_X5528 r -> sdm_K3004 f r.
  Definition sdm_stmtA : Prop := forall f r, sdm_X5528 r -> sdm_K2936L f r.

  Lemma sdm_loop_of : sdm_segH -> sdm_segF -> sdm_segD -> sdm_segB -> sdm_segX -> sdm_loopA.
  Proof.
    intros SH SF SD SB SX f r KX. induction f as [|f IH].
    - intros x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML. cbn [main_loop] in ML. discriminate ML.
    - pose proof (SD f r (SB f r IH (SX f r KX)) KX) as K3.
      exact (SH f r (SF f r K3) K3 KX).
  Qed.

  Lemma sdm_stmt_of : sdm_segE -> sdm_loopA -> sdm_stmtA.
  Proof. intros SE SL f r KX. exact (SE f r (SL f r KX)). Qed.

  Lemma sdm_segX_ok : sdm_segX.
  Proof.
    intros f r KX x m1 jp ra t1 t2 a0 a1 a2 a3 a4 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ML OK B MEM CELLS.
    destruct x as [out s1 s2 [c b p z]]. cbn [de_out de_s1 de_s2 de_bd bd_bits bd_cont bd_ptr bd_zero] in *.
    destruct f as [|f]; [discriminate ML|].
    cbn [main_loop de_bd de_out de_s1 de_s2] in ML. unfold reload_dstream in ML. cbn [bd_bits bd_cont bd_ptr] in ML.
    replace (64 <? b) with true in ML by (symmetry; apply Z.ltb_lt; lia).
    cbn in ML. injection ML as <-.
    pose proof OK as (NB & BOK & BZ & OL & OB). cbn [de_bd de_out bd_zero] in BZ, OL, OB. subst z.
    pose proof MEM as (MU & WM & MI1 & STK1 & SRC1 & (junk & OUT1 & LJ) & DS2 & DS1).
    unfold bitdz_cellsA in CELLS. cbn [bd_cont bd_bits bd_ptr bd_zero] in CELLS.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as LDS.
    zstep. zstep. zstep.
    eapply (KX m jp junk); cbn [de_out de_s1 de_s2 de_bd bd_bits bd_cont bd_ptr bd_zero];
      [exact NB | | lia | exact OL | exact OB | exact MU | exact WM | exact MI1 | exact STK1 | exact SRC1 | exact OUT1 | exact LJ
      | eapply rw_cells_transport; [exact FC32 | exact MU | exact WM | cbn; lia] | exact DS2 | exact DS1 | exact CELLS].
    unfold bitd_ok in *. cbn [de_bd bd_cont bd_bits bd_ptr bd_zero] in BOK |- *. destruct BOK as (Oc & Ob & Op & Op8 & Oz & _).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Oz | intros _; lia].
  Qed.

  Local Ltac sm_br b := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with b; [cbv iota | symmetry; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      first [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.eqb_eq | apply Z.eqb_neq
            | apply Bool.negb_true_iff, Z.ltb_ge | apply Bool.negb_false_iff, Z.ltb_lt
            | apply Bool.negb_true_iff, Z.eqb_neq | apply Bool.negb_false_iff, Z.eqb_eq]; Z.div_mod_to_equations; lia] end.

  Lemma sdm_segE_ok : sdm_segE.
  Proof.
    intros f r KE x m3 jp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6 ML DE OK B MEM CELLS.
    pose proof OK as (NB & BOK & BZ & OL & OB).
    pose proof MEM as (MU & WM & MI3 & STK3 & SRC3 & (junk & OUT3 & LJ) & DS2 & DS1).
    pose proof BOK as (Oc & Ob & Op & Op8 & Oz & _).
    pose proof CELLS as BD3. unfold bitdz_cellsA in BD3. rewrite BZ in BD3. cbv iota in BD3.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as LDS.
    pose proof FC32 as FC3. eapply rw_cells_transport in FC3; [| exact MU | exact WM | cbn; lia].
    repeat zstep.
    rewrite sx32_small; [| first [ lia | rewrite unsigned_lit by lia; lia ]].
    sm_br false. do 7 zstep.
    replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + zlen (de_out x))) by (rewrite DE; cbn [length Z.of_nat]; rewrite Z.add_0_r; reflexivity).
    eapply (KE x m3 jp); [exact ML | exact OK | exact B | exact MEM | exact CELLS].
  Qed.

  Lemma sdm_segB_ok : sdm_segB.
  Proof.
    intros f r K3 K5 x m1 jp ra a1 a4 s7 s8 s9 s10 s11 t3 t6 ML OK B L4 MEM CELLS.
    pose proof OK as (NB & BOK & BZ & OL & OB).
    pose proof MEM as (MU & WM & MI1 & STK1 & SRC1 & (junk & OUT1 & LJ) & DS2 & DS1).
    pose proof BOK as (Oc & Ob & Op & Op8 & Oz & _).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as LDS.
    pose proof FC32 as FC3. eapply rw_cells_transport in FC3; [| exact MU | exact WM | cbn; lia].
    zstep. sm_br false. repeat zstep.
    replace (DST + zlen (de_out x) - 4 + 4) with (DST + zlen (de_out x)) by lia.
    destruct (Z.leb_spec (bd_bits (de_bd x)) 64) as [B6|B6].
    - sm_br true. eapply (K3 x m1 jp); [exact ML | exact OK | exact B6 | exact MEM | exact CELLS].
    - sm_br false. zstep. eapply (K5 x m1 jp); [exact ML | exact OK | lia | exact MEM | exact CELLS].
  Qed.

  Lemma sdm_segF_ok : sdm_segF.
  Proof.
    intros f r KD x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B P8 MEM CELLS.
    pose proof OK as (NB & BOK & BZ & OL & OB).
    pose proof MEM as (MU & WM & MI1 & STK1 & SRC1 & (junk & OUT1 & LJ) & DS2 & DS1).
    pose proof BOK as (Oc & Ob & Op & Op8 & Oz & _).
    pose proof CELLS as BD1. unfold bitdz_cellsA in BD1. rewrite BZ in BD1. cbv iota in BD1.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as LDS.
    zstep.
    assert (NBE : bv_swrap 32 (bv_wrap 32 (bd_bits (de_bd x)) ≫ 3) = bd_bits (de_bd x) / 8).
    { replace (bv_wrap 32 (bd_bits (de_bd x))) with (bd_bits (de_bd x)) by (symmetry; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. apply SysStep.swrap32_small. Z.div_mod_to_equations; lia. }
    rewrite NBE. zstep. sm_br false. repeat zstep.
    assert (X1 : (0 <? S0 + bd_ptr (de_bd x)) = true) by (apply Z.ltb_lt; lia).
    assert (X2 : (Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8) <? 1) = false).
    { apply Z.ltb_ge. destruct (Z.eq_dec (Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8)) 0) as [E|E].
      - rewrite Z.lxor_eq_0_iff in E. Z.div_mod_to_equations; lia.
      - assert (0 <= Z.lxor (S0 + bd_ptr (de_bd x)) (bd_bits (de_bd x) / 8)) by (apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia).
        lia. }
    rewrite X1, X2. cbn [Z.b2z]. change (Z.lxor 1 0) with 1.
    sm_br false. repeat zstep. sm_br false. do 2 zstep.
    assert (LA : Z.land (bd_bits (de_bd x)) 7 = bd_bits (de_bd x) mod 8) by (apply (Z.land_ones _ 3); lia).
    assert (PA : S0 + bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 = S0 + (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) by lia.
    rewrite LA, PA in BD1 |- *.
    set (d0 := mkBD (le64v bs (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) (bd_bits (de_bd x) mod 8) (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8) false).
    assert (RL : reload_dstream bs (de_bd x) = Ok (Unfinished, d0)).
    { unfold reload_dstream, d0. replace (64 <? bd_bits (de_bd x)) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr (de_bd x)) with true by (symmetry; apply Z.leb_le; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      rewrite readLE64_ok by (Z.div_mod_to_equations; lia). cbn [bind].
      rewrite LA. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs (de_bd x) Unfinished d0 BY BOK RL) as (OK0 & _).
    rewrite RF_huf_fdw_sm.main_loop_S, RL in ML. cbn [bind] in ML.
    eapply (KD x Unfinished d0 (bd_cont (de_bd x)) _ jp); [exact ML | exact RL | left; reflexivity | exact OK | exact B | exact OK0
      | reflexivity | unfold d0; cbn [bd_bits]; Z.div_mod_to_equations; lia | unfold d0; cbn [bd_ptr]; Z.div_mod_to_equations; lia
      | reflexivity | | ].
    - exact (conj MU (conj WM (conj MI1 (conj STK1 (conj SRC1 (conj (ex_intro _ junk (conj OUT1 LJ)) (conj DS2 DS1))))))).
    - unfold bitdz_cellsA, d0. cbn [bd_cont bd_bits bd_ptr bd_zero]. exact BD1.
  Qed.

  Lemma segh_fast : forall f r, sdm_K3124 f r -> forall x m1 jp (ra a0 a1 a4 s7 s8 s9 s10 t3 t6 : word),
      main_loop bs d dcap false (Datatypes.S f) x = Ok r -> sdm_ok x -> bd_bits (de_bd x) <= 64 -> 8 <= bd_ptr (de_bd x) ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q (SMH 0x98d1c m1 x ra a0 a1 a4 s7 s8 s9 s10 t3 t6).
  Proof.
    intros f r K3 x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B P8 MEM CELLS.
    pose proof OK as (NZ & BOK & _). pose proof BOK as (_ & _ & BP & BP8 & _). pose proof (ablk_lin _ _ HS0) as HS0l.
    zstep. sm_br true. eapply K3; eassumption.
  Qed.

  Lemma segh_ptr0 : forall f r, sdm_X5528 r -> forall x m1 jp (ra a0 a1 a4 s7 s8 s9 s10 t3 t6 : word),
      main_loop bs d dcap false (Datatypes.S f) x = Ok r -> sdm_ok x -> bd_bits (de_bd x) <= 64 -> bd_ptr (de_bd x) = 0 ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q (SMH 0x98d1c m1 x ra a0 a1 a4 s7 s8 s9 s10 t3 t6).
  Proof.
    intros f r KX x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B P0 MEM CELLS.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as LDS.
    pose proof MEM as (MU & WM & MI1 & STK1 & SRC1 & (junk & DA & LJ) & DS2 & DS1).
    pose proof OK as (NZ & BOK & BZ & LO1 & FO).
    pose proof CELLS as C1. unfold bitdz_cellsA in C1. rewrite BZ in C1. cbv iota in C1.
    assert (RR : r = mkDec (de_out x) (de_s1 x) (de_s2 x) (de_bd x)).
    { cbn [main_loop] in ML. unfold reload_dstream in ML.
      replace (64 <? bd_bits (de_bd x)) with false in ML by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr (de_bd x)) with false in ML by (symmetry; apply Z.leb_gt; lia). rewrite P0 in ML.
      destruct (bd_bits (de_bd x) <? 64); cbn in ML; congruence. }
    subst r.
    pose proof FC32 as FC1. eapply rw_cells_transport in FC1; [| exact MU | exact WM | cbn; lia].
    zstep. sm_br false. repeat zstep. sm_br true.
    eapply KX; cbn [de_out de_s1 de_s2 de_bd]; first [eassumption | lia].
  Qed.

  Lemma segh_xchk : forall p n, 0 < p -> 0 <= n -> p <> n -> Z.lxor (Z.b2z (0 <? p)) (Z.b2z (Z.lxor p n <? 1)) = 1.
  Proof.
    intros p n Hp Hn Hne. replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.lxor p n <? 1) with false; [reflexivity|]. symmetry; apply Z.ltb_ge.
    assert (0 <= Z.lxor p n) by (apply Z.lxor_nonneg; lia).
    assert (Z.lxor p n <> 0) by (intro E; exact (Hne (proj1 (Z.lxor_eq_0_iff p n) E))). lia.
  Qed.

  Lemma segh_land : forall a k, k = Z.ones 32 -> 0 <= a < 2^32 -> Z.land a k = a.
  Proof. intros a k -> Ha. rewrite Z.land_ones by lia. apply Z.mod_small; lia. Qed.

  Lemma segh_subw : forall b n k m, k = Z.ones m -> 32 <= m -> 0 <= n -> n * 8 <= b < 2^31 ->
    bv_swrap 32 (b - Z.land (Z.shiftl n 3) k) = b - n * 8.
  Proof.
    intros b n k m -> Hm Hn Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
    assert (2^32 <= 2^m) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. Z.div_mod_to_equations; lia.
  Qed.

  Lemma segh_part_u : forall f r, sdm_K3180 f r -> forall x m1 jp (ra a0 a1 a4 s7 s8 s9 s10 t3 t6 : word),
      main_loop bs d dcap false (Datatypes.S f) x = Ok r -> sdm_ok x -> bd_bits (de_bd x) <= 64 ->
      0 < bd_ptr (de_bd x) < 8 -> bd_bits (de_bd x) / 8 <= bd_ptr (de_bd x) ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q (SMH 0x98d1c m1 x ra a0 a1 a4 s7 s8 s9 s10 t3 t6).
  Proof.
    intros f r K3 x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B PP NB MEM CELLS.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as LDS.
    pose proof MEM as (MU & WM & MI1 & STK1 & SRC1 & (junk & DA & LJ) & DS2 & DS1).
    pose proof OK as (NZ & BOK & BZ & LO1 & FO). pose proof BOK as (BC & BB & BP & BP8 & BP0 & _).
    assert (Z8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [L|L]; [specialize (BP0 L); lia | exact L]).
    pose proof CELLS as C1. unfold bitdz_cellsA in C1. rewrite BZ in C1. cbv iota in C1.
    repeat zstep. sm_br false. repeat zstep. sm_br false. repeat zstep.
    assert (NBe : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bd_bits (de_bd x))) 3) = bd_bits (de_bd x) / 8).
    { rewrite Z.shiftr_div_pow2 by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. Z.div_mod_to_equations; lia. }
    rewrite ?NBe.
    sm_br false. repeat zstep.
    rewrite segh_xchk by lia. sm_br false. repeat zstep.
    sm_br true. repeat zstep.
    rewrite (segh_land (bd_bits (de_bd x) / 8)) by first [reflexivity | lia].
    sm_br false. repeat zstep. rewrite segh_xchk by lia. sm_br false. repeat zstep. sm_br false. do 4 zstep.
    assert (NB0 : 0 <= bd_bits (de_bd x) / 8 <= 8) by (Z.div_mod_to_equations; lia).
    assert (NB8 : bd_bits (de_bd x) / 8 * 8 <= bd_bits (de_bd x)) by (Z.div_mod_to_equations; lia).
    assert (RL : reload_dstream bs (de_bd x) = Ok (Unfinished, mkBD (le64v bs (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8))
              (bd_bits (de_bd x) - bd_bits (de_bd x) / 8 * 8) (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8) false)).
    { unfold reload_dstream.
      replace (64 <? bd_bits (de_bd x)) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr (de_bd x)) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bd_ptr (de_bd x) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      cbv beta iota zeta. rewrite readLE64_ok by lia. cbn [bind]. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs (de_bd x) _ _ BY BOK RL) as (OK0 & _ & _ & Z0 & _).
    destruct (Z0 B) as [BZ0 _].
    rewrite RF_huf_fdw_sm.main_loop_S, RL in ML. cbn [bind] in ML.
    assert (EP : S0 + bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 = S0 + (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8)) by lia.
    rewrite EP in *.
    replace (S0 + (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8) <? S0) with false by (symmetry; apply Z.ltb_ge; lia).
    lazymatch goal with H : rw_cells _ _ (SP1 + 112) _ |- _ => lazymatch type of H with context [bv_swrap 32 (?b - Z.land (Z.shiftl ?n 3) ?k)] =>
      assert (SW : bv_swrap 32 (b - Z.land (Z.shiftl n 3) k) = b - n * 8)
        by first [ (apply (segh_subw _ _ _ 64); [reflexivity | lia..]) | (apply (segh_subw _ _ _ 32); [reflexivity | lia..]) ] end end.
    rewrite SW in *.
    eapply (K3 x Unfinished (mkBD (le64v bs (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8))
              (bd_bits (de_bd x) - bd_bits (de_bd x) / 8 * 8) (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8) false) (bd_cont (de_bd x))); [exact ML | exact RL | left; reflexivity | exact OK | exact B | exact OK0 | exact BZ0
                                                    | cbn [bd_bits]; lia | cbn [bd_ptr]; lia | reflexivity | | ].
    - unfold sdm_mem. do 5 (split; [eassumption|]). split; [eexists; split; eassumption|]. split; eassumption.
    - eassumption.
  Qed.

  Lemma segh_part_e : forall f r, sdm_K3180 f r -> forall x m1 jp (ra a0 a1 a4 s7 s8 s9 s10 t3 t6 : word),
      main_loop bs d dcap false (Datatypes.S f) x = Ok r -> sdm_ok x -> bd_bits (de_bd x) <= 64 ->
      0 < bd_ptr (de_bd x) < 8 -> bd_ptr (de_bd x) < bd_bits (de_bd x) / 8 ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      evtF bsegs RNG Q (SMH 0x98d1c m1 x ra a0 a1 a4 s7 s8 s9 s10 t3 t6).
  Proof.
    intros f r K3 x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B PP NB MEM CELLS.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HS0) as HS0l. pose proof (ablk_lin _ _ HDST) as LDS.
    pose proof MEM as (MU & WM & MI1 & STK1 & SRC1 & (junk & DA & LJ) & DS2 & DS1).
    pose proof OK as (NZ & BOK & BZ & LO1 & FO). pose proof BOK as (BC & BB & BP & BP8 & BP0 & _).
    assert (Z8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [L|L]; [specialize (BP0 L); lia | exact L]).
    pose proof CELLS as C1. unfold bitdz_cellsA in C1. rewrite BZ in C1. cbv iota in C1.
    repeat zstep. sm_br false. repeat zstep. sm_br false. repeat zstep.
    assert (NBe : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bd_bits (de_bd x))) 3) = bd_bits (de_bd x) / 8).
    { rewrite Z.shiftr_div_pow2 by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. Z.div_mod_to_equations; lia. }
    rewrite ?NBe.
    assert (NB0 : 0 <= bd_bits (de_bd x) / 8 <= 8) by (Z.div_mod_to_equations; lia).
    assert (NB8 : bd_bits (de_bd x) / 8 * 8 <= bd_bits (de_bd x)) by (Z.div_mod_to_equations; lia).
    sm_br false. repeat zstep.
    rewrite segh_xchk by lia. sm_br false. repeat zstep.
    sm_br false. repeat zstep.
    assert (EPE : S0 + bd_ptr (de_bd x) - S0 = bd_ptr (de_bd x)) by lia. rewrite EPE.
    rewrite (segh_land (bd_ptr (de_bd x))) by first [reflexivity | lia].
    sm_br false. repeat zstep. rewrite segh_xchk by lia. sm_br false. repeat zstep. sm_br false. do 4 zstep.
    assert (RL : reload_dstream bs (de_bd x) = Ok (EndOfBuffer, (mkBD (le64v bs 0) (bd_bits (de_bd x) - bd_ptr (de_bd x) * 8) 0 false))).
    { unfold reload_dstream.
      replace (64 <? bd_bits (de_bd x)) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr (de_bd x)) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bd_ptr (de_bd x) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      cbv beta iota zeta. replace (bd_ptr (de_bd x) - bd_ptr (de_bd x)) with 0 by lia.
      rewrite readLE64_ok by lia. cbn [bind]. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs (de_bd x) _ _ BY BOK RL) as (OK0 & _ & _ & Z0 & _).
    destruct (Z0 B) as [BZ0 _].
    rewrite RF_huf_fdw_sm.main_loop_S, RL in ML. cbn [bind] in ML.
    replace (S0 + bd_ptr (de_bd x) - bd_bits (de_bd x) / 8 <? S0) with true by (symmetry; apply Z.ltb_lt; lia).
    assert (EP0 : S0 + bd_ptr (de_bd x) - bd_ptr (de_bd x) = S0 + 0) by lia.
    rewrite EP0 in *.
    lazymatch goal with H : rw_cells _ _ (SP1 + 112) _ |- _ => lazymatch type of H with context [bv_swrap 32 (?b - Z.land (Z.shiftl ?n 3) ?k)] =>
      assert (SW : bv_swrap 32 (b - Z.land (Z.shiftl n 3) k) = b - n * 8)
        by first [ (apply (segh_subw _ _ _ 64); [reflexivity | lia..]) | (apply (segh_subw _ _ _ 32); [reflexivity | lia..]) ] end end.
    rewrite SW in *.
    eapply (K3 x EndOfBuffer (mkBD (le64v bs 0) (bd_bits (de_bd x) - bd_ptr (de_bd x) * 8) 0 false) (bd_cont (de_bd x))); [exact ML | exact RL | right; reflexivity | exact OK | exact B | exact OK0 | exact BZ0
                                                    | cbn [bd_bits]; lia | cbn [bd_ptr]; lia | reflexivity | | ].
    - unfold sdm_mem. do 5 (split; [eassumption|]). split; [eexists; split; eassumption|]. split; eassumption.
    - eassumption.
  Qed.

  Lemma sdm_segH_ok : sdm_segH.
  Proof.
    intros f r K3 K31 KX x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B MEM CELLS.
    pose proof OK as (_ & BOK & _). pose proof BOK as (_ & _ & BP & _).
    destruct (Z_le_gt_dec 8 (bd_ptr (de_bd x))) as [P8|P8].
    - exact (segh_fast f r K3 x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B P8 MEM CELLS).
    - destruct (Z.eq_dec (bd_ptr (de_bd x)) 0) as [P0|P0].
      + exact (segh_ptr0 f r KX x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B P0 MEM CELLS).
      + destruct (Z_le_gt_dec (bd_bits (de_bd x) / 8) (bd_ptr (de_bd x))) as [NB|NB].
        * exact (segh_part_u f r K31 x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B ltac:(lia) NB MEM CELLS).
        * exact (segh_part_e f r K31 x m1 jp ra a0 a1 a4 s7 s8 s9 s10 t3 t6 ML OK B ltac:(lia) ltac:(lia) MEM CELLS).
  Qed.

  Lemma segd_aw : appW [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].
  Proof using BOT DST DST3 DT HDST HTL LO S0 S16 SP16 SPV bs d dcap jd lo rc.
    pose proof atop_range as ATR. pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    pose proof LO as LO'. unfold DEC_STACK in LO'. pose proof HDST as HD. unfold ablk in HD.
    unfold appW. unfold KLOW, KHIGH, KLS, AIMG_HI in *.
    destruct HD as [HD|HD];
    repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]); apply Forall_nil.
  Qed.
  Lemma segd_b8 : forall s n, Z_to_bv 8 (s + 256 * n) = Z_to_bv 8 s.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros s n. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    change (2^8) with 256. rewrite Z.mul_comm. apply Z.mod_add. lia.
  Qed.
  Lemma segd_cb2 : forall ce, firstn 2 (skipn (Z.to_nat 2) (fse_cell_bytes ce)) = [Z_to_bv 8 (dc_symbol ce); Z_to_bv 8 (dc_nbBits ce)].
  Proof using. repeat match goal with H : _ |- _ => clear H end. intros ce. unfold fse_cell_bytes, le2. cbn [Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. cbn [skipn firstn app]. reflexivity. Qed.
  Lemma segd_le2 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> [Z_to_bv 8 x; Z_to_bv 8 y] = le2 (Z_to_bv 64 (x + 256 * y)).
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros x y Hx Hy. unfold le2. cbn [Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia.
    f_equal; [|f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?Z.shiftr_div_pow2 by lia; change (2^8) with 256; Z.div_mod_to_equations; lia.
  Qed.
  Lemma segd_zcb : forall l, zlen (concat (map fse_cell_bytes l)) = 4 * zlen l.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    induction l as [|c l IH]; [reflexivity|].
    cbn [map concat]. rewrite length_app, Nat2Z.inj_add, IH.
    assert (L4 : length (fse_cell_bytes c) = 4%nat) by (unfold fse_cell_bytes; rewrite length_app; reflexivity).
    rewrite L4. cbn [length]. lia.
  Qed.
  Lemma segd_le1 : forall b, le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b))) = [Z_to_bv 8 b].
  Proof using. repeat match goal with H : _ |- _ => clear H end. intros b. exact (le1_zxb (Z_to_bv 8 b)). Qed.

  Lemma segd_shr0 : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.shiftr x k = 0.
  Proof using. repeat match goal with H : _ |- _ => clear H end. intros x k Hk Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
  Lemma segd_lor16 : forall a b, 0 <= a -> 0 <= b < 65536 -> Z.lor (a * 65536) b = a * 65536 + b.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros a b Ha Hb. assert (HL : Z.land (a * 65536) b = 0).
    { assert (Hb' : Z.land b (Z.ones 16) = b) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
      rewrite <- Hb'. rewrite (Z.land_comm b), Z.land_assoc, Z.land_ones by lia. change (2^16) with 65536.
      rewrite Z.mod_mul by lia. apply Z.land_0_l. }
    rewrite Z.add_nocarry_lxor by exact HL. symmetry. apply Z.lxor_lor. exact HL.
  Qed.
  Lemma segd_and16 : forall a b, 0 <= a -> 0 <= b < 65536 -> Z.land (a * 65536 + b) 65535 = b.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros a b Ha Hb. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
    rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.
  Lemma segd_shr24 : forall s n, 0 <= s < 256 -> 0 <= n -> Z.shiftr ((s + 256 * n) * 65536) 24 = n.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros s n Hs Hn. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with (65536 * 256).
    rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. Z.div_mod_to_equations. lia.
  Qed.
  Lemma segd_shr16 : forall a b, 0 <= a -> 0 <= b < 65536 -> Z.shiftr (a * 65536 + b) 16 = a.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros a b Ha Hb. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536.
    rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
  Qed.
  Lemma segd_swrap : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros x Hx. unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus. cbn [Z.of_N].
    change (2^32/2) with (2^31). rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma segd_shr64 : forall c k, 0 <= c < 2^64 -> 0 <= k -> (c ≫ k) mod 2^64 = c ≫ k.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros c k H Hk. apply Z.mod_small. rewrite Z.shiftr_div_pow2 by lia.
    assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
    split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ c); [apply Z.div_le_upper_bound; nia | lia].
  Qed.
  Lemma segd_sv0 : forall c x nb ns, 0 <= c < 2^64 -> 0 <= x <= 200 -> 0 <= nb <= 12 ->
    Z.land ((c ≫ Z.land (bv_swrap 32 (0 - x) mod 2^64) 63) mod 2^64) (bv_unsigned (zx32 (Z_to_bv 64 (2^nb - 1)))) + ns
    = ns + Z.land (c ≫ ((bv_swrap 32 (0 - x) mod 2^64) mod 64)) (2^nb - 1).
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros c x nb ns Hc Hx Hn.
    pose proof (Z.pow_pos_nonneg 2 nb ltac:(lia) ltac:(lia)) as P1.
    pose proof (Z.pow_le_mono_r 2 nb 12 ltac:(lia) ltac:(lia)) as P2.
    rewrite RF_huf_tbl_kit.zx32_unsigned_lit by lia.
    rewrite land63_mod. rewrite segd_shr64 by (try apply Z.mod_pos_bound; lia). lia.
  Qed.
  Lemma segd_sv : forall c x nb ns, 0 <= c < 2^64 -> 0 <= x <= 200 -> 0 <= nb <= 12 ->
    Z.land ((c ≫ Z.land ((bv_swrap 32 (0 - bv_swrap 32 x mod 2^64)) mod 2^64) 63) mod 2^64)
           (bv_unsigned (zx32 (Z_to_bv 64 (2^nb - 1)))) + ns
    = ns + Z.land (c ≫ ((bv_swrap 32 (0 - x) mod 2^64) mod 64)) (2^nb - 1).
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros c x nb ns Hc Hx Hn.
    rewrite (segd_swrap x) by lia. rewrite (Z.mod_small x) by lia. apply segd_sv0; lia.
  Qed.
  Ltac segd_osb OUTA LJ :=
    let SOK := fresh "SOK" in
    lazymatch type of OUTA with u8arr _ ?mm ?D (map (Z_to_bv 8) ?o ++ ?j) =>
    pose proof (u8arr_store_ok bsegs mm D _ (zlen o) (wa (D + zlen o)) OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) eq_refl) as SOK;
    zstep;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    end;
    rewrite ?segd_le1, ?le1_lit; rewrite ?segd_b8;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
      let OUT2 := fresh "OUTA" in
      pose proof (RF_huf_fdw_kit.out_sb bsegs mm D o j v OUTA ltac:(lia)) as OUT2;
      let LO2 := fresh "LO" in
      assert (LO2 : zlen (o ++ [v]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
      let LJ2 := fresh "LJ" in
      assert (LJ2 : zlen (List.tl j) = dcap - zlen (o ++ [v])) by (rewrite RF_huf_fdw_sm.zlen_tl by lia; lia);
      clear OUTA LJ; store_done; rename OUT2 into OUTA; rename LJ2 into LJ
    end end.
  Ltac segd_shz1 Z0 X n a :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MUc : munch _ m0 mm |- _ =>
      let ZSn := fresh "ZSn" in let RDB := fresh "RDB" in
      assert (ZSn : zshadow mm X n) by (exact (zshadow_appW _ _ _ _ _ Z0 MUc segd_aw ltac:(lia) ltac:(lia)));
      replace a with (X + (a - X)) by lia;
      pose proof (chkZ mm X n (X + (a - X)) ZSn ltac:(lia) ltac:(lia)) as RDB;
      let N := eval cbv delta [ASHOFF] in ASHOFF in
      change (Z.shiftr (X + (a - X)) 3 + ASHOFF) with (Z.shiftr (X + (a - X)) 3 + N);
      zstep; rewrite ?sxb0; clear RDB ZSn; try replace (X + (a - X)) with a by lia
    end end.
  Ltac segd_shzA r := try fold ASHOFF;
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 (ASHOFF + Z.shiftr ?a 3) => rewrite (Z.add_comm ASHOFF (Z.shiftr a 3))
    | _ => idtac end;
    let v := reg_val r in
    lazymatch v with Z_to_bv 64 (Z.shiftr ?a 3 + ASHOFF) =>
      let X := leftmost a in
      lazymatch X with
      | DT => segd_shz1 ZDT DT (4 + 4 * 2^tl) a
      | DST => segd_shz1 ZDST DST dcap a
      | ABIT_MASK => segd_shz1 ZMK ABIT_MASK 128 a
      end end.
  Ltac segd_nzb := repeat match goal with |- context [Z.b2z (?x <? ?y)] =>
    first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ]; cbn [Z.b2z] end;
    rewrite ?Z.lxor_0_r, ?Z.lxor_0_l.
  Ltac segd_nz := rewrite ?Z.shiftl_mul_pow2 by lia; (try change (2^2) with 4); (try change (2^16) with 65536); segd_nzb;
    repeat match goal with |- context [Z.shiftr ?x 62] => rewrite (segd_shr0 x 62) by lia end;
    rewrite ?segd_lor16 by lia; rewrite ?segd_and16 by lia; rewrite ?segd_shr24 by lia; rewrite ?segd_shr16 by lia.
  Ltac segd_cc := rewrite ?Z.shiftl_mul_pow2 by lia; (try change (2^2) with 4); (try change (2^16) with 65536);
    wk_land64; wk_mods; segd_nzb; wk_cond.
  Ltac segd_brc := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    first [ replace c with false; [cbv iota | symmetry; segd_cc]
          | replace c with true; [cbv iota | symmetry; segd_cc] ] end.
  Ltac segd_wst := lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => segd_brc
    | |- evtF ?segs _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
        lazymatch fw with Some ?w =>
          let dd := eval vm_compute in (decode_any w) in
          lazymatch dd with
          | Some (Load SZ1 _ _ ?rs0 _, _) =>
              let rs := eval vm_compute in (bv_unsigned rs0) in first [segd_shzA rs | zstep]
          | _ => zstep
          end end end; try segd_nz.
  Ltac segd_wgo pcs := repeat (wk_at pcs; segd_wst).

  Ltac segd_cellrd r k s ce NE TBH :=
    repeat match goal with H : ov_read_bytes _ _ _ _ = _ |- _ => clear H end;
    let v := reg_val r in lazymatch v with Z_to_bv 64 ?e =>
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let RD := fresh "RDc" in
      lazymatch k with
      | 0 => pose proof (RF_huf_fdw_kit.cell_rd_ns bsegs mm (DT + 4) (dt_cells d) s ce (Z_to_bv 64 e) TBH NE ltac:(lia)
                           ltac:(unfold wa; f_equal; lia)) as RD
      | 2 => pose proof (RF_huf_fdw_kit.cell_rd_off bsegs mm (DT + 4) (dt_cells d) s ce 2 2 TBH NE ltac:(lia) ltac:(lia) ltac:(lia)) as RD;
             replace (DT + 4 + (4 * s + 2)) with (e + 2) in RD by lia; rewrite segd_cb2 in RD;
             rewrite (segd_le2 (dc_symbol ce) (dc_nbBits ce)) in RD by lia
      end end end.

  Ltac segd_mask nb :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MI' : mem_inv bsegs mm |- _ =>
      let RMK := fresh "RMK" in
      pose proof (maskA_rd mm nb MI' ltac:(lia)) as RMK;
      replace (4 * nb) with (nb * 4) in RMK by lia end end.

  Ltac segd_feq := first [ reflexivity
    | f_equal; cbn [bd_bits bd_cont bd_ptr bd_zero de_out de_s1 de_s2 de_bd]; rewrite ?length_app; cbn [length]; lia
    | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity ].


  Definition segd_D3928 (f : nat) (r : dec) : Prop :=
    forall out o0 o1 o2 o3 s1b s2a s2b d3 d4 m1 jp (ra a0 a1 a3 a4 s7 s8 s9 s10 s11 t3 : word),
      decode_sym d false s2a d3 = Ok (o3, s2b, d4) ->
      main_loop bs d dcap false f (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4) = Ok r ->
      0 < zlen bs -> bitd_ok bs d3 -> bd_zero d3 = false -> bd_bits d3 <= 100 -> zlen out + 4 <= dcap ->
      Forall (fun c => 0 <= c < 256) (out ++ [o0; o1; o2]) ->
      ra = Z_to_bv 64 (bd_bits d3) -> a3 = Z_to_bv 64 (DT + 4 + 4 * s2a) -> s7 = Z_to_bv 64 (2^64 - 1 - ABIT_MASK) ->
      s8 = Z_to_bv 64 1 -> s9 = Z_to_bv 64 (DT + 4) -> s10 = Z_to_bv 64 (DT + 4) -> s11 = Z_to_bv 64 1 ->
      sdm_mem m1 (out ++ [o0; o1; o2]) s1b s2a -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 d3 jp) ->
      evtF bsegs RNG Q
        (SML 0x990b8 m1 ra (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) a0 a1
             (Z_to_bv 64 (S0 + bd_ptr d3)) a3 a4 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
             (Z_to_bv 64 s2a) (Z_to_bv 64 s1b) s7 s8 s9 s10 s11 t3 (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 ASHOFF)
             (Z_to_bv 64 (bd_cont d3))).

  Definition segd_D3728 (f : nat) (r : dec) : Prop :=
    forall out o0 o1 o2 o3 s1a s2a s1b s2b d2 d3 d4 m1 jp (ra a0 a1 a3 a4 s7 s8 s9 s10 s11 t3 : word),
      decode_sym d false s1a d2 = Ok (o2, s1b, d3) -> decode_sym d false s2a d3 = Ok (o3, s2b, d4) ->
      main_loop bs d dcap false f (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4) = Ok r ->
      0 < zlen bs -> bitd_ok bs d2 -> bd_zero d2 = false -> bd_bits d2 <= 88 -> zlen out + 4 <= dcap ->
      Forall (fun c => 0 <= c < 256) (out ++ [o0; o1]) ->
      ra = Z_to_bv 64 (bd_bits d2) -> a3 = Z_to_bv 64 (DT + 4 + 4 * s1a) -> s7 = Z_to_bv 64 (2^64 - 1 - ABIT_MASK) ->
      s8 = Z_to_bv 64 1 -> s9 = Z_to_bv 64 (DT + 4) -> s10 = Z_to_bv 64 (DT + 4) -> s11 = Z_to_bv 64 1 ->
      sdm_mem m1 (out ++ [o0; o1]) s1a s2a -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 d2 jp) ->
      evtF bsegs RNG Q
        (SML 0x98ff0 m1 ra (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) a0 a1
             (Z_to_bv 64 (S0 + bd_ptr d2)) a3 a4 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
             (Z_to_bv 64 s2a) (Z_to_bv 64 s1a) s7 s8 s9 s10 s11 t3 (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 ASHOFF)
             (Z_to_bv 64 (bd_cont d2))).


  Definition segd_D3540 (f : nat) (r : dec) : Prop :=
    forall out o0 o1 o2 o3 s1a s2 s2a s1b s2b d1 d2 d3 d4 m1 jp (ra a0 a1 a3 a4 s7 s8 s9 s10 s11 t3 : word),
      decode_sym d false s2 d1 = Ok (o1, s2a, d2) -> decode_sym d false s1a d2 = Ok (o2, s1b, d3) ->
      decode_sym d false s2a d3 = Ok (o3, s2b, d4) ->
      main_loop bs d dcap false f (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4) = Ok r ->
      0 < zlen bs -> bitd_ok bs d1 -> bd_zero d1 = false -> bd_bits d1 <= 76 -> zlen out + 4 <= dcap ->
      Forall (fun c => 0 <= c < 256) (out ++ [o0]) ->
      ra = Z_to_bv 64 (bd_bits d1) -> a3 = Z_to_bv 64 (DT + 4 + 4 * s2) -> a4 = Z_to_bv 64 0 ->
      s7 = Z_to_bv 64 (2^64 - 1 - ABIT_MASK) -> s8 = Z_to_bv 64 1 -> s9 = Z_to_bv 64 (DT + 4) -> s10 = Z_to_bv 64 (DT + 4) ->
      s11 = Z_to_bv 64 1 ->
      sdm_mem m1 (out ++ [o0]) s1a s2 -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 d1 jp) ->
      evtF bsegs RNG Q
        (SML 0x98f34 m1 ra (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) a0 a1
             (Z_to_bv 64 (S0 + bd_ptr d1)) a3 a4 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
             (Z_to_bv 64 s2) (Z_to_bv 64 s1a) s7 s8 s9 s10 s11 t3 (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 ASHOFF)
             (Z_to_bv 64 (bd_cont d1))).

  Definition segd_D3320 (f : nat) (r : dec) : Prop :=
    forall out o0 o1 o2 o3 s1 s2 s1a s2a s1b s2b d0 d1 d2 d3 d4 m1 jp (ra a0 a1 a3 a4 s7 s8 s9 t3 : word),
      decode_sym d false s1 d0 = Ok (o0, s1a, d1) -> decode_sym d false s2 d1 = Ok (o1, s2a, d2) ->
      decode_sym d false s1a d2 = Ok (o2, s1b, d3) -> decode_sym d false s2a d3 = Ok (o3, s2b, d4) ->
      main_loop bs d dcap false f (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4) = Ok r ->
      0 < zlen bs -> bitd_ok bs d0 -> bd_zero d0 = false -> bd_bits d0 <= 64 -> zlen out + 4 <= dcap ->
      Forall (fun c => 0 <= c < 256) out ->
      sdm_mem m1 out s1 s2 -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 d0 jp) ->
      evtF bsegs RNG Q
        (SML 0x98e58 m1 ra (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) a0 a1
             (Z_to_bv 64 (S0 + bd_ptr d0)) a3 a4 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
             (Z_to_bv 64 s2) (Z_to_bv 64 s1) s7 s8 s9 (Z_to_bv 64 (bd_bits d0)) (Z_to_bv 64 ASHOFF) t3
             (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (bd_cont d0))).

  Lemma segd_K4120E : forall f r, sdm_K4120 f r ->
    forall x m1 jp (ra t0 a0 a1 a3 a4 s4 s6 s7 s8 s9 s10 s11 t3 t4 t6 : word),
      main_loop bs d dcap false f x = Ok r -> sdm_ok x -> bd_bits (de_bd x) <= 2^29 -> 4 <= zlen (de_out x) ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
      t0 = Z_to_bv 64 (DST + zlen (de_out x) - 4) -> t4 = t0 -> a0 = Z_to_bv 64 (2^64 - 5) ->
      a3 = Z_to_bv 64 (bd_bits (de_bd x)) -> s4 = Z_to_bv 64 (de_s2 x) -> s6 = Z_to_bv 64 (de_s1 x) ->
      evtF bsegs RNG Q
        (SML 0x99178 m1 ra t0 (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) a0 a1 (Z_to_bv 64 (S0 + bd_ptr (de_bd x))) a3 a4
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK) s4 s6 s7 s8 s9 s10 s11 t3 t4
             (Z_to_bv 64 ASHOFF) t6).
  Proof.
    intros f r KB x m1 jp ra t0 a0 a1 a3 a4 s4 s6 s7 s8 s9 s10 s11 t3 t4 t6 ML OK B L MM C E0 E4 Ea0 Ea3 Es4 Es6.
    subst t4 t0 a0 a3 s4 s6. exact (KB x m1 jp ra a1 a4 s7 s8 s9 s10 s11 t3 t6 ML OK B L MM C).
  Qed.

  Lemma segd_s4 : forall f r, sdm_K4120 f r -> segd_D3928 f r.
  Proof.
    intros f r KB out o0 o1 o2 o3 s1b s2a s2b d3 d4 m1 jp ra a0 a1 a3 a4 s7 s8 s9 s10 s11 t3
      DS ML ZB OK3 Z3 B3 LOUT FO E1 E3 E7 E8 E9 E10 E11 MM C112.
    subst ra a3 s7 s8 s9 s10 s11.
    destruct MM as (MU & WM & MI1 & STK1 & SRC1 & (junk & OUT1 & LJ) & C80 & C96).
    pose proof OK3 as (O3c & O3b & O3p & O3p8 & O3l & O3z).
    destruct (RF_huf_fdw_sm.dec_inv tl bs d ltac:(lia) HCELLS HCOK s2a d3 o3 s2b d4 DS ltac:(lia))
      as (ce & NE & SR & SY & NB & NSs & NSB & -> & ES & ->).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HDT) as HDTl. pose proof (ablk_lin _ _ HDST) as HDSTl. pose proof (ablk_lin _ _ HS0) as HS0l.
    assert (PT : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    pose proof (Z.pow_pos_nonneg 2 (dc_nbBits ce) ltac:(lia) ltac:(lia)) as P.
    assert (AMK : 4096 <= ABIT_MASK /\ ABIT_MASK + 128 <= 2^40) by (unfold ABIT_MASK; lia).
    pose proof (rng_mask_sh RNG RISH) as RMS.
    assert (AMI : rng RNG ABIT_MASK 128) by (eapply rng_sub; [exact RI | |]; unfold ABIT_MASK; lia).
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FC32 MU WM ltac:(cbn; lia)) as FC1.
    pose proof (bytes_at_transport bsegs _ _ _ _ _ TBB MU ltac:(rewrite segd_zcb, HCELLS; cbn [disjoint_from]; lia)) as TB1.
    unfold bitdz_cellsA in C112. rewrite Z3 in C112. cbv iota in C112.
    pose proof (length_app out [o0; o1; o2]) as LA. cbn [length] in LA.
    clear DJ1 DJ3 DT4 SPA32 FM NS LJD O3z.
    
    segd_wgo [0x99178].
    segd_cellrd 13%Z 2 s2a ce NE TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
    segd_wgo [0x9911c].
    segd_cellrd 13%Z 0 s2a ce NE TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
    segd_mask (dc_nbBits ce).
    segd_wgo [0x99170].
    segd_osb OUT1 LJ.
    segd_wgo [0x99178].
    lazymatch type of C80 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?w); _] =>
      assert (EW : w = s2b) by (rewrite ES; wk_land64;
        replace (bd_bits d3 + dc_nbBits ce) with (dc_nbBits ce + bd_bits d3) by lia; apply segd_sv; lia);
      rewrite EW in C80 |- * end.
    rewrite (segd_swrap (dc_nbBits ce + bd_bits d3)) in C112 |- * by lia.
    rewrite <- app_assoc in OUT1, LJ. cbn [app] in OUT1, LJ.
    eapply (segd_K4120E f r KB (mkDec (out ++ [o0; o1; o2; dc_symbol ce]) s1b s2b
              (mkBD (bd_cont d3) (bd_bits d3 + dc_nbBits ce) (bd_ptr d3) (bd_zero d3))) _ jp).
    - exact ML.
    - unfold sdm_ok. cbn [de_out de_bd bd_zero]. split; [exact ZB|]. split.
      + unfold bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
        split; [exact O3c|]. split; [lia|]. split; [exact O3p|]. split; [exact O3p8|]. split; [exact O3l|].
        intros HZ. rewrite Z3 in HZ. discriminate HZ.
      + split; [exact Z3|]. split; [rewrite length_app; cbn [length]; lia|].
        replace (out ++ [o0; o1; o2; dc_symbol ce]) with ((out ++ [o0; o1; o2]) ++ [dc_symbol ce])
          by (rewrite <- app_assoc; reflexivity).
        apply Forall_app. split; [exact FO|]. constructor; [lia | constructor].
    - cbn [de_bd bd_bits]. lia.
    - cbn [de_out]. rewrite length_app. cbn [length]. lia.
    - unfold sdm_mem. cbn [de_out de_s1 de_s2].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [| split; eassumption].
      exists (List.tl junk). split; [exact OUT1 | exact LJ].
    - unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero]. rewrite Z3.
      replace (bd_bits d3 + dc_nbBits ce) with (dc_nbBits ce + bd_bits d3) by lia. exact C112.
    - f_equal. cbn [de_out]. rewrite length_app. cbn [length]. lia.
    - reflexivity.
    - apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
    - f_equal. cbn [de_bd bd_bits]. lia.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma segd_s3 : forall f r, segd_D3928 f r -> segd_D3728 f r.
  Proof.
    intros f r KD out o0 o1 o2 o3 s1a s2a s1b s2b d2 d3 d4 m1 jp ra a0 a1 a3 a4 s7 s8 s9 s10 s11 t3
      DS DS4 ML ZB OK2 Z2 B2 LOUT FO E1 E3 E7 E8 E9 E10 E11 MM C112.
    subst ra a3 s7 s8 s9 s10 s11.
    destruct MM as (MU & WM & MI1 & STK1 & SRC1 & (junk & OUT1 & LJ) & C80 & C96).
    pose proof OK2 as (O2c & O2b & O2p & O2p8 & O2l & O2z).
    destruct (RF_huf_fdw_sm.dec_inv tl bs d ltac:(lia) HCELLS HCOK s1a d2 o2 s1b d3 DS ltac:(lia))
      as (ce & NE & SR & SY & NB & NSs & NSB & -> & ES & ->).
    destruct (RF_huf_fdw_sm.dec_inv tl bs d ltac:(lia) HCELLS HCOK s2a _ o3 s2b d4 DS4 ltac:(cbn [bd_bits]; lia))
      as (ce4 & _ & SR4 & _).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HDT) as HDTl. pose proof (ablk_lin _ _ HDST) as HDSTl. pose proof (ablk_lin _ _ HS0) as HS0l.
    assert (PT : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    pose proof (Z.pow_pos_nonneg 2 (dc_nbBits ce) ltac:(lia) ltac:(lia)) as P.
    assert (AMK : 4096 <= ABIT_MASK /\ ABIT_MASK + 128 <= 2^40) by (unfold ABIT_MASK; lia).
    pose proof (rng_mask_sh RNG RISH) as RMS.
    assert (AMI : rng RNG ABIT_MASK 128) by (eapply rng_sub; [exact RI | |]; unfold ABIT_MASK; lia).
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FC32 MU WM ltac:(cbn; lia)) as FC1.
    pose proof (bytes_at_transport bsegs _ _ _ _ _ TBB MU ltac:(rewrite segd_zcb, HCELLS; cbn [disjoint_from]; lia)) as TB1.
    unfold bitdz_cellsA in C112. rewrite Z2 in C112. cbv iota in C112.
    pose proof (length_app out [o0; o1]) as LA. cbn [length] in LA.
    clear DJ1 DJ3 DT4 SPA32 FM NS LJD O2z.
    segd_wgo [0x99028].
    segd_cellrd 13%Z 2 s1a ce NE TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
    segd_wgo [0x99058].
    segd_cellrd 13%Z 0 s1a ce NE TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
    segd_mask (dc_nbBits ce).
    segd_wgo [0x990b4].
    segd_osb OUT1 LJ.
    segd_wgo [0x990b8].
    lazymatch type of C96 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?w); _] =>
      assert (EW : w = s1b) by (rewrite ES; wk_land64;
        replace (bd_bits d2 + dc_nbBits ce) with (dc_nbBits ce + bd_bits d2) by lia; apply segd_sv0; lia);
      rewrite EW in C96 |- * end.
    rewrite <- app_assoc in OUT1, LJ. cbn [app] in OUT1, LJ.
    eapply (KD out o0 o1 (dc_symbol ce) o3 s1b s2a s2b (mkBD (bd_cont d2) (bd_bits d2 + dc_nbBits ce) (bd_ptr d2) (bd_zero d2))
              d4 _ jp).
    - exact DS4.
    - exact ML.
    - exact ZB.
    - unfold bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
      split; [exact O2c|]. split; [lia|]. split; [exact O2p|]. split; [exact O2p8|]. split; [exact O2l|].
      intros HZ. rewrite Z2 in HZ. discriminate HZ.
    - exact Z2.
    - cbn [bd_bits]. lia.
    - exact LOUT.
    - replace (out ++ [o0; o1; dc_symbol ce]) with ((out ++ [o0; o1]) ++ [dc_symbol ce]) by (rewrite <- app_assoc; reflexivity).
      apply Forall_app. split; [exact FO|]. constructor; [lia | constructor].
    - segd_feq.
    - segd_feq.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold sdm_mem.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [| split; eassumption].
      exists (List.tl junk). split; [exact OUT1 | exact LJ].
    - unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero]. rewrite Z2.
      replace (bd_bits d2 + dc_nbBits ce) with (dc_nbBits ce + bd_bits d2) by lia. exact C112.
  Qed.

  Lemma segd_s2 : forall f r, segd_D3728 f r -> segd_D3540 f r.
  Proof.
    intros f r KD out o0 o1 o2 o3 s1a s2 s2a s1b s2b d1 d2 d3 d4 m1 jp ra a0 a1 a3 a4 s7 s8 s9 s10 s11 t3
      DS DS3 DS4 ML ZB OK1 Z1 B1 LOUT FO E1 E3 E4 E7 E8 E9 E10 E11 MM C112.
    subst ra a3 a4 s7 s8 s9 s10 s11.
    destruct MM as (MU & WM & MI1 & STK1 & SRC1 & (junk & OUT1 & LJ) & C80 & C96).
    pose proof OK1 as (O1c & O1b & O1p & O1p8 & O1l & O1z).
    destruct (RF_huf_fdw_sm.dec_inv tl bs d ltac:(lia) HCELLS HCOK s2 d1 o1 s2a d2 DS ltac:(lia))
      as (ce & NE & SR & SY & NB & NSs & NSB & -> & ES & ->).
    destruct (RF_huf_fdw_sm.dec_inv tl bs d ltac:(lia) HCELLS HCOK s1a _ o2 s1b d3 DS3 ltac:(cbn [bd_bits]; lia))
      as (ce3 & _ & SR3 & _).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HDT) as HDTl. pose proof (ablk_lin _ _ HDST) as HDSTl. pose proof (ablk_lin _ _ HS0) as HS0l.
    assert (PT : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    pose proof (Z.pow_pos_nonneg 2 (dc_nbBits ce) ltac:(lia) ltac:(lia)) as P.
    assert (AMK : 4096 <= ABIT_MASK /\ ABIT_MASK + 128 <= 2^40) by (unfold ABIT_MASK; lia).
    pose proof (rng_mask_sh RNG RISH) as RMS.
    assert (AMI : rng RNG ABIT_MASK 128) by (eapply rng_sub; [exact RI | |]; unfold ABIT_MASK; lia).
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FC32 MU WM ltac:(cbn; lia)) as FC1.
    pose proof (bytes_at_transport bsegs _ _ _ _ _ TBB MU ltac:(rewrite segd_zcb, HCELLS; cbn [disjoint_from]; lia)) as TB1.
    unfold bitdz_cellsA in C112. rewrite Z1 in C112. cbv iota in C112.
    pose proof (length_app out [o0]) as LA. cbn [length] in LA.
    clear DJ1 DJ3 DT4 SPA32 FM NS LJD O1z.
    segd_wgo [0x98f70].
    segd_cellrd 13%Z 2 s2 ce NE TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
    segd_wgo [0x98f9c].
    segd_cellrd 13%Z 0 s2 ce NE TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
    segd_mask (dc_nbBits ce).
    segd_wgo [0x98fec].
    segd_osb OUT1 LJ.
    segd_wgo [0x98ff0].
    lazymatch type of C80 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?w); _] =>
      assert (EW : w = s2a) by (rewrite ES; wk_land64;
        replace (bd_bits d1 + dc_nbBits ce) with (dc_nbBits ce + bd_bits d1) by lia; apply segd_sv0; lia);
      rewrite EW in C80 |- * end.
    rewrite <- app_assoc in OUT1, LJ. cbn [app] in OUT1, LJ.
    eapply (KD out o0 (dc_symbol ce) o2 o3 s1a s2a s1b s2b (mkBD (bd_cont d1) (bd_bits d1 + dc_nbBits ce) (bd_ptr d1) (bd_zero d1))
              d3 d4 _ jp).
    - exact DS3.
    - exact DS4.
    - exact ML.
    - exact ZB.
    - unfold bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
      split; [exact O1c|]. split; [lia|]. split; [exact O1p|]. split; [exact O1p8|]. split; [exact O1l|].
      intros HZ. rewrite Z1 in HZ. discriminate HZ.
    - exact Z1.
    - cbn [bd_bits]. lia.
    - exact LOUT.
    - replace (out ++ [o0; dc_symbol ce]) with ((out ++ [o0]) ++ [dc_symbol ce]) by (rewrite <- app_assoc; reflexivity).
      apply Forall_app. split; [exact FO|]. constructor; [lia | constructor].
    - segd_feq.
    - segd_feq.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold sdm_mem.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [| split; eassumption].
      exists (List.tl junk). split; [exact OUT1 | exact LJ].
    - unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero]. rewrite Z1.
      replace (bd_bits d1 + dc_nbBits ce) with (dc_nbBits ce + bd_bits d1) by lia. exact C112.
  Qed.

  Lemma segd2_xones : forall a, 0 <= a < 2^64 -> Z.lxor a (2^64 - 1) = 2^64 - 1 - a.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros a Ha.
    assert (E : Z.lxor a (2^64 - 1) = Z.land (Z.lnot a) (Z.ones 64)).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
      change (2^64 - 1) with (Z.ones 64). rewrite Z.testbit_ones by lia.
      rewrite (proj2 (Z.leb_le 0 i) Hi).
      destruct (Z.ltb_spec i 64) as [Hl|Hl].
      - destruct (Z.testbit a i); reflexivity.
      - assert (TA : Z.testbit a i = false).
        { apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
          apply (Z.lt_le_trans _ (2^64)); [lia | apply Z.pow_le_mono_r; lia]. }
        rewrite TA. reflexivity. }
    rewrite E, Z.land_ones, Z.lnot_eq_pred_opp by lia. Z.div_mod_to_equations. lia.
  Qed.

  Lemma segd_s1 : forall f r, segd_D3540 f r -> segd_D3320 f r.
  Proof.
    intros f r KD out o0 o1 o2 o3 s1 s2 s1a s2a s1b s2b d0 d1 d2 d3 d4 m1 jp ra a0 a1 a3 a4 s7 s8 s9 t3
      DS DS2 DS3 DS4 ML ZB OK0 Z0 B0 LOUT FO MM C112.
    destruct MM as (MU & WM & MI1 & STK1 & SRC1 & (junk & OUT1 & LJ) & C80 & C96).
    pose proof OK0 as (O0c & O0b & O0p & O0p8 & O0l & O0z).
    destruct (RF_huf_fdw_sm.dec_inv tl bs d ltac:(lia) HCELLS HCOK s1 d0 o0 s1a d1 DS ltac:(lia))
      as (ce & NE & SR & SY & NB & NSs & NSB & -> & ES & ->).
    destruct (RF_huf_fdw_sm.dec_inv tl bs d ltac:(lia) HCELLS HCOK s2 _ o1 s2a d2 DS2 ltac:(cbn [bd_bits]; lia))
      as (ce2 & _ & SR2 & _).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HDT) as HDTl. pose proof (ablk_lin _ _ HDST) as HDSTl. pose proof (ablk_lin _ _ HS0) as HS0l.
    assert (PT : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    pose proof (Z.pow_pos_nonneg 2 (dc_nbBits ce) ltac:(lia) ltac:(lia)) as P.
    assert (AMK : 4096 <= ABIT_MASK /\ ABIT_MASK + 128 <= 2^40) by (unfold ABIT_MASK; lia).
    pose proof (rng_mask_sh RNG RISH) as RMS.
    assert (AMI : rng RNG ABIT_MASK 128) by (eapply rng_sub; [exact RI | |]; unfold ABIT_MASK; lia).
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FC32 MU WM ltac:(cbn; lia)) as FC1.
    pose proof (bytes_at_transport bsegs _ _ _ _ _ TBB MU ltac:(rewrite segd_zcb, HCELLS; cbn [disjoint_from]; lia)) as TB1.
    unfold bitdz_cellsA in C112. rewrite Z0 in C112. cbv iota in C112.
    clear DJ1 DJ3 DT4 SPA32 FM NS LJD O0z.
    segd_wgo [0x98e64].
    replace (s1 * 4 + (DT + 4)) with (DT + 4 + 4 * s1) by lia.
    segd_wgo [0x98ea4].
    segd_cellrd 13%Z 2 s1 ce NE TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
    segd_wgo [0x98ec0].
    let v := reg_val 23%Z in lazymatch v with Z_to_bv 64 (Z.lxor ABIT_MASK ?k) =>
      let KE := fresh "KE" in assert (KE : k = 2^64 - 1) by reflexivity; rewrite KE;
      replace (Z.lxor ABIT_MASK (2^64 - 1)) with (2^64 - 1 - ABIT_MASK) by (symmetry; apply segd2_xones; lia) end.
    segd_wgo [0x98ed4].
    segd_cellrd 13%Z 0 s1 ce NE TB1. zstep. rewrite RF_huf_tbl_kit.zx16_lit by lia.
    segd_mask (dc_nbBits ce).
    segd_wgo [0x98f30].
    segd_osb OUT1 LJ.
    segd_wgo [0x98f34].
    lazymatch type of C96 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?w); _] =>
      assert (EW : w = s1a) by (rewrite ES; wk_land64;
        replace (bd_bits d0 + dc_nbBits ce) with (dc_nbBits ce + bd_bits d0) by lia; apply segd_sv0; lia);
      rewrite EW in C96 |- * end.
    eapply (KD out (dc_symbol ce) o1 o2 o3 s1a s2 s2a s1b s2b (mkBD (bd_cont d0) (bd_bits d0 + dc_nbBits ce) (bd_ptr d0) (bd_zero d0))
              d2 d3 d4 _ jp).
    - exact DS2.
    - exact DS3.
    - exact DS4.
    - exact ML.
    - exact ZB.
    - unfold bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
      split; [exact O0c|]. split; [lia|]. split; [exact O0p|]. split; [exact O0p8|]. split; [exact O0l|].
      intros HZ. rewrite Z0 in HZ. discriminate HZ.
    - exact Z0.
    - cbn [bd_bits]. lia.
    - exact LOUT.
    - apply Forall_app. split; [exact FO|]. constructor; [lia | constructor].
    - segd_feq.
    - segd_feq.
    - segd_feq.
    - segd_feq.
    - segd_feq.
    - segd_feq.
    - segd_feq.
    - segd_feq.
    - unfold sdm_mem.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [| split; eassumption].
      exists (List.tl junk). split; [exact OUT1 | exact LJ].
    - unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero]. rewrite Z0.
      replace (bd_bits d0 + dc_nbBits ce) with (dc_nbBits ce + bd_bits d0) by lia. exact C112.
  Qed.


  Lemma segd_l7 : forall x, Z.land x 7 = x mod 8.
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
  Lemma segd_lts : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
  Proof using. repeat match goal with H : _ |- _ => clear H end.
    intros x y HX HY. unfold bv_lts, bv_signed, bv_swrap, bv_half_modulus. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change (2 ^ 64 / 2) with (2 ^ 63).
    rewrite (Z.mod_small x), (Z.mod_small y), (Z.mod_small (x + 2^63)), (Z.mod_small (y + 2^63)) by lia.
    replace (x + 2^63 - 2^63) with x by lia. replace (y + 2^63 - 2^63) with y by lia. reflexivity.
  Qed.
  Ltac segd_br b := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with b; [cbv iota | symmetry; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      first [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.eqb_eq | apply Z.eqb_neq
            | apply Bool.negb_true_iff, Z.ltb_ge | apply Bool.negb_false_iff, Z.ltb_lt
            | apply Bool.negb_true_iff, Z.eqb_neq | apply Bool.negb_false_iff, Z.eqb_eq]; Z.div_mod_to_equations; lia] end.

  Definition segd_KH (pc : Z) (f : nat) (r : dec) : Prop :=
    forall x st d0 c m1 jp (ra a0 a3 a4 s7 s8 s9 t3 t6 : word),
      RF_huf_fdw_sm.ml_body dcap bs d f x st d0 = Ok r -> reload_dstream bs (de_bd x) = Ok (st, d0) ->
      (st = Unfinished \/ st = EndOfBuffer) -> sdm_ok x -> bd_bits (de_bd x) <= 64 ->
      bitd_ok bs d0 -> bd_zero d0 = false -> bd_bits d0 <= 64 -> bd_ptr d0 + 8 <= zlen bs -> bd_cont d0 = le64v bs (bd_ptr d0) ->
      sdm_mem m1 (de_out x) (de_s1 x) (de_s2 x) ->
      rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (mkBD c (bd_bits d0) (bd_ptr d0) false) jp) ->
      evtF bsegs RNG Q
        (SML pc m1 ra (Z_to_bv 64 (DST + zlen (de_out x))) (Z_to_bv 64 64) (Z_to_bv 64 (S0 + 8)) a0
             (Z_to_bv 64 (Z.b2z (dstatus_eqb st Unfinished))) (Z_to_bv 64 (S0 + bd_ptr d0)) a3 a4
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
             (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) s7 s8 s9 (Z_to_bv 64 (bd_bits d0)) (Z_to_bv 64 ASHOFF) t3
             (Z_to_bv 64 (DST + zlen (de_out x))) (Z_to_bv 64 ASHOFF) t6).

  Lemma segd_h1 : forall f r, segd_KH 0x98ddc f r -> sdm_K3180 f r.
  Proof.
    intros f r KH x st d0 c m1 jp ra a0 a3 a4 s7 s8 s9 t3 t6 MB RL ST OK Bx OK0 Z0 B0 P8 CT MM C112.
    pose proof MM as (MU & WM & MI1 & STK1 & SRC1 & _ & C80 & C96).
    pose proof OK as (ZB & _). pose proof OK0 as (O0c & O0b & O0p & _).
    pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof (unpoisoned_appW _ _ _ _ _ USRC MU segd_aw ltac:(lia) ltac:(lia)) as UM.
    destruct (AF_fse_rd_base.chkB m1 S0 (S0 + zlen bs) (S0 + bd_ptr d0) UM ltac:(lia) ltac:(lia)) as (sb & RB & SB & SBR).
    zstep. zstep.
    try (let v := eval unfold ASHOFF in ASHOFF in
         change (Z_to_bv 64 ((S0 + bd_ptr d0) ≫ 3 + ASHOFF)) with (Z_to_bv 64 ((S0 + bd_ptr d0) ≫ 3 + v))).
    zstep. zstep. rewrite !sxb_sval. destruct SB as [SB | SB].
    - segd_br false. eapply KH; eassumption.
    - segd_br true. zstep. zstep. rewrite segd_l7, segd_lts by (pose proof (Z.mod_pos_bound (S0 + bd_ptr d0) 8); lia).
      segd_br true. eapply KH; eassumption.
  Qed.

  Lemma segd_h2 : forall f r, segd_KH 0x98df0 f r -> segd_KH 0x98ddc f r.
  Proof.
    intros f r KH x st d0 c m1 jp ra a0 a3 a4 s7 s8 s9 t3 t6 MB RL ST OK Bx OK0 Z0 B0 P8 CT MM C112.
    pose proof MM as (MU & WM & MI1 & STK1 & SRC1 & _ & C80 & C96).
    pose proof OK as (ZB & _). pose proof OK0 as (O0c & O0b & O0p & _).
    pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof (unpoisoned_appW _ _ _ _ _ USRC MU segd_aw ltac:(lia) ltac:(lia)) as UM.
    destruct (AF_fse_rd_base.chkB m1 S0 (S0 + zlen bs) (S0 + bd_ptr d0 + 7) UM ltac:(lia) ltac:(lia)) as (sb & RB & SB & SBR).
    zstep. zstep. zstep.
    try (let v := eval unfold ASHOFF in ASHOFF in
         change (Z_to_bv 64 ((S0 + bd_ptr d0 + 7) ≫ 3 + ASHOFF)) with (Z_to_bv 64 ((S0 + bd_ptr d0 + 7) ≫ 3 + v))).
    zstep. zstep. rewrite !sxb_sval. destruct SB as [SB | SB].
    - segd_br false. eapply KH; eassumption.
    - segd_br true. zstep. zstep. rewrite segd_l7, segd_lts by (pose proof (Z.mod_pos_bound (S0 + bd_ptr d0 + 7) 8); lia).
      segd_br true. eapply KH; eassumption.
  Qed.


  Ltac segd_ldb p k :=
    let RX := fresh "RX" in
    lazymatch goal with SRC' : bytes_at bsegs ?mg S0 (map (Z_to_bv 8) bs) |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      pose proof (src_rd bsegs mg S0 bs (p + k) SRC' ltac:(lia)) as RX end;
    rewrite ?Z.add_assoc, ?Z.add_0_r in RX;
    zstep; cbv beta; clear RX.

  Lemma segd_h3 : forall f r, segd_D3320 f r -> sdm_X5528 r -> segd_KH 0x98df0 f r.
  Proof.
    intros f r KD KX x st d0 c m1 jp ra a0 a3 a4 s7 s8 s9 t3 t6 MB RL ST OK Bx OK0 Z0 B0 P8 CT MM C112.
    destruct MM as (MU & WM & MI1 & STK1 & SRC1 & (junk & OUT1 & LJ) & C80 & C96).
    pose proof OK as (ZB & OKx & Zx & LOUT & FO).
    pose proof OK0 as (O0c & O0b & O0p & O0p8 & O0l & O0z).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HDST) as HDSTl. pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FC32 MU WM ltac:(cbn; lia)) as FC1.
    segd_ldb (bd_ptr d0) 1. segd_ldb (bd_ptr d0) 2. segd_ldb (bd_ptr d0) 3. segd_ldb (bd_ptr d0) 0.
    zstep. zstep. zstep. zstep. segd_ldb (bd_ptr d0) 4. segd_ldb (bd_ptr d0) 5. zstep.
    segd_ldb (bd_ptr d0) 6. segd_ldb (bd_ptr d0) 7.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite le64_lbu_land by (apply byte_Znth; [exact BY | lia]). fold (le64v bs (bd_ptr d0)). rewrite <- CT.
    pose proof (rw_cells_store_ok_at bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (mkBD c (bd_bits d0) (bd_ptr d0) false) jp) 0
      (C8 (Z_to_bv 64 c)) 8 (Z_to_bv 64 (SP1 + 112)) C112 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
    pose proof (rw_cells_write bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (mkBD c (bd_bits d0) (bd_ptr d0) false) jp) 0
      (C8 (Z_to_bv 64 c)) (C8 (Z_to_bv 64 (bd_cont d0))) C112 eq_refl eq_refl I) as C112b.
    replace (SP1 + 112 + Z.of_nat 0) with (SP1 + 112) in C112b by lia. cbn [cbytes cell_upd Nat.eqb] in C112b.
    change (rw_cells bsegs (write_to_mem m1 (wa (SP1 + 112)) (le8 (Z_to_bv 64 (bd_cont d0)))) (SP1 + 112)
      (bitdz_cellsA S0 (mkBD (bd_cont d0) (bd_bits d0) (bd_ptr d0) false) jp)) in C112b.
    unfold bitdz_cellsA in C112b. cbn [bd_cont bd_bits bd_ptr bd_zero] in C112b.
    zstep. store_done.
    let v := reg_val 11%Z in
    assert (A1 : v = Z_to_bv 64 (Z.b2z (dstatus_eqb st Unfinished && (zlen (de_out x) <? dcap - 3)))).
    { f_equal. destruct (dstatus_eqb st Unfinished); destruct (Z.ltb_spec (DST + zlen (de_out x)) (DST + dcap - 3));
        destruct (Z.ltb_spec (zlen (de_out x)) (dcap - 3)); try lia; reflexivity. }
    rewrite A1. clear A1. zstep.
    destruct (dstatus_eqb st Unfinished && (zlen (de_out x) <? dcap - 3)) eqn:EX.
    - cbn [Z.b2z]. segd_br false. apply andb_true_iff in EX as (EX1 & EX2). apply Z.ltb_lt in EX2.
      unfold RF_huf_fdw_sm.ml_body in MB. unfold FseNCount.Zlength in MB. rewrite EX1 in MB.
      replace (zlen (de_out x) <? dcap - 3) with true in MB by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in MB.
      destruct (decode_sym d false (de_s1 x) d0) as [[[o0 s1a] e1] | | |] eqn:D1; cbn [bind] in MB; try discriminate MB.
      destruct (decode_sym d false (de_s2 x) e1) as [[[o1 s2a] e2] | | |] eqn:D2; cbn [bind] in MB; try discriminate MB.
      destruct (decode_sym d false s1a e2) as [[[o2 s1b] e3] | | |] eqn:D3; cbn [bind] in MB; try discriminate MB.
      destruct (decode_sym d false s2a e3) as [[[o3 s2b] e4] | | |] eqn:D4; cbn [bind] in MB; try discriminate MB.
      eapply (KD (de_out x) o0 o1 o2 o3 (de_s1 x) (de_s2 x) s1a s2a s1b s2b d0 e1 e2 e3 e4 _ jp).
      + exact D1.
      + exact D2.
      + exact D3.
      + exact D4.
      + exact MB.
      + exact ZB.
      + exact OK0.
      + exact Z0.
      + exact B0.
      + lia.
      + exact FO.
      + unfold sdm_mem.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [| split; eassumption].
        exists junk. split; eassumption.
      + unfold bitdz_cellsA. rewrite Z0. exact C112b.
    - cbn [Z.b2z]. segd_br true.
      unfold RF_huf_fdw_sm.ml_body in MB. unfold FseNCount.Zlength in MB. rewrite EX in MB.
      injection MB as MB. subst r.
      eapply KX; cbn [de_out de_s1 de_s2 de_bd].
      + exact ZB.
      + exact OK0.
      + lia.
      + exact LOUT.
      + exact FO.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + exact OUT1.
      + exact LJ.
      + eassumption.
      + eassumption.
      + eassumption.
      + unfold bitdz_cellsA. rewrite Z0. exact C112b.
  Qed.

  Lemma segd_head : forall f r, segd_D3320 f r -> sdm_X5528 r -> sdm_K3180 f r.
  Proof. intros f r KD KX. exact (segd_h1 f r (segd_h2 f r (segd_h3 f r KD KX))). Qed.


  Lemma sdm_segD_ok : sdm_segD.
  Proof.
    intros f r KB KX.
    exact (segd_head f r (segd_s1 f r (segd_s2 f r (segd_s3 f r (segd_s4 f r KB)))) KX).
  Qed.

  Lemma sdm_proofA : sdm_stmtA.
  Proof. exact (sdm_stmt_of sdm_segE_ok (sdm_loop_of sdm_segH_ok sdm_segF_ok sdm_segD_ok sdm_segB_ok sdm_segX_ok)). Qed.

End SDM.
End CANSEC1.
