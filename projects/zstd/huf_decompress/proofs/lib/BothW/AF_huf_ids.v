(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ids () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2Efse_init_dstate_postAC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit<zshadow_appWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_bdt_kit4chkZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib3Lib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib3MemAzext_extract_byteC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_bdt_kit7acc_shZC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF=rng_acc_litZ'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2<bitdz_cellsAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4SpecAHufPure_FseDecomp4bitD00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2?AFSE_INIT_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit4zxb0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib6Common:HufWalkKit5le64vC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AF_huf_ids7ids_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit9byte_ZnthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit=le64_lbu_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib3Lib7ZBridge5zr_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4SpecAHufPure_FseDecomp4bitD01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit6src_rdC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03c59OSSVerify5KrLib5BothW:AF_huf_ids7IDS_PREC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AF_huf_ids6ST_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit?unpoisoned_appWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_fse_rd_base4chkBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4svalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3sxbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemAsext_extract_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4LibA6Shadow9land7_modC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib4LibA6ShadowBsigned_lit_small64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib5BothW:AF_huf_ids6ids_ldC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib4LibA6Shadow8sxb_svalC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AF_huf_ids7ids_c2FC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03c59OSSVerify5KrLib5BothW:AF_huf_ids7ids_c2PC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5Plain@RF_huf_tbl_iface7bitd_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9FseNCount3res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp9read_bitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp>reload_dstreamC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8artcellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW@AF_huf_tbl_iface7zshadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5nshadC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp7bd_contC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp7bd_bitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp6bd_ptrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula01K59OSSVerify5KrLib4Spec9FseNCount3res03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp9skip_bitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp7bd_zeroC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC56Stdlib6ZArith6BinInt1Z<pos_div_euclC57Corelib7BinNums6PosDef3Pos4iterC57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC47Corelib4Init5Logic7f_equalK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib4LibA6Shadow9nshad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit;rng_mask_shC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5BothW9Stdio_kit4appWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnK4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib3Lib3Mem4zx16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@zext_extract_le2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C59OSSVerify5KrLib3Lib8PropExec6v_addwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec6w_addwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit8maskA_rdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@zext_extract_le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib3Lib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6w_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_srlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_srlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_andC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount3res01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas6u32_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit:land63_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib4SpecAHufPure_FseDecomp8readLE64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit;readLE64_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0<C59OSSVerify5KrLib3Lib8PropExec7v_srliwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7w_srliwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib5BothW:AF_huf_ids7ids_c1FC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib5BothW>AF_huf_fdw_kit:land64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:STRW_merge=swrap32_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkKit<wrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppc59OSSVerify5KrLib5BothW:AF_huf_ids7ids_c1PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit:land32_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge?zb_shl_shr_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SFModel<mod64_land63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit:shr_land64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit>neg_shift_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RF_huf_tbl_kitAzx32_unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure:sx32_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RF_huf_tbl_kit8zx16_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2Efse_init_dstate_stmtAC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega=RingMicromega5Psatz05C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuI59OSSVerify5KrLib4SpecAHufPure_FseDecomp7dstatus00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto4kind02C59OSSVerify5KrLib4LibA6Shadow4KLOWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4SpecAHufPure_FseDecomp7dstatus04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4SpecAHufPure_FseDecomp7dstatus01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4SpecAHufPure_FseDecomp7dstatus02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_bdt_kit4sxb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface29ABIT_MASKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4div2C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2;AZEROFILLEDC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5aluop02K59OSSVerify5KrLib4SpecAHufPure_FseDecomp7dstatus03C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K47Corelib4Init9Datatypes:comparison01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Section IDS.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : amem) (DS BD DT S : Z) (bs : list Z) (lo : Z).
  Hypothesis SPD : bv_unsigned sp <= DS.
  Hypothesis DS8 : DS mod 8 = 0.
  Hypothesis DSB : DS + 16 <= BD.
  Hypothesis BD8 : BD mod 8 = 0.
  Hypothesis BDH : BD + 48 <= 2^47.
  Hypothesis BDT : ablk DT (DT + 4).
  Hypothesis DT4 : DT mod 4 = 0.
  Hypothesis BS : ablk S (S + zlen bs).
  Hypothesis S8 : S + 8 <= 2^47.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= bv_unsigned sp + -16.
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis ZDS : zshadow m DS 16.
  Hypothesis ZBD : zshadow m BD 40.
  Hypothesis ZDT : zshadow m DT 4.
  Hypothesis ZMK : zshadow m ABIT_MASK 128.
  Hypothesis US : unpoisoned m S (S + zlen bs).
  Hypothesis RDS : rng RNG DS 16.
  Hypothesis RDSs : rng RNG (shad DS) (nshad (16 + DS mod 8)).
  Hypothesis RBD : rng RNG BD 40.
  Hypothesis RBDs : rng RNG (shad BD) (nshad (40 + BD mod 8)).
  Hypothesis RDT : rng RNG DT 4.
  Hypothesis RDTs : rng RNG (shad DT) (nshad (4 + DT mod 8)).
  Hypothesis RS : rng RNG S (zlen bs).
  Hypothesis RSs : rng RNG (shad S) (nshad (zlen bs + S mod 8)).
  Hypothesis RSTK : rng RNG (bv_unsigned sp - 16) 16.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis AW : appW [(bv_unsigned sp + -16, bv_unsigned sp); (DS, DS + 16); (BD, BD + 40)].
  Hypothesis SA : S + zlen bs <= ATOP.
  Hypothesis SL : 1 <= S.

  Notation WI := [(bv_unsigned sp + -16, bv_unsigned sp); (DS, DS + 16); (BD, BD + 40)].

  Notation POSTI v d2 :=
    (fse_init_dstate_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS BD DT S v d2 lo m).

  Definition IST (pc : Z) (m1 : amem) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None m1 (seg_rom bsegs).

  Definition ST228 (m1 : amem) (b1 : Z) (x15 x29 x30 x31 : word) : machine_state :=
    IST 0x9a660 m1 (Z_to_bv 64 ((BD + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 b1) (Z_to_bv 64 65) (Z_to_bv 64 DS) (Z_to_bv 64 BD)
        (Z_to_bv 64 DT) (Z_to_bv 64 (BD + 8)) (Z_to_bv 64 (BD + 16)) x15 (Z_to_bv 64 2147450880) (Z_to_bv 64 (BD ≫ 3 + 2147450880))
        (Z_to_bv 64 ((BD + 16) ≫ 3 + 2147450880)) x29 x30 x31.

  Ltac zck r ZS0 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch ?W m mm |- _ =>
    let v := reg_val r in
    lazymatch v with Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880) =>
      let RDB := fresh "RDB" in
      pose proof (chkZ mm _ _ a (zshadow_appW W m mm _ _ ZS0 MU AW ltac:(unfold ABIT_MASK; lia) ltac:(unfold ABIT_MASK; lia))
                    ltac:(unfold ABIT_MASK in *; lia) ltac:(unfold ABIT_MASK in *; lia)) as RDB;
      zstep; rewrite ?sxb0, ?zxb0; clear RDB
    end end end.

  Ltac bcz := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?Z.shiftl_mul_pow2 by lia; try change (2 ^ 2) with 4;
    repeat match goal with |- context [?a mod 2 ^ 64] => rewrite (Z.mod_small a (2 ^ 64)) by (unfold ABIT_MASK in *; lia) end;
    solve_cond_rec.
  Ltac bF := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false; [cbv iota | symmetry; bcz] end.
  Ltac bT := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota | symmetry; bcz] end.
  Ltac curm := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => mm end.
  Ltac fixmask tl :=
    match goal with |- context [Z.land ?E ?M] =>
      lazymatch E with context [tl] => idtac end;
      let H := fresh "FM" in assert (H : Z.land E M = ABIT_MASK + 4 * tl);
      [ change M with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.shiftl_mul_pow2 by lia;
        change (2 ^ 2) with 4; unfold ABIT_MASK; rewrite Z.mod_small by lia; lia
      | rewrite H; clear H ] end.
  Ltac fixreg r tl :=
    setreg r (Z_to_bv 64 (ABIT_MASK + 4 * tl))
      ltac:(f_equal; unfold ABIT_MASK; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; lia).
  Ltac wkto o := repeat (lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        let dd := eval vm_compute in (p - AFSE_INIT_DSTATE) in tryif constr_eq dd o then fail else idtac
    | _ => idtac end; first [ zstep | bF ]).
  Ltac zauto := first [ zck 28%Z ZBD | zck 7%Z ZBD | zck 5%Z ZBD | zck 29%Z ZBD | zck 13%Z ZBD | zck 14%Z ZBD | zck 17%Z ZBD
                       | zck 11%Z ZDS | zck 14%Z ZDS | zck 13%Z ZDT | zck 7%Z ZMK ].
  Ltac goto o := repeat (lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        let dd := eval vm_compute in (p - AFSE_INIT_DSTATE) in tryif constr_eq dd o then fail else idtac
    | _ => idtac end; first [ zstep | bF | bT | zauto ]).
  Ltac nb1 b1 :=
    let WB := fresh "WB" in let SB := fresh "SB" in
    assert (WB : bv_wrap 32 b1 = b1) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia);
    assert (SB : bv_swrap 32 (b1 ≫ 3) = b1 / 8)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; apply swrap32_small; Z.div_mod_to_equations; lia);
    rewrite ?WB, ?SB; clear WB SB.
  Ltac zxd :=
    repeat match goal with
    | |- context [Z.lxor ?x ?y <? 1] =>
        replace (Z.lxor x y <? 1) with false by
          (symmetry; apply Z.ltb_ge;
           assert (0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); split; intro; Z.div_mod_to_equations; lia);
           assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; Z.div_mod_to_equations; lia); lia)
    | |- context [0 <? ?a] => replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia)
    end; cbn [Z.b2z Z.lxor].
  Ltac l32 := rewrite ?Z.add_simpl_l, ?land32_mod;
    repeat match goal with |- context [?a mod ?k] => rewrite (Z.mod_small a k) by (Z.div_mod_to_equations; lia) end.
  Ltac fixbits H T :=
    lazymatch type of H with context [bv_swrap 32 ?E] =>
      replace (bv_swrap 32 E) with T in H
        by (symmetry; rewrite Z.shiftl_mul_pow2 by (Z.div_mod_to_equations; lia); change (2 ^ 3) with 8; first [ rewrite land64_mod | rewrite land32_mod ];
            rewrite Z.mod_small by (Z.div_mod_to_equations; lia); apply swrap32_small; Z.div_mod_to_equations; lia) end.
  Ltac wk := repeat first [ zstep | bF ].

  (* [comment removed for export] *)
  Lemma ids_fin : forall m1 v d2 jp jds' junk8 (x5 x6 x7 x11 x13 x14 x15 x17 x28 x29 x30 x31 : word),
    munch [(bv_unsigned sp + -16, bv_unsigned sp); (DS, DS + 16); (BD, BD + 40)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk8; C8 ra] -> stk bsegs m1 lo (bv_unsigned sp + -16) ->
    rw_cells bsegs m1 DS [C8 (Z_to_bv 64 v); CB 8 jds'] ->
    rw_cells bsegs m1 BD (bitdz_cellsA S d2 jp) ->
    evtF bsegs RNG (POSTI v d2)
      (IST 0x9a818 m1 x5 x6 x7 (Z_to_bv 64 DS) x11 (Z_to_bv 64 DT) x13 x14 x15 (Z_to_bv 64 2147450880) x17 x28 x29 x30 x31).
Proof.
  intros m1 v d2 jp jds' junk8 x5 x6 x7 x11 x13 x14 x15 x17 x28 x29 x30 x31 MU WMo MI FR STK HDS HBD.
  unfold IST.
  pose proof BDT as BDT'; unfold ablk, AIMG_HI, KLS in BDT'.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  zstep. zstep. zstep. zck 11%Z ZDS. zstep. bF. zstep. zstep. zstep. zstep. zstep.
  release_frame FR STK (bv_unsigned sp).
  apply evtF_done. unfold fse_init_dstate_postA.
  do 17 eexists. split; [reflexivity|].
  unfold AFSE_INIT_STACK. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia.
  split; [exact MU|]. split; [exact WMo|]. split; [assumption|]. split; [exact STK|]. split; [exact HDS|exact HBD].
Qed.


  Lemma ids_ovf : forall m1 v cont b1 P ptr jp jds' junk8 (x15 x29 x30 x31 : word),
    64 < b1 < 2^31 ->
    munch WI m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk8; C8 ra] -> stk bsegs m1 lo (bv_unsigned sp + -16) ->
    rw_cells bsegs m1 DS [C8 (Z_to_bv 64 v); CB 8 jds'] ->
    rw_cells bsegs m1 BD [C8 (Z_to_bv 64 cont); C4 (Z_to_bv 64 b1); CB 4 jp; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 S);
                          C8 (Z_to_bv 64 (S + 8))] ->
    evtF bsegs RNG (POSTI v (mkBD cont b1 ptr true)) (ST228 m1 b1 x15 x29 x30 x31).
Proof.
  intros m1 v cont b1 P ptr jp jds' junk8 x15 x29 x30 x31 B1 MU WMo MI FR STK HDS HBD.
  unfold ST228, IST.
  pose proof BDT as BDT'; unfold ablk, AIMG_HI, KLS in BDT'.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  goto 668.
  apply (ids_fin _ v _ jp jds' junk8); assumption.
Qed.


  Lemma ids_endc : forall m1 v cont b1 jp jds' junk8 (x15 x29 x30 x31 : word),
    0 <= b1 <= 64 ->
    munch WI m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk8; C8 ra] -> stk bsegs m1 lo (bv_unsigned sp + -16) ->
    rw_cells bsegs m1 DS [C8 (Z_to_bv 64 v); CB 8 jds'] ->
    rw_cells bsegs m1 BD [C8 (Z_to_bv 64 cont); C4 (Z_to_bv 64 b1); CB 4 jp; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 S);
                          C8 (Z_to_bv 64 (S + 8))] ->
    evtF bsegs RNG (POSTI v (mkBD cont b1 0 false)) (ST228 m1 b1 x15 x29 x30 x31).
Proof.
  intros m1 v cont b1 jp jds' junk8 x15 x29 x30 x31 B1 MU WMo MI FR STK HDS HBD.
  unfold ST228, IST.
  pose proof BDT as BDT'; unfold ablk, AIMG_HI, KLS in BDT'.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  goto 668. apply (ids_fin _ v _ jp jds' junk8); try assumption.
  unfold bitdz_cellsA; cbn [bd_cont bd_bits bd_zero bd_ptr]. rewrite Z.add_0_r. assumption.
Qed.


  (* [comment removed for export] *)
  Lemma ids_ld : forall m1 v P p bits jp jds' junk8 (cont0 x5 x6 x7 x13 x14 x17 x28 x29 x30 x31 : word),
    P = S + p -> 0 <= p -> p + 8 <= zlen bs ->
    munch WI m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk8; C8 ra] -> stk bsegs m1 lo (bv_unsigned sp + -16) ->
    rw_cells bsegs m1 DS [C8 (Z_to_bv 64 v); CB 8 jds'] ->
    rw_cells bsegs m1 BD [C8 cont0; C4 (Z_to_bv 64 bits); CB 4 jp; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 S);
                          C8 (Z_to_bv 64 (S + 8))] ->
    bytes_at bsegs m1 S (map (Z_to_bv 8) bs) ->
    evtF bsegs RNG (POSTI v (mkBD (le64v bs p) bits p false))
      (IST 0x9a7b4 m1 x5 x6 x7 (Z_to_bv 64 DS) (Z_to_bv 64 BD) (Z_to_bv 64 DT) x13 x14 (Z_to_bv 64 P)
           (Z_to_bv 64 2147450880) x17 x28 x29 x30 x31).
Proof.
  intros m1 v P p bits jp jds' junk8 cont0 x5 x6 x7 x13 x14 x17 x28 x29 x30 x31 EP P0 P8 MU WMo MI FR STK HDS HBD SRC. subst P.
  unfold IST.
  pose proof BDT as BDT'; unfold ablk, AIMG_HI, KLS in BDT'.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  pose proof (src_rd bsegs m1 S bs (p + 0) SRC ltac:(lia)) as RX0;
  pose proof (src_rd bsegs m1 S bs (p + 1) SRC ltac:(lia)) as RX1;
  pose proof (src_rd bsegs m1 S bs (p + 2) SRC ltac:(lia)) as RX2;
  pose proof (src_rd bsegs m1 S bs (p + 3) SRC ltac:(lia)) as RX3;
  pose proof (src_rd bsegs m1 S bs (p + 4) SRC ltac:(lia)) as RX4;
  pose proof (src_rd bsegs m1 S bs (p + 5) SRC ltac:(lia)) as RX5;
  pose proof (src_rd bsegs m1 S bs (p + 6) SRC ltac:(lia)) as RX6;
  pose proof (src_rd bsegs m1 S bs (p + 7) SRC ltac:(lia)) as RX7.
  rewrite ?Z.add_assoc, ?Z.add_0_r in RX0, RX1, RX2, RX3, RX4, RX5, RX6, RX7.
  goto 668.
  apply (ids_fin _ v _ jp jds' junk8); try assumption.
  lazymatch goal with H : rw_cells bsegs ?mm BD ?cs |- rw_cells bsegs ?mm BD ?cs' =>
    replace cs' with cs; [exact H|] end.
  unfold bitdz_cellsA; cbn [bd_cont bd_bits bd_zero bd_ptr].
  lazymatch goal with |- [?a0; ?a1; ?a2; ?a3; ?a4; ?a5] = [?b0; ?b1; ?b2; ?b3; ?b4; ?b5] =>
    replace a0 with b0; [reflexivity|] end.
  do 2 f_equal. unfold le64v.
  pose proof (fun i => byte_Znth bs i BY) as BZ.
  rewrite le64_lbu_land by (apply BZ; lia).
  rewrite ?Z.add_0_r. ring.
Qed.


  (* [comment removed for export] *)
  Lemma ids_fast : forall m1 v cont b1 ptr jp jds' junk8 (x15 x29 x30 x31 : word),
    0 <= b1 <= 64 -> 8 <= ptr -> ptr + 8 <= zlen bs ->
    munch WI m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk8; C8 ra] -> stk bsegs m1 lo (bv_unsigned sp + -16) ->
    rw_cells bsegs m1 DS [C8 (Z_to_bv 64 v); CB 8 jds'] ->
    rw_cells bsegs m1 BD [C8 (Z_to_bv 64 cont); C4 (Z_to_bv 64 b1); CB 4 jp; C8 (Z_to_bv 64 (S + ptr)); C8 (Z_to_bv 64 S);
                          C8 (Z_to_bv 64 (S + 8))] ->
    bytes_at bsegs m1 S (map (Z_to_bv 8) bs) ->
    evtF bsegs RNG (POSTI v (mkBD (le64v bs (ptr - b1 / 8)) (Z.land b1 7) (ptr - b1 / 8) false)) (ST228 m1 b1 x15 x29 x30 x31).
Proof.
  intros m1 v cont b1 ptr jp jds' junk8 x15 x29 x30 x31 B1 P8 PZ MU WMo MI FR STK HDS HBD SRC.
  unfold ST228, IST.
  pose proof BDT as BDT'; unfold ablk, AIMG_HI, KLS in BDT'.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  goto 532. nb1 b1. goto 532. zxd. goto 532.
  schkJ US (S + ptr - b1 / 8) 14%Z 0x9a798.
  goto 552. schkJ US (S + ptr - b1 / 8 + 7) 5%Z 0x9a7ac.
  goto 568.
  eapply (ids_ld _ v _ (ptr - b1 / 8) (Z.land b1 7) jp jds' junk8); try eassumption; try (Z.div_mod_to_equations; lia).
Qed.


  (* [comment removed for export] *)
  Lemma ids_part : forall m1 v cont b1 ptr jp jds' junk8 (x15 x29 x30 x31 : word),
    0 <= b1 <= 64 -> 0 < ptr < 8 -> ptr + 8 <= zlen bs ->
    munch WI m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk8; C8 ra] -> stk bsegs m1 lo (bv_unsigned sp + -16) ->
    rw_cells bsegs m1 DS [C8 (Z_to_bv 64 v); CB 8 jds'] ->
    rw_cells bsegs m1 BD [C8 (Z_to_bv 64 cont); C4 (Z_to_bv 64 b1); CB 4 jp; C8 (Z_to_bv 64 (S + ptr)); C8 (Z_to_bv 64 S);
                          C8 (Z_to_bv 64 (S + 8))] ->
    bytes_at bsegs m1 S (map (Z_to_bv 8) bs) ->
    let nb := if ptr - b1 / 8 <? 0 then ptr else b1 / 8 in
    evtF bsegs RNG (POSTI v (mkBD (le64v bs (ptr - nb)) (b1 - nb * 8) (ptr - nb) false)) (ST228 m1 b1 x15 x29 x30 x31).
Proof.
  intros m1 v cont b1 ptr jp jds' junk8 x15 x29 x30 x31 B1 P8 PZ MU WMo MI FR STK HDS HBD SRC nb.
  unfold ST228, IST.
  pose proof BDT as BDT'; unfold ablk, AIMG_HI, KLS in BDT'.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  pose proof BS as BS'; unfold ablk, AIMG_HI, KLS in BS'.
  goto 304. nb1 b1. goto 332. zxd.
  unfold nb; destruct (Z.ltb_spec (ptr - b1 / 8) 0) as [NB|NB].
  - goto 348. l32. goto 364. zxd. goto 416.
    schkJ US (S + ptr - ptr) 14%Z 0x9a724. goto 436. schkJ US (S + ptr - ptr + 7) 5%Z 0x9a738.
    goto 568. fixbits HBD (b1 - ptr * 8).
    eapply (ids_ld _ v _ (ptr - ptr) (b1 - ptr * 8) jp jds' junk8); try eassumption; try (Z.div_mod_to_equations; lia).
  - goto 348. l32. goto 364. zxd. goto 416.
    schkJ US (S + ptr - b1 / 8) 14%Z 0x9a724. goto 436. schkJ US (S + ptr - b1 / 8 + 7) 5%Z 0x9a738.
    goto 568. fixbits HBD (b1 - b1 / 8 * 8).
    eapply (ids_ld _ v _ (ptr - b1 / 8) (b1 - b1 / 8 * 8) jp jds' junk8); try eassumption; try (Z.div_mod_to_equations; lia).
Qed.


  Lemma ids_228 : forall m1 v cont b1 ptr z st d2 jp jds' junk8 (x15 x29 x30 x31 : word),
    0 <= b1 < 2^31 -> 0 <= ptr -> ptr + 8 <= Z.max 8 (zlen bs) -> (zlen bs < 8 -> ptr = 0) -> (z = true -> 64 < b1) ->
    reload_dstream bs (mkBD cont b1 ptr z) = Ok (st, d2) ->
    munch WI m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk8; C8 ra] -> stk bsegs m1 lo (bv_unsigned sp + -16) ->
    rw_cells bsegs m1 DS [C8 (Z_to_bv 64 v); CB 8 jds'] ->
    rw_cells bsegs m1 BD [C8 (Z_to_bv 64 cont); C4 (Z_to_bv 64 b1); CB 4 jp;
                          C8 (Z_to_bv 64 (if z then AZEROFILLED else S + ptr)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
    bytes_at bsegs m1 S (map (Z_to_bv 8) bs) ->
    evtF bsegs RNG (POSTI v d2) (ST228 m1 b1 x15 x29 x30 x31).
Proof.
  intros m1 v cont b1 ptr z st d2 jp jds' junk8 x15 x29 x30 x31 B1 P0 PM PZ ZB RL MU WMo MI FR STK HDS HBD SRC.
  unfold reload_dstream in RL; cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
  rewrite Z.shiftr_div_pow2 in RL by lia. change (2 ^ 3) with 8 in RL.
  revert RL. destruct (Z.ltb_spec 64 b1) as [OV|OV]; intro RL.
  - injection RL as E1 E2; subst st d2. eapply ids_ovf; try eassumption; lia.
  - assert (ZF : z = false) by (destruct z; [specialize (ZB eq_refl); lia | reflexivity]). subst z.
    change (if false then AZEROFILLED else S + ptr) with (S + ptr) in HBD.
    revert RL. destruct (Z.leb_spec 8 ptr) as [P8|P8]; intro RL.
    + assert (PZ8 : ptr + 8 <= zlen bs) by (destruct (Z.ltb_spec (zlen bs) 8) as [L|L]; [specialize (PZ L); lia | lia]).
      cbv beta iota zeta in RL. rewrite readLE64_ok in RL by (Z.div_mod_to_equations; lia). cbn [bind] in RL.
      injection RL as E1 E2; subst st d2.
      exact (ids_fast m1 v cont b1 ptr jp jds' junk8 x15 x29 x30 x31 ltac:(lia) P8 PZ8 MU WMo MI FR STK HDS HBD SRC).
    + revert RL. destruct (Z.eqb_spec ptr 0) as [E0|E0]; intro RL.
      * subst ptr. injection RL as E1 E2; subst st d2. rewrite Z.add_0_r in HBD.
        exact (ids_endc m1 v cont b1 jp jds' junk8 x15 x29 x30 x31 ltac:(lia) MU WMo MI FR STK HDS HBD).
      * assert (PZ8 : ptr + 8 <= zlen bs) by (destruct (Z.ltb_spec (zlen bs) 8) as [L|L]; [specialize (PZ L); lia | lia]).
        pose proof (ids_part m1 v cont b1 ptr jp jds' junk8 x15 x29 x30 x31 ltac:(lia) ltac:(lia) PZ8 MU WMo MI FR STK HDS HBD SRC)
          as IP.
        cbv zeta in IP. revert IP RL. destruct (Z.ltb_spec (ptr - b1 / 8) 0) as [NB|NB]; intros IP RL.
        -- cbv beta iota zeta in RL. rewrite readLE64_ok in RL by lia. cbn [bind] in RL.
           injection RL as E1 E2; subst st d2. exact IP.
        -- cbv beta iota zeta in RL. rewrite readLE64_ok in RL by (Z.div_mod_to_equations; lia). cbn [bind] in RL.
           injection RL as E1 E2; subst st d2. exact IP.
Qed.

  Lemma ids_entry : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (d : bitD) (jds jp : list byte) (tl : Z) (fmw : word)
      (v : Z) (d1 : bitD) (st : dstatus) (d2 : bitD),
    rw_cells bsegs m DS [CB 16 jds] -> rw_cells bsegs m BD (bitdz_cellsA S d jp) ->
    rw_cells bsegs m DT [C2 (Z_to_bv 64 tl); C2 fmw] ->
    bytes_at bsegs m S (map (Z_to_bv 8) bs) -> 0 <= tl <= 12 -> bitd_ok bs d ->
    read_bits d tl = Ok (v, d1) -> reload_dstream bs d1 = Ok (st, d2) ->
    stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m -> artcells m ->
    a0 = Z_to_bv 64 DS -> a1 = Z_to_bv 64 BD -> a2 = Z_to_bv 64 DT ->
    evtF bsegs RNG (POSTI v d2)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFSE_INIT_DSTATE) fc None m (seg_rom bsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 d jds jp tl fmw v d1 st d2 HDS HBD HDT SRC TL BOK RB RL STK MI ART E0 E1 E2.
  subst a0 a1 a2.
  unfold artcells in ART; repeat (let H := fresh "ARc" in destruct ART as [H ART]).
  pose proof BDT as BDT'; unfold ablk, AIMG_HI, KLS in BDT'.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  pose proof (rng_mask_sh RNG RISH) as RMKs.
  assert (RMK : rng RNG ABIT_MASK 128) by (eapply rng_sub; [exact RI| |]; unfold ABIT_MASK; apply Z.leb_le; vm_compute; reflexivity).
  assert (MKB : 0 <= ABIT_MASK /\ ABIT_MASK + 136 <= 2^47) by (unfold ABIT_MASK; lia).
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp); (DS, DS + 16); (BD, BD + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WMo.
  unfold AFSE_INIT_DSTATE, bitdz_cellsA in *.
  assert (L1 : Z.land DT 1 = 0) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; change (2^1) with 2; Z.div_mod_to_equations; lia).
  carve_frame 16%nat STK.
  repeat first [ zstep | bF ]. zck 13%Z ZDT. zstep. bF.
  zstep. zstep. rewrite land7_mod, BD8. bF. zstep. zstep. zck 17%Z ZBD. zstep. bF. zstep. zstep. zstep. zstep. zck 5%Z ZBD. wk. rewrite (zx16_lit tl) by lia. wk. fixmask tl. zck 7%Z ZMK. wk. zck 5%Z ZBD.
  let mm := curm in pose proof (maskA_rd mm tl ltac:(assumption) ltac:(lia)) as MRD.
  wk. fixreg 14%Z tl. wk. rewrite land7_mod, DS8. bF. wk. zck 14%Z ZDS. wkto 228.
  destruct BOK as (BC & BB & BP & BPZ & BSm & BZ).
  assert (BU : bv_unsigned (sx32 (Z_to_bv 64 (bd_bits d))) = bd_bits d)
    by (rewrite sx32_small by lia; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
  rewrite BU in HDS, HBD |- *. clear BU.
  rewrite (swrap32_small (bd_bits d + tl)) in HDS, HBD |- * by lia.
  rewrite (land64_mod (bd_bits d + tl)) in HDS. rewrite (Z.mod_small (bd_bits d + tl)) in HDS by lia.
  rewrite (neg_shift_land (bd_bits d + tl)) in HDS by lia.
  rewrite (land64_mod (bd_cont d)) in HDS. rewrite (Z.mod_small (bd_cont d)) in HDS by lia.
  rewrite (shr_land64 (bd_cont d)) in HDS by (Z.div_mod_to_equations; lia).
  assert (PT : 0 < 2 ^ tl <= 2 ^ 12) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  rewrite RF_huf_tbl_kit.zx32_unsigned_lit in HDS by lia.
  replace (64 - (bd_bits d + tl)) with (64 - bd_bits d - tl) in HDS by ring.
  unfold read_bits, look_bits, bit_mask in RB.
  replace ((0 <=? tl) && (tl <? 32)) with true in RB by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  cbn [bind] in RB. injection RB as EV ED. subst v d1.
  unfold skip_bits, u32 in RL. rewrite (Z.mod_small (bd_bits d + tl)) in RL by lia.
  eapply (ids_228 _ _ (bd_cont d) (bd_bits d + tl) (bd_ptr d) (bd_zero d) st d2 jp).
  all: first [ eassumption | lia | (intro HZ; specialize (BZ HZ); lia) ].
Qed.
End IDS.

Lemma fse_init_dstate_proofA : fse_init_dstate_stmtA.
Proof.
  unfold fse_init_dstate_stmtA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m DS BD DT S tl bs
    d jds jp fmw v d1 st d2 lo HDS HBD HDT SRC BY TL BOK RB RL SPD DS8 DSB BD8 BDH BDT DT4 BS S8 STK BOT LO MI ART
    ZDS ZBD ZDT ZMK US RDS RDSs RBD RBDs RDT RDTs RS RSs RSTK RI RISH E0 E1 E2.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  pose proof BS as BS'; unfold ablk, AIMG_HI, KLS in BS'.
  unfold AFSE_INIT_STACK in LO, RSTK.
  eapply ids_entry with (bs := bs); try eassumption.
  all: first [ lia
             | (rewrite DS8; exact RDSs) | (rewrite BD8; exact RBDs)
             | (replace (nshad (4 + DT mod 8)) with 1;
                [exact RDTs | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia])
             | solve_appW ].
Qed.
End CANSEC1.
