(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
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
  AF_huf_tbl_iface2 AF_huf_fdw_kit AF_fse_rd_mem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_fdw_kit RF_huf_fdw_pure.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import I_asan_memset.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_bitd () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib5Lists7ListDef6Forall00c59OSSVerify5KrLib5BothW;AF_huf_bitd4rsumC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5Plain>RF_huf_fdw_kit=Znth_byte_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5BothW;AF_huf_bitd6BS_PREC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib6Common:HufWalkKit7lesmallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2>bit_init_postAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd5ST_bsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Common:HufWalkKit9byte_ZnthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib3Lib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit?unpoisoned_appWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_fse_rd_base4chkBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4svalC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib3Mem3sxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib3MemAsext_extract_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_bdt_kit7acc_shZC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib6Common:HufWalkKit6src_rdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib3MemAzext_extract_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF=rng_acc_litZ'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib3Lib7ZBridge5zr_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib6Common:FseWalkKit8byte_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit<zshadow_appWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_bdt_kit4chkZC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp<init_dstreamC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp7bd_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2<bitdz_cellsAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppI59OSSVerify5KrLib4Spec9FseNCount3res00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount3res02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount9highbit32C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4SpecAHufPure_FseDecomp4bitD01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount3res01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib3Lib3Tac?rw_cells_forgetC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Common:HufWalkKitBinit_dstream_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr01C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib6Common8FseRdKit3sm1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib6Common8FseRdKit;brute_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C59OSSVerify5KrLib3Lib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib6Common8FseRdKit3sm2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8FseRdKit3sm3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC59OSSVerify5KrLib3Lib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit3nsmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_andC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit4pc_aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit4pc_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit4pc_cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC59OSSVerify5KrLib3Lib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC59OSSVerify5KrLib3Lib8PropExec5m_mulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit4pc_dC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0<C59OSSVerify5KrLib3Lib8PropExec7v_srliwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7w_srliwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C59OSSVerify5KrLib3Lib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6w_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp7bd_contC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp7bd_bitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecAHufPure_FseDecomp6bd_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit<highbit32_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib5BothW>AF_huf_fdw_kit:land64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4LibA6Shadow9land7_modC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib4LibA6ShadowBsigned_lit_small64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib4LibA6Shadow8sxb_svalC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK46Stdlib9micromega5Tauto8GFormula03C45stdpp9bitvector;definitions:bv_extractK46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib5Lists7ListDef6firstnK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec9FseNCount4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8FseRdKit8all_fromC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4SpecAHufPure_FseDecomp4bitD00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2?ABIT_INIT_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCountNZSTD_error_corruption_detectedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_bdt_kit4sxb0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop03C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2;AZEROFILLEDC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd6bs_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit4zxb0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd;rsum_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd5bs_b1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd5bs_b2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd5bs_b3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd5bs_b4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd5bs_b5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKit=lor_shift_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8artcellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit7shcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6hull64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow7app_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kitFzshadow_of_unpoisoned8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW@AF_huf_tbl_iface7zshadowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5BothW9Stdio_kit4appWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4ListClength_zero_iff_nilC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib5BothW=AF_fse_rd_mem=amemsetZ_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AF_fse_rd_mem=amemset_specZC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_15C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC59OSSVerify5KrLib5Plain?RF_huf_fdw_pure=lesmall_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP9bv_lit_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd5bs_b6C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKitDinit_dstream_big_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:HufWalkKitCinit_dstream_big_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AF_huf_fdw_kit=le64_lbu_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothWAAF_huf_tbl_iface2>bit_init_stmtAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5nshadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib3Mem;wr_at_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KLOWC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC59OSSVerify5KrLib4SpecAHufPure_FseDecompHZSTD_error_srcSize_wrongC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C59OSSVerify5KrLib4Spec9FseNCountBZSTD_error_GENERICC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AF_huf_bitd;ABIT_INIT_DC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Fixpoint rsum (bs : list Z) (j : nat) : Z :=
  match j with O => 0 | Datatypes.S j' => rsum bs j' + Znth (Z.of_nat (Datatypes.S j')) bs * 2^(8 * Z.of_nat (Datatypes.S j')) end.

Lemma rsum_nonneg : forall bs j, Forall (fun c => 0 <= c < 256) bs -> 0 <= rsum bs j.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bitd ()) ["CANSEC1"] "h01xh17__arithh24__ffh38__varmaph45__with51jh61mh71nh82Hah94__x1h:4__x2h;4__x3h<4__x4h=2BYh>1Hh?2H0h@2H1hA2IHhB6__sat1hC6__sat2hD2bshE1chF4cstrhG1yp;1p;2p;3p;4p;7p;<p;Bp;8p10000p4p7210p1000\p4p710p8g001:j1]Tg001Zj15Tg002?j1=Tg002]j2?Tg0039j2ETg003Tj3pTg0045j2@Tg0050j1eTg005Pj1dTg005nj1bTg006Lj1`Tg0077j2ATg007Zj2xTg008<j2HTg008Vj2tTg009Bj3qTg009\j3oTg00:;j4lTg00:mR0j2LTg00;IR1j16Tg00;hR2j13Tg00<Hj3fTg00=Oj2ITg00>GR3j21Tg00>dj3PTg00?HR4j2:Tg00?eR5j22Tg00@Bj1cTg00@`j4^Tg00AGj1zTg00Alj2yTg00BTj1<Tg00C9j2DTg00Cbj2BTg00DKj2STg00E7j2ZTg00EXj4vTg00F9j3uTg00FZj2sTg00GCj2rTg00Goj3XTg00HOj2WTg00Hmj4QTg00IKj1nTg00Imj2CTg00JPj3UTg00K3j3TTg00KVj7kTg00L:j4jTg00Lej4mTg00MFj4VTg00N1j7iTg00NUj4hTg00O8l<RTg00O]lBGTg00PCl<gTg00Phj3YTg00QQj3[Tg00R:j8wTg00R^R6f0R7'Lp=0g00S<R8f1R9g00SZP7CVp=;P9g00TAR:g00T`R;P;g00U@R<P7g00U`Fip=4P8P8g00V@P7Chp=F1H87p=7g00VdR=P=P8P8P1P2P2f3R1g00WCf2R>P9P7M<Rp=aP=P8P8P8P2P2f5R2f4R?P1P>P9P7M<Rp=OP8P8P8P8P8P8P3P7P9P>P3P1P?P2f6R3f7R@f8RAf9RBMBGp=KP8P8P8P8P8P8P4P7P9P>P4P1P?P2P3P@PAPBMBGp=NP8P8P8P8P8P8P5P7P9P>P5P1P?P2P3P@PAPBMBGp=_P8P8P0P2P0P?P6P6P1P>P9P7M<gp=MAY897p=8A[897p=\AY8>9=[87p=9P8P9g00WgP7CVp=JP1P:P;P;P<P>P9P7Gwp=>%]8%07g00XNR0#5RB#5R5#5R4#5#5#5#5#5#=RC,?7'EXE8=p891@17#0RDX5=g00Y3RE#eRF%]ERG%d8RH%b8RI%`8RJ1A86RK/;K'41xJ<RLP7P>g00Y_RMg00Z?RN'H1t7>=qMNdAo869ClRNb2b3b41L66P7b1g00Z_RM,@>#0e%69RO#3RP=f?>1IP?RP#01?PC'E%=BRP%=4R4%6>#3'1RQPFPGPHPI1A8PRR,;K,4JPLPNb2b3b4%0PRSP7b13P1:PQ#01@31RQ%61RT#3RU/I3RV114URW,:PRX'1RY'2RZ#0%31R[%=0R\'2R],14R^,:PR_,1VR`,2QRa#0P7X08Rb1L97#cXG8X08Rc1H86RdPZPaPbPbPb1297#F#7X68X78PQPQ%7QPYP`PbPbPb1197#F#7X68X78R`PVPV%7VPXP_PbPbPb1:97#F#7X68X78RVPPPP%7PRYPWP^PbPbPbP`P4P4%74R^PUP]PbPb%37#7X0=RQPTP]127\X08R]P1P[%7[CaRaEOM:KM:NM:KM:_EM%0X%0_R_PbPcPdPXPbP]P[O1R[O1R],14RX,:PPbPbPbPVPPPPPYPWPXPbPbPbP`P4P4P^PUP]PbPbPQPTP[PaEOM:KM:NEMP7C^P_%z?%3?#0%32/2\,14,yP1?6PR_%33/2\,14#0%3@/2\,14,:P,?6[[g00[>Ra%3AR[/2\,14RT=PP9UX8S1:PTRT#0\a^8S%<0RS#<#<#<#<#<#<Ra#=,D8RQ%6MRb#6R]#6RU,B8R^%6U#6,B8RU'81B8bRb1B8MRM,8^R`1B8]R]18U^RX/\^'81D8CRW18]M18b],8W3959Q'\59^39g00[ZRQ'SP81Z8\P01Z86Cv9u80,s8RW%5a#=,D8Ra1D8P18^^'899a`79X99WU79M/SQ,rU=XEF5XEPGP8P81W8?P>PHCQP91W81CQPIPJPJ1JKR,4J%n;RRPJ1A841C85R51A8\5U85T8,;K,4JPR1C8SRS,JK,4JC>C>PRPJ1;K5,4JPRPJPJP:P;P;P<1C8BRB,;K,4J1A8C,JB,4JFkPRPJ1C80R0,;K,4JPRAT8BS9U80,;K,4JC>C>C>C>PLPNb2b3b4X98X:8X;8X<812?\,14#01?6?[\_%0?%01R_1?1C'E1123,2?#0\_[[[^98^:8^;8^<8P7P[PT%6A#3f;RT'I1@TAP>P1P3P@O8b1bBbCbFb@Cjb?b>1@?O#0eXADX5=P9CmW=X5=WDo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

Definition ABIT_INIT_D : Z := 0x8dd80.        (* [comment removed for export] *)

Lemma bfa_kshz_unp : forall (m : word -> option byte) A N, unpoisoned m A (A + N) -> A mod 8 = 0 -> N mod 8 = 0 ->
  kshz_fact m ASHOFF A N.
Proof.
  intros m A N (H0 & H1 & H) HA HN x Hx.
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  destruct (H (x / 8)) as (b & Hb & Hg); [lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |].
  rewrite (gran_ok_full _ _ Hg) in Hb by (Z.div_mod_to_equations; lia). exact Hb.
Qed.
Lemma bfa_mb0 : forall segs E (m : word -> option byte) a j,
  ev E j = rdval segs m (adenot E a) 1 false -> m (adenot E a) = Some (Z_to_bv 8 0) ->
  branch_taken BC_NE (edenot E (EVar j)) (edenot E (ELit 0)) = false.
Proof.
  intros segs E m a j H H0. cbn [edenot]. rewrite H. unfold rdval. rewrite (rdn1_some segs m _ _ H0).
  vm_compute. reflexivity.
Qed.

Lemma bfa_add_u : forall z k, 0 <= z -> 0 <= k -> z + k < 2^64 ->
  bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 z) (Z_to_bv 64 k)) = z + k.
Proof.
  intros z k Hz Hk Hzk. pose proof (u_add_eqm (Z_to_bv 64 z) (Z_to_bv 64 k)) as Q. unfold eqm in Q.
  rewrite !Z_to_bv_small in Q by (unfold bv_modulus; cbn; lia).
  destruct Q as (q & Q).
  pose proof (bv_unsigned_in_range 64 (alu64 ALU_ADD (Z_to_bv 64 z) (Z_to_bv 64 k))) as R.
  rewrite Q in R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  rewrite Q. assert (q = 0) by lia. subst q. lia.
Qed.

Lemma bfa_adenot_srl : forall E j k off z, ev E j = Z_to_bv 64 z -> 0 <= z -> 0 <= k -> z + k < 2^64 ->
  adenot E {| a_base := EAlu ALU_SRL (EAlu ALU_ADD (EVar j) (ELit k)) (ELit 3); a_off := off |} = Z_to_bv 64 (off + Z.shiftr (z + k) 3).
Proof.
  intros E j k off z H Hz Hk Hzk. unfold adenot, PropExec.v_addi. cbn [a_base a_off edenot]. rewrite srl3_u, H, bfa_add_u by lia.
  f_equal. lia.
Qed.

Lemma bfa_adenot_srl0 : forall E j off z, ev E j = Z_to_bv 64 z -> 0 <= z < 2^64 ->
  adenot E {| a_base := EAlu ALU_SRL (EVar j) (ELit 3); a_off := off |} = Z_to_bv 64 (off + Z.shiftr z 3).
Proof.
  intros E j off z H Hz. unfold adenot, PropExec.v_addi. cbn [a_base a_off edenot]. rewrite srl3_u, H, Z_to_bv_small by (unfold bv_modulus; cbn; lia).
  f_equal. lia.
Qed.
Lemma bfa_adenot_add2 : forall E i1 i2 off z1 z2, ev E i1 = Z_to_bv 64 z1 -> ev E i2 = Z_to_bv 64 z2 ->
  0 <= z1 -> 0 <= z2 -> z1 + z2 < 2^64 ->
  adenot E {| a_base := EAlu ALU_ADD (EVar i1) (EVar i2); a_off := off |} = Z_to_bv 64 (z1 + z2 + off).
Proof.
  intros E i1 i2 off z1 z2 H1 H2 P1 P2 P3. unfold adenot, PropExec.v_addi. cbn [a_base a_off edenot].
  rewrite H1, H2, bfa_add_u by lia. reflexivity.
Qed.

Lemma bfa_init_n1_lb0 : forall bs, zlen bs = 1 -> Znth 0 bs = 0 ->
  init_dstream bs = Err ZSTD_error_corruption_detected.
Proof.
  intros bs H1 H0. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (1 - 1) with 0. cbn [andb Z.leb Z.ltb Z.compare]. rewrite H0. reflexivity.
Qed.
Lemma bfa_init_n2_lb0 : forall bs, zlen bs = 2 -> Znth 1 bs = 0 ->
  init_dstream bs = Err ZSTD_error_corruption_detected.
Proof.
  intros bs H1 H0. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (2 - 1) with 1. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 1 <? 2 then Ok (Znth 1 bs) else Ub) with (Ok (Znth 1 bs) : res Z). cbv beta iota. rewrite H0. reflexivity.
Qed.
Lemma bfa_init_n2 : forall bs, zlen bs = 2 -> Znth 1 bs <> 0 -> 0 <= Znth 1 bs < 256 ->
  init_dstream bs = Ok (mkBD (Znth 0 bs + 256 * Znth 1 bs) (56 - Z.log2 (Znth 1 bs)) 0 false).
Proof.
  intros bs H1 H0 HR. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (2 - 1) with 1. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 1 <? 2 then Ok (Znth 1 bs) else Ub) with (Ok (Znth 1 bs) : res Z). cbv beta iota.
  replace (Znth 1 bs =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((0 <? Znth 1 bs) && (Znth 1 bs <? 2^32))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
  try replace (2^8) with 256 by reflexivity. do 2 f_equal; lia.
Qed.
Lemma bfa_init_n3 : forall bs c, zlen bs = 3 -> Znth 2 bs <> 0 -> 0 <= Znth 2 bs < 256 -> c = Znth 0 bs + Znth 2 bs * 65536 + Znth 1 bs * 256 ->
  init_dstream bs = Ok (mkBD c (48 - Z.log2 (Znth 2 bs)) 0 false).
Proof.
  intros bs c H1 H0 HR HC. subst c. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (3 - 1) with 2. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 2 <? 3 then Ok (Znth 2 bs) else Ub) with (Ok (Znth 2 bs) : res Z). cbv beta iota.
  replace (Znth 2 bs =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((0 <? Znth 2 bs) && (Znth 2 bs <? 2^32))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
  do 2 f_equal; try change (2 ^ 8) with 256; try change (2 ^ 16) with 65536; lia.
Qed.
Lemma bfa_init_n3_lb0 : forall bs, zlen bs = 3 -> Znth 2 bs = 0 ->
  init_dstream bs = Err ZSTD_error_corruption_detected.
Proof.
  intros bs H1 H0. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (3 - 1) with 2. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 2 <? 3 then Ok (Znth 2 bs) else Ub) with (Ok (Znth 2 bs) : res Z). cbv beta iota. rewrite H0. reflexivity.
Qed.
Lemma bfa_init_n4 : forall bs c, zlen bs = 4 -> Znth 3 bs <> 0 -> 0 <= Znth 3 bs < 256 -> c = Znth 0 bs + Znth 3 bs * 16777216 + Znth 2 bs * 65536 + Znth 1 bs * 256 ->
  init_dstream bs = Ok (mkBD c (40 - Z.log2 (Znth 3 bs)) 0 false).
Proof.
  intros bs c H1 H0 HR HC. subst c. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (4 - 1) with 3. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 3 <? 4 then Ok (Znth 3 bs) else Ub) with (Ok (Znth 3 bs) : res Z). cbv beta iota.
  replace (Znth 3 bs =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((0 <? Znth 3 bs) && (Znth 3 bs <? 2^32))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
  do 2 f_equal; try change (2 ^ 8) with 256; try change (2 ^ 16) with 65536; try change (2 ^ 24) with 16777216; lia.
Qed.
Lemma bfa_init_n4_lb0 : forall bs, zlen bs = 4 -> Znth 3 bs = 0 ->
  init_dstream bs = Err ZSTD_error_corruption_detected.
Proof.
  intros bs H1 H0. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (4 - 1) with 3. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 3 <? 4 then Ok (Znth 3 bs) else Ub) with (Ok (Znth 3 bs) : res Z). cbv beta iota. rewrite H0. reflexivity.
Qed.
Lemma bfa_init_n5 : forall bs c, zlen bs = 5 -> Znth 4 bs <> 0 -> 0 <= Znth 4 bs < 256 -> c = Znth 0 bs + Znth 4 bs * 4294967296 + Znth 3 bs * 16777216 + Znth 2 bs * 65536 + Znth 1 bs * 256 ->
  init_dstream bs = Ok (mkBD c (32 - Z.log2 (Znth 4 bs)) 0 false).
Proof.
  intros bs c H1 H0 HR HC. subst c. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (5 - 1) with 4. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 4 <? 5 then Ok (Znth 4 bs) else Ub) with (Ok (Znth 4 bs) : res Z). cbv beta iota.
  replace (Znth 4 bs =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((0 <? Znth 4 bs) && (Znth 4 bs <? 2^32))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
  do 2 f_equal; try change (2 ^ 8) with 256; try change (2 ^ 16) with 65536; try change (2 ^ 24) with 16777216; try change (2 ^ 32) with 4294967296; lia.
Qed.
Lemma bfa_init_n5_lb0 : forall bs, zlen bs = 5 -> Znth 4 bs = 0 ->
  init_dstream bs = Err ZSTD_error_corruption_detected.
Proof.
  intros bs H1 H0. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (5 - 1) with 4. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 4 <? 5 then Ok (Znth 4 bs) else Ub) with (Ok (Znth 4 bs) : res Z). cbv beta iota. rewrite H0. reflexivity.
Qed.
Lemma bfa_init_n6 : forall bs c, zlen bs = 6 -> Znth 5 bs <> 0 -> 0 <= Znth 5 bs < 256 -> c = Znth 0 bs + Znth 5 bs * 1099511627776 + Znth 4 bs * 4294967296 + Znth 3 bs * 16777216 + Znth 2 bs * 65536 + Znth 1 bs * 256 ->
  init_dstream bs = Ok (mkBD c (24 - Z.log2 (Znth 5 bs)) 0 false).
Proof.
  intros bs c H1 H0 HR HC. subst c. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (6 - 1) with 5. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 5 <? 6 then Ok (Znth 5 bs) else Ub) with (Ok (Znth 5 bs) : res Z). cbv beta iota.
  replace (Znth 5 bs =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((0 <? Znth 5 bs) && (Znth 5 bs <? 2^32))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
  do 2 f_equal; try change (2 ^ 8) with 256; try change (2 ^ 16) with 65536; try change (2 ^ 24) with 16777216; try change (2 ^ 32) with 4294967296; try change (2 ^ 40) with 1099511627776; lia.
Qed.
Lemma bfa_init_n6_lb0 : forall bs, zlen bs = 6 -> Znth 5 bs = 0 ->
  init_dstream bs = Err ZSTD_error_corruption_detected.
Proof.
  intros bs H1 H0. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (6 - 1) with 5. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 5 <? 6 then Ok (Znth 5 bs) else Ub) with (Ok (Znth 5 bs) : res Z). cbv beta iota. rewrite H0. reflexivity.
Qed.
Lemma bfa_init_n7 : forall bs c, zlen bs = 7 -> Znth 6 bs <> 0 -> 0 <= Znth 6 bs < 256 -> c = Znth 0 bs + Znth 6 bs * 281474976710656 + Znth 5 bs * 1099511627776 + Znth 4 bs * 4294967296 + Znth 3 bs * 16777216 + Znth 2 bs * 65536 + Znth 1 bs * 256 ->
  init_dstream bs = Ok (mkBD c (16 - Z.log2 (Znth 6 bs)) 0 false).
Proof.
  intros bs c H1 H0 HR HC. subst c. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (7 - 1) with 6. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 6 <? 7 then Ok (Znth 6 bs) else Ub) with (Ok (Znth 6 bs) : res Z). cbv beta iota.
  replace (Znth 6 bs =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((0 <? Znth 6 bs) && (Znth 6 bs <? 2^32))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
  do 2 f_equal; try change (2 ^ 8) with 256; try change (2 ^ 16) with 65536; try change (2 ^ 24) with 16777216; try change (2 ^ 32) with 4294967296; try change (2 ^ 40) with 1099511627776; try change (2 ^ 48) with 281474976710656; lia.
Qed.
Lemma bfa_init_n7_lb0 : forall bs, zlen bs = 7 -> Znth 6 bs = 0 ->
  init_dstream bs = Err ZSTD_error_corruption_detected.
Proof.
  intros bs H1 H0. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow]. change (7 - 1) with 6. cbn [andb Z.leb Z.ltb Z.compare].
  change (if 6 <? 7 then Ok (Znth 6 bs) else Ub) with (Ok (Znth 6 bs) : res Z). cbv beta iota. rewrite H0. reflexivity.
Qed.
Lemma bfa_adenot_var : forall E i off z, ev E i = Z_to_bv 64 z -> 0 <= z < 2^64 ->
  adenot E {| a_base := EVar i; a_off := off |} = Z_to_bv 64 (z + off).
Proof.
  intros E i off z H Hz. unfold adenot, PropExec.v_addi. cbn [a_base a_off edenot]. rewrite H, Z_to_bv_small by (unfold bv_modulus; cbn; lia).
  reflexivity.
Qed.
Lemma bfa_init_n1 : forall bs, zlen bs = 1 -> Znth 0 bs <> 0 -> 0 <= Znth 0 bs < 256 ->
  init_dstream bs = Ok (mkBD (Znth 0 bs) (64 - Z.log2 (Znth 0 bs)) 0 false).
Proof.
  intros bs H1 H0 HR. cbv [init_dstream add_byte load highbit32 FseNCount.Zlength bind].
  rewrite ?H1. cbn -[Znth Z.log2 Z.pow].
  replace (Znth 0 bs =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((0 <? Znth 0 bs) && (Znth 0 bs <? 2^32))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
  change (1 - 1) with 0. cbn [andb Z.leb Z.ltb Z.compare]. replace (Znth 0 bs =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((0 <? Znth 0 bs) && (Znth 0 bs <? 2^32))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
  do 2 f_equal. lia.
Qed.
Lemma bfa_firstn1_skipn : forall (l : list Z) n, (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l 0].
Proof.
  induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hn. lia.
Qed.

Lemma bfa_rd1 : forall segs (m : word -> option byte) S (bs : list Z) E j w k,
  bytes_at segs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  ev E j = rdval segs m w 1 false -> w = Z_to_bv 64 (S + k) -> 0 <= k < zlen bs ->
  bv_unsigned (ev E j) = Znth k bs.
Proof.
  intros segs m S bs E j w k HB BY H Hw Hk. subst w. rewrite H. unfold rdval.
  replace (Z_to_bv 64 (S + k)) with (wa (S + Z.of_nat (Z.to_nat k))) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_rdn segs m S _ (Z.to_nat k) 1 HB) by (rewrite length_map; lia).
  rewrite skipn_map, firstn_map, bfa_firstn1_skipn by lia.
  assert (R : 0 <= nth (Z.to_nat k) bs 0 < 256).
  { rewrite Forall_forall in BY. apply BY. apply nth_In. lia. }
  unfold Znth. cbn [map extz bytes_le_to_Z]. change (0 ≪ 8) with 0. rewrite Z.lor_0_r.
  rewrite (Z_to_bv_small 8) by (unfold bv_modulus; cbn -[Z.pow]; lia).
  rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; lia). reflexivity.
Qed.
Lemma bfa_init_main : forall bs, 8 <= zlen bs -> Znth (zlen bs + -1) bs <> 0 -> 0 <= Znth (zlen bs + -1) bs < 256 ->
  init_dstream bs = Ok (mkBD (Znth (zlen bs + -8) bs + 2^8 * Znth (zlen bs + -7) bs + 2^16 * Znth (zlen bs + -6) bs
                              + 2^24 * Znth (zlen bs + -5) bs + 2^32 * Znth (zlen bs + -4) bs + 2^40 * Znth (zlen bs + -3) bs
                              + 2^48 * Znth (zlen bs + -2) bs + 2^56 * Znth (zlen bs + -1) bs)
                             (8 - Z.log2 (Znth (zlen bs + -1) bs)) (zlen bs - 8) false).
Proof.
  intros bs H8 H0 HR. cbv [init_dstream readLE64 load highbit32 FseNCount.Zlength bind].
  assert (E1 : (zlen bs <? 1) = false) by (apply Z.ltb_ge; lia).
  assert (E2 : (8 <=? zlen bs) = true) by (apply Z.leb_le; lia).
  assert (E3 : ((0 <=? zlen bs - 8) && (zlen bs - 8 + 8 <=? zlen bs))%bool = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  assert (E4 : ((0 <=? zlen bs - 1) && (zlen bs - 1 <? zlen bs))%bool = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (zlen bs - 1) with (zlen bs + -1) in * by lia.
  assert (E5 : (Znth (zlen bs + -1) bs =? 0) = false) by (apply Z.eqb_neq; exact H0).
  assert (E6 : ((0 <? Znth (zlen bs + -1) bs) && (Znth (zlen bs + -1) bs <? 2^32))%bool = true) by (apply andb_true_intro; split; [apply Z.ltb_lt | apply Z.ltb_lt]; lia).
  rewrite E1, E2, E3, E4, E5, E6.
  replace (zlen bs - 8 + 1) with (zlen bs + -7) by lia. replace (zlen bs - 8 + 2) with (zlen bs + -6) by lia.
  replace (zlen bs - 8 + 3) with (zlen bs + -5) by lia. replace (zlen bs - 8 + 4) with (zlen bs + -4) by lia.
  replace (zlen bs - 8 + 5) with (zlen bs + -3) by lia. replace (zlen bs - 8 + 6) with (zlen bs + -2) by lia.
  replace (zlen bs - 8 + 7) with (zlen bs + -1) by lia.
  replace (Znth (zlen bs - 8) bs) with (Znth (zlen bs + -8) bs) by (f_equal; lia).
  reflexivity.
Qed.
Lemma bfa_init_lb0 : forall bs, 8 <= zlen bs -> Znth (zlen bs - 1) bs = 0 ->
  init_dstream bs = Err ZSTD_error_GENERIC.
Proof.
  intros bs H8 H0. cbv [init_dstream readLE64 load highbit32 FseNCount.Zlength bind].
  assert (E1 : (zlen bs <? 1) = false) by (apply Z.ltb_ge; lia).
  assert (E2 : (8 <=? zlen bs) = true) by (apply Z.leb_le; lia).
  assert (E3 : ((0 <=? zlen bs - 8) && (zlen bs - 8 + 8 <=? zlen bs))%bool = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  assert (E4 : ((0 <=? zlen bs - 1) && (zlen bs - 1 <? zlen bs))%bool = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite E1, E2, E3, E4, H0. reflexivity.
Qed.
Ltac bfa_mb0_go KS :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
      let H := fresh "HRD" in kx_read_eq j H;
      apply (bfa_mb0 _ E _ _ j H); clear H;
      lazymatch goal with
      | KXA : forall j, (j < length ?zv)%nat -> ev E j = _ |- _ =>
        lazymatch goal with
        | |- _ (adenot E {| a_base := EAlu ALU_SRL (EAlu ALU_ADD (EVar ?i) (ELit ?k)) (ELit 3); a_off := ?off |}) = _ =>
            rewrite (bfa_adenot_srl E i k off _ (KXA i ltac:(vm_compute; lia))) by (cbv [nth]; lia)
        | |- _ (adenot E {| a_base := EAlu ALU_SRL (EVar ?i) (ELit 3); a_off := ?off |}) = _ =>
            rewrite (bfa_adenot_srl0 E i off _ (KXA i ltac:(vm_compute; lia))) by (cbv [nth]; lia)
        end
      end;
      cbv [nth]; apply KS; lia
  end.
Lemma bfa_ez_add : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EAlu ALU_ADD a b) = ta + tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma bfa_ez_sub : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EAlu ALU_SUB a b) = ta - tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma bfa_ez_mul : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EMd M_MUL a b) = ta * tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma bfa_ez_srl : forall zv E a sh ta, ez zv E a = ta -> ez zv E (EAlu ALU_SRL a (ELit sh)) = (ta mod 2^64) / 2^(sh mod 64).
Proof. intros zv E a sh ta <-. reflexivity. Qed.
Lemma bfa_ez_lit : forall zv E z, ez zv E (ELit z) = z.
Proof. reflexivity. Qed.
Lemma bfa_ez_hi : forall zv E j, Nat.ltb j (length zv) = false -> ez zv E (EVar j) = bv_unsigned (ev E j).
Proof. intros zv E j H. cbn [ez]. rewrite H. reflexivity. Qed.
Lemma bfa_ez_lo : forall zv E j x, Nat.ltb j (length zv) = true -> nth j zv 0 = x -> ez zv E (EVar j) = x.
Proof. intros zv E j x H <-. cbn [ez]. rewrite H. reflexivity. Qed.
Ltac bfa_ez_pf zv E e :=
  lazymatch e with
  | EAlu ALU_ADD ?a ?b => let pa := bfa_ez_pf zv E a in let pb := bfa_ez_pf zv E b in constr:(bfa_ez_add zv E a b _ _ pa pb)
  | EAlu ALU_SUB ?a ?b => let pa := bfa_ez_pf zv E a in let pb := bfa_ez_pf zv E b in constr:(bfa_ez_sub zv E a b _ _ pa pb)
  | EMd M_MUL ?a ?b => let pa := bfa_ez_pf zv E a in let pb := bfa_ez_pf zv E b in constr:(bfa_ez_mul zv E a b _ _ pa pb)
  | EAlu ALU_SRL ?a (ELit ?sh) => let pa := bfa_ez_pf zv E a in constr:(bfa_ez_srl zv E a sh _ pa)
  | ELit ?z => constr:(bfa_ez_lit zv E z)
  | EVar ?j =>
      lazymatch eval vm_compute in (Nat.ltb j (length zv)) with
      | false => constr:(bfa_ez_hi zv E j eq_refl)
      | true => let x := eval cbv [nth] in (nth j zv 0) in constr:(bfa_ez_lo zv E j x eq_refl eq_refl)
      end
  | _ => constr:(@eq_refl Z (bv_unsigned (edenot E e)) : ez zv E e = bv_unsigned (edenot E e))
  end.
Ltac bfa_cell_gen H W :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                first [ let Hn := fresh "HC" in
                        assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                       [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                          by (eapply (kx_cell_store segs E m pre a W v rest A c0);
                              [ change (pre ++ SE a W v :: rest) with log; exact HLF
                              | exact H | reflexivity
                              | change E with (kE zv xs); kx_estart_z zv
                              | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv
                              | reflexivity | reflexivity | exact I ]);
                        change (pre ++ SE a W v :: rest) with log in Hn;
                        rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
                        let EQ := fresh "HCe" in let pf := bfa_ez_pf zv E v in pose proof pf as EQ; rewrite EQ in Hn; clear EQ;
                        rewrite ?Z_to_bv_bv_unsigned in Hn;
                        clear H; rename Hn into H
                      | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "bfa_cell: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.
Ltac bfa_cell H := first [ bfa_cell_gen H 8%nat | bfa_cell_gen H 4%nat ].
Ltac bfa_rd_atom j S bs HS BY :=
  let H := fresh "HR" in kx_read_eq j H;
  lazymatch type of H with
  | ev ?E j = rdval ?segs ?m (adenot ?E {| a_base := EAlu ALU_ADD (EVar ?i1) (EVar ?i2); a_off := ?off |}) 1 false =>
      lazymatch goal with KXA : forall j, (j < length ?zv)%nat -> ev E j = _ |- _ =>
        let Z1 := fresh "ZR" in
        assert (Z1 : bv_unsigned (ev E j) = Znth (zlen bs + off) bs);
        [ apply (bfa_rd1 segs m S bs E j _ _ HS BY H);
          [ rewrite (bfa_adenot_add2 E i1 i2 off _ _ (KXA i1 ltac:(vm_compute; lia)) (KXA i2 ltac:(vm_compute; lia))) by (cbv [nth]; lia);
            cbv [nth]; f_equal; lia
          | lia ]
        | clear H ]
      end
  end.
Ltac bfa_rd_atom0 j S bs HS BY :=
  let H := fresh "HR" in kx_read_eq j H;
  lazymatch type of H with
  | ev ?E j = rdval ?segs ?m (adenot ?E {| a_base := EVar ?i1; a_off := ?off |}) 1 false =>
      lazymatch goal with KXA : forall j, (j < length ?zv)%nat -> ev E j = _ |- _ =>
        let Z1 := fresh "ZR" in
        assert (Z1 : bv_unsigned (ev E j) = Znth off bs);
        [ apply (bfa_rd1 segs m S bs E j _ _ HS BY H);
          [ rewrite (bfa_adenot_var E i1 off _ (KXA i1 ltac:(vm_compute; lia))) by (cbv [nth]; lia);
            cbv [nth]; f_equal; lia
          | lia ]
        | clear H ]
      end
  end.
Ltac bfa_brute_cell_w H x lo cnt g :=
  lazymatch type of H with
  | rw_cells ?segs ?mm ?A [?C ?e] =>
      let F := eval pattern x in e in
      lazymatch F with
      | ?f x =>
          let BR := fresh "BR" in
          assert (BR : forall r0, lo <= r0 < lo + cnt -> bv_eqb (f r0) (Z_to_bv 64 (g r0)) = true)
            by (apply (brute_range (fun r0 => bv_eqb (f r0) (Z_to_bv 64 (g r0))) lo cnt); vm_compute; reflexivity);
          replace e with (Z_to_bv 64 (g x)) in H by (symmetry; apply bv_eq; apply Z.eqb_eq; rewrite <- bv_eqb_Z; apply BR; lia);
          clear BR
      end
  end.
Ltac bfa_brute_cell H x lo cnt g :=
  lazymatch type of H with
  | rw_cells ?segs ?mm ?A [?C (Z_to_bv 64 ?e)] =>
      let F := eval pattern x in e in
      lazymatch F with
      | ?f x =>
          let BR := fresh "BR" in
          assert (BR : forall r0, lo <= r0 < lo + cnt -> (f r0 =? g r0) = true)
            by (apply (brute_range (fun r0 => f r0 =? g r0) lo cnt); vm_compute; reflexivity);
          replace e with (g x) in H by (symmetry; apply Z.eqb_eq; apply BR; lia);
          clear BR
      end
  end.
Ltac bfa_lb0 j S bs HS BY L0 :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EVar j)) (edenot ?E (ELit 0)) = true =>
      bfa_rd_atom j S bs HS BY;
      cbn [edenot];
      lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
      replace (zlen bs + -1) with (zlen bs - 1) by lia; rewrite L0; reflexivity
  end.
Ltac bfa_lb0g S bs HS BY L0 :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = true => bfa_lb0 j S bs HS BY L0
  end.
Ltac bfa_rd_all S bs HS BY :=
  try bfa_rd_atom0 36%nat S bs HS BY; try bfa_rd_atom 36%nat S bs HS BY; try bfa_rd_atom0 37%nat S bs HS BY; try bfa_rd_atom 37%nat S bs HS BY; try bfa_rd_atom0 38%nat S bs HS BY; try bfa_rd_atom 38%nat S bs HS BY; try bfa_rd_atom0 39%nat S bs HS BY; try bfa_rd_atom 39%nat S bs HS BY; try bfa_rd_atom0 40%nat S bs HS BY; try bfa_rd_atom 40%nat S bs HS BY; try bfa_rd_atom0 41%nat S bs HS BY; try bfa_rd_atom 41%nat S bs HS BY; try bfa_rd_atom0 42%nat S bs HS BY; try bfa_rd_atom 42%nat S bs HS BY; try bfa_rd_atom0 43%nat S bs HS BY; try bfa_rd_atom 43%nat S bs HS BY; try bfa_rd_atom0 44%nat S bs HS BY; try bfa_rd_atom 44%nat S bs HS BY; try bfa_rd_atom0 45%nat S bs HS BY; try bfa_rd_atom 45%nat S bs HS BY; try bfa_rd_atom0 46%nat S bs HS BY; try bfa_rd_atom 46%nat S bs HS BY; try bfa_rd_atom0 47%nat S bs HS BY; try bfa_rd_atom 47%nat S bs HS BY; try bfa_rd_atom0 48%nat S bs HS BY; try bfa_rd_atom 48%nat S bs HS BY; try bfa_rd_atom0 49%nat S bs HS BY; try bfa_rd_atom 49%nat S bs HS BY; try bfa_rd_atom0 50%nat S bs HS BY; try bfa_rd_atom 50%nat S bs HS BY; try bfa_rd_atom0 51%nat S bs HS BY; try bfa_rd_atom 51%nat S bs HS BY; try bfa_rd_atom0 52%nat S bs HS BY; try bfa_rd_atom 52%nat S bs HS BY; try bfa_rd_atom0 53%nat S bs HS BY; try bfa_rd_atom 53%nat S bs HS BY; try bfa_rd_atom0 54%nat S bs HS BY; try bfa_rd_atom 54%nat S bs HS BY; try bfa_rd_atom0 55%nat S bs HS BY; try bfa_rd_atom 55%nat S bs HS BY; try bfa_rd_atom0 56%nat S bs HS BY; try bfa_rd_atom 56%nat S bs HS BY; try bfa_rd_atom0 57%nat S bs HS BY; try bfa_rd_atom 57%nat S bs HS BY; try bfa_rd_atom0 58%nat S bs HS BY; try bfa_rd_atom 58%nat S bs HS BY; try bfa_rd_atom0 59%nat S bs HS BY; try bfa_rd_atom 59%nat S bs HS BY; try bfa_rd_atom0 60%nat S bs HS BY; try bfa_rd_atom 60%nat S bs HS BY.

Definition bit_init_caseA (Q : list Z -> Prop) (E : Z) : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (D S : Z) (bs : list Z) (j : list byte) (lo RLO RHI : Z),
  Q bs ->
  rw_cells bsegs m D [CB 40 j] -> D mod 8 = 0 ->
  bytes_at bsegs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  bv_unsigned sp <= D -> D + 48 <= 2^47 -> (0 < zlen bs -> ablk S (S + zlen bs) /\ S + 8 <= 2^47) ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ABIT_INIT_STACK ->
  mem_inv bsegs m -> artcells m ->
  shclean m D (D + 40) RLO RHI -> unpoisoned m S (S + zlen bs) ->
  rng RNG D 40 -> rng RNG (shad D) 5 -> (0 < zlen bs -> rng RNG S (zlen bs) /\ rng RNG (shad S) (nshad (zlen bs + S mod 8))) ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad RLO) (shad RHI - shad RLO) -> rng_aimg RNG ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen bs) ->
  evtF bsegs RNG (bit_init_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S bs lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 E) fc None m (seg_rom bsegs)).
Ltac bfa_only_cells :=
  repeat match goal with
  | H : _ |- _ => lazymatch type of H with rw_cells _ _ _ _ => fail | _ => clear H end
  end.
Lemma bit_init_c0 : bit_init_caseA (fun bs => zlen bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  rename QC into N0.
  pose proof HS as (HSb0 & HSb1 & _).
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (BS0 : bs = []) by (destruct bs; [reflexivity | unfold zlen in N0; cbn [length] in N0; lia]).
  pose proof ART as (_ & _ & _ & _ & _ & _ & RINI & RLAY & _).
  assert (RFR : rng RNG (bv_unsigned sp - 16) 16) by (eapply rng_sub; [exact RSTK | lia | lia]).
  kx_runFm [asan_memset_entry] 373%nat [KZRange (zlen bs) 0 0; KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj (bv_unsigned sp - 16) 16 D 40] (@nil (Z*Z)) [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8)] [(D, 40)].
  all: try (bfa_mb0_go KSD).
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  clear KC KC0 KC1 KC2 KC3 HD HS FR0.
  bfa_cell FR16. kx_frame KC4. kx_frame HD0.
  kx_frame RGOT. kx_frame RGRIC. kx_frame RMEM. kx_frame RSHB. kx_frame RINI. kx_frame RLAY.
  kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  assert (SHC1 : shclean m1 D (D + 40) RLO RHI).
  { eapply shclean_transport_app; [exact SHC | exact MU | exact WM | | lia].
  apply appW_cons; [right; unfold KHIGH; lia|]. apply appW_cons; [right; unfold KHIGH; lia|]. exact appW_nil. }
  eapply evtF_cut; [ eapply (asan_memset_spec RNG) | ].
  1: exact MI0.
  1: rewrite unsigned_lit by lia; replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia; exact STK16.
  1: rewrite unsigned_lit by lia; lia.
  1: unfold KHIGH; lia.
  1-6: assumption.
  1: rewrite !unsigned_lit by lia; exact HD0.
  1: rewrite !unsigned_lit by lia; right; lia.
  1: rewrite !unsigned_lit by lia; exact (proj2 (proj2 (proj2 SHC1))).
  1: rewrite !unsigned_lit by lia; exact (proj1 SHC1).
  1: rewrite unsigned_lit by lia; lia.
  1: rewrite !unsigned_lit by lia; unfold hull64 in HULL; exact HULL.
  1: exact (proj1 (proj2 (proj2 SHC1))).
  1: exact WIM.
  1: rewrite unsigned_lit by lia; eapply rng_sub; [exact RSTK | lia | lia].
  1: rewrite !unsigned_lit by lia; exact RD.
  1: exact RSH.
  intros ms' PO. unfold asan_memset_post in PO. rewrite !unsigned_lit in PO by lia.
  replace (bv_unsigned sp + -16 - 2208) with (bv_unsigned sp - 2224) in PO by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in PO by lia.
  revert ms' PO. post_call bsegs m1.
  zstep. zstep. zstep. zstep.
  replace (bv_unsigned sp - 16 + 16) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (-72), x13. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split.
  { pose proof (stk_release bsegs x13 lo (bv_unsigned sp - 16) [CB 8 (firstn 8 junkf)] PC KC4 ltac:(lia)) as ST1.
  cbn [cells_size csize] in ST1. replace (bv_unsigned sp - 16 + Z.of_nat (8 + 0)) with (bv_unsigned sp - 16 + 8) in ST1 by lia.
  pose proof (stk_release bsegs x13 lo (bv_unsigned sp - 16 + 8) [C8 ra] ST1 FR16 ltac:(lia)) as ST2.
  cbn [cells_size csize] in ST2. replace (bv_unsigned sp - 16 + 8 + Z.of_nat (8 + 0)) with (bv_unsigned sp) in ST2 by lia. exact ST2. }
  split; [subst bs; apply bytes_at_nil; cbn in HSb1; lia|].
  subst bs. cbv [init_dstream]. split; [reflexivity|].
  eexists. exact POST.
Qed.
Lemma bit_init_cML0 : bit_init_caseA (fun bs => 8 <= zlen bs /\ Znth (zlen bs - 1) bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [NL L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  kx_runFmd (@nil Z) 373%nat [false; false; false; false; true] [KZRange (zlen bs) 8 (2^47); KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4104 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_lb0 46%nat S bs HS BY L0).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  try bfa_cell KC. try bfa_cell KC0. try bfa_cell KC1. try bfa_cell KC2. try bfa_cell KC3. try bfa_cell HD. try bfa_cell FR16. try bfa_cell KC4.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?x10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  replace x10 with (Z_to_bv 64 (- ZSTD_error_GENERIC)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (- ZSTD_error_GENERIC), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_lb0 bs NL L0). split; [reflexivity|].
  assert (HM : rw_cells bsegs m1 D [C8 _; C4 _; CB 4 (firstn 4 (skipn 4 (skipn 8 j))); C8 _; C8 _; C8 _]) by (bfa_only_cells; kx_cells_merge).
  destruct (rw_cells_forget bsegs m1 D _ HM) as (j2 & HJ). exists j2. exact HJ.
Qed.
Lemma bit_init_cM : bit_init_caseA (fun bs => 8 <= zlen bs /\ Znth (zlen bs - 1) bs <> 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [NL L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (LB : 1 <= Znth (zlen bs + -1) bs <= 255).
  { rewrite Forall_forall in BY. assert (IN : In (Znth (zlen bs + -1) bs) bs) by (unfold Znth; apply nth_In; lia). specialize (BY _ IN). split; [|lia]. destruct (Z.eq_dec (Znth (zlen bs + -1) bs) 0); [|lia]. exfalso. apply L0. replace (zlen bs - 1) with (zlen bs + -1) by lia. assumption. }
  replace (zlen bs - 1) with (zlen bs + -1) in L0 by lia.
  kx_runFm (@nil Z) 373%nat [KZRange (zlen bs) 8 (2^47); KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4104 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  bfa_cell KC. bfa_cell KC0. bfa_cell KC2. bfa_cell KC3. bfa_cell HD. bfa_cell FR16.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  bfa_rd_atom 37%nat S bs HS0 BY. bfa_rd_atom 38%nat S bs HS0 BY. bfa_rd_atom 39%nat S bs HS0 BY. bfa_rd_atom 40%nat S bs HS0 BY.
  bfa_rd_atom 41%nat S bs HS0 BY. bfa_rd_atom 42%nat S bs HS0 BY. bfa_rd_atom 43%nat S bs HS0 BY. bfa_rd_atom 44%nat S bs HS0 BY. bfa_rd_atom 46%nat S bs HS0 BY.
  repeat match goal with Z1 : bv_unsigned (ev KXE ?j) = _, H : context [bv_unsigned (ev KXE ?j)] |- _ => rewrite Z1 in H end.
  cbn [edenot] in KC0.
  match goal with Z1 : bv_unsigned (ev KXE 46%nat) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE 46%nat)) in KC0; rewrite Z1 in KC0 end.
  set (lb := Znth (zlen bs + -1) bs) in *.
  bfa_brute_cell KC0 lb 1 255 (fun r0 => 8 - Z.log2 r0).
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (zlen bs), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_main bs NL L0 ltac:(lia)). split; [reflexivity|]. split; [reflexivity|].
  exists (firstn 4 (skipn 4 (skipn 8 j))). unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero].
  subst lb.
  lazymatch type of KC with rw_cells _ _ _ [C8 (Z_to_bv 64 ?e)] =>
  lazymatch goal with |- rw_cells _ _ _ (C8 (Z_to_bv 64 ?e2) :: _) => replace e2 with e by lia end end.
  replace (S + (zlen bs - 8)) with (S + zlen bs + -8) by lia.
  bfa_only_cells; kx_cells_merge.
Qed.
Lemma bit_init_c1L0 : bit_init_caseA (fun bs => zlen bs = 1 /\ Znth (zlen bs - 1) bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N1 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  kx_runFmd (@nil Z) 373%nat [false; false; false; false; true; false; false; false; false; false; false] [KZRange (zlen bs) 1 1; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4097 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_lb0 38%nat S bs HS BY L0).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  try bfa_cell KC. try bfa_cell KC0. try bfa_cell KC1. try bfa_cell KC2. try bfa_cell KC3. try bfa_cell HD. try bfa_cell FR16. try bfa_cell KC4.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?x10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  replace x10 with (Z_to_bv 64 (- ZSTD_error_corruption_detected)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (- ZSTD_error_corruption_detected), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n1_lb0 bs N1 ltac:(rewrite <- L0; f_equal; lia)). split; [reflexivity|].
  assert (HM : rw_cells bsegs m1 D [C8 _; C4 _; CB 4 (firstn 4 (skipn 4 (skipn 8 j))); C8 _; C8 _; C8 _]) by (bfa_only_cells; kx_cells_merge).
  destruct (rw_cells_forget bsegs m1 D _ HM) as (j2 & HJ). exists j2. exact HJ.
Qed.
Lemma bit_init_c1 : bit_init_caseA (fun bs => zlen bs = 1 /\ Znth (zlen bs - 1) bs <> 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N1 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (LB : 1 <= Znth (zlen bs + -1) bs <= 255).
  { rewrite Forall_forall in BY. assert (IN : In (Znth (zlen bs + -1) bs) bs) by (unfold Znth; apply nth_In; lia). specialize (BY _ IN). split; [|lia]. destruct (Z.eq_dec (Znth (zlen bs + -1) bs) 0); [|lia]. exfalso. apply L0. replace (zlen bs - 1) with (zlen bs + -1) by lia. assumption. }
  replace (zlen bs - 1) with (zlen bs + -1) in L0 by lia.
  kx_runFm (@nil Z) 373%nat [KZRange (zlen bs) 1 1; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4097 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_mb0_go KSD).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  bfa_cell KC. bfa_cell KC0. bfa_cell KC2. bfa_cell KC3. bfa_cell HD. bfa_cell FR16.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  bfa_rd_atom0 36%nat S bs HS0 BY.
  repeat match goal with Z1 : bv_unsigned (ev KXE ?j) = _, H : context [bv_unsigned (ev KXE ?j)] |- _ => rewrite Z1 in H end.
  match goal with Z1 : bv_unsigned (ev KXE 36%nat) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE 36%nat)) in KC; rewrite Z1 in KC end.
  bfa_rd_atom 38%nat S bs HS0 BY.
  cbn [edenot] in KC0.
  match goal with Z1 : bv_unsigned (ev KXE 38%nat) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE 38%nat)) in KC0; rewrite Z1 in KC0 end.
  replace (zlen bs + -1) with 0 in * by lia.
  set (lb := Znth 0 bs) in *.
  bfa_brute_cell_w KC0 lb 1 255 (fun r0 => 64 - Z.log2 r0).
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists 1, m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n1 bs N1 ltac:(subst lb; exact L0) ltac:(lia)). split; [lia|]. split; [reflexivity|].
  exists (firstn 4 (skipn 4 (skipn 8 j))). unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero].
  replace (S + 0) with S by lia.
  bfa_only_cells; kx_cells_merge.
Qed.
Lemma bit_init_c2L0 : bit_init_caseA (fun bs => zlen bs = 2 /\ Znth (zlen bs - 1) bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N2 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  kx_runFmd (@nil Z) 373%nat [false; false; false; false; false; true; false; false; false; false; false; false] [KZRange (zlen bs) 2 2; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4098 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_lb0 41%nat S bs HS BY L0).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  try bfa_cell KC. try bfa_cell KC0. try bfa_cell KC1. try bfa_cell KC2. try bfa_cell KC3. try bfa_cell HD. try bfa_cell FR16. try bfa_cell KC4.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?x10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  replace x10 with (Z_to_bv 64 (- ZSTD_error_corruption_detected)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (- ZSTD_error_corruption_detected), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n2_lb0 bs N2 ltac:(rewrite <- L0; f_equal; lia)). split; [reflexivity|].
  assert (HM : rw_cells bsegs m1 D [C8 _; C4 _; CB 4 (firstn 4 (skipn 4 (skipn 8 j))); C8 _; C8 _; C8 _]) by (bfa_only_cells; kx_cells_merge).
  destruct (rw_cells_forget bsegs m1 D _ HM) as (j2 & HJ). exists j2. exact HJ.
Qed.
Lemma bit_init_c2 : bit_init_caseA (fun bs => zlen bs = 2 /\ Znth (zlen bs - 1) bs <> 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N2 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (LB : 1 <= Znth (zlen bs + -1) bs <= 255).
  { rewrite Forall_forall in BY. assert (IN : In (Znth (zlen bs + -1) bs) bs) by (unfold Znth; apply nth_In; lia). specialize (BY _ IN). split; [|lia]. destruct (Z.eq_dec (Znth (zlen bs + -1) bs) 0); [|lia]. exfalso. apply L0. replace (zlen bs - 1) with (zlen bs + -1) by lia. assumption. }
  replace (zlen bs - 1) with (zlen bs + -1) in L0 by lia.
  kx_runFm (@nil Z) 373%nat [KZRange (zlen bs) 2 2; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4098 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  bfa_cell KC. bfa_cell KC0. bfa_cell KC2. bfa_cell KC3. bfa_cell HD. bfa_cell FR16.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  bfa_rd_atom0 36%nat S bs HS0 BY. bfa_rd_atom0 39%nat S bs HS0 BY. bfa_rd_atom 41%nat S bs HS0 BY.
  repeat match goal with Z1 : bv_unsigned (ev KXE ?j) = _, H : context [bv_unsigned (ev KXE ?j)] |- _ => rewrite Z1 in H end.
  cbn [edenot] in KC0.
  match goal with Z1 : bv_unsigned (ev KXE 41%nat) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE 41%nat)) in KC0; rewrite Z1 in KC0 end.
  replace (zlen bs + -1) with 1 in * by lia.
  set (lb := Znth 1 bs) in *.
  bfa_brute_cell_w KC0 lb 1 255 (fun r0 => 56 - Z.log2 r0).
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists 2, m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n2 bs N2 ltac:(subst lb; exact L0) ltac:(lia)). split; [lia|]. split; [reflexivity|].
  exists (firstn 4 (skipn 4 (skipn 8 j))). unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero].
  replace (S + 0) with S by lia.
  bfa_only_cells; kx_cells_merge.
Qed.
Lemma bit_init_c3L0 : bit_init_caseA (fun bs => zlen bs = 3 /\ Znth (zlen bs - 1) bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N3 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  kx_runFmd (@nil Z) 450%nat [false; false; false; false; false; false; true; false; false; false; false; false; false] [KZRange (zlen bs) 3 3; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4099 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_lb0g S bs HS BY L0).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  try bfa_cell KC. try bfa_cell KC0. try bfa_cell KC1. try bfa_cell KC2. try bfa_cell KC3. try bfa_cell HD. try bfa_cell FR16. try bfa_cell KC4.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?x10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  replace x10 with (Z_to_bv 64 (- ZSTD_error_corruption_detected)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (- ZSTD_error_corruption_detected), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n3_lb0 bs N3 ltac:(rewrite <- L0; f_equal; lia)). split; [reflexivity|].
  assert (HM : rw_cells bsegs m1 D [C8 _; C4 _; CB 4 (firstn 4 (skipn 4 (skipn 8 j))); C8 _; C8 _; C8 _]) by (bfa_only_cells; kx_cells_merge).
  destruct (rw_cells_forget bsegs m1 D _ HM) as (j2 & HJ). exists j2. exact HJ.
Qed.
Lemma bit_init_c3 : bit_init_caseA (fun bs => zlen bs = 3 /\ Znth (zlen bs - 1) bs <> 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N3 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (LB : 1 <= Znth (zlen bs + -1) bs <= 255).
  { rewrite Forall_forall in BY. assert (IN : In (Znth (zlen bs + -1) bs) bs) by (unfold Znth; apply nth_In; lia). specialize (BY _ IN). split; [|lia]. destruct (Z.eq_dec (Znth (zlen bs + -1) bs) 0); [|lia]. exfalso. apply L0. replace (zlen bs - 1) with (zlen bs + -1) by lia. assumption. }
  replace (zlen bs - 1) with (zlen bs + -1) in L0 by lia.
  kx_runFm (@nil Z) 450%nat [KZRange (zlen bs) 3 3; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4099 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  bfa_cell KC. bfa_cell KC0. bfa_cell KC2. bfa_cell KC3. bfa_cell HD. bfa_cell FR16.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  bfa_rd_all S bs HS0 BY.
  repeat match goal with Z1 : bv_unsigned (ev KXE ?j) = _, H : context [bv_unsigned (ev KXE ?j)] |- _ => rewrite Z1 in H end.
  cbn [edenot] in KC0.
  match goal with Z1 : bv_unsigned (ev KXE ?j) = Znth (zlen bs + -1) bs |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE j)) in KC0; rewrite Z1 in KC0 end.
  replace (zlen bs + -1) with 2 in * by lia.
  set (lb := Znth 2 bs) in *.
  bfa_brute_cell_w KC0 lb 1 255 (fun r0 => 48 - Z.log2 r0).
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists 3, m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  lazymatch type of KC with rw_cells _ _ _ [C8 (Z_to_bv 64 ?c)] => rewrite (bfa_init_n3 bs c N3 ltac:(subst lb; exact L0) ltac:(lia) ltac:(subst lb; lia)) end. split; [lia|]. split; [reflexivity|].
  exists (firstn 4 (skipn 4 (skipn 8 j))). unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero].
  replace (S + 0) with S by lia.
  bfa_only_cells; kx_cells_merge.
Qed.
Lemma bit_init_c4L0 : bit_init_caseA (fun bs => zlen bs = 4 /\ Znth (zlen bs - 1) bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N4 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  kx_runFmd (@nil Z) 450%nat [false; false; false; false; false; false; false; true; false; false; false; false; false; false] [KZRange (zlen bs) 4 4; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4100 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_lb0g S bs HS BY L0).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  try bfa_cell KC. try bfa_cell KC0. try bfa_cell KC1. try bfa_cell KC2. try bfa_cell KC3. try bfa_cell HD. try bfa_cell FR16. try bfa_cell KC4.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?x10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  replace x10 with (Z_to_bv 64 (- ZSTD_error_corruption_detected)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (- ZSTD_error_corruption_detected), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n4_lb0 bs N4 ltac:(rewrite <- L0; f_equal; lia)). split; [reflexivity|].
  assert (HM : rw_cells bsegs m1 D [C8 _; C4 _; CB 4 (firstn 4 (skipn 4 (skipn 8 j))); C8 _; C8 _; C8 _]) by (bfa_only_cells; kx_cells_merge).
  destruct (rw_cells_forget bsegs m1 D _ HM) as (j2 & HJ). exists j2. exact HJ.
Qed.
Lemma bit_init_c4 : bit_init_caseA (fun bs => zlen bs = 4 /\ Znth (zlen bs - 1) bs <> 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N4 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (LB : 1 <= Znth (zlen bs + -1) bs <= 255).
  { rewrite Forall_forall in BY. assert (IN : In (Znth (zlen bs + -1) bs) bs) by (unfold Znth; apply nth_In; lia). specialize (BY _ IN). split; [|lia]. destruct (Z.eq_dec (Znth (zlen bs + -1) bs) 0); [|lia]. exfalso. apply L0. replace (zlen bs - 1) with (zlen bs + -1) by lia. assumption. }
  replace (zlen bs - 1) with (zlen bs + -1) in L0 by lia.
  kx_runFm (@nil Z) 450%nat [KZRange (zlen bs) 4 4; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4100 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  bfa_cell KC. bfa_cell KC0. bfa_cell KC2. bfa_cell KC3. bfa_cell HD. bfa_cell FR16.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  bfa_rd_all S bs HS0 BY.
  repeat match goal with Z1 : bv_unsigned (ev KXE ?j) = _, H : context [bv_unsigned (ev KXE ?j)] |- _ => rewrite Z1 in H end.
  cbn [edenot] in KC0.
  match goal with Z1 : bv_unsigned (ev KXE ?j) = Znth (zlen bs + -1) bs |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE j)) in KC0; rewrite Z1 in KC0 end.
  replace (zlen bs + -1) with 3 in * by lia.
  set (lb := Znth 3 bs) in *.
  bfa_brute_cell_w KC0 lb 1 255 (fun r0 => 40 - Z.log2 r0).
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists 4, m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  lazymatch type of KC with rw_cells _ _ _ [C8 (Z_to_bv 64 ?c)] => rewrite (bfa_init_n4 bs c N4 ltac:(subst lb; exact L0) ltac:(lia) ltac:(subst lb; lia)) end. split; [lia|]. split; [reflexivity|].
  exists (firstn 4 (skipn 4 (skipn 8 j))). unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero].
  replace (S + 0) with S by lia.
  bfa_only_cells; kx_cells_merge.
Qed.
Lemma bit_init_c5L0 : bit_init_caseA (fun bs => zlen bs = 5 /\ Znth (zlen bs - 1) bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N5 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  kx_runFmd (@nil Z) 450%nat [false; false; false; false; false; false; false; false; true; false; false; false; false; false; false] [KZRange (zlen bs) 5 5; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4101 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_lb0g S bs HS BY L0).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  try bfa_cell KC. try bfa_cell KC0. try bfa_cell KC1. try bfa_cell KC2. try bfa_cell KC3. try bfa_cell HD. try bfa_cell FR16. try bfa_cell KC4.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?x10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  replace x10 with (Z_to_bv 64 (- ZSTD_error_corruption_detected)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (- ZSTD_error_corruption_detected), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n5_lb0 bs N5 ltac:(rewrite <- L0; f_equal; lia)). split; [reflexivity|].
  assert (HM : rw_cells bsegs m1 D [C8 _; C4 _; CB 4 (firstn 4 (skipn 4 (skipn 8 j))); C8 _; C8 _; C8 _]) by (bfa_only_cells; kx_cells_merge).
  destruct (rw_cells_forget bsegs m1 D _ HM) as (j2 & HJ). exists j2. exact HJ.
Qed.
Lemma bit_init_c5 : bit_init_caseA (fun bs => zlen bs = 5 /\ Znth (zlen bs - 1) bs <> 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N5 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (LB : 1 <= Znth (zlen bs + -1) bs <= 255).
  { rewrite Forall_forall in BY. assert (IN : In (Znth (zlen bs + -1) bs) bs) by (unfold Znth; apply nth_In; lia). specialize (BY _ IN). split; [|lia]. destruct (Z.eq_dec (Znth (zlen bs + -1) bs) 0); [|lia]. exfalso. apply L0. replace (zlen bs - 1) with (zlen bs + -1) by lia. assumption. }
  replace (zlen bs - 1) with (zlen bs + -1) in L0 by lia.
  kx_runFm (@nil Z) 450%nat [KZRange (zlen bs) 5 5; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4101 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  bfa_cell KC. bfa_cell KC0. bfa_cell KC2. bfa_cell KC3. bfa_cell HD. bfa_cell FR16.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  bfa_rd_all S bs HS0 BY.
  repeat match goal with Z1 : bv_unsigned (ev KXE ?j) = _, H : context [bv_unsigned (ev KXE ?j)] |- _ => rewrite Z1 in H end.
  cbn [edenot] in KC0.
  match goal with Z1 : bv_unsigned (ev KXE ?j) = Znth (zlen bs + -1) bs |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE j)) in KC0; rewrite Z1 in KC0 end.
  replace (zlen bs + -1) with 4 in * by lia.
  set (lb := Znth 4 bs) in *.
  bfa_brute_cell_w KC0 lb 1 255 (fun r0 => 32 - Z.log2 r0).
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists 5, m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  lazymatch type of KC with rw_cells _ _ _ [C8 (Z_to_bv 64 ?c)] => rewrite (bfa_init_n5 bs c N5 ltac:(subst lb; exact L0) ltac:(lia) ltac:(subst lb; lia)) end. split; [lia|]. split; [reflexivity|].
  exists (firstn 4 (skipn 4 (skipn 8 j))). unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero].
  replace (S + 0) with S by lia.
  bfa_only_cells; kx_cells_merge.
Qed.
Lemma bit_init_c6L0 : bit_init_caseA (fun bs => zlen bs = 6 /\ Znth (zlen bs - 1) bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N6 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  kx_runFmd (@nil Z) 450%nat [false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false] [KZRange (zlen bs) 6 6; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4102 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_lb0g S bs HS BY L0).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  try bfa_cell KC. try bfa_cell KC0. try bfa_cell KC1. try bfa_cell KC2. try bfa_cell KC3. try bfa_cell HD. try bfa_cell FR16. try bfa_cell KC4.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?x10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  replace x10 with (Z_to_bv 64 (- ZSTD_error_corruption_detected)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (- ZSTD_error_corruption_detected), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n6_lb0 bs N6 ltac:(rewrite <- L0; f_equal; lia)). split; [reflexivity|].
  assert (HM : rw_cells bsegs m1 D [C8 _; C4 _; CB 4 (firstn 4 (skipn 4 (skipn 8 j))); C8 _; C8 _; C8 _]) by (bfa_only_cells; kx_cells_merge).
  destruct (rw_cells_forget bsegs m1 D _ HM) as (j2 & HJ). exists j2. exact HJ.
Qed.
Lemma bit_init_c6 : bit_init_caseA (fun bs => zlen bs = 6 /\ Znth (zlen bs - 1) bs <> 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N6 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (LB : 1 <= Znth (zlen bs + -1) bs <= 255).
  { rewrite Forall_forall in BY. assert (IN : In (Znth (zlen bs + -1) bs) bs) by (unfold Znth; apply nth_In; lia). specialize (BY _ IN). split; [|lia]. destruct (Z.eq_dec (Znth (zlen bs + -1) bs) 0); [|lia]. exfalso. apply L0. replace (zlen bs - 1) with (zlen bs + -1) by lia. assumption. }
  replace (zlen bs - 1) with (zlen bs + -1) in L0 by lia.
  kx_runFm (@nil Z) 450%nat [KZRange (zlen bs) 6 6; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4102 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  bfa_cell KC. bfa_cell KC0. bfa_cell KC2. bfa_cell KC3. bfa_cell HD. bfa_cell FR16.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  bfa_rd_all S bs HS0 BY.
  repeat match goal with Z1 : bv_unsigned (ev KXE ?j) = _, H : context [bv_unsigned (ev KXE ?j)] |- _ => rewrite Z1 in H end.
  cbn [edenot] in KC0.
  match goal with Z1 : bv_unsigned (ev KXE ?j) = Znth (zlen bs + -1) bs |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE j)) in KC0; rewrite Z1 in KC0 end.
  replace (zlen bs + -1) with 5 in * by lia.
  set (lb := Znth 5 bs) in *.
  bfa_brute_cell_w KC0 lb 1 255 (fun r0 => 24 - Z.log2 r0).
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists 6, m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  lazymatch type of KC with rw_cells _ _ _ [C8 (Z_to_bv 64 ?c)] => rewrite (bfa_init_n6 bs c N6 ltac:(subst lb; exact L0) ltac:(lia) ltac:(subst lb; lia)) end. split; [lia|]. split; [reflexivity|].
  exists (firstn 4 (skipn 4 (skipn 8 j))). unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero].
  replace (S + 0) with S by lia.
  bfa_only_cells; kx_cells_merge.
Qed.
Lemma bit_init_c7L0 : bit_init_caseA (fun bs => zlen bs = 7 /\ Znth (zlen bs - 1) bs = 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N7 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  kx_runFmd (@nil Z) 450%nat [false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false] [KZRange (zlen bs) 7 7; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4103 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (bfa_lb0g S bs HS BY L0).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  try bfa_cell KC. try bfa_cell KC0. try bfa_cell KC1. try bfa_cell KC2. try bfa_cell KC3. try bfa_cell HD. try bfa_cell FR16. try bfa_cell KC4.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?x10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  replace x10 with (Z_to_bv 64 (- ZSTD_error_corruption_detected)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists (- ZSTD_error_corruption_detected), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  rewrite (bfa_init_n7_lb0 bs N7 ltac:(rewrite <- L0; f_equal; lia)). split; [reflexivity|].
  assert (HM : rw_cells bsegs m1 D [C8 _; C4 _; CB 4 (firstn 4 (skipn 4 (skipn 8 j))); C8 _; C8 _; C8 _]) by (bfa_only_cells; kx_cells_merge).
  destruct (rw_cells_forget bsegs m1 D _ HM) as (j2 & HJ). exists j2. exact HJ.
Qed.
Lemma bit_init_c7 : bit_init_caseA (fun bs => zlen bs = 7 /\ Znth (zlen bs - 1) bs <> 0) ABIT_INIT_D.
Proof.
  unfold bit_init_caseA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI QC
    HD D8 HS BY SPD DH BSS STK LOA LOS MI ART SHC US RD RDs RSS RSTK RSH WIM -> -> ->.
  destruct QC as [N7 L0].
  destruct (BSS ltac:(lia)) as [BS S8]. destruct (RSS ltac:(lia)) as [RS RSs].
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof SHC as (UD & HULL & WRSH & APB).
  unfold ABIT_INIT_STACK in *.
  unfold nshad in RSs.
  pose proof (bfa_kshz_unp m D 40 UD D8 eq_refl) as KSD. unfold ASHOFF in KSD. pose proof RDs as RDs2. unfold shad, ASHOFF in RDs2.
  assert (SB : 4096 <= S /\ S + zlen bs <= ATOP) by (unfold ablk, AIMG_HI, KLS in BS; lia).
  destruct (stk_carve bsegs m lo (bv_unsigned sp) 16 STK ltac:(lia)) as (STK16 & junkf & FR16). change (Z.of_nat 16) with 16 in FR16.
  pose proof HD as HD0. pose proof FR16 as FR0.
  apply (rw_cells_split_CB bsegs m D [] 40 j [] [8;4;4;8;8;8]%nat) in HD; [| reflexivity]. cbn [app mk_CB_cells] in HD. kx_cells_split HD.
  apply (rw_cells_split_CB bsegs m (bv_unsigned sp - 16) [] 16 junkf [] [8;8]%nat) in FR16; [| reflexivity]. cbn [app mk_CB_cells] in FR16. kx_cells_split FR16.
  assert (LB : 1 <= Znth (zlen bs + -1) bs <= 255).
  { rewrite Forall_forall in BY. assert (IN : In (Znth (zlen bs + -1) bs) bs) by (unfold Znth; apply nth_In; lia). specialize (BY _ IN). split; [|lia]. destruct (Z.eq_dec (Znth (zlen bs + -1) bs) 0); [|lia]. exfalso. apply L0. replace (zlen bs - 1) with (zlen bs + -1) by lia. assumption. }
  replace (zlen bs - 1) with (zlen bs + -1) in L0 by lia.
  kx_runFm (@nil Z) 450%nat [KZRange (zlen bs) 7 7; KZImg 134548 134676; KZRange S 4096 (2^47 - 8); KZRange (S + zlen bs) 4103 (2^47); KZRange D 0x7fff7f8018c0 (2^47 - 48); KZAlign D 8; KZRange (bv_unsigned sp) 0x7fff7f8018c0 (2^47); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (bv_unsigned sp - 16) 16; KZWr D 40; KZDisj S (zlen bs) D 40; KZDisj S (zlen bs) (bv_unsigned sp - 16) 16; KZDisj (bv_unsigned sp - 16) 16 D 40] [(S, zlen bs)] [(D, 40); (bv_unsigned sp - 16, 16); (0xb2128, 8); (0xba2f8, 8); (S, zlen bs)] [(S, zlen bs); (D, 40)].
  all: try (bfa_mb0_go KSD).
  all: try (lazymatch goal with |- accP _ _ _ => kx_asan KSD end).
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
  bfa_rd_atom j S bs HS BY; cbn [edenot];
  lazymatch goal with Z1 : bv_unsigned (ev E j) = _ |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev E j)), Z1 end;
  unfold branch_taken; rewrite bv_eqb_Z, !unsigned_lit by lia; apply Z.eqb_neq; lia end).
  pose proof HS as HS0. clear HD0 FR0.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 40)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  bfa_cell KC. bfa_cell KC0. bfa_cell KC2. bfa_cell KC3. bfa_cell HD. bfa_cell FR16.
  kx_frame KC1. kx_frame KC4. kx_frame HS. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  bfa_rd_all S bs HS0 BY.
  repeat match goal with Z1 : bv_unsigned (ev KXE ?j) = _, H : context [bv_unsigned (ev KXE ?j)] |- _ => rewrite Z1 in H end.
  cbn [edenot] in KC0.
  match goal with Z1 : bv_unsigned (ev KXE ?j) = Znth (zlen bs + -1) bs |- _ => rewrite <- (Z_to_bv_bv_unsigned (ev KXE j)) in KC0; rewrite Z1 in KC0 end.
  replace (zlen bs + -1) with 6 in * by lia.
  set (lb := Znth 6 bs) in *.
  bfa_brute_cell_w KC0 lb 1 255 (fun r0 => 16 - Z.log2 r0).
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold bit_init_postA.
  do 14 eexists. exists 7, m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact STK|]. split; [exact HS|].
  lazymatch type of KC with rw_cells _ _ _ [C8 (Z_to_bv 64 ?c)] => rewrite (bfa_init_n7 bs c N7 ltac:(subst lb; exact L0) ltac:(lia) ltac:(subst lb; lia)) end. split; [lia|]. split; [reflexivity|].
  exists (firstn 4 (skipn 4 (skipn 8 j))). unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero].
  replace (S + 0) with S by lia.
  bfa_only_cells; kx_cells_merge.
Qed.
Ltac bfa_case C :=
  let H := fresh "C" in pose proof C as H; unfold bit_init_caseA in H; apply H; clear H; cbv beta.
Lemma bit_init_proofAD : bit_init_stmtA ABIT_INIT_D.
Proof.
  unfold bit_init_stmtA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S bs j lo RLO RHI.
  destruct (Z_lt_le_dec (zlen bs) 8) as [NS|NL].
  2: { destruct (Z.eq_dec (Znth (zlen bs - 1) bs) 0) as [L0|L0];
       [bfa_case bit_init_cML0 | bfa_case bit_init_cM]; split; assumption. }
  destruct (Z.eq_dec (zlen bs) 0) as [N0|N0]. { bfa_case bit_init_c0; assumption. }
  assert (KS : zlen bs = 1 \/ zlen bs = 2 \/ zlen bs = 3 \/ zlen bs = 4 \/ zlen bs = 5 \/ zlen bs = 6 \/ zlen bs = 7) by lia.
  destruct (Z.eq_dec (Znth (zlen bs - 1) bs) 0) as [L0|L0].
  - destruct KS as [K|[K|[K|[K|[K|[K|K]]]]]];
      [bfa_case bit_init_c1L0 | bfa_case bit_init_c2L0 | bfa_case bit_init_c3L0 | bfa_case bit_init_c4L0
      | bfa_case bit_init_c5L0 | bfa_case bit_init_c6L0 | bfa_case bit_init_c7L0]; split; assumption.
  - destruct KS as [K|[K|[K|[K|[K|[K|K]]]]]];
      [bfa_case bit_init_c1 | bfa_case bit_init_c2 | bfa_case bit_init_c3 | bfa_case bit_init_c4
      | bfa_case bit_init_c5 | bfa_case bit_init_c6 | bfa_case bit_init_c7]; split; assumption.
Qed.
End CANSEC1.
