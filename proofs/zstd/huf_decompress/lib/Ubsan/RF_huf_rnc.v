(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_rnc_base RF_huf_rnc_base2 RF_huf_rnc_mem RF_huf_rnc_body.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_rnc () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:map_repeatK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_boundK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC56Stdlib6ZArith6BinInt1Z3addK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsK47Corelib4Init9Datatypes3nat01I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface>fse_readh_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5rdctx01I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5c_bufC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base6c_msv0C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5c_rt0C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_SPC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_loC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_NCC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5c_BUFC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base6c_MSVPC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5c_TLPC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5rd_okC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_rnc_base2=rd_body_posthC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_body8rd_body8C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_raC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_gpC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_tpC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s0C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s1C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s2C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s3C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s4C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s5C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s6C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s7C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s8C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_s9C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5c_s10C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5c_s11C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base3c_mC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base3c_FC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4c_fcI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;read_ncountC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base4rd_WK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic6eq_symI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountAread_ncount_body8K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02K47Corelib4Init9Datatypes4prod01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_monoI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_rnc_base29rd_res_okC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega3Op205I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02c5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_rnc6boundsI5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_rnc_base5rdctx00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface>FSE_READ_STACKI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3subC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init3Nat3addK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02C46Stdlib5Lists4List=repeat_lengthC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K4ELinuxProcessSemantics5Riscv3Sem4core01C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeK46Stdlib9micromega=RingMicromega5Psatz07K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib3Tac>rw_cells_mergeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Tac7sum_natC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC46Stdlib9micromega;ZifyClasses;rew_iff_revc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_rnc8pad_tailC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rnc_mem?rd_rw_cells_appC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rnc_mem?rd_memcpyZ_postC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rnc_mem?rd_memcpy_specZC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC46Stdlib5Lists4List:Forall_appC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List;repeat_specK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C47Corelib4Init5Logic5proj2C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List7map_appC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas@Forall_all_bytesC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas9all_bytesC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSoundGread_ncount_body8_totalC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_rnc_base27err_regC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC56Stdlib6ZArith6BinInt1Z8land_0_lC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_16C5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeK46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4wsumK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I46Stdlib5Lists4List6Exists00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00c5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_rnc<rd_top_smallc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_rnc7rd_top8C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface=PFSE_READNC_BC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface>fse_readh_stmt".
Import ListNotations.
Open Scope Z_scope.

Section Top.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem).
  Variables (SPV NC MSVP TLP BUF : Z) (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word).
  Hypothesis ARR : u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)).
  Hypothesis HMSV : rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)].
  Hypothesis HTL : rw_cells usegs m TLP [C4 tl0].
  Hypothesis HBUF : bytes_at usegs m BUF (map (Z_to_bv 8) buf).
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) buf.
  Hypothesis HMSV1 : msv0 + 1 <= zlen rt0.
  Hypothesis HM0 : 0 <= msv0 <= 255.
  Hypothesis HLEN : zlen buf <= 65536.
  Hypothesis HNP : 0 < NC.
  Hypothesis HNA : NC mod 2 = 0.
  Hypothesis HVP : 0 < MSVP.
  Hypothesis HVA : MSVP mod 4 = 0.
  Hypothesis HTP : 0 < TLP.
  Hypothesis HTA : TLP mod 4 = 0.
  Hypothesis HBP : 0 < BUF.
  Hypothesis HSLACK : BUF + zlen buf + 8 <= 2^64.
  Hypothesis ST : stk usegs m lo SPV.
  Hypothesis LO : lo <= SPV - FSE_READ_STACK.
  Hypothesis RSP : 0 <= SPV < 2^64.
  Hypothesis SNS : NC + 2 * zlen rt0 <= lo \/ SPV <= NC.
  Hypothesis SMS : MSVP + 4 <= lo \/ SPV <= MSVP.
  Hypothesis STS : TLP + 4 <= lo \/ SPV <= TLP.
  Hypothesis SBS : BUF + zlen buf <= lo \/ SPV <= BUF.
  Hypothesis SNM : NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC.
  Hypothesis SNT : NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC.
  Hypothesis SNB : NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC.
  Hypothesis SMT : MSVP + 4 <= TLP \/ TLP + 4 <= MSVP.
  Hypothesis SMB : MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP.
  Hypothesis STB : TLP + 4 <= BUF \/ BUF + zlen buf <= TLP.
  Hypothesis MI : mem_inv usegs m.

  Notation POST := (fse_readh_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 msv0 buf lo m).

  Lemma bounds : 0 <= lo /\ (0 <= NC /\ NC + 2 * zlen rt0 <= 2^64) /\ (0 <= MSVP /\ MSVP + 4 <= 2^64) /\ (0 <= TLP /\ TLP + 4 <= 2^64).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rnc ()) ["Top"] "h02B0h17__sat13h24__x1h31ah41Hh52H0h67__arithh77__sat12h84cstrh95cstr0h:4__p1h;4__ffh<8__varmaph=5__with>2B1h?1nh@1xhA2HahB4__x2hC2B2hD2B3hE2L0hF2_HhG1bhH1mhI1shJ1yp&0p;1p;2p;3p;4p;5p;6p;<p;Bp;7p;8p10000p4p710g000MR0p4p710p8p1000ip4p7210p1001Up4p710R1p8g0023R2p4p7210P1p8p1002Rp4p7210P1p8g0031j1:Tg003Vj1ETg0044j2`Tg004QR1j22Tg004mj2?Tg005IR3j20Tg005dj1UTg006Bj1STg006ej1bTg007Gj1NTg0086j3]Tg0093j1LTg009Uj37Tg009ok101Tg00:Hk300Tg00;8j2|Tg00;Zj2xTg00<4j2>Tg00<TR4j13Tg00=4R5j2DTg00=Qj1jj2^Tg00>7j4hTg00>Sj1gTg00?Nj5fTg00@Fj1<Tg00@ej2BTg00A<j1aTP0j6TTP2j4_Tg00B>R2j24Tg00B[j1MTg00CPj1OTg00D0j3PTg00DPj5QTg00ELj1RTg00FEj28Tg00F_j3KTg00GEk103Tg00Gck402Tg00HFj6@Tg00Hoj4ATg00IVj1[Tg00J;j2zTg00Jcj3wTg00KGj2uTg00Khj1sTg00LHj2XTg00Lfj1pTg00MDj1oTg00Moj2GTg00NRj2WTg00O5j2lTg00OWj2kTg00PCj3mTg00Pbj4nTg00QTj1iTg00R2j4qTg00RPj3rTg00S3j3YTg00SVj3tTg00T9j49Tg00TTl<vTg00U9lBZTg00U_l<eTg00VDj4yTg00Voj7dTg00WSj8}Tg00X7j6~Tg00X[j7cTg00Y?R0f0R6'2p=1f2R7f1R8'4/26p=;f3R91478/26'0p=6g00Y]R:/86p=5g00Z;R;P:P:P:P4P4f5R<f4R=P9P7P8P6M<vp=\P:P:P:P:P:P:P2P6P8P7P2P9P=P<f6R2f7R>f8f9MBZp=IP:P:P1P>P1P2P<P=P9P7P8P6M<ep=HP;P;P;P:P:P:g00ZZP4P4P4P5g00[:P<P=P9P7P8P6MBZp={P:P8g00[]P6Cyp=JP8g00\DR<g00\cR5P5g00]CR4P6g00]cFdp=FP9P<P5P5P4P7P8P6G}p==P8P<P5P5P4P6E~p=VP7P<P5P5P4P8P6Fcp=Cp,2STp,2loR<#1R1p,3SPVR>g00^CR?#:R@#ERA%:@RB#:RC#:#:#:RD#ERE'`RF'212<61?6>'0%UC#SRC#bRGg00^hRHp,1mRI%N83]%LC37$01%N7:00HI1|C657GXGC,xC'0[^3:'0RG'0P3P1PGp,2NCRJ#1RKp,3rt0RL,>:RM#3RN,DARO=;JFRP'0RQp,4MSVPRR#1RS%EBRB=;RFRT'0RUp,3TLPRV#1RWA;VBFRX'0RY'0RZ'0R[,01P6PHPIPJP:%UDRD#SR\%jDR]PLChR^#gR_p,3ARRDfPKPJ1>C_R_#3PFC6P;P_PKPJ%36R_PFC6X?;P6g00_]#<#<RC1>\^R`'BRa%a^ETPKPJ%3aPFC6P;P`PKPJ1BC6#3PFC6X?;P6PMP:P\P]PLC_ET1BCMRL#3R],4JR\/2FR`,0KRaPHPIPRg00`<R^p,4msv0,^D#M%O^Rb3PRcp,4HMSVDQPSPR%Rc#3PFC6PHPIPVp,3tl0#M=P^bRbp,3HTLDQPWPV%Rb#3PFC6P1P[%<C#<R[#3Rb,4VR^/2FRI,0WPYPWPIPWP6X@:RIPBO1RH,4VRc/2Fp-0Rd/8WA7dWWe9KWWPI1286$03XJ:X@:ReP^PcPIPIPIP:P:g00a11486H02#5XH:X?:RcPVPV%5VPbPHPIPI%5_X@;R;P[PB%5BE\R[M:IPFPF%5FA7:FFeR_GHE@P6CAR^PY14RbRf/2FRg,0SPUPSPgPS14RHRg/2F18dSA7dSSe9KSSPIPePfPgPIPIPIPcPRPR%5RPbPHP[M:IPFPFP_GHE@P7CAR[PUPaPQPKP`PKPIPOO1R`,4JRa/2F18dKA7dKKe9KKKPIPeP\PaPIPIPIPcPJPJ%5JP]P`PIPIP;PLPOPCPA%5APMPN%5NE{E\M:IPFPFP_GHE@P=CAR_PQ%[MRM%1NRCp,3buf,>:RO#[RL%3O#1RO1zAER;1?0ARI%1E1?0F[R`[R]%1ARcg00aURaAwAE8UWARE%1F\a^AcRcp,3RSPRa%1>R\1?>FR>'0ReP3P\P>P1P6P2g00b11u0A'8PIeO1RIP`g00bWR2#ORH%s2R21X:8Rb%p:Rg%o:Rf1G:01W:?R?'J,FfRh%L5R5PhC=1lf4R4P6P7g00cCRig00ccRj'81k67=7ijdAm:08CnR0b;b<b=X2:%16Rj%18Ri[^2:P6P<fDO2b6b1X5>X4\P8P6O2n2001000000120000000b3b7b1b9b8b0b0b0PQPZPKPPP^PYP[PUP_PQPMPCPLPOP;P]PEPcPaPeP3P\P>PKP6PIP`PHP2PbPgPf1Vf9R99CfhP5PhC=P4P0b;b<b=X2:X:dRh10j8Pi[^2:^:dRiP6PPPJf;RjO3b6b1X5>X4\P8P6O2n2001000000120000000b3b7b1b9b8b0b0b0P^PYP[PUP_PQPMPCPLPOP;P]PEPcPaPeP3P\P>PPP6PIP`PHP2P:1X:7P8%i:CqPgPf1Vf=1G:AR=1W:@5r:9Y:?At:=DR='J,FfRD5CfP5PDC=P4P0b;b<b=X2:XB:X:dP7P61DA8PFC61DA7=;8F[^2:^B:^:dP6PKPNPJPjO4b6b1X5>X4\P8P6O2n2001000000121000000b3b7b1b9b8b0b0b0C9PUPYPSPTP^PYP[PUP_PQPMPCPLPOP;P]PEPcPaPeP3P\P>PSP6PIP`PhPiP6PTPRf<RjO3b6b1X5>X4\P8P6O2n2001000000120000000b3b7b1b9b8b0b0b0P^PYP[PUP_PQPMPCPLPOP;P]PEPcPaPeP3P\P>PTP6PIP`PHP2PbPgPf1G:B9Y:?/J=,FfR=9Cf9P5P=C=P4P0b;b<b=X2:X:dR0P8P6PBPFC6A;8BF[^2:^:dRdP6PSPRPjO3b6b1X5>X4\P8P6O2n2001000000121000000b3b7b1b9b8b0b0b0C9PWPXP^PYP[PUP_PQPMPCPLPOP;P]PEPcPaPeP3P\P>PWP6PIP`PhPiP6PXPVf=RiO3b6b1X5>X4\P8P6O2n2001000000120000000b3b7b1b9b8b0b0b0P^PYP[PUP_PQPMPCPLPOP;P]PEPcPaPeP3P\P>PXP6PIP`P0PdP6PWPVPiO3b6b1X5>X4\P8P6O2n2001000000121000000b3b7b1b9b8b0b0b0C9C9C9C9bDbCb>b>b>XFGXE1P8P6O2n2001000000121000000bIo"). Qed.

  (* [comment removed for export] *)
  Lemma rd_top8 : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), 8 <= zlen buf ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
               (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e7b8) fc None m (seg_rom usegs)).
Proof.
intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8.
destruct bounds as (L0 & BN & BM & BT).
assert (RE : read_ncount rt0 msv0 buf = read_ncount_body8 buf (msv0 + 1) rt0).
{ unfold read_ncount, FseNCount.Zlength. cbv zeta. replace (zlen buf <? 8) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
set (C := mkRD ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF lo rt0 buf msv0).
assert (OK : rd_ok C).
{ unfold rd_ok, RD_STACK, FSE_READ_STACK in *. cbn. repeat split; try assumption; try lia. }
eapply evt_mono.
- exact (rd_body8 C OK tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI).
- intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & r & m' & -> & MU & WM & MI' & ST' & RES).
  unfold fse_readh_post. do 14 eexists. exists r, m'. split; [reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, rd_W, RD_STACK, FSE_READ_STACK. subst C. cbn [outside c_NC c_rt0 c_MSVP c_TLP c_SP]. intros x; lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. rewrite RE. exact RES.
Qed.
  Lemma pad_tail : forall (z : byte) k, (k <= 8)%nat -> firstn (8 - k) (skipn k (repeat z 8)) = repeat z (8 - k).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rnc ()) ["Top"] "p'0h02Hkh11kh22Hah34__p1h47__sat13h54__x1h61Hh72H0h83Hk0h97__arithh:4__ffh;7__sat12h<8__varmaph=5__with>1ah?4cstrh@5cstr0hA5cstr1hB1xhC1zi001np;1p;2p;4p;3p;6p;<p;7p;8g0031j19Tg005dj1jTg006Bj1ZTg00@FR0j10Tg01gER1j21Tg00Khj1KTg01g_j22Tg00<TR2j1:Tg003Vj1=Tg00B>j2<Tg004QR3j2GTg00FEj2;Tg00Hoj4\Tg00IVj1CTg00<4j2JTg00J;j2YTg004mj2BTg0044j2XTg00Jcj3WTg005IR4j2VTg00KGj2UTg00CPj1TTg00QTj1STg00LHj2RTg00R2j4ATg00Lfj1QTg00MDj1PTg00Moj2@Tg00f?j1ITg00NRj2OTg00VDj4HTg0093j1iTg00X7j6gTg00O5j2fTg00OWj2eTg009Uj3LTg00PCj3`Tg00Pbj4_Tg01S`j3ETg01h6j3^Tg01hTj3bTg00TTl<DTg00U_l<cTg00Voj7dTg00S3j3FTg00WSj8[Tf4R5f3R6f2R7f1R8f0R93E3^p=4f6R:f5R;?b56AE7893Lp=312899E67,;5p=51<78/<9p=7g00Z;R<P<g00Y]R=P=P0P2P2P6g01i3R>P7P8P9M<Dp=aP<P<P=P=P0P2P2P:P>P;P5P<P<P=P=P0P2P2P6P>P7P8P9M<DM<Dp=?P<P=P1P2P3g01iWP;P5P6P7P8P9M<cp=]g00Y?R;/G9p=6%09#0p=8P8g00\DR3g00\cR2P2g00]CR1P9g00]cFdp=NAF=89p=hAF=78=F=9p=>P6P3P2P2P1P7P8P9G[p=Mg00^CR>#9R0#9#9R?#j#ZR@g00_]RA#0RB#0RC#0RD#0RE#0RF#0RG#0RH#0RI,19RJP<%K@RKP@12I8RLP@P8P@P5PID4P@P5PLF3^0JP811AIPKP@P6PIPAD5W0%09RA/1IRJP<PKP@%08RL,2IR5P@PLP@f7RMPID4P@PMP5F3^0JP811BIPKP@P:PIPBD5W0%0ARA/1IRBP<PKP@%0LRJ,2IR5P@PJP@f:RMPID4P@PMP5F3^0BP811CIPKP@f9RBPIPCD5W0%0ARA/1IRCP<PKP@%0JR5,2IRMP@P5P@f=RNPID4P@PNPMF3^0CP811DIPKP@f<RCPIPDD5W0%0ARA/1IRDP<PKP@%05RM,2IRNP@PMP@f@ROPID4P@POPNF3^0DP811EIPKP@f?PIPED5W0%0ARA/1IREP<PKP@%0MRD,2IRNP@PDP@fCROPID4P@POPNF3^0EP811FIPKP@fBPIPFD5W0%0ARA/1IRFP<PKP@%0DRE,2IRNP@PEP@fFROPID4P@POPNF3^0FP811GIPKP@fEPIPGD5W0%0ARA/1IRGP<PKP@%0ERF,2IRNP@PFP@fIROPID4P@POPNF3^0GP811HIPKP@fHPIPHD5W0%0ARA/1IRHP<PKP@%0FRG,2IRNP@PGP@fLROPID4P@POPNF3^0HP811IIPKP@fKPIPID5W0%0A/1I%0GRA/1I%:8RH%=>R>'<?7>>?7>>?7>>?7>>%=?RN'GROPA1<9>XB=RAPAPAPAPAPAPAPAPAPHO1RPO1RQO1RRO1RSO1RTO1RUO1RVO1RWO1PAPGPWPAPFPVPAPEPUPAPDPTPAPMPSPAP5PRPAPJPQPAPLPPPAP8PH1;=HCaF?F?F?F?PIPN1;=NE]P9C\PO%C7%:7#6p,3rt0,J=RO#C%:O#6p,3buf,J=RO#C%:O#6%=0RO%9?#9#9#=R?'Y1B;ORH%6?1XO?RA,B;[RP[%6ORLg00aURQAWO?8UW2%6A\Q^2Lp,3RSPp,3SPVRL#6RQ1BLARL'VP4PQPLPKP@%0B#8#8#8#8RB,2IR4P@PBP@fURBPID4P@PBP4F3P9P:g00b11U;O';PHeO1PPp-0RPg00bWRH#T%KHP=%S=RHP8P=PHP8P=1R=8P8PHCACACA%Q=%P=RHP=1@=;g00[]RO%I0#I,O=R0CH,NH%i2R:PHP=1@=>R4,h0?>44?>44?>44?>44PO1@=NCH,NHP:PHP3P2P2P1P6EgCMCM1fH1P9P7g00cCRHg00ccR1';1e97=LH1dA`=;8C_b:b<b=X5=W3%691<8>?7>>?7>>?7>>?7>>/GNP6[[^5=^3PP9PKP@f>RK#0#8#8#8#8RP,2IR=P@PPP@fZRPPID4P@PPP=F3%:Kf;PCO4b9b4X7LX6QP8P9O2n2001000000121000000b>b;b4bAb@b?b8W0X1<P9O1n0110000020011100P9O1W0X1<P9O1n0110000020011100P9O1W0X1<P9O1n0110000020011100P9O1W0X1<P9O1n0110000020011100P9O1W0X1<P9O1n0110000020011100P9O1W0X1<P9O1n0110000020011100P9O1W0X1<P9O1n0110000020011100P9O1W0X1<P9O1n0110000020011100P9O1W0X1<P9O1n0110000020011100P9O1W0X1<WCo"). Qed.

  (* [comment removed for export] *)
  Ltac rd_small_epi bp :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FR : rw_cells usegs mm (SPV + -112)
                     [CB 8 (map (Z_to_bv 8) bp); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    end;
    [ change [CB 8 (map (Z_to_bv 8) bp); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        with ([CB 8 (map (Z_to_bv 8) bp)] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]);
      apply rd_rw_cells_app; split; [eassumption|]; cbn [cells_size csize Nat.add];
      replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia; eassumption
    | ];
    do 13 zstep; zstep; zstep;
    lazymatch goal with FR : rw_cells _ _ (SPV + -112) _, ST' : stk _ _ _ (SPV + -112) |- _ => release_frame FR ST' SPV end;
    apply evt_done; unfold FSE_READ_STACK;
    do 14 eexists.

  (* [comment removed for export] *)
  Lemma rd_top_small : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), zlen buf < 8 ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
               (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e7b8) fc None m (seg_rom usegs)).
Proof.
intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8.
destruct bounds as (L0 & BN & BM & BT). unfold FSE_READ_STACK in *.
set (hb := zlen buf) in *. set (hbn := Z.to_nat hb).
set (buf' := buf ++ repeat 0 (Z.to_nat (8 - hb))).
assert (LB' : zlen buf' = 8) by (subst buf' hb; rewrite length_app, repeat_length; lia).
pose proof (munch_refl [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - 256, SPV)] m) as MU.
pose proof (wmono_refl usegs m) as WM.
assert (LWS : length (map (Z_to_bv 64) rt0) = length rt0) by apply length_map.
assert (LBS : zlen (map (Z_to_bv 8) buf) = hb) by (rewrite length_map; reflexivity).
carve_frame 128%nat ST.
do 14 zstep.
zstep. zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
do 6 zstep.
zstep. if_cases K1; zify_cond K1;
[exfalso; rewrite (proj2 (Z.ltb_lt 0 BUF) ltac:(lia)), (proj2 (Z.ltb_ge (BUF + hb) 1) ltac:(lia)) in K1; vm_compute in K1; discriminate K1|].
zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
assert (LV3 : Z.land MSVP 3 = MSVP mod 4) by (change 3 with (Z.ones 2); apply Z.land_ones; lia).
zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
do 3 zstep.
if_cases K; zify_cond K; [exfalso; lia|].
do 6 zstep.
lazymatch type of FR with rw_cells _ _ _ (CB 16 ?j0 :: ?rest) => change (CB 16 j0 :: rest) with ([CB 16 j0] ++ rest) in FR end.
apply rd_rw_cells_app in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) in FR by lia.
pose proof (rw_cells_merge usegs _ (SPV + -112) [] [C8 (Z_to_bv 64 0)]
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FM.
cbn [app cells_size cells_bytes csize cbytes Nat.add] in FM. clear FR.
change (le8 (Z_to_bv 64 0) ++ []) with (repeat (Z_to_bv 8 0) 8) in FM.
pose proof (rw_cells_split_CB usegs _ (SPV + -112) [] 8 (repeat (Z_to_bv 8 0) 8)
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
[hbn; (8 - hbn)%nat] FM ltac:(cbn [sum_nat]; lia)) as FS.
cbn [app mk_CB_cells] in FS. clear FM. rewrite (pad_tail (Z_to_bv 8 0) hbn) in FS by lia.
change (CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8)) :: CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn)) ::
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
with ([CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8))] ++ ([CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] ++
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FS.
apply rd_rw_cells_app in FS. destruct FS as [R1 FS]. apply rd_rw_cells_app in FS. destruct FS as [R2 R3].
cbn [cells_size csize Nat.add] in R2, R3.
replace (SPV + -112 + Z.of_nat (hbn + 0)) with (SPV + -112 + hb) in R2, R3 by lia.
replace (SPV + -112 + hb + Z.of_nat (8 - hbn + 0)) with (SPV + -104) in R3 by lia.
call (rd_memcpy_specZ (SPV + -112) BUF hb); [exact HBUF | rewrite length_map; unfold hb; lia | exact R1 | lia | eassumption
| first [reflexivity | f_equal; lia] | reflexivity | reflexivity | lia | lia | lia |].
assert (FB' : Forall (fun c => 0 <= c < 256) buf').
{ subst buf'. apply Forall_app. split; [exact FBY|]. apply Forall_forall. intros c Hc. apply repeat_spec in Hc. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RB8 : rw_cells usegs mm (SPV + -112) [CB 8 (map (Z_to_bv 8) buf')]) end.
{ replace (SPV + -112 + hb) with (SPV + -112 + Z.of_nat (cells_size [CB hbn (map (Z_to_bv 8) buf)])) in R2
by (cbn [cells_size csize Nat.add]; lia).
lazymatch goal with P : rw_cells usegs ?mm (SPV + -112) [CB (Z.to_nat hb) (map (Z_to_bv 8) buf)] |- _ =>
pose proof (proj2 (rd_rw_cells_app usegs mm (SPV + -112) [CB hbn (map (Z_to_bv 8) buf)]
[CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))]) (conj P R2)) as RJ;
pose proof (rw_cells_merge usegs mm (SPV + -112) [] [CB hbn (map (Z_to_bv 8) buf); CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] [] RJ) as RM
end.
cbn [app cells_size cells_bytes csize cbytes Nat.add] in RM. rewrite app_nil_r in RM.
replace (hbn + (8 - hbn + 0))%nat with 8%nat in RM by lia.
subst buf'. rewrite map_app, map_repeat. replace (Z.to_nat (8 - hb)) with (8 - hbn)%nat by lia. exact RM. }
clear R2.
do 7 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
set (C' := mkRD (Z_to_bv 64 0x1e860) gp tp (Z_to_bv 64 hb) (Z_to_bv 64 MSVP) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) s4 (Z_to_bv 64 (BUF + hb))
s6 s7 s8 s9 s10 s11 F fc mm (SPV + -128) NC MSVP TLP (SPV + -112) lo rt0 buf' msv0) end.
assert (OK' : rd_ok C').
{ unfold rd_ok, RD_STACK. subst C'. cbn [c_buf c_msv0 c_rt0 c_SP c_lo c_NC c_BUF c_MSVP c_TLP]. rewrite LB'.
repeat split; try assumption; try lia. }
assert (HBUF' : bytes_at usegs (c_m C') (c_BUF C') (map (Z_to_bv 8) (c_buf C'))).
{ subst C'. cbn [c_m c_BUF c_buf]. destruct RB8 as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA. }
replace (Z_to_bv 64 8) with (Z_to_bv 64 (zlen (c_buf C'))) by (subst C'; cbn [c_buf]; rewrite LB'; reflexivity).
eapply evt_cut.
{ eapply (rd_body8 C' OK' tl0); subst C'; cbn [c_m c_NC c_rt0 c_MSVP c_msv0 c_TLP c_BUF c_buf c_lo c_SP]; try eassumption. }
intros ms' PO. hnf in PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & RES).
unfold rd_W, RD_STACK in MU'. subst C'.
cbn [c_ra c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m c_SP c_NC c_MSVP c_TLP c_BUF c_lo c_rt0 c_buf c_msv0] in *.
clear ARR HMSV HTL HBUF'.
lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call usegs ma mb MU' WM'; clear MU' WM'; try clear ma end.
replace (ret_pc (Z_to_bv 64 0x1e860)) with (Z_to_bv 64 0x1e860) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold rd_res_ok in RES. cbn [c_NC c_MSVP c_TLP] in RES. destruct RES as [RR RES].
assert (RE : read_ncount rt0 msv0 buf = match read_ncount_body8 buf' (msv0 + 1) rt0 with
  | Ok (nc, msv, tl, cs) => if hb <? cs then Err ZSTD_error_corruption_detected else Ok (nc, msv, tl, cs)
  | Err e => Err e | Ub => Ub | NoFuel => NoFuel end).
{ unfold read_ncount, FseNCount.Zlength. cbv zeta. fold hb. replace (hb <? 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
destruct (read_ncount_body8 buf' (msv0 + 1) rt0) as [[[[rt msv] tl] n]|e| |] eqn:EB;
  try rewrite EB in RES; try rewrite EB in RE; cbv beta iota in RES, RE; try contradiction RES.
2: { destruct RES as [-> RE0]. zstep. zstep. zstep. zstep.
  lazymatch goal with |- context [Z.land (Z.b2z (?a <? ?x)) (Z.b2z (hb <? _))] =>
    replace (a <? x) with false by (symmetry; apply Z.ltb_ge; lia) end.
  cbn [Z.b2z]. rewrite Z.land_0_l. if_true.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR0 with rw_cells _ _ _ [CB 16 ?j0] =>
assert (FR : rw_cells usegs mm (SPV + -128)
[CB 16 j0; CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
end end.
{ lazymatch goal with |- rw_cells _ _ _ (CB 16 ?j0 :: ?rest) => change (CB 16 j0 :: rest) with ([CB 16 j0] ++ rest) end.
change (CB 8 (map (Z_to_bv 8) buf') :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
with ([CB 8 (map (Z_to_bv 8) buf')] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
apply rd_rw_cells_app. split; [exact FR0|]. cbn [cells_size csize Nat.add].
replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) by lia.
apply rd_rw_cells_app. split; [exact RB8|]. cbn [cells_size csize Nat.add].
replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact R3. }
clear FR0 RB8 R3.
do 13 zstep. zstep. zstep.
release_frame FR ST' SPV.
  apply evt_done. unfold fse_readh_post, FSE_READ_STACK.
  do 14 eexists. eexists. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [first [eassumption|lia]|].
  rewrite RE. cbv beta iota. split; [first [reflexivity|lia]|lia]. }
destruct RES as (-> & ARR' & HMSV' & HTL').
assert (N1 : 1 <= n <= 8).
{ destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; lia)
  ltac:(unfold FseNCount.Zlength; lia)) as [(nc2 & msv2 & tl2 & n2 & E2 & _ & _ & _ & _ & N2 & _) | (e & E2)];
  rewrite EB in E2; [injection E2 as <- <- <- <-; try (unfold FseNCount.Zlength in N2); lia| discriminate E2]. }
destruct (Z_lt_ge_dec hb n) as [HLT|HGE].
+ zstep. zstep. replace (hb <? n) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  zstep. zstep.
  try (lazymatch goal with |- context [n <? ?x] => replace (n <? x) with true by (symmetry; apply Z.ltb_lt; lia) end).
  cbn [Z.b2z]. try change (Z.land 1 1) with 1. if_false.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR0 with rw_cells _ _ _ [CB 16 ?j0] =>
assert (FR : rw_cells usegs mm (SPV + -128)
[CB 16 j0; CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
end end.
{ lazymatch goal with |- rw_cells _ _ _ (CB 16 ?j0 :: ?rest) => change (CB 16 j0 :: rest) with ([CB 16 j0] ++ rest) end.
change (CB 8 (map (Z_to_bv 8) buf') :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
with ([CB 8 (map (Z_to_bv 8) buf')] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
apply rd_rw_cells_app. split; [exact FR0|]. cbn [cells_size csize Nat.add].
replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) by lia.
apply rd_rw_cells_app. split; [exact RB8|]. cbn [cells_size csize Nat.add].
replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact R3. }
clear FR0 RB8 R3.
repeat zstep.
release_frame FR ST' SPV.
  try replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv_eq; reflexivity).
  apply evt_done. unfold fse_readh_post, FSE_READ_STACK.
  do 14 eexists. eexists. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [first [lia|(vm_compute; split; congruence)]|].
  rewrite RE. replace (hb <? n) with true by (symmetry; apply Z.ltb_lt; lia). cbv beta iota.
  split; [vm_compute; reflexivity|vm_compute; split; reflexivity].
  + zstep. zstep. replace (hb <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    zstep. rewrite Z.land_0_r.
    zstep. if_true.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR0 with rw_cells _ _ _ [CB 16 ?j0] =>
assert (FR : rw_cells usegs mm (SPV + -128)
[CB 16 j0; CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
end end.
{ lazymatch goal with |- rw_cells _ _ _ (CB 16 ?j0 :: ?rest) => change (CB 16 j0 :: rest) with ([CB 16 j0] ++ rest) end.
change (CB 8 (map (Z_to_bv 8) buf') :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
with ([CB 8 (map (Z_to_bv 8) buf')] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
apply rd_rw_cells_app. split; [exact FR0|]. cbn [cells_size csize Nat.add].
replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) by lia.
apply rd_rw_cells_app. split; [exact RB8|]. cbn [cells_size csize Nat.add].
replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact R3. }
clear FR0 RB8 R3.
do 13 zstep. zstep. zstep.
release_frame FR ST' SPV.
    apply evt_done. unfold fse_readh_post, FSE_READ_STACK.
    do 14 eexists. eexists. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    rewrite RE. replace (hb <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbv beta iota.
    split; [reflexivity|]. split; [eassumption|]. split; eassumption.
Qed.
End Top.

(* [comment removed for export] *)
Theorem fse_readh_proof : fse_readh_stmt.
Proof.
unfold fse_readh_stmt.
intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV NC MSVP TLP BUF
  rt0 buf msv0 lo tl0
  ARR HMSV HTL HBUF FBY HM0 HM1 HLEN HNP HNA HVP HVA HTP HTA HBP HSLACK ST LO RSP SNS SMS STS SBS SNM SNT SNB SMT SMB STB MI -> -> -> -> ->.
unfold PFSE_READNC_B.
destruct (Z_lt_le_dec (zlen buf) 8) as [LT|GE].
- eapply rd_top_small; eassumption.
- eapply rd_top8; eassumption.
Qed.
