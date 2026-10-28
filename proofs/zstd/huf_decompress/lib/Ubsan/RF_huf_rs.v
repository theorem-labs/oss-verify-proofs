(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_HufStats HufPure_HufStatsRT HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit StrFun WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_iface2 RF_huf_tbl_kit
  RF_huf_bdt_model RF_huf_fdw_kit RF_huf_fdw_tk RF_huf_fdw RF_huf_rs_pure RF_huf_rs_dl RF_huf_rs_fin RF_huf_rs_tail.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_rs () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List:firstn_nilC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit7sxb_litK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallK47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C45stdpp9bitvector;definitions>Z_to_bv_signedC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6ltb_geK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z7mod_addI47Corelib4Init9Datatypes6option00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats:read_statsC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure4rresC5ARocqVerifyHarness?AgentSubmission5UbsanARF_huf_tbl_iface2?huf_rstats_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hs_retC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats:hs_weightsC47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats<hs_nbSymbolsI47Corelib4Init5Logic2ex00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas@Forall_all_bytesC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufStatsRT>read_stats_retK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega7EnvRing5PExpr06C35stdpp7tactics<f_equal_helpC45stdpp9bitvector;definitions@Z_to_bv_unsignedK47Corelib4Init5Logic3and01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C47Corelib4Init5Logic9False_indK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats7hs_rankC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats;hs_tableLogK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv5Instr5instr00I5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats00C5ARocqVerifyHarness?AgentSubmission5UbsanARF_huf_tbl_iface2@HUF_RSTATS_STACKC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure7rs_tailI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_tk=stk_frame_endC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transc5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs6rs_epiC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_tail<rs_tail_walkC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_tk<wr_at_of_stkC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05c5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs2hkC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_tk=rw_cells_app'C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp?huf_fse_weightsC47Corelib5Lists7ListDef6repeatC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats<collect_loopC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount9highbit32C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shl32C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6assertC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5storeC47Corelib4Init9Datatypes3orbK5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats01C56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andic5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs<lts_pos_byteC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure6rs_fseC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>negb_false_iffK4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List<firstn_skipnC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model9u8arr_appC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List7map_appC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT<Forall_skipnC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT=Forall_firstnC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC5ARocqVerifyHarness?AgentSubmission5UbsanARF_huf_tbl_iface2?fse_decomp_postC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_fdw@fse_decomp_proofC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompCfse_decompress_wkspC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC46Stdlib5Lists4List=repeat_lengthC5ARocqVerifyHarness?AgentSubmission4SpecEHufPure_FseReadBridgeIfse_decompress_wksp_safe'C47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List;Forall_implC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List9app_assocc5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs7rs_joinC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_16C5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutc5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs7land255c5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs<lts_neg_byteC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure9rs_directC56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6leb_gtC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_dl6dl_invC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats;direct_loopC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_dl7dl_loopC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin;srliw_smallC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC56Stdlib6ZArith6BinInt1Z9div_smallc5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs;land255_negc5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs6sxb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC56Stdlib6ZArith4Znat5Nat2Z7inj_minC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface?PHUF_READ_STATSI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompHZSTD_error_srcSize_wrongC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStatsCHUF_SYMBOLVALUE_MAXC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats@HUF_TABLELOG_MAXK4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompMHUF_READ_STATS_WORKSPACE_SIZEc5ARocqVerifyHarness?AgentSubmission5Ubsan9RF_huf_rs<rs_wksp_sizeK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C5ARocqVerifyHarness?AgentSubmission5UbsanARF_huf_tbl_iface2@FSE_DECOMP_STACKC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount@FSE_MAX_TABLELOGK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop03C5ARocqVerifyHarness?AgentSubmission5UbsanARF_huf_tbl_iface2?huf_rstats_stmt".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::= match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg]) end.
Local Ltac zs_idioms_in H ::= match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg]) end.

Definition hk (P : Prop) : Prop := P.

Lemma sxb_eq : forall c, 0 <= c < 256 -> sxb (Z_to_bv 8 c) = Z_to_bv 64 (if c <? 128 then c else c + (2^64 - 256)).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs ()) [] "p'0h04__x1h11Hh27__arithh34__ffh48__varmaph55__with62b1h72b2h81nh91zh:2Hch;1bi001bh<2b0h=1cp;2p;1p;3p;4p;6p;7p;8p10000p4p710g000MR0p4p710R1p8p1000kp4p7210P1p8p1001Wp4p7210p10024p4p710p8p1002Pp4p710P1p8g002oj24Tg003Kj12Tg0040j18Tg004Nj20Tg004jR1j27Tg005Ej15Tg005hj31Tg006Bj23Tg006lj3JTg007Pj1BTg007nj2:Tg008Tj1ETg009Dj2@Tg009aj2\Tg00:>j2YTg00:[j29Tg00;8j2ATg00;Rj2VTg00<4R2j3UTg00<Xj1RTg00=8j1QTg00=Xj2MTg00>6j1LTg00>Tj1KTg00??j2>Tg00?bj2ITg00@Ej4;Tg00A0j1HTg00ARj3GTg00B5j2FTg00BWj2NTg00CCj3OTg00Cbj4PTg00DTj3DTg00E7j3STg00EZj2TTP0j6CTg00FVj2[Tg00GRj7ZTg00H6j7XTg00HZj8WTf1R0g00I>R3g00I]R4P4g00J=R5f0R6g00J]FZp=6g00K=R7P0g00K[P6C;p=<f2R8P3P4P4P5P0P6FXp==f3R9P3P4P4P5P8P0P6GWp=?g00LBR3/46g00L`R:#2R;#2#2R<#2#2#2R=#2R>#2#8R?,06'7R@g00MERA%56RB%50RCP1%58?10613981390517R1[13801386517%59?180[RDf4RE#5?198\1AJ806P6n2001000000120000000W7W6W8PD^7C^6B^8AP6%B=RA%B</:8#ER<g00McRBP7%8>R>,@8RCP8%8;R;%8='\R=/Y?RD,98n0100000020000R1,:ARFP7P1PBP71@9>RGP9199Dn0100000020000RH,:A,3A9176X97P7P1A17H6X971A7113AF1V8>108>14>8;UCPGPBP210E>14>EPBP7P0f6RE19EDn0100000020000R2,43102='7P0f5R2/0>g00NCRG#RRC%QGRG1M70RF%L7RH%K7RIP71>73RJg00NoRK1I7:R:C;,6IRL1>7?RM,<:,6I5=IRN%H4R41>7;=G7AR;,<:,6I9=ILC?1FI5R5P6P8g00OVRL,AB1N68=1BLdAO730CPRLb3b4b5X071430RB100='7\@^07P6f7PEO2REb2W1P6O114>2PCPGPFPHPIPNP4P7PJPKAD7;M9S7:R:C;,6I1<:;,6I5=IC?P5PLb3b4b5X07190DRD,4310D='7\@^07PEb2W1P6O1n200210000000021000011000b<b;,T1EC13A<PCPGPFPHPIPNP4PNC?P5PLb3b4b5X07100?,7B\@^07P6P9P8O2b2,[8ECO4b1W:X=7o"). Qed.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51Eh62Hch71ch81zp;2p;1p;4p;3p;7p;8p;6g002oj25Tg003Kj10Tg0040j12Tg004Nj2:Tg004jj2;Tg00<Xj1MTg00=8j1DTg00P6j1ATg00>6j1?Tg00>Tj1>Tg00??j24Tg00@Ej43Tg00B5j2PTg00;8j2OTg00BWj2NTg005hj36Tg00CCj3LTg00Cbj4KTg00PTj3CTg00Q7j1BTg00QUj28Tg009aj2@Tg00R3j29Tg00=Xj2ETg00?bj2FTg00H6j7GTg00A0j1HTg00HZj8ITg00RSj3JTg00S6j11Tg000Mj6=Tg00GRj7<Tf1R0g00I>R1g00I]R2P2g00J=R3f0R4g00J]F<p=7g00K=R5g00LBR6/54g00L`R7#0R8#0#0R9#0#0#0#0#0#2R:,:4';R;%29R9g00NCR<#MR=%D<R<%A5%?5R>%>5R?P51456R@g00NoRA1459C3'71P?3RBP4f2RCg00McRDg00OVRE'O1N4C=6DEdAL560CKREb1b2b31569P4b05C0%B9,80%28/@9R9,90565P519C9f3R89654X85P=P<1E50P>P?P1P2P2P3P?P1P2P2P3P5P@PA1F57RAC3,7?P5PAg00K[145:C3,7?FGR?%H2P?GIPBPEb1b2b3X4515601:0:';\;^45P4P8PCO2b09JC9%17#1#1#1#1#1#1#2,8CP4E=b5W6W7o"). Qed.

Lemma lts_neg_byte : forall c, 128 <= c < 256 -> bv_lts (Z_to_bv 64 (c + (2^64 - 256))) (Z_to_bv 64 0) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs ()) [] "h01Hh12Hah24__p1h34__p2h44__x1h54__x2h64__x3h74__x4h84__x5h91mh:1nh;1zh<2H0h=2H1h>2H2h?2H3h@2H4hA2H5hB2H6hC2H7hD2H8hE2HchF7__arithhG4__ffhH7__sat10hI6__sat9hJ8__varmaphK5__withL1chM1qhN2q0hO1rhP2r0p&0p;1p;2p;3p;4p;6p;7p;8g003Kj10Tg0040j1>Tg002oj2ATg004Nj22Tg004jR0j27Tg007Pj1sTg009aj2nTg00:>j2DTg00:[j21Tg00S[j2ITg007nj2QTg00TBj2PTg009Dj2?Tg00Tjj2{Tg00R3j28Tg00UJj2XTg00Ukj1pTg00VDj2GTg00Vaj2HTg00W>j2\Tg00Wej2TTg00XLj2STg00Y2j2RTg00YXj2fTg00Z@j3eTg00Zdj19Tg00[Cj1dTg00[aj2cTg00\Bj3bTg00\kj2aTg00]Tj3UTg00^=j2`Tg00^fk201Tg00_Rj2_Tg00<Xk100Tg00`>j3~Tg00=8j1}Tg00=Xj2]Tg00P6j1zTg00`^j4MTg00>6j1wTg00>Tj1vTg00??j2@Tg00A0j1uTg00?bj2BTg00@Ej4FTg00a<j6rTg00E7j3CTg00S6j1WTg00a`j3VTg00ARj3oTg00DTj3NTg00B5j2mTg00;8j2lTg00BWj2qTg00CCj3kTg00Cbj4tTg00bCj2ZTg000Mj6[Tg00c0j3jTg005hj3OTg00c]j3iTg00GRj7hTg00dFj6yTg00H6j7gTg00HZj8|Tf0R1#0#0#0#0p=^g00McR2g00OVR37O1p=6%01#0p=x%01#0#0#0#0#0#0#0p==g00K=R4g00LBR57O1p=Kf1R6=O41p=<1A51p=:1`41p=;Ai461p=5P4P6g00K[P1CFp=EP6g00I>R7g00I]R8P8g00J=R9P1g00J]Fhp=3P6P7P8P8P9P1Eyp=Yf2R:P7P8P8P9P6P1Fgp=Lf3R;P7P8P8P9P:P6P1G|p=4P4P6g00djP1CFp=Jg00L`R<#0R=#0R>#^R?#0R@#>RA/A1%0@R@#>RB,21'7P4%s?RC%>=RD%>?R?'nRE/DBRF,16RG'IRH1QC5RI,PCRJ,?1#6X;4P41IC5RK11:FRL,IC/?1#6X;4P01?61#612:6R0[12611?:6#6[RM1?;:#6\01{61P1n2001000000120000000X94X:4PM^94^:4P1%0@#x#^#=#=#=#=#=#=R@#>RM,1LRL%0@#>R@'8/DM115MR0/8@RN/DM1XL@%K@RL#pRO11;F/1MRP1GP@,H@18P@'1'<[1\P@125@RPf4RQ/1F/1MRR/8@RS#:12S@'7[1TR@12@5RRf5RS/1F/1MRT/8@RU,2@1AU5'7[1ST@f6RT/1F/1MRU/G@#K\L1RU@f7RV/1F/1MRW/8@/<W\L1GW@P4f8RW/1F/1M/8@P41X0@1G0@RF,H@/1N,<0\O1\0@%:N12N@'7\P1T0@12@N1AN5'7\R1S0@%KF\L1R0@1<N0\LPFP4PNP41fD?125D%:?125E[[%:DRNg00eQRFAeD?6UW1%:E\F^1Np-0RNg00NCRFg00emRE#9R?#9RR#9RO#9RX#9RY#9RZ#;%d<,c4%;YRY5b4R['5%;X%;ORO'5,5Y1a4@RY%;?5U41`4E9U4Y%9Z#;%;R,5O,5['5'5'5g00fL+01'_'_&00F3~%}FP4P41]4QP:%z4RFCMP6P41]4SP;PFCMCM%w4%v4RFPF1@45R[1@4@RO'E,3FRR%u8RZP4P[g00NoRY1B4=RECF,3F1YFV5LFC4PZPFPFPFP7P8P8P91JO[,3FErR8PZ1@4MR79C4[%W=,B49V4O=C4E'J,3FC4PZPFPFPRPZ1YFW1B4<RR/EO,3F5LFC4PZPFPFP8PZ%W<,B4R<1@4D=o4C1@4BRD5N45C4=C471B4>9V4O=C4R'J,3FC4PZPFP41@4APYP<CF,3F1E<D,3F5LFPZAN4R7AN4E7'E,3FC4C4C4C4C41mF9P1P:1l231q1:#6dAk456CtbGbJbKX44X54X64X74X84X2NW3%::/7T\Pg00g8\LRL1H@T/1;,<0[f9R012;@R:'7\P1H@V/1Q,<U\L1AAT12TB'71DSM1DTM'2[[[[[^44^54^64^74^84^2N^3NP1f:R1#:P:PQf;fCP;P1PWP0f?f@fBO<bFbIbHbPbNbDbCbBbAb@bObMb?b>b=b<b0O3b01?HK#6ePJ1ZC5E[1QCGR5,PC1ZCGE[AjC5I#6eWEXL4o"). Qed.

Lemma lts_pos_byte : forall c, 0 <= c < 128 -> bv_lts (Z_to_bv 64 c) (Z_to_bv 64 0) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs ()) [] "h01Hh14__p1h24__p2h34__x1h44__x2h54__x3h64__x4h74__x5h81xh91yh:1zh;2H0h<2H1h=2H2h>2H3h?2H4h@2H5hA2H6hB2H7hC2H8hD2HchE7__arithhF4__ffhG8__varmaphH5__withI1chJ1qhK2q0hL1rhM2r0p;1p;2p;3p;4p;6p;7p;8g003Kj10Tg0040j1HTg004Nj22Tg004jR0j25Tg007Pj1qTg00S[j2KTg007nj2XTg00TBj2TTg009Dj2=Tg002oj2>Tg00gUj2|Tg00:[j21Tg00R3j29Tg00:>j2ATg00UJj2]Tg00Ukj1pTg00VDj2FTg00Vaj2CTg00W>j2_Tg00Wej2`Tg00XLj2VTg00Y2j2UTg00Zdj16Tg00[Cj1fTg00[aj2eTg00\Bj3STg00^=j2RTg00\kj2dTg00]Tj3QTg00^fj2cTg00_Rj2PTg00<Xj1bTg00`>j3{Tg00=8j1zTg00=Xj2aTg00P6j1yTg00`^j4OTg00>6j1xTg00>Tj1uTg00??j2ETg00A0j1sTg00?bj2@Tg00a<j6rTg00S6j1\Tg00E7j3BTg00a`j3[Tg00DTj3ZTg00B5j2oTg00;8j2nTg00BWj2lTg005hj3DTg00CCj3mTg00Cbj4jTg00bCj2YTg000Mj6WTg00c0j3iTg00c]j3tTg00@Ej4LTg00GRj7hTg00dFj6vTg00H6j7wTg00HZj8gTg00LBR1f0R2'>p=?%02#0#0#0p=kg00McR3g00h57D2p=8%02#0#0#0#0#0#0#0p=;g00K=R4?D21p=Jf1R5=D42p=<1R42p=:At452p=7P4P5g00K[P2CLp=NP5g00I>R6g00I]R7P7g00J=R8P2g00J]Fhp=3P4P5g00NoP2CLp=MP5P6P7P7P8P2Evp=^f2R9P6P7P7P8P5P2Fwp=Gf3R:P6P7P7P8P9P5P2Ggp=4P4P5g00djP2CLp=I%?2g00L`R;#0R<#0R=#kR>#0R?#HR@,22'5P4%q>R>/K5RA1X>1RB,T>RC,=2#8X:4P41K>1RD1K>9/=2#8X:4P01=52#81>59R0[1>251=95#8[RE1=:9#8\01|52P2n2001000000120000000X94X84PE^94^84P2%;?#;#;#;#;#;#;R?#HRE,19%0?#HR?'9/AE111ER0/9?RF/AE1]0?%J?RG#pRH1F0?RI,C?/1F,<0[1_0?121?RJ%?F12F?'5[1`0?12?1RK12?F1>F1'5[1V0?%JI\G1U0?1<F0\GPIP4PFP4f9RF/1E/]?f:/1ERI1FI?,C?19I?'1'<\H1_I?f;/1ERI/9?RH#?12H?'5\J1`I?f</1ERI/9?RH,2?1>H1'5\K1VI?f=RI/1ERK/F?#J\G1UK?f>RK/1ERH/9?/<H\G1FH?P4f?/1E/9?P4p-0RHg00NCRLg00emRM#6RN#6RO#6RP#6RQ#6RR#:RS%f;,e4RT%:PRP5S4%:O1R4MRM'7'7'7%:Q,7S1d4?RS%:N5Q4AQ4SM%6R#6RR#6#:%:R9S4T/7P'7'7'7g00fL'c'P'P%bL3{%zLP4P4f4RL,a4P9%y4RPCOP5P4f5RT,a4P:PPCOCO%x4%u4RPPP1E41RR1E4?RS'N,3PRM%s7RN1@4<RQ,MR,3Pf7RO,^P5GPC4PNPPPPPPP6P7P7P81ISR,3PErR7PN%\;,@4R61E4ERU5B4%\<,@49[4S=B4Q'I,3PC4PNPPPPPMPNf8RM,^P1@4;R;/NS,3P5GPC4PNPPPPP7PNAB4RU1@4=9[4S=B4;'I,3PC4PNPP1MR6,3P1E4@,N6,3P5GPPNAZ4;UAZ4QU'M,3PC4C4C4C4C41oP8P2P9g00OVRP,n31l29=D3PdAm415CjbFbGbHX34X44X54X64X74X1HW2%?9f6RP'5\Jg00g8\GRG11LE1C?P/1:'<[12:?,5F\J1C?O/1L,<0\G%?P12P@'51ATE1APE'>[[[[[^34^44^54^64^74^1H^2HP2%?M125?P9PFfAP5PMPPPOPIPKf@O<bEbMbKbCbBbAb@b?bLbJb>b=b<b;b0O3b01=AD#8ePC1Y>1EW1X>5R1,T>1Y>5EWAi>1B#8eWDXI4o"). Qed.

Lemma land255_neg : forall c, 0 <= c < 256 -> Z.land (c + 18446744073709551360) 255 = c.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh61Eh71Hh82Hch91cp;2p;1p;4p;3p;7p;8p;6g002oj2<Tg003Kj1:Tg0040j15Tg004Nj2ATg004jj2?Tg00S6j10Tg00:[j21Tg00<Xj1CTg00=8j1BTg00P6j1\Tg00>6j1YTg00>Tj1VTg00??j28Tg00@Ej47Tg00B5j2UTg00;8j2TTg00BWj2NTg005hj3;Tg00CCj3KTg00Cbj4JTg00PTj3HTg00Q7j1GTg00QUj2=Tg009aj2FTg00R3j26Tg00=Xj2ETg00?bj2DTg00a`j3MTg00E7j3>Tg00Vaj2OTg00H6j7PTg00A0j1QTg00HZj8RTg00RSj3STg00a<j6[Tg00hUj4ZTg000Mj6@Tg0024j6XTg00GRj7WTf0R0#:#:p=2%00#0p=L%00#0#0#0p=I%00#0#0#0#0#0#0#0p=3f1R1g00I>R2g00I]R3P3g00J=R4P0g00J]FWp=9g00K=R5?;10p=4g00LBR6/<0g00L`R7#:R8#2R9#:#2#2#5R:,A0'?R;%07#L#IR<#3#3#3#3#3#3R=#2#2#2#2#5R>,11R?%59R9g00NCR@#CRA%B@R@%\5RB%Y5RC%V5RDP51856REg00NoRF1859C7'91UD4RGP0f2RHg00McRIg00OVRJ'T1N0H=;IJdAK561CJRJb1b2b31<69P0b03H%G9,=?%58/F9R9,6?'4P511H>R?/69f3R9,40X55PAP@1E51R8PCP51D57R7%5=R=,85185:RI5M55>5g00djRK185>9>57C7,9DPGPJb1b2b3X451O=:RL,10110>'4^45P0P9O1b011HL/4?P5119LRL160:f4RH'4X55P5169:140HX55PAP@P8PCPDP2P3P3P4PDP2P3P3P4P5PEPFP7C7,9DP5P7g00K[PIC7,9DFPR7%Q3P7GRPGPJb1b2b3X451<611A1:'?\;^45P0PHP9O2b09S9:16L:P9P=P:PAP@PBPCPDP2P3P3P4P5PIPKPEC7,9DE[PGPJb1b2b3A;5:6g00g8[P0b0CZE@119>P0EXb7%5<,=?P0E@b6W8X95o"). Qed.

Lemma rs_wksp_size : HUF_READ_STATS_WORKSPACE_SIZE = 876.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs ()) [] "p;1p;2g00S6j10Tg003Kj11Tg0040j13Tg00;8j22Tg00K=g00L`#0#1#0#0#1#0#0#1#1#3'2o"). Qed.

Section TOP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (HW RK NSP TLP W lo : Z) (src : list Z).
  Notation SP := (bv_unsigned sp).
  Notation FB := (bv_unsigned sp - 64).
  Notation POST := (huf_rstats_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW RK NSP TLP W src lo m).
  Notation WALL := [(bv_unsigned sp - HUF_RSTATS_STACK, bv_unsigned sp); (HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4);
                    (TLP, TLP + 4); (W, W + 876)].
  Hypothesis SPR : 64 <= SP.
  Hypothesis HSB : Forall (fun c => 0 <= c < 256) src.

  (* [comment removed for export] *)
  Lemma rs_epi : forall m' R a0v (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word),
    rw_cells usegs m' (FB + 8) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m' lo (FB + 8) -> lo <= FB ->
    munch WALL m m' -> wmono usegs m m' -> mem_inv usegs m' ->
    read_stats src = R -> rres HW RK NSP TLP R m' a0v ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 FB) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 a0v) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20
                            y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x1f124) fc None m' (seg_rom usegs)).
Proof.
  intros m' R a0v y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 FR STK LOF MU WM MI ER RR.
  do 7 zstep. zstep.
  apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
  assert (STK' : stk usegs m' lo SP).
  { apply (stk_merge usegs m' lo (FB + 8) SP STK); [|lia]. replace SP with (FB + 8 + Z.of_nat 56) at 2 by lia. exact FR. }
  zstep. apply evt_done. unfold huf_rstats_post.
  do 14 eexists. exists (a0v mod 2^64), m'.
  split; [|split; [exact MU|split; [exact WM|split; [exact MI|split; [exact STK'|split; [apply Z.mod_pos_bound; lia|]]]]]].
  2:{ subst R. destruct (read_stats src) as [h|e| |] eqn:ERS; cbn in RR; try contradiction.
      - destruct RR as (-> & RW & RKA & NSC & TLC).
        pose proof (read_stats_ret src h (Forall_all_bytes _ HSB) ERS) as HR.
        split; [rewrite Z.mod_small by lia; reflexivity|]. split; [exact RW|]. split; [exact RKA|]. split; [exact NSC|exact TLC].
      - destruct RR as (-> & E). split; [|lia]. Z.div_mod_to_equations. lia. }
  rewrite Z_to_bv_mod64. rewrite ?Z.sub_add, ?Z_to_bv_bv_unsigned. reflexivity.
Qed.
  (* [comment removed for export] *)
  Lemma rs_join : forall m2 ws junk iS jr nsv tlv (x1 x5 x6 x7 x10 x11 x12 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word),
    read_stats src = rs_tail ws (zlen ws) iS ->
    zlen ws <= 255 -> Forall (fun c => 0 <= c < 256) ws -> zlen junk = 256 - zlen ws -> 0 <= iS <= 128 ->
    u8arr usegs m2 RK jr -> zlen jr = 52 -> u8arr usegs m2 HW (map (Z_to_bv 8) ws ++ junk) ->
    rw_cells usegs m2 NSP [C4 nsv] -> rw_cells usegs m2 TLP [C4 tlv] ->
    rw_cells usegs m2 (FB + 8) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m2 lo (FB + 8) ->
    munch WALL m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
    lo <= FB - 384 -> 0 < HW -> HW + 256 <= lo -> 0 < RK -> RK + 52 <= lo -> SP + 8 <= NSP -> NSP + 4 <= TLP ->
    (HW + 256 <= RK \/ RK + 52 <= HW) -> RK mod 4 = 0 -> NSP mod 4 = 0 -> TLP mod 4 = 0 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp tp x5 x6 x7 (Z_to_bv 64 RK) (Z_to_bv 64 HW) x10 x11 x12
                            (Z_to_bv 64 NSP) (Z_to_bv 64 TLP) x15 x16 x17 (Z_to_bv 64 (zlen ws)) (Z_to_bv 64 iS) x20 x21
                            s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1eec0) fc None m2 (seg_rom usegs)).
Proof using All.
  intros m2 ws junk iS jr nsv tlv x1 x5 x6 x7 x10 x11 x12 x15 x16 x17 x20 x21 x28 x29 x30 x31
         ERS WSL WSB JKL IS0 RKA RKL HWA NSC TLC FR STK MU WM MI LOF HW0 HWL RK0 RKL2 NSL TLL DHR ARK ANS ATL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof TLC as TB. apply rw_cells_bound in TB. cbn [cells_size csize Nat.add] in TB.
  eapply (rs_tail_walk (Z_to_bv 64 FB) gp tp F fc s6 s7 s8 s9 s10 s11 m2 HW RK NSP TLP iS ws junk nsv tlv POST);
    try eassumption; try lia; try apply munch_refl; try apply wmono_refl.
  intros m3 a0v y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 MU3 WM3 MI3 RR.
  eapply (rs_epi m3 (rs_tail ws (zlen ws) iS) a0v); [| | | | | exact MI3 | exact ERS | exact RR].
  - eapply rw_cells_transport; [exact FR | exact MU3 | exact WM3 |]. cbn [cells_size csize Nat.add disjoint_from]. lia.
  - eapply stk_transport_disjoint; [exact STK | exact MU3 | exact WM3 |]. cbn [disjoint_from]. lia.
  - lia.
  - eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU3]]. unfold sub_fp; intros ?x; cbn; intuition lia.
  - eapply wmono_trans; eassumption.
Qed.
End TOP.

Lemma rsx_u8arr_app : forall m A (l1 l2 : list byte), u8arr usegs m A (l1 ++ l2) ->
  u8arr usegs m A l1 /\ u8arr usegs m (A + zlen l1) l2.
Proof.
  intros m A l1 l2 [B [W0 [W1 W2]]]. apply (bytes_at_app usegs) in B as [B1 B2]. rewrite length_app in W1, W2.
  pose proof (proj1 B2) as A2. split; split; try assumption.
  - split; [lia | split; [lia | intros i Hi; apply W2; lia]].
  - split; [lia | split; [lia | intros i Hi; replace (A + zlen l1 + i) with (A + (zlen l1 + i)) by lia; apply W2; lia]].
Qed.

Lemma rsx_u8arr_app_inv : forall m A (l1 l2 : list byte), u8arr usegs m A l1 -> u8arr usegs m (A + zlen l1) l2 ->
  u8arr usegs m A (l1 ++ l2).
Proof.
  intros m A l1 l2 [B1 [V0 [V1 V2]]] [B2 [U0 [U1 U2]]]. split.
  - apply (bytes_at_app usegs). split; assumption.
  - rewrite length_app. split; [lia | split; [lia |]]. intros i Hi.
    destruct (Z.lt_ge_cases i (zlen l1)); [apply V2; lia |].
    replace (A + i) with (A + zlen l1 + (i - zlen l1)) by lia. apply U2; lia.
Qed.

Lemma rsx_bytes_sub : forall m A (l : list byte) k n, bytes_at usegs m A l -> 0 <= k -> 0 <= n -> k + n <= zlen l ->
  bytes_at usegs m (A + k) (firstn (Z.to_nat n) (skipn (Z.to_nat k) l)).
Proof.
  intros m A l k n B K N KN.
  rewrite <- (firstn_skipn (Z.to_nat k) l) in B. apply (bytes_at_app usegs) in B as [_ B].
  rewrite length_firstn in B. replace (A + Z.of_nat (Nat.min (Z.to_nat k) (length l))) with (A + k) in B by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat k) l)) in B. apply (bytes_at_app usegs) in B as [B _]. exact B.
Qed.

Lemma rsx_isz : forall c, 128 <= c < 256 -> ((c + -126) mod 18446744073709551616) ≫ 1 = (c - 126) / 2.
Proof.
  intros c H. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. f_equal; lia.
Qed.

Ltac rsx_zto o := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in (z =? PHUF_READ_STATS + o) in lazymatch d with true => fail | false => zstep end
  | _ => fail end).
Ltac rsx_side sp lo := first
  [ eassumption | lia
  | lazymatch goal with |- stk _ ?mm lo (bv_unsigned sp - 64 + 8) =>
      lazymatch goal with
      | Hj : rw_cells _ mm (bv_unsigned sp + -64) [CB 8 _] |- _ =>
          lazymatch goal with Hs : stk _ mm lo (bv_unsigned sp + -64) |- _ =>
            let SJ := fresh "SJ" in pose proof (stk_of_rw_cells usegs _ _ _ Hj) as SJ; cbn [cells_size csize Nat.add] in SJ;
            replace (bv_unsigned sp - 64 + 8) with (bv_unsigned sp + -64 + Z.of_nat 8) by lia;
            exact (stk_merge usegs _ _ _ _ Hs SJ ltac:(lia)) end end end
  | (unfold rres; split; [reflexivity | unfold ZSTD_error_srcSize_wrong, ZSTD_error_corruption_detected; lia]) ].

Ltac rsx_err ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HW RK NSP TLP W lo src SRCR e ERS :=
  rsx_zto 900;
  eapply (rs_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HW RK NSP TLP W lo src SRCR _ (Err e) (- e));
  [ | | | eassumption | eassumption | eassumption | exact ERS | ]; rsx_side sp lo.

Lemma huf_rstats_body : fse_decomp_stmt -> huf_rstats_stmt.
Proof.
  intros FDEC. unfold huf_rstats_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m HW RK NSP TLP S W src jh jr jw nsv tlv lo
         HWA HWL RKA RKL NSC TLC SRCB SRCR WKA WKL WSZ HW4 RK0 S7 W0 W4 RK4 NS4 TL4
         HWLO RKLO SLO WLO DHR DHS DHW DRS DRW DSW NSL TLL STK LOS SP16 SPH MI -> -> -> -> -> -> -> ->.
  unfold PHUF_READ_STATS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (MU : munch [(bv_unsigned sp - HUF_RSTATS_STACK, bv_unsigned sp); (HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4);
                      (TLP, TLP + 4); (W, W + 876)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  unfold HUF_RSTATS_STACK in LOS, MU.
  pose proof (proj1 STK) as LO0.
  assert (SP64 : 64 <= bv_unsigned sp) by lia.
  zstep. carve_frame 64%nat STK.
  do 9 zstep.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -64) (CB 8 _ :: _) |- _ =>
    apply (proj1 (rw_cells_app' usegs _ _ [_] _)) in H; destruct H as [FRj FRs] end.
  cbn [cells_size csize Nat.add] in FRs.
  replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp - 64 + 8) in FRs by lia.
  zstep. if_cases K0; zify_cond K0.
  { rsx_zto 900.
    assert (ERS : read_stats src = Err ZSTD_error_srcSize_wrong)
      by (unfold read_stats, FseNCount.Zlength; rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity).
    replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (- ZSTD_error_srcSize_wrong)) by reflexivity.
    eapply (rs_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HW RK NSP TLP W lo src SRCR
              _ (Err ZSTD_error_srcSize_wrong) (- ZSTD_error_srcSize_wrong)); [ | | | exact MU | exact WM | exact MI | exact ERS | ].
    all: rsx_side sp lo. }
  zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep.
  assert (BR0 : 0 <= Znth 0 src < 256) by (apply (Forall_Znth (fun c => 0 <= c < 256)); [exact SRCR | lia]).
  pose proof (src_rd usegs _ S src 0 SRCB ltac:(lia)) as RX.
  zstep. cbv beta. clear RX.
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
  rewrite sxb_eq by lia.
  destruct (Z.ltb_spec (Znth 0 src) 128) as [C128|C128].
  { rewrite lts_pos_byte by lia. cbv iota.
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
    rewrite land255 by lia.
    pose proof (rs_fse src ltac:(unfold FseNCount.Zlength; lia) ltac:(lia)) as RSF. unfold FseNCount.Zlength in RSF.
    if_cases K2; zify_cond K2.
    { assert (ERS : read_stats src = Err ZSTD_error_srcSize_wrong)
        by (rewrite RSF; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      rsx_err ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HW RK NSP TLP W lo src SRCR ZSTD_error_srcSize_wrong ERS. }
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
    if_cases K3; zify_cond K3; [exfalso; first [lia | Z.div_mod_to_equations; lia] |].
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in (z =? PFSE_DECOMP) in lazymatch d with true => fail | false => zstep end end).
    set (c0 := Znth 0 src) in *.
    rewrite <- (firstn_skipn 255 jh) in HWA. apply rsx_u8arr_app in HWA as [HWA1 HWZ].
    assert (LH1 : zlen (firstn 255 jh) = 255) by (rewrite length_firstn; lia).
    rewrite LH1 in HWZ.
    assert (LJZ : length (skipn 255 jh) = 1%nat) by (rewrite length_skipn; lia).
    destruct (skipn 255 jh) as [|b255 [|]] eqn:EJZ; try (cbn in LJZ; lia). clear LJZ.
    pose proof (rsx_bytes_sub _ _ _ 1 c0 SRCB ltac:(lia) ltac:(lia) ltac:(rewrite length_map; lia)) as SUBB.
    rewrite skipn_map, firstn_map in SUBB. change (Z.to_nat 1) with 1%nat in SUBB.
    set (sub := firstn (Z.to_nat c0) (skipn 1 src)) in *.
    assert (SUBL : zlen sub = c0) by (unfold sub; rewrite length_firstn, length_skipn; lia).
    assert (SUBR : Forall (fun c => 0 <= c < 256) sub)
      by (unfold sub; apply Forall_firstn, Forall_skipn; exact SRCR).
    clearbody sub.
    eapply evt_cut.
    { eapply FDEC with (DST := HW) (dcap := 255) (S := S + 1) (W := W) (wks := 876) (maxLog := 6) (src := sub)
                       (jd := firstn 255 jh) (jw := jw) (lo := lo);
        rewrite ?unsigned_lit by lia; unfold FSE_DECOMP_STACK;
        first [ eassumption | reflexivity | lia | (f_equal; lia) ]. }
    intros ms' PO. unfold fse_decomp_post, FSE_DECOMP_STACK in PO. rewrite !unsigned_lit in PO by lia. revert ms' PO.
    post_call usegs m0.
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
    destruct (fse_decompress_wksp_safe (repeat 0 256) 255 sub 6 876 read_ncount_safe (Forall_all_bytes _ SUBR) ltac:(lia)
                ltac:(first [unfold FSE_MAX_TABLELOG; lia | split; [lia | vm_compute; intro; discriminate]])
                ltac:(unfold FseNCount.Zlength; rewrite repeat_length; lia)) as [(l & EL & LB & LL) | (e & EE)].
    - rewrite EL in POST. destruct POST as (R0 & jrest & HWo & LJR). subst x13. unfold FseNCount.Zlength in LL.
      if_cases K4; zify_cond K4; [| exfalso; first [lia | Z.div_mod_to_equations; lia]].
      eapply (rs_join ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HW RK NSP TLP W lo src SP64 SRCR
                _ l (jrest ++ [b255]) c0 jr nsv tlv).
      all: try (rewrite RSF, (proj2 (Z.ltb_ge _ _)) by lia; unfold huf_fse_weights; rewrite rs_wksp_size, EL; reflexivity).
      all: try (rewrite app_assoc; apply rsx_u8arr_app_inv; [exact HWo |
                replace (HW + zlen (map (Z_to_bv 8) l ++ jrest)) with (HW + 255) by (rewrite length_app, length_map; lia); exact HWZ]).
      all: try (eapply Forall_impl; [| exact LB]; cbv beta; intros; lia).
      all: try (rewrite length_app; cbn [length]; lia).
      all: try rsx_side sp lo.
    - rewrite EE in POST. destruct POST as (R0 & EB). subst x13.
      if_cases K4; zify_cond K4; [exfalso; first [lia | Z.div_mod_to_equations; lia] |].
      rsx_zto 900.
      repeat match goal with |- context [Z_to_bv 64 (?k - e)] =>
        lazymatch k with Zpos _ => replace (Z_to_bv 64 (k - e)) with (Z_to_bv 64 (- e)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) end end.
      assert (ERS : read_stats src = Err e)
        by (rewrite RSF, (proj2 (Z.ltb_ge _ _)) by lia; unfold huf_fse_weights; rewrite rs_wksp_size, EE; reflexivity).
      rsx_err ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HW RK NSP TLP W lo src SRCR e ERS. }
  { rewrite lts_neg_byte by lia. cbv iota.
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
    rewrite land255_neg by lia.
    set (c0 := Znth 0 src) in *.
    rewrite (rsx_isz c0) by lia.
    pose proof (rs_direct src ltac:(unfold FseNCount.Zlength; lia) ltac:(lia)) as RSD. unfold FseNCount.Zlength in RSD.
    fold c0 in RSD.
    replace ((c0 - 127 + 1) / 2) with ((c0 - 126) / 2) in RSD by (f_equal; lia).
    if_cases K2; zify_cond K2; rewrite ?(rsx_isz c0) in K2 by lia.
    { assert (ERS : read_stats src = Err ZSTD_error_srcSize_wrong)
        by (rewrite RSD; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      rsx_err ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HW RK NSP TLP W lo src SRCR ZSTD_error_srcSize_wrong ERS. }
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
          let d := eval vm_compute in (z =? PHUF_READ_STATS + 200) in lazymatch d with true => fail | false => zstep end
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let K := fresh "KD" in if_cases K; zify_cond K; try (exfalso; first [lia | Z.div_mod_to_equations; lia]) end).
    replace (c0 - 127) with (c0 + -127) in RSD by lia.
    assert (KK : 2 * ((c0 + -127 - 1) / 2) + 1 <= c0 + -127 <= 2 * ((c0 + -127 - 1) / 2) + 2 /\ (c0 - 126) / 2 = (c0 + -127 - 1) / 2 + 1)
      by (Z.div_mod_to_equations; lia).
    eapply dl_loop with (HW := HW) (S := S) (oSize := c0 + -127) (K := (c0 + -127 - 1) / 2) (src := src) (jh := jh)
                        (k := 0) (acc := []) (fuel := Datatypes.S (Z.to_nat (c0 + -127)))
                        (f := Z.to_nat ((c0 + -127 - 1) / 2 + 1)).
    all: try first [ reflexivity | eassumption | lia | (rewrite Z2Nat.id; lia) | (rewrite Nat2Z.inj_succ, Z2Nat.id; lia) | constructor ].
    all: try (unfold dl_inv; cbn [map app length skipn]; split; [eassumption | split; [eassumption | split; [apply munch_refl | split; [apply wmono_refl | eassumption]]]]).
    all: try (lazymatch goal with |- bytes_at _ _ _ _ /\ _ => idtac end;
              split; [eassumption | split; [apply munch_refl | split; [apply wmono_refl | eassumption]]]).
    all: try (intros m2 cells y5 y6 y7 y10 y11 y15 y16 y17 DLR LC FC INV2; destruct INV2 as (HWo & SRC2 & MU2 & WM2 & MI2);
      replace (2 * 0) with 0 in DLR by reflexivity;
      transport_after_call usegs m0 m2 MU2 WM2;
      assert (ZW : zlen (firstn (Z.to_nat (c0 + -127)) cells) = c0 + -127) by (rewrite length_firstn; lia);
      replace (Z_to_bv 64 (c0 + -127)) with (Z_to_bv 64 (zlen (firstn (Z.to_nat (c0 + -127)) cells))) by (rewrite ZW; reflexivity);
      assert (LJT : length (skipn (length cells) jh) = (256 - length cells)%nat) by (rewrite length_skipn; lia);
      set (jt := skipn (length cells) jh) in HWo, LJT; clearbody jt;
      rewrite <- (firstn_skipn (Z.to_nat (c0 + -127)) cells) in HWo; rewrite map_app, <- app_assoc in HWo;
      eapply (rs_join ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HW RK NSP TLP W lo src SP64 SRCR
                _ (firstn (Z.to_nat (c0 + -127)) cells) (map (Z_to_bv 8) (skipn (Z.to_nat (c0 + -127)) cells) ++ jt)
                ((c0 - 126) / 2) jr nsv tlv)).
    all: try (rewrite ZW, RSD, (proj2 (Z.ltb_ge _ _)) by lia;
              rewrite (proj2 (Z.leb_gt _ _)) by (try unfold HufPure_HufStats.HUF_SYMBOLVALUE_MAX; try unfold HUF_SYMBOLVALUE_MAX; lia);
              rewrite DLR; reflexivity).
    all: try (apply Forall_firstn; exact FC).
    all: try (rewrite length_app, length_map, length_skipn, LJT; lia).
    all: try rsx_side sp lo. }
Qed.

Lemma huf_rstats_proof : huf_rstats_stmt.
Proof. exact (huf_rstats_body fse_decomp_proof). Qed.
