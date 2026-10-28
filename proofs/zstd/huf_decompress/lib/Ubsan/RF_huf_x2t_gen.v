(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model
  RF_huf_x2t_model RF_huf_x2t_c1 RF_huf_x2t_kit_fill RF_huf_x2t_skc RF_huf_x2t_lv2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x2t_gen () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftrI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I45stdpp9bitvector;definitions2bv00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX2>fill_two_levelK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_c17x2f_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Logic8iff_reflC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model3ox2C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model6omergeI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model=omerge_lengthC45stdpp9bitvector;definitions;bv_unsignedK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model?rv_at_transportC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model5rv_atC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5oloadC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX26level2C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model8ftl_stepC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model8oload_OkC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shl32C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX26rv_idxC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX29store_runC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX2>level2_weightsC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model:omerge_nthC56Stdlib6ZArith4Znat5Nat2Z2idC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Arr9u8ro_readI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC46Stdlib9micromega;ZifyClasses5mkrelC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model8ftl_stopC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_lv28lv2_loopC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_gen:signed_anyC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model6land31C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model7shl32_1C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas8zload_okC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_c16d1_valI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model?build_x2_fieldsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_seqC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX29x2_nbBitsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26x2_lenC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_c16rep_h0C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_c1;le2_lo_cellC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_c16rep_h1C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_c1;le2_hi_cellC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_c16rep_h2C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_c16rep_h3K46Stdlib9micromega=RingMicromega5Psatz01C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX27ostore2C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model;store_run_SC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model:ostore2_OkC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model:ox2_lengthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib4Init3Nat3addC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem9upd_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model5oset2C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model9ox2_storeC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model<oset2_lengthK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model:rv_at_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C47Corelib4Init9Datatypes4andbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_lC46Stdlib4Bool4Bool>andb_false_iffC46Stdlib4Bool4Bool>negb_false_iffC46Stdlib4Bool4Bool=andb_true_iffC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission6Common6StrFun?land_align_downC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith4Znat5Z2Nat2idC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_skc:skC_chunksC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit2:sx32_smallC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit>unsigned_byte'C47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX28build_x2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission6Common6StrFun@u8arr_store_ok_nK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_2'I47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission6Common6StrFunAu8arr_write_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem@upd_bytes_lengthC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5msize02C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5msize01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop0:".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma shl_shr32 : forall DE, 0 <= DE < 2^32 -> ((DE ≪ 32) mod 18446744073709551616) ≫ 32 = DE.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_gen ()) [] "h07__arithh14__ffh28__varmaph35__with41zh54__x1h62DEh71Hp;2p;1p;3p;4p;6p;8p;7g0000j29Tg000Lj10Tg0011j14Tg001Oj2dTg001lj2BTg002Hj2>Tg002cj2PTg003@j2=Tg003`j2<Tg004@j33Tg004Zj2cTg0057j1]Tg005Wj1WTg0067j1VTg006Uj1TTg0073j1STg007^j26Tg008Aj1RTg008_j3QTg009Bj45Tg009mj6OTg00:Qj2MTg00;3j2LTg00;Mj2KTg00<9j3HTg00<Xj4ITg00=Jj3JTg00=kj3FTg00>Tj6:Tg00?2j2ETg00?[j1;Tg00@:j27Tg00@cj3DTg00ALj3?Tg00B5j2@Tg00Baj2bTg00CMj3CTg00Cmj2aTg00DKj2\Tg00Dnj1XTg00EPj3YTg00F3j8ZTg00FWj3[Tg00G:j2UTg00GZj3^Tg00HCj7_Tg00Hgj7`Tf0R0#0#0#0#0p=G%00#0p=N%00#0#0#0#0#0#0#0p=1f1R1g00IKR2g00IjR3P3g00JJR4P0g00JjF_p=2g00KJR5P1g00KhP0C5p=8f2R6P2P3P3P4P1P0F`p=Ag00LOR7/90g00LmR8#0R9#4R:%G9R9#4R;'dR<,B0'>R=P51P1<R>%09#N#1#1#1R?#1#1#1#1#4R@,=0/<;=356X45P5P>1<0;=356X45P51c><A3506X45g00MRRA#]RB%WARC%V5RD%T5RE%S5RFP2P3P3P4P5165:%R95Q5R9g00N>1657R:C5,2FEO1MF4RGP0P6g00NeRHg00OERI'L1K06=3HIdAH571CIRIb1b2b3A35<7g00Oe[P0b09J1<1<>;PBPCPDPE165;,8:,2FPGPIb1b2b3197;P0b0RD9F>;E:1=>@%4?,E5g00PBR?#;R<,755D5175?R?5?5g00PaRH'@%;<#;,759?5?/@H,b?=CAB5CAPC1a51PEPFP2P3P3P41\58R8,8:,2FP5P8g00QMR4P9C5,2F5AF%X3AY589R8,8:,2FP5P8P4165@C5,2F5AFGZPGPIb1b2b3X55197>1B>@'>\=^55P0P6P1O2b09[>@E:1U1;A^1;DE:W7X65o"). Qed.

Lemma signed_any : forall x, - 2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_gen ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh61Hh71xp;1p;2p;3p;4p;8p;6p;7g000Lj10Tg0011j17Tg00R4j14Tg001Oj2CTg00RYj1[Tg0000j2=Tg001lj2<Tg002Hj2;Tg008Aj18Tg00S6j2BTg004@j33Tg00S]j2?Tg00T:j2>Tg0057j1VTg005Wj1UTg00Cmj2TTg006Uj1RTg0073j1PTg00DKj2OTg007^j26Tg00TWj3GTg00U:j3FTg009Bj42Tg00:Qj2HTg00;3j2ITg00;Mj2DTg00<9j3JTg00<Xj4KTg003@j2LTg008_j3MTg00U]j2NTg00Dnj1ATg00F3j8QTg00FWj3@Tg00>Tj69Tg00V@j2STg00Vfj2ZTg00WNj2YTg00HCj7XTg00Hgj7WTf0R0#0#0#0#0p=E%00#0#0#0#0#0#0#0p=1f1R1g00IKR2g00IjR3P3g00JJR4P0g00JjFXp=5f2R5P2P3P3P4P1P0FWp=:g00KJR6g00LmR7#0R8#7R9%47#4#4#4#4R:#7'CR;#[/=01<0;';R;P6%08#ER8#8R</B1R=A3605X56P6%08#1#1#1#1#1#1#1R8#7R>,?1R?1>0>=365X56g00MRR@#VRA%U@R@1T61RB%R6RC%P6RDP61O67R7166>RE5G6RF=F6Eg00N>P7C2'51HD4REP0P5g00NeRGg00OERH'I1D05=3GHdg00LORH=J61CKRGb2b3b4X061?0>/>>=360^06P0P5O1b1%08#7R8,L?PAP@PBPCPDP2P3P3P4P61669%8:5M6R:,N6g00KhR9P7C2,5DP6P7g00QMR7P:C2,5D5:D%A3P6166HP9PFC2,5DP6PFP71668C2,5D5:DGQPEPGb2b3b4X061=H?1<?8';\;^06P0P5P1O2b19@?8E9A36=1e1S<1,Z<1Y<1E9W6W7o"). Qed.

Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
  ?omerge_length, ?ox2_length, ?upd_bytes_length in *.

Lemma gn_shl2 : forall x, x ≪ 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma gn_lx63 : forall o, 0 <= o < 9223372036854775808 -> (Z.lxor o 9223372036854775808 <? 9223372036854775808) = false.
Proof. intros o Ho. change 9223372036854775808 with (2 ^ 63). rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia. Qed.

Local Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | clear H ]
  | H : stk segs m ?lo2 ?hi2 |- _ =>
      first [ apply (stk_write segs m lo2 hi2 a bs) in H; [ | lia | simpl_sizes; simpl_arr_sizes; lia ]
            | clear H ]
  end.

Local Ltac pnorm U :=
  repeat match type of U with
         | context [Z.lxor ?o 9223372036854775808 <? 9223372036854775808] => rewrite (gn_lx63 o) in U by lia
         end;
  repeat match type of U with
         | context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b)) in U by (rewrite ?Z.mod_small by lia; lia)
         end;
  cbn in U.

Local Ltac pchk U := exfalso; rewrite ?gn_shl2 in U; rewrite ?signed_small2 in U by lia;
  first [ lia | (Z.div_mod_to_equations; lia)
        | (pnorm U; first [discriminate | lia | (Z.div_mod_to_equations; lia)]) ].

Local Ltac cgo stops := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) stops) in lazymatch b with false => zstep end
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 82516 else _) _ _ _ _) =>
      rewrite ?sx32_small by lia; rewrite ?zx32_small2 by lia; rewrite ?swrap32_small by lia; rewrite ?gn_shl2;
      let U := fresh "U" in if_cases U; zify_cond U; [pchk U |]
  | |- evt _ _ (MS _ _ (if _ then _ else Z_to_bv 64 82516) _ _ _ _) =>
      rewrite ?sx32_small by lia; rewrite ?zx32_small2 by lia; rewrite ?swrap32_small by lia; rewrite ?gn_shl2;
      let U := fresh "U" in if_cases U; zify_cond U; [| pchk U]
  end).


Lemma gn_uu : forall cons sym1, 1 <= cons <= 12 -> 0 <= sym1 < 256 ->
  Z.lor (Z.lor (cons * 65536 + 16777216) sym1 ≪ 32 mod 18446744073709551616)
        (Z.lor (cons * 65536 + 16777216) sym1 mod 4294967296)
  = (cons * 65536 + 16777216 + sym1) * 4294967297.
Proof.
  intros cons sym1 HC HS.
  rewrite (lor_add (cons * 65536 + 16777216) sym1 8) by (try change (2 ^ 8) with 256; lia).
  rewrite (Z.mod_small _ 4294967296) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite (Z.mod_small _ 18446744073709551616) by lia.
  rewrite (lor_add _ _ 32) by (change (2 ^ 32) with 4294967296; first [lia | rewrite Z.mod_mul by lia; reflexivity]).
  lia.
Qed.

Local Ltac cellw DT4 ARR u c :=
  xh DT4 ARR (4 * u); cgo (@nil Z); xh DT4 ARR (4 * u + 2);
  replace (Z.to_nat (4 * u)) with (4 * Z.to_nat u)%nat in ARR by lia;
  replace (Z.to_nat (4 * u + 2)) with (4 * Z.to_nat u + 2)%nat in ARR by lia;
  lazymatch type of ARR with
  | context [upd_bytes (upd_bytes (ox2 ?jt ?cells) _ [?a; ?b]) _ [?d; ?e]] =>
      replace [a; b] with [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)] in ARR
        by (match goal with H : x2_seq c = _ |- _ => rewrite H end; reflexivity);
      replace [d; e] with [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)] in ARR
        by (match goal with H : x2_nbBits c = _, H2 : x2_len c = _ |- _ => rewrite H, H2 end; reflexivity);
      rewrite (ox2_store cells jt (Z.to_nat u) c) in ARR by lia
  end;
  cgo [0x147c4].

Section GEN.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (v96 v104 v112 v120 v128 v144 v152 v160 v168 v224 : word).
  Variables (m : fmem) (DT SY WK cons T nbb wEnd minW mwr e1 len1 lo : Z) (sorted : list (option Z)) (js jt : list byte)
    (ncells : nat) (rs0 rv : list Z).
  Variable POST : machine_state -> Prop.
  Notation S := (bv_unsigned sp).
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis HDT2 : DT mod 2 = 0.
  Hypothesis HNC : Z.of_nat ncells <= 4096.
  Hypothesis HSYE : SY = WK + 736.
  Hypothesis HWK : 0 < WK /\ WK + 2124 <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= WK \/ WK + 2124 <= DT + 4.
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ WK + 2124 <= lo /\ lo <= S - 48 /\ S + 400 <= 2^47.
  Hypothesis HT : 1 <= T <= 12.
  Hypothesis HNBB : 2 <= nbb <= 13.
  Hypothesis HWE : 2 <= wEnd <= nbb.
  Hypothesis HCONS : 1 <= cons <= 11.
  Hypothesis HMW : minW = Z.max 1 mwr /\ mwr = cons + nbb - T /\ minW < wEnd.
  Hypothesis HLEN : len1 = 2 ^ (T - cons) /\ 1 <= T - cons <= 11.
  Hypothesis HE1 : e1 <= 256.
  Hypothesis LRS : length rs0 = 15%nat.
  Hypothesis HRSV : forall w, 1 <= w <= wEnd - 1 -> 0 <= Znth w rs0 <= Znth (w + 1) rs0 /\ Znth (w + 1) rs0 <= 256.
  Hypothesis LRV : length rv = 156%nat.
  Variable PRV : Z -> Prop.
  Hypothesis HPRV : forall w, minW <= w <= wEnd - 1 -> PRV (rv_idx cons w).
  Hypothesis HRVR : forall w, minW <= w <= wEnd - 1 -> 0 <= Znth (rv_idx cons w) rv < 2^31.
  Hypothesis RSA0 : u32arr usegs m (WK + 676) (map (Z_to_bv 64) rs0).
  Hypothesis RVA0 : rv_at m WK rv PRV.
  Hypothesis FR0 : rw_cells usegs m (S + 88)
    [C8 (Z_to_bv 64 (DT + 20)); C8 v96; C8 v104; C8 v112; C8 v120; C8 v128;
     C8 (Z_to_bv 64 (WK + 52 * cons + 4 * minW)); C8 v144; C8 v152; C8 v160; C8 v168;
     C8 (Z_to_bv 64 (WK + 4 * minW)); C8 (Z_to_bv 64 (wEnd - minW)); C8 (Z_to_bv 64 (nbb - minW + cons));
     C8 (Z_to_bv 64 (4 * minW)); C8 (Z_to_bv 64 (cons * 65536 + 16777216)); C8 (Z_to_bv 64 (4 * minW)); C8 v224;
     C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 mwr); C8 (Z_to_bv 64 minW); C8 (Z_to_bv 64 (wEnd - 1));
     C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 len1)].
  Notation W3 := [(DT + 4, DT + 4 + 4 * Z.of_nat ncells); (lo, S); (S + 280, S + 288)].
  Notation INV m1 dt := (x2g_inv m m1 W3 DT SY js jt sorted ncells lo S dt
                         /\ exists j, rw_cells usegs m1 (S + 280) [CB 8 j]).
  Notation ST pc mm s start x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x21 x24 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 T) sp gp tp x5 x6 x7 (Z_to_bv 64 (- (WK + 52 * cons) - 1)) (Z_to_bv 64 T) x10 x11 x12 x13
             x14 x15 (Z_to_bv 64 start) x17 (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) x20 x21 (Z_to_bv 64 (52 * cons))
             (Z_to_bv 64 (- (WK + 676) - 1)) x24 (Z_to_bv 64 s) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma gen_loop : forall f s dt start m1 r
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x21 x24 x26 x27 x28 x29 x30 x31 : word),
    fill_two_level f dt s e1 start len1 T cons minW wEnd rv sorted rs0 nbb = Ok r ->
    Z.of_nat f = e1 - s + 1 -> 0 <= s < e1 -> 0 <= start -> start + len1 * (e1 - s) <= 4096 -> INV m1 dt ->
    (forall m2 dt' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y17 y20 y21 y24 y26 y27 y28 y29 y30 y31 : word),
       r = dt' -> INV m2 dt' ->
       evt usegs POST (ST 0x14498 m2 e1 (start + len1 * (e1 - s)) y5 y6 y7 y10 y11 y12 y13 y14 y15 y17 y20 y21 y24 y26
                         y27 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x14660 m1 s start x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x21 x24 x26 x27 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros s dt start m1 r x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x21 x24 x26 x27 x28 x29 x30
      x31 HF Hf Hs Hst Hlen INV CONT; [lia|].
    destruct INV as ((ARR & LDT & SYB & STK & MU & WM & MI) & j0 & SL).
    cbn [fill_two_level] in HF. rewrite (proj2 (Z.eqb_neq s e1) ltac:(lia)) in HF.
    apply bind_Ok_inv in HF as (sym & OL & HF). apply oload_Ok in OL as (OL & NS).
    apply bind_Ok_inv in HF as (dt2 & HL2 & HF).
    pose proof (HSYR _ _ NS) as SYM.
    pose proof (rw_cells_transport usegs _ m m1 _ _ FR0 MU WM ltac:(cbn; lia)) as FR.
    assert (TAIL : forall dt1 m2 (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y24 y27 y28 y29 y30 y31 : word),
      level2_weights (Z.to_nat wEnd) dt1 start minW wEnd T cons rv sorted rs0 nbb sym = Ok dt2 ->
      x2g_inv m m2 W3 DT SY js jt sorted ncells lo S dt1 -> rw_cells usegs m2 (S + 280) [C8 (Z_to_bv 64 start)] ->
      evt usegs POST (MS (mkR (Z_to_bv 64 T) sp gp tp y5 y6 y7 (Z_to_bv 64 (- (WK + 52 * cons) - 1)) (Z_to_bv 64 T)
                            y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 SY) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 sym) y21
                            (Z_to_bv 64 (52 * cons)) (Z_to_bv 64 (- (WK + 676) - 1)) y24 (Z_to_bv 64 s)
                            (Z_to_bv 64 (DT + 4 + 4 * start)) y27 y28 y29 y30 y31)
                         F (Z_to_bv 64 0x147c4) fc None m2 (seg_rom usegs))).
    { intros dt1 m2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y24 y27 y28 y29 y30 y31 HW I2 SL2.
      destruct I2 as (ARR2 & LDT2 & SYB2 & STK2 & MU2 & WM2 & MI2).
      pose proof (rw_cells_transport usegs _ m m2 _ _ FR0 MU2 WM2 ltac:(cbn; lia)) as FR2.
      zstep. cgo (@nil Z).
      if_cases B9; zify_cond B9; rewrite !signed_any in B9 by lia; [exfalso; lia|].
      cgo [0x147e0].
      assert (HST4 : start <= 4096) by nia.
      eapply lv2_loop with (m := m2) (DT := DT) (SY := SY) (WK := WK) (cons := cons) (T := T) (nbb := nbb) (wEnd := wEnd)
        (start := start) (sym1 := sym) (minW := minW) (lo := lo) (sorted := sorted) (js := js) (jt := jt) (ncells := ncells)
        (rs0 := rs0) (rv := rv) (PRV := PRV) (f := Z.to_nat wEnd) (w2 := minW) (dt := dt1) (m1 := m2).
      all: try exact HW.
      all: try lia.
      all: first [ exact HSYR | exact HRSV | exact HPRV | (intros w Hw; specialize (HRVR w Hw); lia)
                 | exact (u32arr_transport usegs _ m m2 _ _ RSA0 MU2 WM2 ltac:(rewrite length_map, LRS; cbn; lia))
                 | exact (rv_at_transport _ m m2 WK rv PRV RVA0 MU2 WM2 ltac:(cbn; lia))
                 | exact (conj ARR2 (conj LDT2 (conj SYB2 (conj STK2 (conj (munch_refl _ m2) (conj (wmono_refl usegs m2) MI2))))))
                 | idtac ].
      intros m3 dt' z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z19 z28 z29 z30 z31 HR I3. subst dt'.
      destruct I3 as (ARR3 & LDT3 & SYB3 & STK3 & MU3 & WM3 & MI3).
      assert (SUB : sub_fp [(DT + 4, DT + 4 + 4 * Z.of_nat ncells); (lo, S)] W3)
        by (intros x HX; cbn [outside] in *; tauto).
      pose proof (munch_trans _ m m2 m3 MU2 (munch_weaken _ _ m2 m3 SUB MU3)) as MU4.
      pose proof (wmono_trans usegs m m2 m3 WM2 WM3) as WM4.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ SL2 MU3 WM3 ltac:(cbn; lia)) as SL3.
      pose proof (rw_cells_transport usegs _ m m3 _ _ FR0 MU4 WM4 ltac:(cbn; lia)) as FR3.
      clear FR2 SL2.
      cgo (@nil Z).
      rewrite (swrap32_small (start + len1)) by nia.
      destruct (rw_cells_forget usegs m3 (S + 280) _ SL3) as (j3 & SL4). cbn [cells_size csize] in SL4.
      assert (INV3 : INV m3 dt2)
        by exact (conj (conj ARR3 (conj LDT3 (conj SYB3 (conj STK3 (conj MU4 (conj WM4 MI3)))))) (ex_intro _ j3 SL4)).
      if_cases K; zify_cond K.
      - apply (IH (s + 1) dt2 (start + len1) m3 r); [exact HF | lia | lia | lia | nia | exact INV3 |].
        intros m4 dt' w5 w6 w7 w10 w11 w12 w13 w14 w15 w17 w20 w21 w24 w26 w27 w28 w29 w30 w31 HR4 I4.
        replace (start + len1 + len1 * (e1 - (s + 1))) with (start + len1 * (e1 - s)) by ring.
        exact (CONT m4 dt' w5 w6 w7 w10 w11 w12 w13 w14 w15 w17 w20 w21 w24 w26 w27 w28 w29 w30 w31 HR4 I4).
      - assert (EE : s + 1 = e1) by lia.
        zstep.
        assert (r = dt2) as ->.
        { destruct f as [|f]; [lia|]. cbn [fill_two_level] in HF. rewrite EE, Z.eqb_refl in HF.
          injection HF as <-. reflexivity. }
        replace (start + len1) with (start + len1 * (e1 - s)) by (replace (e1 - s) with 1 by lia; ring).
        rewrite EE.
        exact (CONT m3 dt2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl INV3). }
    zstep. cgo [0x146a0].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (sy_rd mm SY js sorted s sym SYB HJS HLS ltac:(lia) NS) as RD end.
    cgo (@nil Z).
    rewrite byte_lit by lia.
    unfold level2 in HL2.
    if_cases B1; zify_cond B1; rewrite !signed_any in B1 by lia.
    - assert (EM : minW = 1) by lia.
      rewrite EM, Z.ltb_irrefl in HL2. cbn [bind] in HL2. rewrite <- EM in HL2.
      exact (TAIL dt m0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 (conj ARR (conj LDT (conj SYB (conj STK (conj MU (conj WM MI))))))
               SL).
    - assert (EM : minW = mwr) by lia.
      rewrite (proj2 (Z.ltb_lt 1 minW) ltac:(lia)) in HL2.
      assert (LS : shl32 1 (Z.land (T - cons) 31) = Ok len1).
      { unfold shl32. change 31 with (Z.ones 5). rewrite (Z.land_ones (T - cons) 5) by lia. change (2 ^ 5) with 32.
        rewrite (Z.mod_small (T - cons) 32) by lia.
        replace ((0 <=? T - cons) && (T - cons <? 32)) with true
          by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        unfold u32. rewrite Z.mul_1_l. rewrite Z.mod_small; [destruct HLEN as (-> & _); reflexivity|].
        destruct HLEN as (-> & HL). split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
      rewrite LS in HL2. cbn [bind] in HL2.
      apply bind_Ok_inv in HL2 as (dt1 & HS1 & HL2).
      apply bind_Ok_inv in HS1 as (skip & LK & HS1). apply load_Ok in LK as (LK & ->).
      cgo (@nil Z).
      rewrite (gn_uu cons sym) by lia.
      set (c := build_x2 sym cons 0 1) in *.
      destruct (build_x2_fields sym cons 0 1 SYM ltac:(lia) ltac:(lia) ltac:(left; reflexivity)) as (CS & CN & CL).
      rewrite Z.eqb_refl in CS. fold c in CS, CN, CL.
      destruct (sk_le2 cons sym ltac:(lia) SYM) as (Q0 & Q1 & Q2 & Q3).
      if_cases B2; zify_cond B2.
      + rewrite (proj2 (Z.eqb_eq len1 2) ltac:(lia)) in HS1.
        cbn [store_run] in HS1.
        apply bind_Ok_inv in HS1 as (d1 & O1 & HS1). apply ostore2_Ok in O1 as (K1 & E1).
        assert (L1 : length d1 = ncells) by (rewrite E1, oset2_length; [exact LDT | lia]).
        apply bind_Ok_inv in HS1 as (d2 & O2 & HS1). apply ostore2_Ok in O2 as (K2 & E2).
        assert (L2 : length d2 = ncells) by (rewrite E2, oset2_length; [exact L1 | lia]).
        injection HS1 as <-.
        cgo (@nil Z).
        cellw (DT + 4) ARR start c. rewrite <- E1 in ARR.
        cellw (DT + 4) ARR (start + 1) c. rewrite <- E2 in ARR.
        exact (TAIL d2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2
                 (conj ARR (conj L2 (conj SYB (conj STK (conj MU (conj WM MI)))))) SL).
      + rewrite (proj2 (Z.eqb_neq len1 2) ltac:(lia)) in HS1.
        cgo (@nil Z). if_cases B3; zify_cond B3.
        * rewrite (proj2 (Z.eqb_neq len1 4) ltac:(lia)) in HS1.
          unfold rv_idx in HS1.
          set (skip := Znth (cons * 13 + minW) rv) in *.
          pose proof (HRVR minW ltac:(lia)) as SKR. unfold rv_idx in SKR. fold skip in SKR.
          pose proof (rv_at_transport _ m m0 WK rv PRV RVA0 MU WM ltac:(cbn; lia)) as RV0.
          pose proof (rv_at_read m0 WK rv PRV (cons * 13 + minW) (wa (WK + 4 * (cons * 13 + minW))) RV0
                        (HPRV minW ltac:(lia)) ltac:(lia) eq_refl) as RDK.
          fold skip in RDK.
          cgo (@nil Z).
          rewrite sx32_small by lia.
          if_cases B4; zify_cond B4.
          -- assert (SK0 : skip = 0)
               by (match goal with H : (_ && _)%bool = false |- _ => apply andb_false_iff in H;
                     destruct H as [H|H]; apply Z.ltb_ge in H; lia end).
            rewrite SK0 in HS1. cbn in HS1. injection HS1 as <-.
            cgo [0x147c4].
            exact (TAIL dt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2
                     (conj ARR (conj LDT (conj SYB (conj STK (conj MU (conj WM MI)))))) SL).
          -- assert (SK1 : 0 < skip) by lia.
            cgo [0x14748].
            rewrite Z2Nat.inj_mul in HS1 by (try apply Z.div_pos; lia). change (Z.to_nat 8) with 8%nat in HS1.
            pose proof (store_run_Ok _ _ _ _ _ HS1 ltac:(lia)) as (LR1 & BR1).
            assert (NPOS : (0 < Z.to_nat ((skip + 7) / 8))%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id; Z.div_mod_to_equations; lia).
            specialize (BR1 ltac:(lia)). rewrite Nat2Z.inj_mul, Z2Nat.id in BR1 by (apply Z.div_pos; lia).
            rewrite <- (sk_uu cons sym ltac:(lia) SYM).
            replace (Z_to_bv 64 0) with (Z_to_bv 64 (start - start)) by (f_equal; lia).
            eapply skC_chunks with (m := m0) (DT := DT) (SY := SY) (cons := cons) (sym1 := sym) (st := start) (skip := skip)
              (sorted := sorted) (js := js) (jt := jt) (ncells := ncells) (n := Z.to_nat ((skip + 7) / 8)) (c := c) (dt1 := dt)
              (v := start) (vend := start + 8 * ((skip + 7) / 8)) (m1 := m0) (dtR := dt1).
            all: first [ reflexivity | exact HS1 | exact HJT | exact HJS | exact HLS | exact NPOS
                       | exact (conj ARR (conj LDT (conj SYB (conj (munch_refl _ m0) (conj (wmono_refl usegs m0) MI)))))
                       | (rewrite Z2Nat.id by (apply Z.div_pos; lia); lia)
                       | (Z.div_mod_to_equations; lia) | lia | idtac ].
            intros m3 y5 y6 (A3 & L3 & SB3 & M3 & WM3' & MI3).
            assert (SUB : sub_fp [(DT + 4, DT + 4 + 4 * Z.of_nat ncells)] W3) by (intros x HX; cbn [outside] in *; tauto).
            pose proof (stk_transport_disjoint usegs _ m0 m3 lo S STK M3 WM3' ltac:(cbn; lia)) as STK3.
            pose proof (munch_trans _ m m0 m3 MU (munch_weaken _ _ m0 m3 SUB M3)) as MU3.
            pose proof (wmono_trans usegs m m0 m3 WM WM3') as WM3.
            pose proof (rw_cells_transport usegs _ m0 m3 _ _ SL M3 WM3' ltac:(cbn; lia)) as SL3.
            exact (TAIL dt1 m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2
                     (conj A3 (conj L3 (conj SB3 (conj STK3 (conj MU3 (conj WM3 MI3)))))) SL3).
        * rewrite (proj2 (Z.eqb_eq len1 4) ltac:(lia)) in HS1.
          cbn [store_run] in HS1.
          apply bind_Ok_inv in HS1 as (d1 & O1 & HS1). apply ostore2_Ok in O1 as (K1 & E1).
          assert (L1 : length d1 = ncells) by (rewrite E1, oset2_length; [exact LDT | lia]).
          apply bind_Ok_inv in HS1 as (d2 & O2 & HS1). apply ostore2_Ok in O2 as (K2 & E2).
          assert (L2 : length d2 = ncells) by (rewrite E2, oset2_length; [exact L1 | lia]).
          apply bind_Ok_inv in HS1 as (d3 & O3 & HS1). apply ostore2_Ok in O3 as (K3 & E3).
          replace (start + 1 + 1) with (start + 2) in K3, E3, HS1 by lia.
          assert (L3 : length d3 = ncells) by (rewrite E3, oset2_length; [exact L2 | lia]).
          apply bind_Ok_inv in HS1 as (d4 & O4 & HS1). apply ostore2_Ok in O4 as (K4 & E4).
          replace (start + 2 + 1) with (start + 3) in K4, E4, HS1 by lia.
          assert (L4 : length d4 = ncells) by (rewrite E4, oset2_length; [exact L3 | lia]).
          injection HS1 as <-.
          cgo (@nil Z).
          cellw (DT + 4) ARR start c. rewrite <- E1 in ARR.
          cellw (DT + 4) ARR (start + 1) c. rewrite <- E2 in ARR.
          cellw (DT + 4) ARR (start + 2) c. rewrite <- E3 in ARR.
          cellw (DT + 4) ARR (start + 3) c. replace (start + 2 + 1) with (start + 3) in E4 by lia. rewrite <- E4 in ARR.
          exact (TAIL d4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2
                   (conj ARR (conj L4 (conj SYB (conj STK (conj MU (conj WM MI)))))) SL).
  Qed.

End GEN.
