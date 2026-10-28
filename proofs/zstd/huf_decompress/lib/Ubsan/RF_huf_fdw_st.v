(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model RF_huf_fdw_kit
  RF_huf_fdw_stl RF_huf_fdw_cut RF_huf_fdw_kit_dsym.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_fdw_st () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface7bitd_okC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_contC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_bitsK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6bd_ptrC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp>reload_dstreamI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_zeroI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic6eq_symK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD01K47Corelib4Init9Datatypes4prod01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:mul_div_leC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8readLE64C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes4andbK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dstatus_eqbC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit;le64v_rangeC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit5le64vC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm9land7_modC56Stdlib6ZArith6BinInt1Z6mod_leK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6leb_gtC57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init9Datatypes6lengthK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindK46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD00K47Corelib4Init9Datatypes4bool02K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus01K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus02I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus03I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega5Tauto4kind02I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8dt_cellsC56Stdlib6ZArith6BinInt1Z6to_natK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_nbBitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp>read_bits_fastC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9read_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_symbolC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dc_newStateK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9skip_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:decode_symC47Corelib5Lists7ListDef3nthI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6dtable00I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm6sm_invC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC46Stdlib5Lists4List7map_appC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_assocC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic2ex01C47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega8ZifyInst7Inj_Z_Zc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st4st_KC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm7dec_invC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init3Nat3mulC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib5Lists4List6concatC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model@fse_cells_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6shiftlI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit;cell_rd_symC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics5Riscv3Sem4core01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C56Stdlib6ZArith6BinInt1Z7add_0_rI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit6out_sbC46Stdlib5Lists4List2tlC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm7zlen_tlC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit>unsigned_byte'C45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface<BIT_MASK_TABC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface>fse_cell_bytesK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5instr05C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit;readLE64_okK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC45stdpp9bitvector;definitions7bv_wrapC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_stl7st_ld1fC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_stl7st_ld1pC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountKZSTD_error_dstSize_tooSmallK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_stl7st_ld2fC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_stl7st_ld2pC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kitAzx32_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop0:C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6de_outC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s1C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_bdC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s2c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st8tl_body2I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec00c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st<st_loop_stmtc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st6res_okC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit:cell_rd_nsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit:cell_rd_nbC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kit7mask_rdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st5st_x2c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_stBdecode_sym_not_errK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st<reload_factsc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st=sm_inv_weakenc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st;tail_loop_SC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm6bd_regc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st5st_c2c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st5st_r2c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st>reload_not_errC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kit8zx16_litK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9tail_loopK4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize03C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface<ZEROFILLED_FC56Stdlib6ZArith6BinInt1Z9add_assocc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st5st_x1c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st5st_h2c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_st5st_r1C47Corelib4Init9Datatypes7nat_ind".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma st_rle_ok : forall bs q c, Forall (fun c => 0 <= c < 256) bs -> readLE64 bs q = Ok c ->
  0 <= q /\ q + 8 <= zlen bs /\ 0 <= c < 2^64.
Proof.
  intros bs q c BY R. unfold readLE64 in R.
  destruct ((0 <=? q) && (q + 8 <=? FseNCount.Zlength bs)) eqn:E; [|discriminate].
  apply andb_true_iff in E as (E1 & E2). apply Z.leb_le in E1, E2. try unfold FseNCount.Zlength in E2.
  injection R as <-. pose proof (le64v_range bs q BY) as L. unfold le64v in L. lia.
Qed.

Lemma reload_facts : forall bs d st d', Forall (fun c => 0 <= c < 256) bs -> bitd_ok bs d -> bd_bits d <= 64 ->
  reload_dstream bs d = Ok (st, d') ->
  bitd_ok bs d' /\ bd_bits d' <= bd_bits d /\ bd_zero d' = false /\ dstatus_eqb st Overflow = false.
Proof.
  intros bs [c b p z] st d' BY (C1 & C2 & C3 & C4 & C5 & C6) HB RL.
  cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
  unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
  replace (64 <? b) with false in RL by (symmetry; apply Z.ltb_ge; lia).
  assert (SH : Z.shiftr b 3 = b / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (Q : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b /\ b mod 8 = b - 8 * (b / 8)) by (Z.div_mod_to_equations; lia).
  assert (L7 : Z.land b 7 = b mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  cbv beta zeta in RL. rewrite ?SH in RL. revert RL.
  destruct (Z.leb_spec 8 p) as [P8|P8]; [|destruct (Z.eqb_spec p 0) as [P0|P0]; [|destruct (Z.ltb_spec (p - b / 8) 0) as [PN|PN]]];
    intro RL; cbv iota beta zeta in RL.
  all: try (lazymatch type of RL with context [readLE64 ?b0 ?q0] =>
         destruct (readLE64 b0 q0) as [cv| | |] eqn:RD; cbn [bind] in RL; try discriminate;
         apply (st_rle_ok _ _ _ BY) in RD as (RD1 & RD2 & RD3) end).
  all: injection RL as <- <-; rewrite ?L7.
  all: try (destruct z; [specialize (C6 eq_refl); lia|]).
  all: unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero].
  all: repeat (match goal with |- _ /\ _ => split | |- _ -> _ => intro end); try reflexivity; try congruence; try lia.
  all: destruct (b <? 64); reflexivity.
Qed.

Lemma decode_sym_not_err : forall dt fast s d e, decode_sym dt fast s d <> Err e.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fdw_st ()) [] "p'0h01Hh12H0h22rbi002rbh31bi011bh41ch52e0h61mh71vh81dh92dth:1eh;4fasti024fasth<1pi031ph=1sh>1zi041zi052d'i067lowBitsi071rp;2p;1p;3p;4p;6g00L2j2UTg01Kaj12Tg014Aj2XTg00H>j2QTg00SBj2TTg00;6R0j2PTg00;VR1j1DTg01Lej1:Tg01MEj3WTg00K9j20Tg00S`j1ITg01NHj1@Tg01OMj2BTg01PWj2FTg01Q\j1;Tg01Raj19Tg00U:j28Tg012ej46Tg01Shj2?Tg00?7j3>Tg000Mj6CTg00fdj2VTg00\aj1<Tg0030j1=Tg003Uj1ATg006Zj2RTg00Loj23Tg005Wj1KTg0077j1JTg01Taj1OTg00Y<j2MTg00LOj2LTg00_ij2ETg01UXj2NTg00JYj4GTg01V]j4ZTg01Wcj4YTg01X?R2f2R3f1R4f0R5CYp=4g018kR6P6P4P5CGp=5P3g01;NR7P4P5CGp=7f5R8f4R9f3R:P3P4C6;>5#<p=1A>345#<p=SP6P6P4P5C6p=Hg01YBg019IR;g018MR</U3%29,X2,Q3'TP;P;1P66R=/P7R>#DR?P2P>P;%D2P5%:9f6R@#2AW<<<RA34RB,02%I2RCn01000000200001P67RDP>P;%DDREP@%@5RF,B9,0D1F9Fn0110200020000P0P6P7P?P5%;:%9:/84'5=7=5,0>n2001100000120106105X2DRGC6X421?>3RHE1P5P;P?PDP>P;PEP5%@BRI,B:,0D1F:In0110200020000P0P6P7P?P5f7RJ#:f9RK#2;4ARL#;%9L/84'5=7=5,0>n2001100000120106105RLX2DRMPHE1P9%::%28;4ARN#@RO,B3RPPDP0P6P71?>:RQ9S?LP5f8RL#:f:#2;4ARR#;%9R/84'5=7=5,0>RR1?>@5>?RSP?%:Kf;#2;4ARK#;%9K/83'5=7=4,0>P1P>p-0RKP5g01G5RTg01HlRUPUPUn101107000410000100000000X5?RVg01GQRW1?>JP5ECPU1VU5RXb1W0%<SeX37X>6P4P5O2n2001103000120104101b<P?PDP>10DPP0P6P7P?P5%:@%2L;4ARL#;%9L/84'5=7=5,0>n2001100000120106105X2DR@1?>4RPE1e1U<Og01EKR<#=RS#=#=#=#=RY#A,QO'TP;P;P?PDP>P6PDP;%D6P5%ASRS%:8%2J;4ARA#@RJ'R%A<R<'3RZ,06%I6R[n0100000020000%K8%=Y#ARY%J8'3%@LRL'3#O/MY'L/E5,06X66'HP6P7P51N8LCG,0DX76C6P0P6P7P?P5PRn2001100000120106105X2DPQE1P5%;B%9B%K:%J:,3Y/3I#O/MY'L1RSI/3<R<'E'8'51N:I57=,0>=>?HRIP?%;A%9A%K9%J9,3Y/3J#O/MY'LRY/EZ'8'51N9JRJ57=,0>PVPWPQP5ECPUPXb1W0%<IeP?PDP>P6PD106<1EY5,06X66RY'HP6P7P5PJCG,0DX76RJC6PMPHE1e%I>R<=>?HRIP?P<P1P>PKP5PUPUPTPUn101107000410000100000000X5?RTPWPQP5ECPUPXb1W0%<IeP?PDP>P6PD1H[YPJC6PMPHE1en0110100020101b3P?PDP>1F3OP@PPE1R@eP@en0110100020101P?P2P>102NPDP>P;PEP81B:F,0D1F:Fn0110200020000PGC6X42RGPPE1eA>?<PRFP?P<PTPWPHP5ECPUPXb1W0%<FeP?P2P>PCPGPPE1en0110100020100b3P9P:P3P4CZ1?>55S?eX:6X87X=6W;W9o"). Qed.

Lemma reload_not_err : forall bs d e, reload_dstream bs d <> Err e.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fdw_st ()) [] "p'0h01ch11Hh22H0h31bi001bh42e0h52bsh61dh71ei013nb'i021ri036resulti041xp;1p;2p;4p;3p;6g002Pj1aTg0030j14Tg003Uj15Tg0077j18Tg00H>j2FTg00;6R0j2ZTg00;VR1j1YTg005Wj1WTg009;j1?Tg00IWj4OTg00K9j23Tg00L2j2ATg008:j1TTg00LOj2KTg00Loj21Tg00_ij2STg00hij2XTg00MLj26Tg01Shj2DTg00?7j3:Tg00fdj2]Tg00\aj1=Tg00U:j22Tg014Aj2UTg00SBj2RTg015<j2>Tg006Zj2BTg00S`j1\Tg00<Oj2`Tg00JYj4LTg00Q^j2_Tg012ej4[Tg000Mj6^Tg01:IR2g01;NR3g01=0f0R4CLp=Vf3R5P2P3g01ABR6f2R7f1R8P4g01<PR9COCL'3p=7g018kR:P51_78P4C[p=@P2P3P8P4CLp=EP:P2P4g01BGR;CLp=QP:P2P4P6CLp=PP7P8P4P9COp=;A:784#=p=9f4R9P5P7g01GQP8P4E^p=C1278/>4p=H1684,27p=G1278/>4,65p=01>78,65,29/24p=I1295/27/28/24p=M13:4p=JP:P5P7P8C[=:94#=p=<P2P3P;P4CLp=N%a:g01EKR6#4R<#4R=#4R>#4R?#4R@#4#5RA%88'Fg019IRBPB1Z23RC#YRDPBPDP4%W5%85RE%?5RFg019iRGCO#V,3CRHPBPD%5>R>/AFPCP9%T6RI#5RJ,KERK,1FRLPCP4%89RM%TIRN#5RO'SRP%?9RQ1KMJRR'1RSC7X0:C@RTPBPDg018MRU,XFRVPBP21FEAP;g01F0REn0100000020000/E5,3CP0P:P2PDPB1Z:2RW1FLU%QF%PKn0100000020000PCf6RKf5RF#?RX/18%8KRY167>RZ'1%?KR[/175;4,E8,3CX0:C@n2001104000120101103n0100000020000R\n0100000020000n01000000200001DC7R]39P4%W7%87%?7R^PGCO#V,3C1DC85:DRGPDPHP1PCp-0RHP4g01G5R_g01HlR`P`P`n101102000410000100000000X4DRaP]P4DCP`1]`4Rbb2W1%=Ge1A>^PBPBPBPDP4PCPFPSPCP4%8FR^/SORG1K^JRc,1XRdC7X0:ReC@PBPD1XQUPBP21FMAP;PEn0100000020000/E9,3CRMP0P:P2PDPBPW1FSURf%QQ%PRn0100000020000PCf7RR11[8%8RRQ/1Z%?RRg/175;4,E8,3CX0:C@n2001104000120101103n0100000020000n01000000200001DC5R559DP41AUL12L>1U:9'A'RPBPBPDPCPB%Y:RLP41>dK%5<Rh/B>Ri%56R6=HdK3G%5?,BhR?12dhPK%4IRI#4#4Rj#5,BhRkPdPJPKC0DI%5@,BhR@Pd%5=R=PKC0%T<R<#4#4#4#5,BhRlPd%5<R<PKC0%4j#5,BhRjPd%5IRIPKC0%4N#4#4#5,BhRNPdPOPKC0DMRm#J%\:Rnn0100000020100PCP41SYO1KYJRo,1[RpC7X0:1DC9R9D<P4PC1>SFAHS6F7GiP?12ShPFPkPSPJPFC0DIP@PSP=PFC0PlPSP<PFC0PjPSPIPFC0PNPSPOPFC0DMRqPPPSC7=:D5RSPDPCPmPGPdC7PaP9P4DCP`Pbb2W1%=SePDPC%JqPeP5D<e%\CRq=:D5RSPDPqP1PCPHP4P`P`P_P`n101102000410000100000000X4DR_P9P4DCP`Pbb2W1%=SePDPCPnPeP5D<en0110001020100b3A9DT]RTePTePVPBPBPBPDP4PBP21F^AP;PEn0100000020000/EF,3CREP0P:P2PDPBPW1FdU%QX%Pcn0100000020000PCf8Rc11g8%8cR;/1Z%?cR^/175;4,E8,3CX0:C@n2001104000120101103n0100000020000=9D9P4A:DM5R5PDPEPaP9P4DCP`Pbb2W1%=5ePfPBPBP0P:P2PDPBPWP4%Q[%Pon0100000020000PCf9RW11^8%8W/1Z%?W/175;4,E8,3CX0:C@n20011040001201011031DCFRF59DP411XXRX,AU12X>1U:KRW'A'RPBPBPDPCPBPLP411ggRZ/>cAHZ6c7GiP?12ZhPcPkPZPJPcC0DIP@PZP=PcC0PlPZP<PcC0PjPZPIPcC0PNPZPOPcC0DMR2#JPnn010000002010016^>,1;11^^5;4#N,3CX0:1DCKR0D<P411[[Rf/>RAHf6R7GiP?12fhPRPkPfPJPRC0DIP@PfP=PRC0PlPfP<PRC0PjPfPIPRC0PNPfPOPRC0DMR516[>,1YR[;;f#N,3C=:DFREPD16g>,1QRM=;2Z#N,3CPaP0P4DCP`Pbb2W1%=EePDPC%J5A;4MZ#N,3CX0:RMPFD<eA:DqFRZPDPqP_P0P4DCP`Pbb2W1%=ZeRZPDPCPnPMPFD<en0110001020100b3PCPKPXA;4[f#N,3CX0:C@=9D9e1AUd12d>/AW'RPBPBPDPCPBPLP41KQJRL,1gRg/>cAHg6c7GiP?12ghPcPkPgPJPcC0DIP@PgP=PcC0PlPgP<PcC0PjPgPIPcC0PNPgPOPcC0DMRc#JPnn0100000020100PCP41K;JRB/6>,1;11^BC7X0:P0D<P4PC1>pRAHp6R7GiP?12phPRPkPpPJPRC0DIP@PpP=PRC0PlPpP<PRC0PjPpPIPRC0PNPpPOPRC0DMRR16o>,1YRYPpC7=:DFRoPDPCPc16L>,1QRQPgC7PaP0P4DCP`Pbb2W1%=oePDPC%JRPCP4PQPgC7X0:RgPFD<ePZPDPCPnPgPFD<en0110001020100b3PCPKPdPCP4PYPpC7X0:C@=9D9en0110000020101b3n0110000020001b3A9D\]en0110000020101b3n0110000020001b31`781DC459DeX7:X63W5o"). Qed.

(* [comment removed for export] *)
Definition hk (P : Prop) : Prop := P.

Local Ltac slia ::= slia_sep.
Ltac fixreg r v := let w := reg_val r in replace w with v by zeq.

Ltac fin_tac :=
  intros SP gp tp F fc m0 S DT DST dcap lo bs dt POST out o PRE HO HN HC K m1 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17
    y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 I STK;
  destruct PRE as (TL1 & TLC & COK & BYS & LOSP & SPA & SPH & S8 & SLO & DT0 & DTA & DTLO & DST4 & DSTLO & DCAP & DJ1 & DJ2 & DJ3);
  destruct I as ((junk & OUTA & LJ) & MU & WM & MI);
  wk.

Ltac fin_close K :=
  unfold fdw_K in K; eapply K; try eassumption;
  unfold dres; split;
  [ rewrite ?unsigned_lit by lia; rewrite ?Z.mod_small by lia; rewrite length_app; cbn [length]; lia
  | eexists; split; eassumption ].

Lemma fdw_fin1_proof : fdw_fin1_stmt.
Proof.
  unfold fdw_fin1_stmt, fdw_fin_at, fdw_fin_K, PFDW_FIN1. fin_tac.
  all: fin_close K.
Qed.

Lemma fdw_fin2_proof : fdw_fin2_stmt.
Proof.
  unfold fdw_fin2_stmt, fdw_fin_at, fdw_fin_K, PFDW_FIN2. fin_tac.
  all: fin_close K.
Qed.

Section ST.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
            (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis PRE : fdw_pre SP S DT DST dcap lo bs dt.

  Notation tl := (dt_tableLog dt).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation STH pc mm x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 64) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 DST)
         (Z_to_bv 64 (2^61)) (Z_to_bv 64 (-70)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1)
         (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (2^64 - 1 - BIT_MASK_TAB)) (Z_to_bv 64 2) (Z_to_bv 64 (DST + j + 1))
         (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - j))
         x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Definition TI (m1 : fmem) (out : list Z) (s1 s2 : Z) (d : bitD) : Prop :=
    exists jp, fdw_mem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp.

  Ltac open_pre :=
    pose proof PRE as (TL1 & TLC & COK & BYS & LOSP & SPA & SPH & S8 & SLO & DT0 & DTA & DTLO & DST4 & DSTLO & DCAP & DJ1 & DJ2 & DJ3);
    assert (HJ1 : hsep (DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST)) by exact DJ1;
    assert (HJ2 : hsep (DST + dcap <= S \/ S + zlen bs <= DST)) by exact DJ2;
    assert (HJ3 : hsep (DT + 4 + 4 * 2^tl <= S \/ S + zlen bs <= DT)) by exact DJ3;
    assert (P12 : 2 <= 2^tl <= 2^12) by (split; [change 2 with (2^1) at 1|]; apply Z.pow_le_mono_r; lia);
    assert (TBL : zlen (concat (map fse_cell_bytes (dt_cells dt))) = 4 * 2^tl)
      by (rewrite fse_cells_length; lia);
    assert (HJ4 : hsep (DT + 4 + 4 * 2^tl <= SP)) by (unfold hsep; lia).
  Ltac ti_open I :=
    destruct I as (jp & FS2 & FS1 & FBD & ((junk & OUTA & LJ) & MU & WM & MI) & TBB & SRC & STK);
    cbn [de_out de_s1 de_s2 de_bd] in *.

  Lemma bv_sub_mod : forall a b c M, M = 2^64 -> c = a - b -> Z_to_bv 64 (a mod M - b mod M) = Z_to_bv 64 c.
  Proof.
    intros a b c M -> ->. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite <- Zminus_mod. reflexivity.
  Qed.

  Lemma st_finA : forall m1 out o0 s1a s2 d1 o1 s2' d2 j0
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    TI m1 (out ++ [o0]) s1a s2 d1 -> 0 <= s2 < 2^tl -> 64 < bd_bits d1 < 2^30 -> 0 <= bd_cont d1 < 2^64 ->
    zlen out + 2 <= dcap -> 0 <= o0 < 256 ->
    decode_sym dt false s2 (mkBD (bd_cont d1) (bd_bits d1) (bd_ptr d1) true) = Ok (o1, s2', d2) ->
    fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok ((out ++ [o0]) ++ [o1])) ->
    evt usegs POST (STF 0x207b8 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (DST + zlen out + 1)) x19 x20 (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - zlen out))
                        x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I S2 HB HC HJ HO DEC K. open_pre. ti_open I. unfold bitdz_cells in FBD.
    assert (EL : zlen (out ++ [o0]) = zlen out + 1) by (rewrite length_app; cbn [length]; lia).
    wk.
    eapply evt_cut.
    { eapply (fse_dsym_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + 16) (SP + 48) DT S lo dt
                             s2 (mkBD (bd_cont d1) (bd_bits d1) (bd_ptr d1) true) jp o1 s2' d2).
      all: cbn [bd_cont bd_bits bd_ptr bd_zero]; rewrite ?unsigned_lit by lia.
      all: try (unfold bitdz_cells; cbn [bd_cont bd_bits bd_ptr bd_zero]).
      all: first [ eassumption | lia | (unfold cells_ok in COK; exact COK) | (right; lia) | (left; lia) | idtac ]. }
    unfold fse_dsym_post. post_call usegs m.
    pose proof (dsym_inv _ _ _ _ _ _ _ DEC) as (c & lb & _ & NTH & -> & _ & _ & _).
    assert (HO1 : 0 <= dc_symbol c < 256)
      by (unfold cells_ok in COK; rewrite Forall_forall in COK; apply (COK c (nth_error_In _ _ NTH))).
    wk.
    lazymatch goal with |- context [Z_to_bv 64 (?a mod ?M - ?b mod ?M)] =>
      rewrite (bv_sub_mod a b (DST + zlen (out ++ [o0]) - 1) M) by (reflexivity || lia) end.
    replace (Z_to_bv 64 (DST + zlen out + 1)) with (Z_to_bv 64 (DST + zlen (out ++ [o0]) - 1 + 1)) by (f_equal; lia).
    pose proof (fdw_fin1_proof SP gp tp F fc m0 S DT DST dcap lo bs dt POST (out ++ [o0]) (dc_symbol c) PRE
                  ltac:(lia) ltac:(lia) ltac:(lia) K) as FK.
    unfold fdw_fin_K, PFDW_FIN1 in FK. eapply FK; [|eassumption].
    unfold sm_inv. split; [eexists; split; eassumption|]. split; [eassumption|]. split; eassumption.
  Qed.

  Lemma st_finB : forall m1 out o0 o1 s1a s2 d1 o2 s1b d3 j0
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    TI m1 (out ++ [o0; o1]) s1a s2 d1 -> 0 <= s1a < 2^tl -> 64 < bd_bits d1 <= 2^29 -> 0 <= bd_cont d1 < 2^64 ->
    bd_zero d1 = false -> zlen out + 3 <= dcap -> 0 <= o0 < 256 -> 0 <= o1 < 256 ->
    decode_sym dt false s1a (mkBD (bd_cont d1) (bd_bits d1) (bd_ptr d1) true) = Ok (o2, s1b, d3) ->
    fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok ((out ++ [o0; o1]) ++ [o2])) ->
    evt usegs POST (STF 0x207ec m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (DST + zlen out + 1)) x19 x20 (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - zlen out))
                        x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I S1 HB HC BZ HJ HO HO' DEC K. open_pre. ti_open I. unfold bitdz_cells in FBD. rewrite BZ in FBD.
    assert (EL : zlen (out ++ [o0; o1]) = zlen out + 2) by (rewrite length_app; cbn [length]; lia).
    wk.
    eapply evt_cut.
    { eapply (fse_dsym_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + 32) (SP + 48) DT S lo dt
                             s1a (mkBD (bd_cont d1) (bd_bits d1) (bd_ptr d1) true) jp o2 s1b d3).
      all: cbn [bd_cont bd_bits bd_ptr bd_zero]; rewrite ?unsigned_lit by lia.
      all: try (unfold bitdz_cells; cbn [bd_cont bd_bits bd_ptr bd_zero]).
      all: first [ eassumption | lia | (unfold cells_ok in COK; exact COK) | (right; lia) | (left; lia) | idtac ]. }
    unfold fse_dsym_post. post_call usegs m.
    pose proof (dsym_inv _ _ _ _ _ _ _ DEC) as (c & lb & _ & NTH & -> & _ & _ & _).
    assert (HO1 : 0 <= dc_symbol c < 256)
      by (unfold cells_ok in COK; rewrite Forall_forall in COK; apply (COK c (nth_error_In _ _ NTH))).
    wk.
    lazymatch goal with |- context [Z_to_bv 64 (?a mod ?M - ?b mod ?M)] =>
      rewrite (bv_sub_mod a b (DST + zlen (out ++ [o0; o1]) - 2) M) by (reflexivity || lia) end.
    replace (Z_to_bv 64 (DST + zlen out + 1)) with (Z_to_bv 64 (DST + zlen (out ++ [o0; o1]) - 2 + 1)) by (f_equal; lia).
    pose proof (fdw_fin2_proof SP gp tp F fc m0 S DT DST dcap lo bs dt POST (out ++ [o0; o1]) (dc_symbol c) PRE
                  ltac:(lia) ltac:(lia) ltac:(lia) K) as FK.
    unfold fdw_fin_K, PFDW_FIN2 in FK. eapply FK; [|eassumption].
    unfold sm_inv. split; [eexists; split; eassumption|]. split; [eassumption|]. split; eassumption.
  Qed.

  Lemma dec_step : forall s d, 0 <= s < 2^tl -> 0 <= bd_bits d -> bd_bits d + tl < 2^31 ->
    exists c, nth_error (dt_cells dt) (Z.to_nat s) = Some c /\
      0 <= dc_symbol c < 256 /\ 0 <= dc_nbBits c <= tl /\ 0 <= dc_newState c /\ dc_newState c + 2^(dc_nbBits c) <= 2^tl /\
      decode_sym dt false s d =
        Ok (dc_symbol c,
            dc_newState c + Z.land (Z.shiftr (bd_cont d) ((bv_swrap 32 (0 - (bd_bits d + dc_nbBits c)) mod 2^64) mod 64))
                                   (2^(dc_nbBits c) - 1),
            skip_bits d (dc_nbBits c)).
  Proof.
    intros s d Hs Hb Hb2. pose proof PRE as (TL1 & TLC & COK & _).
    destruct (nth_error (dt_cells dt) (Z.to_nat s)) as [c|] eqn:N.
    2: { apply nth_error_None in N. lia. }
    pose proof (nth_error_In _ _ N) as IN. unfold cells_ok in COK. rewrite Forall_forall in COK.
    destruct (COK c IN) as (C1 & C2 & C3 & C4).
    exists c. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    unfold decode_sym, HufPure_FseDecomp.cell. unfold FseNCount.Zlength.
    replace ((0 <=? s) && (s <? Z.of_nat (length (dt_cells dt)))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite (nth_error_nth _ _ _ N). cbn [bind]. unfold read_bits.
    rewrite lookbits_mach by lia. reflexivity.
  Qed.

  Ltac znormh := repeat match goal with
    | H : context [bv_unsigned (zx16 (Z_to_bv 64 ?v))] |- _ => rewrite (zx16_lit v) in H by lia
    | H : context [Z.lor (Z.shiftl (?s + 256 * ?n) 16 mod ?M) ?w] |- _ => rewrite (cw_lor s n w M) in H by (reflexivity || lia)
    | H : context [Z.shiftr (Z.shiftl (?s + 256 * ?n) 16 mod ?M) 24] |- _ => rewrite (hi_nb s n M) in H by (reflexivity || lia)
    | H : context [Z.land (?w + 65536 * ?s + 16777216 * ?n) 65535] |- _ => rewrite (w_lo w s n) in H by lia
    | H : context [Z.shiftr (?w + 65536 * ?s + 16777216 * ?n) 16] |- _ => rewrite (w_hi w s n) in H by lia
    | H : context [bv_unsigned (sx32 (Z_to_bv 64 ?z))] |- _ => rewrite (sx32_lit2 z) in H by lia
    | H : context [bv_unsigned (zx32 (Z_to_bv 64 ?z))] |- _ => rewrite (zx32_lit2 z) in H by lia
    | H : context [bv_wrap 32 ?x] |- _ => rewrite (wrap32_small x) in H by (kn; lia)
    | H : context [bv_swrap 32 ?x] |- _ => rewrite (swrap32_small x) in H by (kn; lia)
    end.
  Ltac zlia := solve [ lia | znormh; kn; kb; lia ].

  Lemma land_mask_rng : forall x n, 0 <= x -> 0 <= n -> 0 <= Z.land x (2^n - 1) < 2^n.
  Proof.
    intros x n Hx Hn. rewrite Z.sub_1_r, <- Z.ones_equiv, Z.land_ones by lia. apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
  Qed.

  Lemma st_head : forall m1 out s1 s2 d j0 (x1 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    TI m1 out s1 s2 d -> 0 <= s1 < 2^tl -> 0 <= s2 < 2^tl -> bitd_ok bs d -> bd_bits d <= 2^29 -> zlen out + 2 <= dcap ->
    (forall o0 s1a d1 m2 (y23 y24 y25 y28 y29 y30 y31 : word), decode_sym dt false s1 d = Ok (o0, s1a, d1) ->
       TI m2 (out ++ [o0]) s1a s2 d1 -> 0 <= s1a < 2^tl -> 0 <= o0 < 256 -> 64 < bd_bits d1 < 2^30 ->
       0 <= bd_cont d1 < 2^64 ->
       evt usegs POST (STH 0x207b8 m2 x1 j0 (zlen out) y23 y24 y25 x26 x27 y28 y29 y30 y31)) ->
    (forall o0 s1a d1 m2 (y23 y24 y25 y28 y30 y31 : word), decode_sym dt false s1 d = Ok (o0, s1a, d1) ->
       TI m2 (out ++ [o0]) s1a s2 d1 -> 0 <= s1a < 2^tl -> 0 <= o0 < 256 -> bd_bits d1 <= 64 -> bitd_ok bs d1 ->
       evt usegs POST (STH 0x1feac m2 x1 j0 (zlen out) y23 y24 y25 x26 x27 y28 (Z_to_bv 64 (bd_bits d1)) y30 y31)) ->
    evt usegs POST (STH 0x1fe1c m1 x1 j0 (zlen out) x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    intros until x31. intros I S1 S2 BOK HB HJ KA KR. open_pre. pose proof BOK as (BC & BB & BP & BPE & BSM & BZ).
    destruct (dec_step s1 d S1 ltac:(lia) ltac:(lia)) as (c1 & NTH1 & CS1 & CN1 & CW1 & CW1' & DEC).
    rewrite (FseWalkKit.swrap32_small (0 - (bd_bits d + dc_nbBits c1))) in DEC by lia.
    assert (PN : 1 <= 2^(dc_nbBits c1)) by (pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c1) ltac:(lia) ltac:(lia)); lia).
    assert (U32 : u32 (bd_bits d + dc_nbBits c1) = bd_bits d + dc_nbBits c1) by (unfold u32; apply Z.mod_small; lia).
    ti_open I. unfold bitdz_cells in FBD. clear DJ1 DJ2 DJ3 BOK BSM.
    wk.
    all: try replace (Z_to_bv 64 (bd_bits d + dc_nbBits c1)) with (Z_to_bv 64 (bd_bits (skip_bits d (dc_nbBits c1))))
           by (cbn [skip_bits bd_bits]; rewrite U32; reflexivity).
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      first [ eapply (KA (dc_symbol c1) _ (skip_bits d (dc_nbBits c1)) mm)
            | eapply (KR (dc_symbol c1) _ (skip_bits d (dc_nbBits c1)) mm) ] end.
    all: first [ exact DEC
               | (exists jp; unfold fdw_mem; cbn [de_out de_s1 de_s2 de_bd]; split; [exact FS2|];
                  split; [rewrite (Z.add_comm (dc_newState c1)); exact FS1|];
                  split; [unfold bitdz_cells, skip_bits; cbn [bd_cont bd_bits bd_ptr bd_zero]; rewrite U32; exact FBD|];
                  split; [split; [eexists; split; eassumption|]; split; [eassumption|]; split; eassumption|];
                  split; [eassumption|]; split; eassumption)
               | (match goal with |- 0 <= _ + Z.land ?x _ < _ =>
                    pose proof (land_mask_rng x (dc_nbBits c1) ltac:(apply Z.shiftr_nonneg; lia) ltac:(lia)); lia end)
               | lia
               | (unfold bitd_ok, skip_bits; cbn [bd_cont bd_bits bd_ptr bd_zero]; rewrite U32;
                  repeat split; try lia; intros Hz; specialize (BZ Hz); lia)
               | (cbn [skip_bits bd_bits bd_cont bd_zero]; rewrite ?U32; first [lia | zlia]) ].
  Qed.

  Ltac cl_cell F := first [ exact F
    | lazymatch goal with |- rw_cells _ _ _ [C8 (Z_to_bv 64 (?a + ?b)); _] => rewrite (Z.add_comm a b); exact F end ].
  Ltac ti_close2 BZ1 U2 :=
    lazymatch goal with F2 : rw_cells _ _ (SP + 16) _, F1 : rw_cells _ _ (SP + 32) _,
                        FB : rw_cells _ _ (SP + 48) (_ :: _ :: CB 4 ?JP :: _) |- _ =>
    exists JP; unfold fdw_mem; cbn [de_out de_s1 de_s2 de_bd];
    split; [cl_cell F2 |];
    split; [cl_cell F1 |];
    split; [unfold bitdz_cells, skip_bits; cbn [bd_cont bd_bits bd_ptr bd_zero]; rewrite ?BZ1, ?U2; exact FB |];
    split; [split; [eexists; split; eassumption|]; split; [eassumption|]; split; eassumption|];
    split; [eassumption|]; split; eassumption end.

  Lemma st_mid : forall m1 out o0 s1a s2 d1 j0 (x1 x23 x24 x25 x26 x27 x29 x30 x31 : word),
    TI m1 (out ++ [o0]) s1a s2 d1 -> 0 <= s1a < 2^tl -> 0 <= s2 < 2^tl -> bitd_ok bs d1 -> bd_bits d1 <= 64 ->
    0 <= o0 < 256 -> zlen out + 2 <= dcap ->
    (dcap - 2 < zlen out + 1 -> fdw_K SP gp tp F fc m0 DST dcap lo POST (Err ZSTD_error_dstSize_tooSmall)) ->
    (zlen out + 3 <= dcap -> forall o1 s2a d2 o2 s1b d3, decode_sym dt false s2 d1 = Ok (o1, s2a, d2) -> 64 < bd_bits d2 ->
       decode_sym dt false s1a (mkBD (bd_cont d2) (bd_bits d2) (bd_ptr d2) true) = Ok (o2, s1b, d3) ->
       fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok ((out ++ [o0; o1]) ++ [o2]))) ->
    (forall o1 s2a d2 m2 (y23 y24 y25 y30 y31 : word), decode_sym dt false s2 d1 = Ok (o1, s2a, d2) ->
       TI m2 ((out ++ [o0]) ++ [o1]) s1a s2a d2 -> 0 <= s2a < 2^tl -> 0 <= o1 < 256 -> bd_bits d2 <= 64 ->
       bitd_ok bs d2 -> zlen out + 3 <= dcap ->
       evt usegs POST (STH 0x20030 m2 x1 j0 (zlen out) y23 y24 y25 x26 x27 (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (bd_bits d2))
                           y30 y31)) ->
    evt usegs POST (STH 0x1ffa0 m1 x1 j0 (zlen out) x23 x24 x25 x26 x27 (Z_to_bv 64 (S + 8)) x29 x30 x31).
  Proof using All.
    intros until x31. intros I S1 S2 BOK HB HO HJ KE KB KR. open_pre. pose proof BOK as (BC & BB & BP & BPE & BSM & BZ).
    destruct (dec_step s2 d1 S2 ltac:(lia) ltac:(lia)) as (c2 & NTH2 & CS2 & CN2 & CW2 & CW2' & DEC).
    rewrite (FseWalkKit.swrap32_small (0 - (bd_bits d1 + dc_nbBits c2))) in DEC by lia.
    assert (PN : 1 <= 2^(dc_nbBits c2)) by (pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c2) ltac:(lia) ltac:(lia)); lia).
    assert (BZ0 : bd_zero d1 = false) by (destruct (bd_zero d1) eqn:E; [specialize (BZ eq_refl); lia | reflexivity]).
    assert (U32 : u32 (bd_bits d1 + dc_nbBits c2) = bd_bits d1 + dc_nbBits c2) by (unfold u32; apply Z.mod_small; lia).
    assert (EL : zlen (out ++ [o0]) = zlen out + 1) by (rewrite length_app; cbn [length]; lia).
    assert (S2A : 0 <= dc_newState c2 + Z.land (Z.shiftr (bd_cont d1) ((0 - (bd_bits d1 + dc_nbBits c2)) mod 2^64 mod 64))
                                         (2^(dc_nbBits c2) - 1) < 2^tl)
      by (pose proof (land_mask_rng (Z.shiftr (bd_cont d1) ((0 - (bd_bits d1 + dc_nbBits c2)) mod 2^64 mod 64)) (dc_nbBits c2)
                        ltac:(apply Z.shiftr_nonneg; lia) ltac:(lia)); lia).
    ti_open I. unfold bitdz_cells in FBD. rewrite BZ0 in FBD. clear DJ1 DJ2 DJ3 BOK BSM BZ.
    set (o1l := out ++ [o0]) in *.
    wk.
    all: try (unfold o1l in *; clear o1l).
    all: try replace (Z_to_bv 64 (DST + zlen (out ++ [o0]))) with (Z_to_bv 64 (DST + zlen out + 1)) by (f_equal; lia).
    all: try replace (Z_to_bv 64 (bd_bits d1 + dc_nbBits c2)) with (Z_to_bv 64 (bd_bits (skip_bits d1 (dc_nbBits c2))))
           by (cbn [skip_bits bd_bits]; rewrite U32; reflexivity).
    - pose proof (KE ltac:(lia)) as KE'. unfold fdw_K in KE'. eapply KE'; try eassumption.
      split; [reflexivity | unfold ZSTD_error_dstSize_tooSmall; lia].
    - destruct (dec_step s1a (mkBD (bd_cont (skip_bits d1 (dc_nbBits c2))) (bd_bits (skip_bits d1 (dc_nbBits c2)))
                                   (bd_ptr (skip_bits d1 (dc_nbBits c2))) true) S1
                 ltac:(cbn [skip_bits bd_bits]; rewrite U32; lia) ltac:(cbn [skip_bits bd_bits]; rewrite U32; lia))
        as (c3 & NTH3 & CS3 & CN3 & CW3 & CW3' & DEC3).
      rewrite <- app_assoc in OUTA, LJ. cbn [app] in OUTA, LJ.
      eapply (st_finB _ out o0 (dc_symbol c2) s1a _ (skip_bits d1 (dc_nbBits c2))).
      + ti_close2 BZ0 U32.
      + exact S1.
      + cbn [skip_bits bd_bits]. rewrite U32. lia.
      + cbn [skip_bits bd_cont]. lia.
      + cbn [skip_bits bd_zero]. exact BZ0.
      + lia.
      + lia.
      + lia.
      + exact DEC3.
      + eapply KB; [lia | exact DEC | cbn [skip_bits bd_bits]; rewrite U32; lia | exact DEC3].
    - eapply (KR (dc_symbol c2) _ (skip_bits d1 (dc_nbBits c2))).
      + exact DEC.
      + ti_close2 BZ0 U32.
      + exact S2A.
      + lia.
      + cbn [skip_bits bd_bits]. rewrite U32. lia.
      + unfold bitd_ok, skip_bits. cbn [bd_cont bd_bits bd_ptr bd_zero]. rewrite U32, BZ0.
        repeat split; try lia; try (intros Hz; discriminate).
      + lia.
  Qed.
End ST.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
