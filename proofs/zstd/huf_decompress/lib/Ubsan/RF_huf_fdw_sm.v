(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model RF_huf_fdw_kit
  RF_huf_y4_kit_reload RF_huf_fdw_kit_dsym RF_huf_fdw_cut RF_huf_fdw_smb RF_huf_fdw_smc RF_huf_fdw_fil.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_fdw_sm () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit5le64vC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK47Corelib7Numbers7BinNums8positive01K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedI47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit<le64_lbu_rawC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC56Stdlib6ZArith6BinInt1Z9add_assocK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr09C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC46Stdlib5Lists4List2tlI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:decode_symC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8dt_cellsC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6to_natK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell01C47Corelib5Lists7ListDef3nthK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_nbBitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9read_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_symbolC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dc_newStateC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_contC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6bd_ptrC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_zeroK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD01I47Corelib4Init5Logic2ex00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3maxK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega5Tauto8GFormula06C46Stdlib5Lists4List>nth_error_nth'I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9look_bitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9skip_bitsC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit=lookbits_machC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C47Corelib4Init5Logic7f_equalC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC56Stdlib6ZArith6BinInt1Z9mod_smallC35stdpp7tactics<f_equal_helpK47Corelib4Init5Logic2ex01C46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6shiftrK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega:ZMicromega;ZArithProof01I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6dtable00c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm6sm_invc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm7dec_invC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC47Corelib4Init3Nat3mulC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List6concatC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model@fse_cells_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit:cell_rd_nbC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit:cell_rd_nsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit;cell_rd_symK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kit7mask_rdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le4C47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit6out_sbc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm7zlen_tlC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_srlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC46Stdlib5Lists4List9app_assocC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kitAzx32_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7div_modC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kit8zx16_litC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_land_lC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5inr64C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litK46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit>unsigned_byte'C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface<BIT_MASK_TABK4ELinuxProcessSemantics5Riscv5Instr5msize03C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface<ZEROFILLED_FC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface>fse_cell_bytesK4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_bdC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp>reload_dstreamc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm7ml_bodyI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus00c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm5sm_okC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6de_outc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm4sm_KC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s2C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5de_s1K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3dec01C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_tbl_iface7bitd_okC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dstatus_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC46Stdlib4Bool4Bool>negb_false_iffC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm9dec_factsC46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm;main_loop_SC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8readLE64c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm6sm_okrc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm7sm_dec4K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9main_loopC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus04K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I46Stdlib5Lists4List6Exists00K46Stdlib9micromega5Tauto4kind02K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus02K5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7dstatus03C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit;readLE64_okK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit;le64v_rangec5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm9land7_modc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm8sm_afterc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm5sm_ldC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC56Stdlib6ZArith6BinInt1Z6leb_gtc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_sm6bd_regC56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriK4ELinuxProcessSemantics5Riscv5Instr5instr03K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z4lxorK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section LE64.
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bs : list Z) (POST : machine_state -> Prop).
  Hypothesis SRC : bytes_at usegs m S (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.

  Notation ST pc x8 x9 x12 x17 x18 x22 x31 :=
    (MS (mkR ra sp gp tp t0 t1 t2 x8 x9 a0 a1 x12 a3 a4 a5 a6 x17 x18 s3 s4 s5 x22 s7 s8 s9 s10 s11 t3 t4 t5 x31)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Ltac ldb0 p k :=
    let RX := fresh "RX" in
    pose proof (src_rd usegs m S bs (p + k) SRC ltac:(lia)) as RX;
    rewrite ?Z.add_assoc, ?Z.add_0_r in RX;
    zstep; cbv beta; clear RX.

End LE64.

Lemma land7_mod : forall x, Z.land x 7 = x mod 8.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fdw_sm ()) [] "h07__arithh14__ffh28__varmaph35__with41xh51zp;1p;2p;3p;4p;7p;6g002Cj10Tg003ij11Tg00Dcj1=Tg00\6j26Tg00\Sj22Tg00@ej34Tg00?_j23Tg01S3j1<Tg01SQj2;Tg00:Tj1:Tg00;4j17Tg00<2j18Tg00<nj19Tg00=Lj1GTg00>Zj25Tg00hjj4FTg00iUj7ETg00?=j2DTg00@9j2?Tg00A?j3>Tg00A^j4@Tg005dj2ATg01Soj3BTg0019j6CTg01BOR0P0f0R1g01LWR2#0R3#1%=2#1R2'6'2f1R4%03#0#1R3'29401X501213,30%<2,;1g01M<R3#:%73%80%90%G0R3g01Bmg01CLR5P5g01ClR5P0g01A<R6,50g01DL1502CFg01E3FE1D35P1f2R5g01J3R3g01MhR7'31?15=437dA>064C@b1b2b31A62P1b09B12ECW4o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Section SM.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x19 x20 x23 x24 x25 x26 x27 : word).               (* [comment removed for export] *)
  Variables (m0 : fmem) (S TB DST dcap tl : Z) (bs : list Z) (dt : dtable).
  Variable POST : machine_state -> Prop.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells dt) = 2^tl.
  Hypothesis HCOK : cells_ok tl (dt_cells dt).
  Hypothesis TBB : bytes_at usegs m0 TB (concat (map fse_cell_bytes (dt_cells dt))).
  Hypothesis SRC : bytes_at usegs m0 S (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis HS : 8 <= S /\ S + Z.max 8 (zlen bs) + 8 <= 2^64.
  Hypothesis HTB : 0 < TB /\ TB + 4 * 2^tl <= 2^64.
  Hypothesis HDST : 3 <= DST /\ DST + dcap < 2^64 /\ 0 <= dcap <= 255.
  Hypothesis DJ1 : DST + dcap <= TB \/ TB + 4 * 2^tl <= DST.
  Hypothesis DJ2 : DST + dcap <= S \/ S + zlen bs <= DST.
  Variable SP : Z.
  Hypothesis HSPV : 4096 <= SP /\ SP + 192 <= 2^47.
  Hypothesis DJF : DST + dcap <= SP /\ S + zlen bs <= SP /\ TB + 4 * 2^tl <= SP.
  Definition sm_box (P : Prop) : Prop := P.

  Lemma sm_lo16 : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
    Z.land (ns + 65536 * sy + 16777216 * nb) 65535 = ns.
  Proof.
    intros sy nb ns A B C. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
    symmetry. apply (Z.mod_unique _ _ (sy + 256 * nb)); lia.
  Qed.

  Lemma sm_sw : forall n b, 0 <= n + b < 18446744073709551616 ->
    bv_swrap 32 (0 - (n + b) mod 18446744073709551616) = bv_swrap 32 (0 - (b + n)).
  Proof.
    intros n b H. rewrite Z.mod_small by lia. rewrite (Z.add_comm n b). reflexivity.
  Qed.

  Ltac sm_nrm := fd_zx; rewrite ?fd_nb in * by lia; rewrite ?fd_w in * by lia; rewrite ?sm_lo16 in * by lia;
    rewrite ?sm_sw in * by lia; rewrite ?fd_land in * by lia.
  Ltac sm_fix c B E :=
    sm_nrm;
    try replace (dc_nbBits c + B) with (B + dc_nbBits c) in * by lia;
    lazymatch type of E with ?sn = ?ns + ?L => replace (L + ns) with sn in * by (rewrite E; ring) end;
    clear E.

  (* [comment removed for export] *)
  Lemma dec_inv : forall s d o s' d', decode_sym dt false s d = Ok (o, s', d') -> 0 <= bd_bits d <= 2^30 ->
    exists c, nth_error (dt_cells dt) (Z.to_nat s) = Some c /\ 0 <= s < 2^tl
      /\ 0 <= dc_symbol c < 256 /\ 0 <= dc_nbBits c <= tl /\ 0 <= dc_newState c /\ dc_newState c + 2^(dc_nbBits c) <= 2^tl
      /\ o = dc_symbol c
      /\ s' = dc_newState c + Z.land (Z.shiftr (bd_cont d) ((bv_swrap 32 (0 - (bd_bits d + dc_nbBits c)) mod 18446744073709551616) mod 64))
                                    (2^(dc_nbBits c) - 1)
      /\ d' = mkBD (bd_cont d) (bd_bits d + dc_nbBits c) (bd_ptr d) (bd_zero d).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fdw_sm ()) ["SM"] "p'0h04__p1h14__x1h22Hah34__p2h44__x2h51Hh63H28h77__arithh87__sat30h97__sat31h:7__sat32h;7__sat33h<7__sat34h=4__x3h>1ch?4cstrh@5cstr0hA3z28hB4__ffhC7__sat35hD8__varmaphE5__withF4__p3hG7__sat29hH7__sat36hI1ni001nhJ1EhK1RhL4__x4hM4__x5hN1ehO1mi011mhP2rbi022rbhQ1xi031xhR3H29hS2R1hT2R2hU4__p4hV2b1hW2b2hX2d'i042d'hY7defaulthZ1li051lh[1oh\2s'h]1vh^3z29h_2COh`4HCOKha2Hbhb2NEhc7__sat37hd7__sat38he1bi061bhf1di071dhg5lemmahh1ri081rhi1si099dc_nbBitsi0:;dc_newStatei0;9dc_symboli0<8dt_cellsi0=;dt_fastModei0>;dt_tableLogi0?2l'i0@7lowBitsi0A3nthi0B1pi0C2x'i0D1yi0E2y'i0F1zp%0p&0p&1p;2p;1p;4p;3p;7p;5p;6p;8p;<g00I4S00k20<Tg01];S01k10>Tg01^4k40lTg00@ej35Tg01_:j1iTg002Cj14Tg003ij1?Tg00Dcj1YTg00\6j28Tg005dj23Tg01`=k112Tg01aAk210Tg01b<j2JTg01bYj2jTg00?_j2sTg01c7R0j1@Tg01cWk30mTg01dZk408Tg01e6j2fTg01eok10kTg01fhj12Tg01gmk20FTg01i2j1<Tg01j7j1:Tg004Gj2=Tg01k>j4FTg00BPk10fTg00F5k20ATg01l6j1DTg002hk103Tg01UCj2rTg01m9j1XTg01n;j1[Tg01o>j4Zk30Rk20Qk10|Tg020@j2mTg00b;R1j20Tg020Zk20pTg021;k209Tg021Xk20oTg00`XR2j29Tg0228k20nTg004dk20MTg022XR3k20LTg005DR4k10KTg009ok10HTg0230k207Tg023Rj2zTg023lk20GTg00`0j2TTg00a4j3STg00C2j1eTg024Ik10ETg024gk20jTg025Hk30iTg0261k20DTg00:Tk10hTg00;4S02k10CTg00;Tj2oTg00<2k10gTg00<nk10eTg00=Lk10dTg00>Zk20BTg008Tk10cTg00>7j2aTg026Zk70bTg00?=k20aTg00@9k20`Tg00A?k30_Tg00A^k40^Tg01Y4k40?Tg027>k50]Tg027ak30\Tg028Bk30[Tg028Yk20ZTg0292k30YTg029ck30XTg02:Ek50WTg02:`k20VTg02;ej2_Tg0152j4tTg00aXk30TTg00hGk311Tg02<jk40~Tg00cQj6pTg02>1k104Tg02>hk60;Tg02?Ek20}Tg02?fk20STg02@Gk30{Tg02@jk80:Tg01?kj4UTg02AGk40zTg00cmk20yTg02Aak30xTg02B?k20PTg00\Sj2}Tg02Bfk20OTg01SQk20NTg01Y_m<0uTg01Wlm<0tTg02CFk30sTg02Cok20vTg00CQk30rTg00<Pk40wTg00hjj4qTg00iUj7|Tg00j]j8yTg01VGk60qTg00j9k705Tf4R5f3R6g02D[R7g01BOR8P8f2R9f1R:Ctf0R;Ct'fp=Ag01A<R</3:/0;p=P209<;p=]g02E]R=@0x:;p=l13<919:;'0p=C%4;#4p=w13<;p=11=9:/3;p=W%i:/=;p=I%4;#4#4#4p>0U%4;#4#4#4#4#4#4#4p=kf6R>f5R?1r<6-0P5/}9/}:+0O00N;'=p=GA57:;p=MA589:/0;p=R10:;,09p=H10:;,09,06,05p=Vg01J3R@g01MhS0375;p=720G<;p=h1s8;p=gP8g01ITS04P8P8P0P5P4P6g02F`P9P:P;N<0up>0JQ04P8P3P4P2g02GMP?P5P6P9P:P;N<0tp>0I19<;p=;A58:;p=6A58;<p>0620D8;p=cB0s8:;p=Eg02Go-0v;p=dg01M<R2@0r:;p=bP8P9P:P;H0wp=O20B8;p=^P9g01BmR4g01CLR3P3g01ClR0P8P:g01ESRAP;Cqg01E3RBF|p=nP9P4P3P3P0P8P:g01DLRCP;CqPBF|p=NP>P4P3P3P0P?P5P6P4P3P3P0P9P:P;GyGyp=KP:P4P3P3P0P;J0qp=QP8P:g01\TP;Cqp=xP6P4P3P3P0P9P:P4P3P3P0P;PBF|K05p=BP:P4P3P3P0P;PBF|p>0@P9P4P3P3P0P:P;K05p=>109:/0;p>021r<;-0P:p=u1}9:/};p=~189:/r;p=L20O9:00N;p>01P8P:PCP;Cqp=`P8P:PAP;Cqp>00P6P4P3P3P0P9P:P;Gyp>0=13:;,09p=\19:;,09p=vP?P4P3P3P0P5P4P3P3P0P6P9K05P:P;Gyp={20<88RA00<7RC$0>RBp,2dtS05g01GmS06P5P6H0lPCPAP9P:P;DA35%i5RDg01LWRE#4RF#?RG%YES07#Y#YS08#4S09#?RH'8S0:,3D'P%]>Q05$12RD-10=RI,J>'jP@1s@;f7RJ#]1JJI'j=5@;P@f9RK#]1JKI'j=5@;P=PCP@&0>=P:P=f:RL#@PDB0m<<<S0;H08,f=&0k=S0<n010000002000020<87RMPC%2;RN-0FLQ00P8P7PBP;PCPA%<6S0=%:6S0>/=:P;DAn200110200012010@104XPMROCFX>=S0?CFPCPAf8RPPJP>DAS0@55B&0f=RQf<RR#@,lD20A=;RS35p,2tlRT,8GRU9CRR%<;RV%4FS0A#4RW#wS0B#4RX#wRY#?RZ7CVS0C13NT,PNS0D%:;S0E#1R[Q0E18GNR\;WUR]Q0Ef;R^#DR_Q0B$03R`1I^NRa%wY$0U#k#kS0F#wS0G#k#k#k#k#?RY%?XRX%?ERb,r\S0HFGP_Pa%X^%[^CZ,MP5RK9RLV3HDVX>=,m=S0I]J]KP:%]P1JPI'jS0J#7P=PCP=%@KPDQ0;H08,f=PMPC20FKNPOCFX>=S0KCFPCPAPJP>P?DAS0L55BP11j:;#7%79RO%7:Ra'0[R_%7;,0a1j9:#7Ra[%76/0O\a20p:;P:n2001000000120000000XW@XV@P_^W@^V@P;%]^R_1J^IRaP9O3%7_%7a'0P1%]R#71JRI#7f>Ra#@,lD=5QSACaaUQ0CQ0DQ0Ef=R_#DROP`1I_NR\PYPXQ0HFGPOP\%X_%[_CZ,ML5R^9RRV9H[]DVX>=,m=P;%]a#7f?S0M/JI#7P1209:;#7139:[R\13:;2099:#7RO[1369\O20o:;P:n2001000000120000000XO8XI8P\^O8^I8P;P<fAR\P9O3%1\P11J:;#7199:[R119:;1J9:#7RO[1969\O20n:;P:n2001000000120000000XO8XI8P1^O8^I8P;fCS0NPIP6O3Q0N/9IP=fDRI#@PDQ0;H08P=P=PDfER1#@S0OQ0;Q0O20M=DRO+0L%h1Rc&0KORd'9Q0OPcP;XQ8S0P%h;XQ8S0QP1P1%g1I0JPOPd%gdS0RJ0Ip,2bs-0M8Rc$0HRe&0KcRc#1Rf&0HORg%1dRhfGRi-07<%;i%hiS0S/6i'013i<Q0S$06'0'zfHRj#hP8%?WRW007cRk19Wc20GWcRl/6c'013cW16lW'0'zRWPlP81TGXRc%;GRm%1X18GXRn#;[[Ro%1GRpg01OlRqASGX:UW2Rr%1n\q^2pRn1TGHS0T%1HQ0:#;[\mRsASGH:VqX2pRHQ0:#1\q^2pRt1TGTRu%1T%;U[\mRvASGT:VqX2pRw%1U\q^2pRxp-0Ryg01NHRz#eS0U#eR{#eS0V#eR|#eR}#e#cS0W%c}S0X&0EE-0j8%c{S0Y60i820D8zS0Z'E'E'E#dQ0X%c|S0[Q0Z'ES0\'E#d&0h2R|'b'b&0C2S0]1o85&0g8R27O9S0^1o8?S0_?O?29O267O:&0e8S0`&0d8RzPz20B8<R{%^GS0a5nz&0c3R}PzQ07,a8R~9Nz{P}Q0A,a8S0A9nz{FKP}PzPzP4P3P3P0Pz1QzJS0bPz1a8ERE%YF#Y,a8R3'xCBPz1QzPS0cPz1xE{CBK0bP}Pz1a8FRF9nz3P}PzANz{3P}PzQ0A,xF-0@zP}Pz%^bS0d=Nz~S0e1QzKS0f5>zP}AnzEFS0gFKFKFK20az0R0P;P9Q03,s@20`;9#7dB0_8<:H0^R3bBbDbEX18X48X=8XL8XM8X0yX3yWFS03%16%;?[\m16:?,0>&06:,0J'z19>6%1J16?J13bJ/0R19>J[[[[[[^18^48^=8^L8^M8^0y^3y^FyS0hP;Q07#4S07#4#?S0i,3TS0jfRR4/3<%;4P4PUPTPdPKP9PLPaf@S0kp,6HCELLSS0lp,3HTLS0mO>b7b8b9b:b;b<bCb^bRbAb6b@b?H0?I0]Q0O,lD=5QSQ0CQ0D10[]3HX>=S0O>0\=DS0nB0[=;DQ0OP:O1[^Q=R4+0ZQ0n@0Y4;WgQ0O>0X=Dp,4HCOKO2P4P;P9P=%@iR4PDQ0;20L4OQ0S/9dP4Q0SQ0PQ0QPiPi%giI0JPOPdQ0RJ0IPePfPgPhfIRO-07<%;O%hOR4/6O'013O<&064'0'zfJR4#hP8PkPWPlP8PcPoPrPnQ0TPsPHPtPuPvPwPxQ03Q0hP;Q0jfTS0h/3<Q0h#;Q0hPUPTPdPKP9PLQ0kfBS0hQ0lQ0mO>b7b8b9b:b;b<bCb^bRbAb6b@b?H0?I0WO2b`%<:R<#119<Z%2:R<#113<T%::S03Q0318G<;WU'P402402&0>8S03fFR<%29S0R+0VQ03PMPCP8PMP;P8P7P;%25S0Q,_jS0PCt,fMX]8CFQ00P8P7PBP;PCPA%<>S0S%:>S0O/=:P;DAn200110200012010@104XPMCFPCPAP<P1PIDAS0n55BWhP_%D<Q0R,I<,u`?~YXQ0R=LGb401,f8S03P<Q0RPePfPgPhPkPWPlP8Q08#YS08#?S0R,TGQ0R#1Q0R,8GS0o#;[\mQ0R=SG:VqX2pQ0o#1\q^2pPcPoPrPnQ0TPsPHPtPuPvPwPx%2aS0R,TGQ0M#2S0p#1Q0k#2,8G#;[\m%2\S0k=SG:VqX2pQ0k,8GS0q#1\q^2pQ0XQ0V#cQ0U#cQ0Z'E'ES0U'E#dQ0WQ0\'E#d/b|'bS0\Q0]1o89S0W1o867O:S0XQ0`Pz1Qz?S0VPzANz{FPz1`F~CB1Qz>S0r5>z5>zS0sP}PzPzANz{ERaPzQ0aQ09$0360T8,`ECBP}PzPzQ0ePzQ0i#^S09,`~CBS0tP}PzB118EFS0u9Nz{S0vPzQ0uQ0aQ08$0360T8+00CBH0=FKP0P3bBbDbEX18X48X=8X0yX3y%1:S0a?\:9S08=H65S0wQ0aQ0:7\:13b5Q0i7\5S0:1=65S0x#1S0yQ0xQ0o3v[[[^18^48^=8^0y^3yP;%:\S0oQ0oQ0q;WU'P%<\R\?C\ZPTQ0kfU#iQ0MfPR\Q0mO8b7bGb8b9b:b;b<bCbHbcbdbAb6b@b?PePfPgPhPkPWPlP8PcPoPrPnQ0TPsPHPtPuPvPwPx%2R,TG%2_#1Q0R,8G#;[\mQ0p=SG:VqX2pQ0p,8GS0R#1\q^2pQ0U#d/b|Q0]Q0W?O:2S0WQ0`Pz1Qz5S0UPzPaPz1`EFCBS0oQ0V5>z5>zS0qP}PzPzQ0d=NzFPzQ09,`FCBP}PzPaPzQ0B#?S0B#^-00ECBFKP0P3bBbDbEX18X48X0yX3y%1;S09?\;:=H96S0d13b9Q0i7\9%19S0iQ0B7v9[[^18^48^0y^3yP;Q0M#:S0zQ0zQ0R;WU'PQ0M#<S0MQ0M;CZPTQ0pP_Q0mO6b7bGb8b9b:b;b<bCbHbAb6b@b?H0~EpPMPCP8PMQ03P8P7P;%26R_,_iS03Ct,fMX]8CFQ00P8P7PBP;PCPA%<?S0p%:?S0M/=:P;DAn200110200012010@104XPMCFPCPAP1PIQ0NDA55BPBP7Q01PCP7P;Q00PAP7P7P;P;n200110B00012010B106%DOS0z%2?RM,IOS0R$04%XO%[OCZ%DjS0{Q0Q,IjS0|$04%Xj%[jCZS0}Q0}n10110800041010B1010F0000XNBPCPAQ0=Q0>%DiP`1Ii_PYPXALG_bFGQ03DAQ0nP;J0;Q03/MIPBP8Q01PCP8P;Q00PAP7P8P;Q00P8P8P8P:P;n200110B00012010F10Fn200110B00012010B106P8P8P=P8Q04&0C=S03P=^Y=]Z]IQ04Q03Q04P=P9Q02P=P=P:P;P:n1011050002002010310?Q02P=P=P9P:P>P9P;P6O3n1011050002002010310?n0110000020010101XY=WZWIp?100110AS04fKR_#@g02H[Q03Q05P;n0110700013010>10=10<S05Q0;O3S03P9n0110700013010:10;109%D4%2>S02,I4,u`?~YXQ02=LGb401S02P8P8%D_%2JS0n,I_,u`?~YXQ0n=LGb401S0n%:JS0>20}:;R_#?S0=20S:;S0}n0110D0003001010E1010EP8P8Q0nQ0>20S;:S0~&0E_R_n0110D0003001010E1010En011030003001010C1010CP8P8P=P8Q04%@4Q05Q0;O3P9n0110700013010:10;109Q0zQ0R,u`?~YXALGMb401S0zP8P8Q02Q0OQ0=Q0}n0110D0003001010E1010EP8P8Q02Q0OQ0~P_n0110D0003001010E1010En011030003001010C1010CR_P_n10110800041010B1110F0101XNBPCPA%<5%:5Q0{P`Q0|PYPXQ0Q=LGbFGR_Q0PDAPCPAPiP<P1DAP:J0;16_<PBP8Q01PCP8P;Q00PAP7P8P;Q00P8P8P8P:P:n200110B00012010F10Fn200110B00012010B106P=P8Q04fLR_#@Q05Q0;O3P:n0110700013010:10;109P=P8Q03P:n0110700013010:10;109S03Q03n10110800041010B1010F0000XNBPCPAQ0pQ0MQ0z'=1_OMDAPCPAPjPiP<DAP9J0;Q0p/6jQ0S/6OP8%<J%:P%D_P`%2PS0S,I_PYPXQ0S=LGbFGS0p/64fMRj%2KRA'_S0z/M4S0M%@\,lD=5QSS03AC\\US0;Q0CQ0DQ0EfOR\#DS05P`%i\S04/=NS00PYPXQ0HFGRMQ05Q00%X\%[\CZS00,M_S0P5Rj9R6V9H[]DVX>=,m=[[X[8Q0>Q0n'=/6OP8Q0pQ0MQ03Q0;Q0CQ0DP[P]%<^/6VS0p169MQ0PDVDVX>=,m=[X\8Q0S,__/MOP7Q0zQ03Q0;Q0CQ0DP[P]Q0p%:^Q05P`Q04%2^R^'=PYPXALG^bFG/6MQ00,M:DVDVX>=,m=XX7P=%@\,lD=5QSAC\\UQ0CQ0D%<L%:LfNR\#DRSP`%i\RM%2LR^'=PYPXALG^bFGQ0EPSP`1=MNRMPYPXQ0HFG1_\^PSPM%X\%[\CZ'M3R7RV9H[]DVX>=PK%@\,lD20A=K55QAC\\UR\%<KRQ?CQZRD13AT,PAR]%:KRK#1S0H18GAR[=WKUS0E16QQS0DPK%DjRKP`1IjARAPYPX1r[bFGR[/6[S0CQ0zPKPA%XjRX%[jRjCZ'MRY'0S0z'0S00'0S04'0R`'0RV'0RM'0PPP\PMPePfPgPhPkPWPlP8PcPoPrPnQ0TPsPHPtPuPvPwPxQ0N#2RM,TGR\%2IRP#1%21,8G#;[\mR1%2<RS=SG:VqX2pR^18GSRN#1\q^2pR_Q0[Q0YQ0Z'E'E#d/b|Q0]Q0^Q0_9O2??O627O:Q0`PzPzQ0bQ07#Y,a89Nz{Q0c5>zQ0f5>zP}PzQ0A9nzEP}PzPaP}PzQ0A/xF-0@zP}PzQ0e1QzL5>zP}Q0g9>zaFKFKE{P0P3bBbDbEX18X48X=8XL8XM8X0yX3yXFyXUy1P5>=H?J19:5Q0i16>513b>/0RAC??>[[[[[^18^48^=8^L8^M8^0y^3y^Fy^UyP;Q0j%:<R>#1RRAW>NURb'0RJ13STRL%<<R<?C<ZRFPSPdPTPUf[PIPiPOQ0lQ0mO>b7bGb8b9b:b;b<bCbHbAb6b@b?PDPVPePfPgPhPkPWPlP8PcPoPrPnQ0TPsPHPtPuPvPwPxP\P1P^P_P|Q0]1o8:RVQ0`PzPzPzPaPz%^Z-00ECBRD1Qz6ROP}PDE{P0P3bBbDbEX18X0yQ0919;Z<02:Q0a?v:Z[^18^0yP;1PSLRL/0JP<PIO3b7bGb8b9b:b;b<bCbHbAb6b@b?P]P`PePfPgPhPkPWPlP8PcPoPrPnQ0TPsPHPtPuPvPwPxP\P1P^P_P|Q0]Q0WQ0`PzQ0qP}Q0oH0=P0P3bBbDbEX18X48X0yX3yQ0dQ08[^18^48^0y^3yP;PJPFPTPSPIO5b7bGb8b9b:b;b<bCbHbAb6b@b?Q0HQ04PePfPgPhPkPWPlP8PcPoPrPnQ0TPsPHPtPuPvPwPxP\P1P^P_P|Q0]PVQ0`PzPzPOQ0UQ0V9>za5>zP}PaE{P0P3bBbDbEX18X0yX3yXFyQ09/069H:9Q0a[^18^0y^3y^FyP;PbPLPFP>PIO5b7bGb8b9b:b;b<bCbHbAb6b@b?Q0EQ00PePfPgPhPkPWPlP8PcPoPrPnQ0TPsPHPtPuPvPwPxP\P1P^P_P|Q0]Q0XQ0`PzPzQ0VQ0rQ0bQ0u=Nz~R~5>z5>zP}P~E{P0P3bBbDbEX18X48X=8X0yX3yXFy1=;:=\?99H65AW:96[^18^48^=8^0y^3y^FyP;PRPLPFPUPNP>PIO7b7bGb8b9b:b;b<bCbHbAb6b@b?Q0DQ0z%gQQ0CPY%g[P@P7&04AR[>0RKXB0RKAXPjPjP8P7\@RQ20QK[20QKAPXPXP8PQ\8RQ&0|KRKPKP[PAPQ\8/sKQ0B,8GPePfPgPhPkPWPlP8PcPoPrPnPuPvPwPxQ0k,TGQ0h#2#118GM#;[\mASGP:VqX2p18GPRG#1\q^2pQ0\Q0]Q0XQ0`PzQ0sP}PzPzPaPzQ0F#?Ra#^,`ECBP}PzQ0tP}PzQ0vPzQ0uQ0G#?Rz#^+00CBH0=FKP0P3bBbDbEX18X48X=8X0yX3yQ0wQ0a?\:aQ0:Q0yQ0x;vz[[[^18^48^=8^0y^3yP;%:IRzAWzGU'P%<IRI?CIZPTPPfX#iQ0hfSQ0mO8b7bGb8b9b:b;b<bAb6b@b?60{A16[AeL0:%gXL0:1s@jL0:PYeCUCUCUCUCUCUCUCUH0zP4P;EpW5P4P;EpW5P4P;EpW5P;O1b5P;O1b5P;O1b5bJb_bbb>bTb5bSb5WTWSP:P;O2n2001000010121000000bKb5WJWKQ0JQ0655@P=PCQ0<Q0KCFQ0L55BPBP=PCQ0<Q0?CFQ01PCPyP;g01R:RyPyPqPyn101108000410000100000000XNBg01RWQ0@P;EpPyQ0I00y;b5WJWKn0110601020101P;P6O2bKbeWaWJXX7X\8X[8Xf7Xi8o"). Qed.

  Notation UST pc mm x1 x5 x6 x7 x10 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) x10
             (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) x15 x16 x17 (Z_to_bv 64 (DST + dcap))
             (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation USTL pc mm x1 s2 s1 ptr j x23 x24 x25 x26 x27 x28 x31 :=
    (UST pc mm x1 (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 S) (Z_to_bv 64 ptr)
         (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + dcap - 3)) x23 x24 x25 x26 x27 x28
         (Z_to_bv 64 s2) (Z_to_bv 64 s1) x31).

  Ltac sm_eqz := fd_zx; rewrite ?fd_nb by lia; rewrite ?fd_nbd by lia; rewrite ?Z.shiftl_mul_pow2 by lia; lia.
  Ltac sm_tb := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | T : bytes_at usegs mm TB _ |- _ => idtac
    | MU : munch _ m0 mm, DB : sm_box (DST + dcap <= TB \/ _) |- _ =>
        let T := fresh "TBM" in
        assert (T : bytes_at usegs mm TB (concat (map fse_cell_bytes (dt_cells dt))))
          by (apply (bytes_at_transport usegs _ m0 mm TB _ TBB MU); rewrite fse_cells_length; cbn [disjoint_from];
              unfold sm_box in DB; lia)
    end end.
  Ltac sm_rd := sm_tb; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let a := cur_mem_addr in
    first [
      match goal with T : bytes_at usegs mm TB _, NE : nth_error (dt_cells dt) (Z.to_nat ?s) = Some ?c |- _ =>
        let R := fresh "RD" in
        pose proof (cell_rd_ns usegs mm TB (dt_cells dt) s c a T NE ltac:(lia) ltac:(unfold wa; f_equal; sm_eqz)) as R
      end
    | match goal with T : bytes_at usegs mm TB _, NE : nth_error (dt_cells dt) (Z.to_nat ?s) = Some ?c |- _ =>
        let R := fresh "RD" in
        pose proof (cell_rd_off usegs mm TB (dt_cells dt) s c 2 2%nat T NE ltac:(lia) ltac:(lia) ltac:(lia)) as R;
        change (Z.to_nat 2) with 2%nat in R; unfold fse_cell_bytes, le2 in R; cbn [firstn skipn app Z_to_le_bytes] in R;
        rewrite <- (le2_two_bytes (dc_symbol c) (dc_nbBits c)) in R by lia;
        replace (wa (TB + (4 * s + 2))) with a in R by (unfold wa; f_equal; sm_eqz)
      end
    | match goal with MI : mem_inv usegs mm, NE : nth_error (dt_cells dt) (Z.to_nat ?s) = Some ?c |- _ =>
        let R := fresh "RD" in
        pose proof (mask_rd mm (dc_nbBits c) MI ltac:(lia)) as R;
        replace (Z_to_bv 64 (BIT_MASK_TAB + 4 * dc_nbBits c)) with a in R by (f_equal; unfold BIT_MASK_TAB; sm_eqz)
      end ] end.
  Ltac sm_step stop := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20828) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fac8) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fdd0) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [zstep | sm_rd; zstep] end).
  Ltac sm_lx := repeat match goal with H : context [Z.lxor ?a ?b] |- _ =>
    let a' := eval vm_compute in a in is_Zlit a'; let b' := eval vm_compute in b in is_Zlit b';
    let v := eval vm_compute in (Z.lxor a' b') in change (Z.lxor a b) with v in H end.
  Ltac sm_ref := try (exfalso; fd_clr; unfold BIT_MASK_TAB in *; sm_lx; fd_zx; rewrite ?fd_nb in * by lia;
    rewrite ?fd_nbd in * by lia; rewrite ?fd_x4 in * by lia; rewrite ?Z.shiftl_mul_pow2 in * by lia; lia).
  Ltac sm_walk stop := sm_step stop; repeat (fd_brk; sm_ref; sm_step stop).

  (* [comment removed for export] *)
  Ltac osb OUTA LJ OL :=
    let SOK := fresh "SOK" in
    lazymatch type of OUTA with u8arr _ ?mm ?D (map (Z_to_bv 8) ?o ++ ?j) =>
    pose proof (u8arr_store_ok usegs mm D _ (zlen o) (wa (D + zlen o)) OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) eq_refl) as SOK;
    zstep;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) =>
        replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) =>
        replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
    end;
    rewrite le1_lit;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
      let OUT2 := fresh "OUTA" in
      let LJ2 := fresh "LJ" in
      pose proof (out_sb usegs mm D o j v OUTA ltac:(lia)) as OUT2;
      let LO2 := fresh "LO" in
      assert (LO2 : zlen (o ++ [v]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
      assert (LJ2 : zlen (List.tl j) = dcap - zlen (o ++ [v])) by (rewrite zlen_tl by lia; lia);
      clear OUTA LJ; store_done; rename OUT2 into OUTA; rename LJ2 into LJ
    end end.

  (* [comment removed for export] *)
  Lemma dec_facts : forall s d o s' d', decode_sym dt false s d = Ok (o, s', d') -> 0 <= bd_bits d <= 2^30 ->
    exists nb, 0 <= nb <= tl /\ d' = mkBD (bd_cont d) (bd_bits d + nb) (bd_ptr d) (bd_zero d) /\ 0 <= o < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fdw_sm ()) ["SM"] "p'0h02nbh11Hh22Hah31Eh44__x1h51ch63H28h77__arithh84__ffh97__sat29h:7__sat30h;7__sat31h<7__sat32h=7__sat33h>7__sat34h?8__varmaph@5__withA4__x2hB4cstrhC5cstr0hD2d'hE1ohF3z28hG2C1hH2C2hI2HbhJ2_HhK3_H0hL3_H1hM3_H2hN3_H3hO1dhP1ehQ1shR2s'i001xp&0p;2p;1p;4p;3p;7p;8g00I4j2{Tg01];k10ITg01^4j4QTg0152j4MTg01e6j2TTg00@ej34Tg01_:j1OTg002Cj1?Tg003ij1HTg00Dcj1aTg00\6j27Tg005dj25Tg02J^k70HTg00BPk10FTg01`=k10ETg01c7j1PTg02Aaj3RTg00F5j2_Tg01i2j13Tg01fhj11Tg01j7j19Tg01l6j12Tg002hk102Tg01UCj2CTg020@R0j2cTg00`Xj2;Tg00b;R1j20Tg004Gj2>Tg01m9j1LTg01n;j1KTg004dj2oTg009oj1nTg005Dj1mTg0230k20@Tg023lk20?Tg023Rk20=Tg00`0j2^Tg00a4j3bTg00:Tk10<Tg00;4k109Tg00;Tj2jTg00<2k108Tg00<Pk407Tg00<nk106Tg00=Lk104Tg00>Zj2gTg00>7j2eTg00hjj4\Tg008Tk103Tg00?=k205Tg00?_j2iTg00@9k201Tg00A?k30:Tg00A^k40;Tg01?kj4dTg02AGk400Tg0019j7kTg02B?j2VTg00\Sj2FTg02Bfj2WTg01SQj2XTg01o>j4NTg00iUj7~Tg00j9j7}Tg00j]j8|Tg01BOR2P2f1R3f0R4CMp=Sg01A<R5/53/04p=U1554p=:f2R61;34'0p=I%?4#?p=`15561;34'0p==1>63/54p=]%O3/>4p=6%?4#?#?#?#?#?#?#?p=Jf6R7f5R8f4R9f3R:,C5'V/F6/F3'W/X4'>p=[g02D[R;P:P6%L3%K4CN749p=8A429:A4263/04'0p=<1034,06p=D1534,06p=Yf7R<%28%O9/>:%L6%K3CN94;7/04'0p=E1c24p=B1C59,V8/F:/F6,W71C34'X,><p=@15591>:6/53/04'0p=G1556/03/04p=A1063/04p>0G1>:6/53/04p=z%349423p=y1C54p=x1V:6/F3/F4,W9p=w1X63,>:9429/04p=v1C54,V3p=u1F63/F4p=t1W63/X4p=s1>349426p=r1553/04,06,0:p=q%2:P6P3P4CN94;9p>0D%2:P6P3P4CNp=pP91>:6P3P4CNp>0CP9P:P6P3CN94;8/04,07p>0BA4;34p>0AA4234p=l1563/04p>0>P3g01BmR=g01CLR>P>g01ClR?P4g01E3F~p=ZP6P=P>P>P?P3P4F}p=fP:P=P>P>P?P6P3P4G|p=h1{22R=/{;R@$0IRAp,2dtRBg01GmRCP9P:CQP=P;1S63P4CM,T@34%O9RDg01LWRE#?RF#HRG%aE#a#a#?#HRH'7RI,5D'UP7P8P9P:P6P3P4K0Hg02E]RD&0FDRJ&0EBRK%P<5RD1_D4RL34%:<RMp,2tlRN,7GRO7I<%34RP%`FRQ#`RR#?RS#`RT#HRU7=PRV%14RW15WN'URX%94RY#:RZ17GWR[=]YOR\P8PPP9PY%27R]&02RRR167WR^%JT#J#J#J#J#J#J#HRT%HSRS%HER_,C[R[F[P:P]P^P7P7D8D<3D3D3DX5D'cP0PDf8R0#P9RDK=4JLA=00OP7PPP8PY%2<R^PR16<WR]PTPSP[F[P9P^P]P<P<D8D<9DZ\9DVX3DX5D%:4R]?Y4NR^P8P0P0P4P0P0AIM<UGEX02#BP4f:RM#P9RDK=4JLA=MMOP0PPP<PYf9RY#2RPPR16YWRWPTPSP[F[P7PPPWPYPYD8D<9DZ\9DVX3DP1f;RX#P9RDK1_D354J%:XRV1;XO%33R\1;\U%13RZ15ZN%93RWPW17GZRPPOPYP\P0PW%2MRWPR16MZRZPTPSPPP_G@P<PWPZPMPMD8D<DG3A3A40GP^PYf<RZPZP4PZPZAIVXUGEX02#BP4f=RV#P9RDK1_D:54Jf>RJ1;JO%39RW1;WU%19R<15<N%99R9P917G<RPPOPZPWPXP9%2VR9PR16V<R<PTPSPPP_G@PMP9P<PVPVD8D<DG3A3A3AP1f?R<#:R9?I<O%38RM1;MU%18RP15PN%98RWPW17GPR\POPVPMPZPW%2JRWPR16JPRPPTPSP\P_G@PXPWPPPJPJD8D<DG3A3AP^PVf@RPPPP4PPPPAI9<UGEX02#BP4fAR9?=9O%30RW1;WU%10R\15\N%90R0P017G\RMPOPPPWP<P0%29R0PR169\R\PTPSPMP_G@PJP0P\P9P9D8D<DG3A3AP1%3YR\?=\U%1YR0150N%9YRYPY17G0RJPOP9P\PPPYfBRY#2R\PR16Y0R0PTPSPJP_G@P<P\P0PYPYD8D<DG3AP^P9fDR0P0P4P0P0fCR\?=\UGEX02#BP4%3XRX?=XU%1ZRX15XN%9ZRJPJ17GXRMPOP0%3ZP\PJfERJ#2RZPR16JXRXPTPSPMP_G@PYPZPXPJPJD8D<DG3AP1%1VRX15XN'U%9VRZPZ17GXRYPOPJ%3VP0PZfFRZ#2RVPR16ZXRXPTPSPYP_G@P\PVPXPZPZD8D<DGP^PJfHRXPXP4PXPXfGRV?=VUGEX02#BP4%1<R<15<N'U%9PR<P<%1PRY,7GRMPOPX%3PPVP<fIR<#2RPPR16<YRYPTPSPMP_G@PZPPPYP<P<D8D<DGP1%99RY#:PY%19RP,7GRZPOP<%39PXPYfJRY#2R9PR16YPRPPTPSPZP_G@PVP9PPPYPYD8D<CzP^P<fLRPPPP4PPPPfKR9?=9UGEX02#BP4%9\#:%90R\%10RZ,7GRMPOPP%30P9P\fMR\#2R0PR16\ZRZPTPSPMP_G@PYP0PZP\P\D8D<CzP1%9JRZ%1JR0,7GRY;]OP\%3JPPPZfNRZ#2RJPR16Z0R0PTPSPYP_G@P9PJP0PZPZD8D<P^P\fPR0P0P4P0P0fORJ?=JUGEX02#BP4%9V%1V,7G;]OP0%3XPJ%9XfQRV#2RYPR%1XRX,6VRMPTPS17GXP_G@PZPYPMPVPVD8D<P11yV<P0%9<fRRM#2RYPR%1<R<,6MRX#xPTPSDw17G</C_PJPYPXPMPMD8DvP^PVfTRXPXP4PXPXfSRY?=YUGEX02#BP41yY9P2%3PRPPBPCfWR9fVRJCQP=P;1S4XPYCM,T@54AfUR<%9Z%29RW%1ZR7,69R[,uR?tTS17G7/C_3s3rR7PXPWP[P9P9D8R['0P^PJfYRW#2RL%OWR`/>4PWPWD8RaP:1;:UCqX02#B[]3XE2PBPCPJP<CQP=P;1SPYPMCM,T@54APX%9\%2JRPPR%1\R\,6JR:#xPTPSDw17G\/C_PYPPP:PJPJD8DvP1P7P[P^Pa%30Ra1;aUCqX02#BP4%90%10R0,>`,uR?tTS17G0/C_5sL5r9P9fZR9%1V,69%L9%K9I0DP;f[RL%1M,6L%LL%KLCpR_PBPCf]R0f\RTCQP=P;%3YRR/S9P4CM,T@54AP^P6f^R9P9P4P9P9%3<R<?=<UGEX02#B]3XD;PBPCPTPLCQP=P;%3M/SWP_CM,T@54AP2P^%20R^%O0RA%1X%L0R@%K0R0I0CP^1>A4P@P0%3XR0?=0UK0BX02%1YRY15YN,UYPT16TY%LT%KTCpRT00ATRYA=RRURR'0p,2bs,o2R0#nR@%m0R0#:RA1oDKRK#nR^%mK#:RK%HQRQ00@0R_1;Q020?Q0RW/l0'01lWQ:0>0Q+0=RQPWP21^GSR01;5GR=%:S17GSRL,;5[[RC%:GRBg01OlR<AbGS3UW2RS%:L\<^2BRL1^GHR`%:H1;5I[\=RaAbGH3V<X2BRH%:I\<^2BRI1^GNR[%:N1;5O[\=R=AbGN3V<X2BRG%:O\<^2BRBg01M<R<$0<RO&09<R<P21j26P3&082H07&062R7&042R1P21g25g01DLRJ1e2EREC\,Z1R:P2PEPJ1e2FC\,Z15f1RF&03>R>PFCh2051?R?P4P6g01J3RFg01MhRJ'i20146=4FJdB0:253H0;R5b8b?b@X42XA2AY]43%:3RJ?Y36[^42^A2P4PN%19PZO3b7b9b:b;b<b=b>bFb6bCbBPYPR1i;TP@PAP^PKP_PQPWP2P0PCPSPLP`PaPHPIP[P=PGPBPOP<1j23P7P1P2PEg01ES1g2UC\,Z19f1:R:P>P:ChP?P5b8b?b@X42AI]4UAIJ3U[^42P4%39PMO2b7b9b:b;b<b=b>bFb6bCbBCdCdH00W3fXP4P8FkW1WNP3P4O2n2001000000121000000W1W3PXP4PVFkW1P3P4O2n2001000000121000000W1WMP3P4O2n2001000000121000000W1WLP3P4O2n2001000000121000000W1WHP3P4O2n2001000000121000000W1WGP3P4O2n2001000000121000000W1WKP3P4O2n2011000000121000000W1WJP3P4O2n2011000000121000000W1X5DP3P4O2n2011000000121100000bPWIW3XD;XR2XE2XO;XQ2o"). Qed.

  (* [comment removed for export] *)
  Definition ml_body (f : nat) (x : dec) (st : dstatus) (d0 : bitD) : res dec :=
    if dstatus_eqb st Unfinished && (FseNCount.Zlength (de_out x) <? dcap - 3) then
      let! q1 := decode_sym dt false (de_s1 x) d0 in let '(o0, s1a, d1) := q1 in
      let! q2 := decode_sym dt false (de_s2 x) d1 in let '(o1, s2a, d2) := q2 in
      let! q3 := decode_sym dt false s1a d2 in let '(o2, s1b, d3) := q3 in
      let! q4 := decode_sym dt false s2a d3 in let '(o3, s2b, d4) := q4 in
      main_loop bs dt dcap false f (mkDec (de_out x ++ [o0; o1; o2; o3]) s1b s2b d4)
    else Ok (mkDec (de_out x) (de_s1 x) (de_s2 x) d0).

  Lemma main_loop_S : forall f x, main_loop bs dt dcap false (Datatypes.S f) x =
    let! r := reload_dstream bs (de_bd x) in let '(st, d0) := r in ml_body f x st d0.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_fdw_sm ()) ["SM"] "p'0h01fh11ri001rh21xi012d0i022stp;1p;2p;4g01];j16Tg00I4R0j25Tg03XZj10Tg03Y[j21Tg03Zej44Tg01k>j42Tg00?_j23Tg01ITg03[eR1%61R2g03\fR3g02D[R4'5R5P1p,2bsf0R1#0'1P0P3P4P2P1f4f3f1P1C4n2001100000120102101X15C2'3W2W0o"). Qed.

End SM.

Lemma hd_sr : forall q r, 0 <= q <= 8 -> 0 <= r <= 7 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (8 * q + r)) 3) = q.
Proof.
  intros q r Q R. rewrite srliw_val by lia. rewrite (Z.mod_small (8 * q + r)) by lia. change (2^3) with 8.
  symmetry. apply (Z.div_unique (8 * q + r) 8 q r); lia.
Qed.

Lemma hd_l7 : forall q r, 0 <= q -> 0 <= r <= 7 -> Z.land (8 * q + r) 7 = r.
Proof.
  intros q r Q R. rewrite land7_mod. symmetry. apply (Z.mod_unique (8 * q + r) 8 q r); lia.
Qed.

Section L1.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
            (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis PRE : fdw_pre SP S DT DST dcap lo bs dt.

  Notation HST pc mm y1 ptr j x23 y24 y25 y26 y27 x28 s2 s1 x31 :=
    (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST)
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1)
             (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 ptr) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap))
             (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + dcap - 3))
             x23 y24 y25 y26 y27 x28 (Z_to_bv 64 s2) (Z_to_bv 64 s1) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac hd_src SRC P := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let a := cur_mem_addr in let E := addr_expr a in
    let go i := (let RX := fresh "RX" in
      pose proof (src_rd usegs mm S bs i SRC ltac:(lia)) as RX; replace (S + i) with E in RX by lia) in
    first [go P | go (P + 1) | go (P + 2) | go (P + 3) | go (P + 4) | go (P + 5) | go (P + 6) | go (P + 7)] end.

  Ltac hd_q q := repeat match goal with
    | H : context [q mod 18446744073709551616] |- _ => rewrite (Z.mod_small q 18446744073709551616) in H by lia
    | |- context [q mod 18446744073709551616] => rewrite (Z.mod_small q 18446744073709551616) by lia end.

  Ltac hd_walk SRC P EZX ESH EMD ESR q := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20828) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fbd8) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fdd0) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
        rewrite ?EZX, ?ESH, ?EMD, ?ESR; hd_q q; first [zstep | hd_src SRC P; zstep]
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        fd_brk; rewrite ?ESR in *; hd_q q; try (exfalso; fd_clr; lia) end).

  Ltac hd_eqn := rewrite ?hd_l7, ?y4_md by lia; first [ reflexivity
    | rewrite le64_lbu_raw by (apply byte_Znth; [assumption | lia]); reflexivity
    | rewrite ?Z.shiftl_mul_pow2 by lia; try change (2^3) with 8;
      repeat match goal with |- context [?x mod ?m] => is_Zlit_zb m; rewrite (Z.mod_small x m) by lia end;
      rewrite ?FseWalkKit.swrap32_small by lia; lia ].


  Ltac hd_cond := cbn [dstatus_eqb andb]; try unfold FseNCount.Zlength; try unfold zlen in *;
    first [ reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
          | match goal with |- context [if ?c then _ else _] => destruct c; reflexivity end ].

  Ltac hd_mem TBX MU1 TLC := unfold fdw_mem, sm_inv, bitdz_cells; cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero];
    split; [eassumption|]; split; [eassumption|]; split;
    [ lazymatch goal with
      | H : rw_cells usegs ?mm (SP + 48) [C8 (Z_to_bv 64 ?a); C4 (Z_to_bv 64 ?b); CB 4 _; C8 (Z_to_bv 64 ?c); _; _]
        |- rw_cells usegs ?mm (SP + 48) [C8 (Z_to_bv 64 ?a'); C4 (Z_to_bv 64 ?b'); CB 4 _; C8 (Z_to_bv 64 ?c'); _; _] =>
          replace a' with a by hd_eqn; replace b' with b by hd_eqn; replace c' with c by hd_eqn; exact H end |];
    split; [split; [eexists; split; eassumption | split; [eassumption | split; eassumption]] |];
    split; [ unfold sm_box in TBX; apply (bytes_at_transport usegs _ _ _ (DT + 4) _ TBX MU1);
             rewrite fse_cells_length; cbn [disjoint_from];
             assert (Z.of_nat (length (dt_cells dt)) = 2^(dt_tableLog dt)) by exact TLC; lia |];
    split; eassumption.

  Ltac hd_kc KC t16 t23 TBX MU1 TLC BY :=
    rewrite ?le64_lbu_raw by (apply byte_Znth; [exact BY | lia]);
    let e16 := reg_val 16%Z in let e23 := reg_val 23%Z in
    lazymatch e16 with Z_to_bv 64 ?a => replace a with t16 by hd_eqn end;
    lazymatch e23 with Z_to_bv 64 ?a => replace a with t23 by hd_eqn end;
    eapply KC; [hd_cond | hd_mem TBX MU1 TLC].

  Ltac hd_kt KT TBX MU1 TLC BOK0 BLE STO OBY :=
    eapply KT; [hd_cond | unfold sm_okr; cbn [de_bd de_out bd_bits]; split; [exact BOK0 | split; [lia | split; [lia | exact OBY]]]
               | unfold st_ok in STO |- *; cbn [de_s1 de_s2] in STO |- *; exact STO | hd_mem TBX MU1 TLC].

  Ltac hd_close KC KT t16 t23 TBX MU1 TLC BY BOK0 BLE STO OBY EMD EL7 := rewrite ?EMD, ?EL7; lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fbd8) _ _ _ _) => hd_kc KC t16 t23 TBX MU1 TLC BY
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fdd0) _ _ _ _) => hd_kt KT TBX MU1 TLC BOK0 BLE STO OBY end.

  Lemma sm_head : forall x st d0 m1 jp (y1 y23 y24 y25 y26 y27 y31 : word),
    sm_ok dcap bs x -> st_ok (dt_tableLog dt) x -> fdw_mem m0 m1 SP S DT DST dcap lo bs dt x jp ->
    reload_dstream bs (de_bd x) = Ok (st, d0) ->
    (dstatus_eqb st Unfinished && (FseNCount.Zlength (de_out x) <? dcap - 3) = true ->
       forall m2 jp2 (z1 z24 z25 z26 z27 z28 : word),
         fdw_mem m0 m2 SP S DT DST dcap lo bs dt (mkDec (de_out x) (de_s1 x) (de_s2 x) d0) jp2 ->
         evt usegs POST (HST PFDW_L1D m2 z1 (S + bd_ptr d0) (zlen (de_out x)) (Z_to_bv 64 (bd_bits d0))
                             z24 z25 z26 z27 z28 (de_s2 x) (de_s1 x) (Z_to_bv 64 (bd_cont d0)))) ->
    (dstatus_eqb st Unfinished && (FseNCount.Zlength (de_out x) <? dcap - 3) = false ->
       fdw_t1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (de_out x) (de_s1 x) (de_s2 x) d0)) ->
    evt usegs POST (HST PFDW_L1 m1 y1 (S + bd_ptr (de_bd x)) (zlen (de_out x)) y23 y24 y25 y26 y27
                        (Z_to_bv 64 (bd_bits (de_bd x))) (de_s2 x) (de_s1 x) y31).
  Proof.
    intros [out s1 s2 [c b p z]] st d0 m1 jp y1 y23 y24 y25 y26 y27 y31 OK STO MEM RL KC KT.
    cbn [de_out de_s1 de_s2 de_bd] in *.
    destruct PRE as (TL1 & TLC & COK & BY & LO1 & SPA & SPH & S8 & SL & DT0 & DTA & DTL & D4 & DL & DC & DJ1 & DJ2 & DJ3).
    pose proof (fi_reload_facts bs _ st d0 BY (proj1 OK) RL) as (BOK0 & BLE & _).
    destruct OK as ((BC & BB & BP0 & BPE & BSM & BZ) & BB64 & OL & OBY).
    cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero] in *.
    assert (Z0 : z = false) by (destruct z; [specialize (BZ eq_refl); lia | reflexivity]). subst z.
    destruct MEM as (FS2 & FS1 & FBD & ((junk & OUTA & LJ) & MU & WM & MI) & TBB & SRC & STK).
    unfold bitdz_cells in FBD. cbn [bd_cont bd_bits bd_ptr bd_zero] in FBD. cbv iota in FBD.
    pose proof (Z.pow_pos_nonneg 2 (dt_tableLog dt) ltac:(lia) ltac:(lia)) as PT.
    assert (TBX : sm_box (bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))))) by exact TBB.
    clear TBB. pose proof (munch_refl [(SP + 16, SP + 88); (DST, DST + dcap)] m1) as MU1.
    assert (QR : exists q r, b = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7)
      by (exists (b / 8), (b mod 8); pose proof (Z.div_mod b 8 ltac:(lia)) as DM; pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as MB;
          assert (b / 8 <= 8) by (apply Z.div_le_upper_bound; lia); assert (0 <= b / 8) by (apply Z.div_pos; lia); lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    pose proof (y4_zx q r ltac:(lia) ltac:(lia)) as EZX.
    pose proof (y4_sh q r ltac:(lia) ltac:(lia)) as ESH.
    pose proof (y4_md q r ltac:(lia) ltac:(lia)) as EMD.
    pose proof (hd_sr q r ltac:(lia) ltac:(lia)) as ESR.
    pose proof (hd_l7 q r ltac:(lia) ltac:(lia)) as EL7.
    unfold PFDW_L1. unfold PFDW_L1D in KC. unfold fdw_t1_K, PFDW_T1 in KT. cbn [de_out de_s1 de_s2 de_bd] in KC, KT.
    unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
    replace (64 <? 8 * q + r) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z.leb_spec 8 p) as [PA|PA].
    - replace (8 <=? p) with true in RL by (symmetry; apply Z.leb_le; lia).
      rewrite ESH in RL. rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as ST D0. subst st d0. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
      hd_walk SRC (p - q) EZX ESH EMD ESR q.
      all: hd_close KC KT (S + (p - q)) ((8 * q + r) mod 2 ^ 3) TBX MU1 TLC BY BOK0 BLE STO OBY EMD EL7.
    - replace (8 <=? p) with false in RL by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.eqb_spec p 0) as [PB|PB].
      + subst p. cbn [Z.eqb] in RL. injection RL as ST D0. subst st d0. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
        hd_walk SRC 0 EZX ESH EMD ESR q.
        all: hd_close KC KT S 0 TBX MU1 TLC BY BOK0 BLE STO OBY EMD EL7.
      + replace (p =? 0) with false in RL by (symmetry; apply Z.eqb_neq; lia).
        rewrite ESH in RL. destruct (Z.ltb_spec (p - q) 0) as [PC|PC].
        * replace (p - q <? 0) with true in RL by (symmetry; apply Z.ltb_lt; lia). cbv beta iota zeta in RL.
          replace (p - p) with 0 in RL by lia. rewrite readLE64_ok in RL by lia. cbn [bind] in RL.
          injection RL as ST D0. subst st d0. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
          hd_walk SRC 0 EZX ESH EMD ESR q.
          all: hd_close KC KT S 0 TBX MU1 TLC BY BOK0 BLE STO OBY EMD EL7.
        * replace (p - q <? 0) with false in RL by (symmetry; apply Z.ltb_ge; lia). cbv beta iota zeta in RL.
          rewrite readLE64_ok in RL by lia. cbn [bind] in RL.
          injection RL as ST D0. subst st d0. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
          hd_walk SRC (p - q) EZX ESH EMD ESR q.
          all: hd_close KC KT (S + (p - q)) (8 * q + r - q * 8) TBX MU1 TLC BY BOK0 BLE STO OBY EMD EL7.
  Qed.
End L1.

Theorem fdw_l1h_proof : fdw_l1h_stmt.
Proof.
  unfold fdw_l1h_stmt. intros SP gp tp F fc m0 m1 S DT DST dcap lo bs dt POST jp x st d0 y1 y23 y24 y25 y26 y27 y31
    PRE OK STO MEM RL KC KT.
  exact (sm_head SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE x st d0 m1 jp y1 y23 y24 y25 y26 y27 y31
           OK STO MEM RL KC KT).
Qed.

Theorem fdw_l1_proof : fdw_l1_stmt.
Proof. exact (fdw_l1_from_h_proof fdw_l1h_proof). Qed.
