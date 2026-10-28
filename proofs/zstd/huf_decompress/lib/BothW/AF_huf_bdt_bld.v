(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface RF_huf_bdt_model RF_huf_bdt_bld.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_huf_tbl_iface AF_huf_bdt_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkArith StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_bdt_bld () := "C46Stdlib5Lists4List:length_appC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3mulI47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List6concatC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model4tsymC47Corelib4Init3Nat3addC47Corelib4Init3Nat3subK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<length_skipnC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;tsym_lengthC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model@fse_cells_lengthC47Corelib4Init9Datatypes3appc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_bld3tdbC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface>fse_cell_bytesI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C56Stdlib6ZArith6BinInt1Z3powI47Corelib5Lists7ListDef6Forall00c5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_bld7blA_invC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit=shad_outside2C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit=zshadow_munchC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5oloadC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3u16C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount9highbit32C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7to_byteC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shl32C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model8oload_OkC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model8store_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:build_loopC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4chkZK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit7acc_shZK47Corelib5Lists7ListDef6Forall02K4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld7tsym_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld9nth_cell2C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:u8arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbK4ELinuxProcessSemantics5Riscv5Instr5instr06C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMemBnth_error_map_ZnthC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit?u16arr_store_okc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_bld:tdb_lengthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_2'C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<u16arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le2C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld8map_ZupdC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas>upd_nat_lengthC56Stdlib6ZArith6BinInt1Z4log2K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6PArith6BinPos3Pos4sizeC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm1C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm2C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm3C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z9lt_succ_rC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld3nkcC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_aC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_bC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_cK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_dK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z9mod_smallC57Corelib7BinNums6PosDef3Pos3mulK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32K4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model=cell_write_nbC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sllwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_sllwC5ARocqVerifyHarness?AgentSubmission6Common6StrFun@u8arr_store_ok_nC5ARocqVerifyHarness?AgentSubmission6Common6StrFunAu8arr_write_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem9upd_bytesC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model=cell_write_nsK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell01C46Stdlib5Lists4List9app_assocC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model>fse_cells_snocC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7upd_natC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld>Forall_upd_natC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld8ns_mod16C5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld9le2_eqm16C5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litC5ARocqVerifyHarness?AgentSubmission6Common:STRW_merge=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm4C5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld8sm4_onesC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld6sm3_ltC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld;shl48_shr56C5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld6sm2_ltC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld6sm1_ltC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z7mod_modC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_tbl_kit8zx16_litC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_bdt_bld=unsigned_byteC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5storeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC46Stdlib5Lists4List:length_mapC56Stdlib6ZArith6BinInt1Z3lorC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC56Stdlib6ZArith6BinInt1Z3lebK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK46Stdlib9micromega=RingMicromega3Op205c5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_bld5blA_WC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize02I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4sxb0I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition tdb (jt : list byte) (syms : list (option Z)) (acc : list dcell) (u : Z) : list byte :=
  concat (map fse_cell_bytes acc) ++ tsym (skipn (4 * Z.to_nat u) jt) (skipn (Z.to_nat u) syms).

Lemma tdb_length : forall jt syms acc u, zlen acc = u -> 0 <= u -> (4 * Z.to_nat u <= length jt)%nat ->
  length (tdb jt syms acc u) = length jt.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_bld ()) ["CANSEC1"] "h01nh11xh24__p1h34__p2h44__x1h54__x2h64__x3h74__x4h84__x5h92H1h:2H2h;2HAh<2HLh=3HL0h>2HUh?7__arithh@4__ffhA8__varmaphB5__withC3acchD4cstrhE5cstr0hF2jthG1mhH4symshI1uhJ1yhK2z1hL2z2p&0p;1p;2p;4p;3p;<p;6p;Bp;7p;8g0000R0p4p710p1000Op4p710p8p1000kp4p7210g001WR1p4p710p8g0025j1WTg002Zk10CTg0038j1{Tg003[j1FTg004;k10BTg004]j20Tg005=R2j11Tg005]R3j22Tg0069j18Tg006XR4j1UTg0078j2BTg007OR5j2YTg007ik40ATg008Ek20@Tg008`j3KTg009>j2cTg00:>j2MTg00:Uk207Tg00:lk103Tg00;JR6j26Tg00;gj2>Tg00<DR7j2]Tg00<aj1ej3JTg00=;j2tTg00=^j3sTg00>;j2ETg00>Ul<[Tg00?:j4iTg00?aj1ZTg00@Fj2XTg00@hj2NTg00ADj29Tg00A_j2GTg00B9j1hTg00BWj2gTg00C8j3HTg00Cak20=Tg00DJj3TTg00E3j2dTg00E\j2RTg00FHk10<Tg00Fhj2bTg00GFk10;Tg00Gdj4VTg00HBk106Tg00H`k105Tg00IKj2DTg00Inj1`Tg00JSj2\Tg00K6j3_Tg00KYk302Tg00L<j1zTg00L^j3yTg00MAj2xTg00Mcj2wTg00NOj3vTg00Nnj4uTg00O`j4|Tg00PKj3}TP1j6ITg00Plj2~Tg00R3k100Tg00S?k301TP0j3rTg00S\j4qTg00TYk204Tg00U6lBQTg00U\l<pTg00VAj3PTg00Vjk208Tg00WVk309Tg00X6k60:Tg00XZj4fTg00YEj7mTg00Yij7lTg00ZMk70>Tg00[1k80?Tg00[UR0f1R1f0R83Jp=5g00\3R9?J18p=Ag00\RR:0048p=7P9P9P9P0P0P0g00]0P2P2P2P6g00]Pf5R6f4R;f3R<f2R=P1P8MBQp=SP0P9P0P0P4P;P2P<g00^3P=P1P8M<pp=oP9P9P9P0P0P0g00^`P2P2P2f6R4g00_@P6P;P<P=P1P8MBQp=nP9P9P9P0P0P0g00_gP2P2P2P7g00`GP6P;P<P=P1P8MBQp=kP9P0P5P2P3g00`jP6P;P<P=P1P8M<[p=jAJ08:p=O1d08p=:AP0189P0=p=@g00aL-088p=<AP018p=4g00b8R3@0918p=;P1g00bdR5g00cCR7P7g00ccR>P8J0:p=aP0P1g00dCP8Cfp==P1P5P7P7P>P8g00djFmp=3P=P5P7P7P>P1P8Flp=LP0P1g00eJP8Cfp=CP=P5P7P7P>P1P8K0>p=^P<P5P7P7P>P=P1P8L0?p=?g00f1R5#WR?#WR@#W$0C#{RA#FRB&0B0RC#Fg00fVRD#F10D1#1/5812:1g00gYRE#8RF#8RG#8RH#8RI%U='B10A6'YP9PDPBg00h8P;H0A-0@ARB,0ARJ%U<RK,BIRL=KA4RMAKCK6RN'cRO,0ARP'Mf7RQ,0ARR,A8X09P910D;RS,BIRT%U;RU,BI=KAQAKCU4'c,0A,M8/ARX09P910AMRU10D6RC,BI/M8/ARX09RRP910A4RV007LRWPR1MTWRR/AV&03@RX%1SRY'6RZ%1VR[%7<R\,6XR]'>#7R^']R_/5[P9P0%e9P2%e0%11%18'51A181t183sXJ9X19PRP_PTPZPIPX1E0XRZPSPY1E0YESPWP^1>18#7XG0X00PVP[1E0[R^PLP]PIPXPZPKP\P8X10%78X10R\P<P<1E0<DoRWESFnEkPVP[P^M<[1YLV12][R]PLP\P<O1R\,6XPIPXPZPKP\PWESPVP[P^EjP8CiP]%ZC%1C,2:f8RC,0AR]#Z%1],2:1X:41N:4%74R]/54'9124:%O]'9'G%7QP0f;R],0A#116X8'>R^,X:1N:^%7^R[/5^'912^:%O['9'Gf<R[,0A#116X1'>#7P0p-0R^%8IRW#8R\#8RK#8#:%h5,g0RZ%:KRK5H0RY20=0XRS%:WRW5T0RT%:H9T0S1d0ERE3@3@#<%:IRI%:FRF9T0S/4ERS5@K14EK#<RH'R%:\R\%h@,g0R_=H0WRW%:GRG/4S3@#<AH0Z\AH0_F=@TERT'4R_,4K#<%<_14WSRW,4\#<14KW/RH14YTA@EIG#<'R&0<3';';';';';';';';%F3P0P01b0;P=&0;0R3CVP1P01b06P<P3CVCV&060&050R31a3Q1D0?RG%`5,D0RI1\0XRE%`?,D0R?5_0RT6020RY'=,335L31\0:RH,CY,331=GH,335L35^3%z7R7P31a3C1D0@R@,=?,335L31C@H,331=?H,335L35^3P7P31CHI,33P7P31D05R5,CH,33P7P31CTI,33P7P31=5@,33P7A_0E5=y0G/=I,33C?C?C?C?C?C?1x3>P8P=g00iBR3g00ibR>'E1w8==J3>dAv0:1Cub@bAbBX40X50X60X70X80X2^W316X;,>=R>,51,9612>:%O1'9'G156;,9Q12;:%O6'9'G12:;12:<16XC/24156C16X4/]Q/5C[[[[[[^40^50^60^70^80^2^^3^P81N:]f>,0A#1R816X<'>,N:P<P]P8P110D[#1P=P;P6P4PQf:O=b?bLb:bKb9bEbDb=C|PUA}AL4EIPP1~NMEIPJ&00;EIB01ABO,0AArABOEIP4P6P;P<Cq,0A/AVeW<W>W;XI0WCWHWFo"). Qed.

Section Build.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).
  Variables (x1 x5 x6 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word).
  Variables (m : amem) (TD WK : Z) (tl M1 : Z) (jt : list byte) (syms : list (option Z)).
  Variable POST : machine_state -> Prop.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HM1 : 1 <= M1 <= 256.
  Hypothesis HJT : length jt = (4 * Z.to_nat (2^tl))%nat.
  Hypothesis HSL : length syms = Z.to_nat (2^tl).
  Hypothesis BTD : ablk TD (TD + 4 * 2^tl).
  Hypothesis BWK : ablk WK (WK + 2 * M1).
  Hypothesis DTW : TD + 4 * 2^tl <= WK \/ WK + 2 * M1 <= TD.
  Hypothesis T4 : TD mod 4 = 0.
  Hypothesis W2 : WK mod 2 = 0.
  Hypothesis ZT : zshadow m TD (4 * 2^tl).
  Hypothesis ZW : zshadow m WK (2 * M1).
  Hypothesis RT : rng RNG TD (4 * 2^tl).
  Hypothesis RTS : rng RNG (shad TD) (nshad (4 * 2^tl + TD mod 8)).
  Hypothesis RW : rng RNG WK (2 * M1).
  Hypothesis RWS : rng RNG (shad WK) (nshad (2 * M1 + WK mod 8)).

  Definition blA_W : list (Z * Z) := [(TD, TD + 4 * 2^tl); (WK, WK + 2 * M1)].

  Definition blA_inv (m1 : amem) (u : Z) (snext : list Z) (acc : list dcell) : Prop :=
    u8arr bsegs m1 TD (tdb jt syms acc u)
    /\ u8arr bsegs m1 WK (u16s (map (Z_to_bv 64) snext))
    /\ munch blA_W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  Variable SP : Z.
  Hypothesis FDT : rw_cells bsegs m (SP + 32) [C8 (Z_to_bv 64 (TD - 4))].
  Hypothesis FTL : rw_cells bsegs m (SP + 48) [C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 (- WK - 1))].
  Hypothesis FWK : rw_cells bsegs m (SP + 80) [C8 (Z_to_bv 64 WK)].
  Hypothesis RSP : rng RNG (SP + 32) 56.
  Hypothesis DSP : (TD + 4 * 2^tl <= SP + 32 \/ SP + 88 <= TD) /\ (WK + 2 * M1 <= SP + 32 \/ SP + 88 <= WK).

  Notation STB pc mm u x8 x9 x10 x11 x13 x14 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 (Z_to_bv 64 ASHOFF) x8 x9 x10 x11 (Z_to_bv 64 (4 * u)) x13 x14
             (Z_to_bv 64 (4 * 2^tl)) (Z_to_bv 64 1431655765) (Z_to_bv 64 TD) x18
             x19 x20 x21 x22 x23 x24 x25 x26 x27
             (Z_to_bv 64 858993459) (Z_to_bv 64 252645135) (Z_to_bv 64 16843009) (Z_to_bv 64 31))
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Local Ltac kenum16 k := assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15) as KC by lia;
    destruct KC as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]; vm_compute; reflexivity.

  Lemma bl_loopA : forall f u snext acc r m1 (x8 x9 x10 x11 x13 x14 : word),
    build_loop tl f u syms snext acc = Ok r ->
    Z.of_nat f = 2^tl - u -> 0 <= u < 2^tl -> zlen acc = u -> zlen snext = M1 ->
    Forall (fun v => 0 <= v < 65536) snext ->
    blA_inv m1 u snext acc ->
    (forall m2 snext' (y8 y9 y10 y11 y13 y14 : word), zlen r = 2^tl -> blA_inv m2 (2^tl) snext' r ->
       evtF bsegs RNG POST (STB 0x98048 m2 (2^tl) y8 y9 y10 y11 y13 y14)) ->
    evtF bsegs RNG POST (STB 0x97f38 m1 u x8 x9 x10 x11 x13 x14).
Proof.
intros f. induction f as [|f IH]; intros u snext acc r m1 q8 q9 q10 q11 q13 q14 HB HF HU HA HS SNB INV K; [lia|].
pose proof INV as INV0. destruct INV as (UT & UW & MU & WM & MI).
pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td).
pose proof (ablk_lin _ _ BWK) as (Wa & Wb & Wc & Wd).
unfold AIMG_HI in Ta, Wa.
unfold blA_W in MU.
assert (FDT1 : rw_cells bsegs m1 (SP + 32) [C8 (Z_to_bv 64 (TD - 4))])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 32) _ FDT MU WM); cbn [disjoint_from]; cbn; lia).
assert (FTL1 : rw_cells bsegs m1 (SP + 48) [C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 (- WK - 1))])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 48) _ FTL MU WM); cbn [disjoint_from]; cbn; lia).
assert (FWK1 : rw_cells bsegs m1 (SP + 80) [C8 (Z_to_bv 64 WK)])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 80) _ FWK MU WM); cbn [disjoint_from]; cbn; lia).
pose proof (zshadow_munch _ m m1 TD (4 * 2^tl) ZT MU (shad_outside2 TD (4 * 2^tl) TD (4 * 2^tl) WK (2 * M1) BTD BWK ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as ZT1.
pose proof (zshadow_munch _ m m1 WK (2 * M1) ZW MU (shad_outside2 WK (2 * M1) TD (4 * 2^tl) WK (2 * M1) BTD BWK ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as ZW1.
cbn [build_loop] in HB.
destruct (oload syms u) as [sym| | |] eqn:OL; cbn [bind] in HB; try discriminate HB.
destruct (load snext sym) as [nx| | |] eqn:LD; cbn [bind] in HB; try discriminate HB.
destruct (store snext sym (u16 (nx + 1))) as [snext1| | |] eqn:SD; cbn [bind] in HB; try discriminate HB.
destruct (highbit32 nx) as [hb| | |] eqn:HBT; cbn [bind] in HB; try discriminate HB.
destruct (shl32 nx (to_byte (tl - hb))) as [sh| | |] eqn:SHL; cbn [bind] in HB; try discriminate HB.
unfold ASHOFF.
zstep. wk_go [0x97f38; 0x98048; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc].
apply oload_Ok in OL as (OLR & OLN).
apply load_Ok in LD as (LDR & LDV).
apply store_Ok in SD as (SDR & SDV).
assert (LACC : length (concat (map fse_cell_bytes acc)) = (4 * Z.to_nat u)%nat).
{ pose proof (fse_cells_length acc) as FL. lia. }
destruct (tsym_at syms jt (Z.to_nat u) sym ltac:(lia) OLN) as (j0 & j1 & j3 & TSA).
assert (NB2 : nth_error (tdb jt syms acc u) (Z.to_nat (4 * u + 2)) = Some (Z_to_bv 8 sym)).
{ unfold tdb. rewrite TSA. apply nth_cell2. lia. }
pose proof (u8arr_read bsegs m1 TD _ (4 * u + 2) _ (Z_to_bv 64 (TD - 4 + 4 * u + 6)) UT NB2 ltac:(lia)
  ltac:(unfold wa; f_equal; lia)) as RDS.
zstep. clear RDS.
assert (SYB : 0 <= sym < M1) by (rewrite <- HS; exact LDR).
assert (UB : bv_unsigned (Z_to_bv 8 sym) = sym)
  by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
wk_post.
wk_go [0x97f38; 0x98048; 0x97f84; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc].
assert (WS : (WK + Z.shiftl sym 1) mod 18446744073709551616 = WK + 2 * sym)
  by (rewrite Z.shiftl_mul_pow2 by lia; change (2^1) with 2; rewrite Z.mod_small by lia; lia).
rewrite WS.
wk_go [0x97f38; 0x98048; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc].
assert (NXP : 0 < nx < 2^32)
  by (unfold highbit32 in HBT; destruct ((0 <? nx) && (nx <? 2^32)) eqn:E; [|discriminate HBT];
      apply andb_true_iff in E as (E1 & E2); apply Z.ltb_lt in E1; apply Z.ltb_lt in E2; lia).
assert (HBV : hb = Z.log2 nx)
  by (unfold highbit32 in HBT; rewrite (proj2 (andb_true_iff _ _) (conj (proj2 (Z.ltb_lt 0 nx) (proj1 NXP)) (proj2 (Z.ltb_lt nx (2^32)) (proj2 NXP)))) in HBT; injection HBT; lia).
assert (SNL : 0 <= sym < Z.of_nat (length snext)) by (unfold zlen in HS; lia).
assert (NXB : 0 <= nx < 65536) by (rewrite LDV; apply (Forall_Znth _ snext sym SNB); unfold zlen in HS; lia).
pose proof (u16_znth bsegs m1 WK snext sym (Z_to_bv 64 (WK + 2 * sym)) (proj1 UW) SNL ltac:(reflexivity)) as RDW.
zstep. clear RDW.
rewrite <- LDV.
assert (ZX : zx16 (Z_to_bv 64 nx) = Z_to_bv 64 nx)
  by (unfold zx16; f_equal; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616;
      rewrite (Z.mod_small nx 18446744073709551616) by lia; apply Z.mod_small; change (2^16) with 65536; lia).
rewrite ZX.
wk_go [0x97f38; 0x98048; 0x97f8c; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc].
assert (HS1 : store_ok bsegs m1 (Z_to_bv 64 (WK + 2 * sym)) 2 = true)
  by (apply (u16arr_store_ok bsegs m1 WK (map (Z_to_bv 64) snext) sym); [exact UW | rewrite length_map; lia | reflexivity]).
zstep.
set (m2 := write_to_mem m1 (Z_to_bv 64 (WK + 2 * sym)) (le2 (Z_to_bv 64 (nx + 1)))) in *.
assert (MU2 : munch [(TD, TD + 4 * 2^tl); (WK, WK + 2 * M1)] m m2)
  by (unfold m2; change (Z_to_bv 64 (WK + 2 * sym)) with (wa (WK + 2 * sym));
      apply munch_write_n with (n := 2); [reflexivity|lia|lia|exact MU|cbn; lia]).
assert (WM2 : wmono bsegs m m2) by (unfold m2; apply wmono_write; exact WM).
assert (MI2 : mem_inv bsegs m2) by (unfold m2; apply mem_inv_store; [exact MI|exact HS1]).
assert (UW2 : u8arr bsegs m2 WK (u16s (map (Z_to_bv 64) (Zupd sym (u16 (nx + 1)) snext)))).
{ unfold m2. rewrite map_Zupd by lia. change (Z_to_bv 64 (WK + 2 * sym)) with (wa (WK + 2 * sym)).
  rewrite (le2_eqm16 (nx + 1) (u16 (nx + 1))) by (unfold u16; rewrite Z.mod_mod by lia; reflexivity).
  apply u16arr_write; [exact UW | rewrite length_map; lia]. }
assert (UT2 : u8arr bsegs m2 TD (tdb jt syms acc u))
  by (unfold m2; change (Z_to_bv 64 (WK + 2 * sym)) with (wa (WK + 2 * sym));
      apply u8arr_frame_n with (n := 2); [reflexivity|lia|lia|exact UT|rewrite tdb_length; lia]).
wk_post.
wk_go [0x97f38; 0x98048; 0x97fac; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc].
pose proof (zshadow_munch _ m m2 TD (4 * 2^tl) ZT MU2 (shad_outside2 TD (4 * 2^tl) TD (4 * 2^tl) WK (2 * M1) BTD BWK ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as ZT2.
clear ZT1 ZW1.
wk_go [0x97f38; 0x98048; 0x97fac; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc].
do 4 zstep. set (sa := Z.lor nx (nx ≫ 1)) in *.
do 2 zstep. set (sb := Z.lor sa (sa ≫ 2)) in *.
do 2 zstep. set (sc := Z.lor sb (sb ≫ 4)) in *.
assert (SCB : 0 <= sc < 65536) by (unfold sc, sb, sa; apply (sm3_lt nx); lia).
do 3 zstep.
rewrite (shl48_shr56 sc) by lia.
change (Z.lor sc (sc ≫ 8)) with (sm4 nx).
rewrite (sm4_ones nx) by lia.
assert (KB : 0 <= Z.log2 nx <= 15)
  by (split; [apply Z.log2_nonneg | assert (Z.log2 nx < 16) by (apply Z.log2_lt_pow2; lia); lia]).
remember (Z.log2 nx) as k eqn:KD.
clear SCB. clearbody sa sb sc.
wk_go [0x97f38; 0x98048; 0x98008; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc].
lazymatch goal with |- _ => let v := reg_val 10%Z in lazymatch v with Z_to_bv 64 ?e =>
  let E := fresh "E" in
  assert (E : e = k) by (clear - KB; kenum16 k);
  rewrite E; clear E end end.
assert (FTL2 : rw_cells bsegs m2 (SP + 48) [C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 (- WK - 1))])
  by (unfold m2; change (Z_to_bv 64 (WK + 2 * sym)) with (wa (WK + 2 * sym));
      apply rw_cells_frame_n with (n := 2); [reflexivity|lia|lia|exact FTL1|cbn; lia]).
assert (FDT2 : rw_cells bsegs m2 (SP + 32) [C8 (Z_to_bv 64 (TD - 4))])
  by (unfold m2; change (Z_to_bv 64 (WK + 2 * sym)) with (wa (WK + 2 * sym));
      apply rw_cells_frame_n with (n := 2); [reflexivity|lia|lia|exact FDT1|cbn; lia]).
assert (FWK2 : rw_cells bsegs m2 (SP + 80) [C8 (Z_to_bv 64 WK)])
  by (unfold m2; change (Z_to_bv 64 (WK + 2 * sym)) with (wa (WK + 2 * sym));
      apply rw_cells_frame_n with (n := 2); [reflexivity|lia|lia|exact FWK1|cbn; lia]).
clear FTL1 FDT1 FWK1.
wk_go [0x97f38; 0x98048; 0x98014; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc].
assert (NBV : (tl - k) mod 256 = to_byte (tl - hb)) by (unfold to_byte; rewrite HBV, KD; reflexivity).
assert (HS2 : store_ok bsegs m2 (Z_to_bv 64 (TD - 4 + 4 * u + 7)) 1 = true)
  by (apply (u8arr_store_ok bsegs m2 TD (tdb jt syms acc u) (4 * u + 3)); [exact UT2 | rewrite tdb_length; lia | unfold wa; f_equal; lia]).
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?E) ?bs) _) =>
  set (m3 := write_to_mem mm (Z_to_bv 64 E) bs) in * end.
assert (MU3 : munch [(TD, TD + 4 * 2^tl); (WK, WK + 2 * M1)] m m3)
  by (unfold m3; change (Z_to_bv 64 (TD - 4 + 4 * u + 7)) with (wa (TD - 4 + 4 * u + 7));
      apply munch_write_n with (n := 1); [reflexivity|lia|lia|exact MU2|cbn; lia]).
assert (WM3 : wmono bsegs m m3) by (unfold m3; apply wmono_write; exact WM2).
assert (MI3 : mem_inv bsegs m3) by (unfold m3; apply mem_inv_store; [exact MI2|exact HS2]).
assert (LSN : Z.of_nat (length snext) = M1) by exact HS.
assert (UW3 : u8arr bsegs m3 WK (u16s (map (Z_to_bv 64) (Zupd sym (u16 (nx + 1)) snext))))
  by (unfold m3; change (Z_to_bv 64 (TD - 4 + 4 * u + 7)) with (wa (TD - 4 + 4 * u + 7));
      apply u8arr_frame_n with (n := 1); [reflexivity|lia|lia|exact UW2|rewrite ?u16s_length, ?length_map; unfold Zupd; rewrite ?upd_nat_length; rewrite Nat2Z.inj_mul, LSN; lia]).
assert (UT3 : u8arr bsegs m3 TD (upd (tdb jt syms acc u) (Z.to_nat (4 * u + 3)) (Z_to_bv 8 (bv_swrap 32 (tl - k)))))
  by (unfold m3; rewrite ?(FseWalkKit.le1_lit (bv_swrap 32 (tl - k)));
      replace (Z_to_bv 64 (TD - 4 + 4 * u + 7)) with (wa (TD + (4 * u + 3))) by (unfold wa; f_equal; lia);
      apply u8arr_write; [exact UT2 | rewrite tdb_length; lia]).
assert (FTL3 : rw_cells bsegs m3 (SP + 48) [C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 (- WK - 1))])
  by (unfold m3; change (Z_to_bv 64 (TD - 4 + 4 * u + 7)) with (wa (TD - 4 + 4 * u + 7));
      apply rw_cells_frame_n with (n := 1); [reflexivity|lia|lia|exact FTL2|cbn; lia]).
assert (FDT3 : rw_cells bsegs m3 (SP + 32) [C8 (Z_to_bv 64 (TD - 4))])
  by (unfold m3; change (Z_to_bv 64 (TD - 4 + 4 * u + 7)) with (wa (TD - 4 + 4 * u + 7));
      apply rw_cells_frame_n with (n := 1); [reflexivity|lia|lia|exact FDT2|cbn; lia]).
assert (FWK3 : rw_cells bsegs m3 (SP + 80) [C8 (Z_to_bv 64 WK)])
  by (unfold m3; change (Z_to_bv 64 (TD - 4 + 4 * u + 7)) with (wa (TD - 4 + 4 * u + 7));
      apply rw_cells_frame_n with (n := 1); [reflexivity|lia|lia|exact FWK2|cbn; lia]).
pose proof (zshadow_munch _ m m3 TD (4 * 2^tl) ZT MU3 (shad_outside2 TD (4 * 2^tl) TD (4 * 2^tl) WK (2 * M1) BTD BWK ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as ZT3.
clear FTL2 FDT2 FWK2 ZT2 UT2 UW2.
assert (TK : 0 <= tl - k < 32).
{ unfold shl32 in SHL. destruct ((0 <=? to_byte (tl - hb)) && (to_byte (tl - hb) <? 32)) eqn:E; [|discriminate].
  apply andb_true_iff in E; destruct E as [E1 E2]; apply Z.ltb_lt in E2.
  unfold to_byte in E2; rewrite HBV in E2.
  destruct (Z_lt_le_dec (tl - k) 0) as [N|N]; [|lia].
  replace ((tl - k) mod 256) with (tl - k + 256) in E2 by (apply Z.mod_unique with (q := -1); lia). lia. }
assert (A0E : Z.land (bv_swrap 32 (tl - k) mod 18446744073709551616) 255 = tl - k).
{ rewrite FseWalkKit.swrap32_small by lia. rewrite Z.mod_small by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
rewrite ?A0E.
wk_go [0x97f38; 0x98048; 0x97fac; 0x9804c; 0x98058; 0x98068; 0x98074; 0x980cc; 0x98040].
clear UT UW MU WM MI INV0 OLR OLN LDR SDR HBT NB2 SYB UB WS NXP KD SNL NXB ZX HS1 MU2 WM2 MI2 NBV HS2 FTL3 FDT3 FWK3 ZT3 DSP RSP FDT FTL FWK ZT ZW.
assert (HS3 : store_ok bsegs m3 (Z_to_bv 64 (TD - 4 + 4 * u + 4)) 2 = true)
  by (apply (u8arr_store_ok_n bsegs m3 TD _ (4 * u) 2 _ UT3);
      [lia | rewrite upd_length, tdb_length; lia | unfold wa; f_equal; lia]).
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?E) ?bs) _) =>
  set (m4 := write_to_mem mm (Z_to_bv 64 E) bs) in * end.
assert (SHV : sh = u32 (nx * 2 ^ (tl - k))).
{ rewrite (shl32_ok nx (to_byte (tl - hb))) in SHL.
  - injection SHL as <-. unfold to_byte; rewrite HBV, Z.mod_small by lia; reflexivity.
  - unfold to_byte; rewrite HBV, Z.mod_small by lia; lia. }
assert (NSV : bv_swrap 32 (bv_swrap 32 (nx ≪ ((tl - k) mod 32)) mod 18446744073709551616 - 2 ^ tl) mod 65536
              = u16 (sh - 2 ^ tl) mod 65536).
{ rewrite ns_mod16. rewrite (Z.mod_small (tl - k) 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite SHV. reflexivity. }
assert (UT4 : u8arr bsegs m4 TD (upd_bytes (upd (tdb jt syms acc u) (Z.to_nat (4 * u + 3)) (Z_to_bv 8 (bv_swrap 32 (tl - k))))
                                           (Z.to_nat (4 * u)) (le2 (Z_to_bv 64 (u16 (sh - 2 ^ tl)))))).
{ unfold m4. rewrite (le2_eqm16 _ (u16 (sh - 2 ^ tl))) by (rewrite NSV; reflexivity).
  replace (Z_to_bv 64 (TD - 4 + 4 * u + 4)) with (wa (TD + 4 * u)) by (unfold wa; f_equal; lia).
  apply u8arr_write_bytes; [exact UT3 | lia | rewrite upd_length, length_le2, tdb_length by lia; lia]. }
assert (MU4 : munch [(TD, TD + 4 * 2^tl); (WK, WK + 2 * M1)] m m4)
  by (unfold m4; change (Z_to_bv 64 (TD - 4 + 4 * u + 4)) with (wa (TD - 4 + 4 * u + 4));
      apply munch_write_n with (n := 2); [reflexivity|lia|lia|exact MU3|cbn; lia]).
assert (WM4 : wmono bsegs m m4) by (unfold m4; apply wmono_write; exact WM3).
assert (MI4 : mem_inv bsegs m4) by (unfold m4; apply mem_inv_store; [exact MI3|exact HS3]).
assert (UW4 : u8arr bsegs m4 WK (u16s (map (Z_to_bv 64) (Zupd sym (u16 (nx + 1)) snext))))
  by (unfold m4; change (Z_to_bv 64 (TD - 4 + 4 * u + 4)) with (wa (TD - 4 + 4 * u + 4));
      apply u8arr_frame_n with (n := 2); [reflexivity|lia|lia|exact UW3|rewrite ?u16s_length, ?length_map; unfold Zupd; rewrite ?upd_nat_length; rewrite Nat2Z.inj_mul, LSN; lia]).
assert (NBE : bv_swrap 32 (tl - k) = to_byte (tl - hb))
  by (rewrite FseWalkKit.swrap32_small by lia; unfold to_byte; rewrite HBV, Z.mod_small by lia; reflexivity).
rewrite NBE in UT4.
assert (CB : fse_cell_bytes (mkDC (u16 (sh - 2 ^ tl)) sym (to_byte (tl - hb)))
             = le2 (Z_to_bv 64 (u16 (sh - 2 ^ tl))) ++ [Z_to_bv 8 sym; Z_to_bv 8 (to_byte (tl - hb))]) by reflexivity.
assert (TDB4 : upd_bytes (upd (tdb jt syms acc u) (Z.to_nat (4 * u + 3)) (Z_to_bv 8 (to_byte (tl - hb))))
                 (Z.to_nat (4 * u)) (le2 (Z_to_bv 64 (u16 (sh - 2 ^ tl))))
               = tdb jt syms (acc ++ [mkDC (u16 (sh - 2 ^ tl)) sym (to_byte (tl - hb))]) (u + 1)).
{ unfold tdb. rewrite TSA.
  replace (Z.to_nat (4 * u + 3)) with (length (concat (map fse_cell_bytes acc)) + 3)%nat by (rewrite LACC; lia).
  rewrite cell_write_nb.
  replace (Z.to_nat (4 * u)) with (length (concat (map fse_cell_bytes acc))) by (rewrite LACC; lia).
  rewrite cell_write_ns, fse_cells_snoc, CB.
  replace (Z.to_nat (u + 1)) with (S (Z.to_nat u)) by lia.
  rewrite !app_assoc. reflexivity. }
assert (INV4 : blA_inv m4 (u + 1) snext1 (acc ++ [mkDC (u16 (sh - 2 ^ tl)) sym (to_byte (tl - hb))])).
{ unfold blA_inv. rewrite <- TDB4, SDV. split; [exact UT4|]. split; [exact UW4|]. split; [exact MU4|]. split; [exact WM4|exact MI4]. }
assert (SN1 : zlen snext1 = M1) by (rewrite SDV; unfold Zupd; rewrite upd_nat_length; exact LSN).
assert (OK1 : Forall (fun v => 0 <= v < 65536) snext1)
  by (rewrite SDV; unfold Zupd; apply Forall_upd_nat; [exact SNB | unfold u16; apply Z.mod_pos_bound; lia]).
assert (HA1 : zlen (acc ++ [mkDC (u16 (sh - 2 ^ tl)) sym (to_byte (tl - hb))]) = u + 1)
  by (rewrite length_app; cbn [length]; lia).
clear - IH K HB HF HU HA1 SN1 OK1 INV4 Ta Tb Tc Td HTL.
replace (4 * u + 4) with (4 * (u + 1)) by lia.
zstep.
destruct (Z.eq_dec (u + 1) (2 ^ tl)) as [EQ|NE].
- wk_if_false. destruct f as [|f]; [|lia]. cbn [build_loop] in HB. injection HB as <-.
  rewrite EQ in INV4 |- *. rewrite EQ in HA1.
  exact (K _ _ _ _ _ _ _ _ HA1 INV4).
- wk_if_true. destruct f as [|f]; [lia|].
  exact (IH (u + 1) snext1 _ r m4 _ _ _ _ _ _ HB ltac:(lia) ltac:(lia) HA1 SN1 OK1 INV4 K).
Qed.
End Build.
End CANSEC1.
