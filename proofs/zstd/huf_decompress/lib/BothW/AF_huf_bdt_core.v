(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface RF_huf_bdt_model RF_huf_bdt_fast.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_bdt_lp AF_huf_bdt_fast AF_huf_bdt_gen AF_huf_bdt_bld.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkArith StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_bdt_core () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib7Classes9MorphismsCeq_rewrite_relationK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=pow_lt_mono_rK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission6Common:STRW_merge=swrap32_smallC56Stdlib6ZArith6BinInt1Z:shiftl_1_lC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z;pow_nonzeroC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:table_stepK46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model@build_dtable_invC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompJFSE_BUILD_DTABLE_WKSP_SIZEI47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<lowprob_loopK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;spread_loopC47Corelib4Init5Logic3notI47Corelib4Init5Logic2ex00c5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_core?fse_build_postCC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6dtable01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<build_dtableC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init5Peano2ltK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit<lowprob_lenAC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Z2Nat2idC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem4core01C56Stdlib6ZArith6BinInt1Z9add_assocC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C47Corelib4Init3Nat3mulC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5low32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1K4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sllwC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_sllwK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_core7a2_valAC47Corelib4Init3Nat3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib5Lists4List<length_skipnC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit>app_vs_shadowZC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit=zshadow_munchc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_core;zshadow_subC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9nshad_divC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model9u8arr_appC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC5ARocqVerifyHarness?AgentSubmission3Lib3ArrArw_cells_of_u8arrC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model4tsymC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model9tsym_noneC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit3wkbI47Corelib4Init5Peano2le00K47Corelib4Init5Logic2or02C46Stdlib5Lists4List=repeat_lengthC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_bdt_lp6lpA_okC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_bdt_lp7lpA_invC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_bdt_lp5lpA_WK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell03C47Corelib7Classes9Morphisms:respectfulC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismI4ELinuxProcessSemantics5Riscv7Prelude4tree00C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib4Init3Nat3addC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_bld5blA_WC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_bld7blA_invC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_bld3tdbK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseC46Stdlib5Lists4List:skipn_all2C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit9tsym_nilAC46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission3Lib3Tac>rw_cells_mergeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3ArrAu8arr_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le2C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List9app_assocC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_tableLogC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_fastModeC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8dt_cellsK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_bld8bl_loopAC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4chkZC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbK4ELinuxProcessSemantics5Riscv5Instr5instr06C5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit7acc_shZC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit:wkb_lengthC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;tsym_lengthK4ELinuxProcessSemantics5Riscv5Instr5instr07C5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_2'C5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_gen7gnA_invC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_gen8gn_loopAc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_core:step_val2AC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model6omergeC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;omerge_noneC46Stdlib9micromega;ZifyClasses:impl_morphC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_fast7spA_invC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z8mul_commC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_fast7plA_invC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_fast8pl_loopAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_fast9sp_outerAc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_core9step_valAC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_bdt_lp8lp_loopAC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;shl32_shr31c5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_core7t6_valAC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:place_loopC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8gen_loopC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:build_loopC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK46Stdlib9micromega:ZMicromega;ZArithProof03I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC46Stdlib5Lists4List6concatC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface<fse_dt_bytesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6dtable00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIK4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib7Numbers7BinNums1N01C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib6ZArith4Znat5Nat2Z6inj_leI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface>fse_cell_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Program6Basics4implC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC47Corelib7Classes?RelationClasses>impl_ReflexiveC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litK4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4sxb0C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface=AFSE_BUILD_DT".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma a2_valA : forall tl, 1 <= tl <= 12 -> bv_swrap 32 (1 ≪ (tl mod 32)) = 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_core ()) ["CANSEC1"] "h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h62Hah74__x2h81zh91Hh:2H0h;6__sat0h<6__sat1h=2tlp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0P3p4p710R3p9P0p1002Qp4p710R0p9p1003Ip4p710R5p1003fp4p710p8P5g004BR5p4p710R6p8p1004`p4p7210R7P1p8P7P2p8P7P4p8P7P3p8P7p1005Lp4p710p8P7P6p8P7P0p8g006<j1:Tg006Zj29Tg0076j1<Tg007[j13Tg008@j2=Tg008[j1UTg0099j2BTg009Yj2ATg00:@j26Tg00:]j3>Tg00;7j21Tg00;Sj2CTg00<;j3^Tg00<_j1[Tg00=?j1VTg00=_j2ETg00>=j1TTg00>[j4STg00?9j1OTg00?Wj1NTg00@Bj25Tg00@ej1LTg00AGj2@Tg00Ajj2KTg00BLj2JTg00Bfj2ITg00CRj3MTg00D1j4HTg00Dcj6PTg00EJj4QTg00Eej2GTg00Fij1RTP5j6DTg00GMj2]Tg00Gmj3\Tg00HPj4FTg00I;j7ZTg00I_j8WTg00JCj6XTg00Jgj7YTg00KKR5f0R0'9p=2g00KiR7f1R6g00LGP0CFp=8P6g00LnR3g00MMR4P4g00MmR2P0g00NMFZp=0P7P6g00NmP0CFp=7f3R1P3P4P4P2f2R8P6P0GWp=4P6P3P4P4P2P0EXp=?P8P3P4P4P2P6P0FYp=;g00OTR3#:R9/90%<3R:#3#3#:R;,90R<'=R=P7P6%33R>#3#3#3#3R?#UR@1B90'A%:>RA/68RB5>7X87P716A6RC1A@0=>7BX87%2C%<:#<#<#:R:,6A,1C1CA6115ARB%28R@16A1,15[[1CA8%21f4RD,6A,15[\B%2AREg00P9RFf5RG=^A6UW616AGRH#2\F^6Ep-0REg00PURF#[RI%VFRFP71E78P6%T7RJCS%O7RK%N7RLPL1575RM157ARN'8,0L%L4R4PL1@7>R>,7M,0LP41@73R3,8M,0LC4C4P4PL1579RO/7>,0L1?LD5;LP417M3,0LR>C4C41KL2R2P0P8g00QARPg00QaRQ'J1I08=>PQdAM756CHRQb2b3b4X07X77W51158\@\B1998RB/=1P@[[^07^77^5EP019G;PGPHP8PDO5b1b;b<b:PAP6P:PIPFPJPK18ON,0LP2PQb2b3b4119AP0b1PIPFPJPK157:RJ,7M,0LP2PQb2b3b4%2:P0b1PIPF1E76RMPKPL1?L1157;,73,0LR;5;LP4183J,0LC4P2PQb2b3b4X07X5E1=6<116:[^07^5EP0PBP8P6O3b1EPCQ,GC1B96%R6ED%:?R?,]6PIPFPMPKPL17O3,0L=;L;P4157?,83,0L9;L>C4P2PQb2b3b4X07%26116?'=\=^07P0P8P6O2b19\6?EDW9X=7o"). Qed.

Lemma t6_valA : forall tl, 1 <= tl <= 12 ->
  bv_swrap 32 (bv_wrap 32 (bv_swrap 32 (32768 ≪ (tl mod 32)) mod 18446744073709551616) ≫ 16) = 2^(tl-1).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_core ()) ["CANSEC1"] "h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h61zh72Hah82H0h94__x2h:1Bh;2B0h<1Hh=6__sat1h>6__sat2h?6__sat3h@6__sat4hA2tlp;1p;2p;3p;4p;5p;6p;7p;8g006<j19Tg006Zj26Tg0076j1DTg007[j11Tg008@j2@Tg008[j1\Tg0099j2STg009Yj2;Tg00GMj2FTg00RAj2GTg00Rgj2ETg00SGj27Tg00:@j20Tg00Sdj2BTg00<_j1vTg00=?j1pTg00=_j2UTg00?9j1iTg00?Wj1hTg00AGj2XTg00TAj3RTg00Ajj2dTg00BLj2cTg00Bfj2bTg00:]j3ITg00CRj3aTg00D1j4`Tg00Tdj25Tg00@ej1_Tg00@Bj2OTg00>=j1yTg00UAj5^Tg00Udj3]Tg00VGj5xTg00;Sj4wj2JTg00Vnj2HTg00WKj3ZTg00;7j2=Tg00<;j3YTg00>[j4uTg00Dcj6tTg00EJj4qTg00Eej2WTg00Wnj6oTg00XRj4nTg00Y7j3jTg003fj6VTg00YXj3kTg00ZAj2lTg00Gmj3TTg00[Dj3mTg00[gj3gTg00HPj4NTg00I;j7MTg00JCj6fTg00Jgj7rTg00I_j8sTg004Bj6eTf0R0#1#1p=[%10#1#1#1#1#1#1#1p=C%10#1#1#1p=Qg00KiR1f1R2;I0p=31O10p=8P1P2g00\PP0CNp=LP2g00LnR3g00MMR4P4g00MmR5P0g00NMR6FMp=Kf2R7P3P4P4P5P1P2g00NmP0CNP6FMp=:P2P3P4P4P5P0Efp=PP7P3P4P4P5P2P0Frp=>f3R8P3P4P4P5P7P2P0Gsp=2g00KKR9/60p=4P1f4R:P8P7P2P0Eep=<P7P3P4P4P5P1P2g00LGP0CNP6FMp=?1=90p=Ag00OTR6#9R;/60R<%D6R=#1R>#1#9R?,60R@'@RAP2%16RB#1#[RC#1RD#\RE%[D#CRF#9RG/S0,;E%QF#CRF#1#QRH#C#C#C#C#9RI'F,GE%9CRC'E';%9BRJ177;RK'0RL'3X6110J2RM,BGRN1;E0RO/FI,GE/EC,;ERP/3LX61%D=#DR=#9RL,0J,BM10J7RM,BGRQ,30X61g00PURR#vRS%pRRR1U12RT%i1RU%h1RV1X16R6%8GRW5R1AR1W6'L'K1dV5RWP0P7g00QARXg00QaRY'c1b07=IXYdAa192C`RYb2b3b4X011B0G1BG0'3^01P0PMO1b1152LRM,0JRXPJP2PLp-0RZPSPRPTPUPV%8;R[=:V6R\1PV8R]5>VR^%_4R_1O19R`=:V6RaC2PWPYb2b3b4X01W51@<2R<%42Rb[^01^5ZP0167?P7P2O3b1RcPSPR%y1RdPU%8LRe9:V`PWPYb2b3b4%4LP0b1D^D<13XNP1157LRX,0JRN178;,0J,3PX61PJPX%D>#D#9R>PSPRPdPU%8JRX9?V`RPPWPYb2b3b4%AJRfP0b1RgPSPRPTPUPV%8?9:V6Rh9>V]R]P_A]16eRe%8>5:VC2PWPYb2b3b4X01X5Z1@2@R@16M>[^01^5ZP016;8P8P7O3b1Dx10J>,6NPJ158LRNPgPSPRPTPUPVP^P_A:V`eC2PWPYb2b3b4X01X5Z%4M\<^01^5ZP016:?P:P8O3b1Cw10JN#A15:LRN,0JRM1F0I,GE/EC,;Ef5Rg/7;R>,0JRi'3X61PM1GE0/EC,;E/3iX61PM1E0C,;E/3iX6110JCRj,HM13OiX61PSPRPTPUAZ16[Rk%8CRl5]1/Le,KVPWPYb2b3b4X01170;/5C150L'3^01P0PgO1b117:;/5C/3NP115>CRN10J0/Hj,;Ef6Re/7;Rm,0JRn'3X611BijRo1H0j,;E/3nX61Pi13OnX61%4i%D=R=#9Rn,0JRO,=i1JJ>%4mf7Rm/7;,0J#A[\f15eL,JJ15mL#4f8Rm/5L,0J#A[\f%4JRpg00P9Rqf9Rr/5LRs=YJ2UW710Js#4\q^7p17m;,JJ17r;#4f:Rr/7;,0J#A[\ff;Rm/7;Rs=YJ2VqX7p10JsRs#4\q^7pPSPRP11U17P2PdCuPUPVPVPPP_PV1X1BRB=Z1[9:V`P_A?V`6RPC2C2P_PVA:V[B1PV:5>VP_PaC2C2PWPYb2b3b4X01X91X5Z%4K%A7[\f16;7/@8%47R8[[^01^91^5ZP016m?PmPsP7PrO5b1b=b>b?b@b8PJP>PnPSPRPdPUA?V[XPWPYb2b3b41=;JP0b1PSPRPdPU%8nR[9:V`PWPYb2b3b4%4nP0b1PSPRPTPUPVP]P_A?Vk[C2PWPYb2b3b4X01X5Z172;R[/=n\@^01^5ZP016;ePePgO3b1EtCq,Wi1HojPJPCPSPRPdPUPVP3P4P4P51LX`,KVEoPWPYb2b3b4AI1J9g00]7[P0b1PSPRPdPUA:V`lPWPYb2b3b4%4CP0b1RlCn9jijD<10JNPJP>PCPSPRPTPUPVP^P_A:V`kC2PWPYb2b3b4X01X5Z%4[\<^01^5ZP016e?PePgO3b1PlD^D<15gLRgP0EVb81EMCAkMClD<1GEMPSPRPTPUPVPPP_PV%9FRF#89:V6RlP_%9HRH#89?V69>VaC2C2PWPYb2b3b4X01%A0RC162FRF1=7H,@8[[^01P010JgP2P7O3Rgb1,lMD<1FMIPSPRPTPUPVPPP_PVPlP_%8I9?V69>VaC2C2PWPYb2b3b4X011=7I,@8\F\C^01Pgb19TMID<1;EMPSPRPTPUPVPPP_PVPlP_%\=9m1X9?V69>VaC2C2PWPYb2b3b4X011=7O,@8\F\C^01Pgb1,WMD<b;b:PQP0EVb81SG2AgG2cD<%9DRD,F2PSPRPTPUPVA>V\hP_%8D9?V69>VaC2PWPYb2b3b4X011=2D,@b\A^01P0P7P2O2b19T2DD<W<XA1o"). Qed.

Lemma zshadow_sub : forall m A n A' n', zshadow m A n -> A <= A' -> A' + n' <= A + n -> zshadow m A' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_core ()) ["CANSEC1"] "h04__x1h14__x2h24__x3h34__x4h44__x5h51Ah62A'h72H1h82H2h92Hah:2Z0h;7__arithh<4__ffh=8__varmaph>5__with?1ah@1mhA1nhB2n'p;1p;3p;2p;4p;7p;8g007[j13Tg008[j1CTg00]Tj1DTg00^7j1JTg00^Yj3FTg006Zj20Tg00Tdj21Tg00;7j2<Tg008@j2:Tg00_\j16Tg00`;j25Tg00`dj37Tg00aMj2ATg00<_j1VTg00b9j3ETg00=?j1UTg00=_j2BTg00>=j1TTg00>[j4=Tg00?9j1RTg00?Wj1QTg00AGj24Tg0076j1@Tg00Udj3?Tg00HPj49Tg00@ej1LTg00Ajj2KTg00BLj2ITg00Bfj2MTg00:]j3NTg00CRj3HTg00D1j4OTg00I;j7PTg00Jgj7GTg00I_j8STg00KiR0f1R1g00Nmf0R2C9p=8P1g00LnR3g00MMR4P4g00MmR5P2g00NMFPp=2f2R6P3P4P4P5P1P2FGp=>f3R7P3P4P4P5P6P1P2GSp=;g00OTR3#3R8#3R9#3R:#3#3#3#C#D%C:#D#J[f4R:?F7610:61176f5R;/1:R<'010;21<2<':P:P1g00PUR<g00bYR=#6R>#6R?#6R@,50150?150=R=570570g00c8R?'A%6@,50150>=70=570/A?%V<5E<3E%U<P0P01B0:P6%T0R<C=P1P01B0;P7P<C=C=%R0%Q0R<1409R91408R?'8,2<P0P?g00LGR=%@8,409?09R8C9,2<5><%L4R4P<1403R>%@3,405?0R3,88,2<P4P<18>9,2<P418>?,2<P0P?P=P3C9,2<5><C;C;C;1K<5P2P6g00QAR<g00QaR5'I1M26=N<5dg00KK=H01COb<b=b>X00X10X20X30X401071117:,<1':11:;1117'0106;107:117;,<:':[[[^00^10^20^30^40P2f6f7R2f8P6f9P1P7P:O8b;O2W9X?0AF2:7eW8W7W:XB0X60XA0X50W@o"). Qed.

Lemma step_val2A : forall tl, 1 <= tl <= 12 ->
  bv_swrap 32 (bv_wrap 32 (2 ^ tl) ≫ 3) + bv_swrap 32 (bv_wrap 32 (2 ^ tl) ≫ 1) + 3 = table_step (2^tl).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_core ()) ["CANSEC1"] "h01Hh11Th22H0h34__x1h42tlh57__arithh64__ffh78__varmaph85__witp;1p;2p;4p;7p;8p;3g006<j17Tg0076j1CTg007[j1@Tg00<_j1gTg00=?j1`Tg00=_j2\Tg00?9j1XTg00?Wj1VTg00AGj2QTg00HPj4BTg00Jgj7fTg00@ej1dTg00I_j8ZTg00Ajj2YTg00BLj2MTg00Bfj2WTg00:]j33Tg00CRj3UTg00D1j4TTg008[j1PTg00:@j22Tg00RAj25Tg006Zj2ETg00cdj1aTg008@j2HTg00@Bj2FTg00I;j7DTg00djj7GTg00eNR0j2ATg00Rgj2?Tg00Tdj2;Tg009Yj2ITg004Bj7]Tf3R1f2R2'Ef1R3f0R4'E'Hp=8g00KiR5/F4p=KP3g00LnR6g00MMR7P7g00MmR8P4g00NMR9FDp=LP5P3g00\PR:P4CBp=bP5P3P:1F54CBp=_P2P6P7P7P8P5P3P:P4CBP9FDp=^f4R;P6P7P7P8P1P6P7P7P8P5P2P:1F53CBP9FDP4FGp=>f6R:P6P7P7P8f5R<P6P7P7P8P;P9FDP1P6P7P7P8P2P6P7P7P8P3P9FDP4FGFGp=[f7R9=35:A35<;A3512A3534'A'A'Ap==A35;1A3523/A4'Ap=0A3534p=1A35<;A3512A3534'A'Ap=<1?;11?23';/;4p=:1?:<,I91?12,I;';/;3=354p=91?34,I2p=J1;23/;4p=O1?121?34';p=R1;349352p=S1E23/H4p=e1?;11?23';/;4,M5p=6P5P<P;P1P2P3P4F]p=4A3512A3534'Ap=N1E34,H2p=cg00OTR=#7R>P4P4%C=R?#@R@#@#7RAC8RBg00PURC#g%`C1\53%X5%V5RCP6P7P7P8PCP6P7P7P8P5%K>R6g00NmRD1Q5=RECB,LCP5PEPD%KARDCB,LCFf%d7PCPC1bE6PCPC%@=R=#7R6,_EPCPCPE%7?R7PCPCPE%@=RF#7RGPCPCPE%C=R=#7RHPCPCPE%7@R@PCPCPE%C?#7R?PCPCPE%@FRI#7RJPCPCPE%CF#7RFPCPCPE%@=#7RKPCPCPE%C=#7R=A^CEDD>D>D>D>D>D>D>D>D>F[GZ1YC8P4P2g00QARCg00QaR8'M1W42=3C8dg00KK=U53CTb6b7b8X35P3P>P3P6P3P7P3PGP3PHP3P@P3P?P3PJP3PFP3PKP3P=P3PAG=D0D0D0D0R8\B^35P4P2P3O2b5P8P0112>P2P6P2P7P2PGP2PHP2P@P2P?P2PJP2PFP2PKP2P=P2PAE<D0D0D0D0%@I#@#PRI1261R2,5IR8P7PIP8P>P7P2P>P2P7P7D:G9P4111>P>1263R3,5IR2=JI7AJI2>;O7R2P3P>P3P7CR;S7^0BX45RB1E>AR89e>>126>RCP>PCP7P7D6W0P;P4P1E4W2P4O1P1P6P1P7P1PGP1PHP1P@P1P?P1PJP1PFP1PKP1P=P1PAE<D0D0D0D0P011;6P;P7P;PGP;PHP;P@P;P?P;PJP;PFP;PKP;P=P;PAG=D0D0D0PI126<R;,5IR1P7PIP1P>P7P;P>P;P7P7D:G9P411<6P6PBP>P6P6PAC81266R;P>P;P7P7D6W0P:P4P<E4W2P4O1P<P7P<PGP<PHP<P@P<P?P<PJP<PFP<PKP<P=P<PAG=D0D0D0P011:7P:PGP:PHP:P@P:P?P:PJP:PFP:PKP:P=P:PAE<D0D0D0PI1269R:,5IR<P7PIP<P>P7P:P>P:P7P7D:G9P41197P7PBP>P7P7PAC81267R:P>P:P7P7D6W0f8R:P4P9E4W2P4O1P9PGP9PHP9P@P9P?P9PJP9PFP9PKP9P=P9PAE<D0D0D0P011:GP:PHP:P@P:P?P:PJP:PFP:PKP:P=P:PAG=D0D0PIf9R:,26R9,5IR<P7PIP<P>P7P9P>P9P7P7D:G9P411:GPGPBP>PGPGPAC8126GRGP>PGP7P7D6W0f:RGP4P:E4W2P4O1P:PHP:P@P:P?P:PJP:PFP:PKP:P=P:PAG=D0D0P011GHPGP@PGP?PGPJPGPFPGPKPGP=PGPAE<D0D0PIf;RG,26R:,5IR9P7PIP9P>P7P:P>P:P7P7D:G9P411GHPHPBP>PHPHPAC8126HRHP>PHP7P7D6W0f<RHP4PGE4W2P4O1PGP@PGP?PGPJPGPFPGPKPGP=PGPAE<D0D0P011H@PHP?PHPJPHPFPHPKPHP=PHPAG=D0PIf=RH,26RG,5IR:P7PIP:P>P7PGP>PGP7P7D:G9P411H@P@PBP>P@P@PAC8126@R@P>P@P7P7D6W0f>R@P4PHE4W2P4O1PHP?PHPJPHPFPHPKPHP=PHPAG=D0P011@?P@PJP@PFP@PKP@P=P@PAE<D0PIf?R@,26RH,5IRGP7PIPGP>P7PHP>PHP7P7D:G9P411@?P?PBP>P?P?PAC8126?R?P>P?P7P7D6W0f@R?P4P@E4W2P4O1P@PJP@PFP@PKP@P=P@PAE<D0P011?JP?PFP?PKP?P=P?PAG=PIfAR?,26R@,5IRHP7PIPHP>P7P@P>P@P7P7D:G9P411?JPJPBP>PJPJPAC8126JRJP>PJP7P7D6W0fBRJP4P?E4W2P4O1P?PFP?PKP?P=P?PAG=P011JFPJPKPJP=PJPAE<PIfCRJ,26R?,5IR@P7PIP@P>P7P?P>P?P7P7D:G9P411JFPFPBP>PFPFPAC8126FRFP>PFP7P7D6W0fDRFP4PJE4W2P4O1PJPKPJP=PJPAE<P011FKPFP=PFPACNPIfERF,26RJ,5IR?P7PIP?P>P7PJP>PJP7P7D:G9P411FKPKPBP>PKPKPAC8126KRKP>PKP7P7D6W0fFRKP4PFE4W2P4O1PFP=PFPACNP011K=11KAPIfGRK,26R0,5IRFP7PIPFP>P7P0P>P0P7P7D:G9P411K=P=PBP>P=P=PAC8126=R=P>P=P7P7D6W0fHR=P4PKE4W2P4O111KAPAPBAc8AA126AR6P>P6P7P7D6W0P=P4PKE4W1P4O1n200100000021000010000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1P4O1n200100000021000011000b1%a3,12eW0X45o"). Qed.

Lemma step_valA : forall tl, 1 <= tl <= 12 ->
  bv_swrap 32 ((bv_swrap 32 (bv_wrap 32 (2 ^ tl) ≫ 3) + bv_swrap 32 (bv_wrap 32 (2 ^ tl) ≫ 1)) mod 18446744073709551616 + 3)
  = table_step (2^tl).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_core ()) ["CANSEC1"] "h01Hh11Th22H0h34__x1h42tlh57__arithh64__ffh78__varmaph85__witp;1p;2p;4p;7p;8p;3g006<j15Tg0076j1GTg007[j13Tg00<_j1kTg00=?j1aTg00=_j2]Tg00?9j1YTg00?Wj1WTg00AGj2TTg00HPj4DTg00Jgj7jTg00@ej1eTg00I_j8[Tg00Ajj2ZTg00BLj2OTg00Bfj2XTg00:]j34Tg00CRj3VTg00D1j4UTg008[j1STg00:@j22Tg00RAj29Tg006Zj2FTg00cdj1_Tg008@j2JTg00@Bj2KTg00I;j7ETg00djj7ITg00eNR0j2ATg00Rgj2BTg009Yj2HTg00Tdj2>Tg00GMj2QTg004Bj7fTf3R1f2R2'Ff1R3f0R4'F'Jp=<g00KiR5/K4p=MP3g00LnR6g00MMR7P7g00MmR8P4g00NMR9FEp=NP5P3g00\PR:P4CDp=cP5P3P:1K54CDp=`P2P6P7P7P8P5P3P:P4CDP9FEp=^f4R;P6P7P7P8P1P6P7P7P8P5P2P:1K53CDP9FEP4FIp=@f6R:P6P7P7P8f5R<P6P7P7P8P;P9FEP1P6P7P7P8P2P6P7P7P8P3P9FEP4FIFIp=\f7R9=45:A45<;A4512A4534'A'A'Ap=?A45;1A4523/A4'Ap=0A4534p=1A45<;A4512A4534'A'Ap==%34#3p=L1B34,H2p=6%34#3#3#3#3#3#3#3p=C1B;11B23'>/>4p=:1B<;,H:/>1/Q2/>3,H9=454p=;1>23/Q4p=R1>34,H2p=i1B121B34'>p=h1>349452p=g1F23/J4p=d1B;11B23'>/>4,O5p=8P5P<P;P1P2P3P4Ffp=7A4512A4534'Ap=P1F34,J2p=bg00OTR=#5R>P4P4%G=R?#3R@#3#5RAC<RBg00PURC#k%aC1]53%Y5%W5RCP6P7P7P8PCP6P7P7P8P5%M>R6g00NmRD1T5=RECD,NCP5PEPD%MARDCD,NCFj%e7PCPC1cE6PCPC%3=R=#5R6,`EPCPCPE%5?R7PCPCPE%3=RF#5RGPCPCPE%G=R=#5RHPCPCPE%5@R@PCPCPE%G?#5R?PCPCPE%3FRI#5RJPCPCPE%GF#5RFPCPCPE%3=#5RKPCPCPE%G=#5R=A^CEDD@D@D@D@D@D@D@D@D@F\G[1ZC8P4P2g00QARCg00QaR8'O1X42=4C8dg00KK=V53CUb6b7b8X35P3P>P3P6P3P7P3PGP3PHP3P@P3P?P3PJP3PFP3PKP3P=P3PAG?D0D0D0D0R8\B^35P4P2P3O2b5P8P0112>P2P6P2P7P2PGP2PHP2P@P2P?P2PJP2PFP2PKP2P=P2PAE=D0D0D0D0%LIRI#SR2P21261R8,92RCP7A62C>%3I#L#C#C#C#C#C#C#C#5RIP7P8P>P8P7P7D:G;P4111>P>1263R3,92R8=627A628>;RI=i27R8P3P>P3P7Ch;g7^0BX45RB1F>ARC9d>>126>RDP>PDP7P7D8W0P;P4P1E7W2P4O1P1P6P1P7P1PGP1PHP1P@P1P?P1PJP1PFP1PKP1P=P1PAE=D0D0D0D0P011;6P;P7P;PGP;PHP;P@P;P?P;PJP;PFP;PKP;P=P;PAG?D0D0D0P2P2126<R;,92R1P7A621>PIP7P;P>P;P7P7D:G;P411<6P6PBP>P6P6PAC<1266R;P>P;P7P7D8W0P:P4P<E7W2P4O1P<P7P<PGP<PHP<P@P<P?P<PJP<PFP<PKP<P=P<PAG?D0D0D0P011:7P:PGP:PHP:P@P:P?P:PJP:PFP:PKP:P=P:PAE=D0D0D0P2P21269R:,92R<P7A62<>PIP7P:P>P:P7P7D:G;P41197P7PBP>P7P7PAC<1267R:P>P:P7P7D8W0f8R:P4P9E7W2P4O1P9PGP9PHP9P@P9P?P9PJP9PFP9PKP9P=P9PAE=D0D0D0P011:GP:PHP:P@P:P?P:PJP:PFP:PKP:P=P:PAG?D0D0P2P2f9R:,26R9,92R<P7A62<>PIP7P9P>P9P7P7D:G;P411:GPGPBP>PGPGPAC<126GRGP>PGP7P7D8W0f:RGP4P:E7W2P4O1P:PHP:P@P:P?P:PJP:PFP:PKP:P=P:PAG?D0D0P011GHPGP@PGP?PGPJPGPFPGPKPGP=PGPAE=D0D0P2P2f;RG,26R:,92R9P7A629>PIP7P:P>P:P7P7D:G;P411GHPHPBP>PHPHPAC<126HRHP>PHP7P7D8W0f<RHP4PGE7W2P4O1PGP@PGP?PGPJPGPFPGPKPGP=PGPAE=D0D0P011H@PHP?PHPJPHPFPHPKPHP=PHPAG?D0P2P2f=RH,26RG,92R:P7A62:>PIP7PGP>PGP7P7D:G;P411H@P@PBP>P@P@PAC<126@R@P>P@P7P7D8W0f>R@P4PHE7W2P4O1PHP?PHPJPHPFPHPKPHP=PHPAG?D0P011@?P@PJP@PFP@PKP@P=P@PAE=D0P2P2f?R@,26RH,92RGP7A62G>PIP7PHP>PHP7P7D:G;P411@?P?PBP>P?P?PAC<126?R?P>P?P7P7D8W0f@R?P4P@E7W2P4O1P@PJP@PFP@PKP@P=P@PAE=D0P011?JP?PFP?PKP?P=P?PAG?P2P2fAR?,26R@,92RHP7A62H>PIP7P@P>P@P7P7D:G;P411?JPJPBP>PJPJPAC<126JRJP>PJP7P7D8W0fBRJP4P?E7W2P4O1P?PFP?PKP?P=P?PAG?P011JFPJPKPJP=PJPAE=P2P2fCRJ,26R?,92R@P7A62@>PIP7P?P>P?P7P7D:G;P411JFPFPBP>PFPFPAC<126FRFP>PFP7P7D8W0fDRFP4PJE7W2P4O1PJPKPJP=PJPAE=P011FKPFP=PFPACPP2P2fERF,26RJ,92R?P7A62?>PIP7PJP>PJP7P7D:G;P411FKPKPBP>PKPKPAC<126KRKP>PKP7P7D8W0fFRKP4PFE7W2P4O1PFP=PFPACPP011K=11KAP2P2fGRK,26R0,92RFP7A62F>PIP7P0P>P0P7P7D:G;P411K=P=PBP>P=P=PAC<126=R=P>P=P7P7D8W0fHR=P4PKE7W2P4O111KAPAPBAbCAA126AR6P>P6P7P7D8W0P=P4PKE7W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000b1%_3,18eW0X45o"). Qed.

(* [comment removed for export] *)
Definition fse_build_postC (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (SPV DT WK msv tl : Z) (d : dtable) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPV - AFSE_BUILD_STACK, SPV); (DT, DT + FSE_DTABLE_SIZE tl); (WK, WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ u8arr bsegs m' DT (fse_dt_bytes d).

Section Core.
  Variables (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variables (FR : bvmap 5 word) (fc : bv 32) (m : amem) (RNG : footprint).
  Variables (SPV DT NC WK wks msv tl : Z) (nc : list Z) (jdt jw : list byte) (d : dtable) (lo : Z).
  Hypothesis BD : build_dtable nc msv tl wks = Ok d.
  Hypothesis MSV0 : 0 <= msv.
  Hypothesis WKS : 0 <= wks < 2^64.
  Hypothesis DTA : u8arr bsegs m DT jdt.
  Hypothesis LJD : zlen jdt = FSE_DTABLE_SIZE tl.
  Hypothesis WKA : u8arr bsegs m WK jw.
  Hypothesis LJW : zlen jw = FSE_BUILD_DTABLE_WKSP_SIZE tl msv.
  Hypothesis NCB : bytes_at bsegs m NC (u16s (map (Z_to_bv 64) nc)).
  Hypothesis NCR : Forall (fun c => - 32768 <= c < 32768) nc.
  Hypothesis BDT : ablk DT (DT + FSE_DTABLE_SIZE tl).
  Hypothesis BWK : ablk WK (WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv).
  Hypothesis BNC : ablk NC (NC + 2 * zlen nc).
  Hypothesis DT4 : DT mod 4 = 0.
  Hypothesis WK2 : WK mod 2 = 0.
  Hypothesis NC2 : NC mod 2 = 0.
  Hypothesis SDW : DT + FSE_DTABLE_SIZE tl <= WK \/ WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= DT.
  Hypothesis SDN : DT + FSE_DTABLE_SIZE tl <= NC \/ NC + 2 * zlen nc <= DT.
  Hypothesis SWN : WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= NC \/ NC + 2 * zlen nc <= WK.
  Hypothesis ZD : zshadow m DT (FSE_DTABLE_SIZE tl).
  Hypothesis ZW : zshadow m WK (FSE_BUILD_DTABLE_WKSP_SIZE tl msv).
  Hypothesis ZN : zshadow m NC (2 * zlen nc).
  Hypothesis RD : rng RNG DT (FSE_DTABLE_SIZE tl).
  Hypothesis RDS : rng RNG (shad DT) (nshad (FSE_DTABLE_SIZE tl + DT mod 8)).
  Hypothesis RW : rng RNG WK (FSE_BUILD_DTABLE_WKSP_SIZE tl msv).
  Hypothesis RWS : rng RNG (shad WK) (nshad (FSE_BUILD_DTABLE_WKSP_SIZE tl msv + WK mod 8)).
  Hypothesis RN : rng RNG NC (2 * zlen nc).
  Hypothesis RNS : rng RNG (shad NC) (nshad (2 * zlen nc + NC mod 8)).
  Hypothesis ST : stk bsegs m lo SPV.
  Hypothesis LO : lo <= SPV - AFSE_BUILD_STACK.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis SPT : SPV + 16 < 2^47.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Definition core_frc : list cell :=
    [C8 (Z_to_bv 64 (WK + 2 * (msv + 1))); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (WK + 2 * msv)); C8 (Z_to_bv 64 tl);
     C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 (- WK - 1)); C8 (Z_to_bv 64 NC); C8 (Z_to_bv 64 WK);
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition coreI (mm : amem) : Prop :=
    munch [(SPV - AFSE_BUILD_STACK, SPV); (DT, DT + FSE_DTABLE_SIZE tl); (WK, WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv)] m mm
    /\ wmono bsegs m mm /\ mem_inv bsegs mm /\ stk bsegs mm lo (SPV - 192)
    /\ rw_cells bsegs mm (SPV - 168) core_frc.

  Definition core_post := fse_build_postC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DT WK msv tl d lo m.

  Local Ltac zdec :=
  repeat match goal with
  | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
  | |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
  | |- context [?a =? ?b] => first [rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia]
  end; cbn [Z.b2z Z.lxor Z.lor Z.land Pos.lxor Pos.lor Pos.land].
  Local Ltac nrm := repeat first [
    match goal with |- context [bv_swrap 32 ?x] => rewrite (FseWalkKit.swrap32_small x) by lia end
  | match goal with |- context [Z.shiftr (Z.shiftl ?x 32 mod ?M) 31] => rewrite (shl32_shr31 x) by lia end
  | match goal with |- context [?x mod ?M] => rewrite (Z.mod_small x M) by (rewrite ?Z.shiftl_mul_pow2 by lia; lia) end
  | match goal with |- context [Z.shiftl 1 ?k] => rewrite (Z.shiftl_1_l k) end
  | match goal with |- context [Z.shiftl ?x ?k] => rewrite (Z.shiftl_mul_pow2 x k) by lia end
  | match goal with |- context [Z.shiftr ?x ?k] => rewrite (Z.shiftr_div_pow2 x k) by lia end ].
  Local Ltac cnd_solve := rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; nrm; zdec;
  first [reflexivity | apply Z.ltb_ge; lia | apply Z.ltb_lt; lia | apply Z.eqb_neq; lia | apply Z.eqb_eq; lia].
  Local Ltac cnd_false := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota | symmetry; cnd_solve] end.
  Local Ltac cnd_true := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota | symmetry; cnd_solve] end.
  Local Ltac wk_go2 pcs := repeat (wk_at pcs; first [wk_step | cnd_false | cnd_true]).

  Lemma rwc_sub : forall segs mm A cs k j, rw_cells segs mm A cs ->
    rw_cells segs mm (A + Z.of_nat (cells_size (firstn k cs))) (firstn j (skipn k cs)).
  Proof.
    intros segs mm A cs k j H. rewrite <- (firstn_skipn k cs) in H. apply ABytes.rw_cells_app in H as [_ H].
    rewrite <- (firstn_skipn j (skipn k cs)) in H. apply ABytes.rw_cells_app in H as [H _]. exact H.
  Qed.

  Local Ltac pick FRC k j NM := pose proof (rwc_sub _ _ _ _ k j FRC) as NM; cbn [firstn skipn cells_size csize] in NM.

  Lemma rwc_eq : forall segs mm A B cs cs', rw_cells segs mm A cs -> A = B -> cs = cs' -> rw_cells segs mm B cs'.
  Proof. intros; subst; assumption. Qed.

  Lemma rng_shad_sub : forall R A n A' n', rng R (shad A) (nshad (n + A mod 8)) -> 0 <= A -> A <= A' -> 0 <= n' ->
    A' + n' <= A + n -> rng R (shad A') (nshad (n' + A' mod 8)).
  Proof.
    intros R A n A' n' H HA HA' Hn' HE. apply (rng_sub _ _ _ _ _ H); unfold shad, nshad;
      rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
  Qed.

  Lemma hdr_le4 : forall t f M, 1 <= t <= 12 -> (f = 0 \/ f = 1) -> 2^17 <= M ->
    le4 (Z_to_bv 64 (Z.lor (Z.shiftl f 16 mod M) t)) = le2 (Z_to_bv 64 t) ++ le2 (Z_to_bv 64 f).
  Proof.
    intros t f M HT HF HM. rewrite (Z.mod_small (Z.shiftl f 16) M) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (E : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/ t = 9 \/ t = 10 \/ t = 11 \/ t = 12) by lia.
    destruct HF as [-> | ->]; repeat match goal with H : _ \/ _ |- _ => destruct H as [H | H] end; subst t;
      unfold le4, le2; cbn [Z_to_le_bytes app];
      repeat match goal with |- _ :: _ = _ :: _ =>
        apply (f_equal2 cons); [apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity |] end;
      reflexivity.
  Qed.

  Lemma upd_bytes_all : forall cs bs, length bs = length cs -> upd_bytes cs 0 bs = bs.
  Proof. intros cs bs H. unfold upd_bytes. cbn [firstn app Nat.add]. rewrite skipn_all2 by lia. apply app_nil_r. Qed.

  Definition core_W := [(DT, DT + FSE_DTABLE_SIZE tl); (WK, WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv)].

  Lemma core_tr : forall mm mm', coreI mm -> munch core_W mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' -> coreI mm'.
  Proof.
    intros mm mm' (MU & WM & MI1 & STK1 & FRC) MW WM2 MI2.
    pose proof (build_dtable_inv nc msv tl wks d BD MSV0) as (TLR & MSVR & WKSZ & _).
    pose proof (ablk_lin _ _ BDT) as (DTa & DTb & DTc & DTd).
    pose proof (ablk_lin _ _ BWK) as (WKa & WKb & WKc & WKd).
    pose proof atop_range as ATR.
    unfold core_W in MW. unfold AFSE_BUILD_STACK in LO.
    refine (conj _ (conj (wmono_trans _ _ _ _ WM WM2) (conj MI2 (conj _ _)))).
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MW]. intros x; cbn [outside]; tauto.
    - eapply stk_transport_disjoint; [exact STK1 | exact MW | exact WM2 |]. cbn [disjoint_from].
      split; [|split; [|exact I]]; right; lia.
    - eapply rw_cells_transport; [exact FRC | exact MW | exact WM2 |]. unfold core_frc; cbn [cells_size csize disjoint_from].
      split; [|split; [|exact I]]; right; lia.
  Qed.

  Lemma core_low : forall mm mm' lowc, rw_cells bsegs mm (SPV - 192) lowc -> cells_size lowc = 24%nat ->
    munch core_W mm mm' -> wmono bsegs mm mm' -> rw_cells bsegs mm' (SPV - 192) lowc.
  Proof.
    intros mm mm' lowc L LS MW WM2.
    pose proof (build_dtable_inv nc msv tl wks d BD MSV0) as (TLR & MSVR & WKSZ & _).
    pose proof (ablk_lin _ _ BDT) as (DTa & DTb & DTc & DTd).
    pose proof (ablk_lin _ _ BWK) as (WKa & WKb & WKc & WKd).
    pose proof atop_range as ATR.
    unfold AFSE_BUILD_STACK in LO.
    eapply rw_cells_transport; [exact L | exact MW | exact WM2 |]. rewrite LS. unfold core_W; cbn [disjoint_from].
    split; [|split; [|exact I]]; right; lia.
  Qed.

  Lemma core_ncl : msv + 1 <= zlen nc.
  Proof.
    pose proof (build_dtable_inv nc msv tl wks d BD MSV0) as (_ & MSVR & _ & (q1 & q2 & q3 & q4 & q5 & q6 & q7 & LPL & _)).
    pose proof (lowprob_lenA _ _ _ _ _ _ _ _ _ LPL ltac:(lia) ltac:(lia)) as NCL. lia.
  Qed.

  Lemma lxm1_bv : forall x K, K = 2^64 - 1 -> 0 <= x < 2^64 -> Z_to_bv 64 (Z.lxor x K) = Z_to_bv 64 (- x - 1).
  Proof.
    intros x K HK Hx.
    assert (L : Z.log2 x < 64).
    { destruct (Z.eq_dec x 0) as [E0 | Hn]; [rewrite E0; cbn; lia |]. apply Z.log2_lt_pow2; lia. }
    assert (E : Z.lxor x K = K - x).
    { rewrite HK. replace (2^64 - 1) with (Z.ones 64) by reflexivity.
      rewrite <- Z.ldiff_ones_l_low by lia. symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; lia. }
    rewrite E, HK. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    replace (2 ^ 64 - 1 - x) with ((- x - 1) + 1 * 2 ^ Z.of_N 64) by (cbn; lia).
    rewrite Z.mod_add by (cbn; lia). reflexivity.
  Qed.

  Lemma core_nc : forall mm, coreI mm -> bytes_at bsegs mm NC (u16s (map (Z_to_bv 64) nc)).
  Proof.
intros mm (MU & WM & MI1 & STK1 & FRC).
pose proof (ablk_lin _ _ BNC) as (NCa & NCb & NCc & NCd).
pose proof atop_range as ATR.
pose proof LO as LO1. unfold AFSE_BUILD_STACK in LO1.
eapply bytes_at_transport; [exact NCB | exact MU |].
assert (L : zlen (u16s (map (Z_to_bv 64) nc)) = 2 * zlen nc) by (rewrite u16s_length, length_map; lia).
rewrite L. cbn [disjoint_from].
split; [lia | split; [lia | split; [lia | exact I]]].
  Qed.

  Lemma core_zs : forall mm X n, coreI mm -> zshadow m X n -> 0 <= X -> X + n <= 2^47 -> zshadow mm X n.
  Proof.
intros mm X n (MU & WM & MI1 & STK1 & FRC) Z0 HX HXn.
eapply zshadow_munch; [exact Z0 | exact MU | | exact HX | exact HXn].
intros a Ha.
pose proof (shad_outside2 X n DT (FSE_DTABLE_SIZE tl) WK (FSE_BUILD_DTABLE_WKSP_SIZE tl msv) BDT BWK HX HXn a Ha) as O2.
cbn [outside] in O2 |- *.
split; [| exact O2].
pose proof atop_range as ATR.
pose proof LO as LO1. pose proof BOT as BOT1. unfold AFSE_BUILD_STACK in LO1.
assert (SA : 0 <= a / 8 < 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
unfold ASHOFF. lia.
  Qed.

  Lemma core_F : forall mm syms2 snext cells fm lowc
      (r1 r5 r6 r8 r9 r10 r11 r12 r13 r14 r15 r16 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
    build_loop tl (Z.to_nat (2^tl)) 0 syms2 snext [] = Ok cells -> d = mkDT tl fm cells ->
    length syms2 = Z.to_nat (2^tl) -> zlen snext = msv + 1 -> Forall (fun v => 0 <= v < 65536) snext ->
    coreI mm -> rw_cells bsegs mm (SPV - 192) lowc -> cells_size lowc = 24%nat ->
    u8arr bsegs mm DT (le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm)) ->
    u8arr bsegs mm (DT + 4) (tsym (skipn 4 jdt) syms2) ->
    u8arr bsegs mm WK (u16s (map (Z_to_bv 64) snext)) ->
    evtF bsegs RNG core_post
      (MS (mkR r1 (Z_to_bv 64 (SPV - 192)) gp tp r5 r6 (Z_to_bv 64 ASHOFF) r8 r9 r10 r11 r12 r13 r14 r15 r16
               (Z_to_bv 64 (DT + 4)) r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
          FR (Z_to_bv 64 (AFSE_BUILD_DT + 1600)) fc None mm (seg_rom bsegs)).
  Proof.
intros mm syms2 snext cells fm lowc r1 r5 r6 r8 r9 r10 r11 r12 r13 r14 r15 r16 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
  HBL ED HSL ZSN FSN CI LOWC LOWS UH UT UW.
pose proof (build_dtable_inv nc msv tl wks d BD MSV0) as (TLR & MSVR & WKSZ & _).
assert (P2 : 2 <= 2^tl <= 4096) by (split; [apply (Z.pow_le_mono_r 2 1 tl); lia | apply (Z.pow_le_mono_r 2 tl 12); lia]).
pose proof CI as (MU & WM & MI1 & STK1 & FRC).
unfold core_frc in FRC. replace (SPV - 168) with (SPV - 192 + 24) in FRC by lia.
pose proof (ablk_lin _ _ BDT) as (DTa & DTb & DTc & DTd).
pose proof (ablk_lin _ _ BWK) as (WKa & WKb & WKc & WKd).
pose proof atop_range as ATR.
unfold AFSE_BUILD_DT, AFSE_BUILD_STACK, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, AIMG_HI in *.
do 12 zstep.
replace (Z.shiftl (2^tl) 2) with (4 * 2^tl) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
pick FRC 1%nat 1%nat FDT0. pick FRC 3%nat 3%nat FTL0. pick FRC 7%nat 1%nat FWK0.
eapply bl_loopA with (POST:=core_post) (m:=mm) (TD:=DT+4) (WK:=WK) (tl:=tl) (M1:=msv+1) (jt:=skipn 4 jdt) (syms:=syms2)
  (SP:=SPV-192) (f:=Z.to_nat (2^tl)) (u:=0) (snext:=snext) (acc:=@nil dcell) (r:=cells) (m1:=mm).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end; first [exact ED | assumption | lia | reflexivity]).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end;
  first [ rewrite length_drop; unfold zlen in LJD; lia
        | apply (ablk_sub _ _ _ _ BDT); lia | apply (ablk_sub _ _ _ _ BWK); lia
        | apply (core_zs mm) ; [exact CI | apply (zshadow_sub m DT _ _ _ ZD); lia | lia | lia]
        | apply (core_zs mm) ; [exact CI | apply (zshadow_sub m WK _ _ _ ZW); lia | lia | lia]
        | apply (rng_sub _ _ _ _ _ RD); lia | apply (rng_sub _ _ _ _ _ RW); lia
        | apply (rng_sub _ _ _ _ _ RSTK); lia ]).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end;
  first [ rewrite length_drop; unfold zlen in LJD; lia
        | apply (rng_shad_sub _ DT ((1 + 2^tl) * 4)); [exact RDS | lia | lia | lia | lia]
        | apply (rng_shad_sub _ WK (2 * (msv + 1) + 2^tl + 8)); [exact RWS | lia | lia | lia | lia]
        | apply (rwc_eq _ _ _ _ _ _ FDT0); [lia | f_equal; f_equal; f_equal; lia]
        | apply (rwc_eq _ _ _ _ _ _ FTL0); [lia | reflexivity]
        | apply (rwc_eq _ _ _ _ _ _ FWK0); [lia | reflexivity] ]).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end;
  first [ rewrite length_drop; unfold zlen in LJD; apply Nat2Z.inj; rewrite Nat2Z.inj_sub, Nat2Z.inj_mul, Z2Nat.id by lia; lia
        | unfold blA_inv, tdb; cbn [map concat app skipn Z.to_nat Nat.mul];
          refine (conj UT (conj UW (conj (munch_refl _ _) (conj (wmono_refl _ _) MI1)))) ]).
2: { intros m2 sn2 y8 y9 y10 y11 y13 y14 ZC BI. destruct BI as (UT2 & UW2 & MU2 & WM2 & MI2).
  assert (DJ : disjoint_from (blA_W (DT + 4) WK tl (msv + 1)) (SPV - 192 + 24) (Z.of_nat (cells_size
    [C8 (Z_to_bv 64 (WK + 2 * (msv + 1))); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (WK + 2 * msv)); C8 (Z_to_bv 64 tl);
     C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 (- WK - 1)); C8 (Z_to_bv 64 NC); C8 (Z_to_bv 64 WK);
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))).
  { unfold blA_W. cbn [cells_size csize disjoint_from]. repeat split; lia. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRC MU2 WM2 DJ) as FRC2.
  do 18 zstep. apply evtF_done. unfold core_post, fse_build_postC.
  replace (SPV - 192 + 192) with SPV by lia.
  do 15 eexists. split; [reflexivity|].
  unfold AFSE_BUILD_STACK, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE.
  split. { eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU2]; unfold sub_fp, blA_W; intros x; cbn [outside]; lia. }
  split. { eapply wmono_trans; eassumption. }
  split. { exact MI2. }
  split. {
    assert (DJS : (lo + (SPV - 192 - lo) <= DT + 4 \/ DT + 4 + 4 * 2 ^ tl <= lo) /\ (lo + (SPV - 192 - lo) <= WK \/ WK + 2 * (msv + 1) <= lo) /\ True)
      by (split; [|split; [|exact I]]; right; lia).
   
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STK1 MU2 WM2 DJS) as S1.
    assert (DJL : disjoint_from (blA_W (DT + 4) WK tl (msv + 1)) (SPV - 192) (Z.of_nat (cells_size lowc)))
      by (rewrite LOWS; unfold blA_W; cbn [disjoint_from]; split; [|split; [|exact I]]; right; lia).
    pose proof (rw_cells_transport _ _ _ _ _ _ LOWC MU2 WM2 DJL) as L2.
    pose proof (stk_release _ _ _ _ _ S1 L2 ltac:(lia)) as S2. rewrite LOWS in S2.
    pose proof (stk_release _ _ _ _ _ S2 (rwc_eq _ _ _ (SPV - 192 + Z.of_nat 24) _ _ FRC2 ltac:(lia) eq_refl) ltac:(lia)) as S3.
    cbn [cells_size csize] in S3. match type of S3 with stk _ _ _ ?h => replace SPV with h by lia end. exact S3. }
  subst d. unfold fse_dt_bytes. cbn [dt_tableLog dt_fastMode dt_cells]. rewrite app_assoc. apply u8arr_app. split.
  - eapply u8arr_transport; [exact UH | exact MU2 | exact WM2 |]; unfold blA_W; cbn [disjoint_from];
      change (zlen (le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm))) with 4; repeat split; lia.
  - unfold tdb in UT2; rewrite (skipn_all2 (drop 4 jdt)) in UT2 by (rewrite length_drop; pose proof LJD as L3; unfold zlen in L3; lia);
      rewrite tsym_nilA, app_nil_r in UT2; change (zlen (le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm))) with 4; exact UT2. }
1: { first [rewrite length_skipn | rewrite skipn_length]. pose proof LJD as L2. unfold zlen in L2. lia. }
Qed.

  Notation ST640 mm hT fm r1 r5 r6 r8 r10 r13 r14 r15 r26 r27 r30 r31 :=
    (MS (mkR r1 (Z_to_bv 64 (SPV - 192)) gp tp r5 r6 (Z_to_bv 64 ASHOFF) r8 (Z_to_bv 64 (msv + 1)) r10 (Z_to_bv 64 (- NC - 1))
             (Z_to_bv 64 msv) r13 r14 r15 (Z_to_bv 64 (bv_swrap 32 hT)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (msv + 1)) (Z_to_bv 64 (msv + 1)) (Z_to_bv 64 1) (Z_to_bv 64 fm) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 (2^(tl-1))) (Z_to_bv 64 65535) r26 r27
             (Z_to_bv 64 (- (DT + 4) - 1)) (Z_to_bv 64 (2^tl - 1)) r30 r31)
        FR (Z_to_bv 64 (AFSE_BUILD_DT + 640)) fc None mm (seg_rom bsegs)).

  Lemma core_D : forall mm syms1 snext hT fm spread syms2 position cells j0 j8 j16
      (r1 r5 r6 r8 r10 r13 r14 r15 r26 r27 r30 r31 : word),
    hT = 2^tl - 1 ->
    spread_loop nc (Z.to_nat (msv + 1)) 0 (repeat None (Z.to_nat (2^tl + 8))) 0 = Ok spread ->
    place_loop tl (Z.to_nat (2^tl / 2)) 0 spread syms1 0 = Ok (syms2, position) ->
    build_loop tl (Z.to_nat (2^tl)) 0 syms2 snext [] = Ok cells -> d = mkDT tl fm cells ->
    length syms1 = Z.to_nat (2^tl) -> zlen snext = msv + 1 -> Forall (fun v => 0 <= v < 65536) snext ->
    (fm = 0 \/ fm = 1) ->
    coreI mm -> rw_cells bsegs mm (SPV - 192) [CB 8 j0; CB 8 j8; CB 8 j16] ->
    u8arr bsegs mm DT (firstn 4 jdt) -> u8arr bsegs mm (DT + 4) (tsym (skipn 4 jdt) syms1) ->
    u8arr bsegs mm WK (wkb jw snext) ->
    evtF bsegs RNG core_post (ST640 mm hT fm r1 r5 r6 r8 r10 r13 r14 r15 r26 r27 r30 r31).
  Proof.
intros mm syms1 snext hT fm spread syms2 position cells j0 j8 j16 r1 r5 r6 r8 r10 r13 r14 r15 r26 r27 r30 r31
  HT HSP HPL HBL ED HSL ZSN FSN FM CI LOWC UH UT UW.
pose proof (build_dtable_inv nc msv tl wks d BD MSV0) as (TLR & MSVR & WKSZ & _).
assert (P2 : 2 <= 2^tl <= 4096) by (split; [apply (Z.pow_le_mono_r 2 1 tl); lia | apply (Z.pow_le_mono_r 2 tl 12); lia]).
pose proof CI as (MU & WM & MI1 & STK1 & FRC).
unfold core_frc in FRC. replace (SPV - 168) with (SPV - 192 + 24) in FRC by lia.
pose proof (ablk_lin _ _ BDT) as (DTa & DTb & DTc & DTd).
pose proof (ablk_lin _ _ BWK) as (WKa & WKb & WKc & WKd).
pose proof atop_range as ATR.
assert (ZD1 : zshadow mm DT (FSE_DTABLE_SIZE tl)) by (apply (core_zs mm); [exact CI | exact ZD | lia | unfold FSE_DTABLE_SIZE; lia]).
unfold AFSE_BUILD_DT, AFSE_BUILD_STACK, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, AIMG_HI in *.
assert (DTL3 : Z.land DT 3 = 0) by (replace 3 with (Z.ones 2) by reflexivity; rewrite Z.land_ones by lia; change (2^2) with 4; lia).
pose proof (chkZ mm DT ((1 + 2^tl) * 4) DT ZD1 ltac:(lia) ltac:(lia)) as SH0.
unfold ASHOFF in *. rewrite Z.shiftr_div_pow2 in SH0 by lia.
wk_go2 [0x97b84].
assert (LH : length (firstn 4 jdt) = 4%nat) by (rewrite length_firstn; pose proof LJD as L4; unfold zlen in L4; lia).
assert (SOK2 : store_ok bsegs mm (Z_to_bv 64 DT) 4 = true)
  by (apply (u8arr_store_ok_n bsegs mm DT (firstn 4 jdt) 0 4); [exact UH | lia | unfold zlen; rewrite LH; lia | unfold wa; f_equal; lia]).
wk_go2 [0x97b84].
assert (HEQ : bv_eqb (Z_to_bv 64 (bv_swrap 32 hT)) (Z_to_bv 64 (2 ^ tl - 1)) = true).
{ rewrite HT, (FseWalkKit.swrap32_small (2 ^ tl - 1)) by lia. rewrite bv_eqb_Z. apply Z.eqb_eq. reflexivity. }
zstep. rewrite HEQ. cbn [negb].
rewrite hdr_le4 by first [exact FM | lia].
set (hb := le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm)).
assert (LHB : length hb = 4%nat) by reflexivity.
assert (ZHB : zlen hb = 4) by (unfold zlen; rewrite LHB; reflexivity).
set (mm1 := write_to_mem mm (Z_to_bv 64 DT) hb).
assert (MW1 : munch core_W mm mm1).
{ unfold mm1, core_W, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE. apply munch_write.
  - apply munch_refl.
  - lia.
  - rewrite ZHB; lia.
  - cbn [inside]. rewrite ZHB. lia. }
assert (WM1 : wmono bsegs mm mm1) by (apply wmono_write, wmono_refl).
assert (MI2 : mem_inv bsegs mm1) by (apply mem_inv_store; [exact MI1 | rewrite LHB; exact SOK2]).
assert (CI1 : coreI mm1) by (exact (core_tr mm mm1 CI MW1 WM1 MI2)).
assert (LOW1 : rw_cells bsegs mm1 (SPV - 192) [CB 8 j0; CB 8 j8; CB 8 j16]) by (exact (core_low mm mm1 _ LOWC eq_refl MW1 WM1)).
assert (UH1 : u8arr bsegs mm1 DT hb).
{ pose proof (u8arr_write_bytes bsegs mm DT (firstn 4 jdt) 0 hb UH ltac:(lia) ltac:(rewrite LH, LHB; lia)) as U.
  rewrite Z.add_0_r, upd_bytes_all in U by (rewrite LH, LHB; reflexivity). exact U. }
assert (UT1 : u8arr bsegs mm1 (DT + 4) (tsym (skipn 4 jdt) syms1))
  by (apply u8arr_frame; [exact UT | lia | rewrite ZHB; lia | right; rewrite ZHB; lia]).
assert (UW1 : u8arr bsegs mm1 WK (wkb jw snext)).
{ apply u8arr_frame; [exact UW | lia | rewrite ZHB; lia |]. rewrite ZHB.
  assert (E1 : zlen (wkb jw snext) = Z.of_nat (length (wkb jw snext))) by reflexivity.
  assert (E2 : zlen jw = Z.of_nat (length jw)) by reflexivity.
  assert (E3 : zlen snext = Z.of_nat (length snext)) by reflexivity.
  rewrite wkb_length by lia. lia. }
pose proof CI1 as (MUa & WMa & MIa & STKa & FRCa).
unfold core_frc in FRCa. replace (SPV - 168) with (SPV - 192 + 24) in FRCa by lia.
pick FRCa 6%nat 1%nat FNC1.
pose proof (ablk_lin _ _ BNC) as (NCa & NCb & NCc & NCd).
clear MW1.
unfold AFSE_BUILD_STACK, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE in MUa.
pose proof (munch_refl [(SPV - 192, SPV - 168)] mm1) as MWs. pose proof (wmono_refl bsegs mm1) as WMs.
pose proof (conj UH1 (conj UT1 UW1)) as KEEP. clear UH1 UT1 UW1.
wk_go2 [0x97bd0].
let v := reg_val 13%Z in assert (STP : v = Z_to_bv 64 (table_step (2^tl))) by (f_equal; unfold table_step, bv_wrap, bv_modulus; nrm; lia).
rewrite STP in LOW1 |- *.
replace (Z_to_bv 64 msv) with (Z_to_bv 64 (msv + 1 - 1)) by (f_equal; lia).
assert (CI3 : coreI m1).
{ unfold coreI. refine (conj _ (conj WMa (conj MIa (conj STKa _)))).
  - unfold AFSE_BUILD_STACK, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE. exact MUa.
  - apply (rwc_eq _ _ _ _ _ _ FRCa); [lia | reflexivity]. }
destruct KEEP as (UH1 & UT1 & UW1).
assert (UH3 : u8arr bsegs m1 DT hb)
  by (eapply u8arr_transport; [exact UH1 | exact MWs | exact WMs |]; cbn [disjoint_from]; rewrite ZHB; split; [lia | exact I]).
assert (UT3 : u8arr bsegs m1 (DT + 4) (tsym (skipn 4 jdt) syms1))
  by (eapply u8arr_transport; [exact UT1 | exact MWs | exact WMs |]; cbn [disjoint_from]; split; [|exact I];
      rewrite tsym_length, length_skipn; lia).
assert (UW3 : u8arr bsegs m1 WK (wkb jw snext))
  by (eapply u8arr_transport; [exact UW1 | exact MWs | exact WMs |]; cbn [disjoint_from]; split; [|exact I];
      rewrite wkb_length by lia; lia).
clear UH1 UT1 UW1.
pose proof UW3 as UW3'. unfold wkb in UW3'. apply u8arr_app in UW3' as [UWa UWb].
rewrite u16s_length, length_map in UWb.
replace (WK + Z.of_nat (2 * length snext)) with (WK + 2 * (msv + 1)) in UWb by lia.
set (js := skipn (2 * length snext) jw) in UWb.
assert (ZJS : zlen js = 2^tl + 8) by (unfold js; rewrite length_skipn; lia).
pick LOW1 1%nat 1%nat FR8a. pick LOW1 2%nat 1%nat FR16a.
pick FRCa 0%nat 1%nat FR24a. pick FRCa 2%nat 1%nat FR40a. pick FRCa 4%nat 1%nat FR56a.
eapply sp_outerA with (POST:=core_post) (m:=m1) (NC:=NC) (SPR:=WK + 2 * (msv + 1)) (nc:=nc) (M1:=msv+1) (js:=js) (SP:=SPV-192)
  (f:=Z.to_nat (msv+1)) (s:=0) (spr:=repeat None (Z.to_nat (2^tl + 8))) (pos:=0) (r:=spread) (m1:=m1).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end; first [exact HSP | assumption | lia | reflexivity | exact core_ncl]).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end;
  first [ apply (ablk_sub _ _ _ _ BWK); lia
        | apply (core_nc m1 CI3)
        | apply (core_zs m1); [exact CI3 | exact ZN | lia | lia]
        | apply (core_zs m1); [exact CI3 | apply (zshadow_sub m WK _ _ _ ZW); lia | lia | lia]
        | apply (rng_sub _ _ _ _ _ RW); lia | apply (rng_sub _ _ _ _ _ RSTK); lia
        | apply (rng_shad_sub _ WK (2 * (msv + 1) + 2^tl + 8)); [exact RWS | lia | lia | lia | lia]
        | apply (rwc_eq _ _ _ _ _ _ FR8a); [lia | f_equal; f_equal; f_equal; lia]
        | apply (rwc_eq _ _ _ _ _ _ FR24a); [lia | reflexivity]
        | apply (rwc_eq _ _ _ _ _ _ FR40a); [lia | f_equal; f_equal; f_equal; lia]
        | apply (rwc_eq _ _ _ _ _ _ FNC1); [lia | reflexivity]
        | rewrite repeat_length; unfold js; rewrite length_skipn; lia
        | unfold spA_inv; rewrite omerge_none; refine (conj UWb (conj (munch_refl _ _) (conj (wmono_refl _ _) MIa))) ]).
all: match goal with |- forall _, _ => idtac | |- ?g => idtac "OPEN:" g; fail end.
intros m2 y1 y5 y6 y8 y9 y10 y13 y14 y15 y16 y18 y19 y20 y21 y23 y24 y25 y26 y27 y30 y31 INV2 LEN2.
destruct INV2 as (SPB2 & MU2 & WM2 & MI4).
assert (MW2 : munch core_W m1 m2).
{ eapply munch_weaken; [|exact MU2]. intros x Hx. unfold core_W, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE in Hx.
  cbn [outside] in *. rewrite ZJS. split; [lia | exact I]. }
assert (CI4 : coreI m2) by (exact (core_tr m1 m2 CI3 MW2 WM2 MI4)).
pose proof (core_low m1 m2 _ LOW1 eq_refl MW2 WM2) as LOW2.
assert (UH4 : u8arr bsegs m2 DT hb)
  by (eapply u8arr_transport; [exact UH3 | exact MU2 | exact WM2 |]; cbn [disjoint_from]; rewrite ZHB, ZJS; split; [lia | exact I]).
assert (UT4 : u8arr bsegs m2 (DT + 4) (tsym (skipn 4 jdt) syms1))
  by (eapply u8arr_transport; [exact UT3 | exact MU2 | exact WM2 |]; cbn [disjoint_from]; rewrite ZJS; split; [|exact I];
      rewrite tsym_length, length_skipn; lia).
assert (UW4 : u8arr bsegs m2 WK (u16s (map (Z_to_bv 64) snext)))
  by (eapply u8arr_transport; [exact UWa | exact MU2 | exact WM2 |]; cbn [disjoint_from]; rewrite ZJS; split; [|exact I];
      rewrite u16s_length, length_map; lia).
clear MW2 MU2 FR8a FR16a FR24a FR40a FR56a FNC1 LOW1 FRCa UH3 UT3 UW3 UWa.
pose proof CI4 as (MU4 & WM4 & MI5 & STK4 & FRC4).
unfold core_frc in FRC4. replace (SPV - 168) with (SPV - 192 + 24) in FRC4 by lia.
unfold AFSE_BUILD_STACK, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE in MU4.
wk_go2 [0x97e18].
lazymatch goal with |- context [Z_to_bv 64 (Z.lxor (WK + 2 * (msv + 1)) ?c)] =>
  replace (Z_to_bv 64 (Z.lxor (WK + 2 * (msv + 1)) c)) with (Z_to_bv 64 (- (WK + 2 * (msv + 1)) - 1))
    by (rewrite zb_lxor_ones by lia; apply Z_to_bv_eqm; rewrite <- (Z.mod_add (- (WK + 2 * (msv + 1)) - 1) 1 (2^64)) by lia;
        f_equal; lia) end.
assert (TSB : 0 < table_step (2^tl) < 8192) by (unfold table_step; rewrite !Z.shiftr_div_pow2 by lia; split; Z.div_mod_to_equations; lia).
let v := reg_val 16%Z in replace v with (Z_to_bv 64 (2 * table_step (2^tl)))
  by (f_equal; rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
assert (PT1 : 2^tl = 2 * 2^(tl-1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
assert (H2D : 2 * Z.of_nat (Z.to_nat (2^tl / 2)) = 2^tl - 0)
  by (rewrite Z2Nat.id by (apply Z.div_pos; lia); rewrite PT1; Z.div_mod_to_equations; lia).
pick LOW2 2%nat 1%nat FR16b. pick FRC4 2%nat 1%nat FR40b. pick FRC4 4%nat 1%nat FR56b.
eapply pl_loopA with (POST:=core_post) (m:=m2) (TD:=DT+4) (SPR:=WK + 2*(msv+1)) (tl:=tl) (stp:=table_step (2^tl))
  (jt:=skipn 4 jdt) (js:=js) (spread:=spread) (SP:=SPV-192) (f:=Z.to_nat (2^tl/2)) (s:=0) (syms:=syms1) (position:=0)
  (r:=(syms2, position)) (m1:=m2).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end; first [exact HPL | exact H2D | exact SPB2 | assumption | lia | reflexivity]).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end;
  first [ rewrite length_skipn; pose proof LJD as L4; lia
        | symmetry; exact LEN2
        | rewrite LEN2; lia
        | apply (ablk_sub _ _ _ _ BDT); lia | apply (ablk_sub _ _ _ _ BWK); lia
        | apply (core_zs m2); [exact CI4 | apply (zshadow_sub m DT _ _ _ ZD); lia | lia | lia]
        | apply (core_zs m2); [exact CI4 | apply (zshadow_sub m WK _ _ _ ZW); lia | lia | lia]
        | apply (rng_sub _ _ _ _ _ RD); lia | apply (rng_sub _ _ _ _ _ RW); lia | apply (rng_sub _ _ _ _ _ RSTK); lia
        | apply (rng_shad_sub _ DT ((1 + 2^tl) * 4)); [exact RDS | lia | lia | lia | lia]
        | apply (rng_shad_sub _ WK (2 * (msv + 1) + 2^tl + 8)); [exact RWS | lia | lia | lia | lia]
        | apply (rwc_eq _ _ _ _ _ _ FR16b); [lia | reflexivity]
        | apply (rwc_eq _ _ _ _ _ _ FR40b); [lia | f_equal; f_equal; f_equal; lia]
        | apply (rwc_eq _ _ _ _ _ _ FR56b); [lia | reflexivity]
        | unfold plA_inv; refine (conj UT4 (conj (munch_refl _ _) (conj (wmono_refl _ _) MI4))) ]).
all: match goal with |- forall _, _ => idtac | |- ?g => idtac "OPEN:" g; fail end.
intros m3 syms' pos' z5 z10 z11 z12 z13 z14 z31 HR LEN3 INV3.
injection HR as E1' E2''. subst syms'.
destruct INV3 as (UT5 & MU5 & WM5 & MI6).
assert (MW5 : munch core_W m2 m3).
{ eapply munch_weaken; [|exact MU5]. intros x Hx. unfold core_W, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE in Hx.
  cbn [outside] in *. split; [lia | exact I]. }
assert (CI5 : coreI m3) by (exact (core_tr m2 m3 CI4 MW5 WM5 MI6)).
pose proof (core_low m2 m3 _ LOW2 eq_refl MW5 WM5) as LOW3.
assert (UH5 : u8arr bsegs m3 DT hb)
  by (eapply u8arr_transport; [exact UH4 | exact MU5 | exact WM5 |]; cbn [disjoint_from]; rewrite ZHB; split; [lia | exact I]).
assert (UW5 : u8arr bsegs m3 WK (u16s (map (Z_to_bv 64) snext)))
  by (eapply u8arr_transport; [exact UW4 | exact MU5 | exact WM5 |]; cbn [disjoint_from]; split; [|exact I];
      rewrite u16s_length, length_map; lia).
eapply core_F with (mm:=m3) (syms2:=syms2) (snext:=snext) (cells:=cells) (fm:=fm).
all: first [exact HBL | exact ED | exact LEN3 | exact ZSN | exact FSN | exact CI5 | exact LOW3 | reflexivity | exact UH5
           | exact UT5 | exact UW5 | idtac "OPEN2"].
Qed.

  Lemma core_E : forall mm syms1 snext hT fm syms2 position cells j0 j8 j16
      (r1 r5 r6 r8 r10 r13 r14 r15 r26 r27 r30 r31 : word),
    hT <> 2^tl - 1 -> 0 <= hT < 2^32 -> (hT < 2^tl \/ hT = 2^32 - 1) ->
    gen_loop nc tl (Z.to_nat (msv + 1)) 0 syms1 0 hT = Ok (syms2, position) -> position = 0 ->
    build_loop tl (Z.to_nat (2^tl)) 0 syms2 snext [] = Ok cells -> d = mkDT tl fm cells ->
    length syms1 = Z.to_nat (2^tl) -> zlen snext = msv + 1 -> Forall (fun v => 0 <= v < 65536) snext ->
    (fm = 0 \/ fm = 1) ->
    coreI mm -> rw_cells bsegs mm (SPV - 192) [CB 8 j0; CB 8 j8; CB 8 j16] ->
    u8arr bsegs mm DT (firstn 4 jdt) -> u8arr bsegs mm (DT + 4) (tsym (skipn 4 jdt) syms1) ->
    u8arr bsegs mm WK (wkb jw snext) ->
    evtF bsegs RNG core_post (ST640 mm hT fm r1 r5 r6 r8 r10 r13 r14 r15 r26 r27 r30 r31).
  Proof.
intros mm syms1 snext hT fm syms2 position cells j0 j8 j16 r1 r5 r6 r8 r10 r13 r14 r15 r26 r27 r30 r31
  HT HT0 HT1 HG HP0 HBL ED HSL ZSN FSN FM CI LOWC UH UT UW.
pose proof (build_dtable_inv nc msv tl wks d BD MSV0) as (TLR & MSVR & WKSZ & _).
assert (P2 : 2 <= 2^tl <= 4096) by (split; [apply (Z.pow_le_mono_r 2 1 tl); lia | apply (Z.pow_le_mono_r 2 tl 12); lia]).
pose proof CI as (MU & WM & MI1 & STK1 & FRC).
unfold core_frc in FRC. replace (SPV - 168) with (SPV - 192 + 24) in FRC by lia.
pose proof (ablk_lin _ _ BDT) as (DTa & DTb & DTc & DTd).
pose proof (ablk_lin _ _ BWK) as (WKa & WKb & WKc & WKd).
pose proof atop_range as ATR.
assert (ZD1 : zshadow mm DT (FSE_DTABLE_SIZE tl)) by (apply (core_zs mm); [exact CI | exact ZD | lia | unfold FSE_DTABLE_SIZE; lia]).
unfold AFSE_BUILD_DT, AFSE_BUILD_STACK, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, AIMG_HI in *.
assert (DTL3 : Z.land DT 3 = 0) by (replace 3 with (Z.ones 2) by reflexivity; rewrite Z.land_ones by lia; change (2^2) with 4; lia).
pose proof (chkZ mm DT ((1 + 2^tl) * 4) DT ZD1 ltac:(lia) ltac:(lia)) as SH0.
unfold ASHOFF in *. rewrite Z.shiftr_div_pow2 in SH0 by lia.
wk_go2 [0x97b84].
assert (LH : length (firstn 4 jdt) = 4%nat) by (rewrite length_firstn; pose proof LJD as L4; unfold zlen in L4; lia).
assert (SOK2 : store_ok bsegs mm (Z_to_bv 64 DT) 4 = true)
  by (apply (u8arr_store_ok_n bsegs mm DT (firstn 4 jdt) 0 4); [exact UH | lia | unfold zlen; rewrite LH; lia | unfold wa; f_equal; lia]).
wk_go2 [0x97b84].
assert (HNE : bv_eqb (Z_to_bv 64 (bv_swrap 32 hT)) (Z_to_bv 64 (2 ^ tl - 1)) = false).
{ rewrite bv_eqb_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.eqb_neq.
  destruct HT1 as [H1 | H1].
  - rewrite (FseWalkKit.swrap32_small hT) by lia. rewrite !Z.mod_small by lia. lia.
  - subst hT. replace (bv_swrap 32 (2 ^ 32 - 1)) with (-1) by reflexivity.
    replace ((-1) mod 2 ^ Z.of_N 64) with (2 ^ 64 - 1) by reflexivity. rewrite Z.mod_small by lia. lia. }
zstep. rewrite HNE. cbn [negb].
rewrite hdr_le4 by first [exact FM | lia].
set (hb := le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm)).
assert (LHB : length hb = 4%nat) by reflexivity.
assert (ZHB : zlen hb = 4) by (unfold zlen; rewrite LHB; reflexivity).
set (mm1 := write_to_mem mm (Z_to_bv 64 DT) hb).
assert (MW1 : munch core_W mm mm1).
{ unfold mm1, core_W, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE. apply munch_write.
  - apply munch_refl.
  - lia.
  - rewrite ZHB; lia.
  - cbn [inside]. rewrite ZHB. lia. }
assert (WM1 : wmono bsegs mm mm1) by (apply wmono_write, wmono_refl).
assert (MI2 : mem_inv bsegs mm1) by (apply mem_inv_store; [exact MI1 | rewrite LHB; exact SOK2]).
assert (CI1 : coreI mm1) by (exact (core_tr mm mm1 CI MW1 WM1 MI2)).
assert (LOW1 : rw_cells bsegs mm1 (SPV - 192) [CB 8 j0; CB 8 j8; CB 8 j16]) by (exact (core_low mm mm1 _ LOWC eq_refl MW1 WM1)).
assert (UH1 : u8arr bsegs mm1 DT hb).
{ pose proof (u8arr_write_bytes bsegs mm DT (firstn 4 jdt) 0 hb UH ltac:(lia) ltac:(rewrite LH, LHB; lia)) as U.
  rewrite Z.add_0_r, upd_bytes_all in U by (rewrite LH, LHB; reflexivity). exact U. }
assert (UT1 : u8arr bsegs mm1 (DT + 4) (tsym (skipn 4 jdt) syms1))
  by (apply u8arr_frame; [exact UT | lia | rewrite ZHB; lia | right; rewrite ZHB; lia]).
assert (UW1 : u8arr bsegs mm1 WK (wkb jw snext)).
{ apply u8arr_frame; [exact UW | lia | rewrite ZHB; lia |]. rewrite ZHB.
  assert (E1 : zlen (wkb jw snext) = Z.of_nat (length (wkb jw snext))) by reflexivity.
  assert (E2 : zlen jw = Z.of_nat (length jw)) by reflexivity.
  assert (E3 : zlen snext = Z.of_nat (length snext)) by reflexivity.
  rewrite wkb_length by lia. lia. }
let v := reg_val 5%Z in replace v with (Z_to_bv 64 (2^tl/8)) by (f_equal; unfold bv_wrap, bv_modulus; nrm; reflexivity).
let v := reg_val 13%Z in replace v with (Z_to_bv 64 (2^tl/2)) by (f_equal; unfold bv_wrap, bv_modulus; nrm; reflexivity).
pose proof CI1 as (MUa & WMa & MIa & STKa & FRCa).
unfold core_frc in FRCa. replace (SPV - 168) with (SPV - 192 + 24) in FRCa by lia.
pick FRCa 6%nat 1%nat FNC1.
pose proof (ablk_lin _ _ BNC) as (NCa & NCb & NCc & NCd).
eapply gn_entryA with (POST:=core_post) (m:=mm1) (NC:=NC) (TD:=DT+4) (nc:=nc) (tl:=tl) (stp:=table_step (2^tl)) (M1:=msv+1)
  (hT:=hT) (jt:=skipn 4 jdt) (SP:=SPV-192) (syms:=syms1) (r:=(syms2, position)) (m1:=mm1).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end; first [exact HG | assumption | lia | reflexivity]).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end;
  first [ rewrite length_skipn; pose proof LJD as L4; unfold zlen in L4; lia
        | apply (ablk_sub _ _ _ _ BDT); lia
        | apply (core_nc mm1 CI1) | exact core_ncl
        | apply (core_zs mm1) ; [exact CI1 | exact ZN | lia | lia]
        | apply (core_zs mm1) ; [exact CI1 | apply (zshadow_sub m DT _ _ _ ZD); lia | lia | lia]
        | apply (rng_sub _ _ _ _ _ RD); lia | apply (rng_sub _ _ _ _ _ RSTK); lia
        | apply (rng_shad_sub _ DT ((1 + 2^tl) * 4)); [exact RDS | lia | lia | lia | lia]
        | apply (rwc_eq _ _ _ _ _ _ FNC1); [lia | reflexivity]
        | unfold gnA_inv; refine (conj UT1 (conj (munch_refl _ _) (conj (wmono_refl _ _) MI2)))
        | unfold table_step; rewrite !Z.shiftr_div_pow2 by lia; split; Z.div_mod_to_equations; lia ]).
all: match goal with |- forall _, _ => idtac | |- ?g => idtac "OPEN:" g; fail end.
intros m2 syms' p' y5 y10 y12 y13 y14 HR HP HL2 INV2.
injection HR as E1' E2''. subst syms' p'. rewrite HP0.
destruct INV2 as (UT2 & MU2 & WM2 & MI3).
assert (MW2 : munch core_W mm1 m2).
{ eapply munch_weaken; [|exact MU2]. intros x Hx. unfold core_W, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE in Hx.
  cbn [outside] in *. split; [lia | exact I]. }
assert (CI2 : coreI m2) by (exact (core_tr mm1 m2 CI1 MW2 WM2 MI3)).
pose proof (core_low mm1 m2 _ LOW1 eq_refl MW2 WM2) as LOW2.
assert (UH2 : u8arr bsegs m2 DT hb)
  by (eapply u8arr_transport; [exact UH1 | exact MU2 | exact WM2 |]; cbn [disjoint_from]; rewrite ZHB; split; [lia | exact I]).
assert (UW2 : u8arr bsegs m2 WK (u16s (map (Z_to_bv 64) snext))).
{ assert (U : u8arr bsegs m2 WK (wkb jw snext)).
  { eapply u8arr_transport; [exact UW1 | exact MU2 | exact WM2 |]. cbn [disjoint_from]. split; [|exact I].
    rewrite wkb_length by lia. lia. }
  unfold wkb in U. apply u8arr_app in U as [U _]. exact U. }
eapply gn_doneA with (POST:=core_post) (NC:=NC) (TD:=DT+4) (tl:=tl) (hT:=hT) (SP:=SPV-192) (mm:=m2).
eapply core_F with (mm:=m2) (syms2:=syms2) (snext:=snext) (cells:=cells) (fm:=fm) (lowc:=[CB 8 j0; CB 8 j8; CB 8 j16]).
all: first [exact HBL | exact ED | exact HL2 | exact ZSN | exact FSN | exact CI2 | exact LOW2 | reflexivity | exact UH2
           | exact UT2 | exact UW2 | idtac "OPEN2"].
Qed.


  Theorem fse_build_coreA :
    evtF bsegs RNG (fse_build_postC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DT WK msv tl d lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
                (Z_to_bv 64 WK) (Z_to_bv 64 wks) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFSE_BUILD_DT) fc None m (seg_rom bsegs)).
Proof.
pose proof core_zs as CZS. pose proof core_D as CD. pose proof core_E as CE.
pose proof (build_dtable_inv nc msv tl wks d BD MSV0) as (TLR & MSVR & WKSZ & syms1 & snext & hT & fm & syms2 & position & cells & LP & BR & BL & ED).
pose proof (ablk_lin _ _ BDT) as (DTa & DTb & DTc & DTd).
pose proof (ablk_lin _ _ BWK) as (WKa & WKb & WKc & WKd).
pose proof (ablk_lin _ _ BNC) as (NCa & NCb & NCc & NCd).
pose proof atop_range as ATR.
assert (P2 : 2 <= 2^tl <= 4096) by (split; [apply (Z.pow_le_mono_r 2 1 tl); lia | apply (Z.pow_le_mono_r 2 tl 12); lia]).
pose proof (munch_refl [(SPV - AFSE_BUILD_STACK, SPV); (DT, DT + FSE_DTABLE_SIZE tl); (WK, WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
unfold AFSE_BUILD_DT, AFSE_BUILD_STACK, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, AIMG_HI in *.
zstep.
carve_frame 192%nat ST.
lazymatch goal with H : rw_cells bsegs _ _ [CB 192 _] |- _ =>
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in H; [| reflexivity]; cbn [mk_CB_cells app] in H; rename H into FRM end.
repeat match type of FRM with context [CB 8 (firstn 8 ?j)] => let x := fresh "jk" in set (x := firstn 8 j) in FRM; clearbody x end.
clear junk.
do 16 zstep.
wk_go2 [0x97a50].
assert (PT1 : 2^tl = 2 * 2^(tl-1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
assert (PT2 : 2^(tl + -1) = 2^(tl-1)) by (f_equal; lia).
rewrite (lxm1_bv WK) in FRM by first [reflexivity | lia].
match type of FRM with context [Z_to_bv 64 (WK + Z.shiftl (msv mod ?K) 1 + 2)] =>
  replace (Z_to_bv 64 (WK + Z.shiftl (msv mod K) 1 + 2)) with (Z_to_bv 64 (WK + 2 * (msv + 1))) in FRM
    by (f_equal; rewrite Z.mod_small, Z.shiftl_mul_pow2 by lia; rewrite Z.pow_1_r; lia) end.
match type of FRM with context [Z_to_bv 64 (WK + Z.shiftl (msv mod ?K) 1)] =>
  replace (Z_to_bv 64 (WK + Z.shiftl (msv mod K) 1)) with (Z_to_bv 64 (WK + 2 * msv)) in FRM
    by (f_equal; rewrite Z.mod_small, Z.shiftl_mul_pow2 by lia; rewrite Z.pow_1_r; lia) end.
replace (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (tl mod 32)))) with (Z_to_bv 64 (2^tl)) in FRM
  by (f_equal; rewrite (Z.mod_small tl 32), Z.shiftl_1_l by lia; rewrite FseWalkKit.swrap32_small by lia; reflexivity).
pick FRM 0%nat 3%nat LOW0.
pick FRM 8%nat 1%nat FRW0.
pick FRM 9%nat 1%nat FRN0.
pick FRM 10%nat 1%nat FWK0.
pick FRM 3%nat 21%nat FRC0.
assert (LOW1 : rw_cells bsegs m0 (SPV - 192) [CB 8 jk; CB 8 jk0; CB 8 jk1]) by (apply (rwc_eq _ _ _ _ _ _ LOW0); [lia | reflexivity]).
assert (FRC1 : rw_cells bsegs m0 (SPV - 168) core_frc) by (apply (rwc_eq _ _ _ _ _ _ FRC0); [lia | reflexivity]).
assert (CI0 : coreI m0) by (unfold coreI; exact (conj MU (conj WM (conj MI (conj ST FRC1))))).
assert (LH4 : length (firstn 4 jdt) = 4%nat) by (rewrite length_firstn; lia).
pose proof DTA as DTS. rewrite <- (firstn_skipn 4 jdt) in DTS. apply u8arr_app in DTS as [UH0 UT0].
replace (DT + zlen (firstn 4 jdt)) with (DT + 4) in UT0 by lia.
rewrite (lxm1_bv NC) by first [reflexivity | lia].
rewrite (lxm1_bv (DT + 4)) by first [reflexivity | lia].
let v := reg_val 7%Z in replace v with (Z_to_bv 64 ASHOFF) by reflexivity.
let v := reg_val 9%Z in replace v with (Z_to_bv 64 (msv + 1)) by (f_equal; nrm; lia).
let v := reg_val 19%Z in replace v with (Z_to_bv 64 (msv + 1)) by (f_equal; nrm; lia).
let v := reg_val 16%Z in replace v with (Z_to_bv 64 (bv_swrap 32 (2^tl - 1))) by (f_equal; nrm; lia).
let v := reg_val 22%Z in replace v with (Z_to_bv 64 0) by (f_equal; rewrite land_1; lia).
let v := reg_val 23%Z in replace v with (Z_to_bv 64 0) by (f_equal; rewrite land_1; lia).
let v := reg_val 24%Z in replace v with (Z_to_bv 64 (2^(tl-1))) by (f_equal; nrm; lia).
eapply lp_loopA with (POST:=core_post) (m:=m0) (NC:=NC) (WK:=WK) (TD:=DT+4) (nc:=nc) (tl:=tl) (M1:=msv+1)
  (jt:=skipn 4 jdt) (jw:=jw) (SP:=SPV-192) (f:=Z.to_nat (msv+1)) (s:=0) (syms:=repeat None (Z.to_nat (2^tl)))
  (snext:=[]) (hT:=2^tl-1) (fm:=1) (r:=(syms1, snext, hT, fm)) (m1:=m0).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end;
  first [exact LP | exact core_ncl | exact NCR | exact BNC | exact NC2 | exact WK2 | exact RN | exact RNS | lia | reflexivity]).
all: try (match goal with |- forall _, _ => fail 1 | _ => idtac end;
  first [ rewrite length_skipn; lia
        | apply (ablk_sub _ _ _ _ BDT); lia
        | rewrite LJW; exact BWK
        | rewrite LJW; exact RW
        | rewrite LJW; exact RWS
        | apply (CZS m0); [exact CI0 | exact ZN | lia | lia]
        | apply (CZS m0); [exact CI0 | apply (zshadow_sub m DT _ _ _ ZD); lia | lia | lia]
        | apply (CZS m0); [exact CI0 | rewrite LJW; exact ZW | lia | lia]
        | apply (rng_sub _ _ _ _ _ RD); lia
        | apply (rng_sub _ _ _ _ _ RSTK); lia
        | apply (rng_shad_sub _ DT ((1 + 2^tl) * 4)); [exact RDS | lia | lia | lia | lia]
        | apply (rwc_eq _ _ _ _ _ _ FRW0); [lia | reflexivity]
        | apply (rwc_eq _ _ _ _ _ _ FRN0); [lia | reflexivity]
        | apply (rwc_eq _ _ _ _ _ _ FWK0); [lia | reflexivity]
        | unfold lpA_ok; rewrite repeat_length;
          split; [reflexivity | split; [constructor | split; [lia | split; [left; lia | right; reflexivity]]]]
        | unfold lpA_inv; rewrite tsym_none;
          split; [exact UT0 | split; [exact WKA | split; [cbn; lia | split; [exact NCB
            | split; [apply munch_refl | split; [apply wmono_refl | exact MI]]]]]] ]).
all: match goal with |- forall _, _ => idtac | |- ?g => idtac "OPEN:" g; fail end.
intros m2 syms' snext' hT' fm' y5 y10 y13 y15 y30 HR HZ OK2 INV2.
injection HR as HE1 HE2 HE3 HE4. subst syms' snext' hT' fm'.
destruct INV2 as (UT2 & UW2 & LW2 & NCB2 & MU2 & WM2 & MI2).
destruct OK2 as (SL2 & SR2 & HT0 & HT1 & FM2).
assert (MW2 : munch core_W m0 m2).
{ eapply munch_weaken; [|exact MU2]. intros x Hx. unfold core_W, FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE in Hx. unfold lpA_W.
  cbn [outside] in *. destruct Hx as (Hx1 & Hx2 & _). split; [lia | split; [lia | exact I]]. }
assert (CI2 : coreI m2) by (exact (core_tr m0 m2 CI0 MW2 WM2 MI2)).
pose proof (core_low m0 m2 _ LOW1 eq_refl MW2 WM2) as LOW2.
assert (UH2 : u8arr bsegs m2 DT (firstn 4 jdt))
  by (eapply u8arr_transport; [exact UH0 | exact MU2 | exact WM2 |]; unfold lpA_W; cbn [disjoint_from];
      split; [lia | split; [lia | exact I]]).
rewrite (FseWalkKit.swrap32_small (2^tl - 1)) by lia.
destruct BR as [(HTE & spread & SPL & PLL) | (HTN & GL & HP0)].
- eapply CD with (mm:=m2) (syms1:=syms1) (snext:=snext) (hT:=hT) (fm:=fm) (spread:=spread) (syms2:=syms2)
    (position:=position) (cells:=cells) (j0:=jk) (j8:=jk0) (j16:=jk1).
  all: first [exact HTE | exact SPL | exact PLL | exact BL | exact ED | exact SL2 | exact HZ | exact SR2 | exact FM2
             | exact CI2 | exact LOW2 | exact UH2 | exact UT2 | exact UW2 | idtac "OPEN2"].
- eapply CE with (mm:=m2) (syms1:=syms1) (snext:=snext) (hT:=hT) (fm:=fm) (syms2:=syms2)
    (position:=position) (cells:=cells) (j0:=jk) (j8:=jk0) (j16:=jk1).
  all: first [exact HTN | exact HT0 | exact HT1 | exact GL | exact HP0 | exact BL | exact ED | exact SL2 | exact HZ
             | exact SR2 | exact FM2 | exact CI2 | exact LOW2 | exact UH2 | exact UT2 | exact UW2 | idtac "OPEN2"].
Qed.
End Core.
End CANSEC1.
