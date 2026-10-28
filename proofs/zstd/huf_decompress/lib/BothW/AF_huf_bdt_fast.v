(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface RF_huf_bdt_model RF_huf_bdt_fast.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_huf_tbl_iface AF_huf_bdt_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkArith StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_bdt_fast () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes6option00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01C47Corelib4Init9Datatypes6lengthI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<spread_innerC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6write8C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model9write8_OkC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model2wrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit=shad_outside1C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit=zshadow_munchC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4chkZC56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit7acc_shZK47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model6omergeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model<omerge_storeC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8oupd_natC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT?oupd_nat_lengthK4ELinuxProcessSemantics5Riscv3Sem4core01C56Stdlib6ZArith6BinInt1Z7add_0_rI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model6wr4_eqC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model8wr8_machC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model9wr_lengthC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_geC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos6to_natC47Corelib4Init5Logic7f_equalK4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model=omerge_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5msize01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4sxb0C56Stdlib6ZArith6BinInt1Z3subc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_fast7spA_invC56Stdlib6ZArith6BinInt1Z3mulC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC47Corelib4Init3Nat3mulC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7to_byteC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u16_znthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_bdt_fast6sv_le1C5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_bdt_fast8sv_le1_0C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3u64C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;spread_loopC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:signed_litc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_fast9sp_innerAC5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_bdt_fast8sv_rangeC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem:sx16_shortK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_bdt_fast3SVKC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_fast7plA_invC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model4tsymC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;tsym_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?wr_at_transportC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:table_stepC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5oloadC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model8oload_OkC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model9ostore_OkC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_bdt_fast?land_mask_rangeC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model:omerge_nthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:u8arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC47Corelib4Init3Nat3addC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model:tsym_storec5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_bdt_fast8le1_zxbAC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_land_lC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:place_loopC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6ostoreC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK4ELinuxProcessSemantics5Riscv5Instr5aluop0:".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac spbA SPR ARR q :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok bsegs _ SPR _ q (wa (SPR + q)) ARR ltac:(rewrite omerge_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (SPR + q) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (SPR + q) by lia
  end;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?x)) _) =>
    first [ match goal with H : le1 x = [_] |- _ => rewrite H end | rewrite le1_lit ]
  end;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write bsegs _ SPR _ q bb ARR ltac:(rewrite omerge_length; lia)) as ARR2;
    clear ARR; store_done;
    rewrite omerge_store in ARR2 by (rewrite ?oupd_nat_length; lia);
    rename ARR2 into ARR
  end.

(* [comment removed for export] *)
Lemma le1_zxbA : forall b, le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b))) = [Z_to_bv 8 b].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_fast ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51bh61lp;1p;2p;3p;4p;7p;6p;8p10000p4p7210g000\R0p4p710p8g001:j10Tg001_j1=Tg002=j1DTg002`j1;Tg003@j23Tg003fj2PTg004Pj19Tg0050j3<j27j1@Tg005Pj32Tg005jj24Tg006Dj2>Tg006jj16Tg007Hj2QTg007ej21Tg008Ej1OTg008cj1NTg009Aj1LTg009lj2:Tg00:Oj4JTg00;:j7ITg00;^j6CTg00<Bj2ETg00<dj2FTg00=Pj3BTg00=oj4GTg00>aj3HTP0j65Tg00?Bj2ATg00@1j3KTg00@jj88Tg00AGj1?Tg00B7j1MTg00C5R0g00CS#0R1#0#0R2#=R3#DR4#;R5f0R6,33R7,P3R8,33R9%94R:5<4f1R;,33=<4:9256X65P5P517491747P:P:P4P5\5R<%@4R=P=P9P7P<\4/4=P01>36R=%61%62'QR1,16R411;1520X00P0%02#0#0R2#0#0#6R<,16R711;<9206X001407117<g00D8R7#9%;7%O0%N0%L0R7g00DdR9g00ECR>P>g00EcR?P7P9P>P>P?P01:0<g00FCg00FjR>,:0CJg00GHFIEC1E7?P6f2R?g00GhR7g00HHR9'41F6?=279dAB0>;CGb2b3b4A20<>g00Hh[P6b19H6<E511=1=204eP81A36E59K86G8145:G8%=2/38#?%M8E5W5o"). Qed.

Ltac tdsA TD ARR u :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok bsegs _ TD _ (4 * u + 2) (wa (TD + (4 * u + 2))) ARR ltac:(rewrite tsym_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (TD + (4 * u + 2)) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (TD + (4 * u + 2)) by lia
  end;
  rewrite ?le1_zxbA, ?le1_lit;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write bsegs _ TD _ (4 * u + 2) bb ARR ltac:(rewrite tsym_length; lia)) as ARR2;
    clear ARR; store_done;
    replace (Z.to_nat (4 * u + 2)) with (4 * Z.to_nat u + 2)%nat in ARR2 by lia;
    rewrite tsym_store in ARR2 by (rewrite ?oupd_nat_length; lia);
    rename ARR2 into ARR
  end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inner.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).
  Variables (x1 x9 x11 x12 x16 x17 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 : word).
  Variables (m : amem) (SPR : Z) (js : list byte) (pos n b : Z).
  Variable POST : machine_state -> Prop.
  (* [comment removed for export] *)
  Hypothesis B1 : le1 x1 = [Z_to_bv 8 b].
  Hypothesis B16 : le1 x16 = [Z_to_bv 8 b].
  Hypothesis B19 : le1 x19 = [Z_to_bv 8 b].
  Hypothesis B20 : le1 x20 = [Z_to_bv 8 b].
  Hypothesis B21 : le1 x21 = [Z_to_bv 8 b].
  Hypothesis B25 : le1 x25 = [Z_to_bv 8 b].
  Hypothesis B26 : le1 x26 = [Z_to_bv 8 b].
  Hypothesis B27 : le1 x27 = [Z_to_bv 8 b].
  Hypothesis BSP : ablk SPR (SPR + zlen js).
  Hypothesis HPOS : 0 <= pos.
  Hypothesis ZS : zshadow m SPR (zlen js).
  Hypothesis RS : rng RNG SPR (zlen js).
  Hypothesis RSS : rng RNG (shad SPR) (nshad (zlen js + SPR mod 8)).

  Notation STI pc mm x5 x6 x10 x13 x14 x15 x31 :=
    (MS (mkR x1 sp gp tp x5 x6 (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (- (SPR + pos) - 1)) x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (SPR + pos + 8)) x19 x20 x21 x22 x23 (Z_to_bv 64 n) x25 x26 x27 x28 x29 (Z_to_bv 64 (SPR + pos - 2)) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma i_sw : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
  Proof.
    intros z Hz. assert (HM : bv_half_modulus 32 = 2^31) by reflexivity. assert (MM : bv_modulus 32 = 2^32) by reflexivity.
    unfold bv_swrap, bv_wrap. rewrite HM, MM. rewrite Z.mod_small by lia. lia.
  Qed.
  Local Ltac oupd_eq := repeat match goal with
    | |- oupd_nat ?x ?v ?l = oupd_nat ?y ?v ?l' =>
        replace y with x by (first [reflexivity | f_equal; lia]); apply (f_equal (oupd_nat x v))
    end; reflexivity.
  Lemma sp_innerA : forall f spr i r m1 (x6 x10 x14 x15 x31 : word),
    spread_inner f spr pos i n b = Ok r ->
    8 <= i < n -> n < 2^15 -> length js = length spr ->
    u8arr bsegs m1 SPR (omerge js spr) ->
    munch [(SPR, SPR + zlen js)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    (forall m2 (y5 y6 y10 y13 y14 y15 y31 : word), u8arr bsegs m2 SPR (omerge js r) -> length r = length spr ->
       munch [(SPR, SPR + zlen js)] m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
       evtF bsegs RNG POST (STI 0x97bb8 m2 y5 y6 y10 y13 y14 y15 y31)) ->
    evtF bsegs RNG POST (STI 0x97c98 m1 (Z_to_bv 64 (i - 8)) x6 x10 (Z_to_bv 64 i) x14 x15 x31).
Proof.
intros f. induction f as [|f IH]; intros spr i r m1 q6 q10 q14 q15 q31 HSI HI HN HL ARR MU WM MI K; [discriminate HSI|].
pose proof (ablk_lin _ _ BSP) as (Sa & Sb & Sc & Sd). unfold AIMG_HI in Sa.
pose proof (zshadow_munch _ m m1 SPR (zlen js) ZS MU (shad_outside1 SPR (zlen js) SPR (zlen js) BSP ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZS1.
cbn [spread_inner] in HSI. rewrite (proj2 (Z.ltb_lt i n)) in HSI by lia.
destruct (write8 8 spr (pos + i) b) as [sp1| | |] eqn:W8; cbn [bind] in HSI; try discriminate HSI.
destruct (write8_Ok 7 spr (pos + i) b sp1 W8) as (WP0 & WP1 & WP2).
unfold ASHOFF.
(wk_go [0x97cd4]).
spbA SPR ARR (pos + i + 4).
spbA SPR ARR (pos + i + 5).
spbA SPR ARR (pos + i + 6).
spbA SPR ARR (pos + i + 7).
spbA SPR ARR (pos + i).
spbA SPR ARR (pos + i + 1).
spbA SPR ARR (pos + i + 2).
spbA SPR ARR (pos + i + 3).
match goal with H : u8arr bsegs ?mm SPR (omerge js ?l) |- _ =>
  assert (E8 : l = sp1) by (rewrite WP2, wr8_mach, !wr4_eq by lia; oupd_eq); rewrite E8 in H end.
assert (HL1 : length js = length sp1) by (rewrite WP2, wr_length; exact HL).
zstep. rewrite (i_sw (i + 8)) by lia.
destruct (Z_lt_le_dec (i + 8) n) as [LT|GE].
- zstep. unfold bv_lts. rewrite !signed_lit by lia. rewrite (proj2 (Z.ltb_lt (i + 8) n)) by lia. cbv iota.
  replace (Z_to_bv 64 (i - 8 + 8)) with (Z_to_bv 64 (i + 8 - 8)) by (f_equal; lia).
  exact (IH sp1 (i + 8) r _ _ _ _ _ _ HSI ltac:(lia) HN HL1 ARR MU WM MI
           ltac:(intros m3 y5 y6 y10 y13 y14 y15 y31 A3 L3 M3 W3 I3; apply K; [exact A3 | rewrite L3, <- HL1; exact HL | exact M3 | exact W3 | exact I3])).
- zstep. unfold bv_lts. rewrite !signed_lit by lia. rewrite (proj2 (Z.ltb_ge (i + 8) n)) by lia. cbv iota. zstep.
  destruct f as [|f]; [discriminate HSI|]. cbn [spread_inner] in HSI. rewrite (proj2 (Z.ltb_ge (i + 8) n)) in HSI by lia.
  injection HSI as <-.
  exact (K _ _ _ _ _ _ _ _ ARR ltac:(rewrite <- HL1; exact HL) MU WM MI).
Qed.
End Inner.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Outer.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).
  Variables (x17 x28 x29 : word).
  Variables (m : amem) (NC SPR : Z) (nc : list Z) (M1 : Z) (js : list byte).
  Variable POST : machine_state -> Prop.
  Hypothesis HM1 : 1 <= M1 <= 256.
  Hypothesis HNCL : M1 <= zlen nc.
  Hypothesis HNCR : Forall (fun c => - 32768 <= c < 32768) nc.
  Hypothesis BNC : ablk NC (NC + 2 * zlen nc).
  Hypothesis BSP : ablk SPR (SPR + zlen js).
  Hypothesis DNS : NC + 2 * zlen nc <= SPR \/ SPR + zlen js <= NC.
  Hypothesis NCB0 : bytes_at bsegs m NC (u16s (map (Z_to_bv 64) nc)).     (* [comment removed for export] *)
  Hypothesis ZN : zshadow m NC (2 * zlen nc).
  Hypothesis ZS : zshadow m SPR (zlen js).
  Hypothesis RN : rng RNG NC (2 * zlen nc).
  Hypothesis RNS : rng RNG (shad NC) (nshad (2 * zlen nc + NC mod 8)).
  Hypothesis RS : rng RNG SPR (zlen js).
  Hypothesis RSS : rng RNG (shad SPR) (nshad (zlen js + SPR mod 8)).

  Definition spA_inv (m1 : amem) (spr : list (option Z)) : Prop :=
    u8arr bsegs m1 SPR (omerge js spr) /\ munch [(SPR, SPR + zlen js)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  Variable SP : Z.
  Hypothesis FR8 : rw_cells bsegs m (SP + 8) [C8 (Z_to_bv 64 (SPR + 8))].
  Hypothesis FR24 : rw_cells bsegs m (SP + 24) [C8 (Z_to_bv 64 SPR)].
  Hypothesis FR40 : rw_cells bsegs m (SP + 40) [C8 (Z_to_bv 64 (SPR - 2))].
  Hypothesis FRN : rw_cells bsegs m (SP + 72) [C8 (Z_to_bv 64 NC)].
  Hypothesis RSP : rng RNG (SP + 8) 72.
  Hypothesis DSP : SPR + zlen js <= SP + 8 \/ SP + 80 <= SPR.

  Notation STO pc mm x1 x5 x6 x8 x9 x10 x13 x14 x15 x16 x18 x19 x20 x21 x23 x24 x25 x26 x27 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 (Z_to_bv 64 ASHOFF) x8 x9 x10 (Z_to_bv 64 (- NC - 1)) (Z_to_bv 64 (M1 - 1))
             x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 16843009) x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma o_sh : forall s, 0 <= s < 2^31 -> Z.shiftr (Z.shiftl s 32 mod 2^64) 31 = 2 * s.
  Proof.
    intros s Hs. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (s * 2^32) with (2 * s * 2^31) by (change (2^32) with (2 * 2^31); ring). apply Z.div_mul. lia.
  Qed.
  Lemma o_ltneg : forall A x, 0 <= A -> 0 <= x -> A + x < 2^64 -> bv_ltu (Z_to_bv 64 (- A - 1)) (Z_to_bv 64 x) = false.
  Proof.
    intros A x HA Hx HAx. rewrite bv_ltu_Z, !unsigned_lit_wrap. rewrite (Z.mod_small x) by lia.
    rewrite <- (Z.mod_add (- A - 1) 1 (2^64)) by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
  Qed.
  Lemma o_sw : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
  Proof.
    intros z Hz. assert (HM : bv_half_modulus 32 = 2^31) by reflexivity. assert (MM : bv_modulus 32 = 2^32) by reflexivity.
    unfold bv_swrap, bv_wrap. rewrite HM, MM. rewrite Z.mod_small by lia. lia.
  Qed.
  Local Ltac oupd_eq := repeat match goal with
    | |- oupd_nat ?x ?v ?l = oupd_nat ?y ?v ?l' =>
        replace y with x by (first [reflexivity | f_equal; lia]); apply (f_equal (oupd_nat x v))
    end; reflexivity.
  Lemma sp_outerA : forall f s spr pos r m1 (x1 x5 x6 x8 x13 x14 x15 x16 x18 x20 x21 x23 x24 x25 x26 x27 x30 x31 : word),
    spread_loop nc f s spr pos = Ok r ->
    Z.of_nat f = M1 - s -> 0 <= s < M1 -> 0 <= pos < 2^64 -> length spr = length js ->
    spA_inv m1 spr ->
    (forall m2 (y1 y5 y6 y8 y9 y10 y13 y14 y15 y16 y18 y19 y20 y21 y23 y24 y25 y26 y27 y30 y31 : word),
       spA_inv m2 r -> length r = length js ->
       evtF bsegs RNG POST (STO 0x97e00 m2 y1 y5 y6 y8 y9 y10 y13 y14 y15 y16 y18 y19 y20 y21 y23 y24 y25 y26 y27 y30 y31)) ->
    evtF bsegs RNG POST (STO 0x97bd0 m1 x1 x5 x6 x8 (Z_to_bv 64 pos) (Z_to_bv 64 s) x13 x14 x15 x16 x18 (Z_to_bv 64 (s * SVK))
                             x20 x21 x23 x24 x25 x26 x27 x30 x31).
Proof.
Local Ltac acc_hint ::= wk_acc_hint.
intros f. induction f as [|f IH]; intros s spr pos r m1 q1 q5 q6 q8 q13 q14 q15 q16 q18 q20 q21 q23 q24 q25 q26 q27 q30 q31 HS HF HSR HP HL INV K; [lia|].
pose proof INV as INV0. destruct INV as (U & MU & WM & MI).
pose proof (ablk_lin _ _ BSP) as (Sa & Sb & Sc & Sd). pose proof (ablk_lin _ _ BNC) as (Na & Nb & Nc & Nd).
unfold AIMG_HI in Sa, Na.
pose proof (zshadow_munch _ m m1 SPR (zlen js) ZS MU (shad_outside1 SPR (zlen js) SPR (zlen js) BSP ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZS1.
pose proof (zshadow_munch _ m m1 NC (2 * zlen nc) ZN MU (shad_outside1 NC (2 * zlen nc) SPR (zlen js) BSP ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZN1.
assert (NCB1 : bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) nc)))
  by (apply (bytes_at_transport bsegs _ m m1 NC _ NCB0 MU); cbn [disjoint_from]; rewrite u16s_length, length_map; lia).
assert (FR8_1 : rw_cells bsegs m1 (SP + 8) [C8 (Z_to_bv 64 (SPR + 8))])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 8) _ FR8 MU WM); cbn [disjoint_from]; cbn; lia).
assert (FR24_1 : rw_cells bsegs m1 (SP + 24) [C8 (Z_to_bv 64 SPR)])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 24) _ FR24 MU WM); cbn [disjoint_from]; cbn; lia).
assert (FR40_1 : rw_cells bsegs m1 (SP + 40) [C8 (Z_to_bv 64 (SPR - 2))])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 40) _ FR40 MU WM); cbn [disjoint_from]; cbn; lia).
assert (FRN1 : rw_cells bsegs m1 (SP + 72) [C8 (Z_to_bv 64 NC)])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 72) _ FRN MU WM); cbn [disjoint_from]; cbn; lia).
cbn [spread_loop] in HS.
assert (LD : load nc s = Ok (Znth s nc))
  by (unfold load; replace ((0 <=? s) && (s <? FseNCount.Zlength nc)) with true; [reflexivity|];
      symmetry; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; unfold FseNCount.Zlength; lia]).
rewrite LD in HS. cbn [bind] in HS.
destruct (write8 8 spr pos (to_byte s)) as [sp1| | |] eqn:W8; cbn [bind] in HS; try discriminate HS.
destruct (write8_Ok 7 spr pos (to_byte s) sp1 W8) as (WP0 & WP1 & WP2).
destruct (spread_inner (S (Z.to_nat (Znth s nc))) sp1 pos 8 (Znth s nc) (to_byte s)) as [sp2| | |] eqn:SI; cbn [bind] in HS; try discriminate HS.
pose proof (Forall_Znth _ nc s HNCR ltac:(lia)) as NR. cbv beta in NR.
unfold ASHOFF.
assert (TL : forall m3 (z1 z5 z6 z8 z10 z13 z14 z15 z16 z18 z20 z21 z25 z26 z27 z30 z31 : word),
  spA_inv m3 sp2 -> length sp2 = length js ->
  evtF bsegs RNG POST (STO 0x97bb8 m3 z1 z5 z6 z8 (Z_to_bv 64 pos) z10 z13 z14 z15 z16 z18 (Z_to_bv 64 (s * SVK))
                         z20 z21 (Z_to_bv 64 s) (Z_to_bv 64 (Znth s nc)) z25 z26 z27 z30 z31)).
{ intros m3 z1 z5 z6 z8 z10 z13 z14 z15 z16 z18 z20 z21 z25 z26 z27 z30 z31 INV3 HL3.
  unfold ASHOFF. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite bv_eqb_Z, !unsigned_lit_wrap, !(Z.mod_small s), !(Z.mod_small (M1 - 1)) by lia.
  destruct (Z.eqb_spec s (M1 - 1)) as [E|E]; cbv iota.
  - destruct f as [|f]; [|lia]. cbn [spread_loop] in HS. injection HS as <-.
    eapply K; [exact INV3 | exact HL3].
  - rewrite (o_sw (s + 1)) by lia.
    lazymatch goal with |- context [Z_to_bv 64 (s * SVK + ?c)] =>
      replace (s * SVK + c) with ((s + 1) * SVK) by (unfold SVK; ring) end.
    replace (Z_to_bv 64 (pos + Znth s nc)) with (Z_to_bv 64 (u64 (pos + Znth s nc)))
      by (apply Z_to_bv_eqm; unfold u64; rewrite Zmod_mod; reflexivity).
    eapply (IH (s + 1) sp2 (u64 (pos + Znth s nc)) r m3); [exact HS | lia | lia | unfold u64; apply Z.mod_pos_bound; lia
      | exact HL3 | exact INV3 | exact K]. }
zstep. zstep. zstep.
lazymatch goal with |- context [Z_to_bv 64 ((Z.shiftl s 32 mod ?M) ≫ 31)] =>
  replace ((Z.shiftl s 32 mod M) ≫ 31) with (2 * s) by (symmetry; change M with (2^64); apply o_sh; lia) end.
(wk_go [0x97c18]).
rewrite (Z.mod_small s) by lia.
assert (NL : 0 <= s < Z.of_nat (length nc)) by lia.
pose proof (u16_znth bsegs m1 NC nc s (Z_to_bv 64 (NC + Z.shiftl s 1)) NCB1 NL
  ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RDN.
zstep. clear RDN.
rewrite sx16_short by lia.
(wk_go [0x97c50]).
assert (S256 : 0 <= s < 256) by lia.
pose proof (sv_range s S256) as SVR.
rewrite (Z.mod_small (s * SVK)) by lia.
pose proof (sv_le1_0 s S256) as V0.
pose proof (sv_le1 s 8 S256 ltac:(cbn; tauto)) as V8.
pose proof (sv_le1 s 16 S256 ltac:(cbn; tauto)) as V16.
pose proof (sv_le1 s 24 S256 ltac:(cbn; tauto)) as V24.
pose proof (sv_le1 s 32 S256 ltac:(cbn; tauto)) as V32.
pose proof (sv_le1 s 40 S256 ltac:(cbn; tauto)) as V40.
pose proof (sv_le1 s 48 S256 ltac:(cbn; tauto)) as V48.
pose proof (sv_le1 s 56 S256 ltac:(cbn; tauto)) as V56.
rename U into ARR.
spbA SPR ARR (pos + 4).
spbA SPR ARR (pos + 5).
spbA SPR ARR (pos + 6).
spbA SPR ARR (pos + 7).
spbA SPR ARR pos.
spbA SPR ARR (pos + 1).
spbA SPR ARR (pos + 2).
spbA SPR ARR (pos + 3).

match goal with H : u8arr bsegs ?mm SPR (omerge js ?l) |- _ =>
  assert (E8 : l = sp1) by (rewrite WP2, wr8_mach, !wr4_eq by lia; oupd_eq); rewrite E8 in H end.
assert (HL1 : length sp1 = length js) by (rewrite WP2, wr_length; exact HL).
zstep. zstep. unfold bv_lts. rewrite !signed_lit by lia.
destruct (Z.ltb_spec (Znth s nc) 9) as [N9|N9]; cbv iota.
- cbn [spread_inner] in SI. rewrite (proj2 (Z.ltb_ge 8 (Znth s nc))) in SI by lia. injection SI as <-.
  eapply TL; [split; [assumption | split; [assumption | split; assumption]] | exact HL1].
- (wk_go [0x97c98]).
  lazymatch goal with |- context [Z_to_bv 64 (Z.lxor (SPR + pos) ?c)] =>
    replace (Z_to_bv 64 (Z.lxor (SPR + pos) c)) with (Z_to_bv 64 (- (SPR + pos) - 1))
      by (rewrite zb_lxor_ones by lia; apply Z_to_bv_eqm; rewrite <- (Z.mod_add (- (SPR + pos) - 1) 1 (2^64)) by lia;
          f_equal; lia) end.
  replace (Z_to_bv 64 (SPR + 8 + pos)) with (Z_to_bv 64 (SPR + pos + 8)) by (f_equal; lia).
  replace (Z_to_bv 64 (SPR - 2 + pos)) with (Z_to_bv 64 (SPR + pos - 2)) by (f_equal; lia).
  eapply sp_innerA with (b := to_byte s) (i := 8) (n := Znth s nc) (pos := pos) (SPR := SPR) (js := js) (m := m)
            (f := S (Z.to_nat (Znth s nc))) (spr := sp1) (r := sp2).
  all: try assumption. all: try lia. all: try (symmetry; exact HL1).
  intros m3 y5 y6 y10 y13 y14 y15 y31 A3 L3 M3 W3 I3.
  eapply TL; [split; [exact A3 | split; [exact M3 | split; [exact W3 | exact I3]]] | rewrite L3; exact HL1].
Qed.
End Outer.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Place.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).
  Variables (x1 x6 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 : word).
  Variables (m : amem) (TD SPR : Z) (tl stp : Z) (jt js : list byte) (spread : list (option Z)).
  Variable POST : machine_state -> Prop.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HSTP : 0 < stp < 8192.
  Hypothesis HSTPV : stp = table_step (2^tl).
  Hypothesis HJT : length jt = (4 * Z.to_nat (2^tl))%nat.
  Hypothesis HJS : length js = length spread.
  Hypothesis HSPL : 2^tl <= zlen spread.
  Hypothesis BTD : ablk TD (TD + 4 * 2^tl).
  Hypothesis BSP : ablk SPR (SPR + zlen js).
  Hypothesis DTS : TD + 4 * 2^tl <= SPR \/ SPR + zlen js <= TD.
  Hypothesis SPB0 : u8arr bsegs m SPR (omerge js spread).     (* [comment removed for export] *)
  Hypothesis ZT : zshadow m TD (4 * 2^tl).
  Hypothesis ZS : zshadow m SPR (zlen js).
  Hypothesis RT : rng RNG TD (4 * 2^tl).
  Hypothesis RTS : rng RNG (shad TD) (nshad (4 * 2^tl + TD mod 8)).
  Hypothesis RS : rng RNG SPR (zlen js).
  Hypothesis RSS : rng RNG (shad SPR) (nshad (zlen js + SPR mod 8)).

  Definition plA_inv (m1 : amem) (syms : list (option Z)) : Prop :=
    u8arr bsegs m1 TD (tsym jt syms) /\ munch [(TD, TD + 4 * 2^tl)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  Variable SP : Z.
  Hypothesis FR16 : rw_cells bsegs m (SP + 16) [C8 (Z_to_bv 64 stp)].
  Hypothesis FR40 : rw_cells bsegs m (SP + 40) [C8 (Z_to_bv 64 (SPR - 2))].
  Hypothesis FR56 : rw_cells bsegs m (SP + 56) [C8 (Z_to_bv 64 (2^tl))].
  Hypothesis RSP : rng RNG (SP + 16) 48.
  Hypothesis DSP : TD + 4 * 2^tl <= SP + 16 \/ SP + 64 <= TD.

  Notation STP pc mm x5 x10 x11 x12 x13 x14 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 (Z_to_bv 64 ASHOFF) x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (- SPR - 1))
             (Z_to_bv 64 (2 * stp)) (Z_to_bv 64 TD) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             (Z_to_bv 64 (- TD - 1)) (Z_to_bv 64 (2^tl - 1)) x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma p_pt : 2 <= 2^tl <= 4096.
  Proof. assert (2^1 <= 2^tl <= 2^12) by (split; apply Z.pow_le_mono_r; lia). change (2^1) with 2 in H. change (2^12) with 4096 in H. exact H. Qed.
  Lemma p_st : forall m1 syms p v, plA_inv m1 syms -> 0 <= p < 2^tl -> length syms = Z.to_nat (2^tl) ->
    store_ok bsegs m1 (wa (TD + (4 * p + 2))) 1 = true /\
    plA_inv (write_to_mem m1 (wa (TD + (4 * p + 2))) [Z_to_bv 8 v]) (oupd_nat (Z.to_nat p) v syms).
  Proof.
    intros m1 syms p v (U & MU & WM & MI) HP HL. pose proof p_pt as PT.
    pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td).
    assert (LT : Z.of_nat (length (tsym jt syms)) = 4 * 2^tl) by (rewrite tsym_length, HJT; lia).
    assert (SOK : store_ok bsegs m1 (wa (TD + (4 * p + 2))) 1 = true)
      by (apply (u8arr_store_ok bsegs m1 TD (tsym jt syms) (4 * p + 2)); [exact U | lia | reflexivity]).
    split; [exact SOK|].
    unfold plA_inv. split; [| split; [| split]].
    - rewrite <- tsym_store by (rewrite ?HJT, ?HL; lia).
      replace (4 * Z.to_nat p + 2)%nat with (Z.to_nat (4 * p + 2)) by lia.
      apply u8arr_write; [exact U | lia].
    - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | exact SOK].
  Qed.
  Lemma p_mask : forall x, 0 <= Z.land x (2^tl - 1) < 2^tl.
  Proof.
    intros x. replace (2^tl - 1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound. pose proof p_pt. lia.
  Qed.

  Local Ltac acc_hint ::= wk_acc_hint.
  Lemma pl_loopA : forall f s syms position r m1 (x5 x10 x11 x13 x14 : word),
    place_loop tl f s spread syms position = Ok r ->
    2 * Z.of_nat f = 2^tl - s -> 0 <= s < 2^tl -> 0 <= position < 2^tl -> length syms = Z.to_nat (2^tl) ->
    plA_inv m1 syms ->
    (forall m2 syms' pos' (y5 y10 y11 y12 y13 y14 y31 : word), r = (syms', pos') -> length syms' = Z.to_nat (2^tl) ->
       plA_inv m2 syms' ->
       evtF bsegs RNG POST (STP 0x97f08 m2 y5 y10 y11 y12 y13 y14 y31)) ->
    evtF bsegs RNG POST (STP 0x97e18 m1 x5 x10 x11 (Z_to_bv 64 s) x13 x14 (Z_to_bv 64 position)).
Proof.
intros f. induction f as [|f IH]; intros s syms position r m1 q5 q10 q11 q13 q14 HP HF HS HPOS HL INV K; [lia|].
pose proof p_pt as PT. pose proof INV as INV0. destruct INV as (U & MU & WM & MI).
pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td). pose proof (ablk_lin _ _ BSP) as (Sa & Sb & Sc & Sd).
unfold AIMG_HI in Ta, Sa.
pose proof (zshadow_munch _ m m1 TD (4 * 2^tl) ZT MU (shad_outside1 TD (4 * 2^tl) TD (4 * 2^tl) BTD ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZT1.
pose proof (zshadow_munch _ m m1 SPR (zlen js) ZS MU (shad_outside1 SPR (zlen js) TD (4 * 2^tl) BTD ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZS1.
assert (SPB1 : u8arr bsegs m1 SPR (omerge js spread))
  by (apply (u8arr_transport bsegs _ m m1 SPR _ SPB0 MU WM); cbn [disjoint_from]; rewrite omerge_length; lia).
assert (FR16_1 : rw_cells bsegs m1 (SP + 16) [C8 (Z_to_bv 64 stp)])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 16) _ FR16 MU WM); cbn [disjoint_from]; cbn; lia).
assert (FR40_1 : rw_cells bsegs m1 (SP + 40) [C8 (Z_to_bv 64 (SPR - 2))])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 40) _ FR40 MU WM); cbn [disjoint_from]; cbn; lia).
assert (FR56_1 : rw_cells bsegs m1 (SP + 56) [C8 (Z_to_bv 64 (2^tl))])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 56) _ FR56 MU WM); cbn [disjoint_from]; cbn; lia).
cbn [place_loop] in HP. rewrite <- HSTPV in HP.
destruct (oload spread s) as [b0| | |] eqn:OL0; cbn [bind] in HP; try discriminate HP.
pose proof (p_mask position) as M0.
assert (OS1 : ostore syms (Z.land position (2^tl - 1)) b0 = Ok (oupd_nat (Z.to_nat (Z.land position (2^tl - 1))) b0 syms))
  by (apply ostore_ok; first [rewrite FseLemmas.Zlength_correct; lia | unfold FseNCount.Zlength; lia | rewrite Zlength_correct; lia]).
rewrite OS1 in HP. cbn [bind] in HP.
destruct (oload spread (s + 1)) as [b1| | |] eqn:OL1; cbn [bind] in HP; try discriminate HP.
unfold ASHOFF.
(wk_go [0x97e58]).
set (p0 := Z.land position (2^tl - 1)) in *.
destruct (oload_Ok _ _ _ OL0) as (OLR0 & OLN0).
pose proof (omerge_nth spread js (Z.to_nat s) b0 HJS OLN0) as NE0.
pose proof (u8arr_read bsegs m1 SPR _ s _ (Z_to_bv 64 (SPR - 2 + s + 2)) SPB1 NE0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD.
zstep. wk_if_false.
destruct (p_st m1 syms p0 b0 INV0 M0 HL) as (SOK & INV2).
replace (wa (TD + (4 * p0 + 2))) with (Z_to_bv 64 (TD + Z.shiftl p0 2 + 2)) in SOK, INV2
  by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite <- (le1_zxbA b0) in INV2.
zstep.
pose proof INV2 as INV2'. destruct INV2' as (U2 & MU2 & WM2 & MI2).
assert (FR16_2 : rw_cells bsegs (write_to_mem m1 (Z_to_bv 64 (TD + Z.shiftl p0 2 + 2)) (le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b0))))) (SP + 16) [C8 (Z_to_bv 64 stp)])
  by (apply (rw_cells_transport bsegs _ m _ (SP + 16) _ FR16 MU2 WM2); cbn [disjoint_from]; cbn; lia).
assert (FR56_2 : rw_cells bsegs (write_to_mem m1 (Z_to_bv 64 (TD + Z.shiftl p0 2 + 2)) (le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b0))))) (SP + 56) [C8 (Z_to_bv 64 (2^tl))])
  by (apply (rw_cells_transport bsegs _ m _ (SP + 56) _ FR56 MU2 WM2); cbn [disjoint_from]; cbn; lia).
pose proof (p_mask (position + stp)) as M1.
pose proof (zshadow_munch _ m _ TD (4 * 2^tl) ZT MU2 (shad_outside1 TD (4 * 2^tl) TD (4 * 2^tl) BTD ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZT2.
pose proof (zshadow_munch _ m _ SPR (zlen js) ZS MU2 (shad_outside1 SPR (zlen js) TD (4 * 2^tl) BTD ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZS2.
clear ZT1 ZS1.
(wk_go [0x97ea4]).
set (p1 := Z.land (position + stp) (2^tl - 1)) in *.
destruct (oload_Ok _ _ _ OL1) as (OLR1 & OLN1).
pose proof (omerge_nth spread js (Z.to_nat (s + 1)) b1 HJS OLN1) as NE1.
assert (SPB2 : u8arr bsegs (write_to_mem m1 (Z_to_bv 64 (TD + Z.shiftl p0 2 + 2)) (le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b0))))) SPR (omerge js spread))
  by (apply (u8arr_transport bsegs _ m _ SPR _ SPB0 MU2 WM2); cbn [disjoint_from]; rewrite omerge_length; lia).
pose proof (u8arr_read bsegs _ SPR _ (s + 1) _ (Z_to_bv 64 (SPR - 2 + s + 3)) SPB2 NE1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD.
zstep. wk_if_false.
assert (HL2 : length (oupd_nat (Z.to_nat p0) b0 syms) = Z.to_nat (2^tl)) by (rewrite oupd_nat_length; exact HL).
rewrite le1_zxbA in INV2.
destruct (p_st _ _ p1 b1 INV2 M1 HL2) as (SOK3 & INV3).
replace (wa (TD + (4 * p1 + 2))) with (Z_to_bv 64 (TD + Z.shiftl p1 2 + 2)) in SOK3, INV3
  by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite <- (le1_zxbA b1) in INV3.
rewrite (le1_zxbA b0) in *.
zstep.
pose proof INV3 as INV3'. destruct INV3' as (U3 & MU3 & WM3 & MI3).
assert (FR56_3 : rw_cells bsegs (write_to_mem (write_to_mem m1 (Z_to_bv 64 (TD + Z.shiftl p0 2 + 2)) [Z_to_bv 8 b0]) (Z_to_bv 64 (TD + Z.shiftl p1 2 + 2)) (le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b1))))) (SP + 56) [C8 (Z_to_bv 64 (2^tl))])
  by (apply (rw_cells_transport bsegs _ m _ (SP + 56) _ FR56 MU3 WM3); cbn [disjoint_from]; cbn; lia).
zstep. zstep. zstep. zstep.
assert (OS2 : ostore (oupd_nat (Z.to_nat p0) b0 syms) p1 b1 = Ok (oupd_nat (Z.to_nat p1) b1 (oupd_nat (Z.to_nat p0) b0 syms)))
  by (apply ostore_ok; first [rewrite FseLemmas.Zlength_correct; lia | unfold FseNCount.Zlength; lia | rewrite Zlength_correct; lia]).
rewrite OS2 in HP. cbn [bind] in HP.
assert (HL3 : length (oupd_nat (Z.to_nat p1) b1 (oupd_nat (Z.to_nat p0) b0 syms)) = Z.to_nat (2^tl)) by (rewrite !oupd_nat_length; exact HL).
pose proof (p_mask (position + 2 * stp)) as M2.
rewrite (le1_zxbA b1) in *.
destruct (Z.eq_dec (s + 2) (2^tl)) as [EQ|NE].
- destruct f as [|f]; [|lia]. cbn [place_loop] in HP. injection HP as <-.
  zstep. wk_if_false. zstep.
  exact (K _ _ _ _ _ _ _ _ _ _ eq_refl HL3 INV3).
- zstep. wk_if_true.
  exact (IH (s + 2) _ _ r _ _ _ _ _ _ HP ltac:(lia) ltac:(lia) M2 HL3 INV3 K).
Qed.
End Place.
End CANSEC1.
