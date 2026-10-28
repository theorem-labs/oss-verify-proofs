(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_bdt_fast () := "C47Corelib7Classes?RelationClasses9ReflexiveC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init9Datatypes6lengthI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<spread_innerC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6write8C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model9write8_OkC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model2wrC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model6omergeC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model<omerge_storeI4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8oupd_natC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT?oupd_nat_lengthK4ELinuxProcessSemantics5Riscv3Sem4core01C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model6wr4_eqC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model8wr8_machC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model9wr_lengthK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_geC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos6to_natC47Corelib4Init5Logic7f_equalK4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model=omerge_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeK46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List7forallbC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast3SVKC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List:in_map_iffI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast;sv_bytes_okC46Stdlib5Lists4List8map_consK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7to_byteC56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_modK47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast7sv_byteC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z:shiftr_0_rC56Stdlib6ZArith6BinInt1Z3subc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast6sp_invK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC47Corelib4Init3Nat3mulC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u16_znthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast6sv_le1c5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast8sv_le1_0C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3u64C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;spread_loopC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:signed_litK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04c5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast8sp_innerc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast8sv_rangeC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem:sx16_shortC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast6pl_invC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model4tsymC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;tsym_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?wr_at_transportC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:table_stepC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5oloadC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model8oload_OkC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model9ostore_OkC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model:omerge_nthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:u8arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast?land_mask_rangeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model:tsym_storeC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega:ZMicromega;ZArithProof04C46Stdlib4Bool4Bool>negb_false_iffc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast7le1_zxbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_land_lC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:place_loopC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6ostoreK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac spb SPR ARR q :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok usegs _ SPR _ q (wa (SPR + q)) ARR ltac:(rewrite omerge_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (SPR + q) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (SPR + q) by lia
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?x)) _) =>
    first [ match goal with H : le1 x = [_] |- _ => rewrite H end | rewrite le1_lit ]
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write usegs _ SPR _ q bb ARR ltac:(rewrite omerge_length; lia)) as ARR2;
    clear ARR; store_done;
    rewrite omerge_store in ARR2 by (rewrite ?oupd_nat_length; lia);
    rename ARR2 into ARR
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inner.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x5 x6 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x27 x28 : word).
  Variables (m : fmem) (SPR : Z) (js : list byte) (pos n b : Z).
  Variable POST : machine_state -> Prop.
  Hypothesis B8 : le1 x8 = [Z_to_bv 8 b].
  Hypothesis B20 : le1 x20 = [Z_to_bv 8 b].
  Hypothesis B21 : le1 x21 = [Z_to_bv 8 b].
  Hypothesis B22 : le1 x22 = [Z_to_bv 8 b].
  Hypothesis B23 : le1 x23 = [Z_to_bv 8 b].
  Hypothesis B24 : le1 x24 = [Z_to_bv 8 b].
  Hypothesis B25 : le1 x25 = [Z_to_bv 8 b].
  Hypothesis B27 : le1 x27 = [Z_to_bv 8 b].
  Hypothesis HSPR : 0 < SPR /\ SPR + zlen js <= 2^64.
  Hypothesis HPOS : 0 <= pos.

  Notation ST pc mm x1 x7 x10 x18 x30 :=
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             (Z_to_bv 64 n) x27 x28 (Z_to_bv 64 SPR) x30 (Z_to_bv 64 pos))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma wr8_perm : forall l p v, 0 <= p ->
    oupd_nat (Z.to_nat (p + 3)) v (oupd_nat (Z.to_nat (p + 2)) v (oupd_nat (Z.to_nat (p + 1)) v (oupd_nat (Z.to_nat p) v
      (oupd_nat (Z.to_nat (p + 7)) v (oupd_nat (Z.to_nat (p + 6)) v (oupd_nat (Z.to_nat (p + 5)) v
      (oupd_nat (Z.to_nat (p + 4)) v l))))))) = wr 8 l p v.
  Proof.
    intros l p v Hp. cbn [wr].
    replace (p + 1 + 1) with (p + 2) by lia. replace (p + 2 + 1) with (p + 3) by lia.
    replace (p + 3 + 1) with (p + 4) by lia. replace (p + 4 + 1) with (p + 5) by lia.
    replace (p + 5 + 1) with (p + 6) by lia. replace (p + 6 + 1) with (p + 7) by lia.
    assert (C : forall i j l0, oupd_nat i v (oupd_nat j v l0) = oupd_nat j v (oupd_nat i v l0))
      by (intros i j l0; destruct (Nat.eq_dec i j) as [->|NE]; [reflexivity | apply oupd_nat_comm; exact NE]).
    set (a0 := Z.to_nat p). set (a1 := Z.to_nat (p + 1)). set (a2 := Z.to_nat (p + 2)). set (a3 := Z.to_nat (p + 3)).
    set (a4 := Z.to_nat (p + 4)). set (a5 := Z.to_nat (p + 5)). set (a6 := Z.to_nat (p + 6)). set (a7 := Z.to_nat (p + 7)).
    rewrite (C a0 a7), (C a0 a6), (C a0 a5), (C a0 a4), (C a1 a7), (C a1 a6), (C a1 a5), (C a1 a4).
    rewrite (C a2 a7), (C a2 a6), (C a2 a5), (C a2 a4), (C a3 a7), (C a3 a6), (C a3 a5), (C a3 a4).
    reflexivity.
  Qed.

  Lemma sp_inner : forall f spr i r m1 (x18 : word),
    spread_inner f spr pos i n b = Ok r ->
    8 <= i < n -> n < 2^30 -> length js = length spr ->
    u8arr usegs m1 SPR (omerge js spr) ->
    munch [(SPR, SPR + zlen js)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    (forall m2 (y1 y7 y10 y18 y30 : word), u8arr usegs m2 SPR (omerge js r) -> length r = length spr ->
       munch [(SPR, SPR + zlen js)] m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
       evt usegs POST (ST 0x1f414 m2 y1 y7 y10 y18 y30)) ->
    evt usegs POST (ST 0x1f3dc m1 (Z_to_bv 64 (Z.lxor (SPR + pos) 18446744073709551615)) (Z_to_bv 64 (SPR - 2 + pos))
                       (Z_to_bv 64 i) x18 (Z_to_bv 64 (i + 2))).
Proof.
  induction f as [|f IH]; intros spr i r m1 x18 HR HI HN31 HL ARR MU WM MI K; [discriminate HR|].
  cbn [spread_inner] in HR.
  replace (i <? n) with true in HR by (symmetry; apply Z.ltb_lt; lia).
  destruct (write8 8 spr (pos + i) b) as [sp1| | |] eqn:W8; cbn [bind] in HR; try discriminate HR.
  apply write8_Ok in W8 as (WP0 & WP8 & ->). change (Z.of_nat (S 7)) with 8 in WP8.
  zstep. zstep. if_cases KC; zify_cond KC;
    [exfalso; rewrite ?zb_lxor_ones in KC by lia; Z.div_mod_to_equations; lia | clear KC].
  zstep. zstep. rewrite ?(swrap32_small (i + 8)) by lia.
  spb SPR ARR (pos + i + 4). spb SPR ARR (pos + i + 5). spb SPR ARR (pos + i + 6). spb SPR ARR (pos + i + 7).
  spb SPR ARR (pos + i). spb SPR ARR (pos + i + 1). spb SPR ARR (pos + i + 2). spb SPR ARR (pos + i + 3).
  rewrite (wr8_perm spr (pos + i) b) in ARR by lia.
  zstep. zstep. if_cases K1; zify_cond K1; rewrite ?(swrap32_small (i + 8)) in K1 |- * by lia; rewrite ?signed_lit in K1 by lia.
  - try replace (i + 10) with (i + 8 + 2) by lia.
    eapply IH; [exact HR | lia | lia | rewrite wr_length; exact HL | exact ARR | eassumption | eassumption | eassumption |].
    intros m2 y1 y7 y10 y18 y30 A2 L2 M2 W2 I2. rewrite wr_length in L2. eapply K; eassumption.
  - destruct f as [|f]; [discriminate HR|]. cbn [spread_inner] in HR.
    replace (i + 8 <? n) with false in HR by (symmetry; apply Z.ltb_ge; lia).
    cbn [bind] in HR. injection HR as <-.
    eapply K; [exact ARR | exact (wr_length 8 spr (pos + i) b) | eassumption | eassumption | eassumption].
Qed.
End Inner.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SVK : Z := 72340172838076673.     (* [comment removed for export] *)

Lemma sv_bytes_ok : forallb (fun s => forallb (fun k => Z.shiftr (s * SVK) k mod 256 =? s) [0; 8; 16; 24; 32; 40; 48; 56])
                            (map Z.of_nat (seq 0 256)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_fast ()) [] "h01kh11sp;2p;1p;3p;4g00I4j2ATg025Hj2@Tg025ej2;Tg002hj11Tg006@j12Tg026Ej2<Tg026ej2:Tg007:j16Tg00:Yj19Tg00;9j37Tg027Bj38Tg027^j2?Tg028:j4>Tg00B_j3=Tg00ACj10Tf0R0#1#1p=5g01dKR1f1R2;70p=4%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3g01cKR3g01ckR4'Ag028V,@2/;0g01ohR0#1R5#5R6#1R7#1R8#1#5#2'</:2X01g01di%26%27%60R0#1#5R7#2%28%65#1#5#2%17#2%60#1#5#2%91'4'4'4'4'4'4'4571581X11g01b7P1g009<g020MR0%30#3#3#3#3#3#3#3'?C>581==34do"). Qed.

Lemma sv_byte : forall s k, 0 <= s < 256 -> In k [0; 8; 16; 24; 32; 40; 48; 56] -> Z.shiftr (s * SVK) k mod 256 = s.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_fast ()) [] "h01xh11kh21Hh32H0h44__p1h54__p2h64__x1h74__x2h81nh91yh:1Ah;1Bh<7__arithh=4__ffh>8__varmaph?5__with@1fhA1lhB5lemmahC3lenhD1mhE1shF5starthG2z0hH2HIhI2HkhJ2Hsp&0p;2p;1p;3p;4p;5p;<p;6p;7p;8p;Bg00KKR0j29Tg002hj14Tg006@j18Tg006^R1j26Tg00ODR2j21Tg007:j1OTg00:Yj1\Tg00;9j3STg029Tj32Tg026ej27Tg027Bj3BTg00ACj10Tg027^j2GTg028:j4HTg029kj2[Tg02:Dj3]Tg02;5j3cTg002Hj1bTg00B_j3Dj1iTg00O_j2aTg02;Xj5kTg009<R3j1eTg00hoR4j1YTg01_<j2FTg00S>j1hTg00I4j2@Tg01B?l<MTg01_Yj2fTg01]hj2LTg00U>j2ITg01Goj3KTg01HXj2TTg00T?k10>Tg00T]k20=Tg00Ugk30<Tg00Ejk208Tg00FHk107Tg01CKk402Tg00Ffk101Tg00GDj1}Tg00Goj2XTg01DMj4ETg00VPj2_Tg00=ej1yTg00HRj2xTg00INj2wTg00J:j3tTg00JYj4sTg01`;j4ZTg02<7R5j2UTg02<Qj2QTg00lkR6j2PTg02<hj3rTg009\R7j2uTg02=Cj6zTg01IDj3oTg01`fj4|Tg02=lj4nTg02>Fj2~Tg025Hk200Tg025ej2mTg026Ej2lTg01Fdl<dTg01Cik604Tg01E8k705Tg01E\k706Tg01]Dj7jTg01F@k80:Tg01GImB0;Tf0R8#4#4p=Cg01dKR9f1R:;S8p=>g028V-008p=?f2R;/m:/l8p=;%08#0#0#0p>09%08#0#0#0#0#0#0#0p>03%08#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p={%08#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p==g01cKR<g01ckR=7D8p=3AD9:8p=5P9g01b7R>P9P9P4f4R4P3f3R?g01nYP;P:P8M<dp=WP>P9P9P9P3P3f5R@P4P?P;P:P8M<dp=gg01diRA9D98p=Vg01gmRB?S:8p=AP:g01eGRCg01efRDPDg01fFREP8J04p=`P:PCPDPDPEP8g01gMK05p=:P;PCPDPDPEP:P8K06p=<P9P:g01ilP8CEp=NP;PCPDPDPEP:P8Fjp=^P?PCPDPDPEP;P:P8L0:p=JP>P9P5P3P0g02>fg020MR0PAP?P;P:P8M<Mp=vP>P>P>P9P9P9g02?HP3P3P3P7g02?hP0PAP?P;P:P8NB0;p=qP>P9P6P3P1g01oFP@P4P?P;P:P8M<Mp=pP9P:g01ffP8CEp=R19A:g01ohR1#4R6#CR7#4R5#4RC#4#C#8RF,6:'1%87%85%O1R5#4#CR7#8%8C%O6#4#C#8%47#8%O5#4#C#8%\9'>'>'>'>'>'>'>9S9AR5929:g02@K%?:?;8F/7:X19=B95XE9R7P>P9P3%00RC#0RG#0RH#0$09$03#{#=#=#=#=#=#=#=RI,G0RJCHRK5B9#3RLA298KP7P:O1#3[^09RM,[LA]LM8WBAc97KP8O2PMg02AQRMp4p710R7PMp4p7210RMP:\:RL%b;RNP2P4P?P;P:CH92?8P4P8O1=D@;f6RO?28?'1X0@,a@RP[P?P8O1=D4:A2@8;'1X04,a4P@P4P?P;CH924:[RQPOP@P4P?CH92@;\PP4P?P;P:P8DkP8n2001000000120000000X9;WAW@W;W:PQ^9;^AN^@L^;M^:7P8P>P9P3PJPOP>%e8R3f7R7'5A2>8J'1X0>%YORM%eMRL/5ORNA2>MJPN1FAORN/5ORJP9P9%i9RQP8X09RPPQ15:8RQ#hX99X09PLPNPPPP1@93X0>PMPNPP1FA8X09RMPOPO1@9OR3DWEgPOPOP3M<M1fAO16AO/1J19OA%VN'1'L1FA7RNP9p-0RJ1I9GRG1I9C1I90RC5K95K9g01hYR3'TRL1I9H&0>1-0=9>0<9G=K9CRC5K9/T3RG1TC3RC%\BR3'A'A'A%bBRBP92089;P:&079H02RH&019RR%}9RS1`S4RTP91X91R1g01iERU1X96R6CE,:SRV5<S1_9ARW,N6,:SP9P1PUPWCE,:SRU5<S5^S%yDRDPS1NW6,:S1`S@RX5<SPDPVCJCJ1xSEREP8P;1@<=1w8;#3dAt9A:CsR=b=b>b?X69X79X4JW5158:R<,1;19:A%V8RY'1'L19A;RZ/1415;?[[^69^79^4J^5JP8f9R[/6F16A[P[P:P;P7O6b<bGb3CZP21G:;92>81U;:1Q;?,P:'1R\[1U:81Q:;,P8'11G;?92>:[R]1G?492>;\\Ar;:8P8n2001000000120000000X8>XF>XC>P]^8>^F>^C>P8PIP0%Y7R>1U0>R]1Q0IR0,P>R\'119ANR^1uAFR_,6NR`'1P]P\P^P`1@9AR`P>PNPPPMP7P71@97DWRMCvP>PNPMP0P_P`PIPF1@9FCqEpEz1fA716A715N7'1197A%VN'1'Lf8RN,FAP91AL3,AG,ACPBPHPRPS1RW6,:S=<SVA<STU5^SPDPS1_9FRU,R6,:S9<SXPD1NW1,:SAo9WU,R1,:S5<SCJCJPEP=b=b>b?X69X79X4JX5J16A:/1<11;Y'L16;F,1416;_,1Z[[^69^79^4J^5JP8f:RJ,9A19JAPJP:P;PNO6b<bGb3CZO4b3C|CnO6b3A29@KP:POP8O2%?7?;8F/77X19=B95#3%?NRO?;8F/7NX19RK=B95#3A2985RA%?JRZ?;8F/7JX19P:O1#3[^09R_'[%?[?;8F/7[X19=B95#3f;R4#??;8F/74X19P:O1#3\A^09;]8WBAc9K5P8O2P_P8P7P@O2A;O7F/7N#3P217:8#315;:[R217;:#3RN\Q15?;\N1~:8P:n2001000000120000000XD9X89P2^D9^89P8A;Z[FPJP:O3b3b2b2b2bHb2b2WIWJX19XE9o"). Qed.

Lemma sv_range : forall s, 0 <= s < 256 -> 0 <= s * SVK < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_fast ()) [] "h04__x1h12Hsh27__arithh34__ffh48__varmaph55__with61sp;2p;1p;3p;4p;8p;7g00KKj2;Tg002hj10Tg006@j14Tg006^j2<Tg00ODj2:Tg00U>j28Tg00ACj19Tg01Goj3>Tg01HXj2=Tg02Anj2ATg00:Yj1DTg00;9j3BTg002Hj1VTg00Ejj2UTg00Ffj1TTg00GDj1RTg00VPj25Tg00Goj2QTg01DMj47Tg00=ej1MTg007:j11Tg02BZj3LTg003Mj1KTg00f]j3HTg01F@j8GTg00HRj2ITg00I4j2JTg00INj2FTg00B_j3ETg00J:j3NTg00JYj4OTg025Hj2@Tg007_j2PTg01E8j7CTg01E\j7STf0R0#0#0#0#0p=2f1R1g01eGR2g01efR3P3g01fFR4P0g01gMFCp=6f2R5P2P3P3P4P1P0FSp=?%00#0p=3g01dKR6g01diR7/;0g01ohR8#0R9#0#2R:#0R;#0#4R<,<0':R=g01gmR>g020MR?,86R@%9?#9R?,869>6@g01hYRA'='A%9?,869>6@/=A,A@%D>5B>3B%V>1U61%T6%R6R>P2P3P3P4P61567R2g01ilR@1Q68R8C7,6>P6P8g01ffRA156<C7,6>5?>%M3P6P2P@%1;#0#3#2#1#0#3#2#1#0#3#2#1#0#3#2#1#0#3#2#1#0#3#2#1#4R;,569L68R8C7,6>P6P8PA%49R9,56%K:5H6C7,6>5?>GG1I>4P0P5g01cKR>g01ckR4'J1F05=E>4dAN671COb3b4b5X061@1;R;,;7%4:,P9R9,<;':\=^06P0P5P1O2b2g028V,@1R1,;71<19':eW1W6o"). Qed.

Lemma sv_le1 : forall s k, 0 <= s < 256 -> In k [8; 16; 24; 32; 40; 48; 56] ->
  le1 (Z_to_bv 64 (Z.shiftr (s * SVK) k)) = [Z_to_bv 8 (to_byte s)].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_fast ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh62Hkh72Hsh81kh91lh:1sp;2p;1p;3p;4p;7p;8p;6g00KKj2ETg002hj10Tg006@j11Tg006^j2GTg00ODj2DTg007:j1;Tg00:Yj1:Tg029Tj3?Tg003Mj1>Tg003kj1ITg002Hj1ATg025Hj2`Tg025ej2ZTg00=?j28Tg00;9j3<j2Bj1VTg02C=j1CTg00B_j32Tg00I4j26Tg026Ej25Tg00Ejj2TTg00Ffj1STg00GDj1RTg00VPj2@Tg00Goj2QTg01DMj49Tg01E\j7LTg00=ej1KTg01F@j8JTg00HRj2MTg00INj2NTg00J:j3OTg00JYj4PTg02D8j3HTg001Hj67Tg00FHj1UTg02D[j6_Tg02E?j3^Tg02E`j3]Tg02F:j4YTg02G<j3XTg00cTj8FTg00Y4j1WTg02H5j1[Tg01E8j7\Tf0R0#0#0p=4g01dKR1f1R2;<0p=3P2g01eGR3g01efR4P4g01fFR5P0g01gMF\p==g01diR6/E2g01ohR7#0R8#4R9#0R:#0R;#0R<#4#1R=,G2'DR>%19%1:%;7R:#0#4R?#1%1;%;8#0#4#1%0?#1%;:#0#4#1%:1'3'3'3'3'3'3'3R:9?12%>9R9#IR?#AR8f3R;g028V'`f2R@'ZRA,89RB%:?RC5<?f4RD#CRE,89=<?C9280X98P8P81B?B%C;RF,89R9,B?PCPCP?P8\8RG%V?RHPHPBP9PG\?/6HP1P;15E=9210X51P115;=REA21D0X51RHP1P;PH161;PEg01gmRH#:R?%AHRH1T12%S1RG%R1R9P3P4P4P5P9P3P4P4P5P11@16RBg01il1Q17R7C9,=9P1P7g01ff1@1=R7C9,=9FLRI%K4PIGJ1M95RIP0P@g01cKRJg01ckRK'61N0@=2JKdAO162CPRKb1b2b3X411E601G0='DP>[^41P0PDP@O2b09H;=E715E=P?PH%U1PGP9P3P4P4P5P1P7g01iEPBC9,=9E_PIPKb1b2b3A21=6g020l[P0b09^;=E715F=921;e15A=P;P@P2A216@A?1@:;]0CYE79XAFGF168CGF%></8A#W%[AE7W6W7X81X:1o"). Qed.
Lemma sv_le1_0 : forall s, 0 <= s < 256 -> le1 (Z_to_bv 64 (s * SVK)) = [Z_to_bv 8 (to_byte s)].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_fast ()) [] "h01zh11Eh27__arithh34__ffh48__varmaph55__with64__x1h72Hsh81lh91sp;2p;1p;3p;4p;6p;7p;8g00KKj2ITg002hj10Tg006@j12Tg006^j2HTg00ODj2GTg003Mj1ETg003kj1VTg002Hj1BTg025Hj2=Tg00=?j29Tg00:Yj1<Tg00;9j3>j2Fj1ZTg02C=j1:Tg00B_j36Tg00I4j27Tg007:j1?Tg029Tj3XTg02I3j3WTg02F:j4UTg025ej2CTg026Ej21Tg02IMj1RTg00@Hj6QTg00Ejj2OTg00Ffj1NTg00GDj1MTg00VPj2ATg00Goj2LTg01DMj4;Tg01E\j7KTg00=ej1PTg01F@j8JTg00HRj2STg00INj2TTg00J:j3cTg00JYj4bTg02D8j3aTg001Hj68Tg00FHj1`Tg02D[j6_Tg02E?j3\Tg02G<j3[Tg00cTj8DTg00Y4j1YTg02H5j1]Tg01E8j7^Tf0R0#0#0p=5g01dKR1f1R2;>0p=3A6120p=4P2g01eGR3g01efR4P4g01fFR5P0g01gMF^p=@g01diR6/I0g01ohR7#0R8#5R9#0R:#0R;#0R<#5#2R=,H0'GR>%E9R?#VR@#BRAg028VRB,=2RC,9?RD%<@RE5>@f2RF#:,9?=>@E96A0X8APAPA1F@D%:2RG,9?R?,F@PEPEP@PA\ARH%Z@RIPIPDP?PH\@/7IP2P6P0A6166%29%2:%?7R:#0#5R9#2%2;%?8#0#5#2%09#2%?:#0#5#2%<1'3'3'3'3'3'3'39X1617163WCU1CC6/1=/42P11=FBR:/C6110=f3R9'4X01P0P:%R:EQ11:=/4FP1P9f4R:#:/1=,40X01P1119=R814:0X01R;P1P9P;1719P8g01gmR;#<RI%B;R;1O12%N1R@%M1RHP3P4P4P5PHP3P4P4P5P11A16R?g01il1L17R7C;,@HP1P7g01ff1A1=R7C;,@HFKRD%P4PDGJ1SH5RDP0PFg01cKRJg01ckRK'71T0F=6JKdAc162CbRKb3b4b5X611I621H2='G\>^61P0P:P9O2b29a9=E8118=PIP;%`1P@PHP3P4P4P5P1P7g01iEP?C;,@HE_PDPKb3b4b5A61=6g020l[P0b29\9=E8%:9/1=,49e1=9B/1=P0E8b1b19[CGGD17AEGD%E</9C#Y%]CE8W7X91o"). Qed.

Lemma sp_shl32_shr31 : forall x, 0 <= x < 2^31 -> ((x ≪ 32) mod 18446744073709551616) ≫ 31 = 2 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2^32) with ((2 * x) * 2^31) by (change (2^32) with (2 * 2^31); lia). apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Outer.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x5 x6 x13 x14 x15 x16 x17 : word).
  Variables (m : fmem) (NC SPR : Z) (nc : list Z) (M1 : Z) (js : list byte).
  Variable POST : machine_state -> Prop.
  Hypothesis HM1 : 1 <= M1 <= 256.
  Hypothesis HNCL : M1 <= zlen nc.
  Hypothesis HNCR : Forall (fun c => - 32768 <= c < 32768) nc.
  Hypothesis HNC : 0 < NC /\ NC + 2 * zlen nc <= 2^64.
  Hypothesis HSPR : 0 < SPR /\ SPR + zlen js <= 2^64.
  Hypothesis DNS : NC + 2 * zlen nc <= SPR \/ SPR + zlen js <= NC.
  Hypothesis NCB0 : bytes_at usegs m NC (u16s (map (Z_to_bv 64) nc)).     (* [comment removed for export] *)
  Hypothesis SP80 : rw_cells usegs m (bv_unsigned sp + 8) [C8 (Z_to_bv 64 (SPR - 2))].
  Hypothesis DSP : bv_unsigned sp + 8 + 8 <= SPR \/ SPR + zlen js <= bv_unsigned sp + 8.

  Definition sp_inv (m1 : fmem) (spr : list (option Z)) : Prop :=
    u8arr usegs m1 SPR (omerge js spr) /\ munch [(SPR, SPR + zlen js)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  Notation ST pc mm x1 x7 x8 x10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 :=
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 SVK) x10 (Z_to_bv 64 NC) (Z_to_bv 64 (M1 - 1)) x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (Z.lxor NC 18446744073709551615)) (Z_to_bv 64 SPR) x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma sp_outer : forall f s spr pos r m1 (x1 x7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 : word),
    spread_loop nc f s spr pos = Ok r ->
    Z.of_nat f = M1 - s -> 0 <= s < M1 -> 0 <= pos < 2^64 -> length spr = length js ->
    sp_inv m1 spr ->
    (forall m2 (y1 y7 y8 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y30 y31 : word), sp_inv m2 r -> length r = length js ->
       evt usegs POST (ST 0x1f48c m2 y1 y7 y8 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y30 y31)) ->
    evt usegs POST (ST 0x1f358 m1 x1 x7 (Z_to_bv 64 (s * SVK)) (Z_to_bv 64 s) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30
                       (Z_to_bv 64 pos)).
Proof using All.
  induction f as [|f IH]; intros s spr pos r m1 x1 x7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 HR HF HS HP HL INV K; [lia|].
  cbn [spread_loop] in HR.
  destruct (load nc s) as [n| | |] eqn:LD; cbn [bind] in HR; try discriminate HR.
  apply load_Ok in LD as (LDR & ->).
  pose proof (Forall_Znth _ nc s HNCR LDR) as NR. cbv beta in NR.
  destruct INV as (ARR & MU & WM & MI).
  destruct (write8 8 spr pos (to_byte s)) as [sp1| | |] eqn:W8; cbn [bind] in HR; try discriminate HR.
  apply write8_Ok in W8 as (WP0 & WP8 & ->). change (Z.of_nat (S 7)) with 8 in WP8. rewrite HL in WP8.
  zstep. zstep. zstep. rewrite (sp_shl32_shr31 s) by lia.
  zstep. if_cases KC1; zify_cond KC1; [exfalso; rewrite ?zb_lxor_ones in KC1 by lia; Z.div_mod_to_equations; lia | clear KC1].
  zstep. zstep. if_cases KC2; zify_cond KC2; [exfalso; rewrite ?zb_lxor_ones in KC2 by lia; Z.div_mod_to_equations; lia | clear KC2].
  zstep. do 8 zstep. rewrite (Z.mod_small s 4294967296) by lia.
  replace (NC + s ≪ 1) with (NC + 2 * s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (bytes_at_transport usegs _ m m1 _ _ NCB0 MU ltac:(cbn [disjoint_from]; rewrite u16s_length, length_map; split; [lia | exact I])) as NCB.
  lazymatch goal with |- _ => let a := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.cur_mem_addr in
    pose proof (u16_znth usegs m1 NC nc s a NCB ltac:(lia) ltac:(OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.addr_tac)) as RD end.
  zstep. rewrite (sx16_short (Znth s nc)) by lia.
  rewrite ?(Z.mod_small (s * SVK) 18446744073709551616) by (unfold SVK; lia).
  pose proof (sv_le1_0 s ltac:(lia)) as B0.
  pose proof (sv_le1 s 8 ltac:(lia) ltac:(simpl; auto 10)) as B1. pose proof (sv_le1 s 16 ltac:(lia) ltac:(simpl; auto 10)) as B2.
  pose proof (sv_le1 s 24 ltac:(lia) ltac:(simpl; auto 10)) as B3. pose proof (sv_le1 s 32 ltac:(lia) ltac:(simpl; auto 10)) as B4.
  pose proof (sv_le1 s 40 ltac:(lia) ltac:(simpl; auto 10)) as B5. pose proof (sv_le1 s 48 ltac:(lia) ltac:(simpl; auto 10)) as B6.
  pose proof (sv_le1 s 56 ltac:(lia) ltac:(simpl; auto 10)) as B7.
  let sv q := first [rewrite ?(Z.mod_small (s * SVK) 18446744073709551616) by (unfold SVK; lia); spb SPR ARR q
                    | zstep; rewrite ?(Z.mod_small (s * SVK) 18446744073709551616) by (unfold SVK; lia); spb SPR ARR q] in
  sv (pos + 4); sv (pos + 5); sv (pos + 6); sv (pos + 7); sv pos; sv (pos + 1); sv (pos + 2); sv (pos + 3).
  rewrite (wr8_perm js spr pos (to_byte s)) in ARR by lia.
  step_k ltac:(idtac). step_k ltac:(idtac). if_cases KB; zify_cond KB; rewrite ?signed_lit in KB by lia.
  1: (cbn [spread_inner] in HR; replace (8 <? Znth s nc) with false in HR by (symmetry; apply Z.ltb_ge; lia); cbn [bind] in HR;
      do 3 zstep; step_k ltac:(idtac); if_cases KD; zify_cond KD).
  1: (destruct f as [|f]; [|lia]; cbn [spread_loop] in HR; injection HR as <-).
  3: (step_k ltac:(idtac); if_cases KE; zify_cond KE; [exfalso; Z.div_mod_to_equations; lia | clear KE]).
  1: (eapply K; [unfold sp_inv; split; [exact ARR | split; [eassumption | split; eassumption]] | rewrite ?wr_length, ?oupd_nat_length; exact HL]).
  1: (rewrite (swrap32_small (s + 1)) by lia; replace (s * SVK + SVK) with ((s + 1) * SVK) by ring;
      rewrite <- (Z_to_bv_mod64 (pos + Znth s nc));
      eapply IH; [exact HR | lia | lia | apply Z.mod_pos_bound; lia | rewrite ?wr_length, ?oupd_nat_length; exact HL
                 | unfold sp_inv; split; [exact ARR | split; [eassumption | split; eassumption]] | exact K]).
  1: (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (rw_cells_transport usegs [(SPR, SPR + zlen js)] m mm _ _ SP80 ltac:(assumption) ltac:(assumption)
          ltac:(cbn [disjoint_from cells_size csize]; split; [lia | exact I])) as SP8 end).
  1: do 5 zstep.
  1: (lazymatch type of HR with context [spread_inner ?fu ?l ?p ?i ?nn ?bb] =>
        destruct (spread_inner fu l p i nn bb) as [sp2| | |] eqn:SI end; cbn [bind] in HR; try discriminate HR).
  1: (eapply sp_inner with (pos := pos) (n := Znth s nc) (b := to_byte s);
      [ first [exact SI | eassumption | lia | (rewrite ?wr_length, ?oupd_nat_length; symmetry; exact HL)] .. | ]).
  1: intros m2 y1 y7 y10 y18 y30 A2 L2 M2 W2 I2.
  1: repeat zstep.
  1: (if_cases KD; zify_cond KD).
  1: (destruct f as [|f]; [|lia]; cbn [spread_loop] in HR; injection HR as <-).
  1: (eapply K; [unfold sp_inv; split; [exact A2 | split; [exact M2 | split; [exact W2 | exact I2]]] | rewrite L2, ?wr_length, ?oupd_nat_length; exact HL]).
  all: try (rewrite (swrap32_small (s + 1)) by lia; replace (s * SVK + SVK) with ((s + 1) * SVK) by ring;
      rewrite <- (Z_to_bv_mod64 (pos + Znth s nc));
      eapply IH; [exact HR | lia | lia | apply Z.mod_pos_bound; lia | rewrite L2, ?wr_length, ?oupd_nat_length; exact HL
                 | unfold sp_inv; split; [exact A2 | split; [exact M2 | split; [exact W2 | exact I2]]] | exact K]).
Qed.
End Outer.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mask_range : forall x k, 0 <= k -> 0 <= Z.land x (2^k - 1) < 2^k.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_fast ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh61Hh72Hkh81kh91xp;2p;1p;3p;4p;6p;8p;7g00KKj25Tg002hj1TTg006@j18Tg007_j24Tg03>Cj1STg02J1j21Tg00B_j30Tg00:Yj1DTg002Hj1BTg00Ejj2ATg00Ffj1@Tg00GDj1>Tg00Goj2=Tg00VPj27Tg02KOj3RTg01DMj43Tg00HRj2LTg00I4j2KTg00INj2GTg00J:j3FTg00JYj4ETg03>aj1;Tg03??j1CTg001Hj69Tg03?cj2:Tg006^j22Tg00ODj2<Tg026Ej2HTg00FHj1ITg00=ej1JTg01F@j8?Tg00D^j4MTg02mMj3NTg03@Aj3OTg00@Hj6PTg01E8j7QTf1R0g01eGR1g01efR2P2g01fFR3f0R4g01gMFQp=6g01dKR5g01diR6/54R7P5g01ohR8#T#8R9/40R:#Sf2R;,49R<%88R='1R>9054X55g01gmR?#DR@%B?R?1A50RA%@5RB%>5RCP51=58R8175=5R5RDg01iEPDC3'61LC3RDP4P;g01cKREg01ckRF'K1G4;=0EFdAF560CERFb2b3b4X05114=RE=05E^05P4P<O1b1%;0RE%C0E911:=905EP5%;;REf4/:4R=,56f3R:,49RG,2='<X55P51H:<124G,<7X55P9P;P@P?%I5PBP51756RGg01ff1759C3,6CPDPFb2b3b41269P4b1P@P?PAPBPCP1P2P2P3P5PGg01ilP8C3,6CRC%J2PCG?PDPFb2b3b4X051560\7^05P4P:P;O2b1R7CM9N:<1::EAO:;7E9P>P4EPb6W7X85W9o"). Qed.

Lemma le1_zxb : forall b, le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 b))) = [Z_to_bv 8 b].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_fast ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51bh61lp;1p;2p;3p;4p;7p;6p;8g002hj10Tg003Mj1=Tg003kj1DTg002Hj1;Tg00=?j23Tg016Kj2PTg00:Yj19Tg00;9j3<j27j1@Tg00B_j32Tg00I4j24Tg03@dj2>Tg006@j16Tg007_j2QTg026Ej21Tg00FHj1OTg00Ffj1NTg00GDj1LTg00VPj2:Tg01DMj4JTg01E8j7ITg02D[j6CTg00HRj2ETg00INj2FTg00J:j3BTg00JYj4GTg02E?j3HTg001Hj65Tg03AJj2ATg02G<j3KTg00cTj88Tg00Y4j1?Tg02H5j1MTg01dKR0g01oh#0R1#0#0R2#=R3#DR4#;R5f0R6,33R7,P3R8,33R9%94R:5<4f1R;,33=<4:9256X65P5P517491747P:P:P4P5\5R<%@4R=P=P9P7P<\4/4=P01>36R=%61%62'QR1,16R411;1520X00P0%02#0#0R2#0#0#6R<,16R711;<9206X001407117<g01gmR7#9%;7%O0%N0%L0R7g01eGR9g01efR>P>g01fFR?P7P9P>P>P?P01:0<g01iEg01diR>,:0CJg01gMFIEC1E7?P6f2R?g01cKR7g01ckR9'41F6?=279dAB0>;CGb2b3b4A20<>g020l[P6b19H6<E511=1=204eP81A36E59K86G8145:G8%=2/38#?%M8E5W5o"). Qed.

(* [comment removed for export] *)
Ltac tdb TD ARR u :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok usegs _ TD _ (4 * u + 2) (wa (TD + (4 * u + 2))) ARR ltac:(rewrite tsym_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (TD + (4 * u + 2)) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (TD + (4 * u + 2)) by lia
  end;
  rewrite ?le1_zxb, ?le1_lit;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write usegs _ TD _ (4 * u + 2) bb ARR ltac:(rewrite tsym_length; lia)) as ARR2;
    clear ARR; store_done;
    replace (Z.to_nat (4 * u + 2)) with (4 * Z.to_nat u + 2)%nat in ARR2 by lia;
    rewrite tsym_store in ARR2 by (rewrite ?oupd_nat_length; lia);
    rename ARR2 into ARR
  end.

Section Place.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x8 x9 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word).
  Variables (m : fmem) (TD SPR : Z) (tl stp : Z) (jt js : list byte) (spread : list (option Z)).
  Variable POST : machine_state -> Prop.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HSTP : 0 < stp < 8192.
  Hypothesis HSTPV : stp = table_step (2^tl).
  Hypothesis HJT : length jt = (4 * Z.to_nat (2^tl))%nat.
  Hypothesis HJS : length js = length spread.
  Hypothesis HSPL : 2^tl <= zlen spread.
  Hypothesis HTD : 0 < TD /\ TD + 4 * 2^tl <= 2^64.
  Hypothesis HSPR : 0 < SPR /\ SPR + zlen js <= 2^64.
  Hypothesis DTS : TD + 4 * 2^tl <= SPR \/ SPR + zlen js <= TD.
  Hypothesis SPB0 : u8arr usegs m SPR (omerge js spread).     (* [comment removed for export] *)

  Definition pl_inv (m1 : fmem) (syms : list (option Z)) : Prop :=
    u8arr usegs m1 TD (tsym jt syms) /\ munch [(TD, TD + 4 * 2^tl)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  Notation ST pc mm x5 x6 x7 x10 x11 x12 x13 x15 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation STH pc mm x10 s x30 position :=
    (ST pc mm (Z_to_bv 64 (Z.lxor TD 18446744073709551615)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 (SPR + 1)) x10
        (Z_to_bv 64 s) (Z_to_bv 64 (Z.lxor SPR 18446744073709551615)) (Z_to_bv 64 stp) (Z_to_bv 64 (2^tl))
        (Z_to_bv 64 TD) (Z_to_bv 64 (2 * stp)) (Z_to_bv 64 SPR) x30 (Z_to_bv 64 position)).

  Lemma pl_loop : forall f s syms position r m1 (x10 x30 : word),
    place_loop tl f s spread syms position = Ok r ->
    2 * Z.of_nat f = 2^tl - s -> 0 <= s < 2^tl -> 0 <= position < 2^tl -> length syms = Z.to_nat (2^tl) ->
    pl_inv m1 syms ->
    (forall m2 syms' pos' (y5 y6 y7 y10 y11 y12 y13 y28 y29 y30 y31 : word), r = (syms', pos') ->
       length syms' = Z.to_nat (2^tl) -> pl_inv m2 syms' ->
       evt usegs POST (ST 0x1f508 m2 y5 y6 y7 y10 y11 y12 y13 (Z_to_bv 64 (2^tl)) (Z_to_bv 64 TD) y28 y29 y30 y31)) ->
    evt usegs POST (STH 0x1f4a4 m1 x10 s x30 position).
Proof using All.
  induction f as [|f IH]; intros s syms position r m1 x10 x30 HPL HF HS HP HL INV K.
  { lia. }
  cbn [place_loop] in HPL. rewrite <- HSTPV in HPL.
  destruct (oload spread s) as [b0|e0| |] eqn:E0; cbn [bind] in HPL; try discriminate HPL.
  destruct (ostore syms (Z.land position (2^tl - 1)) b0) as [syms1|e1| |] eqn:E1; cbn [bind] in HPL; try discriminate HPL.
  destruct (oload spread (s + 1)) as [b1|e2| |] eqn:E2; cbn [bind] in HPL; try discriminate HPL.
  destruct (ostore syms1 (Z.land (position + stp) (2^tl - 1)) b1) as [syms2|e3| |] eqn:E3; cbn [bind] in HPL; try discriminate HPL.
  apply oload_Ok in E0 as [_ N0]. apply ostore_Ok in E1 as [R1 E1]. apply oload_Ok in E2 as [_ N1]. apply ostore_Ok in E3 as [R3 E3].
  destruct INV as (ARR & MU & WM & MI).
  assert (T1 : 1 < 2^tl) by (replace 1 with (2^0) by reflexivity; apply Z.pow_lt_mono_r; lia).
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?zb_lxor_ones in K0 by lia; lia | clear K0].
  assert (LAND : forall x, 0 <= x -> Z.land x (2^tl + -1) = x mod 2^tl)
    by (intros x Hx; replace (2^tl + -1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); apply Z.land_ones; lia).
  pose proof (u8arr_transport usegs _ m m1 SPR _ SPB0 MU WM ltac:(cbn [disjoint_from]; rewrite omerge_length; split; [lia | exact I])) as SPB.
  pose proof (omerge_nth spread js (Z.to_nat s) b0 HJS N0) as NT0.
  zstep.
  zstep. zstep.
  rewrite (LAND position) by lia; rewrite (Z.mod_small position (2^tl)) by lia; rewrite ?(Z.mod_small position (2^64)) by lia.
  replace (position ≪ 2) with (4 * position) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  if_cases K1; zify_cond K1; [exfalso; rewrite ?zb_lxor_ones in K1 by lia; lia | clear K1].
  zstep.
  lazymatch goal with |- _ => let a := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.cur_mem_addr in pose proof (u8arr_read usegs m1 SPR _ s _ a SPB NT0 ltac:(lia) ltac:(OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.addr_tac)) as RD0 end.
  zstep.
  cbv beta. zstep.
  tdb TD ARR position.
  zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?zb_lxor_ones in K2 by lia; lia | clear K2].
  assert (PR1 : 0 <= (position + stp) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
  zstep. zstep. rewrite (LAND (position + stp)) by lia.
  zstep. rewrite ?(Z.mod_small ((position + stp) mod 2^tl) (2^64)) by lia.
  replace (((position + stp) mod 2^tl) ≪ 2) with (4 * ((position + stp) mod 2^tl)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. if_cases K3; zify_cond K3; [exfalso; rewrite ?zb_lxor_ones in K3 by lia; lia | clear K3].
  pose proof (u8arr_transport usegs _ m _ SPR _ SPB0 MU WM ltac:(cbn [disjoint_from]; rewrite omerge_length; split; [lia | exact I])) as SPB1.
  pose proof (omerge_nth spread js (Z.to_nat (s + 1)) b1 HJS N1) as NT1.
  zstep.
  lazymatch goal with |- _ => let a := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.cur_mem_addr in pose proof (u8arr_read usegs _ SPR _ (s + 1) _ a SPB1 NT1 ltac:(lia) ltac:(OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.addr_tac)) as RD1 end.
  zstep. cbv beta.
  zstep. zstep. zstep.
  tdb TD ARR ((position + stp) mod 2^tl).
  zstep. zstep.
  assert (LAND2 : forall x, 0 <= x -> Z.land x (2^tl - 1) = x mod 2^tl)
    by (intros x Hx; replace (2^tl - 1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); apply Z.land_ones; lia).
  rewrite (LAND2 position), (Z.mod_small position (2^tl)) in E1 by lia.
  rewrite (LAND2 (position + stp)) in E3 by lia.
  rewrite (LAND2 (position + 2 * stp)) in HPL by lia.
  subst syms1 syms2.
  if_cases KL; zify_cond KL.
  - rewrite (LAND (position + 2 * stp)) by lia.
    eapply IH; [exact HPL | lia | lia | apply Z.mod_pos_bound; lia | rewrite !oupd_nat_length; exact HL | split; [exact ARR | split; [exact MU | split; [exact WM | exact MI]]] | exact K].
  - destruct f; [ | exfalso; lia].
    cbn [place_loop] in HPL. injection HPL as HR. subst r.
    zstep.
    eapply K; [reflexivity | rewrite !oupd_nat_length; exact HL | split; [exact ARR | split; [exact MU | split; [exact WM | exact MI]]]].
Qed.
End Place.
(* [comment removed for export] *)
