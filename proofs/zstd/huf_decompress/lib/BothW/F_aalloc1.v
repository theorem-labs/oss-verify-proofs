(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AKit AModelFacts F_aunwind F_aalloc_s F_acache.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_aalloc1 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC56Stdlib6ZArith6BinInt1Z3lebC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr05I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6leb_gtK4ELinuxProcessSemantics5Riscv5Instr5instr01C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuK4ELinuxProcessSemantics5Riscv5Instr5instr0:C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK46Stdlib9micromega6VarMap1t01C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_leK4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6rz_logC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPc5ARocqVerifyHarness?AgentSubmission5BothW9F_aalloc1<allocA_cellsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;needed_sizeC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4iclrc5ARocqVerifyHarness?AgentSubmission5BothW9F_aalloc1;allocA_postK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C56Stdlib6ZArith6BinInt1Z3mulK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell03C5ARocqVerifyHarness?AgentSubmission5BothW;AModelFacts;small_factsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<rounded_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7rz_sizeC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5BothW9F_aunwind@asan_inited_specC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC5ARocqVerifyHarness?AgentSubmission5BothW:F_aalloc_s8rss_specC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib5Image:ro_bytes_bC5ARocqVerifyHarness?AgentSubmission3Lib5Image>ro_cells_imageC5ARocqVerifyHarness?AgentSubmission3Lib4Step8ro_cellsC5ARocqVerifyHarness?AgentSubmission3Lib2FP9bv_lit_eqC5ARocqVerifyHarness?AgentSubmission3Lib4Step@ro_cells_read_atK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC47Corelib5Lists7ListDef5skipnc5ARocqVerifyHarness?AgentSubmission5BothW9F_aalloc1>rz_ladder_specC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr0>C5ARocqVerifyHarness?AgentSubmission4LibA5StepF=stk_lo_nonnegC56Stdlib6ZArith6BinInt1Z4of_NC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5BothW:F_aalloc_s;rz2log_postC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW:F_aalloc_s=rz2log16_specK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib3Arr@u32arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission5BothW:F_aalloc_s?rz2log2048_specC5ARocqVerifyHarness?AgentSubmission5BothW;AModelFactsBrz_log_range_smallc5ARocqVerifyHarness?AgentSubmission5BothW9F_aalloc1=rz_clamp_specC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission5BothW;AModelFactsBrounded_size_alignC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge<zb_land_maskK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sllwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_sllwC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64K5ARocqVerifyHarness?AgentSubmission5BothW4AKit5boxed01I5ARocqVerifyHarness?AgentSubmission5BothW4AKit5boxed00C5ARocqVerifyHarness?AgentSubmission5BothW9F_aunwindGget_current_thread_specC5ARocqVerifyHarness?AgentSubmission5BothW8F_acache>cache_hit_postC5ARocqVerifyHarness?AgentSubmission5BothW8F_acacheGcombined_alloc_hit_specK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission3Lib6ExElim9ex_elim_2C56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z8land_0_lC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission5BothW;AModelFacts7sllw_rzC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC5ARocqVerifyHarness?AgentSubmission5BothW;AModelFacts;land_align8C5ARocqVerifyHarness?AgentSubmission3Lib6ExElim9ex_elim_5K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission5BothW4AKit8sx16_litC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK46Stdlib9micromega7EnvRing5PExpr04K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness?AgentSubmission5BothW:F_aalloc_s7ARSSLIMC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5ATSDIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5ATSDKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5ATP88C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ATSDK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib7Numbers7BinNums1N01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9AINSTANCEC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIc5ARocqVerifyHarness?AgentSubmission5BothW9F_aalloc1>allocate_entryC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AINITEDK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize02".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=      
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Definition allocate_entry := 0x318b4%Z.




Lemma rz_ladder_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x31a20) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3194c) fc None m (seg_rom bsegs)).
Proof using Type.
  intros until n. intros N RIMG. unfold rz_log.
  step. if_cases K0; zify_cond K0.
  2: { replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K1; zify_cond K1.
  2: { replace (n <=? 96) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K2; zify_cond K2.
  2: { replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K3; zify_cond K3.
  2: { replace (n <=? 3968) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K4; zify_cond K4.
  2: { replace (n <=? 16128) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K5; zify_cond K5.
  2: { replace (n <=? 32256) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 32256) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. zstep. zstep.
  apply evtF_done. destruct (Z.leb_spec n 64512) as [K6|K6]; eexists.
  - replace (n <? 64513) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (n <? 64513) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.




Lemma rz_clamp_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n rz : Z),
  0 <= n < 2^40 -> 0 <= rz <= 7 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x31a68) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x31a4c) fc None m (seg_rom bsegs)).
Proof using Type.
  intros until rz. intros N RZ RIMG.
  step. if_cases K0; zify_cond K0.
  -
    step. if_cases K1; zify_cond K1.
    + step. step. step. if_cases K2; zify_cond K2.
      * replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
    + step. replace rz with 7 by lia. step. step. step. if_cases K2; zify_cond K2.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
  - step. replace rz with 0 by lia. step. if_lit. step. step. step. if_cases K2; zify_cond K2.
    + replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
    + step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
Qed.





Definition allocA_cells (m : amem) (ctx t : Z) : Prop :=
     rw_cells bsegs m AINITED [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m ARSSLIM [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0xb7ab8  [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)].

Definition allocA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t c cnt spacebeg lo : Z) (idxw maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x31b54) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw)) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x31b54) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells bsegs m' (bv_unsigned sp - 128)
         [CB 8 j0 ; C8 (Z_to_bv 64 1) ; C8 (Z_to_bv 64 16) ;
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ rw_cells bsegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj']).

Lemma allocA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= 448 -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  rw_cells bsegs m 0xb6cb8 [C8 (Z_to_bv 64 spacebeg)] ->
  Z.shiftr (needed_size n + 31) 5 = c ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (allocA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t c cnt spacebeg lo idxw maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof using Type.
  intros until idxw. intros ST CEIL LO MI TP -> -> -> -> -> -> N HS AC SB HC CR CH LCH CNT NTH IXS STS C0 C1 T0 T1 TAL CT2 SBR RIMG RSTK RCTX RT. band_lin.
  destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.
  do 6 step.
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.
  step. callp rss_spec; [exact RSS|]. step. if_lit.
  step. if_cases KS; zify_cond KS. { exfalso. lia. }
  step. step. if_lit.
  step. step. step. if_lit.
  zstep. zstep. step. if_lit.
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.
  lstep. zstep. zstep. zstep.
  step. step. if_lit.
  step. zstep. zstep. step. if_lit.
  step. zstep. step. step.
  callp rz_ladder_spec; [lia|].
  lstep. step. step. zstep. zstep.
  step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.
  step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| pose proof (rz_log_range_small n N); lia |].
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }
  step. zstep.
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.
  pose proof (rz_log_range_small n N) as RLR. rewrite (sllw_rz n N).
  step. zstep.
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].
  zstep.
  rewrite <- NS.
  zstep. zstep. zstep. zstep. step. zstep.
  replace (needed_size n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((Z.land 1 1 + -1) mod 18446744073709551616) with 0. change (Z.land 1 1) with 1. rewrite Z.land_0_l, Z.add_0_l.
  step. if_cases KB; zify_cond KB. { exfalso. lia. }
  step. if_cases KC; zify_cond KC. { exfalso. lia. }
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }
  box RT.
  step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }
  zstep. step. step. step.
  box RCTX.
  step. call_sp (combined_alloc_hit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t (needed_size n) c cnt spacebeg lo maxc csz stj chunks idxw).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
       | |- rng _ _ _ => solve_rng
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- Z.shiftr _ _ = _ => exact HC
       | |- nth_error _ _ = _ => exact NTH
       | |- length _ = _ => exact LCH
       | |- _ mod _ = _ => exact TAL
       | |- u32arr _ _ _ _ => exact CH
       | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR
       | |- rw_cells _ _ (_ + 2784) _ => exact STS
       | |- rw_cells _ _ _ _ => exact SB
       | |- _ => unfold AIMG_HI; lia
       end.
  apply evtF_done. unfold allocA_post. do 15 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed.
End CANSEC1.
