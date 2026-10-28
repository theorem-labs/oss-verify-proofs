(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ShadowTac F_irt F_rip F_tryinit I_printf_lib I_printf_common I_printf_formats.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_I_printf_icpt () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitions;bv_unsignedK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneK47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib7Numbers7BinNums1N01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC5ARocqVerifyHarness?AgentSubmission3Lib5Cells>cells_size_appC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure<rw_cells_appC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C47Corelib5Lists7ListDef6repeatK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission5BothW<I_printf_libCrw_cells_recell_midC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC56Stdlib6ZArith6BinInt1Z9add_assocC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast=munch_write_nC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission4LibA5StepF=stk_lo_nonnegC56Stdlib6ZArith6BinInt1Z4of_NC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5BothW9F_tryinit<tryinit_postC5ARocqVerifyHarness?AgentSubmission5BothW9F_tryinit<tryinit_specK46Stdlib9micromega5Tauto8GFormula01I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission5BothW<I_printf_lib=unsigned_lit8C5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast@rw_cells_frame_nC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast;stk_write_nC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportK46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op205I47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize01c5ARocqVerifyHarness?AgentSubmission5BothW=I_printf_icpt=fprintf_i_midC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBshadow_bytes_munchC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow<shadow_bytesC5ARocqVerifyHarness?AgentSubmission5BothW<I_printf_libBprintf_common_postC5ARocqVerifyHarness?AgentSubmission3Lib3Tac>rw_cells_mergeC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_16c5ARocqVerifyHarness?AgentSubmission5BothW=I_printf_icpt;fprintf_i_AK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?wr_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission5BothW<I_printf_lib=rw_cells_joinC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDc5ARocqVerifyHarness?AgentSubmission5BothW=I_printf_icpt=vprintf_i_midc5ARocqVerifyHarness?AgentSubmission5BothW=I_printf_icpt=vprintf_i_preC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formats5FMT_DC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formatsDprintf_common_d_stmtc5ARocqVerifyHarness?AgentSubmission5BothW=I_printf_icptAfprintf_i_pre_intC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formats:FMT_TOOBIGC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formatsIprintf_common_toobig_stmtI47Corelib5Lists7ListDef6Forall00c5ARocqVerifyHarness?AgentSubmission5BothW=I_printf_icpt?fprintf_i_pre_sc5ARocqVerifyHarness?AgentSubmission5BothW=I_printf_icptDfprintf_i_pre_s_stmtC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formats9FMT_USAGEC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formatsHprintf_common_usage_specC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formats<FMT_CANTOPENC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formatsKprintf_common_cantopen_specC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formats;FMT_READERRC5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formatsJprintf_common_readerr_spec".
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Notation rt_ckpf m := (rw_cells bsegs m 0x14be78 [C8 (Z_to_bv 64 4294967296)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma vfprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j16 : list byte) (rav s0v s1v s2v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) [CB 16 j16; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44ecc) fc None m (seg_rom bsegs)).
Proof using Type.
  intros until s2v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (rav s0v s1v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) [CB 24 j24; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4435c) fc None m (seg_rom bsegs)).
Proof using Type.
  intros until s1v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 5 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j32 : list byte) (va : list cell) (rav s0v s1v s2v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) ([CB 32 j32; C8 s2v; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 48%nat ->
  rng RNG (bv_unsigned sp) 112 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x452e8) fc None m (seg_rom bsegs)).
Proof using Type.
  intros until s2v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
  rewrite cells_size_app, SZ in B. cbn in B.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac iprem :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
  | |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- unpoisoned _ _ _ => first [assumption | eassumption]
  | |- wr_at _ _ _ _ => first [assumption | eassumption]
  | |- app_blk _ _ => first [assumption | eassumption]
  | |- Forall _ _ => first [assumption | eassumption]
  | |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end]
  | |- ?g => unfold KHIGH, sf_hide in *; first [assumption | lia]
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition fprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j32,
    ms' = MS (mkR (Z_to_bv 64 0x452e8) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2
                  a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp - 48)) x13 x14 x15 x16 x17
                  (Z_to_bv 64 (bv_unsigned sp - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa7c98) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2432, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 112)
    /\ rw_cells bsegs m' (bv_unsigned sp - 112)
         [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
    /\ rt_inited m'.

Section FPRINTF.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2432)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis CKP : rt_ckpf m.
  Hypothesis RPF : rt_real_printf m.
  Hypothesis A1 : a1 = Z_to_bv 64 A.
  Hypothesis NA : (0 <= n /\ 65536 <= A - 64 /\ A + n + 64 < 2^47)%Z.
  Hypothesis FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)).

  Notation MID := (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  Lemma fprintf_i_A : forall Q,
    (forall m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       munch [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       stk bsegs m1 lo (bv_unsigned sp + -112) ->
       rw_cells bsegs m1 (bv_unsigned sp + -112)
         [CB 8 j8; C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48));
          C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
       rt_got m1 -> rt_shbase m1 -> rt_inited m1 -> rt_real_printf m1 ->
       evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x452a8) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 a1 a0
                              (Z_to_bv 64 0x1ea20) a1 (Z_to_bv 64 (bv_unsigned sp + -48)) x13 x14 x15 x16 x17
                              (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44394) fc None m1 (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x45228) fc None m (seg_rom bsegs)).
Proof using MI ST LO KLO GOT SHB INI CKP RPF RI RSTK.
    intros Q K.
    pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof CKP as CKPc. pose proof RPF as RPFc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF.
    recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
    carve_frame 112%nat ST0.
    do 15 zstep. zstep.
    call_sp tryinit_spec. all: match goal with |- ?g => idtac "=="; idtac g end. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    do 4 zstep. zstep.
    eapply K; try assumption; eassumption.
  Qed.

  Hypothesis PCI : printf_common_int_stmt A n.

  Lemma fprintf_i_pre_int :
    evtF bsegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x45228) fc None m (seg_rom bsegs)).
Proof using A n MI ST LO KLO GOT SHB INI CKP RPF A1 NA FZ RI RSTK RSHF PCI.
    apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
    { eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF; change (?P) with (sf_hide P) in FZ.
    call_sp PCI. all: iprem.
    do 4 zstep. do 3 zstep. zstep.
    apply evtF_done. unfold fprintf_i_mid.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2432)%Z with (bv_unsigned sp + -2432)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FR : rw_cells bsegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
    do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
  Qed.

  (* [comment removed for export] *)
  Variables (sstr : list byte) (RLO RHI : Z).
  Notation Sa := (bv_unsigned a2).
  Notation NS := (Z.of_nat (length sstr) + 1)%Z.
  Hypothesis LAY : rt_layout m.
  Hypothesis SSTR : bytes_at bsegs m Sa (sstr ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
  Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= Sa)%Z.
  Hypothesis APPS : app_blk Sa (Sa + NS).
  Hypothesis SPOS : (0 < Sa)%Z.
  Hypothesis USTR : unpoisoned m Sa (Sa + NS).
  Hypothesis NSZ : (NS <= 2^40)%Z.
  Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RS : rng RNG Sa NS.
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).
  Hypothesis PCS : printf_common_s_stmt A n.

  Lemma fprintf_i_pre_s :
    evtF bsegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x45228) fc None m (seg_rom bsegs)).
Proof using A n MI ST LO KLO GOT SHB INI CKP RPF A1 NA FZ RI RSTK RSHF sstr RLO RHI LAY SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RS RSH1 PCS.
    apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof APPS as APPS'. destruct APPS' as [LES AS']. unfold KLOW, KHIGH, KEND in AS'.
    assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
    { eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    assert (LAY1 : rt_layout m1).
    { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SSTR1 : bytes_at bsegs m1 Sa (sstr ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    assert (USTR1 : unpoisoned m1 Sa (Sa + NS)).
    { eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    assert (WR11 : wr_at bsegs m1 (shad RLO) (shad RHI - shad RLO)) by (eapply wr_at_transport; eassumption).
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF; change (?P) with (sf_hide P) in FZ; change (?P) with (sf_hide P) in LAY;
    change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in USTR; change (?P) with (sf_hide P) in WR1.
    chunk_split FR1 8%nat FRV. chunk_split FRV 1%nat FRW.
    call_sp PCS. all: iprem.
    chunk_join FRV FRW. chunk_join FR1 FRV.
    do 4 zstep. do 3 zstep. zstep.
    apply evtF_done. unfold fprintf_i_mid.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2432)%Z with (bv_unsigned sp + -2432)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FR : rw_cells bsegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
    do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
  Qed.
End FPRINTF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vprintf_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24 j16,
    ms' = MS (mkR (Z_to_bv 64 0x44ecc) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
                  a0 (Z_to_bv 64 0xb67e8) (Z_to_bv 64 0xb67e8) a0 a1 x13 x14 x15 x16 x17
                  a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa7c98) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2416, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 96)
    /\ rw_cells bsegs m' (bv_unsigned sp - 48) [CB 24 j24; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp - 96) [CB 16 j16; C8 s2; C8 a1; C8 a0; C8 (Z_to_bv 64 0x4435c)]
    /\ rt_inited m'.

Section VPRINTF.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2416)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis CKP : rt_ckpf m.
  Hypothesis RPF : rt_real_printf m.
  Hypothesis A0 : a0 = Z_to_bv 64 A.
  Hypothesis NA : (0 <= n /\ 65536 <= A - 64 /\ A + n + 64 < 2^47)%Z.
  Hypothesis FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)).
  Hypothesis PCI : printf_common_int_stmt A n.

  Lemma vprintf_i_pre :
    evtF bsegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x442f8) fc None m (seg_rom bsegs)).
Proof using A n MI ST LO KLO GOT SHB INI CKP RPF A0 NA FZ RI RSTK RSHF PCI.
    pose proof (munch_refl [(bv_unsigned sp + -2416, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2416) 2416) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof CKP as CKPc. pose proof RPF as RPFc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF.
    recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
    carve_frame 48%nat ST0.
    do 7 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    do 4 zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
      assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z))
        by (eapply shadow_bytes_munch; [exact FZ | exact MU1 |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]))
    end end.
    change (?P) with (sf_hide P) in FZ.
    call_sp PCI. all: iprem.
    clear FZ1.
    do 4 zstep. zstep.
    do 7 zstep. zstep.
    match goal with H : stk bsegs _ lo (bv_unsigned sp + -48) |- _ => carve_frame 48%nat H end.
    do 9 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. cbv in K4. lia. } clear K4.
    do 4 zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
      assert (FZ2 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z))
        by (unfold sf_hide in FZ; eapply shadow_bytes_munch; [exact FZ | exact MU1 |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]))
    end end.
    call_sp PCI. all: iprem.
    clear FZ2.
    do 5 zstep. zstep.
    apply evtF_done. unfold vprintf_i_mid.
    replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2416)%Z with (bv_unsigned sp + -2416)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FRa : rw_cells bsegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3] rest FRa) as FRm1; cbn [app cells_size csize Nat.add] in FRm1 end;
      lazymatch goal with FRb : rw_cells bsegs mf (bv_unsigned sp + -96) (?c1 :: ?c2 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2] rest FRb) as FRm2; cbn [app cells_size csize Nat.add] in FRm2 end end.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm1. exact FRm2.
  Qed.
End VPRINTF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Corollary vprintf_i_pre_d : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2416)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
  a0 = Z_to_bv 64 FMT_D ->
  shadow_bytes m (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64)) ->
  evtF bsegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x442f8) fc None m (seg_rom bsegs)).
Proof using Type. intros. eapply vprintf_i_pre; try eassumption. { unfold FMT_D. lia. } exact printf_common_d_stmt. Qed.

Corollary fprintf_i_pre_toobig : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
  a1 = Z_to_bv 64 FMT_TOOBIG ->
  shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64)) ->
  evtF bsegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45228) fc None m (seg_rom bsegs)).
Proof using Type. intros. eapply fprintf_i_pre_int; try eassumption. { unfold FMT_TOOBIG. lia. } exact printf_common_toobig_stmt. Qed.

(* [comment removed for export] *)
Definition fprintf_i_pre_s_stmt (A n : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sstr : list byte) (RLO RHI : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m -> rt_layout m ->
  a1 = Z_to_bv 64 A ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
  bytes_at bsegs m (bv_unsigned a2) (sstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr ->
  (bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  app_blk (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (0 < bv_unsigned a2)%Z ->
  unpoisoned m (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (Z.of_nat (length sstr) + 1 <= 2^40)%Z ->
  (RLO <= bv_unsigned a2 /\ bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
  rng RNG (bv_unsigned a2) (Z.of_nat (length sstr) + 1) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF bsegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45228) fc None m (seg_rom bsegs)).

End CANSEC2.
Ltac fis PC A := unfold fprintf_i_pre_s_stmt; intros; eapply fprintf_i_pre_s; try eassumption; [unfold A; lia | exact PC].
Section CANSEC3. Context {rc : runConstT}.
Corollary fprintf_i_pre_usage : fprintf_i_pre_s_stmt FMT_USAGE 16.
Proof using Type. fis printf_common_usage_spec FMT_USAGE. Qed.
Corollary fprintf_i_pre_cantopen : fprintf_i_pre_s_stmt FMT_CANTOPEN 20.
Proof using Type. fis printf_common_cantopen_spec FMT_CANTOPEN. Qed.
Corollary fprintf_i_pre_readerr : fprintf_i_pre_s_stmt FMT_READERR 22.
Proof using Type. fis printf_common_readerr_spec FMT_READERR. Qed.
End CANSEC3.
