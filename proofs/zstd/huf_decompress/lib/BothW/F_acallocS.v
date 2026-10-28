(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF StepF ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes AKit AKit2 AModelFacts APrimFacts ASecFacts ARep ARepKit ARepFrame
     F_ammap F_ammapz F_alarge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_acallocS () := "C5ARocqVerifyHarness?AgentSubmission4LibA8SysStepF?implF_from_evtFC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5implFC5ARocqVerifyHarness?AgentSubmission5BothW8F_alarge:large_specC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA6epostFC5ARocqVerifyHarness?AgentSubmission3Lib5ITree5ebindC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00I5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission5BothW8F_alarge;large_cellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4sclrC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4iclrC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<sec_map_sizeC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_leC5ARocqVerifyHarness?AgentSubmission4LibA6NodesA8at_nodeAC47Corelib4Init5Logic3notI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW8F_alarge:large_postI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node0:C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed9adec_mmapC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;needed_sizeC5ARocqVerifyHarness?AgentSubmission5BothW9ASecFacts9sec_factsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7rz_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<rounded_sizeC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK5ARocqVerifyHarness?AgentSubmission5BothW4AKit5boxed01I5ARocqVerifyHarness?AgentSubmission5BothW4AKit5boxed00C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeI47Corelib4Init5Logic3and00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z3powK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega5Psatz02C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast=munch_write_nC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8K4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr01C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiC56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK47Corelib4Init5Logic2or01K47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission5BothW8F_alargeAlarge_cells_frameC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame8shad_divK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame:fill_frameK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW6AProto5fp_bwC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7fill_atC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7junk_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA9rng_fp_leC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge<zb_lxor_onesC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5ITree5enodeK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvK46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast@rw_cells_frame_nK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast>u64arr_frame_nC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast;stk_write_nC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIK47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00C5ARocqVerifyHarness?AgentSubmission5BothW6AProto6fstepSC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1N01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9AINSTANCEC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_LOI47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_lit".
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac band_lin :=      
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation CALLOCS_STACK := 512 (only parsing).   

Section CANSEC1. Context {rc : runConstT}.
Lemma calloc_sec_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->      
  ra = Z_to_bv 64 0x31b54 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  
  rw_cells bsegs m 0xb6d08 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0xb6d18 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells bsegs m 0xb6d20 [CB 32 jstats] ->
  rw_cells bsegs m 0xb6d40 [CB 512 jbsl] ->
  rw_cells bsegs m 0xb6f40 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xb6f58 [CB 16 jglob] ->
  
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells bsegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      
  
  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0) ->
  
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x31b54) fc None m' (seg_rom bsegs))) ->
  
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS bsegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x31b54) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x35d48) fc None m (seg_rom bsegs)).
Proof.
intros until jslot. cbv zeta.
intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.
pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
unfold AIMG_HI, AREQMAX, AINSTANCE in *.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
box JSL.
iprefix.

carve_frame 48%nat ST.
do 7 step.
do 3 zstep.
replace (needed_size n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NSE RSR N; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
rewrite (Z.mod_small (needed_size n)) by (clear -NSE RSR N MSR MSB; lia). rewrite zb_lxor_ones by (clear -NSE RSR N MSR MSB; lia).
step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 NSE RSR MSR MSB N. lia. }
step. step. step. if_lit.
step. step. if_lit.
step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NSE RSR NB. lia. }
zstep. zstep. step. step.
step.
apply evtF_done.
lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (LC' : large_cells ctx t PA mm) by
(eapply (large_cells_frame ctx t PA m mm); [exact LC | exact MU | exact WM | exact CXI |];
apply Forall_cons; [cbn [fst snd]; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]);
assert (FROK' : forall a, FRESH a = true ->
ablk a (a + sec_map_size n) /\ (a + sec_map_size n <= t \/ t + 4096 <= a) /\ (a + sec_map_size n <= ctx \/ ctx + 4096 <= a)
/\ (a + sec_map_size n <= PA \/ PA + 8388608 <= a) /\ fill_at mm (shad a) (sec_map_size n / 8) 0) by
(intros a' Ha'; destruct (FROK a' Ha') as (Y1 & Y1' & Y2 & Y3 & Y4 & Y5); split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|]; split; [exact Y4|];
eapply fill_frame; [exact Y5 | exact MU | exact WM |]; intros _; cbn [disjoint_from]; split; [| exact I];
rewrite shad_div; unfold ASHOFF; clear -SPR CEIL LO Y1 Y1' MSB; Z.div_mod_to_equations; lia)
end.
clear LC FROK.
unbox JSL.
lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JSL' : nsec < nres -> rw_cells bsegs mm (PA + 8 * nsec) [CB 8 jslot]) by
(intros Hlt; specialize (JSL Hlt); box JSL; carry JSL MU WM ltac:(clear -SPR CEIL LO PA0 PA1 NSR NRB0 Hlt; lia); exact JSL) end.
clear JSL.
lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (large_spec RNG K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) end.
all: try lazymatch goal with
| |- implS _ _ _ _ _ => idtac
| |- forall x, _ => first [exact SHAPE2 | exact UNR3 | exact UNR | exact UNR2 | exact FROK' | exact JSL' | idtac]
| |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
| |- mem_inv _ _ => assumption
| |- large_cells _ _ _ _ => exact LC'
| |- u64arr _ _ _ _ => exact STATS
| |- rw_cells _ _ _ _ => assumption
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- @eq bool _ _ => exact PRIM
| |- @eq nat _ _ => exact LSJ
| |- _ \/ _ => assumption
| |- rng _ _ _ => first [assumption | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia]
| |- _ => first [assumption | rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); unfold AREQMAX; clear -SPR CEIL LO N PA0 PA1 PAL NSR NRM NRB0 CX0 CX1 T0 T1; lia]
end.
all: match goal with |- implS _ _ _ _ _ => idtac | |- forall x, _ => idtac | |- ?G => idtac "REM-LARGE" G end.
all: intros a' RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR HNS LP.
all: pose proof LP as LP0; destruct LP0 as (FPLE & BW & A0 & A1 & A2 & MUL & WML & MIL & STL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _); unfold AINSTANCE in A2, MUL.
all: pose proof (ablk_lin _ _ A1) as (AL1 & AL2 & AL3 & AL4); unfold AIMG_HI in AL1.
all: rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia).
all: rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
all: assert (SHB : 0 <= shad a' /\ shad a' + sec_map_size n / 8 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -A1 A2 MSB AL1 AL2 AL3; Z.div_mod_to_equations; lia).
all: xport FR MUL WML ltac:(unfold AINSTANCE; clear -SPR CEIL LO A0 A1 A2 T0 T1 PA0 PA1 NSR NRB0 NRB' MSB SHB AL1 AL2 AL3; lia).
all: apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
all: iprefix.
all: replace (ret_pc (Z_to_bv 64 0x35df0)) with (Z_to_bv 64 0x35df0 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
all: step; step; step; if_lit.
all: step.
all: step.
all: step.
all: step.
all: step.
all: step.
all: step.
all: step.
all: step.
all: release_frame FR STL (bv_unsigned sp).
all: replace (ret_pc (Z_to_bv 64 0x31b54)) with (Z_to_bv 64 0x31b54 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
all: apply evtF_done.
1: eapply (KONT1 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
2: eapply (KONT2 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
all: lazymatch type of MU with munch _ _ ?mm => exists mm end.
all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
all: split; [exact MU|]; split; [exact WM| exact LP].
Qed.
End CANSEC1.
