(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (maybe_release_spec); the recorded proofs name the unit's interp_eff_accesses and stepF shims, proved equal to the model's). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ARep F_apoison F_ammap F_aensure.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AKit AKit2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_amaybe () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib5BothW9F_aensure8m3_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8F_amaybe:maybe_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_apoison<poison_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7F_ammap:rmap_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF=rng_acc_litZ'C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK47Corelib4Init5Logic3and01K4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC59OSSVerify5KrLib3Lib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5m_mulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib3Lib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_sllC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_sllC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_sraiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_sraiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib3Lib8PropExec5v_andC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_andC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:zr_mod_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem4execC59OSSVerify5KrLib3Lib6MStateKinterp_eff_accesses_nv_shimC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_gnvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics5Riscv3Sem7mul_divC59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8F_amaybe;maybe_entryC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I47Corelib4Init5Logic4True00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop0:".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation MAYBE_STACK := 80 (only parsing).
Section CANSEC1. Context {rc : runConstT}.
Definition maybe_entry : Z := 0x346e4.

Definition maybe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - MAYBE_STACK, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma maybe_release_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c lo nf mfa au mu : Z) (w80 w88 : word),
  let RI := aregion_info L c in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MAYBE_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 0 ->
  m3_cells L m ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 80) [C8 w80] -> rw_cells bsegs m (RI + 88) [C8 w88] ->
  1 <= c < K_NUM_CLASSES ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 ->
  evtF bsegs RNG (maybe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 maybe_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until w88. cbv zeta.
  intros ST CEIL LO MI -> -> -> MC REG R80 R88 HC SP1 SP2 RIMG RSTK RRI.
  pose proof MC as MC0. destruct MC0 as (_ & RC & _ & _ & _ & _ & _ & ISB & IREL & ISE & IPRE).
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & _). clear MC RC ISB IPRE.
  unfold AINSTANCE, K_NUM_CLASSES, K_SPACE_SIZE, K_SPACE_EXTRA, maybe_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128)
    by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 80%nat ST.
  do 10 step.                                                  (* [comment removed for export] *)
  do 4 step.                                                   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac tail RIE SP1 SP2 HC :=
    step; step; step;                                          (* [comment removed for export] *)
    zstep;                                                     (* [comment removed for export] *)
    lazymatch type of RIE with ?ri = _ =>
      setreg 22%Z (Z_to_bv 64 ri) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia)
    end;
    step; if_lit;                                              (* [comment removed for export] *)
    step;                                                      (* [comment removed for export] *)
    zstep;                                                     (* [comment removed for export] *)
    step;
    let K1 := fresh "K" in
    if_cases K1;
    [ (* [comment removed for export] *)
      step; step; zstep; zstep;                                (* [comment removed for export] *)
      step;
      let K2 := fresh "K" in
      if_cases K2;
      [ do 11 step                                             (* [comment removed for export] *)
      | step; if_lit;                                          (* [comment removed for export] *)
        step;                                                  (* [comment removed for export] *)
        step; if_lit;                                          (* [comment removed for export] *)
        do 11 step ]
    | do 12 step ].                                            (* [comment removed for export] *)
  step. if_cases K31; zify_cond K31.
  - (* [comment removed for export] *)
    step. step.                                                (* [comment removed for export] *)
    tail RIE SP1 SP2 HC.
    all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
  - step.                                                      (* [comment removed for export] *)
    step. if_cases K16; zify_cond K16.
    + (* [comment removed for export] *)
      do 9 zstep.
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
    + zstep. step.                                             (* [comment removed for export] *)
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
Qed.
End CANSEC1.
