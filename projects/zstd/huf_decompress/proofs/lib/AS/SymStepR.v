(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (23 recorded proofs replaced by written proofs (mkstR_None, mkstR_svc, stepR_opimm_gen and 20 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec SeqExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SymStepR () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib2AS8SymStepR>asanreflect_fxC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr08K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem5is_x0C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv3Sem7reg_getC59OSSVerify5KrLib2AS8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC59OSSVerify5KrLib2AS8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepc59OSSVerify5KrLib2AS8SymStepR5mkstRC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5instr09C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr0;C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0BC4ELinuxProcessSemantics5Riscv3Sem7mul_divI4ELinuxProcessSemantics5Riscv5Instr5mulop00K4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr01C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib2AS8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib2AS8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib2AS8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib2AS8PropExec4btgtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C59OSSVerify5KrLib2AS7SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC59OSSVerify5KrLib2AS8PropExec9jalr_tgtZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8jalr_tgtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6b_jalrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andK4ELinuxProcessSemantics5Riscv5Instr5instr05C47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv3Sem<branch_takenK47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?c59OSSVerify5KrLib2AS8SymStepR;load_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff07C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib2AS8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8SymStepR;msize_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_extractK47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv5Instr5msize00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5instr07C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6NArith6BinNat1N2leC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions?bv_wrap_bv_wrapC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC35stdpp7tactics<f_equal_helpC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib2AS8SymStepR<resv_inval_wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK4ELinuxProcessSemantics5Riscv3Sem3eff08C59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExecAstore_bytes_low16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExecAstore_bytes_low32C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z6inj_leI47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K4ELinuxProcessSemantics5Riscv5Instr5instr0DC4ELinuxProcessSemantics5Riscv3Sem9amo_bytesC56Stdlib6ZArith6BinInt1Z6moduloc59OSSVerify5KrLib2AS8SymStepR:amo_nbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8SymStepR9amo_msizeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv3Sem3eff06I4ELinuxProcessSemantics5Riscv5Instr6awidth00K4ELinuxProcessSemantics5Riscv5Instr6awidth01K4ELinuxProcessSemantics5Riscv5Instr6awidth02K4ELinuxProcessSemantics5Riscv5Instr5instr0EC56Stdlib6ZArith6BinInt1Z8eqb_reflK4ELinuxProcessSemantics5Riscv5Instr5instr0Fc59OSSVerify5KrLib2AS8SymStepR?amo_store_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7amo_valI4ELinuxProcessSemantics5Riscv5Instr5amoop00".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition mkstR (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (rv : option word)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := rv; ms_fcsr := Z_to_bv 32 0;
     ms_mem := mem; ms_rom := rom |}.

Lemma mkstR_None : forall regs pc mem rom, mkstR regs pc mem rom None = mkst regs pc mem rom.
Proof. reflexivity. Qed.

Lemma mkstR_svc : forall regs pc mem rom rv, ms_svc_pending (mkstR regs pc mem rom rv) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition resv_inval_w (rv : option word) (a : word) : option word :=
  match rv with
  | Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else rv
  | None => None
  end.

(* [comment removed for export] *)
Definition load_result (sz : msize) (sx : bool) (bs : list byte) : word :=
  match sz with
  | SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
  | SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
  | SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
  end.

Definition eff_sx (sz : msize) (sx : bool) : bool :=
  match sz with SZ8 => false | _ => sx end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition amo_msize (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition amo_nbytes (wd : awidth) : nat := match wd with AW => 4%nat | AD => 8%nat end.

(* [comment removed for export] *)
Definition amo_store_bytes (op : amoop) (wd : awidth) (bs : list byte) (src : word) : list byte :=
  match wd with
  | AW => Z_to_le_bytes 4 (bv_unsigned (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 src)))
  | AD => Z_to_le_bytes 8 (bv_unsigned (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) src))
  end.

Ltac stepR_pipeline Hfetch Hecall Hdecode :=
  unfold mkstR;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stepR_opimm_gen : forall segs regs pc mem rom rv w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_opimm32_gen : forall segs regs pc mem rom rv w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm32_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_lui : forall segs regs pc mem rom rv w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma stepR_auipc : forall segs regs pc mem rom rv w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma stepR_jal_link : forall segs regs pc mem rom rv w rd (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                   (btgt pc (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

Lemma stepR_jalr : forall segs regs pc mem rom rv w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                   (v_jalr (getr regs rs1) (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs1 imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd, v_jalr.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_jalr; reflexivity.
Qed.

Lemma stepR_branch_tk_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (btgt pc (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma stepR_branch_ft_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

Lemma stepR_fence : forall segs regs pc mem rom rv w a b c d e,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w a b c d e Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Lemma stepR_fencei : forall segs regs pc mem rom rv w a b c,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI a b c, 4%Z) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w a b c Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stepR_load : forall segs regs pc mem rom rv w sz sx rd rs (imm : bv 12) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w sz sx rd rs imm bs Hfetch Hecall Hdecode Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
    rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4;
    destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_store : forall segs regs pc mem rom rv w sz (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) (msize_bytes sz) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes (msize_bytes sz) (getr regs rs2))) rom
    (resv_inval_w rv (v_addi (getr regs rs1) (bv_signed imm)))).
Proof.
  intros segs regs pc mem rom rv w sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite !b_addsext.
  destruct sz; cbn [msize_bytes] in Hok |- *; cbv beta iota delta [store_val];
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?Hsb, ?store_bytes_low16, ?store_bytes_low32, b_npc4;
    (destruct rv as [r|]; cbv beta iota; [|reflexivity]);
    unfold resv_inval_w;
    match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y); cbv beta iota; reflexivity end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepR_lr : forall segs regs pc mem rom rv w wd aq rl rd rs bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr wd aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod amo_bytes wd = 0)%Z ->
  rdn segs mem (getr regs rs) (amo_nbytes wd) = Some bs ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
                   (v_addi pc 4) mem rom (Some (getr regs rs))).
Proof.
  intros segs regs pc mem rom rv w wd aq rl rd rs bs Hfetch Hecall Hdecode Hal Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite b_npc4; unfold regupd;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_sc_ok : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom (Some r)) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                   (wbytes mem (getr regs rs1) (word_to_le_bytes (amo_nbytes wd) (getr regs rs2))) rom None).
Proof.
  intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    subst r; rewrite Z.eqb_refl; cbv beta iota;
    cbn [amo_nbytes] in Hok |- *; rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?store_bytes_low32, b_npc4;
    unfold regupd, word_to_le_bytes;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_amo : forall segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  rdn segs mem (getr regs rs1) (amo_nbytes wd) = Some bs ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
                   (v_addi pc 4)
                   (wbytes mem (getr regs rs1) (amo_store_bytes op wd bs (getr regs rs2)))
                   rom (resv_inval_w rv (getr regs rs1))).
Proof.
  intros segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread, Hok |- *; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, b_npc4; unfold regupd, amo_store_bytes;
    (destruct rv as [r|]; cbv beta iota);
    unfold resv_inval_w;
    try match goal with |- context [Z.eqb (bv_unsigned r) ?y] =>
          destruct (Z.eqb (bv_unsigned r) y); cbv beta iota end;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
