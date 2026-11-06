(* Case 4 of the ubsan LLVMFuzzerTestOneInput, 0x13a94 .. 0x13e94: the two bytes kb, ab of
   c.key = SPEC_KEY(fuzz_u8(in) % 9 + 1, fuzz_u8(in)) (fuzz_transport.c:1076), with the cursor's UBSan pointer checks
   (`addi s3, s3, 1; bgeu s1, s3`, never taken) and the empty-cursor arms 0x13c80 / 0x13ab0 (the byte is 0). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs.
Import ListNotations.
Open Scope Z_scope.

Lemma op4_bytes : forall data D regs0 m0 Sp lo ops c c1 before B1 F fc ms c1' kb c2' ab (Q : machine_state -> Prop),
  op4_s1 data D regs0 m0 Sp lo ops c c1 before B1 F fc ms ->
  fuzz_u8_m D c1 = (c1', kb) -> fuzz_u8_m D c1' = (c2', ab) ->
  (forall ms', op4_s2 data D regs0 m0 Sp lo ops c2' kb ab before B1 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo ops c c1 before B1 F fc ms c1' kb c2' ab Q H E1 E2 HK.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & j10 & jio & jhi &
                 -> & HOPS & HN & HC & HC1 & RQ & LJ & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  clear HSTK HMI HRO HWM HFN HMU HWMO HRW.
  unfold LH_K, LH_FRAME in *.
  unfold llvm_cursor in HC.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  rewrite (fu8_nz D c HN) in HC1. cbn [fst] in HC1. subst c1.
  cbn [fi_off fi_n] in E1 |- *.
  destruct (Z.eqb_spec (fi_n c) 1) as [N1|N1].
  - (* the cursor is empty after the op byte: 0x13a94 beqz s6 taken; 0x13c80-0x13c8c a0 = a1 = a2 = 0 *)
    rewrite fu8_z in E1 by (cbn [fi_n]; lia). injection E1 as <- <-.
    rewrite fu8_z in E2 by (cbn [fi_n]; lia). injection E2 as <- <-.
    zstep. br. do 4 zstep.
    apply HK. unfold op4_s2. cbn [fi_off fi_n].
    replace (fi_n c - 1) with 0 by lia.
    do 16 eexists. exists m, j10, jio, jhi.
    split; [reflexivity|].
    split; [exact HOPS|]. split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
    split; [lia|]. split; [lia|]. split; [exact RQ|]. split; [exact LJ|]. exact HM0.
  - (* the byte kb is read at 0x13aa0 *)
    rewrite fu8_nz in E1 by (cbn [fi_n]; lia). cbn [fi_off fi_n] in E1. injection E1 as <- <-.
    pose proof (op4_read1 m data D (fi_off c + 1) HD ltac:(lia) ltac:(lia)) as HR1.
    (* 0x13a94 beqz s6 (not taken); 0x13a98 addi s3; 0x13a9c bgeu s1, s3 (trap, not taken); 0x13aa0 lbu a1, 1(s5);
       0x13aa4 addi s3, s5, 2; 0x13aa8 li a0, 2; 0x13aac bne s7, a0 *)
    zstep. br. do 2 zstep. br. do 4 zstep.
    destruct (Z.eqb_spec (fi_n c) 2) as [N2|N2].
    + (* ab = 0: 0x13ab0 mv a0, zero; 0x13ab4 j 0x13c88; 0x13c88 mv a2, zero; 0x13c8c j 0x13e94 *)
      rewrite fu8_z in E2 by (cbn [fi_n]; lia). injection E2 as <- <-.
      br. do 4 zstep.
      apply HK. unfold op4_s2. cbn [fi_off fi_n].
      replace (fi_n c - 1 - 1) with 0 by lia.
      replace (data + (fi_off c + 1 + 1)) with (data + fi_off c + 2) by lia.
      do 16 eexists. exists m, j10, jio, jhi.
      split; [reflexivity|].
      split; [exact HOPS|]. split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
      split; [apply at8_range|]. split; [lia|]. split; [exact RQ|]. split; [exact LJ|]. exact HM0.
    + (* ab is read at 0x13e88 *)
      rewrite fu8_nz in E2 by (cbn [fi_n]; lia). cbn [fi_off fi_n] in E2. injection E2 as <- <-.
      pose proof (op4_read1 m data D (fi_off c + 2) HD ltac:(lia) ltac:(lia)) as HR2.
      (* 0x13e80 addi s3, s3, 1; 0x13e84 bgeu (trap); 0x13e88 lbu a2, 2(s5); 0x13e8c addi a0, s7, -3;
         0x13e90 addi s3, s5, 3 *)
      br. do 2 zstep. br. do 3 zstep.
      apply HK. unfold op4_s2. cbn [fi_off fi_n].
      replace (data + (fi_off c + 1 + 1 + 1)) with (data + fi_off c + 3) by lia.
      replace (fi_n c - 1 - 1 - 1) with (fi_n c + -3) by lia.
      replace (Z.to_nat (fi_off c + 1 + 1)) with (Z.to_nat (fi_off c + 2)) by (f_equal; lia).
      do 16 eexists. exists m, j10, jio, jhi.
      split; [reflexivity|].
      split; [exact HOPS|]. split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
      split; [apply at8_range|]. split; [apply at8_range|]. split; [exact RQ|]. split; [exact LJ|]. exact HM0.
Qed.
