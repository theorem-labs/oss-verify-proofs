(* The epilogue of LLVMFuzzerTestOneInput in the ubsan image, 0x145e8-0x14624 (fuzz_transport.c:1217 `return 0;`):
   a0 = 0, the 13 saved registers back from sp + 0x88 .. sp + 0xe8 (llvm_out's cells CB 136 jlow :: llvm_saved),
   sp + 240, ret. Nothing is stored, so the memory and the footprint are those of the exit. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

Theorem llvm_exit_holds : llvm_exit_stmt.
Proof.
  unfold llvm_exit_stmt.
  intros regs0 m0 Sp lo F fc ms H.
  destruct H as (ra & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jlow &
                 -> & HSP & HLO & HSP2 & HMI & HMU & HWMO & HJL & HRW).
  pose proof (rw_cells_bound rsegs m Sp _ HRW) as [HB0 _].
  unfold llvm_saved in HRW. unfold LH_FRAME in *. unfold LH_OUT.
  step.                                        (* 0x145e8 mv a0, zero *)
  do 13 step.                                  (* 0x145ec .. 0x1461c ld ra, s0 .. s11 *)
  step.                                        (* 0x14620 addi sp, sp, 0xf0 *)
  step.                                        (* 0x14624 ret *)
  apply evt_done. cbv beta.
  do 15 eexists. split; [reflexivity|].
  split; [exact HMU | exact HWMO].
Qed.
