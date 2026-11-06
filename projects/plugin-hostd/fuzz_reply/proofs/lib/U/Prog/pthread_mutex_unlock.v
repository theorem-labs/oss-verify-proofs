From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_unlock_c AmoStep.
Import ListNotations.
Open Scope Z_scope.

Theorem pthread_mutex_unlock_holds : pthread_mutex_unlock_contract.
Proof.
  unfold pthread_mutex_unlock_contract, PTHREAD_MUTEX_UNLOCK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A lo
    HA MX ST LO SEP MI.
  pose proof (rw_cells_bound _ _ _ _ MX) as BM. cbn [cells_size csize Nat.add] in BM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (A + 4, A + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  do 12 zstep.
  zstep. zstep. fold_x32.
  do 4 zstep.
  if_true.
  zstep. zstep.
  zstep.
  astep. fold_x32.
  zstep. if_false.
  astep.
  zstep. if_false.
  zstep. fold_x32. zstep. if_false.
  do 4 zstep.
  if_true.
  zstep. if_true.
  do 13 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.
