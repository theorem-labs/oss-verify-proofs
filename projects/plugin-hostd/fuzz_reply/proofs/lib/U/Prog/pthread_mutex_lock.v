From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c AmoStep.
Import ListNotations.
Open Scope Z_scope.

Theorem pthread_mutex_lock_holds : pthread_mutex_lock_contract.
Proof.
  unfold pthread_mutex_lock_contract, PTHREAD_MUTEX_LOCK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A tb
    HA TB HTB LK MI.
  pose proof (bytes_at_bound _ _ _ _ TB) as BT. cbn [length] in BT.
  pose proof (rw_cells_bound _ _ _ _ LK) as BL. cbn [cells_size csize Nat.add] in BL.
  pose proof (munch_refl [(A + 4, A + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (RD : ov_read_bytes rsegs m (wa A) 1 = Some [tb]).
  { replace (wa A) with (wa (A + 0)) by (f_equal; lia).
    rewrite (bytes_at_read rsegs m A [tb] 0 1 TB ltac:(lia)) by (cbn; lia). reflexivity. }
  assert (L15 : Z.land (bv_unsigned tb) 15 = 0).
  { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact HTB. }
  zstep. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia | ].
  zstep. zstep.
  astep.
  rewrite L15. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  zstep. if_false.
  astep.
  zstep. if_cases K3; zify_cond K3; [exfalso; lia | ].
  zstep. zstep. if_cases K4; zify_cond K4; [ | exfalso; lia].
  zstep. zstep.
  finish.
Qed.
