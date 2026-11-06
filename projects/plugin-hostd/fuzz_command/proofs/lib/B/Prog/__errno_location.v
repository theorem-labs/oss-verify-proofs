From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import __errno_location_c.
Open Scope Z_scope.

Theorem __errno_location_holds : __errno_location_contract.
Proof.
  unfold __errno_location_contract, ERRNO_LOCATION, ERRNO_TP_OFF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. step. step.
  apply evt_done. reflexivity.
Qed.
