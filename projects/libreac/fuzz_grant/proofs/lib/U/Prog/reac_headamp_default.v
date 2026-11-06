From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel reac_headamp_default_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_headamp_default_holds : reac_headamp_default_contract.
Proof.
  unfold reac_headamp_default_contract, REAC_HEADAMP_DEFAULT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p -> HP.
  change (2^64) with 18446744073709551616 in HP.
  zstep. zstep. zstep. zstep.
  rewrite <- dflt_code_all by lia.
  finish.
Qed.
