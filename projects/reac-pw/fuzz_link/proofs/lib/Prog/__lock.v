From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel __lock_c.
Import ListNotations.
Open Scope Z_scope.

Theorem __lock_holds : __lock_contract.
Proof.
  unfold __lock_contract, LOCK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HB.
  replace (A_LIBC + 3) with 0x9589b in HB by reflexivity.
  assert (RD : ov_read_bytes rsegs m (wa 0x9589b) 1 = Some [Z_to_bv 8 0]).
  { replace (wa 0x9589b) with (wa (0x9589b + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x9589b [Z_to_bv 8 0] 0 1 HB ltac:(lia)) by (cbn; lia).
    reflexivity. }
  step. step. step. if_true. step.
  apply evt_done. eexists _, _. reflexivity.
Qed.
