From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
Open Scope Z_scope.

Theorem check_shape_done_holds : check_shape_done_contract.
Proof.
  unfold check_shape_done_contract, CHECK_SHAPE_DONE, G_NOUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HN.
  assert (RD : ov_read_bytes rsegs m (wa 0x318e0) 8 = Some (le8 a0)).
  { replace (wa 0x318e0) with (wa (0x318e0 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x318e0 (le8 a0) 0 8 HN ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  step. step. step. if_false. step.
  apply evt_done. eexists. reflexivity.
Qed.
