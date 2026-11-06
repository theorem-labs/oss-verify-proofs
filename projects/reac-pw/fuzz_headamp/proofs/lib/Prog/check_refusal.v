From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import check_refusal_c.
Import ListNotations.
Open Scope Z_scope.

(** check_refusal of the plain image (0x147fc, 7 instructions), walked with Lib/Tac.v and Lib/Step.v:
    `lw a0, 8(a0)` and `lw a1, 0x84(a1)` read the same four bytes w (the premises), so the two loaded words are one
    term and `bne a0, a1` (to the abort frame at 0x1480c) is not taken; then `ret`. *)

Theorem check_refusal_holds : check_refusal_contract.
Proof.
  unfold check_refusal_contract, CHECK_REFUSAL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m w HL HR HX.
  unfold X_RF_OFF in HX.
  pose proof (bytes_at_ov_read rsegs m _ w 0 4 HR ltac:(lia)) as R0.
  pose proof (bytes_at_ov_read rsegs m _ w 0 4 HX ltac:(lia)) as R1.
  change (Z.of_nat 0) with 0 in R0, R1. change (skipn 0 w) with w in R0, R1.
  rewrite Z.add_0_r in R0, R1. rewrite firstn_all2 in R0, R1 by lia.
  (* lw a0, 8(a0); lw a1, 0x84(a1) *)
  step. step.
  (* bne a0, a1: not taken (the same word); then ret *)
  step.
  let K := fresh "K" in
  if_cases K;
    first [ exfalso; zify_cond K; lia
          | zstep; finish ].
Qed.
