From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import check_no_overrun_c.
Import ListNotations.
Open Scope Z_scope.

(** check_no_overrun of the plain image (0x14680, 12 instructions), walked with Lib/Tac.v and Lib/Step.v:
    three `lbu` of the guard bytes at a0, a0 + 1, a0 + 2, each compared (`bne`) with 0xa5 (the abort frame at
    0x146a4), else `ret`. The premise (the three bytes are GUARD_BYTE = 0xa5) makes no branch taken. *)

Theorem check_no_overrun_holds : check_no_overrun_contract.
Proof.
  unfold check_no_overrun_contract, CHECK_NO_OVERRUN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m HG.
  pose proof (bytes_at_read rsegs m (bv_unsigned a0) _ 0 1 HG ltac:(lia) ltac:(cbn; lia)) as R0.
  pose proof (bytes_at_read rsegs m (bv_unsigned a0) _ 1 1 HG ltac:(lia) ltac:(cbn; lia)) as R1.
  pose proof (bytes_at_read rsegs m (bv_unsigned a0) _ 2 1 HG ltac:(lia) ltac:(cbn; lia)) as R2.
  change (firstn 1 (skipn (Z.to_nat 0) (repeat GUARD_BYTE 3))) with [Z_to_bv 8 0xa5] in R0.
  change (firstn 1 (skipn (Z.to_nat 1) (repeat GUARD_BYTE 3))) with [Z_to_bv 8 0xa5] in R1.
  change (firstn 1 (skipn (Z.to_nat 2) (repeat GUARD_BYTE 3))) with [Z_to_bv 8 0xa5] in R2.
  (* the first load's address is a0 itself *)
  rewrite (wa_of_var a0 (bv_unsigned a0 + 0)) in R0 by lia.
  (* lbu a2, 0(a0); addi a1, zero, 0xa5 *)
  zstep. zstep.
  (* bne a2, a1: not taken *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
  (* lbu a2, 1(a0); bne a2, a1: not taken *)
  zstep. zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
  (* lbu a0, 2(a0); addi a1, zero, 0xa5; bne a0, a1: not taken; then ret *)
  zstep. zstep. zstep.
  let K := fresh "K" in
  if_cases K;
    first [ exfalso; zify_cond K; lia
          | zstep; finish ].
Qed.
