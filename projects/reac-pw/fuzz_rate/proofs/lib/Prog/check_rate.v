From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import check_rate_c.
Import ListNotations.
Open Scope Z_scope.

(** check_rate of the plain image (0x145c8, 7 instructions), walked with Lib/Tac.v and Lib/Step.v:
    `addi a3, zero, 1`, `bne a0, a3`, `bne a1, a2` (both branches go to the abort frame at 0x145d8), else `ret`.
    The premises a0 = 1 and a1 = a2 make neither branch taken. *)

Theorem check_rate_holds : check_rate_contract.
Proof.
  unfold check_rate_contract, CHECK_RATE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m HA0 HEQ.
  subst a2.
  (* addi a3, zero, 1 *)
  zstep.
  (* bne a0, a3: not taken, a0 = 1 *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
  (* bne a1, a1: never taken; then ret *)
  zstep.
  let K := fresh "K" in
  if_cases K;
    first [ exfalso; zify_cond K; lia
          | zstep; finish ].
Qed.
