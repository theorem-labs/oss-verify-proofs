From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import check_absent_c.
Import ListNotations.
Open Scope Z_scope.

(** check_absent of the UBSan image (0x14224, 8 instructions), walked with Lib/Tac.v and Lib/Step.v: `bnez a0`,
    `addi a0, zero, 0x5a`, `bne a1, a0` (both branches go to the abort frame at 0x14234), else `ret`. The premises
    a0 = 0 and a1 = 0x5a make neither branch taken. *)

Theorem check_absent_holds : check_absent_contract.
Proof.
  unfold check_absent_contract, CHECK_ABSENT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m HA0 HA1.
  (* bnez a0: not taken, a0 = 0 *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
  (* addi a0, zero, 0x5a *)
  zstep.
  (* bne a1, a0: not taken, a1 = 0x5a; then ret *)
  zstep.
  let K := fresh "K" in
  if_cases K;
    first [ exfalso; zify_cond K; lia
          | zstep; finish ].
Qed.
