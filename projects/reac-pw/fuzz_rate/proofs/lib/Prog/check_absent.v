From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import check_absent_c.
Import ListNotations.
Open Scope Z_scope.

(** check_absent of the plain image (0x145a8, 8 instructions), walked with Lib/Tac.v and Lib/Step.v (reac-pw/fuzz_role's
    walk, with one more instruction: rate's constant 0x5a5a5a5a is `lui a0, 0x5a5a6; addiw a0, a0, -0x5a6`, role's
    0x5a one `addi`): `bnez a0`, the constant, `bne a1, a0` (both branches go to the abort frame at 0x145bc), else
    `ret`. The premises a0 = 0 and a1 = 0x5a5a5a5a make neither branch taken. *)

Theorem check_absent_holds : check_absent_contract.
Proof.
  unfold check_absent_contract, CHECK_ABSENT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m HA0 HA1.
  (* bnez a0: not taken, a0 = 0 *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
  (* lui a0, 0x5a5a6; addiw a0, a0, -0x5a6 *)
  zstep. zstep.
  (* bne a1, a0: not taken, a1 = 0x5a5a5a5a; then ret *)
  zstep.
  let K := fresh "K" in
  if_cases K;
    first [ exfalso; zify_cond K; lia
          | zstep; finish ].
Qed.
