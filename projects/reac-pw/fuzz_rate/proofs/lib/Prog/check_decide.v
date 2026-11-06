From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import check_decide_c.
Import ListNotations.
Open Scope Z_scope.

(** check_decide of the plain image (0x14608, 5 instructions), walked with the tactics of Lib/Tac.v and
    Lib/Step.v: `bne a0, a1` to the abort call, else `ret`. The premise a0 = a1 makes the bne never taken. *)

Theorem check_decide_holds : check_decide_contract.
Proof.
  unfold check_decide_contract, CHECK_DECIDE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m HEQ.
  subst a1.
  (* bne a0, a0 *)
  zstep.
  let K := fresh "K" in
  if_cases K;
    first [ exfalso; zify_cond K; lia
          | zstep; finish ].
Qed.
