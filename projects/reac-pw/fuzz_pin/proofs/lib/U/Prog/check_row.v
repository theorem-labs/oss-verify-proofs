From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import check_row_c.
Import ListNotations.
Open Scope Z_scope.

(** check_row of the ubsan image (0x12ed8, 6 instructions: the plain code with a trailing unimp after the
    abort call), so the walk is the plain one (Prog/check_row.v): `bne a0, a1` to the abort call, else `ret`.
    The premise a0 = a1 makes the bne never taken. *)

Theorem check_row_holds : check_row_contract.
Proof.
  unfold check_row_contract, CHECK_ROW.
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
