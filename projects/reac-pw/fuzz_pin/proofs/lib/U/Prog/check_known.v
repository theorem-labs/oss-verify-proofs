From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import check_known_c.
Import ListNotations.
Open Scope Z_scope.

(** check_known of the ubsan image (0x12eb8, 8 instructions: the plain code with a trailing unimp after the
    abort call), so the walk is the plain one (Prog/check_known.v): `seqz a0, a0; seqz a1, a1; beq a0, a1` to
    the abort call, else `ret`. The premise says exactly one of a0, a1 is zero, so the two seqz results differ
    and the beq is never taken. *)

Theorem check_known_holds : check_known_contract.
Proof.
  unfold check_known_contract, CHECK_KNOWN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m [HA0 HA1].
  pose proof (u64_range a0) as R0. pose proof (u64_range a1) as R1.
  (* seqz a0, a0; seqz a1, a1 *)
  zstep. zstep.
  (* beq a0, a1: taken only when (a0 = 0) <-> (a1 = 0), which the premise refutes *)
  zstep.
  let K := fresh "K" in
  if_cases K;
    first [ exfalso; zify_cond K; revert K;
            do 2 (match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end);
            cbn; lia
          | zstep; finish ].
Qed.
