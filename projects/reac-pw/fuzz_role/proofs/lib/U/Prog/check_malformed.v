From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import check_malformed_c.
Import ListNotations.
Open Scope Z_scope.

(** check_malformed of the UBSan image (0x14264, 9 instructions), walked with Lib/Tac.v and Lib/Step.v:
    `addi a2, zero, -1`, `bne a0, a2`, `addi a0, zero, 0x5a`, `bne a1, a0` (both branches go to the abort frame at
    0x14278), else `ret`. The premises a0 = 2^64 - 1 and a1 = 0x5a make neither branch taken. *)

Theorem check_malformed_holds : check_malformed_contract.
Proof.
  unfold check_malformed_contract, CHECK_MALFORMED.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m HA0 HA1.
  assert (HA0' : bv_unsigned a0 = 18446744073709551615) by (rewrite HA0; reflexivity).
  clear HA0.
  (* addi a2, zero, -1 *)
  zstep.
  (* bne a0, a2: not taken, a0 is all ones *)
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
