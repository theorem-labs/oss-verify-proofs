(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the walk of diginet_personality_of (src/diginet_codec.c:27-33) on the UBSan
   image, the leaf at 0x13dcc (14 words: 13 instructions walked, no call, no frame, and the unimp at 0x13e00),
   against lib/U/Prog/diginet_personality_of_c.v. Three paths: a0 = 1 returns 0x1d888 (0x13dd0 taken, 0x13dec-0x13df4),
   a0 = 2 returns 0x1d8a0 (0x13ddc-0x13de8), any other a0 returns 0 (0x13dd8 taken, 0x13df8-0x13dfc). The UBSan
   check 0x13de4 `beqz a0` (to the unimp at 0x13e00) tests the constant 0x1d8a0 that 0x13ddc-0x13de0 forms, so it is
   never taken. The function has no abort site. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout diginet_personality_of_c.
Open Scope Z_scope.

(* the model's result for each desk value the binary tests *)
Lemma personality_of_cases : forall d,
  diginet_personality_of d = if d =? 1 then Some 0 else if d =? 2 then Some 1 else None.
Proof.
  intros d. unfold diginet_personality_of, personalities, DIGINET_DESK_CONTROL24, DIGINET_DESK_PROCONTROL.
  cbn [personality_find dp_desk]. rewrite (Z.eqb_sym 1 d), (Z.eqb_sym 2 d). reflexivity.
Qed.

Theorem diginet_personality_of_holds : diginet_personality_of_contract.
Proof.
  unfold diginet_personality_of_contract, DIGINET_PERSONALITY_OF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  rewrite personality_of_cases.
  step. step. if_cases H1.
  - zify_cond H1. rewrite H1. cbn [Z.eqb Pos.eqb].
    step. step. step. apply evt_done. eexists. reflexivity.
  - zify_cond H1. rewrite (proj2 (Z.eqb_neq _ _) H1).
    step. step. if_cases H2.
    + zify_cond H2. rewrite (proj2 (Z.eqb_neq _ _) H2).
      step. step. apply evt_done. eexists. reflexivity.
    + zify_cond H2. rewrite H2. cbn [Z.eqb Pos.eqb].
      step. step. step. if_false. step. apply evt_done. eexists. reflexivity.
Qed.
