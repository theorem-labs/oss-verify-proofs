(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/U/Prog/diginet_personality_of.v, with its module paths and module names changed; 1 of its 22 lines of code is new or changed and 7 lines of the source are left out. *)
(* New for libdiginet/fuzz_decode: the walk of diginet_personality_of (src/diginet_codec.c:27-33) on the UBSan
   image, the leaf at 0x15678 (14 words: 13 instructions walked, no call, no frame, and the unimp at 0x156ac),
   against lib/U/Prog/diginet_personality_of_c.v. Three paths: a0 = 1 returns 0x1f880 (0x1567c taken, 0x15698-0x156a0),
   a0 = 2 returns 0x1f898 (0x15688-0x15694), any other a0 returns 0 (0x15684 taken, 0x156a4-0x156a8). The UBSan
   check 0x15690 `beqz a0` (to the unimp at 0x156ac) tests the constant 0x1f898 that 0x15688-0x1568c forms, so it is
   never taken. The function has no abort site. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_personality_of_c.
Open Scope Z_scope.

Theorem diginet_personality_of_holds : diginet_personality_of_contract.
Proof.
  unfold diginet_personality_of_contract, DIGINET_PERSONALITY_OF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  unfold pers_of.
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
