(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Walk of diginet_personality_of in fuzz_decode.plain (0x13cc0): desk 1 returns at the beq (0x13cd0)
   with a0 = &personalities[0]; otherwise snez / addi -1 / and select &personalities[1] for desk 2 and
   0 for any other desk.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_personality_of_c.
Import ListNotations.
Open Scope Z_scope.

Theorem diginet_personality_of_holds : diginet_personality_of_contract.
Proof.
  unfold diginet_personality_of_contract, DIGINET_PERSONALITY_OF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m desk HD.
  do 5 step.
  if_cases HB.
  - zify_cond HB.
    assert (E : desk = 1) by (Z.div_mod_to_equations; lia). subst desk.
    step. apply evt_done. do 2 eexists. reflexivity.
  - zify_cond HB.
    assert (N1 : desk <> 1) by (intro; subst; apply HB; reflexivity).
    destruct (Z.eq_dec desk 2) as [E2|N2].
    + subst desk. do 6 step. apply evt_done. do 2 eexists. reflexivity.
    + assert (V : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (desk + -2)) = Z_to_bv 64 1).
      { unfold v_sltu, c_ltu, bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
        replace (0 mod 2 ^ Z.of_N 64) with 0 by reflexivity.
        destruct (Z.ltb_spec 0 ((desk + -2) mod 2 ^ Z.of_N 64)) as [L|L]; [reflexivity|].
        exfalso. Z.div_mod_to_equations. lia. }
      assert (P : personality_ptr (diginet_personality_of desk) = 0).
      { unfold diginet_personality_of, personality_find, personalities, DIGINET_DESK_CONTROL24,
          DIGINET_DESK_PROCONTROL; cbn [dp_desk].
        rewrite (proj2 (Z.eqb_neq 1 desk)) by lia. rewrite (proj2 (Z.eqb_neq 2 desk)) by lia. reflexivity. }
      do 6 step. rewrite V, P. apply evt_done. do 2 eexists. reflexivity.
Qed.
