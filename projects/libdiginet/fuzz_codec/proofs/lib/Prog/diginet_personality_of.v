(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_personality_of.v, with its module paths and module names changed; 9 of its 36 lines of code are new or changed and 5 lines of the source are left out. *)
(* Walk of diginet_personality_of in fuzz_codec.plain (0x152c4): desk 1 returns at the beq (0x152d4)
   with a0 = &personalities[0]; otherwise snez / addi -1 / and select &personalities[1] for desk 2 and
   0 for any other desk.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells diginet_personality_of_c.
Import ListNotations.
Open Scope Z_scope.

Theorem diginet_personality_of_holds : diginet_personality_of_contract.
Proof.
  unfold diginet_personality_of_contract, DIGINET_PERSONALITY_OF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  (* the walk reads a0 as Z_to_bv 64 desk, desk its unsigned value *)
  pose proof (bv_unsigned_in_range 64 a0) as HD. unfold bv_modulus in HD.
  replace (2 ^ Z.of_N 64) with 18446744073709551616 in HD by reflexivity.
  set (desk := bv_unsigned a0) in *.
  assert (Ea : a0 = Z_to_bv 64 desk) by (symmetry; apply Z_to_bv_bv_unsigned).
  clearbody desk. subst a0.
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
      assert (P : pers_of desk = 0).
      { unfold pers_of. rewrite (proj2 (Z.eqb_neq desk 1)) by lia. rewrite (proj2 (Z.eqb_neq desk 2)) by lia.
        reflexivity. }
      do 6 step. rewrite V, P. apply evt_done. do 2 eexists. reflexivity.
Qed.
