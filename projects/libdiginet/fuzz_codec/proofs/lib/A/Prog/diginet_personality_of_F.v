(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_personality_of.v, with its module paths and module names changed; 16 of its 41 lines of code are new or changed and 7 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proof of diginet_personality_of_contract_F (fuzz_decode.asan, image A) in the form of projects/libreac/fuzz_decode/proofs/lib/A/Prog/reac_upstream_channels_F.v, step for step with lib/Prog/diginet_personality_of.v (the plain walk) at this image's table address. *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/libdiginet/fuzz_decode/lib/A/Prog/diginet_personality_of_F.v (fuzz_decode.asan, image A, a code-identical twin) to fuzz_codec.asan, image A: entry 0x84888 and the personalities table 0x9d920, the image segments lib/A/AWalkFw0.v tfibsegs, module paths changed; the premise on desk widened from -2^31 <= desk < 2^31 to 0 <= desk < 2^64 (any 64-bit a0: the code compares the whole register with 1 and 2). *)
(* Proof of diginet_personality_of_contract_F (image A, entry 0x84888). desk 1 returns at the beq (0x84898) with
   a0 = PERSONALITIES_A; otherwise sltu / addi -1 / and select PERSONALITIES_A + 24 for desk 2 and 0 for any other
   desk. The code makes no data access, so no step needs an rng fact. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_personality_of_c diginet_personality_of_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Theorem diginet_personality_of_holds_F : diginet_personality_of_contract_F.
Proof.
  unfold diginet_personality_of_contract_F, DIGINET_PERSONALITY_OF.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m desk HD.
  do 5 step.
  if_cases HB.
  - zify_cond HB.
    assert (E : desk = 1) by (Z.div_mod_to_equations; lia). subst desk.
    step. apply evtF_done. do 2 eexists. reflexivity.
  - zify_cond HB.
    assert (N1 : desk <> 1) by (intro; subst; apply HB; reflexivity).
    destruct (Z.eq_dec desk 2) as [E2|N2].
    + subst desk. do 6 step. apply evtF_done. do 2 eexists. reflexivity.
    + assert (V : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (desk + -2)) = Z_to_bv 64 1).
      { unfold v_sltu, c_ltu, bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
        replace (0 mod 2 ^ Z.of_N 64) with 0 by reflexivity.
        destruct (Z.ltb_spec 0 ((desk + -2) mod 2 ^ Z.of_N 64)) as [L|L]; [reflexivity|].
        exfalso. Z.div_mod_to_equations. lia. }
      assert (P : personality_ptr_A (diginet_personality_of desk) = 0).
      { unfold diginet_personality_of, personality_find, personalities, DIGINET_DESK_CONTROL24,
          DIGINET_DESK_PROCONTROL; cbn [dp_desk].
        rewrite (proj2 (Z.eqb_neq 1 desk)) by lia. rewrite (proj2 (Z.eqb_neq 2 desk)) by lia. reflexivity. }
      do 6 step. rewrite V, P. apply evtF_done. do 2 eexists. reflexivity.
Qed.

(* The footprint form implies the image-A contract: take the footprint that allows every access. *)
Corollary diginet_personality_of_holds_of_F : diginet_personality_of_contract.
Proof.
  unfold diginet_personality_of_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m desk HD.
  apply (ExecF.evtF_evt tfibsegs RNG_all).
  exact (diginet_personality_of_holds_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6 F fc m desk HD).
Qed.
