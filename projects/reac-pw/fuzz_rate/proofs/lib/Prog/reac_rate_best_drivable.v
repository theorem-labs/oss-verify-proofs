From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import reac_rate_best_drivable_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_best_drivable of the plain image (0x14a38, 16 instructions), walked with Lib/Tac.v and Lib/Step.v. The
    walk splits on bits 2, 1 and 0 of a0, the order of rate_best. `andi a1, a0, 4; bnez a1` and
    `andi a1, a0, 2; bnez a1` are decided by [testbit_land_pow] (Pod/RateCfg.v) and return 96000 or 48000 built by
    `lui; addiw`. Else `slli a0, a0, 63` leaves bit 0 alone at bit 63 ([shl63_w] rewrites it to the literal 2^63 or
    0), `srai a0, a0, 63` spreads it, and the `and` with 44100 gives 44100 or 0. *)

(** A branch the context contradicts: every compare here is of a0 or a literal, so lia decides it. *)
Ltac kill K := exfalso; zify_cond K; lia.

(** Step to the `ret`, deciding each branch from the context. *)
Ltac walk :=
  repeat first [ let K := fresh "K" in if_cases K; [ first [ kill K | idtac ] .. ]
               | zstep ].

Lemma testbit0_mod2 : forall x, Z.testbit x 0 = (x mod 2 =? 1).
Proof. intros x. rewrite Z.bit0_odd. apply Zodd_mod. Qed.

(** A shift left by 63 keeps only bit 0, at bit 63. *)
Lemma shl63 : forall x, 0 <= x -> (Z.shiftl x 63) mod 2^64 = (if Z.testbit x 0 then 2^63 else 0) mod 2^64.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite testbit0_mod2.
  pose proof (Z.div_mod x 2 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 2 ltac:(lia)) as B.
  set (q := x / 2) in *. set (r := x mod 2) in *. clearbody q r.
  rewrite D.
  replace ((2 * q + r) * 2^63) with (r * 2^63 + q * 2^64) by (change (2^64) with (2 * 2^63); ring).
  rewrite Z.mod_add by lia.
  destruct (Z.eqb_spec r 1) as [->|N]; [reflexivity|].
  assert (r = 0) by lia. subst r. reflexivity.
Qed.

Lemma shl63_w : forall x : word,
  Z_to_bv 64 (Z.shiftl (bv_unsigned x) 63) = Z_to_bv 64 (if Z.testbit (bv_unsigned x) 0 then 2^63 else 0).
Proof. intros x. apply Z_to_bv_eqm. apply shl63. apply (proj1 (zr_word x)). Qed.

Theorem reac_rate_best_drivable_holds : reac_rate_best_drivable_contract.
Proof.
  unfold reac_rate_best_drivable_contract, REAC_RATE_BEST_DRIVABLE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m.
  pose proof (zr_word a0) as R0. unfold inr64 in R0.
  pose proof (testbit_land_pow (bv_unsigned a0) 2 ltac:(lia)) as L2. change (2 ^ 2) with 4 in L2.
  pose proof (testbit_land_pow (bv_unsigned a0) 1 ltac:(lia)) as L1. change (2 ^ 1) with 2 in L1.
  unfold rate_best, RATE_96K, RATE_48K, RATE_44K1.
  destruct (Z.testbit (bv_unsigned a0) 2) eqn:T2; cbn [negb] in L2.
  - (* bit 2: 96000 *)
    apply Z.eqb_neq in L2. walk. finish.
  - apply Z.eqb_eq in L2.
    destruct (Z.testbit (bv_unsigned a0) 1) eqn:T1; cbn [negb] in L1.
    + (* bit 1: 48000 *)
      apply Z.eqb_neq in L1. walk. finish.
    + apply Z.eqb_eq in L1.
      (* andi a1, a0, 4; bnez a1; andi a1, a0, 2; bnez a1: neither taken; slli, lui, srai, addiw, and, ret *)
      walk.
      (* the register holds the and of 44100 with srai (slli a0 63) 63: bit 0 decides it *)
      rewrite shl63_w.
      destruct (Z.testbit (bv_unsigned a0) 0); finish.
Qed.
