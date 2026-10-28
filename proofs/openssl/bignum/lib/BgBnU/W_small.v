(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnModel BnMInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition bn_small_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (lo : Z) (m : word -> option byte) (R : word -> (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ munch W m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ stk bgusegs m' lo (bv_unsigned sp) /\ R a0' m'.

Lemma BN_set_negative_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0)%Z -> (Z.of_nat (bn_top b) < 2^31)%Z ->
  stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells bgusegs m' A (bn_cells D (bn_with_neg b (negb (bv_unsigned a1 =? 0)%Z && negb (bn_top b =? 0)%nat)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xff4b8) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] TOP ST LO MI SEP ->.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN _]; apply cells_at_bound in BN; cbn in BN; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  step. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    step. rewrite (land7_wrap _ PM).
    step.
    chk ltac:(fun C => clear - C PA AB; lia).
    chk ltac:(fun C => clear - C; lia).
    step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
    rewrite K. cbn [Z.eqb negb andb Z.b2z]. exact BN.
  - (* [comment removed for export] *)
    chk ltac:(fun C => clear - C PA AB; lia).
    step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
    step.
    step. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      chk ltac:(fun C => clear - C PA AB; lia).
      chk ltac:(fun C => clear - C; lia).
      step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
      finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
      replace (bn_top b =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
      rewrite andb_false_r. exact BN.
    + step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
      finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
      replace (bn_top b =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (bv_unsigned a1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K).
      exact BN.
Qed.
