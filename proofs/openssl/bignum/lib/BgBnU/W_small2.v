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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep W_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition BN_IS_ZERO : Z := 0xfde2c.
Definition BN_IS_NEGATIVE : Z := 0xffb98.
Definition BN_ZERO_EX : Z := 0xff920.
Definition BN_INIT : Z := 0xfe050.

(* [comment removed for export] *)
Lemma BN_is_zero_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0)%Z -> (Z.of_nat (bn_top b) < 2^31)%Z ->
  stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (bn_top b =? 0)%nat)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_ZERO) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] TOP ST LO MI SEP ->. unfold BN_IS_ZERO.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN _]; apply cells_at_bound in BN; cbn in BN; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z. do 2 f_equal.
  destruct (Nat.eqb_spec (bn_top b) 0) as [E|E]; [rewrite E; reflexivity| apply Z.ltb_ge; lia].
Qed.

(* [comment removed for export] *)
Lemma BN_is_negative_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0)%Z ->
  stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (bn_neg b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_NEGATIVE) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] ST LO MI SEP ->. unfold BN_IS_NEGATIVE.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN _]; apply cells_at_bound in BN; cbn in BN; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (sx32_small (Z.b2z (bn_neg b))) by (destruct (bn_neg b); cbn; lia).
  step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish. destruct (bn_neg b); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma BN_zero_ex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0)%Z ->
  stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells bgusegs m' A (bn_cells D (bn_zero_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_ZERO_EX) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] ST LO MI SEP ->. unfold BN_ZERO_EX.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN _]; apply cells_at_bound in BN; cbn in BN; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish.
Qed.

(* [comment removed for export] *)
Lemma bn_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A : Z) (junk : list byte),
  rw_cells bgusegs m A [CB 24 junk] ->
  stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun a0' m' => a0' = Z_to_bv 64 A /\ rw_cells bgusegs m' A (bn_cells 0 (bn_nil 0))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_INIT) fc None m (seg_rom bgusegs)).
Proof.
  intros until junk. intros BN ST LO MI SEP ->. unfold BN_INIT.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  carve_frame 16%nat ST.
  do 4 step.
  step. step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish; [reflexivity|].
  eapply bk_rw_cells_recast; [exact BN| cbn; tauto| reflexivity| reflexivity].
Qed.
