(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnModel BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import BnRepDefs AsStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition BN_SET_NEGATIVE : Z := 0x226470.
Definition BN_IS_ZERO : Z := 0x223efc.
Definition BN_IS_NEGATIVE : Z := 0x226f60.
Definition BN_ZERO_EX : Z := 0x226aa4.

Definition bn_small_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (lo : Z) (m : word -> option byte) (R : word -> (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgasegs)
    /\ munch W m m' /\ wmono bgasegs m m' /\ mem_inv bgasegs m'
    /\ stk bgasegs m' lo (bv_unsigned sp) /\ R a0' m'.

Lemma bn_cells_bound47 : forall m A cs, rw_cells bgasegs m A cs -> mem_inv bgasegs m -> (0 < Z.of_nat (cells_size cs))%Z ->
  (0 <= A /\ A + Z.of_nat (cells_size cs) <= 140737488355328)%Z.
Proof.
  intros m A cs [_ W] MI Hn. pose proof (wr_at_below bgasegs m A _ MI W Hn) as T. unfold UTOP in T. destruct W as (W0 & _). lia.
Qed.

Lemma BN_set_negative_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgasegs m A (bn_cells D b) -> (Z.of_nat (bn_top b) < 2^31)%Z ->
  stk bgasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgasegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  shb_cells bgasegs 5917624 6738232 m -> acc bgasegs m A 24 -> (A mod 8 = 0)%Z ->
  (SHHI <= lo)%Z -> (A + 24 <= SHLO \/ SHHI <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgasegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells bgasegs m' A (bn_cells D (bn_with_neg b (negb (bv_unsigned a1 =? 0)%Z && negb (bn_top b =? 0)%nat)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_SET_NEGATIVE) fc None m (seg_rom bgasegs)).
Proof.
  intros until b. intros BN TOP ST LO MI SEP (SHB1 & SHB2) ACC AL SLO SOFF ->. unfold SHLO, SHHI in *. unfold BN_SET_NEGATIVE.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 7 step.
  step. if_cases K; zify_cond K.
  -
    step. do 3 step. shl. chk0. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
    rewrite K. cbn [Z.eqb negb andb Z.b2z]. exact BN.
  -
    do 3 step. shl. chk0.
    step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
    step. if_cases K2; zify_cond K2.
    +
      step. do 3 step. shl. chk0. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
      replace (bn_top b =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
      rewrite andb_false_r. exact BN.
    + step. step. do 3 step. shl. chk0. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
      replace (bn_top b =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (bv_unsigned a1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K).
      exact BN.
Qed.

Lemma BN_is_zero_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgasegs m A (bn_cells D b) -> (Z.of_nat (bn_top b) < 2^31)%Z ->
  stk bgasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgasegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  shb_cells bgasegs 5917624 6738232 m -> acc bgasegs m A 24 -> (A mod 8 = 0)%Z ->
  (SHHI <= lo)%Z -> (A + 24 <= SHLO \/ SHHI <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgasegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (bn_top b =? 0)%nat)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_ZERO) fc None m (seg_rom bgasegs)).
Proof.
  intros until b. intros BN TOP ST LO MI SEP (SHB1 & SHB2) ACC AL SLO SOFF ->. unfold SHLO, SHHI in *. unfold BN_IS_ZERO.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 7 step. do 3 step. shl. chk0.
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  finish. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z. do 2 f_equal.
  destruct (Nat.eqb_spec (bn_top b) 0) as [E|E]; [rewrite E; reflexivity| apply Z.ltb_ge; lia].
Qed.

Lemma BN_zero_ex_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgasegs m A (bn_cells D b) ->
  stk bgasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgasegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  shb_cells bgasegs 5917624 6738232 m -> acc bgasegs m A 24 -> (A mod 8 = 0)%Z ->
  (SHHI <= lo)%Z -> (A + 24 <= SHLO \/ SHHI <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgasegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells bgasegs m' A (bn_cells D (bn_zero_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_ZERO_EX) fc None m (seg_rom bgasegs)).
Proof.
  intros until b. intros BN ST LO MI SEP (SHB1 & SHB2) ACC AL SLO SOFF ->. unfold SHLO, SHHI in *. unfold BN_ZERO_EX.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 7 step. do 3 step. shl. chk0. step.
  do 3 step. shl. chk0. step.
  do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  finish.
Qed.
