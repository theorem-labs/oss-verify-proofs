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
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import BnRepDefs AsStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2237364 => 2
  | 2237368 => 1
  | 2237372 => 2
  | 2247380 => 2
  | 2247384 => 1
  | 2247388 => 2
  | 2247428 => 1
  | 2247432 => 1
  | 2247436 => 2
  | 2247440 => 2
  | 2249300 => 2
  | 2249304 => 1
  | 2249308 => 2
  | 2250488 => 2
  | 2250492 => 1
  | 2250496 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition BN_SET_NEGATIVE : Z := 0x224ab4.
Definition BN_IS_ZERO : Z := 0x2223a4.
Definition BN_IS_NEGATIVE : Z := 0x2256e8.
Definition BN_ZERO_EX : Z := 0x225244.

Definition bn_small_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (lo : Z) (m : word -> option byte) (R : word -> (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgbsegs)
    /\ munch W m m' /\ wmono bgbsegs m m' /\ mem_inv bgbsegs m'
    /\ stk bgbsegs m' lo (bv_unsigned sp) /\ R a0' m'.

Lemma bn_cells_bound47 : forall m A cs, rw_cells bgbsegs m A cs -> mem_inv bgbsegs m -> (0 < Z.of_nat (cells_size cs))%Z ->
  (0 <= A /\ A + Z.of_nat (cells_size cs) <= 140737488355328)%Z.
Proof.
  intros m A cs [_ W] MI Hn. pose proof (wr_at_below bgbsegs m A _ MI W Hn) as T. unfold UTOP in T. destruct W as (W0 & _). lia.
Qed.

Lemma BN_set_negative_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) -> (Z.of_nat (bn_top b) < 2^31)%Z ->
  stk bgbsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> (A mod 8 = 0)%Z ->
  (SHHI <= lo)%Z -> (A + 24 <= SHLO \/ SHHI <= A)%Z ->
  a0 = Z_to_bv 64 A -> (0 < A)%Z ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells bgbsegs m' A (bn_cells D (bn_with_neg b (negb (bv_unsigned a1 =? 0)%Z && negb (bn_top b =? 0)%nat)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_SET_NEGATIVE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN TOP ST LO MI SEP (SHB1 & SHB2) ACC AL SLO SOFF -> PA. unfold SHLO, SHHI in *. unfold BN_SET_NEGATIVE.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 7 (ub; step).
  ub; step. if_cases K; zify_cond K.
  -
    ub; step. do 3 (ub; step). ub; shl. ub; chk0. ub; step. do 2 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
    finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
    rewrite K. cbn [Z.eqb negb andb Z.b2z]. exact BN.
  -
    do 3 (ub; step). ub; shl. ub; chk0.
    ub; step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
    ub; step. ub; step. if_cases K2; zify_cond K2.
    +
      ub; step. do 3 (ub; step). ub; shl. ub; chk0. ub; step. do 2 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
      finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
      replace (bn_top b =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
      rewrite andb_false_r. exact BN.
    + ub; step. do 3 (ub; step). ub; shl. ub; chk0. ub; step. do 2 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
      finish. unfold bn_cells, bn_with_neg. cbn [bn_top bn_buf bn_neg bn_flags bn_d bn_dmax].
      replace (bn_top b =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (bv_unsigned a1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K).
      exact BN.
Qed.

Lemma BN_is_zero_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) -> (Z.of_nat (bn_top b) < 2^31)%Z ->
  stk bgbsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> (A mod 8 = 0)%Z ->
  (SHHI <= lo)%Z -> (A + 24 <= SHLO \/ SHHI <= A)%Z ->
  a0 = Z_to_bv 64 A -> (0 < A)%Z ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (bn_top b =? 0)%nat)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_ZERO) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN TOP ST LO MI SEP (SHB1 & SHB2) ACC AL SLO SOFF -> PA. unfold SHLO, SHHI in *. unfold BN_IS_ZERO.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 7 (ub; step). do 3 (ub; step). ub; shl. ub; chk0.
  ub; step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  ub; step. do 2 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
  finish. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z. do 2 f_equal.
  destruct (Nat.eqb_spec (bn_top b) 0) as [E|E]; [rewrite E; reflexivity| apply Z.ltb_ge; lia].
Qed.

Lemma BN_zero_ex_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) ->
  stk bgbsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> (A mod 8 = 0)%Z ->
  (SHHI <= lo)%Z -> (A + 24 <= SHLO \/ SHHI <= A)%Z ->
  a0 = Z_to_bv 64 A -> (0 < A)%Z ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells bgbsegs m' A (bn_cells D (bn_zero_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_ZERO_EX) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN ST LO MI SEP (SHB1 & SHB2) ACC AL SLO SOFF -> PA. unfold SHLO, SHHI in *. unfold BN_ZERO_EX.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 7 (ub; step). do 3 (ub; step). ub; shl. ub; chk0. ub; step.
  do 3 (ub; step). ub; shl. ub; chk0. ub; step.
  do 2 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
  finish.
Qed.
