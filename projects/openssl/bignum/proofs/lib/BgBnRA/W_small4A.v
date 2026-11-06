(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv BgState BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX BnNumBits.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import BnRepDefs AsStruct AsStruct2 W_smallA AW_num_bits_word.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import W_small3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_IS_ONE : Z := 0x226bd0.

Definition BN_IS_ONE_STACK : Z := 16.

Lemma BN_is_one_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgasegs m A (bn_cells D b) -> u64arr bgasegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgasegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - BN_IS_ONE_STACK -> mem_inv bgasegs m ->
  (A + 24 <= bv_unsigned sp - BN_IS_ONE_STACK \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - BN_IS_ONE_STACK \/ bv_unsigned sp <= D) ->
  shb_cells bgasegs 5917624 6738232 m -> acc bgasegs m A 24 -> A mod 8 = 0 ->
  acc bgasegs m D (8 * Z.of_nat (bn_top b)) -> D mod 8 = 0 -> 0 <= D /\ D + 8 * Z.of_nat (bn_top b) <= 140737488355328 ->
  SHHI <= lo -> 0 < A ->
  a0 = Z_to_bv 64 A ->
  evt bgasegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - BN_IS_ONE_STACK, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (is_one_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_ONE) fc None m (seg_rom bgasegs)).
Proof.
  intros until b. intros BN U0 LB HT HD ST LO MI SEP SEPD (SHB1 & SHB2) ACC AL ACCD ALD BD SLO A0 ->. unfold BN_IS_ONE, BN_IS_ONE_STACK in *.
  unfold SHLO, SHHI in *.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 7 step. do 3 step. shl_with ACC AL. chk0.
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step.
  step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by lia.
  -
    step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish. unfold is_one_pure, abs_is_word_pure. replace (bn_top b =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia). cbn [andb orb Z.eqb]. reflexivity.
  - assert (ET1 : bn_top b = 1%nat) by lia.
    do 2 step. shl_with ACC AL. chk0.
    step. unfold wz at 1.
    destruct (bn_buf b) as [|x0 l0] eqn:Ebuf; [exfalso; unfold bn_dmax in HT; rewrite Ebuf in HT; cbn [length] in HT; lia|].
    assert (DM1 : 1 <= Z.of_nat (bn_dmax b)) by (unfold bn_dmax; rewrite Ebuf; cbn [length]; lia).
    pose proof (limbs_nth (x0 :: l0) 0 LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN. cbn [nth] in LN.
    do 2 step. shl_limb ACCD ALD BD 0. chk0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in pose proof (u64arr_read_0 mx D x0 l0 a U0 ltac:(addr_tac)) as RD end.
    step. clear RD.
    step.
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    +
      step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold is_one_pure, abs_is_word_pure. rewrite ET1, Ebuf. cbn [nth Nat.eqb andb orb].
      replace (x0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K1). reflexivity.
    +
      do 3 step. shl_with ACC AL. chk0.
      step. unfold wz at 1. rewrite (sx32_small (Z.b2z (bn_neg b))) by (destruct (bn_neg b); cbn; lia).
      step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold is_one_pure, abs_is_word_pure. rewrite ET1, Ebuf. cbn [nth Nat.eqb andb orb].
      replace (x0 =? 1) with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [andb].
      rewrite v_sltiu_b2z, unsigned_lit by (destruct (bn_neg b); cbn; lia). change (bv_wrap 64 1) with 1%Z. do 2 f_equal.
      destruct (bn_neg b); reflexivity.
Qed.
