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
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import BnRepDefs AsStruct AsStruct2 W_smallA AW_num_bits_word.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import W_small3A.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2249680 => 2
  | 2249684 => 1
  | 2249688 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_IS_ONE : Z := 0x22539c.

Definition BN_IS_ONE_STACK : Z := 48.

Lemma BN_is_one_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) -> u64arr bgbsegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgbsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - BN_IS_ONE_STACK -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - BN_IS_ONE_STACK \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - BN_IS_ONE_STACK \/ bv_unsigned sp <= D) ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> A mod 8 = 0 ->
  acc bgbsegs m D (8 * Z.of_nat (bn_top b)) -> D mod 8 = 0 -> 0 <= D /\ D + 8 * Z.of_nat (bn_top b) <= 140737488355328 ->
  SHHI <= lo -> 0 < A -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  a0 = Z_to_bv 64 A ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - BN_IS_ONE_STACK, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (is_one_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_ONE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN U0 LB HT HD ST LO MI SEP SEPD SHBC ACC AL ACCD ALD BD SLO A0 PD ->. unfold BN_IS_ONE, BN_IS_ONE_STACK in *.
  pose proof SHBC as (SHB1 & SHB2).
  unfold SHLO, SHHI in *.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  pose proof (proj1 ST) as LO0.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32).
  { apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R. lia. }
  unfold bn_cells in BN.
  carve_frame 32%nat ST.
  do 9 step. do 3 step.

  lazymatch goal with MUx : munch _ m ?mq |- _ =>
    assert (ACC1 : acc bgbsegs mq A 24) by (eapply acc_munch; [exact ACC | exact MUx | exact OFF | clear - A0; lia | clear - B47; lia]);
    assert (ACCD1 : acc bgbsegs mq D (8 * Z.of_nat (bn_top b))) by (eapply acc_munch; [exact ACCD | exact MUx | exact OFF | clear - BD; lia | clear - BD; lia])
  end.
  eapply evt_cut.
  { eapply BN_abs_is_word_specA with (lo := lo) (A := A) (D := D) (b := b);
      [exact BN | exact U0 | exact LB | exact HT | exact HD | rewrite ESP; exact ST | rewrite ESP; clear - LO; lia | exact MI
      | rewrite ESP; clear - SEP; lia | rewrite ESP; clear - SEPD; lia
      | exact (conj SHB1 SHB2) | exact ACC1 | exact AL | exact ACCD1 | exact ALD | exact BD | unfold SHHI; exact SLO | reflexivity | exact A0 | exact PD]. }
  intros ms' PO. unfold bn_small_postA in PO.
  destruct PO as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m2 & E & MUc & WMc & MIc & STc & RES).
  subst ms' u3. rewrite ESP in MUc, STc. rewrite (ret_pc_even 2249676) by lia.
  rewrite (unsigned_lit 1) by lia.
  lazymatch goal with MUx : munch _ m ?mq |- _ =>
    assert (FR2 := rw_cells_transport bgbsegs _ mq m2 _ _ FR MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia));
    assert (BN2 := rw_cells_transport bgbsegs _ mq m2 _ _ BN MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [clear - SEP; lia| exact I]));
    assert (MU2 : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m2)
      by (eapply munch_trans; [exact MUx|]; eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x Hx; lia)
  end.
  assert (WM2 := wmono_trans bgbsegs _ _ _ WM WMc).
  clear FR MU WM MUc WMc ST MI BN U0 ACC1 ACCD1 SHB1 SHB2.
  step. if_cases KR; zify_cond KR; rewrite ?unsigned_lit in KR by (destruct (abs_is_word_pure b 1); cbn; lia).
  -
    do 4 step. release_frame FR2 STc (bv_unsigned sp). step. step.
    finish. unfold is_one_pure. destruct (abs_is_word_pure b 1); [cbn in KR; lia | reflexivity].
  - hide_ors. ub. unhide.
    do 3 step. shl_with ACC AL. chk0.
    step. unfold wz at 1. rewrite (sx32_small (Z.b2z (bn_neg b))) by (destruct (bn_neg b); cbn; lia).
    step. do 4 step. release_frame FR2 STc (bv_unsigned sp). step. step.
    finish. unfold is_one_pure. destruct (abs_is_word_pure b 1); [| exfalso; clear - KR; first [discriminate KR | apply KR; reflexivity | cbn in KR; lia]]. cbn [andb].
    rewrite v_sltiu_b2z, unsigned_lit by (destruct (bn_neg b); cbn; lia). change (bv_wrap 64 1) with 1%Z. do 2 f_equal.
    destruct (bn_neg b); reflexivity.
Qed.
