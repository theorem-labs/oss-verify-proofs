(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import MStateS8 MemS8 CellsS8 StepS8 FrameS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma Z_testbit_high8 : forall (b : byte) i, 8 <= i -> Z.testbit (bv_unsigned b) i = false.
Proof.
  intros b i Hi. pose proof (u8_range b) as Hb.
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [rewrite E; apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 8); [|lia].
  apply Z.log2_lt_pow2; lia.
Qed.

Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high8 b i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high8 b i) by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

Lemma bytes_le_to_Z_bound : forall bs, 0 <= bytes_le_to_Z bs < 256 ^ (Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; [cbn; lia|]. rewrite bytes_le_to_Z_cons. cbn [length].
  pose proof (u8_range b). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte, exists v : word, le4 v = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3. exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  unfold le4. pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as Hb. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Hb.
  rewrite unsigned_lit by (change (256 ^ 4) with 4294967296 in Hb; lia).
  exact (Z_to_le_bytes_to_Z [b0; b1; b2; b3]).
Qed.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.

Definition agree_on (lo hi : Z) (m m' : word -> option byte) : Prop :=
  forall a, lo <= a < hi -> m' (wa a) = m (wa a).

Lemma mrd_agree : forall m m' x, m' x = m x -> mrd segs m' x = mrd segs m x.
Proof. intros m m' x E. unfold mrd. rewrite E. reflexivity. Qed.

Lemma bytes_at_agree : forall m m' a bs,
  bytes_at segs m a bs -> agree_on a (a + Z.of_nat (length bs)) m m' -> bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & HB) HA. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (mrd_agree m m') by (apply HA; lia). apply HB. exact Hi.
Qed.

Lemma wmono_of_grows : forall m m' : word -> option byte,
  (forall x, m x <> None -> m' x <> None) -> wmono segs m m'.
Proof.
  intros m m' Hg x Hx. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - specialize (Hg x ltac:(rewrite E; discriminate)). destruct (m' x); [discriminate| congruence].
  - destruct (m' x); [discriminate| exact Hx].
Qed.

Lemma wr_at_wmono : forall m m' a n, wr_at segs m a n -> wmono segs m m' -> wr_at segs m' a n.
Proof. intros m m' a n (H0 & H1 & HW) WM. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply WM. apply HW. exact Hi. Qed.

Lemma rw_cells_agree : forall m m' A cs,
  rw_cells segs m A cs -> agree_on A (A + Z.of_nat (cells_size cs)) m m' -> wmono segs m m' -> rw_cells segs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] HA WM. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by exact Hwf. exact HA.
  - eapply wr_at_wmono; [exact HW| exact WM].
Qed.

Lemma stk_agree : forall m m' lo hi,
  stk segs m lo hi -> agree_on lo hi m m' -> wmono segs m m' -> stk segs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & HS) HA WM. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HS a Ha) as [W [b Hb]]. split; [apply WM; exact W|].
  exists b. rewrite (mrd_agree m m') by (apply HA; exact Ha). exact Hb.
Qed.

End WithSegs.
