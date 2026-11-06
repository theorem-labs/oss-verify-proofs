(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Cells Step.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMXB Require Import ShZero RdnCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land_m8' : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx. change 18446744073709551608 with (Z.shiftl (Z.ones 61) 3).
  change 8 with (2 ^ 3). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 3) as [L|G].
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
    replace (i - 3 + 3) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [L2|G2].
    + replace ((0 <=? i - 3) && (i - 3 <? 61))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply Bool.andb_true_r.
    + assert (Tf : Z.testbit x i = false).
      { destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
        apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
      rewrite Tf. reflexivity.
Qed.

Lemma land_round8 : forall y, 0 <= y < 2^64 -> Z.land (Z.land y 18446744073709551615) 18446744073709551608 = y / 8 * 8.
Proof.
  intros y Hy. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  apply land_m8'. exact Hy.
Qed.

Lemma nth_le8_zero : forall i, (i < 8)%nat -> nth_error (le8 (Z_to_bv 64 0)) i = Some (Z_to_bv 8 0).
Proof. intros i Hi. destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try reflexivity; lia. Qed.

Section S.
Variable segs : list Segment.

Lemma zsh_qword : forall m lo hi y, zsh m lo hi -> 0 <= y < 2^64 - 8 ->
  shw_lo lo <= y / 8 * 8 -> y / 8 * 8 + 8 <= shw_hi hi ->
  ro_cells segs m (Z.land (Z.land y 18446744073709551615) 18446744073709551608) [C8 (Z_to_bv 64 0)].
Proof.
  intros m lo hi y Z Hy H1 H2. rewrite land_round8 by lia.
  pose proof (Z.mul_div_le y 8 ltac:(lia)) as D1. rewrite Z.mul_comm in D1.
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  split; [pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia|]. split; [rewrite length_le8; cbn; lia|].
  intros i Hi. rewrite length_le8 in Hi. rewrite nth_le8_zero by exact Hi. unfold mrd. rewrite Z; [reflexivity|]. lia.
Qed.
End S.

Lemma round8_bounds : forall y, 0 <= y -> y - 7 <= y / 8 * 8 <= y.
Proof. intros y Hy. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia. Qed.

Lemma div8_bounds : forall x, 0 <= x -> x / 8 * 8 <= x < x / 8 * 8 + 8.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

Lemma zsh_qwords : forall segs m p n, zsh m p (p + n) -> 0 < n -> 0 <= p -> p + n <= 0x7fffffffff00 ->
  ro_cells segs m (Z.land (Z.land (2147450880 + Z.shiftr p 3) 18446744073709551615) 18446744073709551608) [C8 (Z_to_bv 64 0)] /\
  ro_cells segs m (Z.land (Z.land (2147450880 + Z.shiftr (p + n - 1) 3) 18446744073709551615) 18446744073709551608) [C8 (Z_to_bv 64 0)].
Proof.
  intros segs m p n Z Hn Hp Hpn.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (div8_bounds p Hp) as Dp. pose proof (div8_bounds (p + n - 1) ltac:(lia)) as Dq.
  pose proof (div8_bounds (p + n) ltac:(lia)) as Dr.
  pose proof (round8_bounds (2147450880 + p / 8) ltac:(lia)) as R0.
  pose proof (round8_bounds (2147450880 + (p + n - 1) / 8) ltac:(lia)) as R1.
  assert (M : (p + n - 1) / 8 <= (p + n) / 8) by (apply Z.div_le_mono; lia).
  assert (M0 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  split; (apply zsh_qword with (lo := p) (hi := p + n); [exact Z | | unfold shw_lo, SBZ | unfold shw_hi, SBZ]; lia).
Qed.
