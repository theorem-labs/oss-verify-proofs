(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjLeaves.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition sxu (v : Z) : Z := bv_unsigned (sx32 (Z_to_bv 64 v)).
Definition or4 (a b c e : Z) : Z := Z.lor (Z.lor (Z.lor (sxu a) (sxu b)) (sxu c)) (sxu e).
Definition ONES64 : Z := 18446744073709551615.
Definition DINV : Z := 4294967295.

Lemma sxu_valid : forall v, 0 <= v < 65536 -> sxu v = v.
Proof. intros v H. unfold sxu. rewrite sx32_small by lia. apply u64_small. lia. Qed.

Lemma sxu_invalid : sxu DINV = ONES64.
Proof. vm_compute. reflexivity. Qed.

Lemma sxu_range : forall v, 0 <= sxu v < 2 ^ 64.
Proof. intros v. unfold sxu. pose proof (bv_unsigned_in_range 64 (sx32 (Z_to_bv 64 v))) as R. unfold bv_modulus in R. exact R. Qed.

Lemma lor_ones64_r : forall x, 0 <= x < 2 ^ 64 -> Z.lor x ONES64 = ONES64.
Proof.
  intros x H. unfold ONES64. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  destruct (Z.ltb_spec n 64).
  - rewrite Z.ones_spec_low by lia. apply orb_true_r.
  - rewrite Z.ones_spec_high by lia. rewrite orb_false_r.
    apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|].
    apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (2 ^ 64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma lor_ones64_l : forall x, 0 <= x < 2 ^ 64 -> Z.lor ONES64 x = ONES64.
Proof. intros. rewrite Z.lor_comm. apply lor_ones64_r. assumption. Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb. assert (NN : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; [exact NN|].
  assert (S0 : Z.shiftr (Z.lor a b) n = 0).
  { rewrite Z.shiftr_lor, !Z.shiftr_div_pow2 by lia. rewrite !Z.div_small by lia. reflexivity. }
  apply Z.shiftr_eq_0_iff in S0. destruct S0 as [->|[P L]]; [apply Z.pow_pos_nonneg; lia|].
  apply Z.log2_lt_pow2; assumption.
Qed.

Definition dshape (x : Z) : Prop := 0 <= x < 65536 \/ x = DINV.

Lemma or4_cases : forall a b c e, dshape a -> dshape b -> dshape c -> dshape e ->
  or4 a b c e = ONES64 \/
  (0 <= or4 a b c e < 65536 /\ 0 <= a < 65536 /\ 0 <= b < 65536 /\ 0 <= c < 65536 /\ 0 <= e < 65536).
Proof.
  intros a b c e Ha Hb Hc He. unfold or4.
  pose proof (sxu_range a) as Ra. pose proof (sxu_range b) as Rb. pose proof (sxu_range c) as Rc. pose proof (sxu_range e) as Re.
  assert (Rab : 0 <= Z.lor (sxu a) (sxu b) < 2 ^ 64) by (apply lor_lt_pow2; lia).
  assert (Rabc : 0 <= Z.lor (Z.lor (sxu a) (sxu b)) (sxu c) < 2 ^ 64) by (apply lor_lt_pow2; lia).
  destruct He as [He| ->]; [|left; rewrite sxu_invalid; apply lor_ones64_r; exact Rabc].
  destruct Hc as [Hc| ->]; [|left; rewrite sxu_invalid, (lor_ones64_r _ Rab); apply lor_ones64_l; exact Re].
  destruct Hb as [Hb| ->]; [|left; rewrite sxu_invalid, (lor_ones64_r _ Ra), (lor_ones64_l _ Rc); apply lor_ones64_l; exact Re].
  destruct Ha as [Ha| ->]; [|left; rewrite sxu_invalid, (lor_ones64_l _ Rb), (lor_ones64_l _ Rc); apply lor_ones64_l; exact Re].
  right. rewrite !sxu_valid by lia. change 65536 with (2 ^ 16).
  split; [|lia]. apply lor_lt_pow2; [lia| |lia]. apply lor_lt_pow2; [lia| |lia]. apply lor_lt_pow2; lia.
Qed.

Lemma dig_valid_not_qb : forall base b, (base = 630 \/ base = 420 \/ base = 210 \/ base = 0) -> dig (base + b) < 65536 -> not_qb b.
Proof.
  intros base b Hb Hv. destruct dig_hextab as [_ HT]. split; intro Eb; subst b.
  - rewrite (HT base 34 Hb (or_introl eq_refl)) in Hv. lia.
  - rewrite (HT base 92 Hb (or_intror eq_refl)) in Hv. lia.
Qed.

Lemma lor_shl8_add : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (Z.shiftl a 8) b = a * 256 + b.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.add_lor_land.
  assert (L0 : Z.land (a * 256) b = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8).
    - replace (a * 256) with (a * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite (Z.bits_above_log2 b n); [apply andb_false_r|lia|].
      destruct (Z.eq_dec b 0) as [->|NZ]; [cbn; lia|].
      apply Z.lt_le_trans with 8; [|lia]. apply Z.log2_lt_pow2; lia. }
  lia.
Qed.

Lemma lor_shl8_bu : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor (Z.shiftl a 8) b = 23669 -> a = 92 /\ b = 117.
Proof. intros a b Ha Hb H. rewrite lor_shl8_add in H by lia. lia. Qed.
