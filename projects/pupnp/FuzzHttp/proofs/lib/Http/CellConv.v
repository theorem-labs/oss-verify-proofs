(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge.
Import ListNotations.
Open Scope Z_scope.

Lemma byte_lt256 : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma bytes_le_to_Z_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn; [lia|].
  apply Z.lor_nonneg. split; [pose proof (byte_lt256 b); lia|]. apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma lor_shiftl8_low : forall b r, 0 <= b < 256 -> 0 <= r -> (Z.lor b (Z.shiftl r 8)) mod 2^8 = b.
Proof.
  intros b r Hb Hr. rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 8).
  - rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r r) by lia. rewrite orb_false_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
    symmetry. apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
    apply Z.lt_le_trans with 8; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_shiftl8_high : forall b r, 0 <= b < 256 -> 0 <= r -> Z.shiftr (Z.lor b (Z.shiftl r 8)) 8 = r.
Proof.
  intros b r Hb Hr. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
  replace (i + 8 - 8) with i by lia.
  rewrite (Z.bits_above_log2 b); [reflexivity| lia|].
  destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma Z_to_le_bytes_inv : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_lt256 b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap8_mod. apply lor_shiftl8_low; lia.
  - rewrite lor_shiftl8_high by lia. exact IH.
Qed.

Lemma bytes_le_to_Z_bound : forall bs, bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs. rewrite <- (Z_to_le_bytes_inv bs) at 1.
  rewrite bytes_le_to_Z_of_le_bytes by apply bytes_le_to_Z_nonneg.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma le8_of_bytes : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. pose proof (bytes_le_to_Z_nonneg bs).
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn in B |- *; lia).
  rewrite <- L. apply Z_to_le_bytes_inv.
Qed.

Lemma le4_of_bytes : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le4, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. pose proof (bytes_le_to_Z_nonneg bs).
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn in B |- *; lia).
  rewrite <- L. apply Z_to_le_bytes_inv.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rw_cells_recell : forall m A pre c c' post,
  rw_cells segs m A (pre ++ c :: post) -> cell_wf c' -> cbytes c' = cbytes c -> csize c' = csize c ->
  rw_cells segs m A (pre ++ c' :: post).
Proof.
  intros m A pre c c' post [[Hwf Hb] Hw] W' E S'.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
  split; [split|].
  - apply cells_wf_app. cbn. tauto.
  - rewrite !cells_bytes_app in *. cbn [cells_bytes] in *. rewrite E. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size] in *. rewrite S'. exact Hw.
Qed.

#[using="Type"] Lemma rw_cells_CB_C8 : forall m A pre bs post,
  rw_cells segs m A (pre ++ CB 8 bs :: post) -> rw_cells segs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre bs post H.
  assert (L : length bs = 8%nat).
  { destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [Hc _]]. exact Hc. }
  eapply rw_cells_recell; [exact H| exact I| cbn; apply le8_of_bytes; exact L| reflexivity].
Qed.

#[using="Type"] Lemma rw_cells_CB_C4 : forall m A pre bs post,
  rw_cells segs m A (pre ++ CB 4 bs :: post) -> rw_cells segs m A (pre ++ C4 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre bs post H.
  assert (L : length bs = 4%nat).
  { destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [Hc _]]. exact Hc. }
  eapply rw_cells_recell; [exact H| exact I| cbn; apply le4_of_bytes; exact L| reflexivity].
Qed.
End WithSegs.
