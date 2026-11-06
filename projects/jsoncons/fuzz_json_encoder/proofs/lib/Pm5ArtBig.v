(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ArtMem Pm5ArtCellJoin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).

Lemma Z_to_bv8_bits : forall z z', (forall i, 0 <= i < 8 -> Z.testbit z i = Z.testbit z' i) -> Z_to_bv 8 z = Z_to_bv 8 z'.
Proof.
  intros z z' H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  apply Z.bits_inj'. intros i Hi. rewrite !Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i 8); [cbn [andb]; apply H; lia|reflexivity].
Qed.
Lemma Z_to_le_bytes_bits : forall n z z', (forall i, 0 <= i < 8 * Z.of_nat n -> Z.testbit z i = Z.testbit z' i) -> Z_to_le_bytes n z = Z_to_le_bytes n z'.
Proof.
  induction n as [|n IH]; intros z z' H; [reflexivity|]. cbn [Z_to_le_bytes]. f_equal.
  - apply Z_to_bv8_bits. intros i Hi. apply H. lia.
  - apply IH. intros i Hi. rewrite !Z.shiftr_spec by lia. apply H. lia.
Qed.
Lemma Z_to_le_bytes_mod : forall n z, Z_to_le_bytes n z = Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n)).
Proof.
  intros n z. apply Z_to_le_bytes_bits. intros i Hi. rewrite Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i (8 * Z.of_nat n)); [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Lemma art_w2lb4_mod : forall v, 0 <= v < 2 ^ 64 -> word_to_le_bytes 4 (Z_to_bv 64 v) = word_to_le_bytes 4 (Z_to_bv 64 (v mod 2 ^ 32)).
Proof.
  intros v Hv. unfold word_to_le_bytes. pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as Hm.
  rewrite !art_u_lit by lia. rewrite (Z_to_le_bytes_mod 4 v). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). reflexivity.
Qed.
Lemma art_cell4_mod : forall (M : word -> option byte) a v, 0 <= a -> 0 <= v < 2 ^ 64 -> cellA M a 4 v -> cellA M a 4 (v mod 2 ^ 32).
Proof. intros M a v Ha Hv C. unfold cell in *. rewrite <- art_w2lb4_mod by lia. exact C. Qed.
Lemma art_cell4_mod_r : forall (M : word -> option byte) a v, 0 <= a -> 0 <= v < 2 ^ 64 -> cellA M a 4 (v mod 2 ^ 32) -> cellA M a 4 v.
Proof. intros M a v Ha Hv C. unfold cell in *. rewrite art_w2lb4_mod by lia. exact C. Qed.

(* [comment removed for export] *)
Lemma art_hdr_word2 : forall (M : word -> option byte) h st b1 hi, 0 <= h -> h + 4 < 2 ^ 64 -> 0 <= st < 256 -> 0 <= b1 < 256 -> 0 <= hi < 2 ^ 16 ->
  cellA M h 1 st -> cellA M (h + 1) 1 b1 -> cellA M (h + 2) 2 hi -> cellA M h 4 (st + 256 * b1 + 65536 * hi).
Proof.
  intros M h st b1 hi Hh Hh' Hst Hb1 Hhi C0 C1 C2.
  assert (C12 : cellA M (h + 1) 3 (b1 + hi * 2 ^ (8 * Z.of_nat 1))).
  { apply (art_cell_join M (h + 1) 1 2 b1 hi); [lia|cbn; lia|lia|cbn; lia|cbn; lia|exact C1|]. replace (h + 1 + Z.of_nat 1) with (h + 2) by lia. exact C2. }
  replace (st + 256 * b1 + 65536 * hi) with (st + (b1 + hi * 2 ^ (8 * Z.of_nat 1)) * 2 ^ (8 * Z.of_nat 1)) by (cbn; lia).
  apply (art_cell_join M h 1 3 st (b1 + hi * 2 ^ (8 * Z.of_nat 1))); [lia|cbn; lia|lia|cbn; lia|cbn; lia|exact C0|]. replace (h + Z.of_nat 1) with (h + 1) by lia. exact C12.
Qed.

(* [comment removed for export] *)
Lemma art_land_hi_lo : forall h l, 0 <= h -> 0 <= l < 2 ^ 32 -> Z.land (h * 2 ^ 32) l = 0.
Proof.
  intros h l Hh Hl. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i 32) as [Lo|Hi'].
  - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec l 0) as [->|Nz]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    rewrite (Z.bits_above_log2 l i); [apply Bool.andb_false_r|lia|]. apply Z.lt_le_trans with (m := 32); [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma art_lor_hi_lo : forall h l, 0 <= h -> 0 <= l < 2 ^ 32 -> Z.lor (h * 2 ^ 32) l = h * 2 ^ 32 + l.
Proof.
  intros h l Hh Hl. rewrite <- Z.lxor_lor by (apply art_land_hi_lo; lia). symmetry. apply Z.add_nocarry_lxor. apply art_land_hi_lo; lia.
Qed.
Lemma art_div32_range : forall n, 0 <= n < 2 ^ 39 -> 0 <= n / 2 ^ 32 < 2 ^ 7.
Proof. intros n Hn. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. Qed.
Lemma art_divmod32 : forall n, 0 <= n -> n = n mod 2 ^ 32 + 2 ^ 32 * (n / 2 ^ 32).
Proof. intros n Hn. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). lia. Qed.
