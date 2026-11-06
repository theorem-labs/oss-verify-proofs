(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics StackLayout.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import MState Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

(* [comment removed for export] *)
Class RunRnd : Type := mkRunRnd { run_draw : EntryDraw ; run_hw : word }.
(* [comment removed for export] *)
Definition run_rnd {RN__ : RunRnd} : bv 128 := ed_random run_draw.

(* [comment removed for export] *)
Definition rnd_lo (r : bv 128) : word := bv_extract 0 64 r.
Definition rnd_hi (r : bv 128) : word := bv_extract 64 64 r.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with (2 ^ 8)%Z.
    rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i 8).
    + rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia. rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      symmetry. apply (Z.bits_above_log2 (bv_unsigned b) i); [lia|].
      destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [rewrite E; cbn; lia|].
      assert (Z.log2 (bv_unsigned b) < 8)%Z by (apply Z.log2_lt_pow2; lia). lia.
  - replace (Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) 8) with (bytes_le_to_Z bs); [exact IH|].
    apply Z.bits_inj'. intros i Hi.
    rewrite Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
    replace (i + 8 - 8)%Z with i by lia.
    rewrite (Z.bits_above_log2 (bv_unsigned b) (i + 8)); [reflexivity|lia|].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [rewrite E; cbn; lia|].
    assert (Z.log2 (bv_unsigned b) < 8)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with ((bytes_le_to_Z bs) mod 2^64)%Z.
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

(* [comment removed for export] *)
Definition guard_bytes (g : word) : list byte := firstn 1 (le8 g) ++ [Z_to_bv 8 0] ++ skipn 2 (le8 g).
Definition guard_of (g : word) : word := le_bytes_to_word (guard_bytes g).

Lemma guard_bytes_length : forall g, length (guard_bytes g) = 8%nat.
Proof. intros g. unfold guard_bytes. rewrite !app_length, firstn_length, skipn_length, length_le8. reflexivity. Qed.

Lemma le8_guard_of : forall g, le8 (guard_of g) = guard_bytes g.
Proof. intros g. apply le8_le_bytes_to_word, guard_bytes_length. Qed.

Section WithRnd.
  Context {RN__ : RunRnd}.
  (* [comment removed for export] *)
  Definition rr_guard : word := guard_of (rnd_lo run_rnd).
  Definition rr_secret : word := rnd_hi run_rnd.
End WithRnd.
