(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Export ExSmallIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition CLEN (n : Z) : Z := 100 + 2 * cbound n.
Definition ZE_STREAM_END : Z := 1.
Definition ZE_DATA_ERROR : Z := -3.
Definition INFL_ERRS : list Z := [1; 2; -2; -3; -4; -5].
Definition SYNC_ERRS : list Z := [-2; -3; -5].
Definition INFL_RCS  : list Z := [0; 1; 2; -2; -3; -4; -5].

Inductive i1exit : Type := I1_OK | I1_E (err : Z).
Inductive isexit : Type := IS_OK | IS_E (err : Z).
Inductive i2exit : Type := I2_W | I2_R (rc : Z).

Record flush_model : Type := FLUSH_MODEL {
  fm_compr : list Z -> list Z;
  fm_busy  : list Z -> bool;
  fm_tot   : list Z -> Z;
  fm_i1  : list Z -> Z -> i1exit;
  fm_is  : list Z -> Z -> Z -> isexit;
  fm_i2  : list Z -> Z -> Z -> i2exit;
  fm_i2b : list Z -> Z -> Z -> Z;
  fm_compr_len : forall d, Z.of_nat (length (fm_compr d)) = CLEN (Z.of_nat (length d));
  fm_tot_range : forall d, 2 <= fm_tot d <= CLEN (Z.of_nat (length d));
  fm_i1_errs   : forall c n e, fm_i1 c n = I1_E e -> In e INFL_ERRS;
  fm_is_errs   : forall c clen n e, fm_is c clen n = IS_E e -> In e SYNC_ERRS;
  fm_i2_rcs    : forall c clen n rc, fm_i2 c clen n = I2_R rc -> In rc INFL_RCS;
  fm_i2b_rcs   : forall c clen n, In (fm_i2b c clen n) INFL_RCS
}.

Definition fm_clen (FM : flush_model) (d : list Z) : Z :=
  if fm_busy FM d then CLEN (Z.of_nat (length d)) else fm_tot FM d.

Lemma CLEN_ge : forall n, 0 <= n -> 126 <= CLEN n.
Proof. intros n Hn. unfold CLEN, cbound. pose proof (Z.div_pos n 4096). pose proof (Z.div_pos n 16384). pose proof (Z.div_pos n 33554432). lia. Qed.
Lemma CLEN_lt32 : forall n, 0 <= n <= 2 ^ 20 -> CLEN n < 2 ^ 22.
Proof.
  intros n Hn. unfold CLEN, cbound.
  assert (n / 4096 <= 2 ^ 8) by (apply Z.div_le_upper_bound; lia).
  assert (n / 16384 <= 2 ^ 6) by (apply Z.div_le_upper_bound; lia).
  rewrite (Z.div_small n 33554432) by lia. lia.
Qed.
Lemma fm_clen_range : forall FM d, 2 <= fm_clen FM d <= CLEN (Z.of_nat (length d)).
Proof. intros FM d. unfold fm_clen. destruct (fm_busy FM d); [| apply fm_tot_range]. pose proof (CLEN_ge (Z.of_nat (length d)) ltac:(lia)). lia. Qed.
Lemma INFL_ERRS_range : forall e, In e INFL_ERRS -> -5 <= e <= 2 /\ e <> 0.
Proof. intros e H. unfold INFL_ERRS in H. cbn in H. lia. Qed.
Lemma SYNC_ERRS_range : forall e, In e SYNC_ERRS -> -5 <= e <= -2.
Proof. intros e H. unfold SYNC_ERRS in H. cbn in H. lia. Qed.
Lemma INFL_RCS_range : forall e, In e INFL_RCS -> -5 <= e <= 2.
Proof. intros e H. unfold INFL_RCS in H. cbn in H. lia. Qed.
