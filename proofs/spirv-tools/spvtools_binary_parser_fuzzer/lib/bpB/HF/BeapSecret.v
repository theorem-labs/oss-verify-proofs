(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase StackLayout.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Class HeapSecret : Type := mkHeapSecret {
  hsecret : Z ;
  hsecret_range : 0 <= hsecret < 2^64 ;
  hcanary : Z ;
  hcanary_range : 0 <= hcanary < 2^64
}.

Ltac hsb :=
  let K := fresh "HSECB" in
  pose proof (hsecret_range : 0 <= hsecret < 2^64) as K;
  let K2 := fresh "HCANB" in
  pose proof (hcanary_range : 0 <= hcanary < 2^64) as K2.

Fixpoint bytes_le_val (bs : list byte) : Z :=
  match bs with
  | [] => 0
  | b :: bs' => bv_unsigned b + 256 * bytes_le_val bs'
  end.

Definition secret_bytes_of_draw (rnd : EntryDraw) : list byte :=
  skipn 8 (at_random_bytes (ed_random rnd)).

Definition secret_of_draw (rnd : EntryDraw) : Z := bytes_le_val (secret_bytes_of_draw rnd).

Lemma bytes_le_val_range : forall bs, 0 <= bytes_le_val bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_val length]; [lia|].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  replace (8 * Z.of_nat (S (length bs))) with (8 + 8 * Z.of_nat (length bs)) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma length_secret_bytes_of_draw : forall rnd, length (secret_bytes_of_draw rnd) = 8%nat.
Proof. intros rnd. reflexivity. Qed.

Lemma secret_of_draw_range : forall rnd, 0 <= secret_of_draw rnd < 2^64.
Proof.
  intros rnd. unfold secret_of_draw.
  pose proof (bytes_le_val_range (secret_bytes_of_draw rnd)) as R.
  rewrite length_secret_bytes_of_draw in R. exact R.
Qed.

Lemma word_range (w : word) : 0 <= bv_unsigned w < 2^64.
Proof. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R. Qed.
Definition heap_secret_of_draw (rnd : EntryDraw) (cw : word) : HeapSecret :=
  mkHeapSecret (secret_of_draw rnd) (secret_of_draw_range rnd) (bv_unsigned cw) (word_range cw).

Section Facts.
  Context {HSEC : HeapSecret}.

End Facts.
