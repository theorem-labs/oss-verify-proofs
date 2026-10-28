(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require HxaComba8.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require AW_sub_part_words AW_mul_normal.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import ARun BnCallsKA AW_mul_recursive AW_mul_rec_top AW_mul_part_recursive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition CS8A : Z := 592%Z.

Lemma CS8A_0 : (0 <= CS8A)%Z.
Proof. unfold CS8A. lia. Qed.

Lemma comba8_okA : comba8_aspec CS8A.
Proof. exact HxaComba8.comba8_okA. Qed.

Lemma sub_part_words_okA : sub_part_words_bspec.
Proof.
  unfold sub_part_words_bspec. intros.
  eapply AW_sub_part_words.bn_sub_part_words_aspec; eassumption.
Qed.

Lemma mul_normal_okA : mul_normal_bspec.
Proof.
  unfold mul_normal_bspec. intros.
  eapply AW_mul_normal.bn_mul_normal_aspec; eassumption.
Qed.

Section Closed.
  Context {AR : ARun}.

  (* [comment removed for export] *)
  Theorem bn_mul_recursive_closedA : forall k, rec_spec_atA CS8A k.
  Proof. exact (bn_mul_recursive_aspec CS8A CS8A_0 comba8_okA sub_part_words_okA mul_normal_okA). Qed.

  (* [comment removed for export] *)
  Theorem bn_mul_part_recursive_closedA : forall fuel, part_spec_atA CS8A fuel.
  Proof. exact (bn_mul_part_recursive_aspec CS8A CS8A_0 comba8_okA sub_part_words_okA mul_normal_okA). Qed.
End Closed.
(* [comment removed for export] *)
