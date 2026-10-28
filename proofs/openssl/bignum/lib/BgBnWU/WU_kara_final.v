(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import BnCallsU WU_cmp_part_words WU_sub_part_words WU_mul_normal WU_mul_recursive WU_mul_part_recursive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cmp_part_words_uok : cmp_part_words_uspec 16.
Proof. unfold cmp_part_words_uspec. intros. eapply bn_cmp_part_words_uspec; eassumption. Qed.

Lemma sub_part_words_uok : sub_part_words_uspec 144.
Proof. unfold sub_part_words_uspec. intros. eapply bn_sub_part_words_uspec; eassumption. Qed.

Lemma mul_normal_uok : mul_normal_uspec 224.
Proof. unfold mul_normal_uspec. intros. eapply bn_mul_normal_uspec; eassumption. Qed.

Section Final.
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_uspec CS8.

  (* [comment removed for export] *)
  Definition kara_uleaf : Z := Z.max 224 CS8.

  Lemma kara_uleaf_ok : (0 <= CS8 <= kara_uleaf /\ 0 <= 16 <= kara_uleaf /\ 0 <= 144 <= kara_uleaf /\ 0 <= 224 <= kara_uleaf)%Z.
  Proof. unfold kara_uleaf. lia. Qed.
  Lemma kara_uleaf_80 : (80 <= kara_uleaf)%Z.
  Proof. unfold kara_uleaf. lia. Qed.

  (* [comment removed for export] *)
  Theorem bn_mul_recursive_ufinal : forall k, rec_uspec_at kara_uleaf k.
  Proof.
    exact (bn_mul_recursive_uspec kara_uleaf CS8 16 144 224 kara_uleaf_ok kara_uleaf_80 comba8_ok cmp_part_words_uok sub_part_words_uok mul_normal_uok).
  Qed.

  (* [comment removed for export] *)
  Theorem bn_mul_part_recursive_ufinal : forall fuel, part_uspec_at kara_uleaf fuel.
  Proof.
    exact (bn_mul_part_recursive_uspec kara_uleaf CS8 16 144 224 kara_uleaf_ok kara_uleaf_80 comba8_ok cmp_part_words_uok sub_part_words_uok
             mul_normal_uok bn_mul_recursive_ufinal).
  Qed.
End Final.
