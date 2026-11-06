(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMESHK.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma stack_zeros12 M sp : shadow_zero M (sp - 12288) 1536 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
  intros SZ S16 i Hi. pose proof (SZ (1024 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
  replace (sp / 8 + 2147450368 + i) with ((sp - 12288) / 8 + 2147450880 + (1024 + i)) by Lia.lia. exact X.
Qed.
Lemma zsh1 M p : byte_at M (S p) 0 -> L5KA.zeros_at M (p / 8 + 2147450880) 1.
Proof. intros X i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r. unfold byte_at, S, SB in X. exact X. Qed.
Lemma shadow_low b c j : 0 <= b -> b + c <= 2 ^ 47 -> 0 <= j < c / 8 -> 2147450880 <= S b + j < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma S_range x : 0 <= x < 2 ^ 47 -> 2147450880 <= S x < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma S_add8 a j : S a + j = S (a + 8 * j).
Proof. unfold S. Lia.lia. Qed.
Lemma stk_sh_idx sp i : sp mod 16 = 0 -> 0 <= i < 512 -> sp / 8 + 2147450368 + i = S (sp - 4096 + 8 * i).
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma d32 x : (32 * x) / 8 = 4 * x.
Proof. Lia.lia. Qed.
Lemma d32b x : (32 * x + 32) / 8 = 4 * x + 4.
Proof. Lia.lia. Qed.
Lemma pow2k k : 0 <= k <= 11 -> 1 <= 2 ^ k <= 2048.
Proof. intros Hk. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(Lia.lia) ltac:(Lia.lia)); Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma ecap_le11 k : 0 < k -> PEC.ecap k <= 1024 -> k <= 11.
Proof.
  intros Hk Hc. destruct (Z_le_gt_dec k 11) as [X|X]; [exact X|]. exfalso.
  unfold PEC.ecap in Hc. replace (k =? 0) with false in Hc by (symmetry; apply Z.eqb_neq; lia).
  assert (Y : 2 ^ 11 <= 2 ^ (k - 1)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in Y. lia.
Qed.
End PMESHK.
