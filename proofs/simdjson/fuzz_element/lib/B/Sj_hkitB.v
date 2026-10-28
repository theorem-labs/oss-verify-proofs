(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land7_mod8 : forall A, A mod 8 = 0 -> Z.land A 7 = 0.
Proof. intros A H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma land3_mod8 : forall A, A mod 8 = 0 -> Z.land A 3 = 0.
Proof.
  intros A H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  assert (E : A = 8 * (A / 8)) by (pose proof (Z.div_mod A 8 ltac:(lia)); lia).
  rewrite E. replace (8 * (A / 8)) with ((2 * (A / 8)) * 4) by lia. apply Z.mod_mul. lia.
Qed.

Lemma land15_mod16 : forall A, A mod 16 = 0 -> Z.land A 15 = 0.
Proof. intros A H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact H. Qed.

Lemma land7_mod16 : forall A, A mod 16 = 0 -> Z.land A 7 = 0.
Proof.
  intros A H. apply land7_mod8.
  assert (E : A = 16 * (A / 16)) by (pose proof (Z.div_mod A 16 ltac:(lia)); lia).
  rewrite E. replace (16 * (A / 16)) with ((2 * (A / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma mod8_of_mod16 : forall A, A mod 16 = 0 -> A mod 8 = 0.
Proof.
  intros A H. assert (E : A = 16 * (A / 16)) by (pose proof (Z.div_mod A 16 ltac:(lia)); lia).
  rewrite E. replace (16 * (A / 16)) with ((2 * (A / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.
