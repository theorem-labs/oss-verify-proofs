(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition alloc_floor : Z := 0x7FFF7F800000.
Definition alloc_ceiling_max : Z := 0x7FFFFF800000.

Class HasCeiling : Type := mkCeiling {
  alloc_ceiling : Z;
  alloc_ceiling_range : alloc_floor <= alloc_ceiling <= alloc_ceiling_max;

  alloc_ceiling_al16 : alloc_ceiling mod 16 = 0
}.

Lemma alloc_ceiling_bounds {HC : HasCeiling} :
  0x7FFF7F800000 <= alloc_ceiling <= 0x7FFFFF800000.
Proof. exact alloc_ceiling_range. Qed.

Lemma alloc_ceiling_lt63 {HC : HasCeiling} : alloc_ceiling < 2^63.
Proof. pose proof alloc_ceiling_bounds. lia. Qed.

Lemma alloc_ceiling_lt47 {HC : HasCeiling} : alloc_ceiling < 2^47.
Proof. pose proof alloc_ceiling_bounds. lia. Qed.

Lemma alloc_ceiling_pos {HC : HasCeiling} : 0 < alloc_ceiling.
Proof. pose proof alloc_ceiling_bounds. lia. Qed.

Lemma alloc_ceiling_le_max {HC : HasCeiling} : alloc_ceiling <= alloc_ceiling_max.
Proof. exact (proj2 alloc_ceiling_range). Qed.

Lemma alloc_floor_le {HC : HasCeiling} : alloc_floor <= alloc_ceiling.
Proof. exact (proj1 alloc_ceiling_range). Qed.

Lemma alloc_ceiling_aligned {HC : HasCeiling} : alloc_ceiling mod 16 = 0.
Proof. exact alloc_ceiling_al16. Qed.

Lemma alloc_ceiling_aligned8 {HC : HasCeiling} : alloc_ceiling mod 8 = 0.
Proof. pose proof alloc_ceiling_al16. Z.div_mod_to_equations. lia. Qed.

Lemma alloc_ceiling_aligned4096_false_hint : True. Proof. exact I. Qed.

Lemma alloc_ceiling_facts {HC : HasCeiling} :
  (0x7FFF7F800000 <= alloc_ceiling <= 0x7FFFFF800000) /\ alloc_ceiling mod 16 = 0.
Proof. split; [exact alloc_ceiling_range | exact alloc_ceiling_al16]. Qed.

Definition ceiling_of (c : Z) (H : alloc_floor <= c <= alloc_ceiling_max) (A : c mod 16 = 0) : HasCeiling :=
  mkCeiling c H A.

Lemma alloc_ceiling_of c H A : @alloc_ceiling (ceiling_of c H A) = c.
Proof. reflexivity. Qed.
