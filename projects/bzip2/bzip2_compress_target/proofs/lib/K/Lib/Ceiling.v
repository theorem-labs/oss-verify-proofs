(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Class Ceiling : Type := mkCeiling {
  alloc_ceiling : Z;
  (* [comment removed for export] *)
  alloc_ceiling_ge : 0x7fff7f800000 <= alloc_ceiling;
  (* [comment removed for export] *)
  alloc_ceiling_le : alloc_ceiling + 8388608 <= 0x800000000000;
  (* [comment removed for export] *)
  alloc_ceiling_al : alloc_ceiling mod 16 = 0
}.

Ltac ceil_bounds :=
  pose proof alloc_ceiling_ge; pose proof alloc_ceiling_le; pose proof alloc_ceiling_al.

Section Facts.
  Context {CE : Ceiling}.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma alloc_ceiling_range : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
  Proof. ceil_bounds. lia. Qed.
End Facts.

(* [comment removed for export] *)

Definition ceiling_raw (sp : Z) : Z :=
  Z.max 0x7fff7f800000 (Z.min 0x7fffff800000 ((sp - 8388608) / 16 * 16)).

Lemma ceiling_raw_ge : forall sp, 0x7fff7f800000 <= ceiling_raw sp.
Proof. intros sp. unfold ceiling_raw. lia. Qed.

Lemma ceiling_raw_le : forall sp, ceiling_raw sp + 8388608 <= 0x800000000000.
Proof. intros sp. unfold ceiling_raw. lia. Qed.

Lemma ceiling_raw_al : forall sp, ceiling_raw sp mod 16 = 0.
Proof.
  intros sp. unfold ceiling_raw.
  destruct (Z.max_spec 0x7fff7f800000 (Z.min 0x7fffff800000 ((sp - 8388608) / 16 * 16))) as [[_ ->]|[_ ->]];
    [|reflexivity].
  destruct (Z.min_spec 0x7fffff800000 ((sp - 8388608) / 16 * 16)) as [[_ ->]|[_ ->]]; [reflexivity|].
  apply Z_mod_mult.
Qed.

Definition ceiling_of_sp (sp : Z) : Ceiling :=
  mkCeiling (ceiling_raw sp) (ceiling_raw_ge sp) (ceiling_raw_le sp) (ceiling_raw_al sp).

(* [comment removed for export] *)
