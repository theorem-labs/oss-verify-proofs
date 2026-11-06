(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

(* [comment removed for export] *)
Definition CEIL_MIN : Z := 0x7fff7f800000.
Definition CEIL_MAX : Z := 0x7fffff800000.

Class Ceil : Type := mkCeil {
  ceil_val : Z;
  ceil_lo : 0x7fff7f800000 <= ceil_val;
  ceil_hi : ceil_val <= 0x7fffff800000;
  (* [comment removed for export] *)
  ceil_al : ceil_val mod 16 = 0
}.

Definition alloc_ceiling {C : Ceil} : Z := @ceil_val C.
Arguments alloc_ceiling {C} : simpl never.

Lemma alloc_ceiling_range {C : Ceil} : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. unfold alloc_ceiling. split; [apply ceil_lo | apply ceil_hi]. Qed.

Lemma alloc_ceiling_lo {C : Ceil} : 0x7fff7f800000 <= alloc_ceiling.
Proof. apply alloc_ceiling_range. Qed.

Lemma alloc_ceiling_hi {C : Ceil} : alloc_ceiling <= 0x7fffff800000.
Proof. apply alloc_ceiling_range. Qed.

Lemma alloc_ceiling_al {C : Ceil} : alloc_ceiling mod 16 = 0.
Proof. unfold alloc_ceiling. apply ceil_al. Qed.

Lemma alloc_ceiling_lt {C : Ceil} : alloc_ceiling < 2^63.
Proof. pose proof (@alloc_ceiling_hi C). assert (0x7fffff800000 < 2^63) by (vm_compute; reflexivity).
  eapply Z.le_lt_trans; eassumption. Qed.

(* [comment removed for export] *)
Definition ceil_of_val (v : Z) (H1 : 0x7fff7f800000 <= v) (H2 : v <= 0x7fffff800000) (H3 : v mod 16 = 0) : Ceil :=
  mkCeil v H1 H2 H3.

(* [comment removed for export] *)
Ltac ceil_add C :=
  lazymatch goal with
  | _ : (0x7fff7f800000 <= @alloc_ceiling C)%Z |- _ => fail
  | _ => pose proof (@alloc_ceiling_lo C); pose proof (@alloc_ceiling_hi C);
         pose proof (@ceil_lo C); pose proof (@ceil_hi C);
         pose proof (@alloc_ceiling_al C); pose proof (@ceil_al C);
         (* [comment removed for export] *)
         pose proof (eq_refl : @alloc_ceiling C = @ceil_val C)
  end.
Ltac ceil_saturate :=
  repeat match goal with
  | |- context [@alloc_ceiling ?C] => ceil_add C
  | _ : context [@alloc_ceiling ?C] |- _ => ceil_add C
  | |- context [@ceil_val ?C] => ceil_add C
  | _ : context [@ceil_val ?C] |- _ => ceil_add C
  end.

(* [comment removed for export] *)
From Stdlib Require Import Zify.
Ltac Zify.zify_pre_hook ::= ceil_saturate.

(* [comment removed for export] *)
From Stdlib Require Import Lia.
Ltac zify_noceil := intros; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate;
  Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Ltac Lia.nia ::= first [ zify_noceil; xnia zchecker | Zify.zify; xnia zchecker ].
