(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Unset Lia Cache.

Definition CEIL_MIN : Z := 0x7fff7f800000.
Definition CEIL_MAX : Z := 0x7fffff800000.

Class ceiling : Type := Ceiling {
  alloc_ceiling : Z;
  alloc_ceiling_range : CEIL_MIN <= alloc_ceiling <= CEIL_MAX;
  alloc_ceiling_pg : alloc_ceiling mod 4096 = 0;
  ssp_canary : Z;
  ssp_canary_range : 0 <= ssp_canary < 2^64;

  ctx_secret : Z;
  ctx_secret_range : 0 <= ctx_secret < 2^64
}.

Section CEIL.
Context {CLG : ceiling}.

Lemma alloc_ceiling_range' : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact alloc_ceiling_range. Qed.
Lemma alloc_ceiling_lt47 : alloc_ceiling < 2^47.
Proof. pose proof alloc_ceiling_range. unfold CEIL_MIN, CEIL_MAX in *. lia. Qed.
Lemma alloc_ceiling_lt63 : alloc_ceiling < 2^63.
Proof. pose proof alloc_ceiling_range. unfold CEIL_MIN, CEIL_MAX in *. lia. Qed.
Lemma alloc_ceiling_lt64 : alloc_ceiling < 2^64.
Proof. pose proof alloc_ceiling_range. unfold CEIL_MIN, CEIL_MAX in *. lia. Qed.
Lemma alloc_ceiling_pos : 0 < alloc_ceiling.
Proof. pose proof alloc_ceiling_range. unfold CEIL_MIN, CEIL_MAX in *. lia. Qed.
Lemma ssp_canary_range' : 0 <= ssp_canary < 2^64.
Proof. exact ssp_canary_range. Qed.
Lemma ctx_secret_range' : 0 <= ctx_secret < 2^64.
Proof. exact ctx_secret_range. Qed.
End CEIL.

Ltac pose_ceil :=
  repeat match goal with
  | |- context [@alloc_ceiling ?e] => is_evar e; lazymatch goal with C : ceiling |- _ => unify e C end
  | H : context [@alloc_ceiling ?e] |- _ => is_evar e; lazymatch goal with C : ceiling |- _ => unify e C end
  end;
  lazymatch goal with
  | H : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z |- _ => idtac
  | _ => pose proof alloc_ceiling_range' as CEIL_RANGE
  end.

Ltac clear_ceil :=
  repeat match goal with H : context [@alloc_ceiling _] |- _ => clear H end;
  try match goal with C : ceiling |- _ => clear C end.

Definition ceiling_min : ceiling.
Proof. refine (Ceiling CEIL_MIN _ _ 0 _ 0 _); [unfold CEIL_MIN, CEIL_MAX; lia | reflexivity | lia | lia]. Defined.
