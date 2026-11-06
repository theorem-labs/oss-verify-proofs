(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CEIL_LO : Z := 0x7fff7f800000.
Definition CEIL_HI : Z := 0x7fffff800000.

Class RunP : Type := mkRunP {
  ceil_val : Z;
  ceil_range : CEIL_LO <= ceil_val <= CEIL_HI;
  secret_val : Z;
  secret_range : 0 <= secret_val < 2^64;
  canary_val : Z;
  canary_range : 0 <= canary_val < 2^64
}.

Section RUNP.
Context {RUNp : RunP}.

Definition alloc_ceiling : Z := ceil_val.

Lemma alloc_ceiling_range : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. unfold alloc_ceiling. pose proof ceil_range. unfold CEIL_LO, CEIL_HI in *. lia. Qed.
Lemma alloc_ceiling_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. apply alloc_ceiling_range. Qed.
Lemma alloc_ceiling_hi : alloc_ceiling <= 0x7fffff800000.
Proof. apply alloc_ceiling_range. Qed.
Lemma alloc_ceiling_lt63 : alloc_ceiling < 2^63.
Proof. pose proof alloc_ceiling_range. lia. Qed.
Lemma alloc_ceiling_pos : 0 < alloc_ceiling.
Proof. pose proof alloc_ceiling_range. lia. Qed.
Lemma secret_val_range : 0 <= secret_val < 2^64.
Proof. exact secret_range. Qed.
Lemma canary_val_range : 0 <= canary_val < 2^64.
Proof. exact canary_range. Qed.

End RUNP.

Lemma alloc_ceiling_mkRunP : forall c Hc s Hs k Hk, @alloc_ceiling (mkRunP c Hc s Hs k Hk) = c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac fix_runp :=
  try (let i := constr:(_ : RunP) in
       repeat match goal with
              | |- context [?R] => is_evar R; lazymatch type of R with RunP => unify R i end
              end).
(* [comment removed for export] *)
Ltac pose_ceil :=
  fix_runp;
  lazymatch goal with
  | _ : _ <= alloc_ceiling <= _ |- _ => idtac
  | _ => let H := fresh "CEIL_RANGE__" in pose proof alloc_ceiling_range as H
  end.
(* [comment removed for export] *)
Ltac pose_secret :=
  fix_runp;
  lazymatch goal with
  | _ : 0 <= secret_val < _ |- _ => idtac
  | _ => let H := fresh "SECRET_RANGE__" in pose proof secret_val_range as H
  end.
Ltac pose_canary :=
  fix_runp;
  lazymatch goal with
  | _ : 0 <= canary_val < _ |- _ => idtac
  | _ => let H := fresh "CANARY_RANGE__" in pose proof canary_val_range as H
  end.
