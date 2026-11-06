(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Class RunW : Type := mkRunW { rw_guard_w : bv 64 ; rw_secret_w : bv 64 }.

Definition run_guard {RW : RunW} : Z := bv_unsigned rw_guard_w.
Definition run_secret {RW : RunW} : Z := bv_unsigned rw_secret_w.

Section Facts.
Context {RW : RunW}.
Lemma run_guard_range : 0 <= run_guard < 2^64.
Proof. unfold run_guard. pose proof (bv_unsigned_in_range 64 rw_guard_w) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
Lemma run_secret_range : 0 <= run_secret < 2^64.
Proof. unfold run_secret. pose proof (bv_unsigned_in_range 64 rw_secret_w) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
