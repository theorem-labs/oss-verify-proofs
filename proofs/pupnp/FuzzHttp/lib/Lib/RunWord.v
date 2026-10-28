(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.

Class HasGuard : Type := mkGuard { guard_word : word ; secret_word : word }.

Definition run_guard (g s : word) : HasGuard := mkGuard g s.

Lemma guard_word_of g s : @guard_word (run_guard g s) = g.
Proof. reflexivity. Qed.
Lemma secret_word_of g s : @secret_word (run_guard g s) = s.
Proof. reflexivity. Qed.
