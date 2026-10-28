(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_check_tlenA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition D2I_OCTET_STACK_A : Z := 2048 + CHECK_TLEN_STACK_A.
Definition D2I_OCTET_COST_A (n : Z) : Z := 15 * n + 2 ^ 20.
Definition D2I_OCTET_FRAMES_A : Z := 2 + CHECK_TLEN_FRAMES_A.

Lemma D2I_OCTET_COST_A_bound : forall n, 0 <= n < 2 ^ 26 -> 0 <= D2I_OCTET_COST_A n <= 2 ^ 30 - 2 ^ 25.
Proof. intros n Hn. unfold D2I_OCTET_COST_A. lia. Qed.
Lemma D2I_OCTET_FRAMES_A_val : D2I_OCTET_FRAMES_A = 8.
Proof. reflexivity. Qed.
