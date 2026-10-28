(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_check_tlenA Fr_asn1_d2i_ex_primitive.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition EXO_STACK_A : Z := ADEP_FRAME + CHECK_TLEN_STACK_A + 6 * 176.
(* [comment removed for export] *)
Definition EXO_COST_A (n : Z) : Z := 15 * n + 2 ^ 19.
(* [comment removed for export] *)
Definition EXO_FRAMES_A : Z := 1 + CHECK_TLEN_FRAMES_A.

Lemma exo_budgets : EXO_STACK_A = 67680 /\ EXO_FRAMES_A = 7 /\ (forall n, EXO_COST_A n = 15 * n + 524288).
Proof.
  unfold EXO_STACK_A, EXO_FRAMES_A, EXO_COST_A, ADEP_FRAME. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. intros n. reflexivity.
Qed.

Lemma exo_within_d2i_octet : EXO_STACK_A + 720 <= D2I_OCTET_STACK_A /\ EXO_FRAMES_A + 1 <= D2I_OCTET_FRAMES_A /\ (forall n, 0 <= n -> EXO_COST_A n + 2 ^ 19 <= D2I_OCTET_COST_A n).
Proof.
  unfold EXO_STACK_A, EXO_FRAMES_A, EXO_COST_A, D2I_OCTET_STACK_A, D2I_OCTET_FRAMES_A, D2I_OCTET_COST_A, ADEP_FRAME.
  split; [clear; lia|]. split; [clear; lia|]. intros n Hn. clear - Hn. lia.
Qed.
