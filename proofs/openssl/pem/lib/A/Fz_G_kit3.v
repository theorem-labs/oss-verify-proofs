(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wg_live_neq : forall (RT : rt_sig) (AF : art_facts RT) Σ (m : mem) (L : list (Z * Z)) (i j : nat) p1 n1 p2 n2,
  ART RT Σ m -> rt_live RT Σ = L -> nth_error L i = Some (p1, n1) -> nth_error L j = Some (p2, n2) -> i <> j -> 0 < n1 -> 0 < n2 -> p1 <> p2.
Proof.
  intros RT AF Σ m L i j p1 n1 p2 n2 HA EL H1 H2 NE N1 N2 EQ. subst p2.
  destruct (nth_error_split L i H1) as (l1 & l2 & E & LEN).
  assert (IN2 : In (p1, n2) (l1 ++ l2)).
  { rewrite E in H2. destruct (Nat.lt_ge_cases j (length l1)) as [LT|GE].
    - rewrite nth_error_app1 in H2 by exact LT. apply in_or_app. left. exact (nth_error_In _ _ H2).
    - rewrite nth_error_app2 in H2 by exact GE.
      destruct (j - length l1)%nat as [|k] eqn:EJ; [exfalso; clear - EJ GE NE LEN; lia|]. cbn [nth_error] in H2. apply in_or_app. right. exact (nth_error_In _ _ H2). }
  rewrite E in EL. pose proof (af_live_disj RT AF Σ m p1 n1 p1 n2 l1 l2 HA EL IN2) as D. clear - D N1 N2. lia.
Qed.
