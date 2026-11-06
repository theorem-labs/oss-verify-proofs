(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface.
Import ListNotations.
Open Scope Z_scope.

Section LiveKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma live_base_size : forall Σ (m : mem) p n1 n2, ART RT Σ m -> In (p, n1) (rt_live RT Σ) -> In (p, n2) (rt_live RT Σ) ->
  0 < n1 -> 0 < n2 -> n1 = n2.
Proof using AF.
  intros Σ m p n1 n2 HA Hi1 Hi2 P1 P2. destruct (Z.eq_dec n1 n2) as [E|NE]; [exact E| exfalso].
  destruct (in_split _ _ Hi1) as (l1 & l2 & E).
  assert (Hi3 : In (p, n2) (l1 ++ l2)).
  { rewrite E in Hi2. apply in_app_or in Hi2. apply in_or_app.
    destruct Hi2 as [X|[X|X]]; [left; exact X| injection X as X; congruence| right; exact X]. }
  pose proof (af_live_disj RT AF Σ m p n1 p n2 l1 l2 HA E Hi3) as D. lia.
Qed.

(* [comment removed for export] *)
Lemma live_size_ne : forall Σ (m : mem) p n q k, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) ->
  0 < n -> 0 < k -> n <> k -> p <> q.
Proof using AF. intros Σ m p n q k HA H1 H2 P1 P2 NE E. subst q. exact (NE (live_base_size Σ m p n k HA H1 H2 P1 P2)). Qed.

(* [comment removed for export] *)
Lemma live_head_apart : forall Σ (m : mem) p n rest q k, ART RT Σ m -> rt_live RT Σ = (p, n) :: rest -> In (q, k) rest ->
  p + n <= q \/ q + k <= p.
Proof using AF. intros Σ m p n rest q k HA E H. exact (af_live_disj RT AF Σ m p n q k [] rest HA E H). Qed.
Lemma live_second_apart : forall Σ (m : mem) p0 n0 p n rest q k, ART RT Σ m -> rt_live RT Σ = (p0, n0) :: (p, n) :: rest -> In (q, k) rest ->
  p + n <= q \/ q + k <= p.
Proof using AF. intros Σ m p0 n0 p n rest q k HA E H. apply (af_live_disj RT AF Σ m p n q k [(p0, n0)] rest HA E). right. exact H. Qed.
End LiveKit.
