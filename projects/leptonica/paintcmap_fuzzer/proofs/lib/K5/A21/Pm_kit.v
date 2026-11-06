(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface.
Import ListNotations.
Open Scope Z_scope.

Section PmKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma pm_live_apart : forall Σ m p n q k, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) -> p <> q ->
  p + n <= q \/ q + k <= p.
Proof using AF.
  intros Σ m p n q k HA H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p n q k l1 l2 HA E). rewrite E in H2. apply in_app_or in H2. apply in_or_app.
  destruct H2 as [X|[X|X]]; [left; exact X| injection X as X1 X2; congruence | right; exact X].
Qed.

(* [comment removed for export] *)
Lemma removed_chunk_apart : forall Σ (m : mem) p n live0 usp a,
  ART RT Σ m -> In (p, n) (rt_live RT Σ) -> (forall e, In e live0 -> In e (rt_live RT Σ) /\ fst e <> p) ->
  rt_sp0 RT Σ - STACK_WIN <= usp ->
  aclient live0 (rt_frames RT Σ) usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ m p n live0 usp a HA INL SUB SPL Ha.
  pose proof (af_live_range RT AF Σ m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp). destruct (SUB _ Hin) as [HinL NE]. cbn [fst] in NE.
    pose proof (pm_live_apart Σ m p n p' n' HA INL HinL ltac:(congruence)) as D. lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_frames_range RT AF Σ m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_fshadow_apart RT AF Σ m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.
End PmKit.

Lemma live_remove_in : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> In e l /\ fst e <> p.
Proof.
  intros l p e He. split; [exact (live_remove_sub l p e He)|]. unfold live_remove in He.
  apply stdpp.base.list_elem_of_In in He. apply stdpp.list_basics.list.list_elem_of_filter in He. destruct He as [Hf _].
  intro E. rewrite E, Z.eqb_refl in Hf. exact Hf.
Qed.
