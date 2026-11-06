(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import CellsX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AXPres AXRep AXRep2 AXPRep AXPRep2 AXRep_fields AXRep_mbuf X8_rsfree X8_state1_stmt X8_state2_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record pst := mkPST {
  ps_c : pcore ; ps_S : list Z ; ps_L : list Z ; ps_ns : NS ; ps_ls : LS ; ps_em : gmap Z elt ;
  ps_h : hdrv ; ps_u : Z ; ps_es : list mbe ; ps_insz : Z ; ps_g : bool ; ps_rdi : byte ;
  ps_LBn : list block ;
  ps_A : Z }.                       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KB : Z := 22.

(* [comment removed for export] *)
Definition body_res (es : list mbe) (insz r : Z) : Z :=
  3 * (insz + r) + 512 - mb_cap es + 31 * (KB - Z.of_nat (length es)).

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
Definition new_body_off (LB0 : list block) (SP : Z) (es0 es : list mbe) : Prop :=
  forall x s, In (x, s) es -> In (x, s) es0 \/ (forall a k, aclient_range H LB0 SP a k -> 0 < k -> a + k <= x \/ x + 24 + s <= a).

(* [comment removed for export] *)
Definition HdrOwnA (LB : list block) (m : mem) (h : hdrv) : Prop :=
  ASvOwn LB m (hv_mp h) (hv_ml h) /\ ASvOwn LB m (hv_tp h) (hv_tl h) /\ 0 <= hv_ml h < 2^64 /\ 0 <= hv_tl h < 2^64.

(* [comment removed for export] *)
Definition HdrDisjP (em : gmap Z elt) (h : hdrv) : Prop :=
  (1 <= hv_ml h -> em !! (hv_mp h) = None) /\ (1 <= hv_tl h -> em !! (hv_tp h) = None) /\ (1 <= hv_ml h -> 1 <= hv_tl h -> hv_mp h <> hv_tp h).
Definition BodyDisjP (em : gmap Z elt) (h : hdrv) (es : list mbe) : Prop :=
  forall x s, In (x, s) es -> em !! x = None /\ (1 <= hv_ml h -> x <> hv_mp h) /\ (1 <= hv_tl h -> x <> hv_tp h).

(* [comment removed for export] *)
Definition hdr_disj (L : list Z) (es : list mbe) (h : hdrv) : Prop :=
  (hv_tl h <> 0 -> forall e, e ∈ L -> e + 48 <= hv_tp h \/ hv_tp h + hv_tl h <= e)
  /\ (hv_ml h <> 0 -> forall e, e ∈ L -> e + 48 <= hv_mp h \/ hv_mp h + hv_ml h <= e)
  /\ (hv_tl h <> 0 -> forall x s, In (x, s) es -> x + 24 + s <= hv_tp h \/ hv_tp h + hv_tl h <= x)
  /\ (hv_ml h <> 0 -> forall x s, In (x, s) es -> x + 24 + s <= hv_mp h \/ hv_mp h + hv_ml h <= x)
  /\ (hv_ml h <> 0 -> hv_tl h <> 0 -> hv_mp h + hv_ml h <= hv_tp h \/ hv_tp h + hv_tl h <= hv_mp h).

(* [comment removed for export] *)
Definition blk_fresh (LB0 : list block) (SP : Z) (A n : Z) : Prop :=
  forall a k, aclient_range H LB0 SP a k -> 0 < k -> a + k <= A \/ A + n <= a.

(* [comment removed for export] *)
Definition hdr_new (LB0 : list block) (SP : Z) (h0 h : hdrv) : Prop :=
  h = h0 \/ (hdr_empty h0 /\ (hv_tl h <> 0 -> blk_fresh LB0 SP (hv_tp h) (hv_tl h)) /\ (hv_ml h <> 0 -> blk_fresh LB0 SP (hv_mp h) (hv_ml h))).

(* [comment removed for export] *)
Definition svownedP (ptr len : Z) (b : block) : Prop := 1 <= len /\ blk_addr b = ptr /\ blk_size b = len.
Definition mbownedP (es : list mbe) (b : block) : Prop := exists s, In (blk_addr b, s) es /\ blk_size b = mb_block_size s.
Definition lbn_ownedP (L : list Z) (h : hdrv) (es : list mbe) (LBn : list block) : Prop :=
  forall b, In b LBn -> (blk_addr b ∈ L /\ 1 <= blk_size b) \/ svownedP (hv_mp h) (hv_ml h) b \/ svownedP (hv_tp h) (hv_tl h) b \/ mbownedP es b.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition al_ok (s : as_St H) (A MA R : Z) : Prop :=
  0 <= A <= MA /\ 0 <= R /\ as_Cm H MA - as_Cm H A + R <= as_AL H s.

Lemma al_ok_afford : asan_rt_hyps H -> forall s A MA R x,
  al_ok s A MA R -> 0 <= x -> A + x <= MA -> as_Cm H x <= as_AL H s.
Proof.
  intros HH s A MA R x (A0 & R0 & AL) Hx HAx. pose proof (ah_costs H HH) as (Cm0 & CmM & _ & _ & CmS & _).
  pose proof (CmS A x ltac:(lia) Hx). pose proof (CmM (A + x) MA ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma al_ok_afford2 : asan_rt_hyps H -> forall s A MA R x y,
  al_ok s A MA R -> 0 <= x -> 0 <= y -> A + x + y <= MA -> as_Cm H x + as_Cm H y <= as_AL H s.
Proof.
  intros HH s A MA R x y (A0 & R0 & AL) Hx Hy HAx. pose proof (ah_costs H HH) as (Cm0 & CmM & _ & _ & CmS & _).
  pose proof (CmS A x ltac:(lia) Hx). pose proof (CmS (A + x) y ltac:(lia) Hy). pose proof (CmM (A + x + y) MA ltac:(lia)). lia.
Qed.

Lemma al_ok_pay : asan_rt_hyps H -> forall s s' A MA R x,
  al_ok s A MA R -> 0 <= x -> A + x <= MA -> as_AL H s' >= as_AL H s - as_Cm H x -> al_ok s' (A + x) MA R.
Proof.
  intros HH s s' A MA R x (A0 & R0 & AL) Hx HAx AL'. pose proof (ah_costs H HH) as (Cm0 & CmM & _ & _ & CmS & _).
  pose proof (CmS A x ltac:(lia) Hx). split; [lia| split; [exact R0| lia]].
Qed.

(* [comment removed for export] *)
Lemma al_ok_mono : asan_rt_hyps H -> forall s A A' MA R,
  al_ok s A MA R -> A <= A' <= MA -> al_ok s A' MA R.
Proof.
  intros HH s A A' MA R (A0 & R0 & AL) HA. pose proof (ah_costs H HH) as (Cm0 & CmM & _). pose proof (CmM A A' ltac:(lia)). split; [lia| split; [exact R0| lia]].
Qed.

Lemma al_ok_keep : forall s s' A MA R, al_ok s A MA R -> as_AL H s' >= as_AL H s -> al_ok s' A MA R.
Proof. intros s s' A MA R (A0 & R0 & AL) K. split; [exact A0| split; [exact R0| lia]]. Qed.

(* [comment removed for export] *)
Lemma al_ok_init : asan_rt_hyps H -> forall s MA, 0 <= MA -> as_Cm H MA <= as_AL H s -> al_ok s 0 MA (as_AL H s - (as_Cm H MA - as_Cm H 0)).
Proof.
  intros HH s MA M0 AL. pose proof (ah_costs H HH) as (Cm0 & CmM & _). pose proof (Cm0 0 ltac:(lia)). pose proof (CmM 0 MA ltac:(lia)). split; [lia| split; lia].
Qed.

(* [comment removed for export] *)
Lemma al_ok_final : asan_rt_hyps H -> forall s0 s A MA,
  al_ok s A MA (as_AL H s0 - (as_Cm H MA - as_Cm H 0)) -> as_AL H s >= as_AL H s0 - (as_Cm H MA - as_Cm H 0).
Proof.
  intros HH s0 s A MA (A0 & R0 & AL). pose proof (ah_costs H HH) as (Cm0 & CmM & _). pose proof (CmM A MA ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma al_ok_lend : asan_rt_hyps H -> forall s A MA R MA',
  al_ok s A MA R -> A <= MA' <= MA -> al_ok s A MA' (R + (as_Cm H MA - as_Cm H MA')).
Proof.
  intros HH s A MA R MA' (A0 & R0 & AL) HM. pose proof (ah_costs H HH) as (Cm0 & CmM & _). pose proof (CmM MA' MA ltac:(lia)). split; [lia| split; lia].
Qed.
Lemma al_ok_unlend : forall s A MA R MA',
  al_ok s A MA' (R + (as_Cm H MA - as_Cm H MA')) -> 0 <= R -> MA' <= MA -> al_ok s A MA R.
Proof. intros s A MA R MA' (A0 & R0 & AL) HR HM. split; [lia| split; [exact HR| lia]]. Qed.

End HCW.
