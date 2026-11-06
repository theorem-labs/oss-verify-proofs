(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
Import ListNotations.

Record md_pure (md : Model) : Prop := MD_PURE {
  mp_halted : m_halted md = None;
  mp_lazy   : m_vm_lazy md = [];
  mp_mat    : m_vm_materialized md = []
}.

Lemma md_pure_with_vmmaps : forall h md, md_pure md -> md_pure (with_vmmaps h md).
Proof.
  intros h md [H1 H2 H3]. constructor.
  - exact H1.
  - unfold m_vm_lazy in *. cbn. exact H2.
  - unfold m_vm_materialized in *. cbn. exact H3.
Qed.

Lemma md_pure_killed_none : forall md, md_pure md -> m_killed md = None.
Proof. intros md [H _ _]. apply m_killed_of_m_halted_none. exact H. Qed.
