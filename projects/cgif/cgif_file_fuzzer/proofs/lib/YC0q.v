(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
Definition af_xf (P : Prop) : Prop := P.
Lemma af_xf_in : forall P : Prop, P -> af_xf P. Proof. intros P H. exact H. Qed.
Lemma af_xf_out : forall P : Prop, af_xf P -> P. Proof. intros P H. exact H. Qed.
