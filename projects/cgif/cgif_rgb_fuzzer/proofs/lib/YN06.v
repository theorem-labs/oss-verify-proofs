(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0o YK0j YK15.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section d. Context {fx : YK11.FPState}.
Section e.
Variable segs : list Segment.
Definition SR (c : config) (Q : config -> Prop) : Prop :=
forall T, (forall c', Q c' -> realizes segs c' T) -> realizes segs c T.
Lemma SR_ret : forall c (Q : config -> Prop), Q c -> SR c Q.
Proof. intros c Q HQ T HK. apply HK, HQ. Qed.
Lemma SR_bind : forall c (R Q : config -> Prop),
SR c R -> (forall c', R c' -> SR c' Q) -> SR c Q.
Proof. intros c R Q H1 H2 T HK. apply H1. intros c' HR. apply (H2 c' HR T HK). Qed.
Lemma SR_mono : forall c (Q Q' : config -> Prop),
SR c Q -> (forall c', Q c' -> Q' c') -> SR c Q'.
Proof. intros c Q Q' H HQQ T HK. apply H. intros c' HQ. apply HK, HQQ, HQ. Qed.
Lemma SR_realizes : forall c Q T,
SR c Q -> (forall c', Q c' -> realizes segs c' T) -> realizes segs c T.
Proof. intros c Q T H HK. exact (H T HK). Qed.
Lemma SR_step : forall ms model ms' Q,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
SR (mkCfg ms' model) Q ->
SR (mkCfg ms model) Q.
Proof.
intros ms model ms' Q Hh Hl Hs Hst H T HK.
eapply rz_step; eauto.
Qed.
Lemma SR_msteps : forall ms ms' model Q,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
SR (mkCfg ms' model) Q ->
SR (mkCfg ms model) Q.
Proof.
intros ms ms' model Q Hh Hl Hms H T HK.
eapply rz_msteps; eauto.
Qed.
Lemma SR_node : forall c (I : Type) (nx : I -> config) (i0 : I) Q,
node_ok segs c I (fun _ => []) nx ->
(forall i, SR (nx i) Q) ->
SR c Q.
Proof.
intros c I nx i0 Q Hnode H T HK.
assert (HT0 : T []).
{ eapply realizes_nonempty. apply (H i0 T HK). }
apply (rz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
- apply (rz_node segs c I (fun _ => []) nx (fun _ => T) i0 Hnode).
intros i. apply (H i T HK).
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.




End e.
End d.
Arguments SR segs c Q : clear implicits.
