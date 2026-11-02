(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YM06.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
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
Lemma SR_case : forall (A : Prop) c Q,
(A \/ ~ A) -> (A -> SR c Q) -> (~ A -> SR c Q) -> SR c Q.
Proof. intros A c Q [a|na] H1 H2; auto. Qed.
Lemma SR_wf : forall (W : Type) (R : W -> W -> Prop),
well_founded R ->
forall (P : W -> config -> Prop) (Q : config -> Prop),
(forall w c, P w c -> SR c (fun c' => Q c' \/ exists w', R w' w /\ P w' c')) ->
forall w c, P w c -> SR c Q.
Proof.
intros W R Hwf P Q Hbody w.
induction (Hwf w) as [w _ IH].
intros c HP. eapply SR_bind; [apply Hbody, HP|].
intros c' [HQ | (w' & HR & HP')].
- apply SR_ret, HQ.
- apply (IH w' HR c' HP').
Qed.
Lemma SR_loop : forall (W : Type) (m : W -> nat)
(P : W -> config -> Prop) (Q : config -> Prop),
(forall w c, P w c -> SR c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
forall w c, P w c -> SR c Q.
Proof.
intros W m P Q Hbody.
apply (SR_wf W (fun a b => (m a < m b)%nat)).
- apply (wf_inverse_image W nat lt m), PeanoNat.Nat.lt_wf_0.
- exact Hbody.
Qed.
Lemma SR_loopZ : forall (W : Type) (m : W -> Z)
(P : W -> config -> Prop) (Q : config -> Prop),
(forall w c, P w c -> SR c (fun c' => Q c' \/ exists w', (0 <= m w' < m w)%Z /\ P w' c')) ->
forall w c, P w c -> SR c Q.
Proof.
intros W m P Q Hbody.
apply (SR_wf W (fun a b => (0 <= m a < m b)%Z)).
- apply (wf_inverse_image W Z (fun x y => (0 <= x < y)%Z) m). apply Z.lt_wf with (z := 0%Z).
- exact Hbody.
Qed.
End e.
End d.
Arguments SR segs c Q : clear implicits.
