(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape PropExec MState Mem Exec.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Inductive aevt (Q : config -> Prop) : config -> Prop :=
| aevt_now : forall c, Q c -> aevt Q c
| aevt_step : forall c,
    (exists c', sstep segs c [] (SNext c')) ->
    (forall e st, sstep segs c e st -> e = [] /\ st <> SError) ->
    (forall e c', sstep segs c e (SNext c') -> aevt Q c') ->
    aevt Q c.

#[using="Type"] Lemma aevt_bind : forall (P Q : config -> Prop) c,
  aevt P c -> (forall c', P c' -> aevt Q c') -> aevt Q c.
Proof.
  intros P Q c H K. induction H as [c HP | c Hprog Hsil Hk IH].
  - apply K, HP.
  - apply aevt_step; [exact Hprog | exact Hsil |].
    intros e c' Hs. apply IH with e. exact Hs.
Qed.

#[using="Type"] Lemma aevt_mono : forall (P Q : config -> Prop) c,
  aevt P c -> (forall c', P c' -> Q c') -> aevt Q c.
Proof.
  intros P Q c H K. eapply aevt_bind; [exact H|]. intros c' HP. apply aevt_now, K, HP.
Qed.

#[using="Type"] Lemma aevt_eq : forall Q c c', c = c' -> aevt Q c' -> aevt Q c.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevt_realizes : forall Q c T,
  aevt Q c -> (forall c', Q c' -> realizes segs c' T) -> realizes segs c T.
Proof.
  intros Q c T H K. induction H as [c HP | c Hprog Hsil Hk IH].
  - apply K, HP.
  - destruct Hprog as [c0 Hc0].
    set (I := { c' : config | sstep segs c [] (SNext c') }).
    assert (Hnode : node_ok segs c I (fun _ => []) (fun i => proj1_sig i)).
    { split.
      - intros [c' Hc']. exact Hc'.
      - intros e st Hs. destruct (Hsil e st Hs) as [-> Hne].
        destruct st as [c'|]; [|congruence].
        exists (exist _ c' Hs). split; reflexivity. }
    assert (HT : forall i : I, realizes segs (proj1_sig i) T).
    { intros [c' Hc']. cbn. apply (IH [] c' Hc'). }
    apply (rz_conseq segs c (t_alt (fun i : I => t_emit [] T))).
    + apply (rz_node segs c I (fun _ => []) (fun i => proj1_sig i) (fun _ => T)
               (exist _ c0 Hc0) Hnode HT).
    + assert (T0 : T []).
      { eapply realizes_nonempty. apply (HT (exist _ c0 Hc0)). }
      intro tr. split.
      * intros [i Hi]. apply (proj1 (t_emit_nil_eq T T0 tr)). exact Hi.
      * intros Htr. exists (exist _ c0 Hc0). apply (proj2 (t_emit_nil_eq T T0 tr)). exact Htr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevt_mstep : forall Q ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  aevt Q (mkCfg ms' model) ->
  aevt Q (mkCfg ms model).
Proof.
  intros Q ms model ms' Hh Hlazy Hsvc Hstep Hc.
  apply aevt_step.
  - exists (mkCfg ms' model). apply (sstep_instr segs ms model ms' model); [assumption|assumption|].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hs. destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hs) as [-> ->].
    split; [reflexivity|congruence].
  - intros e c' Hs. destruct (sstep_instr_inv segs ms model ms' e (SNext c') Hlazy Hsvc Hstep Hs) as [_ E].
    inversion E; subst. exact Hc.
Qed.

#[using="Type"] Lemma aevt_msteps : forall Q ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  aevt Q (mkCfg ms' model) ->
  aevt Q (mkCfg ms model).
Proof.
  intros Q ms ms' model Hh Hlazy Hms.
  induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intro Hc; [exact Hc|].
  eapply aevt_mstep; eauto.
Qed.


(* [comment removed for export] *)
Definition MOK (mo : Model) : Prop := m_halted mo = None /\ m_vm_lazy mo = [].

Definition aevtM (mo : Model) (Q : config -> Prop) (ms : machine_state) : Prop :=
  aevt Q (mkCfg ms mo).

#[using="Type"] Lemma aevtM_step : forall mo Q ms ms1,
  MOK mo -> mstep segs ms ms1 -> aevtM mo Q ms1 -> aevtM mo Q ms.
Proof.
  intros mo Q ms ms1 [Hh Hl] [Hsvc Hst] H. unfold aevtM in *.
  eapply aevt_mstep; eauto.
Qed.

#[using="Type"] Lemma aevtM_done : forall mo (Q : config -> Prop) ms, Q (mkCfg ms mo) -> aevtM mo Q ms.
Proof. intros. apply aevt_now. assumption. Qed.

#[using="Type"] Lemma aevtM_msteps : forall mo Q ms ms', MOK mo -> msteps segs ms ms' -> aevtM mo Q ms' -> aevtM mo Q ms.
Proof.
  intros mo Q ms ms' MK H. induction H; intros HQ; [exact HQ|].
  eapply aevtM_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtM_cut_evt : forall mo (P : machine_state -> Prop) Q ms,
  MOK mo -> evt segs P ms -> (forall ms', P ms' -> aevtM mo Q ms') -> aevtM mo Q ms.
Proof.
  intros mo P Q ms MK (ms' & Hs & HP) K. eapply aevtM_msteps; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtM_cut : forall mo (P : config -> Prop) Q ms,
  aevtM mo P ms -> (forall ms' mo', P (mkCfg ms' mo') -> aevtM mo' Q ms') -> aevtM mo Q ms.
Proof.
  intros mo P Q ms H K. unfold aevtM in *. eapply aevt_bind; [exact H|].
  intros [ms' mo'] HP. apply (K ms' mo' HP).
Qed.

#[using="Type"] Lemma aevtM_mono : forall mo (P Q : config -> Prop) ms,
  aevtM mo P ms -> (forall c, P c -> Q c) -> aevtM mo Q ms.
Proof. intros. unfold aevtM in *. eapply aevt_mono; eauto. Qed.

#[using="Type"] Lemma aevtM_eq : forall mo Q ms ms', ms = ms' -> aevtM mo Q ms' -> aevtM mo Q ms.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evt_aevtM : forall mo (P : machine_state -> Prop) ms,
  MOK mo -> evt segs P ms -> aevtM mo (fun c => P (cfg_ms c) /\ cfg_model c = mo) ms.
Proof.
  intros mo P ms MK H. eapply aevtM_cut_evt; [exact MK| exact H|].
  intros ms' HP. apply aevtM_done. split; [exact HP| reflexivity].
Qed.

End WithSegs.

Arguments aevtM segs mo Q ms /.
