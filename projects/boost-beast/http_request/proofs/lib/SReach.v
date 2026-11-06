(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.
(* [comment removed for export] *)
Let sstepc := sstep_cfg segs the_scfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sreach (Q : config -> Prop) : config -> Prop :=
| sr_done : forall c, Q c -> sreach Q c
| sr_step : forall c,
    (exists c', sstepc c [] (SNext c')) ->
    (forall evs X, sstepc c evs X -> evs = [] /\ exists c', X = SNext c') ->
    (forall evs c', sstepc c evs (SNext c') -> sreach Q c') ->
    sreach Q c.

(* [comment removed for export] *)
Lemma sr_step' : forall (Q : config -> Prop) c,
  (exists c', sstepc c [] (SNext c')) ->
  (forall evs X, sstepc c evs X ->
     evs = [] /\ exists c', X = SNext c' /\ sreach Q c') ->
  sreach Q c.
Proof.
  intros Q c Hp Ha. apply sr_step; [exact Hp| |].
  - intros evs X Hss. destruct (Ha evs X Hss) as [-> (c' & -> & _)]. split; [reflexivity | exists c'; reflexivity].
  - intros evs c' Hss. destruct (Ha evs (SNext c') Hss) as [_ (c'' & E & H)]. injection E as <-. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sreach_done : forall (Q : config -> Prop) c, Q c -> sreach Q c.
Proof. intros Q c H. apply sr_done. exact H. Qed.

Lemma sreach_mono : forall (Q Q' : config -> Prop) c,
  sreach Q c -> (forall c', Q c' -> Q' c') -> sreach Q' c.
Proof.
  intros Q Q' c H HQ. induction H as [c Hc | c Hprog Hall Hk IH].
  - apply sr_done. apply HQ. exact Hc.
  - apply sr_step; [exact Hprog | exact Hall |].
    intros evs c' Hss. exact (IH evs c' Hss).
Qed.

(* [comment removed for export] *)
Lemma sreach_seq : forall (Q1 Q2 : config -> Prop) c,
  sreach Q1 c -> (forall c', Q1 c' -> sreach Q2 c') -> sreach Q2 c.
Proof.
  intros Q1 Q2 c H K. induction H as [c Hc | c Hprog Hall Hk IH].
  - apply K. exact Hc.
  - apply sr_step; [exact Hprog | exact Hall |].
    intros evs c' Hss. exact (IH evs c' Hss).
Qed.

Lemma sreach_bind : forall (Q1 Q2 : config -> Prop) c,
  (forall c', Q1 c' -> sreach Q2 c') -> sreach Q1 c -> sreach Q2 c.
Proof. intros Q1 Q2 c K H. exact (sreach_seq Q1 Q2 c H K). Qed.

(* [comment removed for export] *)
Lemma sreach_inv : forall (Q : config -> Prop) c,
  sreach Q c ->
  Q c \/ ((exists c', sstepc c [] (SNext c'))
          /\ forall evs X, sstepc c evs X ->
               evs = [] /\ exists c', X = SNext c' /\ sreach Q c').
Proof.
  intros Q c H. destruct H as [c Hc | c Hp Ha Hk]; [left; exact Hc | right; split; [exact Hp|]].
  intros evs X Hss. destruct (Ha evs X Hss) as [-> (c' & ->)].
  split; [reflexivity|]. exists c'. split; [reflexivity | exact (Hk [] c' Hss)].
Qed.

(* [comment removed for export] *)
Lemma sreach_eq : forall (Q : config -> Prop) c c', c = c' -> sreach Q c' -> sreach Q c.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma sreach_exists_intro : forall {A} (Q : A -> config -> Prop) (a : A) c,
  sreach (Q a) c -> sreach (fun c' => exists x, Q x c') c.
Proof. intros A Q a c H. eapply sreach_mono; [exact H|]. intros c' Hc'. exists a. exact Hc'. Qed.

Lemma sreach_or_introl : forall (Q1 Q2 : config -> Prop) c,
  sreach Q1 c -> sreach (fun c' => Q1 c' \/ Q2 c') c.
Proof. intros Q1 Q2 c H. eapply sreach_mono; [exact H|]. intros; left; assumption. Qed.

Lemma sreach_or_intror : forall (Q1 Q2 : config -> Prop) c,
  sreach Q2 c -> sreach (fun c' => Q1 c' \/ Q2 c') c.
Proof. intros Q1 Q2 c H. eapply sreach_mono; [exact H|]. intros; right; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sreach_no_error_now : forall (Q : config -> Prop) c evs,
  sreach Q c -> ~ Q c -> ~ sstepc c evs SError.
Proof.
  intros Q c evs H HnQ Hss. destruct H as [c Hc | c Hp Ha Hk]; [exact (HnQ Hc)|].
  destruct (Ha evs SError Hss) as [_ (c' & Hc')]. discriminate Hc'.
Qed.

Lemma sreach_silent_now : forall (Q : config -> Prop) c evs X,
  sreach Q c -> ~ Q c -> sstepc c evs X -> evs = [].
Proof.
  intros Q c evs X H HnQ Hss. destruct H as [c Hc | c Hp Ha Hk]; [exact (False_ind _ (HnQ Hc))|].
  exact (proj1 (Ha evs X Hss)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sreach_node : forall c (I : Type) (nx : I -> config) (i0 : I) (Q : config -> Prop),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, sreach Q (nx i)) ->
  sreach Q c.
Proof.
  intros c I nx i0 Q [Hcomp Hsound] Hk.
  apply sr_step.
  - exists (nx i0). apply (Hcomp i0).
  - intros evs X Hss. destruct (Hsound evs X Hss) as (i & -> & ->).
    split; [reflexivity|]. exists (nx i). reflexivity.
  - intros evs c' Hss. destruct (Hsound evs (SNext c') Hss) as (i & _ & E).
    injection E as ->. apply Hk.
Qed.

(* [comment removed for export] *)
Lemma sreach_node_post : forall c (I : Type) (nx : I -> config) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  sreach (fun c' => exists i, c' = nx i) c.
Proof.
  intros c I nx i0 Hn. apply (sreach_node c I nx i0); [exact Hn|].
  intros i. apply sr_done. exists i. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sreach_silent1 : forall c c' (Q : config -> Prop),
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  sreach Q c' -> sreach Q c.
Proof. intros c c' Q Hn Hc. apply (sreach_node c unit (fun _ => c') tt Q Hn). intros []; exact Hc. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sreach_step1 : forall ms model ms' (Q : config -> Prop),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sreach Q (mkCfg ms' model) ->
  sreach Q (mkCfg ms model).
Proof.
  intros ms model ms' Q Hh Hlazy Hsvc Hstep Hc.
  eapply sreach_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma sreach_msteps : forall ms ms' model (Q : config -> Prop),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  sreach Q (mkCfg ms' model) ->
  sreach Q (mkCfg ms model).
Proof.
  intros ms ms' model Q Hh Hlazy Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intros Hc; [exact Hc|].
  eapply sreach_step1; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma evt_sreach : forall (P : machine_state -> Prop) ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (exists ms', msteps segs ms ms' /\ P ms') ->
  sreach (fun c => P (cfg_ms c) /\ cfg_model c = model) (mkCfg ms model).
Proof.
  intros P ms model Hh Hlazy (ms' & Hms & HP).
  eapply sreach_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply sr_done. cbn. split; [exact HP | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma evt_sreach_k : forall (P : machine_state -> Prop) ms model (Q : config -> Prop),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (exists ms', msteps segs ms ms' /\ P ms') ->
  (forall ms', P ms' -> sreach Q (mkCfg ms' model)) ->
  sreach Q (mkCfg ms model).
Proof.
  intros P ms model Q Hh Hlazy Hevt K.
  eapply sreach_seq; [apply (evt_sreach P ms model Hh Hlazy Hevt)|].
  intros [ms1 mo1] [HP Hmo]. cbn in HP, Hmo. subst mo1. apply K. exact HP.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem sreach_realizes : forall (Q : config -> Prop) c T,
  sreach Q c ->
  (forall c', Q c' -> realizes segs c' T) ->
  realizes segs c T.
Proof.
  intros Q c T H K. induction H as [c Hc | c Hprog Hall Hk IH].
  - apply K. exact Hc.
  - destruct Hprog as [c1 Hc1].
    pose (I := {c' : config | sstepc c [] (SNext c')}).
    assert (Hnode : node_ok segs c I (fun _ => []) (fun i => proj1_sig i)).
    { split.
      - intros [c' Hc']. cbn. exact Hc'.
      - intros e st Hss. destruct (Hall e st Hss) as [-> (c' & ->)].
        exists (exist _ c' Hss). split; reflexivity. }
    assert (HT : forall i : I, realizes segs (proj1_sig i) T).
    { intros [c' Hc']. cbn. apply (IH [] c' Hc'). }
    assert (HT0 : T []) by (eapply realizes_nonempty; apply (HT (exist _ c1 Hc1))).
    apply (rz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
    + apply (rz_node segs c I (fun _ => []) (fun i => proj1_sig i) (fun _ => T) (exist _ c1 Hc1) Hnode HT).
    + intros tr. split.
      * intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
      * intros Htr. exists (exist _ c1 Hc1). exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

(* [comment removed for export] *)
Lemma sreach_realizes_at : forall c c1 T,
  sreach (fun c' => c' = c1) c -> realizes segs c1 T -> realizes segs c T.
Proof. intros c c1 T H Hc1. eapply sreach_realizes; [exact H|]. intros c' ->. exact Hc1. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Example sreach_then_exit : forall ms ms1 model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms1 ->
  ms_svc_pending ms1 = Some x8 ->
  is_exit_no x8 ->
  realizes segs (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms1 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms ms1 model x8 Hh Hlazy Hms Hsvc Hx8.
  apply (sreach_realizes (fun c' => c' = mkCfg ms1 model)).
  - eapply sreach_msteps; [exact Hh | exact Hlazy | exact Hms | apply sr_done; reflexivity].
  - intros c' ->. eapply rz_exit; [exact Hh | exact Hsvc | exact Hx8].
Qed.

End WithSegs.

Arguments sreach segs {SC} Q c.
