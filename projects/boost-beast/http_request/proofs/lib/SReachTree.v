(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require ITree Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg SReach.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cj_msteps_msteps : forall ms ms',
  Exec.msteps segs ms ms' <-> CatSim.msteps segs ms ms'.
Proof.
  intros ms ms'. split.
  - intros H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH].
    + apply mst_refl.
    + eapply mst_step; [exact Hsvc | exact Hstep | exact IH].
  - intros H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
    + apply Exec.msteps_refl.
    + eapply Exec.msteps_cons; [split; [exact Hsvc | exact Hstep] | exact IH].
Qed.

Lemma cj_msteps_sreach : forall ms ms' model (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  Exec.msteps segs ms ms' ->
  sreach segs Q (mkCfg ms' model) -> sreach segs Q (mkCfg ms model).
Proof.
  intros ms ms' model Q Hh Hlazy Hms Hc.
  eapply sreach_msteps; [exact Hh | exact Hlazy | apply cj_msteps_msteps; exact Hms | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma cj_evt_sreach : forall (P : machine_state -> Prop) ms model,
  m_halted model = None -> m_vm_lazy model = [] ->
  Exec.evt segs P ms ->
  sreach segs (fun c => P (cfg_ms c) /\ cfg_model c = model) (mkCfg ms model).
Proof.
  intros P ms model Hh Hlazy (ms' & Hms & HP).
  eapply cj_msteps_sreach; [exact Hh | exact Hlazy | exact Hms |].
  apply sr_done. cbn. split; [exact HP | reflexivity].
Qed.

Lemma cj_evt_sreach_k : forall (P : machine_state -> Prop) ms model (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  Exec.evt segs P ms ->
  (forall ms', P ms' -> sreach segs Q (mkCfg ms' model)) ->
  sreach segs Q (mkCfg ms model).
Proof.
  intros P ms model Q Hh Hlazy (ms' & Hms & HP) K.
  eapply cj_msteps_sreach; [exact Hh | exact Hlazy | exact Hms | apply K; exact HP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tree.
Context {node : Type}.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> ITree.resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : ITree.node_sound node segs at_node nstep nexit minv nsafe.
Hypothesis minv_lazy : forall mo, minv mo -> m_vm_lazy mo = [].

#[local] Notation "'itree'" := (ITree.itree node) (at level 0).
#[local] Notation "'impl'" := (ITree.impl segs at_node) (at level 0).
#[local] Notation "'tsafe'" := (ITree.tsafe nstep nsafe) (at level 0).
#[local] Notation "'tpath'" := (ITree.tpath nstep) (at level 0).

(* [comment removed for export] *)
Fixpoint tsilent {R} (t : itree R) (mo : Model) : Prop :=
  match t with
  | ITree.Ret _ => True
  | ITree.Vis n k =>
      (forall code mo', ~ nexit n mo code mo')
      /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ tsilent (k rsp) mo'
  end.

(* [comment removed for export] *)
Definition silent_node (n : node) : Prop :=
  (forall mo code mo', ~ nexit n mo code mo')
  /\ (forall mo rsp mo' evs, nstep n mo rsp mo' evs -> evs = []).

Fixpoint tforall {R} (P : node -> Prop) (t : itree R) : Prop :=
  match t with
  | ITree.Ret _ => True
  | ITree.Vis n k => P n /\ forall rsp, tforall P (k rsp)
  end.

Lemma tforall_tsilent : forall {R} (t : itree R),
  tforall silent_node t -> forall mo, tsilent t mo.
Proof.
  intros R t. induction t as [r | n k IH]; intros Ht mo; cbn; [exact I|].
  destruct Ht as [[Hne Hns] Hk]. split.
  - intros code mo'. apply Hne.
  - intros rsp mo' evs Hst. split; [eapply Hns; exact Hst | apply IH; apply Hk].
Qed.

Lemma tforall_bind : forall {A B} (P : node -> Prop) (t : itree A) (f : A -> itree B),
  tforall P t -> (forall a, tforall P (f a)) -> tforall P (ITree.bind node t f).
Proof.
  intros A B P t. induction t as [r | n k IH]; intros f Ht Hf; cbn.
  - apply Hf.
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. apply IH; [apply Hk | exact Hf].
Qed.

Lemma tforall_ebind : forall {A B} (P : node -> Prop) (t : itree (ITree.Exc.exc A))
    (f : A -> itree (ITree.Exc.exc B)),
  tforall P t -> (forall a, tforall P (f a)) -> tforall P (ITree.ebind t f).
Proof.
  intros A B P t f Ht Hf. unfold ITree.ebind. apply tforall_bind; [exact Ht|].
  intros [|a]; cbn; [exact I | apply Hf].
Qed.

(* [comment removed for export] *)
Theorem impl_sreach : forall {R} (t : itree R) (Q : R -> machine_state -> Prop) ms mo,
  impl t Q ms ->
  m_halted mo = None -> minv mo -> tsafe t mo -> tsilent t mo ->
  sreach segs
    (fun c => exists r mo', Q r (cfg_ms c) /\ cfg_model c = mo'
                 /\ m_halted mo' = None /\ minv mo' /\ tpath t mo [] r mo')
    (mkCfg ms mo).
Proof.
  intros R t. induction t as [r | n k IH]; intros Q ms mo Himpl Hh Hminv Hsafe Hsil.
  - (* [comment removed for export] *)
    cbn in Himpl.
    eapply sreach_mono; [apply (cj_evt_sreach (Q r) ms mo Hh (minv_lazy mo Hminv) Himpl)|].
    intros [ms1 mo1] [HQ Hmo]; cbn in HQ, Hmo; subst mo1.
    exists r, mo. cbn. repeat split; assumption || reflexivity.
  - (* [comment removed for export] *)
    cbn in Himpl. destruct Hsil as [Hnoexit Hsil]. destruct Hsafe as [Hnsafe Hksafe].
    apply (cj_evt_sreach_k _ ms mo _ Hh (minv_lazy mo Hminv) Himpl).
    intros ms1 [Hat Hk].
    apply sr_step.
    + (* [comment removed for export] *)
      destruct (ITree.ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hminv Hnsafe)
        as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
      * destruct (ITree.ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hminv Hnsafe Hst) as (_ & _ & Hss).
        destruct (Hsil rsp mo' evs Hst) as [-> _].
        eexists. exact Hss.
      * exfalso. exact (Hnoexit code mo' Hex).
    + (* [comment removed for export] *)
      intros evs X Hss.
      destruct (ITree.ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs X Hat Hh Hminv Hnsafe Hss)
        as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & _)].
      * destruct (Hsil rsp mo' evs Hst) as [-> _]. split; [reflexivity | eexists; reflexivity].
      * exfalso. exact (Hnoexit code mo' Hex).
    + (* [comment removed for export] *)
      intros evs c' Hss.
      destruct (ITree.ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hminv Hnsafe Hss)
        as [(rsp & mo' & E & Hst) | (code & mo' & _ & Hex & _)]; [| exfalso; exact (Hnoexit code mo' Hex)].
      injection E as ->.
      destruct (ITree.ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hminv Hnsafe Hst) as (Hh' & Hminv' & _).
      destruct (Hsil rsp mo' evs Hst) as [-> Hsil'].
      eapply sreach_mono.
      * apply (IH rsp Q (ITree.nret ms1 rsp) mo' (Hk rsp) Hh' Hminv' (Hksafe rsp mo' [] Hst) Hsil').
      * intros c (r & mo'' & HQ & Hmo & Hh'' & Hminv'' & Hp).
        exists r, mo''. repeat split; try assumption.
        cbn. exists rsp, mo', [], []. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Corollary impl_sreach_post : forall {R} (t : itree R) (Q : R -> machine_state -> Prop) ms mo
    (MQ : R -> Model -> Prop),
  impl t Q ms ->
  m_halted mo = None -> minv mo -> tsafe t mo -> tsilent t mo ->
  (forall r mo', tpath t mo [] r mo' -> MQ r mo') ->
  sreach segs
    (fun c => exists r, Q r (cfg_ms c) /\ MQ r (cfg_model c)
                 /\ m_halted (cfg_model c) = None /\ minv (cfg_model c))
    (mkCfg ms mo).
Proof.
  intros R t Q ms mo MQ Himpl Hh Hminv Hsafe Hsil HMQ.
  eapply sreach_mono; [apply (impl_sreach t Q ms mo Himpl Hh Hminv Hsafe Hsil)|].
  intros c (r & mo' & HQ & <- & Hh' & Hminv' & Hp).
  exists r. repeat split; try assumption. apply (HMQ _ _ Hp).
Qed.

End Tree.

End WithSegs.
