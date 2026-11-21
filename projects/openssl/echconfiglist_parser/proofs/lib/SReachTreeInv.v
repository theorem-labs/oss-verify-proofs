(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the node-soundness hypothesis and impl take the node post-state npost, and impl_sreach uses the robustness field of node_sound). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/SReachTree.v; 42 of its 109 lines of code are new or changed and 98 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/SReachTree.v, lines 7-19, 71-87, 111, 116-124, 136-150, 156 and 161-209, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): [SReachTree.impl_sreach] with a configuration invariant
   carried to every reached state.  The invariant is kept by the machine steps between nodes
   ([Inv_ms]) and by each node's step ([Inv_node], asked only where the node's own safety holds, so
   a caller proves it for the calls its tree makes).  The run instance of the heap interface uses it
   to carry the empty overlay over the vDSO text ([VdsoClean.vclean]) through malloc's tree; any
   unit with this [SReachTree] copies it whole. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require ITree Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg SReach SReachTree.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Section Tree.
Context {node : Type}.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> ITree.resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable npost : node -> machine_state -> ITree.resp -> machine_state.
Hypothesis NS : ITree.node_sound node segs at_node nstep nexit minv nsafe npost.
Hypothesis minv_lazy : forall mo, minv mo -> m_vm_lazy mo = [].

Variable Inv : config -> Prop.
Hypothesis Inv_ms : forall ms ms' mo, Exec.msteps segs ms ms' -> Inv (mkCfg ms mo) -> Inv (mkCfg ms' mo).
Hypothesis Inv_node : forall n ms mo rsp mo' evs,
  at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo -> nstep n mo rsp mo' evs ->
  Inv (mkCfg ms mo) -> Inv (mkCfg (npost n ms rsp) mo').

#[local] Notation "'itree'" := (ITree.itree node) (at level 0).
#[local] Notation "'impl'" := (ITree.impl segs at_node npost) (at level 0).
#[local] Notation "'tsafe'" := (ITree.tsafe nstep nsafe) (at level 0).
#[local] Notation "'tpath'" := (ITree.tpath nstep) (at level 0).

Lemma cj_evt_sreach_inv : forall (P : machine_state -> Prop) ms model,
  m_halted model = None -> m_vm_lazy model = [] -> Exec.evt segs P ms -> Inv (mkCfg ms model) ->
  sreach segs (fun c => P (cfg_ms c) /\ cfg_model c = model /\ Inv c) (mkCfg ms model).
Proof.
  intros P ms model Hh Hl (ms' & Hms & HP) HI.
  eapply cj_msteps_sreach; [exact Hh | exact Hl | exact Hms |].
  apply sr_done. cbn. split; [exact HP|]. split; [reflexivity| exact (Inv_ms ms ms' model Hms HI)].
Qed.

Lemma cj_evt_sreach_k_inv : forall (P : machine_state -> Prop) ms model (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] -> Exec.evt segs P ms -> Inv (mkCfg ms model) ->
  (forall ms', P ms' -> Inv (mkCfg ms' model) -> sreach segs Q (mkCfg ms' model)) ->
  sreach segs Q (mkCfg ms model).
Proof.
  intros P ms model Q Hh Hl (ms' & Hms & HP) HI K.
  eapply cj_msteps_sreach; [exact Hh | exact Hl | exact Hms |].
  apply K; [exact HP | exact (Inv_ms _ _ _ Hms HI)].
Qed.

Theorem impl_sreach_inv : forall {R} (t : itree R) (Q : R -> machine_state -> Prop) ms mo,
  impl t Q ms ->
  m_halted mo = None -> minv mo -> tsafe t mo -> tsilent nstep nexit t mo -> Inv (mkCfg ms mo) ->
  sreach segs
    (fun c => exists r mo', Q r (cfg_ms c) /\ cfg_model c = mo'
                 /\ m_halted mo' = None /\ minv mo' /\ tpath t mo [] r mo' /\ Inv c)
    (mkCfg ms mo).
Proof.
  pose proof NS as NSall.
  destruct NSall as [NSblocked NScomplete NSsound NSexit NSprogress NSrob].
  intros R t. induction t as [r | n k IH]; intros Q ms mo Himpl Hh Hminv Hsafe Hsil HI.
  - cbn in Himpl.
    eapply sreach_mono; [apply (cj_evt_sreach_inv (Q r) ms mo Hh (minv_lazy mo Hminv) Himpl HI)|].
    intros [ms1 mo1] (HQ & Hmo & HI1); cbn in HQ, Hmo; subst mo1.
    exists r, mo. cbn. repeat split; assumption || reflexivity.
  - cbn in Himpl. destruct Hsil as [Hnoexit Hsil]. destruct Hsafe as [Hnsafe Hksafe].
    apply (cj_evt_sreach_k_inv _ ms mo _ Hh (minv_lazy mo Hminv) Himpl HI).
    intros ms1 [Hat Hk] HI1.
    apply sr_step.
    + exact (NSrob n ms1 mo Hat Hh Hminv Hnsafe).
    + destruct (NSprogress n ms1 mo Hat Hh Hminv Hnsafe)
        as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
      * destruct (NSsound n ms1 mo rsp mo' evs Hat Hh Hminv Hnsafe Hst) as (_ & _ & Hss).
        destruct (Hsil rsp mo' evs Hst) as [-> _].
        eexists. exact Hss.
      * exfalso. exact (Hnoexit code mo' Hex).
    + intros evs X Hss.
      destruct (NScomplete n ms1 mo evs X Hat Hh Hminv Hnsafe Hss)
        as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & _)].
      * destruct (Hsil rsp mo' evs Hst) as [-> _]. split; [reflexivity | eexists; reflexivity].
      * exfalso. exact (Hnoexit code mo' Hex).
    + intros evs c' Hss.
      destruct (NScomplete n ms1 mo evs (SNext c') Hat Hh Hminv Hnsafe Hss)
        as [(rsp & mo' & E & Hst) | (code & mo' & _ & Hex & _)]; [| exfalso; exact (Hnoexit code mo' Hex)].
      injection E as ->.
      destruct (NSsound n ms1 mo rsp mo' evs Hat Hh Hminv Hnsafe Hst) as (Hh' & Hminv' & _).
      destruct (Hsil rsp mo' evs Hst) as [-> Hsil'].
      eapply sreach_mono.
      * apply (IH rsp Q (npost n ms1 rsp) mo' (Hk rsp) Hh' Hminv' (Hksafe rsp mo' [] Hst) Hsil'
                  (Inv_node n ms1 mo rsp mo' [] Hat Hh Hminv Hnsafe Hst HI1)).
      * intros c (r & mo'' & HQ & Hmo & Hh'' & Hminv'' & Hp & HIc).
        exists r, mo''. repeat split; try assumption.
        cbn. exists rsp, mo', [], []. repeat split; assumption.
Qed.

Corollary impl_sreach_post_inv : forall {R} (t : itree R) (Q : R -> machine_state -> Prop) ms mo
    (MQ : R -> Model -> Prop),
  impl t Q ms ->
  m_halted mo = None -> minv mo -> tsafe t mo -> tsilent nstep nexit t mo -> Inv (mkCfg ms mo) ->
  (forall r mo', tpath t mo [] r mo' -> MQ r mo') ->
  sreach segs
    (fun c => exists r, Q r (cfg_ms c) /\ MQ r (cfg_model c)
                 /\ m_halted (cfg_model c) = None /\ minv (cfg_model c) /\ Inv c)
    (mkCfg ms mo).
Proof.
  intros R t Q ms mo MQ Himpl Hh Hminv Hsafe Hsil HI HMQ.
  eapply sreach_mono; [apply (impl_sreach_inv t Q ms mo Himpl Hh Hminv Hsafe Hsil HI)|].
  intros c (r & mo' & HQ & <- & Hh' & Hminv' & Hp & HIc).
  exists r. repeat split; try assumption. apply (HMQ _ _ Hp).
Qed.

End Tree.
End WithSegs.
