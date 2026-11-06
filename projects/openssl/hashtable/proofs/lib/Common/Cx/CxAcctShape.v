(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CatSim ShapeAlg AsanAcct SpinAlg AsanAcctShape CxRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Let CP_of (T : TSet) : config -> Prop := fun c => crz segs c T.

Let CP_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    CP_of T c' -> CP_of T c :=
  fun c c' Hn Hr => crz_silent1 segs c c' T Hn Hr.

Theorem crz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  crz segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  crz segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (CP_of T) (CP_of_silent1 T) A ms msr' model).
Qed.

Theorem crz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      crz segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  crz segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (CP_of T) (CP_of_silent1 T) A ms msr' model).
Qed.

End WithSegs.
