(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct SpinAlg.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.pnode_ok segs.
Proof. reflexivity. Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs scfg c T.

Let P_of_silent1 (T : TSet) : forall c c',
    ms_svc_pending (cfg_ms c) = None ->
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hsvc Hn Hr => rz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn) Hr.

Theorem rz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.

Theorem rz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      realizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.

Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs scfg c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    ms_svc_pending (cfg_ms c) = None ->
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hsvc Hn Hr => srz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn) Hr.

Theorem srz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.

Theorem srz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.

End FPX_1.
