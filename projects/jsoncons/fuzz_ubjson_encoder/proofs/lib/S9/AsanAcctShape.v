(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ShapeAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AsanAcct SpinAlg.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.

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

Let P_of_leaf (T : TSet) (BOFF : bm_on = false) : bm_on = true -> forall c c', budget_refused_at segs c -> P_of T c' -> P_of T c.
Proof. intros Hon. rewrite BOFF in Hon. discriminate Hon. Qed.

Theorem rz_step_restricted_T : bm_on = false -> forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros BOFF A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (P_of T) (P_of_silent1 T) (P_of_leaf T BOFF) A ms msr' model).
Qed.

Theorem rz_msteps_restricted_T : bm_on = false -> forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      realizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros BOFF A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (P_of T) (P_of_silent1 T) (P_of_leaf T BOFF) A ms msr' model).
Qed.

Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs scfg c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    ms_svc_pending (cfg_ms c) = None ->
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hsvc Hn Hr => srz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn) Hr.

Let SP_of_leaf (T : TSet) : bm_on = true -> forall c c', budget_refused_at segs c -> SP_of T c' -> SP_of T c :=
  fun Hon c c' Hb Hr => srz_brefused segs scfg c T Hon Hb (srealizes_nonempty segs scfg c' T Hr).

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
  exact (rz_step_restricted segs H HH Hwx (SP_of T) (SP_of_silent1 T) (SP_of_leaf T) A ms msr' model).
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
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) (SP_of_leaf T) A ms msr' model).
Qed.
End WithSegs.

End FPX_1.
