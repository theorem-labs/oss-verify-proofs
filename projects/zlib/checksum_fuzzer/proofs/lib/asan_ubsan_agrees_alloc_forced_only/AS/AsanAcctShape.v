(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import CatSim.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import ShapeAlg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AsanAcct SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.
(* the run's tail (the vDSO pair), never executable.
   (s)realizes is over the run's list segs ++ tail; msteps (the restricted world) stays over segs. *)
Variable tail : list Segment.
Hypothesis Htail : Forall (fun s => seg_executable s = false) tail.

Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.node_ok segs.
Proof. reflexivity. Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes (segs ++ tail) c T.

Let P_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok (segs ++ tail) c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hr => rz_silent1 (segs ++ tail) c c' T Hn Hr.

Theorem rz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes (segs ++ tail) (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes (segs ++ tail) (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx tail Htail (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.

Theorem rz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      realizes (segs ++ tail) (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes (segs ++ tail) (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx tail Htail (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes (segs ++ tail) c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok (segs ++ tail) c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hn Hr => srz_silent1 (segs ++ tail) c c' T Hn Hr.

Theorem srz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes (segs ++ tail) (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes (segs ++ tail) (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx tail Htail (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.

Theorem srz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes (segs ++ tail) (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes (segs ++ tail) (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx tail Htail (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.
