(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the silent steps take the pending-syscall fact that RomBase.sys_rob_instr turns into the read-only-backing premise, and the sanitizer lemmas carry the flag of the flagged relation SpinAlg.srealizesM. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import CatSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg. (* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import AsanAcct SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.node_ok segs.
Proof. reflexivity. Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    ms_svc_pending (cfg_ms c) = None ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hsvc Hr => rz_silent1 segs c c' T Hn (RomBase.sys_rob_instr segs c Hsvc) Hr.

Theorem rz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs (mkCfg ms model) T.
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
      realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.
(* [comment removed for export] *)
Let SP_of (b : bool) (T : TSet) : config -> Prop := fun c => srealizesM segs b c T.

(* the srealizes side takes the same shape so it can share [rz_step_restricted]; (B2):
   [srz_node] asks [RomBase.sys_rob] too, discharged from the svc fact exactly as
   [P_of_silent1] does *)
Let SP_of_silent1 (b : bool) (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    ms_svc_pending (cfg_ms c) = None ->
    SP_of b T c' -> SP_of b T c :=
  fun c c' Hn Hsvc Hr => srz_silent1 segs c c' T Hn (RomBase.sys_rob_instr segs c Hsvc) Hr.

Theorem srz_step_restricted_T {b : bool} : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizesM segs b (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizesM segs b (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (SP_of b T) (SP_of_silent1 b T) A ms msr' model).
Qed.

Theorem srz_msteps_restricted_T {b : bool} : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizesM segs b (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizesM segs b (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of b T) (SP_of_silent1 b T) A ms msr' model).
Qed.
End WithSegs.
