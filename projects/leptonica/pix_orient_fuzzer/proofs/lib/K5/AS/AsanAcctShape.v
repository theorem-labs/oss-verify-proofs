(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of rz_step_restricted_T, rz_msteps_restricted_T, srz_step_restricted_T, srz_msteps_restricted_T replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import CatSim.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg. (* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanAcct SpinAlg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Cfg Require RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

(* [ShapeAlg.node_ok] is [AsanAcct.node_ok] and [RomBase.sys_rob] *)
Let P_of_silent1 (T : TSet) : forall ms model c', ms_svc_pending ms = None ->
    AsanAcct.node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T (mkCfg ms model) :=
  fun ms model c' Hs Hn Hr =>
    rz_silent1 segs (mkCfg ms model) c' T
      (ShapeAlg.node_ok_of_c segs (mkCfg ms model) unit _ _ Hn (ShapeAlg.rob_instr segs ms model Hs)) Hr.

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
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall ms model c', ms_svc_pending ms = None ->
    AsanAcct.node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T (mkCfg ms model) :=
  fun ms model c' Hs Hn Hr =>
    srz_silent1 segs (mkCfg ms model) c' T
      (ShapeAlg.node_ok_of_c segs (mkCfg ms model) unit _ _ Hn (ShapeAlg.rob_instr segs ms model Hs)) Hr.

Theorem srz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
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
      srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.
