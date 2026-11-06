(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK05.v, with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK15.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YK18.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section a.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.
Lemma node_ok_same : YK04.node_ok segs = YK15.node_ok segs.
Proof. reflexivity. Qed.
Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.
Let P_of_silent1 (T : TSet) : forall c c',
YK04.node_ok segs c unit (fun _ => []) (fun _ => c') ->
P_of T c' -> P_of T c :=
fun c c' Hn Hr => rz_silent1 segs c c' T Hn Hr.
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
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.
Let SP_of_silent1 (T : TSet) : forall c c',
YK04.node_ok segs c unit (fun _ => []) (fun _ => c') ->
SP_of T c' -> SP_of T c :=
fun c c' Hn Hr => srz_silent1 segs c c' T Hn Hr.
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
End a.
