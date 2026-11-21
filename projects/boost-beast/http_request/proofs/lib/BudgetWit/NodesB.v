(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Nodes.v: rz_ret_only_copyins_silent and rz_cases restated over BudgetWit.Rzb.rzb, each node with its no-allocation check *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg RelSpec SimInv ExitSim CatSim FileSim ShapeAlg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Nodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import Rzb.
From OSSVerify.Proofs.boost_beast.http_request.lib.Common.Cfg Require RomBase.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.
Lemma rzb_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  rzb segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  injected_arm (bv_unsigned x8) = None ->
  rzb segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hrob Hchk Hh' Hlazy Hc Hna.
  eapply rzb_silent1; [eapply node_ret_only_copyins; eassumption | exact Hrob
                      | exact (nonalloc_no ms model x8 Hsvc Hna) | exact Hc].
Qed.
Lemma rzb_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  nonalloc c ->
  (forall i, rzb segs (nx i) (T i)) ->
  rzb segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hrob Hna Hc.
  apply (rzb_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rzb_node segs c I (fun _ => []) nx T i0 Hnode Hrob Hna Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (rzb_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (rzb_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.
End WithSegs.
