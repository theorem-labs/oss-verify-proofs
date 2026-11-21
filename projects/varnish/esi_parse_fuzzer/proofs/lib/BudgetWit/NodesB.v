(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Nodes.v: rz_ret_only_copyins_silent and rz_cases restated over BudgetWit.Rzb.rzb, each node with its no-allocation check *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the syscall node lemma takes the read-only-backing fact (RomBase.sys_rob) that node_ok's new third conjunct asks for. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require BWorld ShapeAlg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BWorld OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BudgetWit Require Import Rzb.

Section WithSegs.
Variable segs : list Segment.
Lemma rzb_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  rzb segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  rzb segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hno Hchk Hh' Hlazy Hrob Hc.
  eapply rzb_silent1; [eapply node_ret_only_copyins; eassumption | exact (nonalloc_no ms model x8 Hsvc Hno) | exact Hc].
Qed.
Lemma rzb_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  nonalloc c ->
  (forall i, rzb segs (nx i) (T i)) ->
  rzb segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hna Hc.
  apply (rzb_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rzb_node segs c I (fun _ => []) nx T i0 Hnode Hna Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (rzb_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (rzb_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

End WithSegs.
