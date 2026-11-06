(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg PropExec ShapeAlg SpinAlg AgentLib ExitSim AllocSim Nodes MmapSim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Export AsanRefNodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma srz_silent_all {SC : StepCfg} : forall segs c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes segs (nx i) T) ->
  srealizes segs c T.
Proof.
  intros segs c I nx T i0 Hnode Hc.
  apply (srz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node segs c I (fun _ => []) nx (fun _ => T) i0 Hnode Hc).
  - intros tr. unfold t_alt. split.
    + intros [i H]. exact (proj1 (t_emit_nil_eq T (srealizes_nonempty segs _ _ (Hc i)) tr) H).
    + intros H. exists i0. exact (proj2 (t_emit_nil_eq T (srealizes_nonempty segs _ _ (Hc i0)) tr) H).
Qed.
