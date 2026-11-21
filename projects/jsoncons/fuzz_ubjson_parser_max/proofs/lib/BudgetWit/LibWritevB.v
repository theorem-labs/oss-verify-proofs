(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from fuzz_bigint's LibWritev.v, whose twinned declarations have the same statements as this harness's LibWritev.v (whose statements are TCodec-encoded): the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
  SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes FileSim AgentLib AgentNodes.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import LibWritev.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import SpinAlgB.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Section FPX_1.
Context {fx : FPState}.
Lemma rz_wall_b : forall segs scfg c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  SpinAlgB.rzb segs scfg c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  SpinAlgB.rzb segs scfg c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs scfg c ch bs K Hnb HK H. eapply SpinAlgB.rzb_conseq; [exact H | apply t_alt_wall; assumption].
Qed.
End FPX_1.
