(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import
  PropExec SimInv ExitSim CatSim CatExec SeqExec StreamExec FileSim ShapeAlg ShapeAlgCfg AgentLib AgentNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithCfg.
Context {fx : PropExec.FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Definition cfg_nonalloc_on : Prop :=
  sc_fs cfg = true /\ sc_fd cfg = true /\ sc_net cfg = true /\ sc_cred cfg = true /\ sc_intr cfg = true.

End WithCfg.
