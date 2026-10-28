(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BPropExec BCatExec BCatSim BSeqExec BStoreOk BSimInv BExitSim BShapeAlg BReach BSymExec BFrame BSymExec2 BSymExec2Sound BSymRun BSymDrive BazyRestrict BazyRestrictRun BazyRestrictAlg BazySR.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.

Context {SC : StepCfg}.
Context {fx : DFP}.
Variables L S Zr : list (word * word).

End WithSegs.
