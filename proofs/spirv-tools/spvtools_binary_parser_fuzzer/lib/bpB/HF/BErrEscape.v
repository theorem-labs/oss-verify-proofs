(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BExitSim BPropExec BCatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section WithFP1.
Context {fx : DFP}.

Section WithSegs.
Variable segs : list Segment.

End WithSegs.

Section OmniWithSegs.
Variable segs : list Segment.

End OmniWithSegs.

Section AllErrorWithSegs.
Variable segs : list Segment.

End AllErrorWithSegs.

Section NoUnmodeledWithSegs.
Variable segs : list Segment.

End NoUnmodeledWithSegs.

End WithFP1.
