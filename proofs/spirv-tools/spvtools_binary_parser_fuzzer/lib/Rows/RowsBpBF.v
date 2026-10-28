(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed FinInput Classifier Measure.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final Require FinalS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows Require HaltsBpDrvS1 RowsBpB.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB Require TopB.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition base_bpB := RowsBpB.base_bpB_abort FinalS1.lib_contract_S1_final TopB.as_realizes_spec_B_final.
