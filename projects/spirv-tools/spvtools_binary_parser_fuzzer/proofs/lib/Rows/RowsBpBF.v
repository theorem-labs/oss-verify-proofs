(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added halts_bpB, copied from projects/spirv-tools/spvtools_binary_parser_fuzzer/proofs/lib/Rows/RowsBpAF.v line 20 at commit 874e3397a35, with TopA.as_realizes_spec_A_final replaced by TopB.as_realizes_spec_B_final. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed FinInput Classifier Measure.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final Require FinalS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows Require HaltsBpDrvS1 RowsBpB.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB Require TopB.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition base_bpB := RowsBpB.base_bpB_abort FinalS1.lib_contract_S1_final TopB.as_realizes_spec_B_final.
Definition halts_bpB := RowsBpB.halts_bpB TopB.as_realizes_spec_B_final.
