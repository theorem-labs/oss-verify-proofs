(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed FinInput Classifier Measure.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final Require FinalS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows Require HaltsBpDrvS1 RowsBpA.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA Require TopA.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition base_bpA := RowsBpA.base_bpA_abort FinalS1.lib_contract_S1_final TopA.as_realizes_spec_A_final.
Definition halts_bpA := RowsBpA.halts_bpA TopA.as_realizes_spec_A_final.
