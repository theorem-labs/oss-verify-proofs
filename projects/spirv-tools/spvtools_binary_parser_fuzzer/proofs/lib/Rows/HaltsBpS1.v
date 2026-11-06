(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows Require Import HaltsBpDrvS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final Require FinalS1.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_HaltsBpS1 () := "C59OSSVerify5KrLib4Rows<HaltsBpDrvS1Bhalts_bp_plain_drvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Final7FinalS1Elib_contract_S1_finalC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Theorem halts_bp_plain :
  halts_allowed_T_scfg_budgets Run.forced_only_cfg ShippedBudgets.lim_source CODES02
    (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsBpS1 ()) [] "p;1g0000j10Tg0019#0o"). Qed.
