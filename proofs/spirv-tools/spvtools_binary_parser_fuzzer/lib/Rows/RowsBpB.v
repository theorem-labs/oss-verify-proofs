(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed FinInput Classifier Measure.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase ShapeAlg SRealizes SRzAbort HaltsKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common Require Import ClassifierRows BoundRows.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBHalts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import LibContractS1 S1Spec BaseSpecNk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows Require Import HaltsBpDrvS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA Require Import BaseAsanA.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation SRC := (mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs) (only parsing).
Notation TGT := (mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.phdrs) (only parsing).
Notation SRCO := (mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs) (only parsing).
Notation TGTO := (mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.phdrs) (only parsing).

Section RowsB.
  Hypothesis LIB1 : lib_contract_S1.
  Hypothesis ASB : as_realizes_spec_B.

  Theorem base_bpB_abort :
    strong_universal_error_free_T_scfg_budgets_abort CFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target SRC TGT.
  Proof. exact (base_both_glue LIB1 ASB). Qed.
End RowsB.
