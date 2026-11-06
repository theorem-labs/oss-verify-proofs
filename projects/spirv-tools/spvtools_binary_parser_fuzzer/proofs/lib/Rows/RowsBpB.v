(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added must_exit_bpB and halts_bpB, copied from projects/spirv-tools/spvtools_binary_parser_fuzzer/proofs/lib/Rows/RowsBpA.v lines 36-51 at commit 874e3397a35, with ASA replaced by this file's ASB. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed FinInput Classifier Measure.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase ShapeAlg SRealizes SRzAbort HaltsKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common Require Import ClassifierRows BoundRows.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBHalts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import LibContractS1 S1Spec BaseSpecNk.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows Require Import HaltsBpDrvS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA Require Import BaseAsanA.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation SRC := (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs) (only parsing).
Notation TGT := (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.phdrs) (only parsing).
Notation SRCO := (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs) (only parsing).
Notation TGTO := (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.phdrs) (only parsing).

Section RowsB.
  Hypothesis LIB1 : lib_contract_S1.
  Hypothesis ASB : as_realizes_spec_B.

  Theorem base_bpB_abort :
    strong_universal_error_free_T_scfg_budgets_abort CFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target SRC TGT.
  Proof. exact (base_both_glue LIB1 ASB). Qed.

  Lemma must_exit_bpB : forall en inp, valid_entry TGT en inp -> valid_input inp ->
    must_exit_in_scfg forced_only_cfg CODES02 TGT target_alloc_limit en inp.
  Proof.
    intros [sp brk mbase rnd] inp Hen Hinp. cbn [must_exit_in_scfg].
    pose proof (ASB (mkEntry sp brk mbase rnd) inp Hen (valid_input_either_of_valid_input inp Hinp)) as HS.
    cbn [en_sp en_brk en_mmap_base en_draw] in HS.
    exact (srealizes_must_exit_le _ forced_only_cfg CODES02 _ _ cfg_le_forced_only_CFG HS (spec_nokill _ _) (spec_exits_02 _ _)
             (init_config_not_halted _ _ _ _ _ _ _ _ _)).
  Qed.

  Theorem halts_bpB : halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source CODES02 TGT.
  Proof.
    apply (halts_budgets_of_larger forced_only_cfg CODES02 TGT ShippedBudgets.lim_source target_alloc_limit).
    - vm_compute. discriminate.
    - exact must_exit_bpB.
  Qed.
End RowsB.
