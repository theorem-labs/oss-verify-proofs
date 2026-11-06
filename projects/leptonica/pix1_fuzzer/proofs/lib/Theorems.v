(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require OSSVerify.leptonica.pix1_fuzzer.images.Plain.
Require OSSVerify.leptonica.pix1_fuzzer.images.Asan.
Require OSSVerify.leptonica.pix1_fuzzer.images.Ubsan.
Require OSSVerify.leptonica.pix1_fuzzer.images.AsanUbsan.
Require OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Top.BasePix1Asan.
Require OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Top.BasePix1Ubsan.
Require OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Top.BasePix1Both.
Require OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.BudgetBridge.

Theorem strong_universal_error_free_pix1_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.loaded_segments OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.init_pc OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.leptonica.pix1_fuzzer.images.Asan.M.loaded_segments OSSVerify.leptonica.pix1_fuzzer.images.Asan.M.init_pc OSSVerify.leptonica.pix1_fuzzer.images.Asan.M.phdrs).
Proof.
exact (OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.BudgetBridge.sue_budgets_source_shrink _ _ _ _ _ _ OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.BudgetBridge.sanitizer_le_shipped OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Top.BasePix1Asan.strong_universal_error_free_pix1_fuzzer_asan).
Qed.

Theorem strong_universal_error_free_pix1_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.loaded_segments OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.init_pc OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.leptonica.pix1_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.leptonica.pix1_fuzzer.images.Ubsan.M.init_pc OSSVerify.leptonica.pix1_fuzzer.images.Ubsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Top.BasePix1Ubsan.strong_universal_error_free_pix1_fuzzer_ubsan.
Qed.

Theorem strong_universal_error_free_pix1_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.loaded_segments OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.init_pc OSSVerify.leptonica.pix1_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.leptonica.pix1_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.leptonica.pix1_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.leptonica.pix1_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact (OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.BudgetBridge.sue_budgets_source_shrink _ _ _ _ _ _ OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.BudgetBridge.sanitizer_le_shipped OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Top.BasePix1Both.strong_universal_error_free_pix1_fuzzer_both).
Qed.
