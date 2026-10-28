(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.

Require OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Asan.
Require OssFuzzTheorems.cgif.cgif_file_fuzzer.images.AsanUbsan.
Require OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Ubsan.
Require OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.
Require OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A.AZ05.
Require OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.UZ03.
Require OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.YZ05.
Require OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.Halts_tfib.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module CgifCgifFileFuzzerHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End CgifCgifFileFuzzerHaltsBothExits.

Theorem strong_universal_error_free_cgif_file_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Asan.M.loaded_segments OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Asan.M.init_pc OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Asan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A.AZ05.strong_universal_error_free_cgif_file_fuzzer_asan_closed.
Qed.

Theorem strong_universal_error_free_cgif_file_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Ubsan.M.loaded_segments OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Ubsan.M.init_pc OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Ubsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.UZ03.strong_universal_error_free_cgif_file_fuzzer_ubsan.
Qed.

Theorem strong_universal_error_free_cgif_file_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.cgif.cgif_file_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_file_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.cgif.cgif_file_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.cgif.cgif_file_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.YZ05.strong_universal_error_free_cgif_file_fuzzer_both_closed.
Qed.

Theorem halts_allowed_cgif_cgif_file_fuzzer_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    CgifCgifFileFuzzerHaltsBothExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_file_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.cgif.cgif_file_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.cgif.cgif_file_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.Halts_tfib.halts_allowed_cgif_cgif_file_fuzzer_halts_both_closed.
Qed.
