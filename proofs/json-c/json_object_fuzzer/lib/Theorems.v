(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.
Require OssFuzzTheorems.json_c.json_object_fuzzer.images.Asan.
Require OssFuzzTheorems.json_c.json_object_fuzzer.images.AsanUbsan.
Require OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.AT Require TargetJo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.ATB Require TargetJo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbsanDone.

Theorem strong_universal_error_free_json_object_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Asan.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Asan.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Asan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.AT.TargetJo.json_object_asan_ba.
Qed.

Theorem strong_universal_error_free_json_object_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.ATB.TargetJo.json_object_both_ba.
Qed.

Theorem strong_universal_error_free_json_object_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top.TopUbsanDone.json_object_ubsan_ba_closed.
Qed.
