(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.
Require OssFuzzTheorems.bzip2.bzip2_compress_target.images.Asan.
Require OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Require OssFuzzTheorems.bzip2.bzip2_compress_target.images.AsanUbsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require FilingA0 FilingB0 FilingU0.

Theorem strong_universal_error_free_bzip2_compress_target_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.loaded_segments OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.init_pc OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.bzip2.bzip2_compress_target.images.Asan.M.loaded_segments OssFuzzTheorems.bzip2.bzip2_compress_target.images.Asan.M.init_pc OssFuzzTheorems.bzip2.bzip2_compress_target.images.Asan.M.phdrs).
Proof.
exact FilingA0.compress_asan_san.
Qed.

Theorem strong_universal_error_free_bzip2_compress_target_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.loaded_segments OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.init_pc OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.bzip2.bzip2_compress_target.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.bzip2.bzip2_compress_target.images.AsanUbsan.M.init_pc OssFuzzTheorems.bzip2.bzip2_compress_target.images.AsanUbsan.M.phdrs).
Proof.
exact FilingB0.compress_both_san.
Qed.

Theorem strong_universal_error_free_bzip2_compress_target_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.loaded_segments OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.init_pc OssFuzzTheorems.bzip2.bzip2_compress_target.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.M.loaded_segments OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.M.init_pc OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.M.phdrs).
Proof.
exact FilingU0.compress_ubsan_std.
Qed.
