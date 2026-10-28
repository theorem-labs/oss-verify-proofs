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
Require OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.
Require OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Asan.
Require OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Ubsan.
Require OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.AsanUbsan.

Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmHaltsPlainC.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmCasanBase.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmCbothBase.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmHaltsAsanC.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmHaltsBothC.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmCubsanBase.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module JsonconsFuzzJsonCursorHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonCursorHaltsPlainExits.

Module JsonconsFuzzJsonCursorHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonCursorHaltsAsanExits.

Module JsonconsFuzzJsonCursorHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonCursorHaltsBothExits.

Theorem strong_universal_error_free_fuzz_json_cursor_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Asan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Asan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Asan.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmCasanBase.PmCasanBase.base_abort).
Qed.

Theorem strong_universal_error_free_fuzz_json_cursor_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.AsanUbsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.AsanUbsan.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmCbothBase.PmCbothBase.base_abort).
Qed.

Theorem halts_allowed_jsoncons_fuzz_json_cursor_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    JsonconsFuzzJsonCursorHaltsPlainExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmHaltsPlainC.PmHaltsPlainC.halts_plain).
Qed.

Theorem halts_allowed_jsoncons_fuzz_json_cursor_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    JsonconsFuzzJsonCursorHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Asan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Asan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Asan.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmHaltsAsanC.PmHaltsAsanC.halts_asan).
Qed.

Theorem halts_allowed_jsoncons_fuzz_json_cursor_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    JsonconsFuzzJsonCursorHaltsBothExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.AsanUbsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.AsanUbsan.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmHaltsBothC.PmHaltsBothC.halts_both).
Qed.

Theorem strong_universal_error_free_fuzz_json_cursor_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Ubsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Ubsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Ubsan.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg.PmCubsanBase.PmCubsanBase.base_abort).
Qed.
