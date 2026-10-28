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
Require OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.
Require OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Asan.
Require OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Ubsan.
Require OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.BsonPmAsanBase.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.BsonPmHalts.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.BsonPmUbsanTop.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.BsonPmAsanBase_b.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module JsonconsFuzzBsonParserMaxHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonParserMaxHaltsPlainExits.

Theorem strong_universal_error_free_fuzz_bson_parser_max_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Asan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Asan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Asan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.BsonPmAsanBase.bson_pm_asan_base_abort.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_jsoncons_fuzz_bson_parser_max_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    JsonconsFuzzBsonParserMaxHaltsPlainExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.BsonPmHalts.bson_pm_halts_plain.
Qed.

Theorem strong_universal_error_free_fuzz_bson_parser_max_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Ubsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Ubsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Ubsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.BsonPmUbsanTop.bson_pm_ubsan_final_abort.
Qed.

Theorem strong_universal_error_free_fuzz_bson_parser_max_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.BsonPmAsanBase_b.bson_pm_asan_base_abort.
Qed.
