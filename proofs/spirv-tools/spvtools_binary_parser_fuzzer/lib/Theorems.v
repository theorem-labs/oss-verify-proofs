(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.
Require OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Require OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.HaltsBpS1.
Require OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBp.
Require OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.HaltsBp.
Require OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpAF.
Require OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpBF.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module SpirvToolsSpvtoolsBinaryParserFuzzerHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End SpirvToolsSpvtoolsBinaryParserFuzzerHaltsPlainExits.

Module SpirvToolsSpvtoolsBinaryParserFuzzerHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End SpirvToolsSpvtoolsBinaryParserFuzzerHaltsAsanExits.

Module SpirvToolsSpvtoolsBinaryParserFuzzerHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End SpirvToolsSpvtoolsBinaryParserFuzzerHaltsUbsanExits.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Theorem strong_universal_error_free_spvtools_binary_parser_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpAF.base_bpA.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Theorem strong_universal_error_free_spvtools_binary_parser_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBp.base_bp_abort.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    SpirvToolsSpvtoolsBinaryParserFuzzerHaltsPlainExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.HaltsBpS1.halts_bp_plain.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    SpirvToolsSpvtoolsBinaryParserFuzzerHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpAF.halts_bpA.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    SpirvToolsSpvtoolsBinaryParserFuzzerHaltsUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.HaltsBp.halts_bp_ubsan.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Theorem strong_universal_error_free_spvtools_binary_parser_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpBF.base_bpB.
Qed.
