(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added the ASan+UBSan allowed-exits module and the halts theorem for that build, copied from this file's own Asan module and theorem (lines 33-37 and 195-203) at commit 874e3397a35. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.HaltsBpS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBp.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.HaltsBp.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpAF.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpBF.

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

Module SpirvToolsSpvtoolsBinaryParserFuzzerHaltsAsanUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End SpirvToolsSpvtoolsBinaryParserFuzzerHaltsAsanUbsanExits.

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
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpAF.base_bpA.
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
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBp.base_bp_abort.
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
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs).
Proof.
  exact OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.HaltsBpS1.halts_bp_plain.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    SpirvToolsSpvtoolsBinaryParserFuzzerHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Asan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpAF.halts_bpA.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    SpirvToolsSpvtoolsBinaryParserFuzzerHaltsUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.HaltsBp.halts_bp_ubsan.
Qed.

Theorem halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_asan_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    SpirvToolsSpvtoolsBinaryParserFuzzerHaltsAsanUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpBF.halts_bpB.
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
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows.RowsBpBF.base_bpB.
Qed.
