(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Plain.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Asan.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.
Require OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require RU_FinalCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require RA_FinalCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require RB_FinalCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require HaltsFinalR.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require HaltsFinalU.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require HaltsFinalA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require HaltsFinalB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module YajlRubyJsonFuzzerHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End YajlRubyJsonFuzzerHaltsPlainExits.

Module YajlRubyJsonFuzzerHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End YajlRubyJsonFuzzerHaltsAsanExits.

Module YajlRubyJsonFuzzerHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End YajlRubyJsonFuzzerHaltsUbsanExits.

Module YajlRubyJsonFuzzerHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End YajlRubyJsonFuzzerHaltsBothExits.

Theorem strong_universal_error_free_json_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.phdrs).
Proof.
exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top.RA_FinalCfg.strong_universal_error_free_json_fuzzer_asan.
Qed.

Theorem strong_universal_error_free_json_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.phdrs).
Proof.
apply LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_of_scfg.
exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top.RU_FinalCfg.strong_universal_error_free_json_fuzzer_ubsan.
Qed.

Theorem strong_universal_error_free_json_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top.RB_FinalCfg.strong_universal_error_free_json_fuzzer_both.
Qed.

Theorem halts_allowed_yajl_ruby_json_fuzzer_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    YajlRubyJsonFuzzerHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.phdrs).
Proof.
exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top.HaltsFinalA.halts_asan.
Qed.

Theorem halts_allowed_yajl_ruby_json_fuzzer_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    YajlRubyJsonFuzzerHaltsBothExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top.HaltsFinalB.halts_both.
Qed.

Theorem halts_allowed_yajl_ruby_json_fuzzer_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    YajlRubyJsonFuzzerHaltsPlainExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs).
Proof.
exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top.HaltsFinalR.halts_plain.
Qed.

Theorem halts_allowed_yajl_ruby_json_fuzzer_halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    YajlRubyJsonFuzzerHaltsUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top.HaltsFinalU.halts_ubsan.
Qed.
