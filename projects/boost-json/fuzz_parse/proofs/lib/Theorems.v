(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The three equivalence theorems for boost-json fuzz_parse, with their proofs.

   Each theorem states that the uninstrumented build (the Plain image) and one
   sanitizer build (the Asan, Ubsan or AsanUbsan image) are equivalent and
   error-free. The statements asan_agrees, ubsan_agrees and asan_ubsan_agrees
   are proved from them, so their names and types must not change. *)

(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.boost_json.fuzz_parse.images.Plain.
Require OSSVerify.boost_json.fuzz_parse.images.Asan.
Require OSSVerify.boost_json.fuzz_parse.images.Ubsan.
Require OSSVerify.boost_json.fuzz_parse.images.AsanUbsan.

(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require BaseUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require BaseAsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require BaseBoth.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require PlainClosed UbsanClosed.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require HaltsAsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require HaltsBoth.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module BoostJsonHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End BoostJsonHaltsPlainExits.

Module BoostJsonHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End BoostJsonHaltsAsanExits.

Module BoostJsonHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End BoostJsonHaltsUbsanExits.

Module BoostJsonHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End BoostJsonHaltsBothExits.

Theorem strong_universal_error_free_boost_json_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.Plain.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.Plain.M.init_pc OSSVerify.boost_json.fuzz_parse.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.Asan.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.Asan.M.init_pc OSSVerify.boost_json.fuzz_parse.images.Asan.M.phdrs).
Proof.
exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top.BaseAsan.asan_base.
Qed.

Theorem strong_universal_error_free_boost_json_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.Plain.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.Plain.M.init_pc OSSVerify.boost_json.fuzz_parse.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.init_pc OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top.BaseUbsan.ubsan_base.
Qed.

Theorem strong_universal_error_free_boost_json_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.Plain.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.Plain.M.init_pc OSSVerify.boost_json.fuzz_parse.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.AsanUbsan.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.AsanUbsan.M.init_pc OSSVerify.boost_json.fuzz_parse.images.AsanUbsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top.BaseBoth.both_base.
Qed.

Theorem halts_allowed_boost_json_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    BoostJsonHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.Asan.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.Asan.M.init_pc OSSVerify.boost_json.fuzz_parse.images.Asan.M.phdrs).
Proof.
exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top.HaltsAsan.asan_halts.
Qed.

Theorem halts_allowed_boost_json_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    BoostJsonHaltsBothExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.AsanUbsan.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.AsanUbsan.M.init_pc OSSVerify.boost_json.fuzz_parse.images.AsanUbsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top.HaltsBoth.both_halts.
Qed.

Theorem halts_allowed_boost_json_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    BoostJsonHaltsPlainExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.Plain.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.Plain.M.init_pc OSSVerify.boost_json.fuzz_parse.images.Plain.M.phdrs).
Proof.
exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top.PlainClosed.plain_halts_closed.
Qed.

Theorem halts_allowed_boost_json_halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    BoostJsonHaltsUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.loaded_segments OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.init_pc OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top.UbsanClosed.ubsan_halts_closed.
Qed.
