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
Require OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.
Require OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Asan.
Require OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Ubsan.
Require OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.AsanUbsan.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require YZ00 YZ01.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require YZ03.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Halts_tra Halts_trb.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require HaltsPlainFO.

Module HaltsCfgMayFail <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.may_fail_cfg.
End HaltsCfgMayFail.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module CgifCgifRgbFuzzerHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End CgifCgifRgbFuzzerHaltsAsanExits.

Module CgifCgifRgbFuzzerHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End CgifCgifRgbFuzzerHaltsBothExits.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require YZ00 YZ01 UZZ0.

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
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem strong_universal_error_free_cgif_rgb_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Asan.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Asan.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Asan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.YZ00.cgif_rgb_fuzzer_asan_equiv_sanitizer.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem strong_universal_error_free_cgif_rgb_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Ubsan.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Ubsan.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Ubsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.UZZ0.cgif_rgb_fuzzer_ubsan_equiv_shipped.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem strong_universal_error_free_cgif_rgb_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.YZ01.cgif_rgb_fuzzer_both_equiv_sanitizer.
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
Theorem halts_allowed_cgif_cgif_rgb_fuzzer_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg
    HaltsCfgMayFail.cfg
    LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.AnyExit.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.YZ03.halts_src2.
Qed.

Theorem halts_allowed_cgif_cgif_rgb_fuzzer_halts_plain_forced_only :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.HaltsFO.codes02
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Plain.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.HaltsPlainFO.halts_plain_forced_only.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_cgif_cgif_rgb_fuzzer_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    CgifCgifRgbFuzzerHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Asan.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Asan.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.Asan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.Halts_tra.halts_allowed_cgif_cgif_rgb_fuzzer_halts_asan_closed.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_cgif_cgif_rgb_fuzzer_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    CgifCgifRgbFuzzerHaltsBothExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.Halts_trb.halts_allowed_cgif_cgif_rgb_fuzzer_halts_both_closed.
Qed.
