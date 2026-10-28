(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.
Require OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Asan.
Require OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Ubsan.
Require OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.AsanUbsan.
Require OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.FinalAsan.
Require OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.FinalHaltsAsan.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module MbedtlsFuzzPkcs7HaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End MbedtlsFuzzPkcs7HaltsAsanExits.
Require OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.FinalU.
Require OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B.FinalBoth.

Theorem strong_universal_error_free_fuzz_pkcs7_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.init_pc OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Asan.M.loaded_segments OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Asan.M.init_pc OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Asan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.FinalAsan.asan_assembled_sanitizer.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Theorem strong_universal_error_free_fuzz_pkcs7_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.init_pc OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Ubsan.M.loaded_segments OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Ubsan.M.init_pc OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Ubsan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.FinalU.ubsan_assembled_shipped.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Theorem strong_universal_error_free_fuzz_pkcs7_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.init_pc OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.AsanUbsan.M.init_pc OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.AsanUbsan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B.FinalBoth.both_assembled_sanitizer.
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
Theorem halts_allowed_mbedtls_fuzz_pkcs7_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    MbedtlsFuzzPkcs7HaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Asan.M.loaded_segments OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Asan.M.init_pc OssFuzzTheorems.mbedtls.fuzz_pkcs7.images.Asan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.FinalHaltsAsan.halts_asan_assembled.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
