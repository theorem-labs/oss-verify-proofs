(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: adds the halting theorems of the two AddressSanitizer builds, coturn_fuzzstunclient_asan_halts and coturn_fuzzstunclient_asan_ubsan_halts. *)
(* [comment removed for export] *)


From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.Asan.
Require OSSVerify.coturn.FuzzStunClient.images.Ubsan.
Require OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.

From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require UbsanTop.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require BothFinal.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require AsanFinal.
Require OSSVerify.Core.Shapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem strong_universal_error_free_fuzzstunclient_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.coturn.FuzzStunClient.images.Asan.M.loaded_segments OSSVerify.coturn.FuzzStunClient.images.Asan.M.init_pc OSSVerify.coturn.FuzzStunClient.images.Asan.M.phdrs).
Proof.
exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.AsanFinal.asan_base.
Qed.

Theorem strong_universal_error_free_fuzzstunclient_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.coturn.FuzzStunClient.images.Ubsan.M.loaded_segments OSSVerify.coturn.FuzzStunClient.images.Ubsan.M.init_pc OSSVerify.coturn.FuzzStunClient.images.Ubsan.M.phdrs).
Proof.
exact (LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets_of_pinned _ _ OSSVerify.Proofs.coturn.FuzzStunClient.lib.UbsanTop.ubsan_base).
Qed.

Theorem strong_universal_error_free_fuzzstunclient_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.loaded_segments OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.init_pc OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.BothFinal.both_base.
Qed.

(* The halting statements of the two AddressSanitizer builds. *)
Theorem coturn_fuzzstunclient_asan_halts :
  OSSVerify.Core.Shapes.halts_within_budget OSSVerify.Core.Shapes.Budgets.Standard.lim_source
    OSSVerify.Core.Shapes.Exits.ok_or_refused
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.coturn.FuzzStunClient.images.Asan.M.loaded_segments OSSVerify.coturn.FuzzStunClient.images.Asan.M.init_pc OSSVerify.coturn.FuzzStunClient.images.Asan.M.phdrs).
Proof.
exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.AsanFinal.asan_halts.
Qed.

Theorem coturn_fuzzstunclient_asan_ubsan_halts :
  OSSVerify.Core.Shapes.halts_within_budget OSSVerify.Core.Shapes.Budgets.Standard.lim_source
    OSSVerify.Core.Shapes.Exits.ok_or_refused
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.loaded_segments OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.init_pc OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.BothFinal.both_halts.
Qed.
