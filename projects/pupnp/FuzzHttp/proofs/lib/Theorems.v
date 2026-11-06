(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.pupnp.FuzzHttp.images.Plain.
Require OSSVerify.pupnp.FuzzHttp.images.Asan.
Require OSSVerify.pupnp.FuzzHttp.images.AsanUbsan.
Require OSSVerify.pupnp.FuzzHttp.images.Ubsan.

Require OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G.ClosedA0.
Require OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G.ClosedA0.
Require OSSVerify.Proofs.pupnp.FuzzHttp.lib.Common.SanTop.
Require OSSVerify.Proofs.pupnp.FuzzHttp.lib.U0.Top.ProofU.

Theorem strong_universal_error_free_fuzzhttp_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.pupnp.FuzzHttp.images.Plain.M.loaded_segments OSSVerify.pupnp.FuzzHttp.images.Plain.M.init_pc OSSVerify.pupnp.FuzzHttp.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.pupnp.FuzzHttp.images.Asan.M.loaded_segments OSSVerify.pupnp.FuzzHttp.images.Asan.M.init_pc OSSVerify.pupnp.FuzzHttp.images.Asan.M.phdrs).
Proof.
exact (OSSVerify.Proofs.pupnp.FuzzHttp.lib.Common.SanTop.scfg_pinned_to_sanitizer _ _ _ OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G.ClosedA0.fuzzhttp_asan_error_free).
Qed.

Theorem strong_universal_error_free_fuzzhttp_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.pupnp.FuzzHttp.images.Plain.M.loaded_segments OSSVerify.pupnp.FuzzHttp.images.Plain.M.init_pc OSSVerify.pupnp.FuzzHttp.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.pupnp.FuzzHttp.images.AsanUbsan.M.loaded_segments OSSVerify.pupnp.FuzzHttp.images.AsanUbsan.M.init_pc OSSVerify.pupnp.FuzzHttp.images.AsanUbsan.M.phdrs).
Proof.
exact (OSSVerify.Proofs.pupnp.FuzzHttp.lib.Common.SanTop.scfg_pinned_to_sanitizer _ _ _ OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G.ClosedA0.fuzzhttp_asan_error_free).
Qed.

Theorem strong_universal_error_free_fuzzhttp_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.pupnp.FuzzHttp.images.Plain.M.loaded_segments OSSVerify.pupnp.FuzzHttp.images.Plain.M.init_pc OSSVerify.pupnp.FuzzHttp.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.pupnp.FuzzHttp.images.Ubsan.M.loaded_segments OSSVerify.pupnp.FuzzHttp.images.Ubsan.M.init_pc OSSVerify.pupnp.FuzzHttp.images.Ubsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.pupnp.FuzzHttp.lib.U0.Top.ProofU.strong_universal_error_free_fuzzhttp_ubsan.
Qed.
