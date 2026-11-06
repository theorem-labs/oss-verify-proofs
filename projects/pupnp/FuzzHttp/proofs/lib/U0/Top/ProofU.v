(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/pupnp/FuzzHttp/lib/Theorems.v; 2 of its 15 lines of code are new or changed and 27 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.pupnp.FuzzHttp.images.Plain.
Require OSSVerify.pupnp.FuzzHttp.images.Ubsan.

Require OSSVerify.Proofs.pupnp.FuzzHttp.lib.U0.Top.TopU.

Theorem strong_universal_error_free_fuzzhttp_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.pupnp.FuzzHttp.images.Plain.M.loaded_segments OSSVerify.pupnp.FuzzHttp.images.Plain.M.init_pc OSSVerify.pupnp.FuzzHttp.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.pupnp.FuzzHttp.images.Ubsan.M.loaded_segments OSSVerify.pupnp.FuzzHttp.images.Ubsan.M.init_pc OSSVerify.pupnp.FuzzHttp.images.Ubsan.M.phdrs).
Proof.
exact (LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_of_scfg _ _ _ OSSVerify.Proofs.pupnp.FuzzHttp.lib.U0.Top.TopU.fuzzhttp_ubsan_error_free).
Qed.
