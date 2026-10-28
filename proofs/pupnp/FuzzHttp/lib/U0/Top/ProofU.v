From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OssFuzzTheorems.pupnp.FuzzHttp.images.Plain.
Require OssFuzzTheorems.pupnp.FuzzHttp.images.Ubsan.

Require OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Top.TopU.

Theorem strong_universal_error_free_fuzzhttp_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.pupnp.FuzzHttp.images.Plain.M.loaded_segments OssFuzzTheorems.pupnp.FuzzHttp.images.Plain.M.init_pc OssFuzzTheorems.pupnp.FuzzHttp.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.pupnp.FuzzHttp.images.Ubsan.M.loaded_segments OssFuzzTheorems.pupnp.FuzzHttp.images.Ubsan.M.init_pc OssFuzzTheorems.pupnp.FuzzHttp.images.Ubsan.M.phdrs).
Proof.
exact (LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_of_scfg _ _ _ OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Top.TopU.fuzzhttp_ubsan_error_free).
Qed.
