From OssFuzzTheorems.pupnp.FuzzHttp Require Statements.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.pupnp.FuzzHttp.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Theorems.strong_universal_error_free_fuzzhttp_ubsan. Qed.
