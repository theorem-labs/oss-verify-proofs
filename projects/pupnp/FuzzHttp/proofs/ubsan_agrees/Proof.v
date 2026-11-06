From OSSVerify.pupnp.FuzzHttp Require Statements.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.pupnp.FuzzHttp.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.pupnp.FuzzHttp.lib.Theorems.strong_universal_error_free_fuzzhttp_ubsan. Qed.
