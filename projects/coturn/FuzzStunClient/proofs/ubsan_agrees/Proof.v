From OSSVerify.coturn.FuzzStunClient Require Statements.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.coturn.FuzzStunClient.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.Theorems.strong_universal_error_free_fuzzstunclient_ubsan. Qed.
