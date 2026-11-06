From OSSVerify.coturn.FuzzStunClient Require Statements.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.coturn.FuzzStunClient.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.Theorems.strong_universal_error_free_fuzzstunclient_both. Qed.
