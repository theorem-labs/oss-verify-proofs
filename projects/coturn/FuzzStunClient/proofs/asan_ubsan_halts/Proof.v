From OSSVerify.coturn.FuzzStunClient Require Statements.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.coturn.FuzzStunClient.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.Theorems.coturn_fuzzstunclient_asan_ubsan_halts. Qed.
