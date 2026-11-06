From OSSVerify.boost_beast.http_request Require Statements.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.boost_beast.http_request.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.halts_allowed_boost_beast_halts_both. Qed.
