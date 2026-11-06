From OSSVerify.boost_beast.http_request Require Statements.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.boost_beast.http_request.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.halts_allowed_boost_beast_halts_ubsan. Qed.
