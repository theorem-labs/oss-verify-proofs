From OSSVerify.boost_beast.http_request Require Statements.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.boost_beast.http_request.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.strong_universal_error_free_boost_beast_ubsan. Qed.
