From OSSVerify.boost_beast.http_request Require Statements.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.boost_beast.http_request.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.boost_beast.http_request.lib.Theorems.halts_allowed_boost_beast_halts_plain. Qed.
