From OSSVerify.boost_beast.http_request Require Statements.
From OSSVerify.Proofs.boost_beast.http_request.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.boost_beast.http_request.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.boost_beast.http_request.lib.ConstAccept.asan_decidable. Qed.
