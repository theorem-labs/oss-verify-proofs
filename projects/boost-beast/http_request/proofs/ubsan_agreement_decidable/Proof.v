From OSSVerify.boost_beast.http_request Require Statements.
From OSSVerify.Proofs.boost_beast.http_request.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OSSVerify.boost_beast.http_request.Statements.ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.boost_beast.http_request.lib.ConstAccept.ubsan_decidable. Qed.
