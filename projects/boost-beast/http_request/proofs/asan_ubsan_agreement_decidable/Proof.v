From OSSVerify.boost_beast.http_request Require Statements.
From OSSVerify.Proofs.boost_beast.http_request.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.boost_beast.http_request.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.boost_beast.http_request.lib.ConstAccept.asan_ubsan_decidable. Qed.
