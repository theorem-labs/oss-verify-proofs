From OssFuzzTheorems.boost_beast.http_request Require Statements.
From OssFuzzTheorems.Proofs.boost_beast.http_request.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OssFuzzTheorems.boost_beast.http_request.Statements.asan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.boost_beast.http_request.lib.ConstAccept.asan_decidable. Qed.
