From OssFuzzTheorems.boost_beast.http_request Require Statements.
From OssFuzzTheorems.Proofs.boost_beast.http_request.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.boost_beast.http_request.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.boost_beast.http_request.lib.ConstAccept.ubsan_decidable. Qed.
