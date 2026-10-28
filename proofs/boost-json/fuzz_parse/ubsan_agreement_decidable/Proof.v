From OssFuzzTheorems.boost_json.fuzz_parse Require Statements.
From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib Require ConstAccept.

Theorem ubsan_agreement_decidable_holds : OssFuzzTheorems.boost_json.fuzz_parse.Statements.ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.ConstAccept.ubsan_decidable. Qed.
