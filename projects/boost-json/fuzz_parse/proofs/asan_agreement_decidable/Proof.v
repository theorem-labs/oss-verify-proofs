From OSSVerify.boost_json.fuzz_parse Require Statements.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.boost_json.fuzz_parse.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.boost_json.fuzz_parse.lib.ConstAccept.asan_decidable. Qed.
