From OSSVerify.jsoncons.fuzz_msgpack_encoder Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.jsoncons.fuzz_msgpack_encoder.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.ConstAccept.asan_decidable. Qed.
