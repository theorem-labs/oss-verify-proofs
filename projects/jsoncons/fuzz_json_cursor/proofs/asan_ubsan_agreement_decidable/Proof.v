From OSSVerify.jsoncons.fuzz_json_cursor Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OSSVerify.jsoncons.fuzz_json_cursor.Statements.asan_ubsan_agreement_decidable.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.ConstAccept.asan_ubsan_decidable. Qed.
