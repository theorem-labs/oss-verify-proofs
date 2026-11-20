From OSSVerify.simdjson.fuzz_utf8 Require Statements.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Halts Require HaltsTops.

Theorem plain_halts_holds : OSSVerify.simdjson.fuzz_utf8.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Halts.HaltsTops.halts_plain. Qed.
