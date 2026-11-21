From OSSVerify.jsoncons.fuzz_bigint Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus Require CorpusTops.

Theorem ubsan_halts_holds : OSSVerify.jsoncons.fuzz_bigint.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusTops.halts_allowed_jsoncons_fuzz_bigint_halts_ubsan. Qed.
