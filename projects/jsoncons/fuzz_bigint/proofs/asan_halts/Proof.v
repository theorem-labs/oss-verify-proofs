From OSSVerify.jsoncons.fuzz_bigint Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus Require CorpusTopsA.

Theorem asan_halts_holds : OSSVerify.jsoncons.fuzz_bigint.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusTopsA.halts_allowed_jsoncons_fuzz_bigint_halts_asan. Qed.
