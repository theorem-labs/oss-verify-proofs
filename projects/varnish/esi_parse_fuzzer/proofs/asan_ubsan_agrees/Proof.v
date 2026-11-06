From OSSVerify.varnish.esi_parse_fuzzer Require Statements.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Theorems.

Theorem asan_ubsan_agrees_holds : OSSVerify.varnish.esi_parse_fuzzer.Statements.asan_ubsan_agrees.
Proof. exact OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Theorems.strong_universal_error_free_esi_parse_fuzzer_both. Qed.
