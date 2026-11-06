From OSSVerify.speex.speex_decode_fuzzer_float Require Statements.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.speex.speex_decode_fuzzer_float.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Theorems.strong_universal_error_free_speexdec_fuzzer_asan. Qed.
