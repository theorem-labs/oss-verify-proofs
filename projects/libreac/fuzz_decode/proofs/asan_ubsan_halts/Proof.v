From OSSVerify.libreac.fuzz_decode Require Statements.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.libreac.fuzz_decode.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.libreac.fuzz_decode.lib.Theorems.libreac_fuzz_decode_asan_ubsan_halts. Qed.
