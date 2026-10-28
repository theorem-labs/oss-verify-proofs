From OssFuzzTheorems.cgif.cgif_rgb_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require ConstAccept.

Theorem asan_ubsan_agreement_decidable_holds : OssFuzzTheorems.cgif.cgif_rgb_fuzzer.Statements.asan_ubsan_agreement_decidable.
Proof. exact OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib.ConstAccept.asan_ubsan_decidable. Qed.
