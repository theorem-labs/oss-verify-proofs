From OSSVerify.cgif.cgif_rgb_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require ConstAccept.

Theorem asan_agreement_decidable_holds : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.asan_agreement_decidable.
Proof. exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.ConstAccept.asan_decidable. Qed.
