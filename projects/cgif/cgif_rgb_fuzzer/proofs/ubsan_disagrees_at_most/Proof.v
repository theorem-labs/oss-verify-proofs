From Stdlib Require Import QArith.
From OSSVerify.cgif.cgif_rgb_fuzzer Require Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.cgif.cgif_rgb_fuzzer.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.ConstAccept.ubsan_bound_0. Qed.
