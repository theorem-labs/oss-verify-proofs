From OSSVerify.double_conversion.string_to_double_fuzzer Require Statements.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Halts Require HaltsTops.

Theorem ubsan_halts_holds : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Halts.HaltsTops.ubsan_halts_thm. Qed.
