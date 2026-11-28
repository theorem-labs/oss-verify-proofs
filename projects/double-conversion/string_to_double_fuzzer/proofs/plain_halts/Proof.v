From OSSVerify.double_conversion.string_to_double_fuzzer Require Statements.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Halts Require HaltsTops.

Theorem plain_halts_holds : OSSVerify.double_conversion.string_to_double_fuzzer.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Halts.HaltsTops.plain_halts_thm. Qed.
