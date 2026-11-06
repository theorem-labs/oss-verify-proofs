From OSSVerify.fast_float.from_chars Require Statements.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Theorems.

Theorem plain_halts_holds : OSSVerify.fast_float.from_chars.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.fast_float.from_chars.lib.Theorems.halts_allowed_fast_float_from_chars_halts_plain. Qed.
