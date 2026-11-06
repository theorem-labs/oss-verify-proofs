From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require Theorems.

Theorem plain_halts_may_fail_holds : OSSVerify.reac_pw.fuzz_qdisc.Statements.plain_halts_may_fail.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Theorems.reac_pw_fuzz_qdisc_plain_halts_may_fail. Qed.
