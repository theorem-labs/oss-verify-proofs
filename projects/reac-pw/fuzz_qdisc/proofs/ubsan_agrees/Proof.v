From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.reac_pw.fuzz_qdisc.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Theorems.reac_pw_fuzz_qdisc_ubsan_agrees. Qed.
