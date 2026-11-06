From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.reac_pw.fuzz_qdisc.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Theorems.reac_pw_fuzz_qdisc_ubsan_halts. Qed.
