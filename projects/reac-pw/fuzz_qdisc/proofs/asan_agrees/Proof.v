From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require AD2o.

Theorem asan_agrees_holds : OSSVerify.reac_pw.fuzz_qdisc.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A.AD2o.qdisc_asan_agrees_closed. Qed.
