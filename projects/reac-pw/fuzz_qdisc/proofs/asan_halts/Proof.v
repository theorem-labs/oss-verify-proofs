From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require AD2o.

Theorem asan_halts_holds : OSSVerify.reac_pw.fuzz_qdisc.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A.AD2o.qdisc_asan_halts_closed. Qed.
