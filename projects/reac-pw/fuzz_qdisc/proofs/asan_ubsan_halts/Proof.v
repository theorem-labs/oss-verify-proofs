From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require YD2o.

Theorem asan_ubsan_halts_holds : OSSVerify.reac_pw.fuzz_qdisc.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU.YD2o.qdisc_asan_ubsan_halts_closed. Qed.
