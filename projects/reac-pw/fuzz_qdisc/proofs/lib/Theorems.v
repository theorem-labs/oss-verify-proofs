From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require QdiscEnd.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog Require QdiscEnd.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require AgreeQdisc.

Definition reac_pw_fuzz_qdisc_plain_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog.QdiscEnd.plain_halts_holds.
Definition reac_pw_fuzz_qdisc_ubsan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog.QdiscEnd.ubsan_halts_holds.
Definition reac_pw_fuzz_qdisc_ubsan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AgreeQdisc.ubsan_agrees_holds.
Definition reac_pw_fuzz_qdisc_plain_halts_may_fail :=
  OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog.QdiscEnd.plain_halts_may_fail_holds.
Definition reac_pw_fuzz_qdisc_ubsan_halts_may_fail :=
  OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog.QdiscEnd.ubsan_halts_may_fail_holds.
