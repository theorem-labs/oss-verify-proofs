From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require RateTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require RateTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require AgreeRate.

Definition reac_pw_fuzz_rate_plain_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateTop.plain_halts_holds.
Definition reac_pw_fuzz_rate_ubsan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateTop.ubsan_halts_holds.
Definition reac_pw_fuzz_rate_ubsan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AgreeRate.ubsan_agrees_holds.
