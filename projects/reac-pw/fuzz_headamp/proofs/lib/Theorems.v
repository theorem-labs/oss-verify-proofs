From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require HeadTop HeadAgreeTop.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require HeadTop.

Definition reac_pw_fuzz_headamp_plain_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadTop.plain_halts_holds.
Definition reac_pw_fuzz_headamp_ubsan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadTop.ubsan_halts_holds.
Definition reac_pw_fuzz_headamp_ubsan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadAgreeTop.ubsan_agrees_holds.
