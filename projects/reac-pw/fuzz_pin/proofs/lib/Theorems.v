From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require PinTop.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require PinTop.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require AgreePin.

Definition reac_pw_fuzz_pin_plain_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.PinTop.plain_halts_holds.
Definition reac_pw_fuzz_pin_ubsan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.PinTop.ubsan_halts_holds.
Definition reac_pw_fuzz_pin_ubsan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AgreePin.ubsan_agrees_holds.
