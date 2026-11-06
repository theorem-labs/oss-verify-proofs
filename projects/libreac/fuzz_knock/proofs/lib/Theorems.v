From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require KnockEnd.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog Require KnockEnd.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require AgreeKnock.

Definition libreac_fuzz_knock_plain_halts :=
  OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog.KnockEnd.plain_halts_holds.
Definition libreac_fuzz_knock_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog.KnockEnd.ubsan_halts_holds.
Definition libreac_fuzz_knock_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_knock.lib.AgreeKnock.ubsan_agrees_holds.
Definition libreac_fuzz_knock_plain_halts_may_fail :=
  OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog.KnockEnd.plain_halts_may_fail_holds.
Definition libreac_fuzz_knock_ubsan_halts_may_fail :=
  OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog.KnockEnd.ubsan_halts_may_fail_holds.
