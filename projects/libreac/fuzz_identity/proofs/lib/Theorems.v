From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Link AgreeTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require ULink.

Definition libreac_fuzz_identity_plain_halts :=
  OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Link.plain_halts_holds.
Definition libreac_fuzz_identity_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg.ULink.ubsan_halts_holds.
Definition libreac_fuzz_identity_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.AgreeTop.ubsan_agrees_holds.
