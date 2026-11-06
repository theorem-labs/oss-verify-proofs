From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_agree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxClose.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBClose.

Definition libreac_fuzz_boxreg_plain_halts :=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.LLVMFuzzerTestOneInput_halts.plain_halts_holds.
Definition libreac_fuzz_boxreg_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog.LLVMFuzzerTestOneInput_halts.ubsan_halts_holds.
Definition libreac_fuzz_boxreg_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.LLVMFuzzerTestOneInput_agree.ubsan_agrees_holds.
Definition libreac_fuzz_boxreg_asan_halts :=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxClose.box_asan_halts.
Definition libreac_fuzz_boxreg_asan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.BoxClose.box_asan_agrees.
Definition libreac_fuzz_boxreg_asan_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBClose.box_asan_ubsan_halts.
Definition libreac_fuzz_boxreg_asan_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBClose.box_asan_ubsan_agrees.
