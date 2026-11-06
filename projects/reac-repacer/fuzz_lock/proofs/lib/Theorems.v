From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require LLVMFuzzerTestOneInput_agree.

Definition reac_repacer_fuzz_lock_plain_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog.LLVMFuzzerTestOneInput_halts.plain_halts_holds.
Definition reac_repacer_fuzz_lock_ubsan_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.LLVMFuzzerTestOneInput_halts.ubsan_halts_holds.
Definition reac_repacer_fuzz_lock_ubsan_agrees :=
  OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog.LLVMFuzzerTestOneInput_agree.ubsan_agrees_holds.
