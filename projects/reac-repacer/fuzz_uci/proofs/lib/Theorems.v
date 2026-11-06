(* The unit's tops, as libreac/fuzz_decode's released lib/Theorems.v: plain_halts (lib/Prog), ubsan_halts
   (lib/U/Prog/LLVMFuzzerTestOneInput_halts), ubsan_agrees (lib/Prog/LLVMFuzzerTestOneInput_agree), asan_halts and
   asan_agrees (lib/A/UciClose), asan_ubsan_halts and asan_ubsan_agrees (lib/B/UciBClose). *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require LLVMFuzzerTestOneInput_agree.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require UciClose.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require UciBClose.

Definition reac_repacer_fuzz_uci_plain_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.LLVMFuzzerTestOneInput_halts.plain_halts_holds.
Definition reac_repacer_fuzz_uci_ubsan_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog.LLVMFuzzerTestOneInput_halts.ubsan_halts_holds.
Definition reac_repacer_fuzz_uci_ubsan_agrees :=
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.LLVMFuzzerTestOneInput_agree.ubsan_agrees_holds.
Definition reac_repacer_fuzz_uci_asan_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.UciClose.uci_asan_halts_of_parts.
Definition reac_repacer_fuzz_uci_asan_agrees :=
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.UciClose.uci_asan_agrees_of_parts.
Definition reac_repacer_fuzz_uci_asan_ubsan_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.UciBClose.uci_asan_ubsan_halts_of_parts.
Definition reac_repacer_fuzz_uci_asan_ubsan_agrees :=
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.UciBClose.uci_asan_ubsan_agrees_of_parts.
