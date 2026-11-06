(* The unit's tops, as reac-repacer/fuzz_uci's lib/Theorems.v (recipes commit 0295462466b2): plain_halts and ubsan_halts from the
   harness-entry packs lib/Prog/LLVMFuzzerTestOneInput_halts.v and lib/U/Prog/LLVMFuzzerTestOneInput_halts.v,
   ubsan_agrees from the agreement chain's lib/Prog/LLVMFuzzerTestOneInput_agree.v, asan_halts and asan_agrees from
   image A's close lib/A/WireClose.v, asan_ubsan_halts and asan_ubsan_agrees from image B's close
   lib/B/WireBClose.v. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require LLVMFuzzerTestOneInput_agree.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require WireClose.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require WireBClose.

Definition reac_repacer_fuzz_wire_plain_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.LLVMFuzzerTestOneInput_halts.plain_halts_holds.
Definition reac_repacer_fuzz_wire_ubsan_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog.LLVMFuzzerTestOneInput_halts.ubsan_halts_holds.
Definition reac_repacer_fuzz_wire_ubsan_agrees :=
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.LLVMFuzzerTestOneInput_agree.ubsan_agrees_holds.
Definition reac_repacer_fuzz_wire_asan_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.WireClose.wire_asan_halts_of_parts.
Definition reac_repacer_fuzz_wire_asan_agrees :=
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.WireClose.wire_asan_agrees_of_parts.
Definition reac_repacer_fuzz_wire_asan_ubsan_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.WireBClose.wire_asan_ubsan_halts_of_parts.
Definition reac_repacer_fuzz_wire_asan_ubsan_agrees :=
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.WireBClose.wire_asan_ubsan_agrees_of_parts.
