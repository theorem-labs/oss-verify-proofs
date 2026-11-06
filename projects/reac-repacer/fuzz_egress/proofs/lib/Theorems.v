(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The unit's tops, as libreac/fuzz_decode's released lib/Theorems.v: plain_halts (lib/Prog/LLVMFuzzerTestOneInput_halts),
   ubsan_halts (lib/U/Prog/LLVMFuzzerTestOneInput_halts) and ubsan_agrees (lib/Prog/LLVMFuzzerTestOneInput_agree). *)
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require LLVMFuzzerTestOneInput_agree.

Definition reac_repacer_fuzz_egress_plain_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog.LLVMFuzzerTestOneInput_halts.plain_halts_holds.
Definition reac_repacer_fuzz_egress_ubsan_halts :=
  OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog.LLVMFuzzerTestOneInput_halts.ubsan_halts_holds.
Definition reac_repacer_fuzz_egress_ubsan_agrees :=
  OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog.LLVMFuzzerTestOneInput_agree.ubsan_agrees_holds.
