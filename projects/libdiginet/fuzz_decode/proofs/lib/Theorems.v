(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The unit's tops, as libreac/fuzz_decode's released lib/Theorems.v: plain_halts (lib/Prog), ubsan_halts (lib/U/Prog),
   ubsan_agrees (lib/Prog/LLVMFuzzerTestOneInput_agree.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require LLVMFuzzerTestOneInput_agree.

Definition libdiginet_fuzz_decode_plain_halts :=
  OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog.LLVMFuzzerTestOneInput_halts.plain_halts_holds.

Definition libdiginet_fuzz_decode_ubsan_halts :=
  OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog.LLVMFuzzerTestOneInput_halts.ubsan_halts_holds.

Definition libdiginet_fuzz_decode_ubsan_agrees :=
  OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog.LLVMFuzzerTestOneInput_agree.ubsan_agrees_holds.
