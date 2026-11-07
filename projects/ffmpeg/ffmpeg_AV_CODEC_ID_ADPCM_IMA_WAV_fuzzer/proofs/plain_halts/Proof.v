(* SPDX-License-Identifier: MIT *)
(** ADPCM_IMA_WAV's plain build halts with status 0 or 2: the driver, musl and
    mallocng proof ported from zlib/checksum_fuzzer (lib/Reusable), composed
    with the proof of this target's own LLVMFuzzerTestOneInput (lib/AHarness.v, lib/AHarnessContract.v). *)
From OSSVerify.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer Require Statements.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib Require Import
  ZComplete ZAllocator AHarnessContract.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  apply plain_halts_from_runtime_contracts, runtime_contracts_from_harness.
  exact adpcm_harness_holds.
Qed.
