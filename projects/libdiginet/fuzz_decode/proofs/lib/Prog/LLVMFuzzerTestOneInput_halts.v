(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode, on libreac/fuzz_decode's released lib/Prog/LLVMFuzzerTestOneInput_halts.v:
   plain_halts from the frame and the entry contract. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YK11 YM05 YO0d YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require FrameProof.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import Statement LLVMFuzzerTestOneInput_end.
From OSSVerify.libdiginet.fuzz_decode Require Statements.
Local Open Scope Z_scope.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  apply plain_halts_of_slot; [|exact FrameProof.frame_plain_holds].
  intros rc fx LS B API SH SK FR. exact (llvm_contract B API FR).
Qed.
