(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan instance of musl's __toread walk inside libreac/fuzz_pcap
   (libreac v1.9.0). The walk rtoread_contract_proof is image-free, in lib/A/Stdio/PFtoreadMW.v;
   this file applies it to the asan image at PTOREAD = 0x8e638 (lib/A/Stdio/PStdioImgA.v). The
   asan-ubsan instance is in lib/B/Stdio/PFtoreadMWB.v. Its image facts are checked by computation
   over the image's own segments, AR_laws by YG0q.AR_laws_ok; the stream record's image law stays a
   premise (the composition's). Moved unchanged from PFtoreadMW.v (a working branch 016391ab8b5).
   rule 24: no function proved (split of a proved file). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0s YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN01 YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YP09 YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PFtoreadMW PStdioImgA.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* asan: __toread at PTOREAD = 0x8e638. *)
Theorem rtoread_contract_asan : forall B K,
  asource_img_laws SK Asan.M.loaded_segments B K ->
  rtoread_contract Asan.M.loaded_segments B K PTOREAD.
Proof.
  intros B K ASIL. apply (rtoread_contract_proof Asan.M.loaded_segments B K (YG0q.AR_laws_ok _ B)).
  - apply segs_low_of_b. vm_compute. reflexivity.
  - apply wx_segs_nowrap_of_b. vm_compute. reflexivity.
  - exact ASIL.
  - vm_compute. reflexivity.
Qed.
End i.
