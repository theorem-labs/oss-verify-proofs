From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFfx.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YFeq YFgi YFfv YFgn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition R_IMN : YP09.region := YP09.mkRegion None (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL26internal_alloc_placeholderE + 0x8)%Z) (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL26internal_alloc_placeholderE + 0x10)%Z) 0 0 [YP09.mkChunk (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL26internal_alloc_placeholderE + 0x8)%Z) (CZero 8)].
Definition SS_L1N : sstate := Eval vm_compute in (xrun_to (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer18internal_allocatorEv) YFgn.SS0).
Definition SS_AN : sstate := Eval vm_compute in
(xrun_to (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj) (xpin 10 (SLit TFIB_IAL_LO) (xadd R_IMN (xadd R_SCR (xafter 54 (-2128) (symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x34)%Z) SS_L1N))))).
Definition SS_RN : sstate := Eval vm_compute in (xrun_to (symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x1cc)%Z) (xadd R_SCR (xafterU 70 (symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x194)%Z) SS_AN))).
Goal ss_pc SS_AN = (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj) /\ ss_pc SS_RN = (symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x1cc)%Z). Proof. split; reflexivity. Qed.
