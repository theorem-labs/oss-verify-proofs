(* Modified by Theorem Labs, 2026-11: made from A/AE3j.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE3j.v, with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK0k YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AE34 AF0l AE3e.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AE3f_w AE3g_w AE6g_w AE39_w AE2p_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AE3i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AE3h_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AF0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AE22_w AF0x_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AE20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AE2y_w AE7f_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b.
Definition FMT_open : Z := (symaddr (Symbols.Asan.Sec.s_rodata + 0xd351)%Z).
End b.
