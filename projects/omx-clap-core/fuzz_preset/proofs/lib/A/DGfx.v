(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGfx.v (a working branch 84ee52cd012, file sha256 829259ab65fc) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at d1f93c50c87) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc 0474699fc83547e0 (a working branch 83209f9d9cd8), --assume-source, --resolve the internal file resolve-102.txt (0 lines name this file); 3 numerals changed. *)
(* The state of the frame-generic Deallocate walk on a NULL pointer (from YFfx): Deallocate's early return.  The
   run from the generic seed DGgn.SS0 (a1 = 0) saves the callee-saved registers, takes [beqz a1], restores them and
   stops at the [ret] at 0x32328, whose target is the caller's return pc (atom 1). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFeq DGbase DGgi DGfv DGgn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition SS_RN : sstate := Eval vm_compute in (xrun_to 0x32328 DGgn.SS0).
Goal ss_pc SS_RN = 0x32328. Proof. reflexivity. Qed.
