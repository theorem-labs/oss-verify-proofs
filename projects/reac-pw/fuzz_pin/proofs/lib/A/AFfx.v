(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFfx.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AFfx.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AFeq AFgi AFfv AFgn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition R_IMN : YP09.region := YP09.mkRegion None 0xa2808 0xa2810 0 0 [YP09.mkChunk 0xa2808 (CZero 8)].
Definition SS_L1N : sstate := Eval vm_compute in (xrun_to 0x5e08c AFgn.SS0).
Definition SS_AN : sstate := Eval vm_compute in
(xrun_to 0x5a5a8 (xpin 10 (SLit TFIB_IAL_LO) (xadd R_IMN (xadd R_SCR (xafter 54 (-2128) 0x52b8c SS_L1N))))).
Definition SS_RN : sstate := Eval vm_compute in (xrun_to 0x52d24 (xadd R_SCR (xafterU 70 0x52cec SS_AN))).
Goal ss_pc SS_AN = 0x5a5a8 /\ ss_pc SS_RN = 0x52d24. Proof. split; reflexivity. Qed.
