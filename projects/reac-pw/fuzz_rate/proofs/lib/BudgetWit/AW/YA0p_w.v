(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0p.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YA0p.v (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA0p.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK0j YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import YA0n_w YA0o_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
