(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v at theorem-labs/oss-verify-proofs@6b32741d849a, with its module paths changed, names TfibSyms -> GrantSyms and its addresses moved to libreac/fuzz_grant's ASan build; the sink's path, mode, "rwa" and trailer strings are removed from tfib_AIL, FINV_IVS and finv_img_ivs, tfib_AIL's icell cases are the four rows that build keeps, and tfib_AIL, finv_img_ivs, finv_frame and finv_acall_post read the sink's cells through tfib_K's ak_owned (tfib_owned_iff, tfib_core_owned). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AD1u.v (donor image sha256 c2c7559b29bd), with its module paths changed, names GrantSyms -> WireSyms and its addresses moved to reac-repacer/fuzz_wire's ASan build; one proof step reads acall_post's grow-then-le layout clause through lib/Reusable/KnLayoutGle.v's gle_le; no statement changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1u.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK00 YK0s YK15.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.BudgetWit.AW Require Import AE2k_w.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.BudgetWit.AW Require Import AD1y_w.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
