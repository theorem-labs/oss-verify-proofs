(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's; tfib_AIL, finv_img_ivs, finv_frame and finv_acall_post read the sink's cells through tfib_K's ak_owned (tfib_owned_iff, tfib_core_owned); the image start and image top of the FINV_IVS image checks are now cited from lib/Reusable/YImgTop.v instead of written as numbers, and the steps that hand a range to AD1y's image lemmas unfold those citations first, so lia still sees the numbers once AD1y cites them too. *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane, rev6b): finv_acall_post reads acall_post's grow-then-le layout clause through lib/Reusable/KnLayoutGle.v's gle_le; no statement changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1u.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.libreac.fuzz_knock.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK00 YK0s YK15.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import AE2k_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 AF0m.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import AD1y_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
