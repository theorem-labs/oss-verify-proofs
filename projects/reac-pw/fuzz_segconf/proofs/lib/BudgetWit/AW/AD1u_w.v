(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build; FINV and finv_img take YE00's aclosed_stdio_env and aclosed_env_addr instead of astdio_env and aenv_addr, FINV_IVS drops cgif's four sink-file string ranges and tfib_AIL proves asink_img_laws on the closed address set, since fuzz_command's harness opens no sink file; tfib_AIL's ail_icells case takes AE2k's four tfib_icells cells. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AD1u.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1u.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK00 YK0s YK15.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AE2k_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AD1y_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
