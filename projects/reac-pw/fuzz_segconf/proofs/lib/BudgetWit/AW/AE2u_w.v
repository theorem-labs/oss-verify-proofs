(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2u.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AE2u.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2u.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w YA0m_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AE34 AF0l AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AF0x_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1w AE20.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AE2y_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AE3f_w AE2p_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AE3i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AE39_w AE3h_w AE3k_w AE31_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AE38.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AE7c_w AE7d_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section g.
Definition FPI_STK : Z := 9216.
End g.
