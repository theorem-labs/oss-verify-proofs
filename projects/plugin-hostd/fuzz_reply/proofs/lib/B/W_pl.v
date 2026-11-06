(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the PAListing instance of fuzz_reply.asan-ubsan's program listing (lib/B's twin of lib/A/W_pl.v), in the form of the PL_asan3_0 instance of proofs/cgif/cgif_file_fuzzer/lib/YC4a.v. *)
(* It holds no address: it only compiles the listing into the two tables the symbolic runner reads. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP02 YP0b YP0a YP0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition fr_prog_tpi : ptree wsym := ptree_of_list fr_prog_listing.
Definition fr_prog_tw : ctable := Eval vm_compute in (tw_of 0 fr_prog_listing).
#[global] Instance PL_fr : PAListing fr_prog_listing :=
{| pl_tpi := fr_prog_tpi; pl_tpi_eq := eq_refl; pl_tw := fr_prog_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.
