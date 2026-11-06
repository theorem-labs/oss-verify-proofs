(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import TopLevel PlainTopU.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import TopLevelGen.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg PlainClosed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg UbsanClosed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_ubsan_mc : plain_client_stmt -> ubsan_client_stmt ->
  strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs) (mkImage usegs u_init_pc u_phdrs).
Proof. intros PC UC. exact (base_ubsan (plain_impl_closed_modulo_client PC) (ubsan_impl_closed_modulo_client UC)). Qed.
