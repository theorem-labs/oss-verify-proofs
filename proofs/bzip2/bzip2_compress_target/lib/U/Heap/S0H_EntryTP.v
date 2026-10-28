(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocTight AllocCover. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import S0H_Iface S0H_Tight S0H_Cover S0H_Entry.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0GrowStmt U.S0TargetPhase.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Definition S0_HE0 : S0TargetPhase.entry_facts_0 S0_alloc S0_cover := S0_entry_facts0.
Definition S0_HE0W : S0GrowStmt.grow_entry_stmt S0_alloc S0_tight := S0_entry0w.
Definition S0_HTC : S0GrowStmt.tight_cover_stmt S0_alloc S0_tight S0_cover := S0_tight_cover.

End ACeilS1.
