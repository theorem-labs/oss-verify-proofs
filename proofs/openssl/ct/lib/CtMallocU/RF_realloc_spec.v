(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMalloc_iface RRealloc_iface RF_impl_spec RF_realloc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rrealloc_spec : rrealloc_stmt.
Proof. exact (rrealloc_spec_proof rmalloc_impl_spec rfree_impl_spec). Qed.
End WithCeiling0.
