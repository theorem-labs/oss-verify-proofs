(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RRealloc_iface RF_realloc_I.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rrealloc_inplace_spec : rrealloc_inplace_stmt.
Proof. exact rrealloc_inplace_proof. Qed.
End WithCeiling0.
