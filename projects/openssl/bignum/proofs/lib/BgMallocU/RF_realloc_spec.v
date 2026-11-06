(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocU Require Import RMalloc_iface RRealloc_iface RF_impl_spec RF_realloc.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rrealloc_spec : rrealloc_stmt.
Proof. exact (rrealloc_spec_proof rmalloc_impl_spec rfree_impl_spec). Qed.
End WithCeiling0.
