(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.punycode.lib.MallocP Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Rnd Fz_iface Fz_fuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rfuzz_one_closed : forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__.
Proof. intros CE RN. exact (rfuzz_one_proof rmalloc_spec rfree_spec_proof). Qed.
