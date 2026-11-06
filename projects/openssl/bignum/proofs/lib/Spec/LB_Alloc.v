(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Export LB_Logic LB_Inv LB_StmtA LB_Raw LB_Init.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog LB_WMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling. Context {CE__ : Ceiling}.

Definition raw_malloc_LQ := raw_malloc_L malloc_core_fq_proof.
Definition raw_free_LQ := raw_free_L.

End WithCeiling.
