(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Export LiaOrc.
Ltac orc_klia_ref := first [ lx_slim_tight; first [ clear_disj; lia_ref | prune_disj; lia_ref ] | prune_disj; lia_ref | lia_ref ].
Ltac orc_klia := orc_go_M ltac:(orc_klia_ref).
