(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import RT_iface RT_rep D_libiface Fz_defs Fz_iface Fz_top Fz_ring0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem fuzz_one_A : rt_contracts RTA -> fuzz_one_cps RTA LIB_A.
Proof. intros RC. exact (fuzz_one_ok RTA RC ring0_ok). Qed.
