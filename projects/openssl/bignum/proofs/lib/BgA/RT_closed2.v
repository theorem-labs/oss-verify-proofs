(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import RT_iface RT_iface2 RT_state RT_rep RT_closed RT_stackmalloc2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_contracts2 : rt_contracts2 RTA.
Proof. exact (rt_contracts2_of RTA rta_contracts_all rta_stack_malloc_1 rta_stack_malloc_3). Qed.

