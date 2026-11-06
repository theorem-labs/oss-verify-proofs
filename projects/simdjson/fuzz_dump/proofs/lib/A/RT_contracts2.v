(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import RT_iface RT_iface2 RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_contracts RT_stackmalloc RT_stackmalloc1 RT_iclifts_t2 RT_iclift0 RT_icliftmv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Theorem rta_contracts2 : refill_stmt -> core_stmt_sec -> free_contract RTA -> smgc_stmt -> smgc1_case -> rt_contracts2 RTA.
Proof. intros RF CS FR GC GC1. exact (mkRTC2 RTA (rta_contracts RF CS FR GC) (rta_stack_malloc_1 GC1) rta_memmove2 rta_memcmp_wide rta_memcmp_zero). Qed.
