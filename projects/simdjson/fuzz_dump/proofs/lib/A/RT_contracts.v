(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_malcore_m RT_malloc
  RT_freelift RT_iclifts RT_iclifts3 RT_setshadow RT_artfacts RT_stackmalloc RT_stackmalloc5 RT_stackfree5 RT_iclifts4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Theorem rta_contracts : refill_stmt -> core_stmt_sec -> free_contract RTA -> smgc_stmt -> rt_contracts RTA.
Proof.
  intros RF CS FR GC.
  exact (mkRTC RTA (rta_malloc (core_prim RF) CS) FR rta_free_null
           rta_memcpy rta_asan_memcpy rta_memset rta_asan_memset rta_asan_memmove rta_memchr rta_strlen rta_strnlen rta_memcmp
           (rta_stack_malloc_4 GC) (rta_stack_malloc_5 GC) rta_stack_free_5 rta_set_shadow rta_art_facts).
Qed.
