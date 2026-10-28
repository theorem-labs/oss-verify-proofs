(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_malcore_m RT_malloc RT_freelift RT_iclifts RT_iclifts3 RT_setshadow RT_artfacts RT_stackmalloc RT_stackmalloc0 RT_stackmalloc5 RT_stackfree5 RT_iclifts4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Theorem rta_contracts : refill_stmt -> core_stmt_sec -> free_contract RTA -> smgc_stmt -> rt_contracts RTA.
Proof.
  intros RF CS FR GC.
  exact (mkRTC RTA (rta_malloc (core_prim RF) CS) FR rta_free_null
           rta_memcpy rta_asan_memcpy rta_memset rta_asan_memset rta_asan_memmove rta_memchr rta_strlen rta_strnlen rta_memcmp
           (rta_stack_malloc_0 GC) (rta_stack_malloc_4 GC) (rta_stack_malloc_5 GC) rta_stack_free_5 rta_set_shadow rta_art_facts).
Qed.
