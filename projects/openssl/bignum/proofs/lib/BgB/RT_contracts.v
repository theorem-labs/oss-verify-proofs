(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_malcore_m RT_malloc RT_freelift RT_iclifts RT_setshadow RT_artfacts RT_calloc RT_stackmalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_contracts : refill_stmt -> core_stmt_sec -> free_contract RTA -> realloc_contract RTA -> rt_contracts RTA.
Proof.
  intros RF CS FR RA.
  exact (mkRTC RTA (rta_malloc (core_prim RF) CS) FR rta_free_null (rta_calloc RF) RA
           rta_memcpy rta_asan_memcpy rta_memset rta_asan_memset rta_memchr rta_strlen rta_strnlen rta_strncmp
           rta_stack_malloc_0 rta_stack_malloc_2 rta_stack_malloc_4 rta_set_shadow rta_art_facts).
Qed.
