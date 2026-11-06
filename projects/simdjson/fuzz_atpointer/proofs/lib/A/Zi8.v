(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Zks Zm2 RT_rep Zl3 Zls Zl0 Zl4
  Zkg Zko Zkp Zlx Zi7 Zlz Zm1 Zly Zkq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_contracts : refill_stmt -> core_stmt_sec -> free_contract RTA -> rt_contracts RTA.
Proof.
  intros RF CS FR.
  exact (mkRTC RTA (rta_malloc (core_prim RF) CS) FR rta_free_null
           rta_memcpy rta_asan_memcpy rta_memset rta_asan_memset rta_asan_memmove rta_memchr rta_strlen rta_strnlen rta_memcmp
           rta_stack_malloc_2 rta_stack_malloc_4 rta_stack_malloc_5 rta_stack_free_5 rta_set_shadow rta_art_facts).
Qed.
