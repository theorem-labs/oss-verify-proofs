(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_malcore_m RT_malloc RT_freelift RT_iclifts RT_setshadow RT_artfacts RT_stackmalloc RT_stackmalloc2 RT_stackfree RT_iclifts2 RT_malloc0.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malcore_stmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_refillstmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malcore_m.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freelift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iclifts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_setshadow.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_artfacts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_stackmalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_stackmalloc2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_stackfree.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iclifts2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malloc0.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem rta_contracts : refill_stmt -> core_stmt_sec -> free_contract RTA -> rt_contracts RTA.
Proof.
  intros RF CS FR.
  exact (mkRTC RTA (rta_malloc (core_prim RF) CS) FR rta_free_null
           rta_memcpy rta_memset rta_memchr rta_strlen rta_strnlen rta_asan_memset
           rta_stack_malloc_0 rta_stack_malloc_2 rta_stack_malloc_3 rta_stack_malloc_6 rta_stack_malloc_7
           rta_stack_free_6 rta_stack_free_7 rta_memcmp (rta_malloc0 (core_prim5 RF))
           rta_set_shadow rta_art_facts).
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_malcore_m RT_malloc
  RT_freelift RT_iclifts RT_setshadow RT_artfacts RT_stackmalloc RT_stackmalloc2 RT_stackfree RT_iclifts2 RT_malloc0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem rta_contracts : refill_stmt -> core_stmt_sec -> free_contract RTA -> rt_contracts RTA.
Proof.
  intros RF CS FR.
  exact (mkRTC RTA (rta_malloc (core_prim RF) CS) FR rta_free_null
           rta_memcpy rta_memset rta_memchr rta_strlen rta_strnlen rta_asan_memcpy rta_asan_memset
           rta_stack_malloc_0 rta_stack_malloc_2 rta_stack_malloc_3 rta_stack_malloc_6 rta_stack_malloc_7
           rta_stack_free_6 rta_stack_free_7 rta_memcmp (rta_malloc0 (core_prim5 RF))
           rta_set_shadow rta_art_facts).
Qed.
