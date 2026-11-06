(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_malcore_m RT_freestmt RT_sys_stmt RT_iface_pem RT_realloc RTM_malcore_stmt RTM_malcore_m RT_memalign RT_iclifts_pem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_contracts_pem : refill_stmt -> drain_stmt -> fixed_commit_node -> rt_contracts_pem RTA.
Proof.
  intros RF DR FC.
  exact (mkRTCP RTA (rta_realloc (core_prim_g RF) DR FC) (rta_memalign (core_prim_al64 RF)) rta_memcmp rta_strcpy rta_asan_memmove).
Qed.
