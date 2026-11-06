(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_gaps_iface RT_state RT_rep RT_sys_stmt RT_sys_fixed RT_sys_grant RT_refill RT_calcore_stmt RT_calcore_m RT_calsec
  RT_callocK RT_gaps_proof.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_callocK_ok : calloc_contractK RTA.
Proof. exact (rta_callocK (core_prim0 RF_ok) (cal_core_sec grant_node_ok fixed_commit_pab_ok)). Qed.
