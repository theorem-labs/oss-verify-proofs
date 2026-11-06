(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA RT_iface RT_rep RT_gaps_iface RT_sys_grant RT_sys_fixed RT_calcore_stmt RT_calsec
  RT_calloc_sec RT_stackmallocF Ed_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CS0S_ok : core_stmt_sec0 := cal_core_sec grant_node_ok fixed_commit_pab_ok.

Lemma rta_ed_gaps : ed_gaps RTA.
Proof. exact (mkEdGaps RTA (rta_calloc_sec CS0S_ok) rta_stack_malloc_0F). Qed.
