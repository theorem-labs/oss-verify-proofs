(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith NArith List Bool Lia.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import RT_iface RT_state RT_rep RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_reacore_stmt RT_reacore_m RT_reacore_case RT_reasec RT_refreeG RT_realloc RT_reallocG RT_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem rta_rcore_all_closed : rcore_stmt_all.
Proof. exact (rcore_all_of (rcore_prim_case (rcore_prim rta_refill_closed)) (rea_core_sec grant_node_ok fixed_commit_pab_ok)). Qed.

(* [comment removed for export] *)
Theorem rta_realloc_gen_closed : realloc_contract_any RTA.
Proof. exact (rta_realloc_gen_of rta_rcore_all_closed rta_drain_r_closed fixed_commit_ok). Qed.

(* [comment removed for export] *)
Lemma rta_realloc_prim_of_gen : realloc_contract RTA.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 n lo
         F1 F2 HIN Hn0 Hn HA0 HA1 HTP LR CR HART MI CO UC.
  apply (rta_realloc_gen_closed Σ PMc); try assumption. lia.
Qed.
