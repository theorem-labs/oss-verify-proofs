(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_rep RT_closed D_libiface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import ARun BnIfaceA UnwindA EdgesA EdgesInstA LibaA W_fuzzA FuzzCpsA FuzzOneClosedA W_mulA W_mulA2.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaEceIface HxaEceClosed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Theorem BN_mul_walkA_closed : forall AR : ARun, @BN_mul_walkA_stmt AR UK_A BN_MUL_TOP_STACK BN_MUL_TOP_COST.
Proof. intros AR. exact (@BN_mul_walkA AR UK_A BE_A). Qed.

Lemma BN_MUL_TOP_STACK_bounds : 0 <= BN_MUL_TOP_STACK <= 0x18000.
Proof. unfold BN_MUL_TOP_STACK, BN_MUL_FIXED_STACKA. rewrite MUL_CST_val. lia. Qed.

Lemma BN_MUL_TOP_COST_bounds : 0 <= BN_MUL_TOP_COST /\ 13 * MC + BN_MUL_TOP_COST + ECE_COST <= FUZZ_COST.
Proof. unfold BN_MUL_TOP_COST, MC, ECE_COST, HxaEceIface.ECE_COST, FUZZ_COST. split; [lia|]. cbn. lia. Qed.

Theorem fuzz_one_cps_RTA : fuzz_one_cps' RTA (LIBA RTA).
Proof.
  exact (fuzz_one_cps_RTA_of_mul BN_MUL_TOP_STACK BN_MUL_TOP_COST BN_MUL_TOP_STACK_bounds BN_MUL_TOP_COST_bounds BN_mul_walkA_closed).
Qed.

Check (fuzz_one_cps_RTA : fuzz_one_cps' RTA (LIBA RTA)).
