(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_rep RT_closed D_defs D_libiface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import ARun BnHeapA BnIfaceA UnwindA EdgesA EdgesInstA LibaA W_cryptoA W_expandA W_lshiftA W_fuzzA FuzzCpsA W_div_tailA W_divA W_bndivA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaEceClosed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma BN_DIV_TOP_STACK_bounds : 0 <= BN_DIV_TOP_STACK <= 0x18000.
Proof.
  unfold BN_DIV_TOP_STACK, BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. lia.
Qed.

Lemma BN_DIV_TOP_COST_val : BN_DIV_TOP_COST = 10 * MC.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem BN_div_walkA_closed : forall AR : ARun, @BN_div_walkA_stmt AR UK_A BN_DIV_TOP_STACK BN_DIV_TOP_COST.
Proof. intros AR. exact (@BN_div_walkA AR UK_A BE_A). Qed.

Section MulPending.
  (* [comment removed for export] *)
  Variables (BN_MUL_STACK BN_MUL_COST : Z).
  Hypothesis MUL_STACK : 0 <= BN_MUL_STACK <= 0x18000.
  Hypothesis MUL_COST : 0 <= BN_MUL_COST /\ 13 * MC + BN_MUL_COST + ECE_COST <= FUZZ_COST.
  Hypothesis BN_mul_walkA_closed : forall AR : ARun, @BN_mul_walkA_stmt AR UK_A BN_MUL_STACK BN_MUL_COST.

  Theorem fuzz_one_cps_RTA_of_mul : fuzz_one_cps' RTA (LIBA RTA).
  Proof.
    apply (fuzz_one_cpsA RTA rta_contracts_all BN_MUL_STACK BN_DIV_TOP_STACK ECE_STACK BN_MUL_COST BN_DIV_TOP_COST ECE_COST
             MUL_STACK BN_DIV_TOP_STACK_bounds ECE_STACK_bounds (proj1 MUL_COST) ltac:(rewrite BN_DIV_TOP_COST_val; unfold MC; lia) ECE_COST_nonneg
             ltac:(rewrite BN_DIV_TOP_COST_val; pose proof MUL_COST; lia)
             BN_mul_walkA_closed BN_div_walkA_closed ece_cpsA_closed).
  Qed.
End MulPending.

Check fuzz_one_cps_RTA_of_mul.
