(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnModel BnTree BgState BgLib BgExp BgTree.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import RT_iface RT_iface2 RT_rep RT_closed RT_closed2 D_libiface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import ARun ImplA UnwindA EdgesA EdgesInstA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import LibaBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require BgIface BgIfaceF.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXA Require HxaEceIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require ExpKitA ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import W_fuzzA FuzzGapA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma FUZZ_TOTAL_le : forall EXP_COST SIMPLE_COST, EXP_COST + SIMPLE_COST + 2048 <= FUZZ_COST -> FUZZ_TOTAL EXP_COST SIMPLE_COST <= FUZZ_COST.
Proof. intros EXP_COST SIMPLE_COST H. unfold FUZZ_TOTAL, BnIfaceA.MC, HxaEceIface.ECE_COST. lia. Qed.

Theorem fuzz_one_cps_RTA_of_exp : forall (EXP_STACK EXP_COST SIMPLE_STACK SIMPLE_COST : Z) (EXP_DEPTH SIMPLE_DEPTH : nat),
  0 <= EXP_STACK <= FUZZ_CALLEE_MAX -> 0 <= SIMPLE_STACK <= FUZZ_CALLEE_MAX -> 0 <= EXP_COST -> 0 <= SIMPLE_COST ->
  (EXP_DEPTH <= 4)%nat -> (SIMPLE_DEPTH <= 4)%nat ->
  FUZZ_TOTAL EXP_COST SIMPLE_COST <= FUZZ_COST ->
  (forall AR : ARun, @ar_FR AR = [] -> @ExpKitA.exp_stmtA_f AR UK_A BN_MOD_EXP EXP_STACK EXP_COST EXP_DEPTH (BN_mod_exp (tree_ops bptr)) None) ->
  (forall AR : ARun, @ar_FR AR = [] -> @ExpKitA.exp_stmtA AR UK_A BN_MOD_EXP_SIMPLE SIMPLE_STACK SIMPLE_COST SIMPLE_DEPTH (BN_mod_exp_simple (tree_ops bptr)) None) ->
  fuzz_one_cps' RTA (LIBA RTA).
Proof.
  intros EXP_STACK EXP_COST SIMPLE_STACK SIMPLE_COST EXP_DEPTH SIMPLE_DEPTH S1 S2 C1 C2 D1 D2 CT HEXP HSIM.
  exact (fuzz_one_cpsA RTA rta_contracts_all rta_contracts2 EXP_STACK EXP_COST SIMPLE_STACK SIMPLE_COST EXP_DEPTH SIMPLE_DEPTH S1 S2 C1 C2 D1 D2 CT HEXP HSIM).
Qed.

