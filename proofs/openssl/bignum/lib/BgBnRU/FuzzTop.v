(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BgState BgLib BgExp BgTree BgBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInstBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgIface LibInstBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require W_mod_exp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_fuzz FuzzGap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem fuzz_one_walk_stmt_of_exp : forall (MEXP_STACK MEXPS_STACK : Z),
  MEXP_STACK <= W_fuzz.FUZZ_CALLEE_MAX -> MEXPS_STACK <= W_fuzz.FUZZ_CALLEE_MAX ->
  W_mod_exp.exp_stmt_f W_fuzz.BN_MOD_EXP MEXP_STACK (BN_mod_exp (tree_ops bptr)) None ->
  W_mod_exp.exp_stmt W_fuzz.BN_MOD_EXP_SIMPLE MEXPS_STACK (BN_mod_exp_simple (tree_ops bptr)) None ->
  FuzzGap.fuzz_one_walk_stmt W_fuzz.FUZZ_STACK.
Proof.
  intros MEXP_STACK MEXPS_STACK S1 S2 W1 W2. unfold FuzzGap.fuzz_one_walk_stmt. intros until d.
  exact (W_fuzz.fuzz_one_walk RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof MEXP_STACK MEXPS_STACK S1 S2 W1 W2
           ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s OW LB EA lo B errv D d).
Qed.

Theorem rfuzz_one_bgr_of_exp : forall (MEXP_STACK MEXPS_STACK : Z),
  MEXP_STACK <= W_fuzz.FUZZ_CALLEE_MAX -> MEXPS_STACK <= W_fuzz.FUZZ_CALLEE_MAX ->
  W_mod_exp.exp_stmt_f W_fuzz.BN_MOD_EXP MEXP_STACK (BN_mod_exp (tree_ops bptr)) None ->
  W_mod_exp.exp_stmt W_fuzz.BN_MOD_EXP_SIMPLE MEXPS_STACK (BN_mod_exp_simple (tree_ops bptr)) None ->
  rfuzz_one_stmt (LM := LM_bg unit tt bg_lib_one) (LSP := LSP_bgr unit tt bg_lib_one).
Proof.
  intros MEXP_STACK MEXPS_STACK S1 S2 W1 W2.
  apply (FuzzGap.rfuzz_of_walk W_fuzz.FUZZ_STACK); [unfold W_fuzz.FUZZ_STACK; lia|].
  exact (fuzz_one_walk_stmt_of_exp MEXP_STACK MEXPS_STACK S1 S2 W1 W2).
Qed.
End WithCeiling0.
