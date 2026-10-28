(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Th_mutex Fz_T_lock_new Fz_M_calloc Fz_I1_defs Fz_I1_new Fz_M_aligned Fz_G_ossl_lib_ctx_get_ex_data_global Fz_G_ossl_do_ex_data_init F_memset Fz_T_sa_new Fz_G_ossl_method_store_new Fz_G_ossl_prov_conf_ctx_new. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_strdup Fz_T_atomic Fz_T_once Fz_I3_base Fz_G_ossl_rand_ctx_new Fz_I2_dcache Fz_T_sk Fz_G_OPENSSL_sk_new Fz_G_ossl_provider_store_new Fz_I2_ppi Fz_I2_namemap Fz_I2_pdefns Fz_G_ossl_ctx_global_properties_new Fz_G_ossl_bio_core_globals_new Fz_G_ossl_prov_drbg_nonce_ctx_new Fz_G_ossl_self_test_set_callback_new Fz_G_ossl_indicator_set_callback_new Th_mutex_init Fz_G_ossl_crypto_mutex_new Th_cond Fz_G_ossl_crypto_condvar_new Fz_G_ossl_threads_ctx_new Fz_G_ossl_child_prov_ctx_new Fz_G_COMP_zlib Fz_G_COMP_get_type Fz_G_ossl_load_builtin_compressions Fz_I2_pstring Fz_I2_htnew Fz_T_rcu Fz_M_realloc Fz_kit_ra.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tslia ::= wp_tslia.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_G_context_init : Z := 0xe4374.
Definition context_init_STACK : Z := 32 + PPI_STACK.

Definition context_init_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q1_1 A1_1 q2_1 A2_1 q3_1 A3_1 q3_2 A3_2 q3_3 A3_3 q3_4 A3_4 q3_5 A3_5 q3_6 A3_6 q3_7 A3_7 q3_8 A3_8 q3_9 A3_9 q3_10 A3_10 q3_11 A3_11 q3_12 A3_12 q3_13 A3_13 q3_14 A3_14 q3_15 A3_15 q4_1 A4_1 q4_2 A4_2 q5_1 A5_1 q5_2 A5_2 q5_3 A5_3 q6_1 A6_1 q6_2 A6_2 q6_3 A6_3 q6_4 A6_4 q6_5 A6_5 q6_6 A6_6 q6_7 A6_7 q6_8 A6_8 q6_9 A6_9 q6_10 A6_10 q6_11 A6_11 q6_12 A6_12 q6_13 A6_13 q6_14 A6_14 q6_15 A6_15 q7_1 A7_1 q7_2 A7_2 q7_3 A7_3 q7_4 A7_4 q8_1 A8_1 q8_2 A8_2 q8_3 A8_3 q8_4 A8_4 q8_5 A8_5 q8_6 A8_6 q8_7 A8_7 q8_8 A8_8 q8_9 A8_9 q8_10 A8_10 q8_11 A8_11 q8_12 A8_12 q8_13 A8_13 q8_14 A8_14 q8_15 A8_15 q9_1 A9_1 q9_2 A9_2 q9_3 A9_3 q9_4 A9_4 q9_5 A9_5 q9_6 A9_6 q9_7 A9_7 q9_8 A9_8 q9_9 A9_9 q9_10 A9_10 q9_11 A9_11 q9_12 A9_12 q9_13 A9_13 q9_14 A9_14 q9_15 A9_15 q10_1 A10_1 q10_2 A10_2 q10_3 A10_3 q10_4 A10_4 q10_5 A10_5 q11_1 A11_1 q11_2 A11_2 q11_3 A11_3 q11_4 A11_4 q11_5 A11_5 q11_6 A11_6 q11_7 A11_7 q11_8 A11_8 q12_1 A12_1 q12_2 A12_2 q12_3 A12_3 q12_4 A12_4 q12_5 A12_5 q12_6 A12_6 q12_7 A12_7 q12_8 A12_8 q12_9 A12_9 q13_1 A13_1 q13_2 A13_2 q14_1 A14_1 q15_1 A15_1 q16_1 A16_1 q16_2 A16_2 q17_1 A17_1 q18_1 A18_1 q19_1 A19_1 q19_2 A19_2 q19_3 A19_3 q20_1 A20_1 q21_1 A21_1 q21_2 A21_2 q21_3 A21_3 q21_4 A21_4 q21_5 A21_5 q21_6 A21_6 q21_7 A21_7 q21_8 A21_8 q21_9 A21_9 q21_10 A21_10 q21_11 A21_11 q21_12 A21_12 q21_13 A21_13 q21_14 A21_14 q21_15 A21_15 q21_16 A21_16 q21_17 A21_17 q21_18 A21_18 q22_1 A22_1,
       v = (Z_to_bv 64 1)
    /\ LBall' = (q22_1, A22_1, 56) :: (q21_18, A21_18, 24) :: (q21_17, A21_17, 18) :: (q21_16, A21_16, 24) :: (q21_15, A21_15, 32) :: (q21_14, A21_14, 19) :: (q21_13, A21_13, 24) :: (q21_12, A21_12, 25) :: (q21_11, A21_11, 24) :: (q21_10, A21_10, 48) :: (q21_9, A21_9, 21) :: (q21_8, A21_8, 24) :: (q21_7, A21_7, 22) :: (q21_6, A21_6, 24) :: (q21_5, A21_5, 20) :: (q21_4, A21_4, 24) :: (q21_3, A21_3, 23) :: (q21_2, A21_2, 24) :: (q21_1, A21_1, 24) :: (q20_1, A20_1, 88) :: (q19_3, A19_3, 48) :: (q19_2, A19_2, 40) :: (q19_1, A19_1, 32) :: (q18_1, A18_1, 8) :: (q17_1, A17_1, 16) :: (q16_2, A16_2, 40) :: (q16_1, A16_1, 16) :: (q15_1, A15_1, 56) :: (q14_1, A14_1, 16) :: (q13_2, A13_2, 128) :: (q13_1, A13_1, 104) :: (q12_9, A12_9, 56) :: (q12_8, A12_8, 16) :: (q12_7, A12_7, 264) :: (q12_6, A12_6, 32768) :: (q12_5, A12_5, 24) :: (q12_4, A12_4, 40) :: (q12_3, A12_3, 96) :: (q12_2, A12_2, 40) :: (q12_1, A12_1, 40) :: (q11_8, A11_8, 56) :: (q11_7, A11_7, 56) :: (q11_6, A11_6, 128) :: (q11_5, A11_5, 104) :: (q11_4, A11_4, 128) :: (q11_3, A11_3, 104) :: (q11_2, A11_2, 40) :: (q11_1, A11_1, 48) :: (q10_5, A10_5, 40) :: (q10_4, A10_4, 56) :: (q10_3, A10_3, 40) :: (q10_2, A10_2, 56) :: (q10_1, A10_1, 80) :: (q9_15, A9_15, 40) :: (q9_14, A9_14, 40) :: (q9_13, A9_13, 40) :: (q9_12, A9_12, 32) :: (q9_11, A9_11, 40) :: (q9_10, A9_10, 40) :: (q9_9, A9_9, 32) :: (q9_8, A9_8, 40) :: (q9_7, A9_7, 40) :: (q9_6, A9_6, 32) :: (q9_5, A9_5, 40) :: (q9_4, A9_4, 40) :: (q9_3, A9_3, 32) :: (q9_2, A9_2, 384) :: (q9_1, A9_1, 24) :: (q8_15, A8_15, 40) :: (q8_14, A8_14, 40) :: (q8_13, A8_13, 40) :: (q8_12, A8_12, 32) :: (q8_11, A8_11, 40) :: (q8_10, A8_10, 40) :: (q8_9, A8_9, 32) :: (q8_8, A8_8, 40) :: (q8_7, A8_7, 40) :: (q8_6, A8_6, 32) :: (q8_5, A8_5, 40) :: (q8_4, A8_4, 40) :: (q8_3, A8_3, 32) :: (q8_2, A8_2, 384) :: (q8_1, A8_1, 24) :: (q7_4, A7_4, 128) :: (q7_3, A7_3, 104) :: (q7_2, A7_2, 40) :: (q7_1, A7_1, 16) :: (q6_15, A6_15, 40) :: (q6_14, A6_14, 40) :: (q6_13, A6_13, 40) :: (q6_12, A6_12, 32) :: (q6_11, A6_11, 40) :: (q6_10, A6_10, 40) :: (q6_9, A6_9, 32) :: (q6_8, A6_8, 40) :: (q6_7, A6_7, 40) :: (q6_6, A6_6, 32) :: (q6_5, A6_5, 40) :: (q6_4, A6_4, 40) :: (q6_3, A6_3, 32) :: (q6_2, A6_2, 384) :: (q6_1, A6_1, 24) :: (q5_3, A5_3, 40) :: (q5_2, A5_2, 5) :: (q5_1, A5_1, 88) :: (q4_2, A4_2, 40) :: (q4_1, A4_1, 16) :: (q3_15, A3_15, 40) :: (q3_14, A3_14, 40) :: (q3_13, A3_13, 40) :: (q3_12, A3_12, 32) :: (q3_11, A3_11, 40) :: (q3_10, A3_10, 40) :: (q3_9, A3_9, 32) :: (q3_8, A3_8, 40) :: (q3_7, A3_7, 40) :: (q3_6, A3_6, 32) :: (q3_5, A3_5, 40) :: (q3_4, A3_4, 40) :: (q3_3, A3_3, 32) :: (q3_2, A3_2, 384) :: (q3_1, A3_1, 24) :: (q2_1, A2_1, 40) :: (q1_1, A1_1, 40) :: LBall
    /\ rw_cells usegs m' A1_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A2_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_2 [C8 (Z_to_bv 64 A3_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_4); C8 (Z_to_bv 64 A3_5); C8 (Z_to_bv 64 A3_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_7); C8 (Z_to_bv 64 A3_8); C8 (Z_to_bv 64 A3_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_10); C8 (Z_to_bv 64 A3_11); C8 (Z_to_bv 64 A3_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_13); C8 (Z_to_bv 64 A3_14)]
    /\ rw_cells usegs m' A3_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A3_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A3_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A3_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A3_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A3_2); C8 (Z_to_bv 64 A3_15)]
    /\ rw_cells usegs m' A4_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A4_1 [C8 (Z_to_bv 64 A4_2); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells usegs m' A5_3 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A5_2 [CB (S (length [Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 112; Z_to_bv 8 115])) ([Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 112; Z_to_bv 8 115] ++ [Z_to_bv 8 0])]
    /\ rw_cells usegs m' A5_1 [C8 (Z_to_bv 64 A5_3); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 A5_2); CB 48 (repeat (Z_to_bv 8 0) 48)]
    /\ rw_cells usegs m' A6_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_2 [C8 (Z_to_bv 64 A6_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_4); C8 (Z_to_bv 64 A6_5); C8 (Z_to_bv 64 A6_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_7); C8 (Z_to_bv 64 A6_8); C8 (Z_to_bv 64 A6_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_10); C8 (Z_to_bv 64 A6_11); C8 (Z_to_bv 64 A6_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_13); C8 (Z_to_bv 64 A6_14)]
    /\ rw_cells usegs m' A6_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A6_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A6_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A6_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A6_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A6_2); C8 (Z_to_bv 64 A6_15)]
    /\ rw_cells usegs m' A8_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_2 [C8 (Z_to_bv 64 A8_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_4); C8 (Z_to_bv 64 A8_5); C8 (Z_to_bv 64 A8_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_7); C8 (Z_to_bv 64 A8_8); C8 (Z_to_bv 64 A8_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_10); C8 (Z_to_bv 64 A8_11); C8 (Z_to_bv 64 A8_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_13); C8 (Z_to_bv 64 A8_14)]
    /\ rw_cells usegs m' A8_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A8_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A8_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A8_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A8_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A8_2); C8 (Z_to_bv 64 A8_15)]
    /\ rw_cells usegs m' A9_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_2 [C8 (Z_to_bv 64 A9_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_4); C8 (Z_to_bv 64 A9_5); C8 (Z_to_bv 64 A9_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_7); C8 (Z_to_bv 64 A9_8); C8 (Z_to_bv 64 A9_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_10); C8 (Z_to_bv 64 A9_11); C8 (Z_to_bv 64 A9_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_13); C8 (Z_to_bv 64 A9_14)]
    /\ rw_cells usegs m' A9_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A9_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A9_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A9_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A9_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A9_2); C8 (Z_to_bv 64 A9_15)]
    /\ rw_cells usegs m' A10_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A10_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 994472); C8 (Z_to_bv 64 1004348); C8 (Z_to_bv 64 1004268); C8 (Z_to_bv 64 1004392)]
    /\ rw_cells usegs m' A10_3 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A10_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1004432); C8 (Z_to_bv 64 1004308); C8 (Z_to_bv 64 1004476)]
    /\ rw_cells usegs m' A10_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A10_2); C8 (Z_to_bv 64 A10_4); C8 (Z_to_bv 64 A10_3); C8 (Z_to_bv 64 A10_5); CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 (Z.lor (bv_unsigned (zxb (Z_to_bv 8 0))) 1)); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells usegs m' A14_1 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells usegs m' A15_1 [CB 56 (repeat (Z_to_bv 8 0) 56)]
    /\ rw_cells usegs m' A16_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A16_1 [C8 (Z_to_bv 64 A16_2); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells usegs m' A17_1 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells usegs m' A18_1 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells usegs m' A19_3 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A19_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A19_1 [CB 16 (repeat (Z_to_bv 8 0) 16); C8 (Z_to_bv 64 A19_2); C8 (Z_to_bv 64 A19_3)]
    /\ rw_cells usegs m' A20_1 [CB 88 (repeat (Z_to_bv 8 0) 88)]
    /\ rw_cells usegs m' A22_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2803492); C8 (Z_to_bv 64 2803608); C8 (Z_to_bv 64 2803692); C8 (Z_to_bv 64 2803652)]
    /\ rw_cells usegs m' 3334008 [C8 (Z_to_bv 64 A3_1); C8 (Z_to_bv 64 A10_1); C8 (Z_to_bv 64 A12_1); C8 (Z_to_bv 64 A13_1); C8 (Z_to_bv 64 A14_1); C8 (Z_to_bv 64 A5_1); C8 (Z_to_bv 64 A16_1); C8 (Z_to_bv 64 A4_1); C8 (Z_to_bv 64 A15_1); C8 (Z_to_bv 64 A20_1); C8 (Z_to_bv 64 A6_1); C8 (Z_to_bv 64 A7_1); C8 (Z_to_bv 64 A8_1); C8 (Z_to_bv 64 A9_1); C8 (Z_to_bv 64 A17_1); C8 (Z_to_bv 64 A18_1); C8 (Z_to_bv 64 A19_1); C8 (Z_to_bv 64 A22_1)]
    /\ rw_cells usegs m' 3334000 [C8 (Z_to_bv 64 A11_1)]
    /\ rw_cells usegs m' 3333840 [C8 (Z_to_bv 64 A2_1)]
    /\ rw_cells usegs m' 3333832 [C8 (Z_to_bv 64 A1_1)].

Definition context_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (x_2e82f0 : word) (x_2e8338 x_2e8340 x_2e83e0 x_2e83e8 : list byte)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (126 <= f)%nat -> croom L (119) (6) (83768) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - context_init_STACK -> bv_unsigned sp mod 16 = 0 ->
  a0 = Z_to_bv 64 0x32dec8 ->
  rw_cells usegs m 0x32de28 [C1 (Z_to_bv 8 0)] ->
  rw_cells usegs m 0x32de40 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] ->
  rw_cells usegs m 0x32de80 [C8 x_2e82f0] ->
  rw_cells usegs m 0x32dec8 [CB 8 x_2e8338] ->
  rw_cells usegs m 0x32ded0 [CB 8 x_2e8340] ->
  rw_cells usegs m 0x32df70 [CB 8 x_2e83e0] ->
  rw_cells usegs m 0x32df78 [CB 144 x_2e83e8] ->
  rw_cells usegs m 0x351010 [C4 (Z_to_bv 64 0)] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_G_context_init) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z 126
                (119) (6) (83768) (context_init_res LBall L)).

Lemma context_init_part2 : crypto_zalloc_stmt -> ossl_property_parse_init_fp_stmt -> 
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x_2e83e8 : list byte)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (q1_1 : bptr) (A1_1 : Z) (st1 : PState) (mb1 : mem) (q2_1 : bptr) (A2_1 : Z) (st2 : PState) (mb2 : mem) (q3_1 : bptr) (A3_1 : Z) (q3_2 : bptr) (A3_2 : Z) (q3_3 : bptr) (A3_3 : Z) (q3_4 : bptr) (A3_4 : Z) (q3_5 : bptr) (A3_5 : Z) (q3_6 : bptr) (A3_6 : Z) (q3_7 : bptr) (A3_7 : Z) (q3_8 : bptr) (A3_8 : Z) (q3_9 : bptr) (A3_9 : Z) (q3_10 : bptr) (A3_10 : Z) (q3_11 : bptr) (A3_11 : Z) (q3_12 : bptr) (A3_12 : Z) (q3_13 : bptr) (A3_13 : Z) (q3_14 : bptr) (A3_14 : Z) (q3_15 : bptr) (A3_15 : Z) (st3 : PState) (mb3 : mem) (q4_1 : bptr) (A4_1 : Z) (q4_2 : bptr) (A4_2 : Z) (st4 : PState) (mb4 : mem) (q5_1 : bptr) (A5_1 : Z) (q5_2 : bptr) (A5_2 : Z) (q5_3 : bptr) (A5_3 : Z) (st5 : PState) (mb5 : mem) (q6_1 : bptr) (A6_1 : Z) (q6_2 : bptr) (A6_2 : Z) (q6_3 : bptr) (A6_3 : Z) (q6_4 : bptr) (A6_4 : Z) (q6_5 : bptr) (A6_5 : Z) (q6_6 : bptr) (A6_6 : Z) (q6_7 : bptr) (A6_7 : Z) (q6_8 : bptr) (A6_8 : Z) (q6_9 : bptr) (A6_9 : Z) (q6_10 : bptr) (A6_10 : Z) (q6_11 : bptr) (A6_11 : Z) (q6_12 : bptr) (A6_12 : Z) (q6_13 : bptr) (A6_13 : Z) (q6_14 : bptr) (A6_14 : Z) (q6_15 : bptr) (A6_15 : Z) (st6 : PState) (mb6 : mem) (q7_1 : bptr) (A7_1 : Z) (q7_2 : bptr) (A7_2 : Z) (q7_3 : bptr) (A7_3 : Z) (q7_4 : bptr) (A7_4 : Z) (st7 : PState) (mb7 : mem) (q8_1 : bptr) (A8_1 : Z) (q8_2 : bptr) (A8_2 : Z) (q8_3 : bptr) (A8_3 : Z) (q8_4 : bptr) (A8_4 : Z) (q8_5 : bptr) (A8_5 : Z) (q8_6 : bptr) (A8_6 : Z) (q8_7 : bptr) (A8_7 : Z) (q8_8 : bptr) (A8_8 : Z) (q8_9 : bptr) (A8_9 : Z) (q8_10 : bptr) (A8_10 : Z) (q8_11 : bptr) (A8_11 : Z) (q8_12 : bptr) (A8_12 : Z) (q8_13 : bptr) (A8_13 : Z) (q8_14 : bptr) (A8_14 : Z) (q8_15 : bptr) (A8_15 : Z) (st8 : PState) (mb8 : mem) (q9_1 : bptr) (A9_1 : Z) (q9_2 : bptr) (A9_2 : Z) (q9_3 : bptr) (A9_3 : Z) (q9_4 : bptr) (A9_4 : Z) (q9_5 : bptr) (A9_5 : Z) (q9_6 : bptr) (A9_6 : Z) (q9_7 : bptr) (A9_7 : Z) (q9_8 : bptr) (A9_8 : Z) (q9_9 : bptr) (A9_9 : Z) (q9_10 : bptr) (A9_10 : Z) (q9_11 : bptr) (A9_11 : Z) (q9_12 : bptr) (A9_12 : Z) (q9_13 : bptr) (A9_13 : Z) (q9_14 : bptr) (A9_14 : Z) (q9_15 : bptr) (A9_15 : Z) (st9 : PState) (mb9 : mem) (q10_1 : bptr) (A10_1 : Z) (q10_2 : bptr) (A10_2 : Z) (q10_3 : bptr) (A10_3 : Z) (q10_4 : bptr) (A10_4 : Z) (q10_5 : bptr) (A10_5 : Z) (st10 : PState) (mb10 : mem) (q11_1 : bptr) (A11_1 : Z) (q11_2 : bptr) (A11_2 : Z) (q11_3 : bptr) (A11_3 : Z) (q11_4 : bptr) (A11_4 : Z) (q11_5 : bptr) (A11_5 : Z) (q11_6 : bptr) (A11_6 : Z) (q11_7 : bptr) (A11_7 : Z) (q11_8 : bptr) (A11_8 : Z) (st11 : PState) (mb11 : mem) (q12_1 : bptr) (A12_1 : Z) (q12_2 : bptr) (A12_2 : Z) (q12_3 : bptr) (A12_3 : Z) (q12_4 : bptr) (A12_4 : Z) (q12_5 : bptr) (A12_5 : Z) (q12_6 : bptr) (A12_6 : Z) (q12_7 : bptr) (A12_7 : Z) (q12_8 : bptr) (A12_8 : Z) (q12_9 : bptr) (A12_9 : Z) (st12 : PState) (mb12 : mem) (q13_1 : bptr) (A13_1 : Z) (q13_2 : bptr) (A13_2 : Z) (st13 : PState) (mb13 : mem) (q14_1 : bptr) (A14_1 : Z) (st14 : PState) (mb14 : mem) (q15_1 : bptr) (A15_1 : Z) (st15 : PState) (mb15 : mem) (q16_1 : bptr) (A16_1 : Z) (q16_2 : bptr) (A16_2 : Z) (u0_16 : word) (u1_16 : word) (u2_16 : word) (b1_16 : word) (b2_16 : word) (b3_16 : word) (b4_16 : word) (b5_16 : word) (b6_16 : word) (b7_16 : word) (u3_16 : word) (u4_16 : word) (u5_16 : word) (u6_16 : word) (f16 : nat) (st16 : PState) (mb16 : mem) (ma0 : mem) (ma1 : mem) (ma3 : mem) (ma4 : mem) (ma5 : mem) (ma6 : mem) (ma7 : mem) (ma8 : mem) (ma9 : mem) (ma10 : mem) (ma11 : mem) (ma12 : mem) (ma13 : mem) (ma14 : mem) (ma15 : mem) (junk : list byte),
  let LBc0 := LBall in let Lc0 := L in
  let LBc1 := (q1_1, A1_1, 40) :: LBc0 in let Lc1 := (q1_1, 40) :: Lc0 in
  let LBc2 := (q2_1, A2_1, 40) :: LBc1 in let Lc2 := (q2_1, 40) :: Lc1 in
  let LBc3 := (q3_15, A3_15, 40) :: (q3_14, A3_14, 40) :: (q3_13, A3_13, 40) :: (q3_12, A3_12, 32) :: (q3_11, A3_11, 40) :: (q3_10, A3_10, 40) :: (q3_9, A3_9, 32) :: (q3_8, A3_8, 40) :: (q3_7, A3_7, 40) :: (q3_6, A3_6, 32) :: (q3_5, A3_5, 40) :: (q3_4, A3_4, 40) :: (q3_3, A3_3, 32) :: (q3_2, A3_2, 384) :: (q3_1, A3_1, 24) :: LBc2 in let Lc3 := (q3_15, 40) :: (q3_14, 40) :: (q3_13, 40) :: (q3_12, 32) :: (q3_11, 40) :: (q3_10, 40) :: (q3_9, 32) :: (q3_8, 40) :: (q3_7, 40) :: (q3_6, 32) :: (q3_5, 40) :: (q3_4, 40) :: (q3_3, 32) :: (q3_2, 384) :: (q3_1, 24) :: Lc2 in
  let LBc4 := (q4_2, A4_2, 40) :: (q4_1, A4_1, 16) :: LBc3 in let Lc4 := (q4_2, 40) :: (q4_1, 16) :: Lc3 in
  let LBc5 := (q5_3, A5_3, 40) :: (q5_2, A5_2, 5) :: (q5_1, A5_1, 88) :: LBc4 in let Lc5 := (q5_3, 40) :: (q5_2, 5) :: (q5_1, 88) :: Lc4 in
  let LBc6 := (q6_15, A6_15, 40) :: (q6_14, A6_14, 40) :: (q6_13, A6_13, 40) :: (q6_12, A6_12, 32) :: (q6_11, A6_11, 40) :: (q6_10, A6_10, 40) :: (q6_9, A6_9, 32) :: (q6_8, A6_8, 40) :: (q6_7, A6_7, 40) :: (q6_6, A6_6, 32) :: (q6_5, A6_5, 40) :: (q6_4, A6_4, 40) :: (q6_3, A6_3, 32) :: (q6_2, A6_2, 384) :: (q6_1, A6_1, 24) :: LBc5 in let Lc6 := (q6_15, 40) :: (q6_14, 40) :: (q6_13, 40) :: (q6_12, 32) :: (q6_11, 40) :: (q6_10, 40) :: (q6_9, 32) :: (q6_8, 40) :: (q6_7, 40) :: (q6_6, 32) :: (q6_5, 40) :: (q6_4, 40) :: (q6_3, 32) :: (q6_2, 384) :: (q6_1, 24) :: Lc5 in
  let LBc7 := (q7_4, A7_4, 128) :: (q7_3, A7_3, 104) :: (q7_2, A7_2, 40) :: (q7_1, A7_1, 16) :: LBc6 in let Lc7 := (q7_4, 128) :: (q7_3, 104) :: (q7_2, 40) :: (q7_1, 16) :: Lc6 in
  let LBc8 := (q8_15, A8_15, 40) :: (q8_14, A8_14, 40) :: (q8_13, A8_13, 40) :: (q8_12, A8_12, 32) :: (q8_11, A8_11, 40) :: (q8_10, A8_10, 40) :: (q8_9, A8_9, 32) :: (q8_8, A8_8, 40) :: (q8_7, A8_7, 40) :: (q8_6, A8_6, 32) :: (q8_5, A8_5, 40) :: (q8_4, A8_4, 40) :: (q8_3, A8_3, 32) :: (q8_2, A8_2, 384) :: (q8_1, A8_1, 24) :: LBc7 in let Lc8 := (q8_15, 40) :: (q8_14, 40) :: (q8_13, 40) :: (q8_12, 32) :: (q8_11, 40) :: (q8_10, 40) :: (q8_9, 32) :: (q8_8, 40) :: (q8_7, 40) :: (q8_6, 32) :: (q8_5, 40) :: (q8_4, 40) :: (q8_3, 32) :: (q8_2, 384) :: (q8_1, 24) :: Lc7 in
  let LBc9 := (q9_15, A9_15, 40) :: (q9_14, A9_14, 40) :: (q9_13, A9_13, 40) :: (q9_12, A9_12, 32) :: (q9_11, A9_11, 40) :: (q9_10, A9_10, 40) :: (q9_9, A9_9, 32) :: (q9_8, A9_8, 40) :: (q9_7, A9_7, 40) :: (q9_6, A9_6, 32) :: (q9_5, A9_5, 40) :: (q9_4, A9_4, 40) :: (q9_3, A9_3, 32) :: (q9_2, A9_2, 384) :: (q9_1, A9_1, 24) :: LBc8 in let Lc9 := (q9_15, 40) :: (q9_14, 40) :: (q9_13, 40) :: (q9_12, 32) :: (q9_11, 40) :: (q9_10, 40) :: (q9_9, 32) :: (q9_8, 40) :: (q9_7, 40) :: (q9_6, 32) :: (q9_5, 40) :: (q9_4, 40) :: (q9_3, 32) :: (q9_2, 384) :: (q9_1, 24) :: Lc8 in
  let LBc10 := (q10_5, A10_5, 40) :: (q10_4, A10_4, 56) :: (q10_3, A10_3, 40) :: (q10_2, A10_2, 56) :: (q10_1, A10_1, 80) :: LBc9 in let Lc10 := (q10_5, 40) :: (q10_4, 56) :: (q10_3, 40) :: (q10_2, 56) :: (q10_1, 80) :: Lc9 in
  let LBc11 := (q11_8, A11_8, 56) :: (q11_7, A11_7, 56) :: (q11_6, A11_6, 128) :: (q11_5, A11_5, 104) :: (q11_4, A11_4, 128) :: (q11_3, A11_3, 104) :: (q11_2, A11_2, 40) :: (q11_1, A11_1, 48) :: LBc10 in let Lc11 := (q11_8, 56) :: (q11_7, 56) :: (q11_6, 128) :: (q11_5, 104) :: (q11_4, 128) :: (q11_3, 104) :: (q11_2, 40) :: (q11_1, 48) :: Lc10 in
  let LBc12 := (q12_9, A12_9, 56) :: (q12_8, A12_8, 16) :: (q12_7, A12_7, 264) :: (q12_6, A12_6, 32768) :: (q12_5, A12_5, 24) :: (q12_4, A12_4, 40) :: (q12_3, A12_3, 96) :: (q12_2, A12_2, 40) :: (q12_1, A12_1, 40) :: LBc11 in let Lc12 := (q12_9, 56) :: (q12_8, 16) :: (q12_7, 264) :: (q12_6, 32816) :: (q12_5, 24) :: (q12_4, 40) :: (q12_3, 96) :: (q12_2, 40) :: (q12_1, 40) :: Lc11 in
  let LBc13 := (q13_2, A13_2, 128) :: (q13_1, A13_1, 104) :: LBc12 in let Lc13 := (q13_2, 128) :: (q13_1, 104) :: Lc12 in
  let LBc14 := (q14_1, A14_1, 16) :: LBc13 in let Lc14 := (q14_1, 16) :: Lc13 in
  let LBc15 := (q15_1, A15_1, 56) :: LBc14 in let Lc15 := (q15_1, 56) :: Lc14 in
  let LBc16 := (q16_2, A16_2, 40) :: (q16_1, A16_1, 16) :: LBc15 in let Lc16 := (q16_2, 40) :: (q16_1, 16) :: Lc15 in
  (bv_unsigned sp <= B) ->
  ((126 <= f)%nat) ->
  (croom L (119) (6) (83768)) ->
  (cl_own LBall LB L) ->
  (lo <= bv_unsigned sp - 8576) ->
  (bv_unsigned sp mod 16 = 0) ->
  (cstate st16 LBc16 LB Lc16 mb16 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B) ->
  (rw_cells usegs mb16 3334008 [C8 (Z_to_bv 64 A3_1); C8 (Z_to_bv 64 A10_1); C8 (Z_to_bv 64 A12_1); C8 (Z_to_bv 64 A13_1); C8 (Z_to_bv 64 A14_1); C8 (Z_to_bv 64 A5_1); CB 8 (drop 40 (take 48 (drop 8 x_2e83e8))); C8 (Z_to_bv 64 A4_1); C8 (Z_to_bv 64 A15_1); CB 8 (drop 8 (take 16 (drop 56 (drop 8 x_2e83e8)))); C8 (Z_to_bv 64 A6_1); C8 (Z_to_bv 64 A7_1); C8 (Z_to_bv 64 A8_1); C8 (Z_to_bv 64 A9_1); CB 32 (drop 8 (drop 8 (drop 8 (drop 24 (drop 56 (drop 8 x_2e83e8))))))]) ->
  (rw_cells usegs mb16 3334000 [C8 (Z_to_bv 64 A11_1)]) ->
  (rw_cells usegs mb16 3333840 [C8 (Z_to_bv 64 A2_1)]) ->
  (rw_cells usegs mb16 3333832 [C8 (Z_to_bv 64 A1_1)]) ->
  (rw_cells usegs mb16 (bv_unsigned sp + -32) [CB 8 (take 8 (take 16 (take 24 junk))); C8 s1; C8 s0; C8 ra]) ->
  (psd_rep mb16 LBc16 Lc16 (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) ->
  ((f <= f16 + 99)%nat) ->
  (cgrow L Lc16 93 6 83768) ->
  ((In (q1_1, A1_1, 40) LBc1 ∧ wp_box (rw_cells usegs mb1 A1_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q2_1, A2_1, 40) LBc2 ∧ wp_box (rw_cells usegs mb2 A2_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q3_15, A3_15, 40) LBc3 ∧ In (q3_14, A3_14, 40) LBc3 ∧ In (q3_13, A3_13, 40) LBc3 ∧ In (q3_12, A3_12, 32) LBc3 ∧ In (q3_11, A3_11, 40) LBc3 ∧ In (q3_10, A3_10, 40) LBc3 ∧ In (q3_9, A3_9, 32) LBc3 ∧ In (q3_8, A3_8, 40) LBc3 ∧ In (q3_7, A3_7, 40) LBc3 ∧ In (q3_6, A3_6, 32) LBc3 ∧ In (q3_5, A3_5, 40) LBc3 ∧ In (q3_4, A3_4, 40) LBc3 ∧ In (q3_3, A3_3, 32) LBc3 ∧ In (q3_2, A3_2, 384) LBc3 ∧ In (q3_1, A3_1, 24) LBc3 ∧ wp_box (rw_cells usegs mb3 A3_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A3_2); C8 (Z_to_bv 64 A3_15)]) ∧ wp_box (rw_cells usegs mb3 A3_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb3 A3_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb3 A3_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb3 A3_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb3 A3_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb3 A3_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb3 A3_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb3 A3_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb3 A3_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb3 A3_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb3 A3_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb3 A3_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb3 A3_2 [C8 (Z_to_bv 64 A3_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_4); C8 (Z_to_bv 64 A3_5); C8 (Z_to_bv 64 A3_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_7); C8 (Z_to_bv 64 A3_8); C8 (Z_to_bv 64 A3_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_10); C8 (Z_to_bv 64 A3_11); C8 (Z_to_bv 64 A3_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_13); C8 (Z_to_bv 64 A3_14)]) ∧ wp_box (rw_cells usegs mb3 A3_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q4_2, A4_2, 40) LBc4 ∧ In (q4_1, A4_1, 16) LBc4 ∧ wp_box (rw_cells usegs mb4 A4_1 [C8 (Z_to_bv 64 A4_2); CB 8 (repeat (Z_to_bv 8 0) 8)]) ∧ wp_box (rw_cells usegs mb4 A4_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q5_3, A5_3, 40) LBc5 ∧ In (q5_2, A5_2, 5) LBc5 ∧ In (q5_1, A5_1, 88) LBc5 ∧ wp_box (rw_cells usegs mb5 A5_1 [C8 (Z_to_bv 64 A5_3); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 A5_2); CB 48 (repeat (Z_to_bv 8 0) 48)]) ∧ wp_box (rw_cells usegs mb5 A5_2 [CB (S (length [Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 112; Z_to_bv 8 115])) ([Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 112; Z_to_bv 8 115] ++ [Z_to_bv 8 0])]) ∧ wp_box (rw_cells usegs mb5 A5_3 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q6_15, A6_15, 40) LBc6 ∧ In (q6_14, A6_14, 40) LBc6 ∧ In (q6_13, A6_13, 40) LBc6 ∧ In (q6_12, A6_12, 32) LBc6 ∧ In (q6_11, A6_11, 40) LBc6 ∧ In (q6_10, A6_10, 40) LBc6 ∧ In (q6_9, A6_9, 32) LBc6 ∧ In (q6_8, A6_8, 40) LBc6 ∧ In (q6_7, A6_7, 40) LBc6 ∧ In (q6_6, A6_6, 32) LBc6 ∧ In (q6_5, A6_5, 40) LBc6 ∧ In (q6_4, A6_4, 40) LBc6 ∧ In (q6_3, A6_3, 32) LBc6 ∧ In (q6_2, A6_2, 384) LBc6 ∧ In (q6_1, A6_1, 24) LBc6 ∧ wp_box (rw_cells usegs mb6 A6_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A6_2); C8 (Z_to_bv 64 A6_15)]) ∧ wp_box (rw_cells usegs mb6 A6_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb6 A6_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb6 A6_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb6 A6_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb6 A6_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb6 A6_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb6 A6_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb6 A6_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb6 A6_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb6 A6_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb6 A6_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb6 A6_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb6 A6_2 [C8 (Z_to_bv 64 A6_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_4); C8 (Z_to_bv 64 A6_5); C8 (Z_to_bv 64 A6_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_7); C8 (Z_to_bv 64 A6_8); C8 (Z_to_bv 64 A6_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_10); C8 (Z_to_bv 64 A6_11); C8 (Z_to_bv 64 A6_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_13); C8 (Z_to_bv 64 A6_14)]) ∧ wp_box (rw_cells usegs mb6 A6_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q7_4, A7_4, 128) LBc7 ∧ In (q7_3, A7_3, 104) LBc7 ∧ In (q7_2, A7_2, 40) LBc7 ∧ In (q7_1, A7_1, 16) LBc7)) ->
  ((In (q8_15, A8_15, 40) LBc8 ∧ In (q8_14, A8_14, 40) LBc8 ∧ In (q8_13, A8_13, 40) LBc8 ∧ In (q8_12, A8_12, 32) LBc8 ∧ In (q8_11, A8_11, 40) LBc8 ∧ In (q8_10, A8_10, 40) LBc8 ∧ In (q8_9, A8_9, 32) LBc8 ∧ In (q8_8, A8_8, 40) LBc8 ∧ In (q8_7, A8_7, 40) LBc8 ∧ In (q8_6, A8_6, 32) LBc8 ∧ In (q8_5, A8_5, 40) LBc8 ∧ In (q8_4, A8_4, 40) LBc8 ∧ In (q8_3, A8_3, 32) LBc8 ∧ In (q8_2, A8_2, 384) LBc8 ∧ In (q8_1, A8_1, 24) LBc8 ∧ wp_box (rw_cells usegs mb8 A8_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A8_2); C8 (Z_to_bv 64 A8_15)]) ∧ wp_box (rw_cells usegs mb8 A8_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb8 A8_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb8 A8_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb8 A8_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb8 A8_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb8 A8_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb8 A8_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb8 A8_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb8 A8_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb8 A8_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb8 A8_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb8 A8_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb8 A8_2 [C8 (Z_to_bv 64 A8_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_4); C8 (Z_to_bv 64 A8_5); C8 (Z_to_bv 64 A8_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_7); C8 (Z_to_bv 64 A8_8); C8 (Z_to_bv 64 A8_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_10); C8 (Z_to_bv 64 A8_11); C8 (Z_to_bv 64 A8_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_13); C8 (Z_to_bv 64 A8_14)]) ∧ wp_box (rw_cells usegs mb8 A8_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q9_15, A9_15, 40) LBc9 ∧ In (q9_14, A9_14, 40) LBc9 ∧ In (q9_13, A9_13, 40) LBc9 ∧ In (q9_12, A9_12, 32) LBc9 ∧ In (q9_11, A9_11, 40) LBc9 ∧ In (q9_10, A9_10, 40) LBc9 ∧ In (q9_9, A9_9, 32) LBc9 ∧ In (q9_8, A9_8, 40) LBc9 ∧ In (q9_7, A9_7, 40) LBc9 ∧ In (q9_6, A9_6, 32) LBc9 ∧ In (q9_5, A9_5, 40) LBc9 ∧ In (q9_4, A9_4, 40) LBc9 ∧ In (q9_3, A9_3, 32) LBc9 ∧ In (q9_2, A9_2, 384) LBc9 ∧ In (q9_1, A9_1, 24) LBc9 ∧ wp_box (rw_cells usegs mb9 A9_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A9_2); C8 (Z_to_bv 64 A9_15)]) ∧ wp_box (rw_cells usegs mb9 A9_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb9 A9_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb9 A9_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb9 A9_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb9 A9_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb9 A9_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb9 A9_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb9 A9_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb9 A9_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb9 A9_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb9 A9_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb9 A9_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) ∧ wp_box (rw_cells usegs mb9 A9_2 [C8 (Z_to_bv 64 A9_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_4); C8 (Z_to_bv 64 A9_5); C8 (Z_to_bv 64 A9_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_7); C8 (Z_to_bv 64 A9_8); C8 (Z_to_bv 64 A9_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_10); C8 (Z_to_bv 64 A9_11); C8 (Z_to_bv 64 A9_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_13); C8 (Z_to_bv 64 A9_14)]) ∧ wp_box (rw_cells usegs mb9 A9_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q10_5, A10_5, 40) LBc10 ∧ In (q10_4, A10_4, 56) LBc10 ∧ In (q10_3, A10_3, 40) LBc10 ∧ In (q10_2, A10_2, 56) LBc10 ∧ In (q10_1, A10_1, 80) LBc10 ∧ wp_box (rw_cells usegs mb10 A10_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A10_2); C8 (Z_to_bv 64 A10_4); C8 (Z_to_bv 64 A10_3); C8 (Z_to_bv 64 A10_5); CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 (Z.lor (bv_unsigned (zxb (Z_to_bv 8 0))) 1)); CB 7 (repeat (Z_to_bv 8 0) 7)]) ∧ wp_box (rw_cells usegs mb10 A10_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1004432); C8 (Z_to_bv 64 1004308); C8 (Z_to_bv 64 1004476)]) ∧ wp_box (rw_cells usegs mb10 A10_3 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ∧ wp_box (rw_cells usegs mb10 A10_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 994472); C8 (Z_to_bv 64 1004348); C8 (Z_to_bv 64 1004268); C8 (Z_to_bv 64 1004392)]) ∧ wp_box (rw_cells usegs mb10 A10_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  ((In (q11_8, A11_8, 56) LBc11 ∧ In (q11_7, A11_7, 56) LBc11 ∧ In (q11_6, A11_6, 128) LBc11 ∧ In (q11_5, A11_5, 104) LBc11 ∧ In (q11_4, A11_4, 128) LBc11 ∧ In (q11_3, A11_3, 104) LBc11 ∧ In (q11_2, A11_2, 40) LBc11 ∧ In (q11_1, A11_1, 48) LBc11)) ->
  ((In (q12_9, A12_9, 56) LBc12 ∧ In (q12_8, A12_8, 16) LBc12 ∧ In (q12_7, A12_7, 264) LBc12 ∧ In (q12_6, A12_6, 32768) LBc12 ∧ In (q12_5, A12_5, 24) LBc12 ∧ In (q12_4, A12_4, 40) LBc12 ∧ In (q12_3, A12_3, 96) LBc12 ∧ In (q12_2, A12_2, 40) LBc12 ∧ In (q12_1, A12_1, 40) LBc12)) ->
  ((In (q13_2, A13_2, 128) LBc13 ∧ In (q13_1, A13_1, 104) LBc13)) ->
  ((In (q14_1, A14_1, 16) LBc14 ∧ wp_box (rw_cells usegs mb14 A14_1 [CB 16 (repeat (Z_to_bv 8 0) 16)]))) ->
  ((In (q15_1, A15_1, 56) LBc15 ∧ wp_box (rw_cells usegs mb15 A15_1 [CB 56 (repeat (Z_to_bv 8 0) 56)]))) ->
  ((In (q16_2, A16_2, 40) LBc16 ∧ In (q16_1, A16_1, 16) LBc16 ∧ wp_box (rw_cells usegs mb16 A16_1 [C8 (Z_to_bv 64 A16_2); CB 8 (repeat (Z_to_bv 8 0) 8)]) ∧ wp_box (rw_cells usegs mb16 A16_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st LBc0 Lc0 ma0) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st1 LBc1 Lc1 mb1 st1 LBc1 Lc1 ma1) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st3 LBc3 Lc3 mb3 st3 LBc3 Lc3 ma3) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st4 LBc4 Lc4 mb4 st4 LBc4 Lc4 ma4) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st5 LBc5 Lc5 mb5 st5 LBc5 Lc5 ma5) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st6 LBc6 Lc6 mb6 st6 LBc6 Lc6 ma6) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st7 LBc7 Lc7 mb7 st7 LBc7 Lc7 ma7) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st8 LBc8 Lc8 mb8 st8 LBc8 Lc8 ma8) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st9 LBc9 Lc9 mb9 st9 LBc9 Lc9 ma9) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st10 LBc10 Lc10 mb10 st10 LBc10 Lc10 ma10) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st11 LBc11 Lc11 mb11 st11 LBc11 Lc11 ma11) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st12 LBc12 Lc12 mb12 st12 LBc12 Lc12 ma12) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st13 LBc13 Lc13 mb13 st13 LBc13 Lc13 ma13) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st14 LBc14 Lc14 mb14 st14 LBc14 Lc14 ma14) ->
  (forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st15 LBc15 Lc15 mb15 st15 LBc15 Lc15 ma15) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st LBc0 Lc0 ma0 st1 LBc1 Lc1 mb1) ->
  (cframe (fun _ => False) [(0x32ded0, 0x32ded8)]%Z (bv_unsigned sp + -32) st1 LBc1 Lc1 ma1 st2 LBc2 Lc2 mb2) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st2 LBc2 Lc2 mb2 st3 LBc3 Lc3 mb3) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st3 LBc3 Lc3 ma3 st4 LBc4 Lc4 mb4) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st4 LBc4 Lc4 ma4 st5 LBc5 Lc5 mb5) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st5 LBc5 Lc5 ma5 st6 LBc6 Lc6 mb6) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st6 LBc6 Lc6 ma6 st7 LBc7 Lc7 mb7) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st7 LBc7 Lc7 ma7 st8 LBc8 Lc8 mb8) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st8 LBc8 Lc8 ma8 st9 LBc9 Lc9 mb9) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st9 LBc9 Lc9 ma9 st10 LBc10 Lc10 mb10) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st10 LBc10 Lc10 ma10 st11 LBc11 Lc11 mb11) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st11 LBc11 Lc11 ma11 st12 LBc12 Lc12 mb12) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st12 LBc12 Lc12 ma12 st13 LBc13 Lc13 mb13) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st13 LBc13 Lc13 ma13 st14 LBc14 Lc14 mb14) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st14 LBc14 Lc14 ma14 st15 LBc15 Lc15 mb15) ->
  (cframe (fun _ => False) []%Z (bv_unsigned sp + -32) st15 LBc15 Lc15 ma15 st16 LBc16 Lc16 mb16) ->
  climpl f16 Lc16 st16 (MS (mkR ((Z_to_bv 64 935056)) ((Z_to_bv 64 (bv_unsigned sp + -32))) gp tp u0_16 u1_16 u2_16 sp ((Z_to_bv 64 3333832)) ((Z_to_bv 64 A16_1)) b1_16 b2_16 b3_16 b4_16 b5_16 b6_16 b7_16 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_16 u4_16 u5_16 u6_16) F (Z_to_bv 64 0xe4490) fc None mb16 (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z 126 (119) (6) (83768) (context_init_res LBall L)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros HB_crypto_zalloc_stmt HB_ossl_property_parse_init_fp_stmt ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x_2e83e8 F fc m st LBall LB L f lo B q1_1 A1_1 st1 mb1 q2_1 A2_1 st2 mb2 q3_1 A3_1 q3_2 A3_2 q3_3 A3_3 q3_4 A3_4 q3_5 A3_5 q3_6 A3_6 q3_7 A3_7 q3_8 A3_8 q3_9 A3_9 q3_10 A3_10 q3_11 A3_11 q3_12 A3_12 q3_13 A3_13 q3_14 A3_14 q3_15 A3_15 st3 mb3 q4_1 A4_1 q4_2 A4_2 st4 mb4 q5_1 A5_1 q5_2 A5_2 q5_3 A5_3 st5 mb5 q6_1 A6_1 q6_2 A6_2 q6_3 A6_3 q6_4 A6_4 q6_5 A6_5 q6_6 A6_6 q6_7 A6_7 q6_8 A6_8 q6_9 A6_9 q6_10 A6_10 q6_11 A6_11 q6_12 A6_12 q6_13 A6_13 q6_14 A6_14 q6_15 A6_15 st6 mb6 q7_1 A7_1 q7_2 A7_2 q7_3 A7_3 q7_4 A7_4 st7 mb7 q8_1 A8_1 q8_2 A8_2 q8_3 A8_3 q8_4 A8_4 q8_5 A8_5 q8_6 A8_6 q8_7 A8_7 q8_8 A8_8 q8_9 A8_9 q8_10 A8_10 q8_11 A8_11 q8_12 A8_12 q8_13 A8_13 q8_14 A8_14 q8_15 A8_15 st8 mb8 q9_1 A9_1 q9_2 A9_2 q9_3 A9_3 q9_4 A9_4 q9_5 A9_5 q9_6 A9_6 q9_7 A9_7 q9_8 A9_8 q9_9 A9_9 q9_10 A9_10 q9_11 A9_11 q9_12 A9_12 q9_13 A9_13 q9_14 A9_14 q9_15 A9_15 st9 mb9 q10_1 A10_1 q10_2 A10_2 q10_3 A10_3 q10_4 A10_4 q10_5 A10_5 st10 mb10 q11_1 A11_1 q11_2 A11_2 q11_3 A11_3 q11_4 A11_4 q11_5 A11_5 q11_6 A11_6 q11_7 A11_7 q11_8 A11_8 st11 mb11 q12_1 A12_1 q12_2 A12_2 q12_3 A12_3 q12_4 A12_4 q12_5 A12_5 q12_6 A12_6 q12_7 A12_7 q12_8 A12_8 q12_9 A12_9 st12 mb12 q13_1 A13_1 q13_2 A13_2 st13 mb13 q14_1 A14_1 st14 mb14 q15_1 A15_1 st15 mb15 q16_1 A16_1 q16_2 A16_2 u0_16 u1_16 u2_16 b1_16 b2_16 b3_16 b4_16 b5_16 b6_16 b7_16 u3_16 u4_16 u5_16 u6_16 f16 st16 mb16 ma0 ma1 ma3 ma4 ma5 ma6 ma7 ma8 ma9 ma10 ma11 ma12 ma13 ma14 ma15 junk
         LBc0 Lc0 LBc1 Lc1 LBc2 Lc2 LBc3 Lc3 LBc4 Lc4 LBc5 Lc5 LBc6 Lc6 LBc7 Lc7 LBc8 Lc8 LBc9 Lc9 LBc10 Lc10 LBc11 Lc11 LBc12 Lc12 LBc13 Lc13 LBc14 Lc14 LBc15 Lc15 LBc16 Lc16
         HB Hf ROOM OWN SLO SP16 CST16 SK_3048424 SK_3048416 SK_3048256 SK_3048248 FRs16 XR11_0 FUc16 GRc16 PK1 PK2 PK3 PK4 PK5 PK6 PK7 PK8 PK9 PK10 PK11 PK12 PK13 PK14 PK15 PK16 SF0 SF1 SF3 SF4 SF5 SF6 SF7 SF8 SF9 SF10 SF11 SF12 SF13 SF14 SF15 FRM1 FRM2 FRM3 FRM4 FRM5 FRM6 FRM7 FRM8 FRM9 FRM10 FRM11 FRM12 FRM13 FRM14 FRM15 FRM16.
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc16 s_ ms_ Q_) end.
  pose proof CST16 as (HP16 & _ & (errv16 & _ & HB_ & ST16 & LO & _ & MI16 & _) & _ & _ & _ & GLO). clear HB_.
  unfold context_init_STACK, PPI_STACK, SNM_STACK, NMN_STACK, PSD_STACK, HTN_STACK, ossl_method_store_new_STACK, ossl_rand_ctx_new_STACK, ossl_provider_store_new_STACK, ossl_do_ex_data_init_STACK, ossl_prov_conf_ctx_new_STACK, DCN_STACK, RCU_STACK, ossl_prov_drbg_nonce_ctx_new_STACK, ossl_load_builtin_compressions_STACK, PDN_STACK, ossl_threads_ctx_new_STACK, LOCK_NEW_STACK, LHN_STACK, ossl_crypto_mutex_new_STACK, CRE_STACK, OPENSSL_sk_new_STACK, ossl_ctx_global_properties_new_STACK, ossl_bio_core_globals_new_STACK, ossl_self_test_set_callback_new_STACK, ossl_indicator_set_callback_new_STACK, ossl_child_prov_ctx_new_STACK, CZ_STACK, RREALLOC_STACK, CM_STACK, RMALLOC_STACK, FZ_G_context_init, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  rewrite ?unsigned_lit in ST16 by wp_lia.
  destruct PK16 as (IN_A16_2 & IN_A16_1 & BC16_0 & BC16_1).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ q16_1 A16_1 16 CST16 ltac:(do 1 right; left; reflexivity)) as RNG_A16_1. pose proof RNG_A16_1 as (P0_A16_1 & _ & _ & PC_A16_1 & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ q16_2 A16_2 40 CST16 ltac:(left; reflexivity)) as RNG_A16_2. pose proof RNG_A16_2 as (P0_A16_2 & _ & _ & PC_A16_2 & _).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfa8, 0x32dfb0)]%Z mb16) as MU16. pose proof (wmono_refl usegs mb16) as WM16.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma16 end.
  assert (CSTa16 : cstate st16 LBc16 LB Lc16 ma16 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb16 ma16 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST16| exact MU16| exact WM16| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF16 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st16 LBc16 Lc16 mb16 st16 LBc16 Lc16 ma16).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU16| exact WM16| exact HP16| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF16 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST16 HP16 ST16 MI16 MU16 WM16. try clear errv16.
  clear P0_A16_1 P0_A16_2 PC_A16_1 PC_A16_2 RNG_A16_1 RNG_A16_2.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_self_test_set_callback_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc16)| wp_wnorm; wp_lia..]| exact CSTa16| rewrite unsigned_lit by wp_lia; unfold ossl_self_test_set_callback_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f17 L17 st17 ms17 (v17 & mb17 & LB17 & RET17 & FU17 & GR17 & CST17 & FRM17 & (q17_1 & A17_1 & -> & -> & -> & RNG_A17_1 & BC17_0)).
  destruct RET17 as (u0_17 & u1_17 & u2_17 & b1_17 & b2_17 & b3_17 & b4_17 & b5_17 & b6_17 & b7_17 & u3_17 & u4_17 & u5_17 & u6_17 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM17 by wp_lia.
  pose proof FRM17 as (CFR17 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM17 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma16 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR17 FRh ltac:(wp_lia)) as FRs17; clear FRh end.
  match goal with Hs : rw_cells _ ma16 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR17 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma16 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR17 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma16 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR17 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma16 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR17 Hs Hn; clear Hs end.
  pose proof CST17 as (HP17 & _ & (errv17 & _ & _ & ST17 & _ & _ & MI17 & _) & _).
  rewrite unsigned_lit in ST17 by wp_lia.
  pose proof RNG_A17_1 as (P0_A17_1 & _ & _ & PC_A17_1 & _).
  assert (FUc17 : (f <= f17 + 100)%nat) by (clear - FU17 FUc16; lia).
  change (Z.to_nat 16) with 16%nat in BC17_0.
  pose (LBc17 := (q17_1, A17_1, 16) :: LBc16). pose (Lc17 := (q17_1, 16) :: Lc16).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc17 s_ ms_ Q_) end.
  assert (GRc17 : cgrow L Lc17 94 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc16 GR17)| wp_wnorm; wp_lia..]).
  assert (IN_A17_1 : In (q17_1, A17_1, 16) LBc17) by (left; reflexivity).
  wp_box1 BC17_0.
  pose proof (conj IN_A17_1 BC17_0) as PK17. clear CSTa16 CFR17 FU17 GR17 FUc16 GRc16 f16 IN_A17_1 BC17_0.
  try (clear u0_16 u1_16 u2_16 b1_16 b2_16 b3_16 b4_16 b5_16 b6_16 b7_16 u3_16 u4_16 u5_16 u6_16).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfe8, 0x32dff0)]%Z mb17) as MU17. pose proof (wmono_refl usegs mb17) as WM17.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma17 end.
  assert (CSTa17 : cstate st17 LBc17 LB Lc17 ma17 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb17 ma17 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST17| exact MU17| exact WM17| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF17 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st17 LBc17 Lc17 mb17 st17 LBc17 Lc17 ma17).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU17| exact WM17| exact HP17| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF17 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST17 HP17 ST17 MI17 MU17 WM17. try clear errv17.
  clear P0_A17_1 PC_A17_1 RNG_A17_1.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_indicator_set_callback_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc17)| wp_wnorm; wp_lia..]| exact CSTa17| rewrite unsigned_lit by wp_lia; unfold ossl_indicator_set_callback_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f18 L18 st18 ms18 (v18 & mb18 & LB18 & RET18 & FU18 & GR18 & CST18 & FRM18 & (q18_1 & A18_1 & -> & -> & -> & RNG_A18_1 & BC18_0)).
  destruct RET18 as (u0_18 & u1_18 & u2_18 & b1_18 & b2_18 & b3_18 & b4_18 & b5_18 & b6_18 & b7_18 & u3_18 & u4_18 & u5_18 & u6_18 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM18 by wp_lia.
  pose proof FRM18 as (CFR18 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM18 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma17 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR18 FRh ltac:(wp_lia)) as FRs18; clear FRh end.
  match goal with Hs : rw_cells _ ma17 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR18 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma17 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR18 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma17 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR18 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma17 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR18 Hs Hn; clear Hs end.
  pose proof CST18 as (HP18 & _ & (errv18 & _ & _ & ST18 & _ & _ & MI18 & _) & _).
  rewrite unsigned_lit in ST18 by wp_lia.
  pose proof RNG_A18_1 as (P0_A18_1 & _ & _ & PC_A18_1 & _).
  assert (FUc18 : (f <= f18 + 101)%nat) by (clear - FU18 FUc17; lia).
  change (Z.to_nat 8) with 8%nat in BC18_0.
  pose (LBc18 := (q18_1, A18_1, 8) :: LBc17). pose (Lc18 := (q18_1, 8) :: Lc17).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc18 s_ ms_ Q_) end.
  assert (GRc18 : cgrow L Lc18 95 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc17 GR18)| wp_wnorm; wp_lia..]).
  assert (IN_A18_1 : In (q18_1, A18_1, 8) LBc18) by (left; reflexivity).
  wp_box1 BC18_0.
  pose proof (conj IN_A18_1 BC18_0) as PK18. clear CSTa17 CFR18 FU18 GR18 FUc17 GRc17 f17 IN_A18_1 BC18_0.
  try (clear u0_17 u1_17 u2_17 b1_17 b2_17 b3_17 b4_17 b5_17 b6_17 b7_17 u3_17 u4_17 u5_17 u6_17).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dff0, 0x32dff8)]%Z mb18) as MU18. pose proof (wmono_refl usegs mb18) as WM18.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma18 end.
  assert (CSTa18 : cstate st18 LBc18 LB Lc18 ma18 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb18 ma18 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST18| exact MU18| exact WM18| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF18 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st18 LBc18 Lc18 mb18 st18 LBc18 Lc18 ma18).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU18| exact WM18| exact HP18| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF18 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST18 HP18 ST18 MI18 MU18 WM18. try clear errv18.
  clear P0_A18_1 PC_A18_1 RNG_A18_1.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_threads_ctx_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc18)| wp_wnorm; wp_lia..]| exact CSTa18| rewrite unsigned_lit by wp_lia; unfold ossl_threads_ctx_new_STACK, ossl_crypto_mutex_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f19 L19 st19 ms19 (v19 & mb19 & LB19 & RET19 & FU19 & GR19 & CST19 & FRM19 & (q19_1 & A19_1 & q19_2 & A19_2 & q19_3 & A19_3 & -> & -> & -> & RNG_A19_1 & RNG_A19_2 & RNG_A19_3 & BC19_0 & BC19_1 & BC19_2)).
  destruct RET19 as (u0_19 & u1_19 & u2_19 & b1_19 & b2_19 & b3_19 & b4_19 & b5_19 & b6_19 & b7_19 & u3_19 & u4_19 & u5_19 & u6_19 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM19 by wp_lia.
  pose proof FRM19 as (CFR19 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM19 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma18 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR19 FRh ltac:(wp_lia)) as FRs19; clear FRh end.
  match goal with Hs : rw_cells _ ma18 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR19 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma18 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR19 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma18 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR19 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma18 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR19 Hs Hn; clear Hs end.
  pose proof CST19 as (HP19 & _ & (errv19 & _ & _ & ST19 & _ & _ & MI19 & _) & _).
  rewrite unsigned_lit in ST19 by wp_lia.
  pose proof RNG_A19_1 as (P0_A19_1 & _ & _ & PC_A19_1 & _).
  pose proof RNG_A19_2 as (P0_A19_2 & _ & _ & PC_A19_2 & _).
  pose proof RNG_A19_3 as (P0_A19_3 & _ & _ & PC_A19_3 & _).
  assert (FUc19 : (f <= f19 + 104)%nat) by (clear - FU19 FUc18; lia).
  change (Z.to_nat 32) with 32%nat in BC19_0, BC19_1, BC19_2.
  change (Z.to_nat 40) with 40%nat in BC19_0, BC19_1, BC19_2.
  change (Z.to_nat 48) with 48%nat in BC19_0, BC19_1, BC19_2.
  pose (LBc19 := (q19_3, A19_3, 48) :: (q19_2, A19_2, 40) :: (q19_1, A19_1, 32) :: LBc18). pose (Lc19 := (q19_3, 48) :: (q19_2, 40) :: (q19_1, 32) :: Lc18).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc19 s_ ms_ Q_) end.
  assert (GRc19 : cgrow L Lc19 98 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc18 GR19)| wp_wnorm; wp_lia..]).
  assert (IN_A19_3 : In (q19_3, A19_3, 48) LBc19) by (left; reflexivity).
  assert (IN_A19_2 : In (q19_2, A19_2, 40) LBc19) by (do 1 right; left; reflexivity).
  assert (IN_A19_1 : In (q19_1, A19_1, 32) LBc19) by (do 2 right; left; reflexivity).
  wp_box1 BC19_0.
  wp_box1 BC19_1.
  wp_box1 BC19_2.
  pose proof (conj IN_A19_3 (conj IN_A19_2 (conj IN_A19_1 (conj BC19_0 (conj BC19_1 BC19_2))))) as PK19. clear CSTa18 CFR19 FU19 GR19 FUc18 GRc18 f18 IN_A19_3 IN_A19_2 IN_A19_1 BC19_0 BC19_1 BC19_2.
  try (clear u0_18 u1_18 u2_18 b1_18 b2_18 b3_18 b4_18 b5_18 b6_18 b7_18 u3_18 u4_18 u5_18 u6_18).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dff8, 0x32e000)]%Z mb19) as MU19. pose proof (wmono_refl usegs mb19) as WM19.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma19 end.
  assert (CSTa19 : cstate st19 LBc19 LB Lc19 ma19 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb19 ma19 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST19| exact MU19| exact WM19| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF19 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st19 LBc19 Lc19 mb19 st19 LBc19 Lc19 ma19).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU19| exact WM19| exact HP19| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF19 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST19 HP19 ST19 MI19 MU19 WM19. try clear errv19.
  clear P0_A19_1 PC_A19_1 RNG_A19_1 P0_A19_2 PC_A19_2 RNG_A19_2 P0_A19_3 PC_A19_3 RNG_A19_3.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_child_prov_ctx_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc19)| wp_wnorm; wp_lia..]| exact CSTa19| rewrite unsigned_lit by wp_lia; unfold ossl_child_prov_ctx_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f20 L20 st20 ms20 (v20 & mb20 & LB20 & RET20 & FU20 & GR20 & CST20 & FRM20 & (q20_1 & A20_1 & -> & -> & -> & RNG_A20_1 & BC20_0)).
  destruct RET20 as (u0_20 & u1_20 & u2_20 & b1_20 & b2_20 & b3_20 & b4_20 & b5_20 & b6_20 & b7_20 & u3_20 & u4_20 & u5_20 & u6_20 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM20 by wp_lia.
  pose proof FRM20 as (CFR20 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM20 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma19 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR20 FRh ltac:(wp_lia)) as FRs20; clear FRh end.
  match goal with Hs : rw_cells _ ma19 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR20 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma19 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR20 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma19 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR20 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma19 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR20 Hs Hn; clear Hs end.
  pose proof CST20 as (HP20 & _ & (errv20 & _ & _ & ST20 & _ & _ & MI20 & _) & _).
  rewrite unsigned_lit in ST20 by wp_lia.
  pose proof RNG_A20_1 as (P0_A20_1 & _ & _ & PC_A20_1 & _).
  assert (FUc20 : (f <= f20 + 105)%nat) by (clear - FU20 FUc19; lia).
  change (Z.to_nat 88) with 88%nat in BC20_0.
  pose (LBc20 := (q20_1, A20_1, 88) :: LBc19). pose (Lc20 := (q20_1, 88) :: Lc19).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc20 s_ ms_ Q_) end.
  assert (GRc20 : cgrow L Lc20 99 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc19 GR20)| wp_wnorm; wp_lia..]).
  assert (IN_A20_1 : In (q20_1, A20_1, 88) LBc20) by (left; reflexivity).
  wp_box1 BC20_0.
  pose proof (conj IN_A20_1 BC20_0) as PK20. clear CSTa19 CFR20 FU20 GR20 FUc19 GRc19 f19 IN_A20_1 BC20_0.
  try (clear u0_19 u1_19 u2_19 b1_19 b2_19 b3_19 b4_19 b5_19 b6_19 b7_19 u3_19 u4_19 u5_19 u6_19).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfc0, 0x32dfc8)]%Z mb20) as MU20. pose proof (wmono_refl usegs mb20) as WM20.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma20 end.
  assert (CSTa20 : cstate st20 LBc20 LB Lc20 ma20 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb20 ma20 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST20| exact MU20| exact WM20| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF20 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st20 LBc20 Lc20 mb20 st20 LBc20 Lc20 ma20).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU20| exact WM20| exact HP20| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF20 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST20 HP20 ST20 MI20 MU20 WM20. try clear errv20.
  clear P0_A20_1 PC_A20_1 RNG_A20_1.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { pose proof HB_ossl_property_parse_init_fp_stmt as CALLEE. unfold ossl_property_parse_init_fp_stmt, PPI_EV, CTX_A, CTX_PSD, PPI_NA in CALLEE. try unfold ossl_property_parse_init_fp_stmt, PPI_EV, CTX_A, CTX_PSD, PPI_NA in CALLEE. change ((3333832) + 168)%Z with 3334000%Z in CALLEE. eapply CALLEE with (KP := (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc20)| wp_wnorm; wp_lia..]| exact CSTa20| rewrite unsigned_lit by wp_lia; unfold PPI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; wp_lia| rewrite unsigned_lit by wp_lia; clear - SP16; lia| reflexivity| wp_cells| exact XR11_0]. }
  intros f21 L21 st21 ms21 (v21 & mb21 & LB21 & RET21 & FU21 & GR21 & CST21 & FRM21 & (q21_1 & q21_2 & q21_3 & q21_4 & q21_5 & q21_6 & q21_7 & q21_8 & q21_9 & q21_10 & q21_11 & q21_12 & q21_13 & q21_14 & q21_15 & q21_16 & q21_17 & q21_18 & A21_1 & A21_2 & A21_3 & A21_4 & A21_5 & A21_6 & A21_7 & A21_8 & A21_9 & A21_10 & A21_11 & A21_12 & A21_13 & A21_14 & A21_15 & A21_16 & A21_17 & A21_18 & -> & -> & RNG_A21_1 & RNG_A21_2 & RNG_A21_3 & RNG_A21_4 & RNG_A21_5 & RNG_A21_6 & RNG_A21_7 & RNG_A21_8 & RNG_A21_9 & RNG_A21_10 & RNG_A21_11 & RNG_A21_12 & RNG_A21_13 & RNG_A21_14 & RNG_A21_15 & RNG_A21_16 & RNG_A21_17 & RNG_A21_18)).
  destruct RET21 as (u0_21 & u1_21 & u2_21 & b1_21 & b2_21 & b3_21 & b4_21 & b5_21 & b6_21 & b7_21 & u3_21 & u4_21 & u5_21 & u6_21 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM21 by wp_lia.
  pose proof FRM21 as (CFR21 & _).
  lazymatch goal with FRh : rw_cells _ ma20 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR21 FRh ltac:(wp_lia)) as FRs21; clear FRh end.
  match goal with Hs : rw_cells _ ma20 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR21 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma20 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR21 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma20 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR21 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma20 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR21 Hs Hn; clear Hs end.
  pose proof CST21 as (HP21 & _ & (errv21 & _ & _ & ST21 & _ & _ & MI21 & _) & _).
  rewrite unsigned_lit in ST21 by wp_lia.
  pose proof RNG_A21_1 as (P0_A21_1 & _ & _ & PC_A21_1 & _).
  pose proof RNG_A21_2 as (P0_A21_2 & _ & _ & PC_A21_2 & _).
  pose proof RNG_A21_3 as (P0_A21_3 & _ & _ & PC_A21_3 & _).
  pose proof RNG_A21_4 as (P0_A21_4 & _ & _ & PC_A21_4 & _).
  pose proof RNG_A21_5 as (P0_A21_5 & _ & _ & PC_A21_5 & _).
  pose proof RNG_A21_6 as (P0_A21_6 & _ & _ & PC_A21_6 & _).
  pose proof RNG_A21_7 as (P0_A21_7 & _ & _ & PC_A21_7 & _).
  pose proof RNG_A21_8 as (P0_A21_8 & _ & _ & PC_A21_8 & _).
  pose proof RNG_A21_9 as (P0_A21_9 & _ & _ & PC_A21_9 & _).
  pose proof RNG_A21_10 as (P0_A21_10 & _ & _ & PC_A21_10 & _).
  pose proof RNG_A21_11 as (P0_A21_11 & _ & _ & PC_A21_11 & _).
  pose proof RNG_A21_12 as (P0_A21_12 & _ & _ & PC_A21_12 & _).
  pose proof RNG_A21_13 as (P0_A21_13 & _ & _ & PC_A21_13 & _).
  pose proof RNG_A21_14 as (P0_A21_14 & _ & _ & PC_A21_14 & _).
  pose proof RNG_A21_15 as (P0_A21_15 & _ & _ & PC_A21_15 & _).
  pose proof RNG_A21_16 as (P0_A21_16 & _ & _ & PC_A21_16 & _).
  pose proof RNG_A21_17 as (P0_A21_17 & _ & _ & PC_A21_17 & _).
  pose proof RNG_A21_18 as (P0_A21_18 & _ & _ & PC_A21_18 & _).
  assert (FUc21 : (f <= f21 + 125)%nat) by (clear - FU21 FUc20; lia).
  change (Z.to_nat 18) with 18%nat in |-.
  change (Z.to_nat 19) with 19%nat in |-.
  change (Z.to_nat 20) with 20%nat in |-.
  change (Z.to_nat 21) with 21%nat in |-.
  change (Z.to_nat 22) with 22%nat in |-.
  change (Z.to_nat 23) with 23%nat in |-.
  change (Z.to_nat 24) with 24%nat in |-.
  change (Z.to_nat 25) with 25%nat in |-.
  change (Z.to_nat 32) with 32%nat in |-.
  change (Z.to_nat 48) with 48%nat in |-.
  pose (LBc21 := (q21_18, A21_18, 24) :: (q21_17, A21_17, 18) :: (q21_16, A21_16, 24) :: (q21_15, A21_15, 32) :: (q21_14, A21_14, 19) :: (q21_13, A21_13, 24) :: (q21_12, A21_12, 25) :: (q21_11, A21_11, 24) :: (q21_10, A21_10, 48) :: (q21_9, A21_9, 21) :: (q21_8, A21_8, 24) :: (q21_7, A21_7, 22) :: (q21_6, A21_6, 24) :: (q21_5, A21_5, 20) :: (q21_4, A21_4, 24) :: (q21_3, A21_3, 23) :: (q21_2, A21_2, 24) :: (q21_1, A21_1, 24) :: LBc20). pose (Lc21 := L21).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc21 s_ ms_ Q_) end.
  assert (GRc21 : cgrow L Lc21 118 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc20 GR21)| wp_wnorm; wp_lia..]).
  assert (IN_A21_18 : In (q21_18, A21_18, 24) LBc21) by (left; reflexivity).
  assert (IN_A21_17 : In (q21_17, A21_17, 18) LBc21) by (do 1 right; left; reflexivity).
  assert (IN_A21_16 : In (q21_16, A21_16, 24) LBc21) by (do 2 right; left; reflexivity).
  assert (IN_A21_15 : In (q21_15, A21_15, 32) LBc21) by (do 3 right; left; reflexivity).
  assert (IN_A21_14 : In (q21_14, A21_14, 19) LBc21) by (do 4 right; left; reflexivity).
  assert (IN_A21_13 : In (q21_13, A21_13, 24) LBc21) by (do 5 right; left; reflexivity).
  assert (IN_A21_12 : In (q21_12, A21_12, 25) LBc21) by (do 6 right; left; reflexivity).
  assert (IN_A21_11 : In (q21_11, A21_11, 24) LBc21) by (do 7 right; left; reflexivity).
  assert (IN_A21_10 : In (q21_10, A21_10, 48) LBc21) by (do 8 right; left; reflexivity).
  assert (IN_A21_9 : In (q21_9, A21_9, 21) LBc21) by (do 9 right; left; reflexivity).
  assert (IN_A21_8 : In (q21_8, A21_8, 24) LBc21) by (do 10 right; left; reflexivity).
  assert (IN_A21_7 : In (q21_7, A21_7, 22) LBc21) by (do 11 right; left; reflexivity).
  assert (IN_A21_6 : In (q21_6, A21_6, 24) LBc21) by (do 12 right; left; reflexivity).
  assert (IN_A21_5 : In (q21_5, A21_5, 20) LBc21) by (do 13 right; left; reflexivity).
  assert (IN_A21_4 : In (q21_4, A21_4, 24) LBc21) by (do 14 right; left; reflexivity).
  assert (IN_A21_3 : In (q21_3, A21_3, 23) LBc21) by (do 15 right; left; reflexivity).
  assert (IN_A21_2 : In (q21_2, A21_2, 24) LBc21) by (do 16 right; left; reflexivity).
  assert (IN_A21_1 : In (q21_1, A21_1, 24) LBc21) by (do 17 right; left; reflexivity).
  pose proof (conj IN_A21_18 (conj IN_A21_17 (conj IN_A21_16 (conj IN_A21_15 (conj IN_A21_14 (conj IN_A21_13 (conj IN_A21_12 (conj IN_A21_11 (conj IN_A21_10 (conj IN_A21_9 (conj IN_A21_8 (conj IN_A21_7 (conj IN_A21_6 (conj IN_A21_5 (conj IN_A21_4 (conj IN_A21_3 (conj IN_A21_2 IN_A21_1))))))))))))))))) as PK21. clear CSTa20 CFR21 FU21 GR21 FUc20 GRc20 f20 IN_A21_18 IN_A21_17 IN_A21_16 IN_A21_15 IN_A21_14 IN_A21_13 IN_A21_12 IN_A21_11 IN_A21_10 IN_A21_9 IN_A21_8 IN_A21_7 IN_A21_6 IN_A21_5 IN_A21_4 IN_A21_3 IN_A21_2 IN_A21_1.
  try (clear u0_20 u1_20 u2_20 b1_20 b2_20 b3_20 b4_20 b5_20 b6_20 b7_20 u3_20 u4_20 u5_20 u6_20).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z mb21) as MU21. pose proof (wmono_refl usegs mb21) as WM21.
  cprefix. step. wp_brF. step.
  chere.
  assert (CSTa21 : cstate st21 LBc21 LB Lc21 mb21 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb21 mb21 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST21| exact MU21| exact WM21| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  clear CST21 HP21 ST21 MI21 MU21 WM21. try clear errv21.
  clear P0_A21_1 PC_A21_1 RNG_A21_1 P0_A21_2 PC_A21_2 RNG_A21_2 P0_A21_3 PC_A21_3 RNG_A21_3 P0_A21_4 PC_A21_4 RNG_A21_4 P0_A21_5 PC_A21_5 RNG_A21_5 P0_A21_6 PC_A21_6 RNG_A21_6 P0_A21_7 PC_A21_7 RNG_A21_7 P0_A21_8 PC_A21_8 RNG_A21_8 P0_A21_9 PC_A21_9 RNG_A21_9 P0_A21_10 PC_A21_10 RNG_A21_10 P0_A21_11 PC_A21_11 RNG_A21_11 P0_A21_12 PC_A21_12 RNG_A21_12 P0_A21_13 PC_A21_13 RNG_A21_13 P0_A21_14 PC_A21_14 RNG_A21_14 P0_A21_15 PC_A21_15 RNG_A21_15 P0_A21_16 PC_A21_16 RNG_A21_16 P0_A21_17 PC_A21_17 RNG_A21_17 P0_A21_18 PC_A21_18 RNG_A21_18.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_load_builtin_compressions_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc21)| wp_wnorm; wp_lia..]| exact CSTa21| rewrite unsigned_lit by wp_lia; unfold ossl_load_builtin_compressions_STACK, OPENSSL_sk_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f22 L22 st22 ms22 (v22 & mb22 & LB22 & RET22 & FU22 & GR22 & CST22 & FRM22 & (q22_1 & A22_1 & -> & -> & -> & RNG_A22_1 & BC22_0)).
  destruct RET22 as (u0_22 & u1_22 & u2_22 & b1_22 & b2_22 & b3_22 & b4_22 & b5_22 & b6_22 & b7_22 & u3_22 & u4_22 & u5_22 & u6_22 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM22 by wp_lia.
  pose proof FRM22 as (CFR22 & _).
  lazymatch goal with FRh : rw_cells _ mb21 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR22 FRh ltac:(wp_lia)) as FRs22; clear FRh end.
  match goal with Hs : rw_cells _ mb21 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR22 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb21 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR22 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb21 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR22 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb21 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR22 Hs Hn; clear Hs end.
  pose proof CST22 as (HP22 & _ & (errv22 & _ & _ & ST22 & _ & _ & MI22 & _) & _).
  rewrite unsigned_lit in ST22 by wp_lia.
  pose proof RNG_A22_1 as (P0_A22_1 & _ & _ & PC_A22_1 & _).
  assert (FUc22 : (f <= f22 + 126)%nat) by (clear - FU22 FUc21; lia).
  change (Z.to_nat 56) with 56%nat in BC22_0.
  pose (LBc22 := (q22_1, A22_1, 56) :: LBc21). pose (Lc22 := (q22_1, 56) :: Lc21).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc22 s_ ms_ Q_) end.
  assert (GRc22 : cgrow L Lc22 119 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc21 GR22)| wp_wnorm; wp_lia..]).
  assert (IN_A22_1 : In (q22_1, A22_1, 56) LBc22) by (left; reflexivity).
  wp_box1 BC22_0.
  pose proof (conj IN_A22_1 BC22_0) as PK22. clear CSTa21 CFR22 FU22 GR22 FUc21 GRc21 f21 IN_A22_1 BC22_0.
  try (clear u0_21 u1_21 u2_21 b1_21 b2_21 b3_21 b4_21 b5_21 b6_21 b7_21 u3_21 u4_21 u5_21 u6_21).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32e000, 0x32e008)]%Z mb22) as MU22. pose proof (wmono_refl usegs mb22) as WM22.
  cprefix. ths. do 7 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _, STh : stk _ _ _ _ |- _ => release_frame FRh STh (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mz end.
  assert (CSTz : cstate st22 LBc22 LB Lc22 mz sp tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb22 mz _ sp tp lo B (bv_unsigned sp)); [exact CST22| exact MU22| exact WM22| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - exact HB. }
  assert (SF22 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st22 LBc22 Lc22 mb22 st22 LBc22 Lc22 mz).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU22| exact WM22| exact HP22| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST22 HP22 ST22 MI22 MU22 WM22. try clear errv22.
  (* [comment removed for export] *)
  assert (CSTx : cstate st22 ([(q22_1, A22_1, 56); (q21_18, A21_18, 24); (q21_17, A21_17, 18); (q21_16, A21_16, 24); (q21_15, A21_15, 32); (q21_14, A21_14, 19); (q21_13, A21_13, 24); (q21_12, A21_12, 25); (q21_11, A21_11, 24); (q21_10, A21_10, 48); (q21_9, A21_9, 21); (q21_8, A21_8, 24); (q21_7, A21_7, 22); (q21_6, A21_6, 24); (q21_5, A21_5, 20); (q21_4, A21_4, 24); (q21_3, A21_3, 23); (q21_2, A21_2, 24); (q21_1, A21_1, 24); (q20_1, A20_1, 88); (q19_3, A19_3, 48); (q19_2, A19_2, 40); (q19_1, A19_1, 32); (q18_1, A18_1, 8); (q17_1, A17_1, 16); (q16_2, A16_2, 40); (q16_1, A16_1, 16); (q15_1, A15_1, 56); (q14_1, A14_1, 16); (q13_2, A13_2, 128); (q13_1, A13_1, 104); (q12_9, A12_9, 56); (q12_8, A12_8, 16); (q12_7, A12_7, 264); (q12_6, A12_6, 32768); (q12_5, A12_5, 24); (q12_4, A12_4, 40); (q12_3, A12_3, 96); (q12_2, A12_2, 40); (q12_1, A12_1, 40); (q11_8, A11_8, 56); (q11_7, A11_7, 56); (q11_6, A11_6, 128); (q11_5, A11_5, 104); (q11_4, A11_4, 128); (q11_3, A11_3, 104); (q11_2, A11_2, 40); (q11_1, A11_1, 48); (q10_5, A10_5, 40); (q10_4, A10_4, 56); (q10_3, A10_3, 40); (q10_2, A10_2, 56); (q10_1, A10_1, 80); (q9_15, A9_15, 40); (q9_14, A9_14, 40); (q9_13, A9_13, 40); (q9_12, A9_12, 32); (q9_11, A9_11, 40); (q9_10, A9_10, 40); (q9_9, A9_9, 32); (q9_8, A9_8, 40); (q9_7, A9_7, 40); (q9_6, A9_6, 32); (q9_5, A9_5, 40); (q9_4, A9_4, 40); (q9_3, A9_3, 32); (q9_2, A9_2, 384); (q9_1, A9_1, 24); (q8_15, A8_15, 40); (q8_14, A8_14, 40); (q8_13, A8_13, 40); (q8_12, A8_12, 32); (q8_11, A8_11, 40); (q8_10, A8_10, 40); (q8_9, A8_9, 32); (q8_8, A8_8, 40); (q8_7, A8_7, 40); (q8_6, A8_6, 32); (q8_5, A8_5, 40); (q8_4, A8_4, 40); (q8_3, A8_3, 32); (q8_2, A8_2, 384); (q8_1, A8_1, 24); (q7_4, A7_4, 128); (q7_3, A7_3, 104); (q7_2, A7_2, 40); (q7_1, A7_1, 16); (q6_15, A6_15, 40); (q6_14, A6_14, 40); (q6_13, A6_13, 40); (q6_12, A6_12, 32); (q6_11, A6_11, 40); (q6_10, A6_10, 40); (q6_9, A6_9, 32); (q6_8, A6_8, 40); (q6_7, A6_7, 40); (q6_6, A6_6, 32); (q6_5, A6_5, 40); (q6_4, A6_4, 40); (q6_3, A6_3, 32); (q6_2, A6_2, 384); (q6_1, A6_1, 24); (q5_3, A5_3, 40); (q5_2, A5_2, 5); (q5_1, A5_1, 88); (q4_2, A4_2, 40); (q4_1, A4_1, 16); (q3_15, A3_15, 40); (q3_14, A3_14, 40); (q3_13, A3_13, 40); (q3_12, A3_12, 32); (q3_11, A3_11, 40); (q3_10, A3_10, 40); (q3_9, A3_9, 32); (q3_8, A3_8, 40); (q3_7, A3_7, 40); (q3_6, A3_6, 32); (q3_5, A3_5, 40); (q3_4, A3_4, 40); (q3_3, A3_3, 32); (q3_2, A3_2, 384); (q3_1, A3_1, 24); (q2_1, A2_1, 40); (q1_1, A1_1, 40)] ++ LBall) LB Lc22 mz sp tp lo B) by exact CSTz.
  assert (FRESH : forall q_, In q_ (map blk_id LBall) \/ In q_ (map fst L) -> ~ (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) q_).
  { intros q_ Hq_ Hin_. cbv beta delta [ppk_T ppk_ids k_ps k_pk k_pl1 k_pb1 k_pl2 k_pb2 k_pq1 k_pq2 a_S a_LK a_lh1 a_B1 a_lh2 a_B2 a_Q1 a_Q2] in Hin_. cbn in Hin_. destruct Hin_ as [E_|[E_|[E_|[E_|[E_|[E_|[E_|[E_|[]]]]]]]]]; [exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q11_8, A11_8, 56) ltac:(do 40 right; left; reflexivity) q_ Hq_ (eq_sym E_))| exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q11_7, A11_7, 56) ltac:(do 41 right; left; reflexivity) q_ Hq_ (eq_sym E_))| exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q11_6, A11_6, 128) ltac:(do 42 right; left; reflexivity) q_ Hq_ (eq_sym E_))| exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q11_5, A11_5, 104) ltac:(do 43 right; left; reflexivity) q_ Hq_ (eq_sym E_))| exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q11_4, A11_4, 128) ltac:(do 44 right; left; reflexivity) q_ Hq_ (eq_sym E_))| exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q11_3, A11_3, 104) ltac:(do 45 right; left; reflexivity) q_ Hq_ (eq_sym E_))| exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q11_2, A11_2, 40) ltac:(do 46 right; left; reflexivity) q_ Hq_ (eq_sym E_))| exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q11_1, A11_1, 48) ltac:(do 47 right; left; reflexivity) q_ Hq_ (eq_sym E_))]. } clear CSTx.
  pose proof (SF0 (fun _ : bptr => False)) as PRE0.
  assert (PREb1 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st1 LBc1 Lc1 mb1).
  { eapply cframe_call; [exact PRE0| exact FRM1| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PRE0.
  assert (PREa1 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st1 LBc1 Lc1 ma1).
  { eapply cframe_call; [exact PREb1| exact (SF1 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb1.
  assert (PREb2 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st2 LBc2 Lc2 mb2).
  { eapply cframe_call; [exact PREa1| exact FRM2| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa1.
  assert (PREb3 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st3 LBc3 Lc3 mb3).
  { eapply cframe_call; [exact PREb2| exact FRM3| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREb2.
  assert (PREa3 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st3 LBc3 Lc3 ma3).
  { eapply cframe_call; [exact PREb3| exact (SF3 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb3.
  assert (PREb4 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st4 LBc4 Lc4 mb4).
  { eapply cframe_call; [exact PREa3| exact FRM4| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa3.
  assert (PREa4 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st4 LBc4 Lc4 ma4).
  { eapply cframe_call; [exact PREb4| exact (SF4 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb4.
  assert (PREb5 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st5 LBc5 Lc5 mb5).
  { eapply cframe_call; [exact PREa4| exact FRM5| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa4.
  assert (PREa5 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st5 LBc5 Lc5 ma5).
  { eapply cframe_call; [exact PREb5| exact (SF5 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb5.
  assert (PREb6 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st6 LBc6 Lc6 mb6).
  { eapply cframe_call; [exact PREa5| exact FRM6| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa5.
  assert (PREa6 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st6 LBc6 Lc6 ma6).
  { eapply cframe_call; [exact PREb6| exact (SF6 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb6.
  assert (PREb7 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st7 LBc7 Lc7 mb7).
  { eapply cframe_call; [exact PREa6| exact FRM7| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa6.
  assert (PREa7 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st7 LBc7 Lc7 ma7).
  { eapply cframe_call; [exact PREb7| exact (SF7 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb7.
  assert (PREb8 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st8 LBc8 Lc8 mb8).
  { eapply cframe_call; [exact PREa7| exact FRM8| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa7.
  assert (PREa8 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st8 LBc8 Lc8 ma8).
  { eapply cframe_call; [exact PREb8| exact (SF8 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb8.
  assert (PREb9 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st9 LBc9 Lc9 mb9).
  { eapply cframe_call; [exact PREa8| exact FRM9| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa8.
  assert (PREa9 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st9 LBc9 Lc9 ma9).
  { eapply cframe_call; [exact PREb9| exact (SF9 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb9.
  assert (PREb10 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st10 LBc10 Lc10 mb10).
  { eapply cframe_call; [exact PREa9| exact FRM10| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa9.
  assert (PREa10 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st10 LBc10 Lc10 ma10).
  { eapply cframe_call; [exact PREb10| exact (SF10 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb10.
  assert (PREb11 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st11 LBc11 Lc11 mb11).
  { eapply cframe_call; [exact PREa10| exact FRM11| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa10.
  assert (PREa11 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st11 LBc11 Lc11 ma11).
  { eapply cframe_call; [exact PREb11| exact (SF11 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb11.
  assert (PREb12 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st12 LBc12 Lc12 mb12).
  { eapply cframe_call; [exact PREa11| exact FRM12| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa11.
  assert (PREa12 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st12 LBc12 Lc12 ma12).
  { eapply cframe_call; [exact PREb12| exact (SF12 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb12.
  assert (PREb13 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st13 LBc13 Lc13 mb13).
  { eapply cframe_call; [exact PREa12| exact FRM13| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa12.
  assert (PREa13 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st13 LBc13 Lc13 ma13).
  { eapply cframe_call; [exact PREb13| exact (SF13 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb13.
  assert (PREb14 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st14 LBc14 Lc14 mb14).
  { eapply cframe_call; [exact PREa13| exact FRM14| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa13.
  assert (PREa14 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st14 LBc14 Lc14 ma14).
  { eapply cframe_call; [exact PREb14| exact (SF14 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb14.
  assert (PREb15 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st15 LBc15 Lc15 mb15).
  { eapply cframe_call; [exact PREa14| exact FRM15| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa14.
  assert (PREa15 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st15 LBc15 Lc15 ma15).
  { eapply cframe_call; [exact PREb15| exact (SF15 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb15.
  assert (PREb16 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st16 LBc16 Lc16 mb16).
  { eapply cframe_call; [exact PREa15| exact FRM16| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa15.
  assert (PREa16 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st16 LBc16 Lc16 ma16).
  { eapply cframe_call; [exact PREb16| exact (SF16 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb16.
  assert (PREb17 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st17 LBc17 Lc17 mb17).
  { eapply cframe_call; [exact PREa16| exact FRM17| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa16.
  assert (PREa17 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st17 LBc17 Lc17 ma17).
  { eapply cframe_call; [exact PREb17| exact (SF17 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb17.
  assert (PREb18 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st18 LBc18 Lc18 mb18).
  { eapply cframe_call; [exact PREa17| exact FRM18| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa17.
  assert (PREa18 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st18 LBc18 Lc18 ma18).
  { eapply cframe_call; [exact PREb18| exact (SF18 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb18.
  assert (PREb19 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st19 LBc19 Lc19 mb19).
  { eapply cframe_call; [exact PREa18| exact FRM19| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa18.
  assert (PREa19 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st19 LBc19 Lc19 ma19).
  { eapply cframe_call; [exact PREb19| exact (SF19 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb19.
  assert (PREb20 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st20 LBc20 Lc20 mb20).
  { eapply cframe_call; [exact PREa19| exact FRM20| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREa19.
  assert (PREa20 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st20 LBc20 Lc20 ma20).
  { eapply cframe_call; [exact PREb20| exact (SF20 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb20.
  assert (PREb21 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st21 LBc21 Lc21 mb21).
  { eapply cframe_call; [exact PREa20| exact FRM21| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 Hq0 _; exact (FRESH q0 Hq0)]. } clear PREa20.
  assert (PREb22 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st22 LBc22 Lc22 mb22).
  { eapply cframe_call; [exact PREb21| exact FRM22| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. } clear PREb21.
  assert (PREa22 : cframe (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact PREb22| exact (SF22 (fun _ : bptr => False))| apply Z.le_refl| intros a X; exact X| intros q0 _ _ Y; exact Y]. } clear PREb22.
  rename PREa22 into FRz.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CSTz) as [NDz _].
  pose proof (wp_notin_pos (map blk_id LBc22) 123%nat q1_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q1_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 122%nat q2_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q2_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 121%nat q3_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 108%nat q3_14 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_14.
  pose proof (wp_notin_pos (map blk_id LBc22) 109%nat q3_13 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_13.
  pose proof (wp_notin_pos (map blk_id LBc22) 110%nat q3_12 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_12.
  pose proof (wp_notin_pos (map blk_id LBc22) 111%nat q3_11 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_11.
  pose proof (wp_notin_pos (map blk_id LBc22) 112%nat q3_10 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_10.
  pose proof (wp_notin_pos (map blk_id LBc22) 113%nat q3_9 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_9.
  pose proof (wp_notin_pos (map blk_id LBc22) 114%nat q3_8 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_8.
  pose proof (wp_notin_pos (map blk_id LBc22) 115%nat q3_7 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_7.
  pose proof (wp_notin_pos (map blk_id LBc22) 116%nat q3_6 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_6.
  pose proof (wp_notin_pos (map blk_id LBc22) 117%nat q3_5 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_5.
  pose proof (wp_notin_pos (map blk_id LBc22) 118%nat q3_4 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_4.
  pose proof (wp_notin_pos (map blk_id LBc22) 119%nat q3_3 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_3.
  pose proof (wp_notin_pos (map blk_id LBc22) 120%nat q3_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 107%nat q3_15 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q3_15.
  pose proof (wp_notin_pos (map blk_id LBc22) 106%nat q4_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q4_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 105%nat q4_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q4_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 104%nat q5_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q5_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 103%nat q5_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q5_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 102%nat q5_3 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q5_3.
  pose proof (wp_notin_pos (map blk_id LBc22) 101%nat q6_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 88%nat q6_14 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_14.
  pose proof (wp_notin_pos (map blk_id LBc22) 89%nat q6_13 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_13.
  pose proof (wp_notin_pos (map blk_id LBc22) 90%nat q6_12 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_12.
  pose proof (wp_notin_pos (map blk_id LBc22) 91%nat q6_11 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_11.
  pose proof (wp_notin_pos (map blk_id LBc22) 92%nat q6_10 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_10.
  pose proof (wp_notin_pos (map blk_id LBc22) 93%nat q6_9 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_9.
  pose proof (wp_notin_pos (map blk_id LBc22) 94%nat q6_8 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_8.
  pose proof (wp_notin_pos (map blk_id LBc22) 95%nat q6_7 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_7.
  pose proof (wp_notin_pos (map blk_id LBc22) 96%nat q6_6 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_6.
  pose proof (wp_notin_pos (map blk_id LBc22) 97%nat q6_5 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_5.
  pose proof (wp_notin_pos (map blk_id LBc22) 98%nat q6_4 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_4.
  pose proof (wp_notin_pos (map blk_id LBc22) 99%nat q6_3 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_3.
  pose proof (wp_notin_pos (map blk_id LBc22) 100%nat q6_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 87%nat q6_15 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q6_15.
  pose proof (wp_notin_pos (map blk_id LBc22) 82%nat q8_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 69%nat q8_14 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_14.
  pose proof (wp_notin_pos (map blk_id LBc22) 70%nat q8_13 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_13.
  pose proof (wp_notin_pos (map blk_id LBc22) 71%nat q8_12 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_12.
  pose proof (wp_notin_pos (map blk_id LBc22) 72%nat q8_11 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_11.
  pose proof (wp_notin_pos (map blk_id LBc22) 73%nat q8_10 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_10.
  pose proof (wp_notin_pos (map blk_id LBc22) 74%nat q8_9 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_9.
  pose proof (wp_notin_pos (map blk_id LBc22) 75%nat q8_8 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_8.
  pose proof (wp_notin_pos (map blk_id LBc22) 76%nat q8_7 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_7.
  pose proof (wp_notin_pos (map blk_id LBc22) 77%nat q8_6 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_6.
  pose proof (wp_notin_pos (map blk_id LBc22) 78%nat q8_5 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_5.
  pose proof (wp_notin_pos (map blk_id LBc22) 79%nat q8_4 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_4.
  pose proof (wp_notin_pos (map blk_id LBc22) 80%nat q8_3 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_3.
  pose proof (wp_notin_pos (map blk_id LBc22) 81%nat q8_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 68%nat q8_15 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q8_15.
  pose proof (wp_notin_pos (map blk_id LBc22) 67%nat q9_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 54%nat q9_14 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_14.
  pose proof (wp_notin_pos (map blk_id LBc22) 55%nat q9_13 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_13.
  pose proof (wp_notin_pos (map blk_id LBc22) 56%nat q9_12 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_12.
  pose proof (wp_notin_pos (map blk_id LBc22) 57%nat q9_11 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_11.
  pose proof (wp_notin_pos (map blk_id LBc22) 58%nat q9_10 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_10.
  pose proof (wp_notin_pos (map blk_id LBc22) 59%nat q9_9 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_9.
  pose proof (wp_notin_pos (map blk_id LBc22) 60%nat q9_8 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_8.
  pose proof (wp_notin_pos (map blk_id LBc22) 61%nat q9_7 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_7.
  pose proof (wp_notin_pos (map blk_id LBc22) 62%nat q9_6 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_6.
  pose proof (wp_notin_pos (map blk_id LBc22) 63%nat q9_5 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_5.
  pose proof (wp_notin_pos (map blk_id LBc22) 64%nat q9_4 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_4.
  pose proof (wp_notin_pos (map blk_id LBc22) 65%nat q9_3 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_3.
  pose proof (wp_notin_pos (map blk_id LBc22) 66%nat q9_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 53%nat q9_15 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q9_15.
  pose proof (wp_notin_pos (map blk_id LBc22) 52%nat q10_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q10_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 49%nat q10_4 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q10_4.
  pose proof (wp_notin_pos (map blk_id LBc22) 50%nat q10_3 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q10_3.
  pose proof (wp_notin_pos (map blk_id LBc22) 51%nat q10_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q10_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 48%nat q10_5 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q10_5.
  pose proof (wp_notin_pos (map blk_id LBc22) 28%nat q14_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q14_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 27%nat q15_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q15_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 26%nat q16_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q16_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 25%nat q16_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q16_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 24%nat q17_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q17_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 23%nat q18_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q18_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 22%nat q19_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q19_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 21%nat q19_2 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q19_2.
  pose proof (wp_notin_pos (map blk_id LBc22) 20%nat q19_3 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q19_3.
  pose proof (wp_notin_pos (map blk_id LBc22) 19%nat q20_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q20_1.
  pose proof (wp_notin_pos (map blk_id LBc22) 0%nat q22_1 [40; 41; 42; 43; 44; 45; 46; 47]%nat [q11_8; q11_7; q11_6; q11_5; q11_4; q11_3; q11_2; q11_1] NDz eq_refl eq_refl eq_refl) as NT_q22_1.
  pose proof (SF22 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8))) as SufB22.
  destruct PK22 as (IN_A22_1 & BC22_0).
  unfold wp_box in BC22_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q22_1, A22_1, 56) (proj1 SufB22) BC22_0 IN_A22_1 ltac:(exact NT_q22_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC22_0. clear BC22_0.
  assert (LF22 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st21 LBc21 Lc21 mb21 st22 LBc22 Lc22 mb22).
  { eapply cframe_call; [apply cframe_refl| exact FRM22| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA21 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st21 LBc21 Lc21 mb21 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF22| exact SufB22| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  pose proof SufA21 as SufB21.
  clear LF22 SufA21 SufB22 FRM22.
  destruct PK21 as (IN_A21_18 & IN_A21_17 & IN_A21_16 & IN_A21_15 & IN_A21_14 & IN_A21_13 & IN_A21_12 & IN_A21_11 & IN_A21_10 & IN_A21_9 & IN_A21_8 & IN_A21_7 & IN_A21_6 & IN_A21_5 & IN_A21_4 & IN_A21_3 & IN_A21_2 & IN_A21_1).
  assert (LF21 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st20 LBc20 Lc20 ma20 st21 LBc21 Lc21 mb21).
  { eapply cframe_call; [apply cframe_refl| exact FRM21| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ X; exact X]. }
  assert (SufA20 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st20 LBc20 Lc20 ma20 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF21| exact SufB21| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB20 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st20 LBc20 Lc20 mb20 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF20 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA20| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF21 SufA20 SufB21 FRM21.
  destruct PK20 as (IN_A20_1 & BC20_0).
  unfold wp_box in BC20_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q20_1, A20_1, 88) (proj1 SufB20) BC20_0 IN_A20_1 ltac:(exact NT_q20_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC20_0. clear BC20_0.
  assert (LF20 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st19 LBc19 Lc19 ma19 st20 LBc20 Lc20 mb20).
  { eapply cframe_call; [apply cframe_refl| exact FRM20| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA19 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st19 LBc19 Lc19 ma19 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF20| exact SufB20| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB19 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st19 LBc19 Lc19 mb19 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF19 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA19| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF20 SufA19 SufB20 FRM20.
  destruct PK19 as (IN_A19_3 & IN_A19_2 & IN_A19_1 & BC19_0 & BC19_1 & BC19_2).
  unfold wp_box in BC19_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q19_1, A19_1, 32) (proj1 SufB19) BC19_0 IN_A19_1 ltac:(exact NT_q19_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC19_0. clear BC19_0.
  unfold wp_box in BC19_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q19_2, A19_2, 40) (proj1 SufB19) BC19_1 IN_A19_2 ltac:(exact NT_q19_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC19_1. clear BC19_1.
  unfold wp_box in BC19_2. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q19_3, A19_3, 48) (proj1 SufB19) BC19_2 IN_A19_3 ltac:(exact NT_q19_3) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC19_2. clear BC19_2.
  assert (LF19 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st18 LBc18 Lc18 ma18 st19 LBc19 Lc19 mb19).
  { eapply cframe_call; [apply cframe_refl| exact FRM19| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA18 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st18 LBc18 Lc18 ma18 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF19| exact SufB19| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB18 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st18 LBc18 Lc18 mb18 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF18 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA18| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF19 SufA18 SufB19 FRM19.
  destruct PK18 as (IN_A18_1 & BC18_0).
  unfold wp_box in BC18_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q18_1, A18_1, 8) (proj1 SufB18) BC18_0 IN_A18_1 ltac:(exact NT_q18_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC18_0. clear BC18_0.
  assert (LF18 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st17 LBc17 Lc17 ma17 st18 LBc18 Lc18 mb18).
  { eapply cframe_call; [apply cframe_refl| exact FRM18| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA17 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st17 LBc17 Lc17 ma17 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF18| exact SufB18| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB17 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st17 LBc17 Lc17 mb17 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF17 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA17| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF18 SufA17 SufB18 FRM18.
  destruct PK17 as (IN_A17_1 & BC17_0).
  unfold wp_box in BC17_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q17_1, A17_1, 16) (proj1 SufB17) BC17_0 IN_A17_1 ltac:(exact NT_q17_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC17_0. clear BC17_0.
  assert (LF17 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st16 LBc16 Lc16 ma16 st17 LBc17 Lc17 mb17).
  { eapply cframe_call; [apply cframe_refl| exact FRM17| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA16 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st16 LBc16 Lc16 ma16 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF17| exact SufB17| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB16 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st16 LBc16 Lc16 mb16 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF16 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA16| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF17 SufA16 SufB17 FRM17.
  unfold wp_box in BC16_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q16_1, A16_1, 16) (proj1 SufB16) BC16_0 IN_A16_1 ltac:(exact NT_q16_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC16_0. clear BC16_0.
  unfold wp_box in BC16_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q16_2, A16_2, 40) (proj1 SufB16) BC16_1 IN_A16_2 ltac:(exact NT_q16_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC16_1. clear BC16_1.
  assert (LF16 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st15 LBc15 Lc15 ma15 st16 LBc16 Lc16 mb16).
  { eapply cframe_call; [apply cframe_refl| exact FRM16| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA15 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st15 LBc15 Lc15 ma15 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF16| exact SufB16| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB15 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st15 LBc15 Lc15 mb15 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF15 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA15| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF16 SufA15 SufB16 FRM16.
  destruct PK15 as (IN_A15_1 & BC15_0).
  unfold wp_box in BC15_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q15_1, A15_1, 56) (proj1 SufB15) BC15_0 IN_A15_1 ltac:(exact NT_q15_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC15_0. clear BC15_0.
  assert (LF15 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st14 LBc14 Lc14 ma14 st15 LBc15 Lc15 mb15).
  { eapply cframe_call; [apply cframe_refl| exact FRM15| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA14 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st14 LBc14 Lc14 ma14 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF15| exact SufB15| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB14 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st14 LBc14 Lc14 mb14 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF14 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA14| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF15 SufA14 SufB15 FRM15.
  destruct PK14 as (IN_A14_1 & BC14_0).
  unfold wp_box in BC14_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q14_1, A14_1, 16) (proj1 SufB14) BC14_0 IN_A14_1 ltac:(exact NT_q14_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC14_0. clear BC14_0.
  assert (LF14 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st13 LBc13 Lc13 ma13 st14 LBc14 Lc14 mb14).
  { eapply cframe_call; [apply cframe_refl| exact FRM14| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA13 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st13 LBc13 Lc13 ma13 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF14| exact SufB14| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB13 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st13 LBc13 Lc13 mb13 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF13 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA13| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF14 SufA13 SufB14 FRM14.
  destruct PK13 as (IN_A13_2 & IN_A13_1).
  assert (LF13 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st12 LBc12 Lc12 ma12 st13 LBc13 Lc13 mb13).
  { eapply cframe_call; [apply cframe_refl| exact FRM13| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA12 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st12 LBc12 Lc12 ma12 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF13| exact SufB13| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB12 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st12 LBc12 Lc12 mb12 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF12 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA12| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF13 SufA12 SufB13 FRM13.
  destruct PK12 as (IN_A12_9 & IN_A12_8 & IN_A12_7 & IN_A12_6 & IN_A12_5 & IN_A12_4 & IN_A12_3 & IN_A12_2 & IN_A12_1).
  assert (LF12 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st11 LBc11 Lc11 ma11 st12 LBc12 Lc12 mb12).
  { eapply cframe_call; [apply cframe_refl| exact FRM12| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA11 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st11 LBc11 Lc11 ma11 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF12| exact SufB12| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB11 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st11 LBc11 Lc11 mb11 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF11 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA11| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF12 SufA11 SufB12 FRM12.
  destruct PK11 as (IN_A11_8 & IN_A11_7 & IN_A11_6 & IN_A11_5 & IN_A11_4 & IN_A11_3 & IN_A11_2 & IN_A11_1).
  assert (LF11 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st10 LBc10 Lc10 ma10 st11 LBc11 Lc11 mb11).
  { eapply cframe_call; [apply cframe_refl| exact FRM11| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA10 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st10 LBc10 Lc10 ma10 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF11| exact SufB11| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB10 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st10 LBc10 Lc10 mb10 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF10 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA10| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF11 SufA10 SufB11 FRM11.
  destruct PK10 as (IN_A10_5 & IN_A10_4 & IN_A10_3 & IN_A10_2 & IN_A10_1 & BC10_0 & BC10_1 & BC10_2 & BC10_3 & BC10_4).
  unfold wp_box in BC10_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q10_1, A10_1, 80) (proj1 SufB10) BC10_0 IN_A10_1 ltac:(exact NT_q10_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC10_0. clear BC10_0.
  unfold wp_box in BC10_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q10_4, A10_4, 56) (proj1 SufB10) BC10_1 IN_A10_4 ltac:(exact NT_q10_4) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC10_1. clear BC10_1.
  unfold wp_box in BC10_2. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q10_3, A10_3, 40) (proj1 SufB10) BC10_2 IN_A10_3 ltac:(exact NT_q10_3) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC10_2. clear BC10_2.
  unfold wp_box in BC10_3. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q10_2, A10_2, 56) (proj1 SufB10) BC10_3 IN_A10_2 ltac:(exact NT_q10_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC10_3. clear BC10_3.
  unfold wp_box in BC10_4. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q10_5, A10_5, 40) (proj1 SufB10) BC10_4 IN_A10_5 ltac:(exact NT_q10_5) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC10_4. clear BC10_4.
  assert (LF10 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st9 LBc9 Lc9 ma9 st10 LBc10 Lc10 mb10).
  { eapply cframe_call; [apply cframe_refl| exact FRM10| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA9 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st9 LBc9 Lc9 ma9 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF10| exact SufB10| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB9 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st9 LBc9 Lc9 mb9 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF9 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA9| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF10 SufA9 SufB10 FRM10.
  destruct PK9 as (IN_A9_15 & IN_A9_14 & IN_A9_13 & IN_A9_12 & IN_A9_11 & IN_A9_10 & IN_A9_9 & IN_A9_8 & IN_A9_7 & IN_A9_6 & IN_A9_5 & IN_A9_4 & IN_A9_3 & IN_A9_2 & IN_A9_1 & BC9_0 & BC9_1 & BC9_2 & BC9_3 & BC9_4 & BC9_5 & BC9_6 & BC9_7 & BC9_8 & BC9_9 & BC9_10 & BC9_11 & BC9_12 & BC9_13 & BC9_14).
  unfold wp_box in BC9_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_1, A9_1, 24) (proj1 SufB9) BC9_0 IN_A9_1 ltac:(exact NT_q9_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_0. clear BC9_0.
  unfold wp_box in BC9_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_14, A9_14, 40) (proj1 SufB9) BC9_1 IN_A9_14 ltac:(exact NT_q9_14) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_1. clear BC9_1.
  unfold wp_box in BC9_2. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_13, A9_13, 40) (proj1 SufB9) BC9_2 IN_A9_13 ltac:(exact NT_q9_13) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_2. clear BC9_2.
  unfold wp_box in BC9_3. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_12, A9_12, 32) (proj1 SufB9) BC9_3 IN_A9_12 ltac:(exact NT_q9_12) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_3. clear BC9_3.
  unfold wp_box in BC9_4. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_11, A9_11, 40) (proj1 SufB9) BC9_4 IN_A9_11 ltac:(exact NT_q9_11) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_4. clear BC9_4.
  unfold wp_box in BC9_5. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_10, A9_10, 40) (proj1 SufB9) BC9_5 IN_A9_10 ltac:(exact NT_q9_10) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_5. clear BC9_5.
  unfold wp_box in BC9_6. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_9, A9_9, 32) (proj1 SufB9) BC9_6 IN_A9_9 ltac:(exact NT_q9_9) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_6. clear BC9_6.
  unfold wp_box in BC9_7. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_8, A9_8, 40) (proj1 SufB9) BC9_7 IN_A9_8 ltac:(exact NT_q9_8) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_7. clear BC9_7.
  unfold wp_box in BC9_8. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_7, A9_7, 40) (proj1 SufB9) BC9_8 IN_A9_7 ltac:(exact NT_q9_7) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_8. clear BC9_8.
  unfold wp_box in BC9_9. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_6, A9_6, 32) (proj1 SufB9) BC9_9 IN_A9_6 ltac:(exact NT_q9_6) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_9. clear BC9_9.
  unfold wp_box in BC9_10. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_5, A9_5, 40) (proj1 SufB9) BC9_10 IN_A9_5 ltac:(exact NT_q9_5) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_10. clear BC9_10.
  unfold wp_box in BC9_11. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_4, A9_4, 40) (proj1 SufB9) BC9_11 IN_A9_4 ltac:(exact NT_q9_4) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_11. clear BC9_11.
  unfold wp_box in BC9_12. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_3, A9_3, 32) (proj1 SufB9) BC9_12 IN_A9_3 ltac:(exact NT_q9_3) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_12. clear BC9_12.
  unfold wp_box in BC9_13. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_2, A9_2, 384) (proj1 SufB9) BC9_13 IN_A9_2 ltac:(exact NT_q9_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_13. clear BC9_13.
  unfold wp_box in BC9_14. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q9_15, A9_15, 40) (proj1 SufB9) BC9_14 IN_A9_15 ltac:(exact NT_q9_15) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC9_14. clear BC9_14.
  assert (LF9 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st8 LBc8 Lc8 ma8 st9 LBc9 Lc9 mb9).
  { eapply cframe_call; [apply cframe_refl| exact FRM9| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA8 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st8 LBc8 Lc8 ma8 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF9| exact SufB9| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB8 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st8 LBc8 Lc8 mb8 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF8 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA8| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF9 SufA8 SufB9 FRM9.
  destruct PK8 as (IN_A8_15 & IN_A8_14 & IN_A8_13 & IN_A8_12 & IN_A8_11 & IN_A8_10 & IN_A8_9 & IN_A8_8 & IN_A8_7 & IN_A8_6 & IN_A8_5 & IN_A8_4 & IN_A8_3 & IN_A8_2 & IN_A8_1 & BC8_0 & BC8_1 & BC8_2 & BC8_3 & BC8_4 & BC8_5 & BC8_6 & BC8_7 & BC8_8 & BC8_9 & BC8_10 & BC8_11 & BC8_12 & BC8_13 & BC8_14).
  unfold wp_box in BC8_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_1, A8_1, 24) (proj1 SufB8) BC8_0 IN_A8_1 ltac:(exact NT_q8_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_0. clear BC8_0.
  unfold wp_box in BC8_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_14, A8_14, 40) (proj1 SufB8) BC8_1 IN_A8_14 ltac:(exact NT_q8_14) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_1. clear BC8_1.
  unfold wp_box in BC8_2. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_13, A8_13, 40) (proj1 SufB8) BC8_2 IN_A8_13 ltac:(exact NT_q8_13) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_2. clear BC8_2.
  unfold wp_box in BC8_3. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_12, A8_12, 32) (proj1 SufB8) BC8_3 IN_A8_12 ltac:(exact NT_q8_12) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_3. clear BC8_3.
  unfold wp_box in BC8_4. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_11, A8_11, 40) (proj1 SufB8) BC8_4 IN_A8_11 ltac:(exact NT_q8_11) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_4. clear BC8_4.
  unfold wp_box in BC8_5. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_10, A8_10, 40) (proj1 SufB8) BC8_5 IN_A8_10 ltac:(exact NT_q8_10) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_5. clear BC8_5.
  unfold wp_box in BC8_6. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_9, A8_9, 32) (proj1 SufB8) BC8_6 IN_A8_9 ltac:(exact NT_q8_9) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_6. clear BC8_6.
  unfold wp_box in BC8_7. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_8, A8_8, 40) (proj1 SufB8) BC8_7 IN_A8_8 ltac:(exact NT_q8_8) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_7. clear BC8_7.
  unfold wp_box in BC8_8. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_7, A8_7, 40) (proj1 SufB8) BC8_8 IN_A8_7 ltac:(exact NT_q8_7) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_8. clear BC8_8.
  unfold wp_box in BC8_9. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_6, A8_6, 32) (proj1 SufB8) BC8_9 IN_A8_6 ltac:(exact NT_q8_6) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_9. clear BC8_9.
  unfold wp_box in BC8_10. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_5, A8_5, 40) (proj1 SufB8) BC8_10 IN_A8_5 ltac:(exact NT_q8_5) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_10. clear BC8_10.
  unfold wp_box in BC8_11. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_4, A8_4, 40) (proj1 SufB8) BC8_11 IN_A8_4 ltac:(exact NT_q8_4) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_11. clear BC8_11.
  unfold wp_box in BC8_12. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_3, A8_3, 32) (proj1 SufB8) BC8_12 IN_A8_3 ltac:(exact NT_q8_3) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_12. clear BC8_12.
  unfold wp_box in BC8_13. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_2, A8_2, 384) (proj1 SufB8) BC8_13 IN_A8_2 ltac:(exact NT_q8_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_13. clear BC8_13.
  unfold wp_box in BC8_14. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q8_15, A8_15, 40) (proj1 SufB8) BC8_14 IN_A8_15 ltac:(exact NT_q8_15) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC8_14. clear BC8_14.
  assert (LF8 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st7 LBc7 Lc7 ma7 st8 LBc8 Lc8 mb8).
  { eapply cframe_call; [apply cframe_refl| exact FRM8| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA7 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st7 LBc7 Lc7 ma7 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF8| exact SufB8| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB7 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st7 LBc7 Lc7 mb7 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF7 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA7| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF8 SufA7 SufB8 FRM8.
  destruct PK7 as (IN_A7_4 & IN_A7_3 & IN_A7_2 & IN_A7_1).
  assert (LF7 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st6 LBc6 Lc6 ma6 st7 LBc7 Lc7 mb7).
  { eapply cframe_call; [apply cframe_refl| exact FRM7| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA6 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st6 LBc6 Lc6 ma6 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF7| exact SufB7| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB6 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st6 LBc6 Lc6 mb6 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF6 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA6| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF7 SufA6 SufB7 FRM7.
  destruct PK6 as (IN_A6_15 & IN_A6_14 & IN_A6_13 & IN_A6_12 & IN_A6_11 & IN_A6_10 & IN_A6_9 & IN_A6_8 & IN_A6_7 & IN_A6_6 & IN_A6_5 & IN_A6_4 & IN_A6_3 & IN_A6_2 & IN_A6_1 & BC6_0 & BC6_1 & BC6_2 & BC6_3 & BC6_4 & BC6_5 & BC6_6 & BC6_7 & BC6_8 & BC6_9 & BC6_10 & BC6_11 & BC6_12 & BC6_13 & BC6_14).
  unfold wp_box in BC6_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_1, A6_1, 24) (proj1 SufB6) BC6_0 IN_A6_1 ltac:(exact NT_q6_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_0. clear BC6_0.
  unfold wp_box in BC6_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_14, A6_14, 40) (proj1 SufB6) BC6_1 IN_A6_14 ltac:(exact NT_q6_14) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_1. clear BC6_1.
  unfold wp_box in BC6_2. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_13, A6_13, 40) (proj1 SufB6) BC6_2 IN_A6_13 ltac:(exact NT_q6_13) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_2. clear BC6_2.
  unfold wp_box in BC6_3. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_12, A6_12, 32) (proj1 SufB6) BC6_3 IN_A6_12 ltac:(exact NT_q6_12) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_3. clear BC6_3.
  unfold wp_box in BC6_4. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_11, A6_11, 40) (proj1 SufB6) BC6_4 IN_A6_11 ltac:(exact NT_q6_11) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_4. clear BC6_4.
  unfold wp_box in BC6_5. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_10, A6_10, 40) (proj1 SufB6) BC6_5 IN_A6_10 ltac:(exact NT_q6_10) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_5. clear BC6_5.
  unfold wp_box in BC6_6. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_9, A6_9, 32) (proj1 SufB6) BC6_6 IN_A6_9 ltac:(exact NT_q6_9) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_6. clear BC6_6.
  unfold wp_box in BC6_7. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_8, A6_8, 40) (proj1 SufB6) BC6_7 IN_A6_8 ltac:(exact NT_q6_8) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_7. clear BC6_7.
  unfold wp_box in BC6_8. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_7, A6_7, 40) (proj1 SufB6) BC6_8 IN_A6_7 ltac:(exact NT_q6_7) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_8. clear BC6_8.
  unfold wp_box in BC6_9. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_6, A6_6, 32) (proj1 SufB6) BC6_9 IN_A6_6 ltac:(exact NT_q6_6) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_9. clear BC6_9.
  unfold wp_box in BC6_10. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_5, A6_5, 40) (proj1 SufB6) BC6_10 IN_A6_5 ltac:(exact NT_q6_5) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_10. clear BC6_10.
  unfold wp_box in BC6_11. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_4, A6_4, 40) (proj1 SufB6) BC6_11 IN_A6_4 ltac:(exact NT_q6_4) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_11. clear BC6_11.
  unfold wp_box in BC6_12. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_3, A6_3, 32) (proj1 SufB6) BC6_12 IN_A6_3 ltac:(exact NT_q6_3) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_12. clear BC6_12.
  unfold wp_box in BC6_13. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_2, A6_2, 384) (proj1 SufB6) BC6_13 IN_A6_2 ltac:(exact NT_q6_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_13. clear BC6_13.
  unfold wp_box in BC6_14. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q6_15, A6_15, 40) (proj1 SufB6) BC6_14 IN_A6_15 ltac:(exact NT_q6_15) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC6_14. clear BC6_14.
  assert (LF6 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st5 LBc5 Lc5 ma5 st6 LBc6 Lc6 mb6).
  { eapply cframe_call; [apply cframe_refl| exact FRM6| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA5 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st5 LBc5 Lc5 ma5 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF6| exact SufB6| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB5 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st5 LBc5 Lc5 mb5 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF5 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA5| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF6 SufA5 SufB6 FRM6.
  destruct PK5 as (IN_A5_3 & IN_A5_2 & IN_A5_1 & BC5_0 & BC5_1 & BC5_2).
  unfold wp_box in BC5_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q5_1, A5_1, 88) (proj1 SufB5) BC5_0 IN_A5_1 ltac:(exact NT_q5_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC5_0. clear BC5_0.
  unfold wp_box in BC5_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q5_2, A5_2, 5) (proj1 SufB5) BC5_1 IN_A5_2 ltac:(exact NT_q5_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC5_1. clear BC5_1.
  unfold wp_box in BC5_2. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q5_3, A5_3, 40) (proj1 SufB5) BC5_2 IN_A5_3 ltac:(exact NT_q5_3) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC5_2. clear BC5_2.
  assert (LF5 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st4 LBc4 Lc4 ma4 st5 LBc5 Lc5 mb5).
  { eapply cframe_call; [apply cframe_refl| exact FRM5| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA4 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st4 LBc4 Lc4 ma4 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF5| exact SufB5| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB4 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st4 LBc4 Lc4 mb4 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF4 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA4| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF5 SufA4 SufB5 FRM5.
  destruct PK4 as (IN_A4_2 & IN_A4_1 & BC4_0 & BC4_1).
  unfold wp_box in BC4_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q4_1, A4_1, 16) (proj1 SufB4) BC4_0 IN_A4_1 ltac:(exact NT_q4_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC4_0. clear BC4_0.
  unfold wp_box in BC4_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q4_2, A4_2, 40) (proj1 SufB4) BC4_1 IN_A4_2 ltac:(exact NT_q4_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC4_1. clear BC4_1.
  assert (LF4 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st3 LBc3 Lc3 ma3 st4 LBc4 Lc4 mb4).
  { eapply cframe_call; [apply cframe_refl| exact FRM4| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA3 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st3 LBc3 Lc3 ma3 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF4| exact SufB4| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB3 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st3 LBc3 Lc3 mb3 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF3 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA3| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF4 SufA3 SufB4 FRM4.
  destruct PK3 as (IN_A3_15 & IN_A3_14 & IN_A3_13 & IN_A3_12 & IN_A3_11 & IN_A3_10 & IN_A3_9 & IN_A3_8 & IN_A3_7 & IN_A3_6 & IN_A3_5 & IN_A3_4 & IN_A3_3 & IN_A3_2 & IN_A3_1 & BC3_0 & BC3_1 & BC3_2 & BC3_3 & BC3_4 & BC3_5 & BC3_6 & BC3_7 & BC3_8 & BC3_9 & BC3_10 & BC3_11 & BC3_12 & BC3_13 & BC3_14).
  unfold wp_box in BC3_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_1, A3_1, 24) (proj1 SufB3) BC3_0 IN_A3_1 ltac:(exact NT_q3_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_0. clear BC3_0.
  unfold wp_box in BC3_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_14, A3_14, 40) (proj1 SufB3) BC3_1 IN_A3_14 ltac:(exact NT_q3_14) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_1. clear BC3_1.
  unfold wp_box in BC3_2. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_13, A3_13, 40) (proj1 SufB3) BC3_2 IN_A3_13 ltac:(exact NT_q3_13) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_2. clear BC3_2.
  unfold wp_box in BC3_3. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_12, A3_12, 32) (proj1 SufB3) BC3_3 IN_A3_12 ltac:(exact NT_q3_12) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_3. clear BC3_3.
  unfold wp_box in BC3_4. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_11, A3_11, 40) (proj1 SufB3) BC3_4 IN_A3_11 ltac:(exact NT_q3_11) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_4. clear BC3_4.
  unfold wp_box in BC3_5. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_10, A3_10, 40) (proj1 SufB3) BC3_5 IN_A3_10 ltac:(exact NT_q3_10) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_5. clear BC3_5.
  unfold wp_box in BC3_6. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_9, A3_9, 32) (proj1 SufB3) BC3_6 IN_A3_9 ltac:(exact NT_q3_9) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_6. clear BC3_6.
  unfold wp_box in BC3_7. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_8, A3_8, 40) (proj1 SufB3) BC3_7 IN_A3_8 ltac:(exact NT_q3_8) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_7. clear BC3_7.
  unfold wp_box in BC3_8. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_7, A3_7, 40) (proj1 SufB3) BC3_8 IN_A3_7 ltac:(exact NT_q3_7) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_8. clear BC3_8.
  unfold wp_box in BC3_9. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_6, A3_6, 32) (proj1 SufB3) BC3_9 IN_A3_6 ltac:(exact NT_q3_6) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_9. clear BC3_9.
  unfold wp_box in BC3_10. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_5, A3_5, 40) (proj1 SufB3) BC3_10 IN_A3_5 ltac:(exact NT_q3_5) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_10. clear BC3_10.
  unfold wp_box in BC3_11. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_4, A3_4, 40) (proj1 SufB3) BC3_11 IN_A3_4 ltac:(exact NT_q3_4) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_11. clear BC3_11.
  unfold wp_box in BC3_12. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_3, A3_3, 32) (proj1 SufB3) BC3_12 IN_A3_3 ltac:(exact NT_q3_3) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_12. clear BC3_12.
  unfold wp_box in BC3_13. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_2, A3_2, 384) (proj1 SufB3) BC3_13 IN_A3_2 ltac:(exact NT_q3_2) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_13. clear BC3_13.
  unfold wp_box in BC3_14. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_15, A3_15, 40) (proj1 SufB3) BC3_14 IN_A3_15 ltac:(exact NT_q3_15) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC3_14. clear BC3_14.
  assert (LF3 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st2 LBc2 Lc2 mb2 st3 LBc3 Lc3 mb3).
  { eapply cframe_call; [apply cframe_refl| exact FRM3| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA2 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st2 LBc2 Lc2 mb2 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF3| exact SufB3| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  pose proof SufA2 as SufB2.
  clear LF3 SufA2 SufB3 FRM3.
  destruct PK2 as (IN_A2_1 & BC2_1).
  unfold wp_box in BC2_1. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q2_1, A2_1, 40) (proj1 SufB2) BC2_1 IN_A2_1 ltac:(exact NT_q2_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC2_1. clear BC2_1.
  assert (LF2 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st1 LBc1 Lc1 ma1 st2 LBc2 Lc2 mb2).
  { eapply cframe_call; [apply cframe_refl| exact FRM2| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA1 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st1 LBc1 Lc1 ma1 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF2| exact SufB2| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB1 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st1 LBc1 Lc1 mb1 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF1 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA1| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF2 SufA1 SufB2 FRM2.
  destruct PK1 as (IN_A1_1 & BC1_0).
  unfold wp_box in BC1_0. pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q1_1, A1_1, 40) (proj1 SufB1) BC1_0 IN_A1_1 ltac:(exact NT_q1_1) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as ZBC1_0. clear BC1_0.
  assert (LF1 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 ma0 st1 LBc1 Lc1 mb1).
  { eapply cframe_call; [apply cframe_refl| exact FRM1| wp_lia| intros a X; first [exact X | cbn [rin_ivs fst snd] in *; wp_lia | destruct X]| intros q0 _ _ Y; exact Y]. }
  assert (SufA0 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 ma0 st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact LF1| exact SufB1| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (SufB0 : cframe (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st22 LBc22 Lc22 mz).
  { eapply cframe_call; [exact (SF0 (ppk_T (PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8)))| exact SufA0| apply Z.le_refl| intros a X; exact X| intros q0 _ X; exact X]. }
  clear LF1 SufA0 SufB1 FRM1.
  apply climpl_done.
  exists (Z_to_bv 64 1), mz, LBc22.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [wp_lia|].
  split; [eapply cgrow_weaken; [exact GRc22| wp_wnorm; wp_lia..]|].
  split; [exact CSTz|]. split; [exact FRz|].
  exists q1_1, A1_1, q2_1, A2_1, q3_1, A3_1, q3_2, A3_2, q3_3, A3_3, q3_4, A3_4, q3_5, A3_5, q3_6, A3_6, q3_7, A3_7, q3_8, A3_8, q3_9, A3_9, q3_10, A3_10, q3_11, A3_11, q3_12, A3_12, q3_13, A3_13, q3_14, A3_14, q3_15, A3_15, q4_1, A4_1, q4_2, A4_2, q5_1, A5_1, q5_2, A5_2, q5_3, A5_3, q6_1, A6_1, q6_2, A6_2, q6_3, A6_3, q6_4, A6_4, q6_5, A6_5, q6_6, A6_6, q6_7, A6_7, q6_8, A6_8, q6_9, A6_9, q6_10, A6_10, q6_11, A6_11, q6_12, A6_12, q6_13, A6_13, q6_14, A6_14, q6_15, A6_15, q7_1, A7_1, q7_2, A7_2, q7_3, A7_3, q7_4, A7_4, q8_1, A8_1, q8_2, A8_2, q8_3, A8_3, q8_4, A8_4, q8_5, A8_5, q8_6, A8_6, q8_7, A8_7, q8_8, A8_8, q8_9, A8_9, q8_10, A8_10, q8_11, A8_11, q8_12, A8_12, q8_13, A8_13, q8_14, A8_14, q8_15, A8_15, q9_1, A9_1, q9_2, A9_2, q9_3, A9_3, q9_4, A9_4, q9_5, A9_5, q9_6, A9_6, q9_7, A9_7, q9_8, A9_8, q9_9, A9_9, q9_10, A9_10, q9_11, A9_11, q9_12, A9_12, q9_13, A9_13, q9_14, A9_14, q9_15, A9_15, q10_1, A10_1, q10_2, A10_2, q10_3, A10_3, q10_4, A10_4, q10_5, A10_5, q11_1, A11_1, q11_2, A11_2, q11_3, A11_3, q11_4, A11_4, q11_5, A11_5, q11_6, A11_6, q11_7, A11_7, q11_8, A11_8, q12_1, A12_1, q12_2, A12_2, q12_3, A12_3, q12_4, A12_4, q12_5, A12_5, q12_6, A12_6, q12_7, A12_7, q12_8, A12_8, q12_9, A12_9, q13_1, A13_1, q13_2, A13_2, q14_1, A14_1, q15_1, A15_1, q16_1, A16_1, q16_2, A16_2, q17_1, A17_1, q18_1, A18_1, q19_1, A19_1, q19_2, A19_2, q19_3, A19_3, q20_1, A20_1, q21_1, A21_1, q21_2, A21_2, q21_3, A21_3, q21_4, A21_4, q21_5, A21_5, q21_6, A21_6, q21_7, A21_7, q21_8, A21_8, q21_9, A21_9, q21_10, A21_10, q21_11, A21_11, q21_12, A21_12, q21_13, A21_13, q21_14, A21_14, q21_15, A21_15, q21_16, A21_16, q21_17, A21_17, q21_18, A21_18, q22_1, A22_1.
  split; [reflexivity|]. split; [reflexivity|].
  split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. wp_cells.
Qed.
End WithCeiling0.
