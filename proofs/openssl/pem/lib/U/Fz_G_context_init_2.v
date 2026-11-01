(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
  fun v LBall' L' m' =>
  exists (q1_1 : bptr) (A1_1 : Z) (q2_1 : bptr) (A2_1 : Z) (q3_1 : bptr) (A3_1 : Z) (q3_2 : bptr) (A3_2 : Z) (q3_3 : bptr) (A3_3 : Z) (q3_4 : bptr) (A3_4 : Z) (q3_5 : bptr) (A3_5 : Z) (q3_6 : bptr) (A3_6 : Z) (q3_7 : bptr) (A3_7 : Z) (q3_8 : bptr) (A3_8 : Z) (q3_9 : bptr) (A3_9 : Z) (q3_10 : bptr) (A3_10 : Z) (q3_11 : bptr) (A3_11 : Z) (q3_12 : bptr) (A3_12 : Z) (q3_13 : bptr) (A3_13 : Z) (q3_14 : bptr) (A3_14 : Z) (q3_15 : bptr) (A3_15 : Z) (q4_1 : bptr) (A4_1 : Z) (q4_2 : bptr) (A4_2 : Z) (q5_1 : bptr) (A5_1 : Z) (q5_2 : bptr) (A5_2 : Z) (q5_3 : bptr) (A5_3 : Z) (q6_1 : bptr) (A6_1 : Z) (q6_2 : bptr) (A6_2 : Z) (q6_3 : bptr) (A6_3 : Z) (q6_4 : bptr) (A6_4 : Z) (q6_5 : bptr) (A6_5 : Z) (q6_6 : bptr) (A6_6 : Z) (q6_7 : bptr) (A6_7 : Z) (q6_8 : bptr) (A6_8 : Z) (q6_9 : bptr) (A6_9 : Z) (q6_10 : bptr) (A6_10 : Z) (q6_11 : bptr) (A6_11 : Z) (q6_12 : bptr) (A6_12 : Z) (q6_13 : bptr) (A6_13 : Z) (q6_14 : bptr) (A6_14 : Z) (q6_15 : bptr) (A6_15 : Z) (q7_1 : bptr) (A7_1 : Z) (q7_2 : bptr) (A7_2 : Z) (q7_3 : bptr) (A7_3 : Z) (q7_4 : bptr) (A7_4 : Z) (q8_1 : bptr) (A8_1 : Z) (q8_2 : bptr) (A8_2 : Z) (q8_3 : bptr) (A8_3 : Z) (q8_4 : bptr) (A8_4 : Z) (q8_5 : bptr) (A8_5 : Z) (q8_6 : bptr) (A8_6 : Z) (q8_7 : bptr) (A8_7 : Z) (q8_8 : bptr) (A8_8 : Z) (q8_9 : bptr) (A8_9 : Z) (q8_10 : bptr) (A8_10 : Z) (q8_11 : bptr) (A8_11 : Z) (q8_12 : bptr) (A8_12 : Z) (q8_13 : bptr) (A8_13 : Z) (q8_14 : bptr) (A8_14 : Z) (q8_15 : bptr) (A8_15 : Z) (q9_1 : bptr) (A9_1 : Z) (q9_2 : bptr) (A9_2 : Z) (q9_3 : bptr) (A9_3 : Z) (q9_4 : bptr) (A9_4 : Z) (q9_5 : bptr) (A9_5 : Z) (q9_6 : bptr) (A9_6 : Z) (q9_7 : bptr) (A9_7 : Z) (q9_8 : bptr) (A9_8 : Z) (q9_9 : bptr) (A9_9 : Z) (q9_10 : bptr) (A9_10 : Z) (q9_11 : bptr) (A9_11 : Z) (q9_12 : bptr) (A9_12 : Z) (q9_13 : bptr) (A9_13 : Z) (q9_14 : bptr) (A9_14 : Z) (q9_15 : bptr) (A9_15 : Z) (q10_1 : bptr) (A10_1 : Z) (q10_2 : bptr) (A10_2 : Z) (q10_3 : bptr) (A10_3 : Z) (q10_4 : bptr) (A10_4 : Z) (q10_5 : bptr) (A10_5 : Z) (q11_1 : bptr) (A11_1 : Z) (q11_2 : bptr) (A11_2 : Z) (q11_3 : bptr) (A11_3 : Z) (q11_4 : bptr) (A11_4 : Z) (q11_5 : bptr) (A11_5 : Z) (q11_6 : bptr) (A11_6 : Z) (q11_7 : bptr) (A11_7 : Z) (q11_8 : bptr) (A11_8 : Z) (q12_1 : bptr) (A12_1 : Z) (q12_2 : bptr) (A12_2 : Z) (q12_3 : bptr) (A12_3 : Z) (q12_4 : bptr) (A12_4 : Z) (q12_5 : bptr) (A12_5 : Z) (q12_6 : bptr) (A12_6 : Z) (q12_7 : bptr) (A12_7 : Z) (q12_8 : bptr) (A12_8 : Z) (q12_9 : bptr) (A12_9 : Z) (q13_1 : bptr) (A13_1 : Z) (q13_2 : bptr) (A13_2 : Z) (q14_1 : bptr) (A14_1 : Z) (q15_1 : bptr) (A15_1 : Z) (q16_1 : bptr) (A16_1 : Z) (q16_2 : bptr) (A16_2 : Z) (q17_1 : bptr) (A17_1 : Z) (q18_1 : bptr) (A18_1 : Z) (q19_1 : bptr) (A19_1 : Z) (q19_2 : bptr) (A19_2 : Z) (q19_3 : bptr) (A19_3 : Z) (q20_1 : bptr) (A20_1 : Z) (q21_1 : bptr) (A21_1 : Z) (q21_2 : bptr) (A21_2 : Z) (q21_3 : bptr) (A21_3 : Z) (q21_4 : bptr) (A21_4 : Z) (q21_5 : bptr) (A21_5 : Z) (q21_6 : bptr) (A21_6 : Z) (q21_7 : bptr) (A21_7 : Z) (q21_8 : bptr) (A21_8 : Z) (q21_9 : bptr) (A21_9 : Z) (q21_10 : bptr) (A21_10 : Z) (q21_11 : bptr) (A21_11 : Z) (q21_12 : bptr) (A21_12 : Z) (q21_13 : bptr) (A21_13 : Z) (q21_14 : bptr) (A21_14 : Z) (q21_15 : bptr) (A21_15 : Z) (q21_16 : bptr) (A21_16 : Z) (q21_17 : bptr) (A21_17 : Z) (q21_18 : bptr) (A21_18 : Z) (q22_1 : bptr) (A22_1 : Z),
    v = Z_to_bv 64 1
    /\ LBall' = [(q22_1, A22_1, 56); (q21_18, A21_18, 24); (q21_17, A21_17, 18); (q21_16, A21_16, 24); (q21_15, A21_15, 32); (q21_14, A21_14, 19); (q21_13, A21_13, 24); (q21_12, A21_12, 25); (q21_11, A21_11, 24); (q21_10, A21_10, 48); (q21_9, A21_9, 21); (q21_8, A21_8, 24); (q21_7, A21_7, 22); (q21_6, A21_6, 24); (q21_5, A21_5, 20); (q21_4, A21_4, 24); (q21_3, A21_3, 23); (q21_2, A21_2, 24); (q21_1, A21_1, 24); (q20_1, A20_1, 88); (q19_3, A19_3, 48); (q19_2, A19_2, 40); (q19_1, A19_1, 32); (q18_1, A18_1, 8); (q17_1, A17_1, 16); (q16_2, A16_2, 40); (q16_1, A16_1, 16); (q15_1, A15_1, 56); (q14_1, A14_1, 16); (q13_2, A13_2, 128); (q13_1, A13_1, 104); (q12_9, A12_9, 56); (q12_8, A12_8, 16); (q12_7, A12_7, 264); (q12_6, A12_6, 32768); (q12_5, A12_5, 24); (q12_4, A12_4, 40); (q12_3, A12_3, 96); (q12_2, A12_2, 40); (q12_1, A12_1, 40); (q11_8, A11_8, 56); (q11_7, A11_7, 56); (q11_6, A11_6, 128); (q11_5, A11_5, 104); (q11_4, A11_4, 128); (q11_3, A11_3, 104); (q11_2, A11_2, 40); (q11_1, A11_1, 48); (q10_5, A10_5, 40); (q10_4, A10_4, 56); (q10_3, A10_3, 40); (q10_2, A10_2, 56); (q10_1, A10_1, 80); (q9_15, A9_15, 40); (q9_14, A9_14, 40); (q9_13, A9_13, 40); (q9_12, A9_12, 32); (q9_11, A9_11, 40); (q9_10, A9_10, 40); (q9_9, A9_9, 32); (q9_8, A9_8, 40); (q9_7, A9_7, 40); (q9_6, A9_6, 32); (q9_5, A9_5, 40); (q9_4, A9_4, 40); (q9_3, A9_3, 32); (q9_2, A9_2, 384); (q9_1, A9_1, 24); (q8_15, A8_15, 40); (q8_14, A8_14, 40); (q8_13, A8_13, 40); (q8_12, A8_12, 32); (q8_11, A8_11, 40); (q8_10, A8_10, 40); (q8_9, A8_9, 32); (q8_8, A8_8, 40); (q8_7, A8_7, 40); (q8_6, A8_6, 32); (q8_5, A8_5, 40); (q8_4, A8_4, 40); (q8_3, A8_3, 32); (q8_2, A8_2, 384); (q8_1, A8_1, 24); (q7_4, A7_4, 128); (q7_3, A7_3, 104); (q7_2, A7_2, 40); (q7_1, A7_1, 16); (q6_15, A6_15, 40); (q6_14, A6_14, 40); (q6_13, A6_13, 40); (q6_12, A6_12, 32); (q6_11, A6_11, 40); (q6_10, A6_10, 40); (q6_9, A6_9, 32); (q6_8, A6_8, 40); (q6_7, A6_7, 40); (q6_6, A6_6, 32); (q6_5, A6_5, 40); (q6_4, A6_4, 40); (q6_3, A6_3, 32); (q6_2, A6_2, 384); (q6_1, A6_1, 24); (q5_3, A5_3, 40); (q5_2, A5_2, 5); (q5_1, A5_1, 88); (q4_2, A4_2, 40); (q4_1, A4_1, 16); (q3_15, A3_15, 40); (q3_14, A3_14, 40); (q3_13, A3_13, 40); (q3_12, A3_12, 32); (q3_11, A3_11, 40); (q3_10, A3_10, 40); (q3_9, A3_9, 32); (q3_8, A3_8, 40); (q3_7, A3_7, 40); (q3_6, A3_6, 32); (q3_5, A3_5, 40); (q3_4, A3_4, 40); (q3_3, A3_3, 32); (q3_2, A3_2, 384); (q3_1, A3_1, 24); (q2_1, A2_1, 40); (q1_1, A1_1, 40)] ++ LBall
    /\ rw_cells usegs m' A1_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A2_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A3_2); C8 (Z_to_bv 64 A3_15)]
    /\ rw_cells usegs m' A3_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A3_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A3_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A3_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A3_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A3_2 [C8 (Z_to_bv 64 A3_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_4); C8 (Z_to_bv 64 A3_5); C8 (Z_to_bv 64 A3_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_7); C8 (Z_to_bv 64 A3_8); C8 (Z_to_bv 64 A3_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_10); C8 (Z_to_bv 64 A3_11); C8 (Z_to_bv 64 A3_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A3_13); C8 (Z_to_bv 64 A3_14)]
    /\ rw_cells usegs m' A3_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A4_1 [C8 (Z_to_bv 64 A4_2); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells usegs m' A4_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A5_1 [C8 (Z_to_bv 64 A5_3); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 A5_2); CB 48 (repeat (Z_to_bv 8 0) 48)]
    /\ rw_cells usegs m' A5_2 [CB (S (length [Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 112; Z_to_bv 8 115])) ([Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 112; Z_to_bv 8 115] ++ [Z_to_bv 8 0])]
    /\ rw_cells usegs m' A5_3 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A6_2); C8 (Z_to_bv 64 A6_15)]
    /\ rw_cells usegs m' A6_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A6_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A6_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A6_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A6_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A6_2 [C8 (Z_to_bv 64 A6_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_4); C8 (Z_to_bv 64 A6_5); C8 (Z_to_bv 64 A6_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_7); C8 (Z_to_bv 64 A6_8); C8 (Z_to_bv 64 A6_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_10); C8 (Z_to_bv 64 A6_11); C8 (Z_to_bv 64 A6_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A6_13); C8 (Z_to_bv 64 A6_14)]
    /\ rw_cells usegs m' A6_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A8_2); C8 (Z_to_bv 64 A8_15)]
    /\ rw_cells usegs m' A8_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A8_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A8_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A8_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A8_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A8_2 [C8 (Z_to_bv 64 A8_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_4); C8 (Z_to_bv 64 A8_5); C8 (Z_to_bv 64 A8_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_7); C8 (Z_to_bv 64 A8_8); C8 (Z_to_bv 64 A8_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_10); C8 (Z_to_bv 64 A8_11); C8 (Z_to_bv 64 A8_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A8_13); C8 (Z_to_bv 64 A8_14)]
    /\ rw_cells usegs m' A8_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A9_2); C8 (Z_to_bv 64 A9_15)]
    /\ rw_cells usegs m' A9_14 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_13 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A9_11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A9_8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A9_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A9_3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells usegs m' A9_2 [C8 (Z_to_bv 64 A9_3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_4); C8 (Z_to_bv 64 A9_5); C8 (Z_to_bv 64 A9_6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_7); C8 (Z_to_bv 64 A9_8); C8 (Z_to_bv 64 A9_9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_10); C8 (Z_to_bv 64 A9_11); C8 (Z_to_bv 64 A9_12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 A9_13); C8 (Z_to_bv 64 A9_14)]
    /\ rw_cells usegs m' A9_15 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A10_1 [C8 (Z_to_bv 64 3333832); C8 (Z_to_bv 64 A10_2); C8 (Z_to_bv 64 A10_4); C8 (Z_to_bv 64 A10_3); C8 (Z_to_bv 64 A10_5); CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 (Z.lor (bv_unsigned (zxb (Z_to_bv 8 0))) 1)); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells usegs m' A10_4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1004432); C8 (Z_to_bv 64 1004308); C8 (Z_to_bv 64 1004476)]
    /\ rw_cells usegs m' A10_3 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A10_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 994472); C8 (Z_to_bv 64 1004348); C8 (Z_to_bv 64 1004268); C8 (Z_to_bv 64 1004392)]
    /\ rw_cells usegs m' A10_5 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A14_1 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells usegs m' A15_1 [CB 56 (repeat (Z_to_bv 8 0) 56)]
    /\ rw_cells usegs m' A16_1 [C8 (Z_to_bv 64 A16_2); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells usegs m' A16_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A17_1 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells usegs m' A18_1 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells usegs m' A19_1 [CB 16 (repeat (Z_to_bv 8 0) 16); C8 (Z_to_bv 64 A19_2); C8 (Z_to_bv 64 A19_3)]
    /\ rw_cells usegs m' A19_2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A19_3 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A20_1 [CB 88 (repeat (Z_to_bv 8 0) 88)]
    /\ rw_cells usegs m' A22_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2803492); C8 (Z_to_bv 64 2803608); C8 (Z_to_bv 64 2803692); C8 (Z_to_bv 64 2803652)]
    /\ rw_cells usegs m' 3334008 [C8 (Z_to_bv 64 A3_1); C8 (Z_to_bv 64 A10_1); C8 (Z_to_bv 64 A12_1); C8 (Z_to_bv 64 A13_1); C8 (Z_to_bv 64 A14_1); C8 (Z_to_bv 64 A5_1); C8 (Z_to_bv 64 A16_1); C8 (Z_to_bv 64 A4_1); C8 (Z_to_bv 64 A15_1); C8 (Z_to_bv 64 A20_1); C8 (Z_to_bv 64 A6_1); C8 (Z_to_bv 64 A7_1); C8 (Z_to_bv 64 A8_1); C8 (Z_to_bv 64 A9_1); C8 (Z_to_bv 64 A17_1); C8 (Z_to_bv 64 A18_1); C8 (Z_to_bv 64 A19_1); C8 (Z_to_bv 64 A22_1)]
    /\ rw_cells usegs m' 3334000 [C8 (Z_to_bv 64 A11_1)]
    /\ rw_cells usegs m' 3333840 [C8 (Z_to_bv 64 A2_1)]
    /\ rw_cells usegs m' 3333832 [C8 (Z_to_bv 64 A1_1)].

Definition context_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (x_2e82f0 : word)
         (x_2e8338 x_2e8340 x_2e83e0 x_2e83e8 : list byte)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
    (126 <= f)%nat ->
    croom L 119 6 83768 ->
    cstate st LBall LB L m sp tp lo B ->
    lo <= bv_unsigned sp - context_init_STACK ->
    bv_unsigned sp mod 16 = 0 ->
    a0 = Z_to_bv 64 0x32dec8 ->
    rw_cells usegs m 0x32de28 [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs m 0x32de40 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] ->
    rw_cells usegs m 0x32de80 [C8 x_2e82f0] ->
    rw_cells usegs m 0x32dec8 [CB 8 x_2e8338] ->
    rw_cells usegs m 0x32ded0 [CB 8 x_2e8340] ->
    rw_cells usegs m 0x32df70 [CB 8 x_2e83e0] ->
    rw_cells usegs m 0x32df78 [CB 144 x_2e83e8] ->
    rw_cells usegs m 0x351010 [C4 (Z_to_bv 64 0)] ->
    climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_G_context_init) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False)
             [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z 126 (119) (6) (83768) (context_init_res LBall L)).

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
Proof.
  intros ZAL PPI. intros until junk.
  intros LBc0 Lc0 LBc1 Lc1 LBc2 Lc2 LBc3 Lc3 LBc4 Lc4 LBc5 Lc5 LBc6 Lc6 LBc7 Lc7 LBc8 Lc8 LBc9 Lc9 LBc10 Lc10 LBc11 Lc11 LBc12 Lc12 LBc13 Lc13 LBc14 Lc14 LBc15 Lc15 LBc16 Lc16.
  intros SPB FU0 RM0 OW0 LOW AL16 CS16 CX78 CX70 CXd0 CXc8 FRM PSD FU16 GR16.
  intros OB1 OB2 OB3 OB4 OB5 OB6 OB7 OB8 OB9 OB10 OB11 OB12 OB13 OB14 OB15 OB16.
  intros SG0 SG1 SG3 SG4 SG5 SG6 SG7 SG8 SG9 SG10 SG11 SG12 SG13 SG14 SG15.
  intros CL1 CL2 CL3 CL4 CL5 CL6 CL7 CL8 CL9 CL10 CL11 CL12 CL13 CL14 CL15 CL16.

  pose proof ceil_window_holds as CEIL. unfold ceil_window in CEIL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof CS16 as (_ & _ & (_ & _ & _ & STK0 & GLO & _ & _ & _) & _). pose proof STK0 as (LO0 & _). clear STK0.
  assert (SPm : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  set (KP := PPK q11_1 q11_2 q11_3 q11_4 q11_5 q11_6 q11_7 q11_8 A11_1 A11_2 A11_3 A11_4 A11_5 A11_6 A11_7 A11_8) in PSD.
  pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CS16) as (ND16 & NDL16).
  assert (NPK : forall i qq, nth_error (map blk_id LBc16) i = Some qq ->
                 existsb (Nat.eqb i) [15;16;17;18;19;20;21;22]%nat = false -> ~ ppk_T KP qq).
  { intros i qq Hi Hex. unfold ppk_T.
    exact (wp_notin_pos (map blk_id LBc16) i qq [15;16;17;18;19;20;21;22]%nat (ppk_ids KP) ND16 Hi eq_refl Hex). }
  assert (XB : forall (T : bptr -> Prop) (W : list (Z * Z)) (SP : Z) (LBk : list block) (mk mk' : mem) (A n : Z) (cs : list cell) (qq : bptr),
                 cfr T W SP LBk mk mk' -> rw_cells usegs mk A cs -> In (qq, A, n) LBk -> ~ T qq ->
                 Z.of_nat (cells_size cs) <= n -> rw_cells usegs mk' A cs).
  { intros T W SP LBk mk mk' A n cs qq CF RW INb NT SZ.
    exact (cfr_cells_block T W SP LBk mk mk' A cs (qq, A, n) CF RW INb NT
             ltac:(cbn [blk_addr fst snd]; lia) ltac:(cbn [blk_addr blk_size fst snd]; lia)). }
  assert (CFW : forall (T : bptr -> Prop) (W W' : list (Z * Z)) (SP SP' : Z) (sa : PState) (LB0 : list block) (L0 : @clist bptr) (m0 : mem)
                       (sb : PState) (LB1 : list block) (L1 : @clist bptr) (m1 : mem),
                  SP' <= SP -> (forall a, rin_ivs W' a -> rin_ivs W a) ->
                  cframe (fun _ => False) W' SP' sa LB0 L0 m0 sb LB1 L1 m1 -> cframe T W SP sa LB0 L0 m0 sb LB1 L1 m1).
  { intros T W W' SP SP' sa LB0 L0 m0 sb LB1 L1 m1 HSP HW (AG & (K1 & K2) & E1 & E2).
    split; [| split; [split | split; assumption]].
    - eapply agree_on_mono; [exact AG|]. intros aa [HH|[(bb & Hb & _ & Hr)|(C1 & C2 & C3 & C4)]];
        [left; lia | right; left; exists bb; auto | right; right; split; [exact C1|]; split; [exact C2|]; split; [exact C3|]; intros X; apply C4; apply HW; exact X].
    - intros bb Hb _. exact (K1 bb Hb (fun X => X)).
    - intros qq nm Hq _. exact (K2 qq nm Hq (fun X => X)). }
  destruct OB1 as (I1_1 & B1_1).
  destruct OB2 as (I2_1 & B2_1).
  destruct OB3 as (I3_15 & I3_14 & I3_13 & I3_12 & I3_11 & I3_10 & I3_9 & I3_8 & I3_7 & I3_6 & I3_5 & I3_4 & I3_3 & I3_2 & I3_1 & B3_1 & B3_2 & B3_3 & B3_4 & B3_5 & B3_6 & B3_7 & B3_8 & B3_9 & B3_10 & B3_11 & B3_12 & B3_13 & B3_14 & B3_15).
  destruct OB4 as (I4_2 & I4_1 & B4_1 & B4_2).
  destruct OB5 as (I5_3 & I5_2 & I5_1 & B5_1 & B5_2 & B5_3).
  destruct OB6 as (I6_15 & I6_14 & I6_13 & I6_12 & I6_11 & I6_10 & I6_9 & I6_8 & I6_7 & I6_6 & I6_5 & I6_4 & I6_3 & I6_2 & I6_1 & B6_1 & B6_2 & B6_3 & B6_4 & B6_5 & B6_6 & B6_7 & B6_8 & B6_9 & B6_10 & B6_11 & B6_12 & B6_13 & B6_14 & B6_15).
  destruct OB7 as (I7_4 & I7_3 & I7_2 & I7_1).
  destruct OB8 as (I8_15 & I8_14 & I8_13 & I8_12 & I8_11 & I8_10 & I8_9 & I8_8 & I8_7 & I8_6 & I8_5 & I8_4 & I8_3 & I8_2 & I8_1 & B8_1 & B8_2 & B8_3 & B8_4 & B8_5 & B8_6 & B8_7 & B8_8 & B8_9 & B8_10 & B8_11 & B8_12 & B8_13 & B8_14 & B8_15).
  destruct OB9 as (I9_15 & I9_14 & I9_13 & I9_12 & I9_11 & I9_10 & I9_9 & I9_8 & I9_7 & I9_6 & I9_5 & I9_4 & I9_3 & I9_2 & I9_1 & B9_1 & B9_2 & B9_3 & B9_4 & B9_5 & B9_6 & B9_7 & B9_8 & B9_9 & B9_10 & B9_11 & B9_12 & B9_13 & B9_14 & B9_15).
  destruct OB10 as (I10_5 & I10_4 & I10_3 & I10_2 & I10_1 & B10_1 & B10_2 & B10_3 & B10_4 & B10_5).
  destruct OB11 as (I11_8 & I11_7 & I11_6 & I11_5 & I11_4 & I11_3 & I11_2 & I11_1).
  destruct OB12 as (I12_9 & I12_8 & I12_7 & I12_6 & I12_5 & I12_4 & I12_3 & I12_2 & I12_1).
  destruct OB13 as (I13_2 & I13_1).
  destruct OB14 as (I14_1 & B14_1).
  destruct OB15 as (I15_1 & B15_1).
  destruct OB16 as (I16_2 & I16_1 & B16_1 & B16_2).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CS16 I16_1) as RB16a. unfold rblock_range in RB16a.
  pose proof (cframe_refl (fun _ : bptr => False) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st16 LBc16 Lc16 mb16) as PF.
  pose proof GR16 as GR. clear GR16.
  pose proof CS16 as CSb.
  pose proof CSb as (HPc & _ & (evc & _ & _ & STKc & _ & _ & MIc & _) & _).
  match goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => pose proof (munch_refl [(3334056, 3334056+8)] mm) as MUc; pose proof (wmono_refl usegs mm) as WMc end.
  apply climpl_from_evt.
  step.
  step. if_cases NZ; [exfalso; zify_cond NZ; lia | clear NZ].
  step.
  step.
  apply evt_done; cbv beta.
  pose proof (cstate_seg _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned sp + -32)) _ _ _ B CSb MUc WMc MIc
                ltac:(constructor; [apply cwin_bss; lia | constructor]) ltac:(lia) ltac:(lia)
                ltac:(cbn [disjoint_from]; unfold LX_FLAGS; split; [lia | exact I]) STKc ltac:(rewrite SPm; lia)) as CSa.
  pose proof (cframe_seg _ _ _ _ _ _ _ _ _ _ _ _ _ PF MUc WMc HPc ltac:(lia)
                ltac:(constructor; [apply cseg_ok_static; [lia | lia | intros aa Ha; cbn [rin_ivs fst snd]; lia] | constructor])) as PFn.
  clear PF MUc WMc CSb; rename PFn into PF.
  eapply climpl_seq.
  { eapply (ossl_self_test_set_callback_new_spec ZAL).
    - lia.
    - change (wA 16) with 1. change (wB 16) with 0. change (wBig 16) with 0.
      destruct RM0 as (RA & RB & RC); destruct GR as (GA & GB & GC); split; [lia | split; lia].
    - exact CSa.
    - rewrite SPm. unfold ossl_self_test_set_callback_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK. lia. }
  intros f17 L17 s17 ms17 PO17.
  destruct PO17 as (v17 & m17 & LB17 & RT17 & FF17 & GG17 & CSn & FR17 & RS17).
  destruct RT17 as (t0x_17 & t1x_17 & t2x_17 & a1x_17 & a2x_17 & a3x_17 & a4x_17 & a5x_17 & a6x_17 & a7x_17 & t3x_17 & t4x_17 & t5x_17 & t6x_17 & ->).
  destruct RS17 as (q17_1 & A17_1 & -> & -> & -> & RB17 & Z17).
  unfold rblock_range in RB17.
  rewrite SPm in FR17. pose proof FR17 as (CF17 & _).
  cst_static CF17 CX78 CX78n. cst_static CF17 CX70 CX70n. cst_static CF17 CXd0 CXd0n. cst_static CF17 CXc8 CXc8n.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CF17 FRM ltac:(lia)) as FRMn.
  clear CX78 CX70 CXd0 CXc8 FRM MIc STKc HPc evc CF17 CSa.
  rename CX78n into CX78; rename CX70n into CX70; rename CXd0n into CXd0; rename CXc8n into CXc8; rename FRMn into FRM.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PF FR17 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as PFn.
  clear PF FR17; rename PFn into PF; rename CSn into CSb.
  pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR GG17) as GRn. clear GR GG17; rename GRn into GR.
  change (93 + wA 16) with 94 in GR. change (6 + wB 16) with 6 in GR. change (83768 + wBig 16) with 83768 in GR.
  cret_lit.
  pose proof CSb as (HPc & _ & (evc & _ & _ & STKc & _ & _ & MIc & _) & _).
  match goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => pose proof (munch_refl [(3334120, 3334120+8)] mm) as MUc; pose proof (wmono_refl usegs mm) as WMc end.
  apply climpl_from_evt.
  step.
  step. if_cases NZ; [exfalso; zify_cond NZ; lia | clear NZ].
  step.
  step.
  apply evt_done; cbv beta.
  pose proof (cstate_seg _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned sp + -32)) _ _ _ B CSb MUc WMc MIc
                ltac:(constructor; [apply cwin_bss; lia | constructor]) ltac:(lia) ltac:(lia)
                ltac:(cbn [disjoint_from]; unfold LX_FLAGS; split; [lia | exact I]) STKc ltac:(rewrite SPm; lia)) as CSa.
  pose proof (cframe_seg _ _ _ _ _ _ _ _ _ _ _ _ _ PF MUc WMc HPc ltac:(lia)
                ltac:(constructor; [apply cseg_ok_static; [lia | lia | intros aa Ha; cbn [rin_ivs fst snd]; lia] | constructor])) as PFn.
  clear PF MUc WMc CSb; rename PFn into PF.
  eapply climpl_seq.
  { eapply (ossl_indicator_set_callback_new_spec ZAL).
    - lia.
    - change (wA 8) with 1. change (wB 8) with 0. change (wBig 8) with 0.
      destruct RM0 as (RA & RB & RC); destruct GR as (GA & GB & GC); split; [lia | split; lia].
    - exact CSa.
    - rewrite SPm. unfold ossl_indicator_set_callback_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK. lia. }
  intros f18 L18 s18 ms18 PO18.
  destruct PO18 as (v18 & m18 & LB18 & RT18 & FF18 & GG18 & CSn & FR18 & RS18).
  destruct RT18 as (t0x_18 & t1x_18 & t2x_18 & a1x_18 & a2x_18 & a3x_18 & a4x_18 & a5x_18 & a6x_18 & a7x_18 & t3x_18 & t4x_18 & t5x_18 & t6x_18 & ->).
  destruct RS18 as (q18_1 & A18_1 & -> & -> & -> & RB18 & Z18).
  unfold rblock_range in RB18.
  rewrite SPm in FR18. pose proof FR18 as (CF18 & _).
  cst_static CF18 CX78 CX78n. cst_static CF18 CX70 CX70n. cst_static CF18 CXd0 CXd0n. cst_static CF18 CXc8 CXc8n.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CF18 FRM ltac:(lia)) as FRMn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF18 Z17 ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z17n.
  clear Z17; rename Z17n into Z17.
  clear CX78 CX70 CXd0 CXc8 FRM MIc STKc HPc evc CF18 CSa.
  rename CX78n into CX78; rename CX70n into CX70; rename CXd0n into CXd0; rename CXc8n into CXc8; rename FRMn into FRM.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PF FR18 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as PFn.
  clear PF FR18; rename PFn into PF; rename CSn into CSb.
  pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR GG18) as GRn. clear GR GG18; rename GRn into GR.
  change (94 + wA 8) with 95 in GR. change (6 + wB 8) with 6 in GR. change (83768 + wBig 8) with 83768 in GR.
  cret_lit.
  pose proof CSb as (HPc & _ & (evc & _ & _ & STKc & _ & _ & MIc & _) & _).
  match goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => pose proof (munch_refl [(3334128, 3334128+8)] mm) as MUc; pose proof (wmono_refl usegs mm) as WMc end.
  apply climpl_from_evt.
  step.
  step. if_cases NZ; [exfalso; zify_cond NZ; lia | clear NZ].
  step.
  step.
  apply evt_done; cbv beta.
  pose proof (cstate_seg _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned sp + -32)) _ _ _ B CSb MUc WMc MIc
                ltac:(constructor; [apply cwin_bss; lia | constructor]) ltac:(lia) ltac:(lia)
                ltac:(cbn [disjoint_from]; unfold LX_FLAGS; split; [lia | exact I]) STKc ltac:(rewrite SPm; lia)) as CSa.
  pose proof (cframe_seg _ _ _ _ _ _ _ _ _ _ _ _ _ PF MUc WMc HPc ltac:(lia)
                ltac:(constructor; [apply cseg_ok_static; [lia | lia | intros aa Ha; cbn [rin_ivs fst snd]; lia] | constructor])) as PFn.
  clear PF MUc WMc CSb; rename PFn into PF.
  eapply climpl_seq.
  { eapply (ossl_threads_ctx_new_spec ZAL).
    - lia.
    - change (wA 32 + wA 40 + wA 48) with 3. change (wB 32 + wB 40 + wB 48) with 0. change (wBig 32 + wBig 40 + wBig 48) with 0.
      destruct RM0 as (RA & RB & RC); destruct GR as (GA & GB & GC); split; [lia | split; lia].
    - exact CSa.
    - rewrite SPm. unfold ossl_threads_ctx_new_STACK, ossl_crypto_mutex_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK. lia. }
  intros f19 L19 s19 ms19 PO19.
  destruct PO19 as (v19 & m19 & LB19 & RT19 & FF19 & GG19 & CSn & FR19 & RS19).
  destruct RT19 as (t0x_19 & t1x_19 & t2x_19 & a1x_19 & a2x_19 & a3x_19 & a4x_19 & a5x_19 & a6x_19 & a7x_19 & t3x_19 & t4x_19 & t5x_19 & t6x_19 & ->).
  destruct RS19 as (q19_1 & A19_1 & q19_2 & A19_2 & q19_3 & A19_3 & -> & -> & -> & RB19a & RB19b & RB19c & Z19a & Z19b & Z19c).
  unfold rblock_range in RB19a, RB19b, RB19c.
  rewrite SPm in FR19. pose proof FR19 as (CF19 & _).
  cst_static CF19 CX78 CX78n. cst_static CF19 CX70 CX70n. cst_static CF19 CXd0 CXd0n. cst_static CF19 CXc8 CXc8n.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CF19 FRM ltac:(lia)) as FRMn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF19 Z17 ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z17n.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF19 Z18 ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z18n.
  clear Z17 Z18; rename Z17n into Z17; rename Z18n into Z18.
  clear CX78 CX70 CXd0 CXc8 FRM MIc STKc HPc evc CF19 CSa.
  rename CX78n into CX78; rename CX70n into CX70; rename CXd0n into CXd0; rename CXc8n into CXc8; rename FRMn into FRM.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PF FR19 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as PFn.
  clear PF FR19; rename PFn into PF; rename CSn into CSb.
  pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR GG19) as GRn. clear GR GG19; rename GRn into GR.
  change (95 + (wA 32 + wA 40 + wA 48)) with 98 in GR. change (6 + (wB 32 + wB 40 + wB 48)) with 6 in GR. change (83768 + (wBig 32 + wBig 40 + wBig 48)) with 83768 in GR.
  cret_lit.
  pose proof CSb as (HPc & _ & (evc & _ & _ & STKc & _ & _ & MIc & _) & _).
  match goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => pose proof (munch_refl [(3334136, 3334136+8)] mm) as MUc; pose proof (wmono_refl usegs mm) as WMc end.
  apply climpl_from_evt.
  step.
  step. if_cases NZ; [exfalso; zify_cond NZ; lia | clear NZ].
  step.
  step.
  apply evt_done; cbv beta.
  pose proof (cstate_seg _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned sp + -32)) _ _ _ B CSb MUc WMc MIc
                ltac:(constructor; [apply cwin_bss; lia | constructor]) ltac:(lia) ltac:(lia)
                ltac:(cbn [disjoint_from]; unfold LX_FLAGS; split; [lia | exact I]) STKc ltac:(rewrite SPm; lia)) as CSa.
  pose proof (cframe_seg _ _ _ _ _ _ _ _ _ _ _ _ _ PF MUc WMc HPc ltac:(lia)
                ltac:(constructor; [apply cseg_ok_static; [lia | lia | intros aa Ha; cbn [rin_ivs fst snd]; lia] | constructor])) as PFn.
  clear PF MUc WMc CSb; rename PFn into PF.
  eapply climpl_seq.
  { eapply (ossl_child_prov_ctx_new_spec ZAL).
    - lia.
    - change (wA 88) with 1. change (wB 88) with 0. change (wBig 88) with 0.
      destruct RM0 as (RA & RB & RC); destruct GR as (GA & GB & GC); split; [lia | split; lia].
    - exact CSa.
    - rewrite SPm. unfold ossl_child_prov_ctx_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK. lia. }
  intros f20 L20 s20 ms20 PO20.
  destruct PO20 as (v20 & m20 & LB20 & RT20 & FF20 & GG20 & CSn & FR20 & RS20).
  destruct RT20 as (t0x_20 & t1x_20 & t2x_20 & a1x_20 & a2x_20 & a3x_20 & a4x_20 & a5x_20 & a6x_20 & a7x_20 & t3x_20 & t4x_20 & t5x_20 & t6x_20 & ->).
  destruct RS20 as (q20_1 & A20_1 & -> & -> & -> & RB20 & Z20).
  unfold rblock_range in RB20.
  rewrite SPm in FR20. pose proof FR20 as (CF20 & _).
  cst_static CF20 CX78 CX78n. cst_static CF20 CX70 CX70n. cst_static CF20 CXd0 CXd0n. cst_static CF20 CXc8 CXc8n.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CF20 FRM ltac:(lia)) as FRMn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF20 Z17 ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z17n.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF20 Z18 ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z18n.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF20 Z19a ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19an.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF20 Z19b ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19bn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF20 Z19c ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19cn.
  clear Z17 Z18 Z19a Z19b Z19c; rename Z17n into Z17; rename Z18n into Z18; rename Z19an into Z19a; rename Z19bn into Z19b; rename Z19cn into Z19c.
  clear CX78 CX70 CXd0 CXc8 FRM MIc STKc HPc evc CF20 CSa.
  rename CX78n into CX78; rename CX70n into CX70; rename CXd0n into CXd0; rename CXc8n into CXc8; rename FRMn into FRM.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PF FR20 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as PFn.
  clear PF FR20; rename PFn into PF; rename CSn into CSb.
  pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR GG20) as GRn. clear GR GG20; rename GRn into GR.
  change (98 + wA 88) with 99 in GR. change (6 + wB 88) with 6 in GR. change (83768 + wBig 88) with 83768 in GR.
  cret_lit.
  pose proof CSb as (HPc & _ & (evc & _ & _ & STKc & _ & _ & MIc & _) & _).
  match goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => pose proof (munch_refl [(3334080, 3334080+8)] mm) as MUc; pose proof (wmono_refl usegs mm) as WMc end.
  apply climpl_from_evt.
  step.
  step. if_cases NZ; [exfalso; zify_cond NZ; lia | clear NZ].
  step.
  step.
  apply evt_done; cbv beta.
  pose proof (cstate_seg _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned sp + -32)) _ _ _ B CSb MUc WMc MIc
                ltac:(constructor; [apply cwin_bss; lia | constructor]) ltac:(lia) ltac:(lia)
                ltac:(cbn [disjoint_from]; unfold LX_FLAGS; split; [lia | exact I]) STKc ltac:(rewrite SPm; lia)) as CSa.
  pose proof (cframe_seg _ _ _ _ _ _ _ _ _ _ _ _ _ PF MUc WMc HPc ltac:(lia)
                ltac:(constructor; [apply cseg_ok_static; [lia | lia | intros aa Ha; cbn [rin_ivs fst snd]; lia] | constructor])) as PFn.
  clear PF MUc WMc CSb; rename PFn into PF.
  pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CSa) as (ND20 & _).
  assert (NPK2 : forall i qq, nth_error (map blk_id ((q20_1, A20_1, 88) :: (q19_3, A19_3, 48) :: (q19_2, A19_2, 40)
                                 :: (q19_1, A19_1, 32) :: (q18_1, A18_1, 8) :: (q17_1, A17_1, 16) :: LBc16)) i = Some qq ->
                 existsb (Nat.eqb i) [21;22;23;24;25;26;27;28]%nat = false -> ~ ppk_T KP qq).
  { intros i qq Hi Hex. unfold ppk_T.
    exact (wp_notin_pos _ i qq [21;22;23;24;25;26;27;28]%nat (ppk_ids KP) ND20 Hi eq_refl Hex). }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ PSD PF ltac:(intros qq _ [])) as PSDc.
  pose proof PPI as PPIu. unfold ossl_property_parse_init_fp_stmt in PPIu.
  eapply climpl_seq.
  { eapply PPIu with (KP := KP).
    - unfold PPI_EV. lia.
    - change PPI_NA with 19.
      destruct RM0 as (RA & RB & RC); destruct GR as (GA & GB & GC); split; [lia | split; lia].
    - exact CSa.
    - rewrite SPm. unfold PPI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK. lia.
    - rewrite SPm. lia.
    - unfold CTX_A. reflexivity.
    - exact CX70.
    - exact PSDc. }
  intros f21 L21 s21 ms21 PO21.
  destruct PO21 as (v21 & m21 & LB21 & RT21 & FF21 & GG21 & CSn & FR21 & RS21).
  destruct RT21 as (t0x_21 & t1x_21 & t2x_21 & a1x_21 & a2x_21 & a3x_21 & a4x_21 & a5x_21 & a6x_21 & a7x_21 & t3x_21 & t4x_21 & t5x_21 & t6x_21 & ->).
  destruct RS21 as (q21_1 & q21_2 & q21_3 & q21_4 & q21_5 & q21_6 & q21_7 & q21_8 & q21_9 & q21_10 & q21_11 & q21_12 & q21_13 & q21_14 & q21_15 & q21_16 & q21_17 & q21_18 & A21_1 & A21_2 & A21_3 & A21_4 & A21_5 & A21_6 & A21_7 & A21_8 & A21_9 & A21_10 & A21_11 & A21_12 & A21_13 & A21_14 & A21_15 & A21_16 & A21_17 & A21_18 & -> & -> & RB21_1 & RB21_2 & RB21_3 & RB21_4 & RB21_5 & RB21_6 & RB21_7 & RB21_8 & RB21_9 & RB21_10 & RB21_11 & RB21_12 & RB21_13 & RB21_14 & RB21_15 & RB21_16 & RB21_17 & RB21_18).
  rewrite SPm in FR21. pose proof FR21 as (CF21 & _).
  cst_static CF21 CX78 CX78n. cst_static CF21 CX70 CX70n. cst_static CF21 CXd0 CXd0n. cst_static CF21 CXc8 CXc8n.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CF21 FRM ltac:(lia)) as FRMn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF21 Z17 ltac:(wp_in_lit) ltac:(apply (NPK2 5%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z17n.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF21 Z18 ltac:(wp_in_lit) ltac:(apply (NPK2 4%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z18n.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF21 Z19a ltac:(wp_in_lit) ltac:(apply (NPK2 3%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19an.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF21 Z19b ltac:(wp_in_lit) ltac:(apply (NPK2 2%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19bn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF21 Z19c ltac:(wp_in_lit) ltac:(apply (NPK2 1%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19cn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF21 Z20 ltac:(wp_in_lit) ltac:(apply (NPK2 0%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z20n.
  clear Z17 Z18 Z19a Z19b Z19c Z20; rename Z17n into Z17; rename Z18n into Z18; rename Z19an into Z19a; rename Z19bn into Z19b; rename Z19cn into Z19c; rename Z20n into Z20.
  clear CX78 CX70 CXd0 CXc8 FRM MIc STKc HPc evc CF21 CSa.
  rename CX78n into CX78; rename CX70n into CX70; rename CXd0n into CXd0; rename CXc8n into CXc8; rename FRMn into FRM.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (CFW (ppk_T KP) _ _ (bv_unsigned sp) (bv_unsigned sp) _ _ _ _ _ _ _ _ ltac:(lia) ltac:(intros aa HH; exact HH) PF) FR21
                ltac:(lia) ltac:(intros aa []) ltac:(intros qq _ HH; exact HH)) as PFn.
  clear PF FR21; rename PFn into PF; rename CSn into CSb.
  pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR GG21) as GRn. clear GR GG21; rename GRn into GR.
  change (99 + PPI_NA) with 118 in GR. change (6 + 0) with 6 in GR. change (83768 + 0) with 83768 in GR.
  unfold PPI_EV in FF21.
  cret_lit.
  pose proof CSb as (HPc & _ & (evc & _ & _ & STKc & _ & _ & MIc & _) & _).
  apply climpl_from_evt.
  step. if_cases NZ; [exfalso; zify_cond NZ; lia | clear NZ].
  step.
  apply evt_done; cbv beta.
  pose proof CSb as CSa. clear CSb.
  eapply climpl_seq.
  { eapply (ossl_load_builtin_compressions_spec ZAL).
    - lia.
    - change (wA 56) with 1. change (wB 56) with 0. change (wBig 56) with 0.
      destruct RM0 as (RA & RB & RC); destruct GR as (GA & GB & GC); split; [lia | split; lia].
    - exact CSa.
    - rewrite SPm. unfold ossl_load_builtin_compressions_STACK, OPENSSL_sk_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK. lia. }
  intros f22 L22 s22 ms22 PO22.
  destruct PO22 as (v22 & m22 & LB22 & RT22 & FF22 & GG22 & CSn & FR22 & RS22).
  destruct RT22 as (t0x_22 & t1x_22 & t2x_22 & a1x_22 & a2x_22 & a3x_22 & a4x_22 & a5x_22 & a6x_22 & a7x_22 & t3x_22 & t4x_22 & t5x_22 & t6x_22 & ->).
  destruct RS22 as (q22_1 & A22_1 & -> & -> & -> & RB22 & Z22).
  unfold rblock_range in RB22.
  rewrite SPm in FR22. pose proof FR22 as (CF22 & _).
  cst_static CF22 CX78 CX78n. cst_static CF22 CX70 CX70n. cst_static CF22 CXd0 CXd0n. cst_static CF22 CXc8 CXc8n.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CF22 FRM ltac:(lia)) as FRMn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF22 Z17 ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z17n.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF22 Z18 ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z18n.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF22 Z19a ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19an.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF22 Z19b ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19bn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF22 Z19c ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z19cn.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ CF22 Z20 ltac:(wp_in_lit) ltac:(intros []) ltac:(cbn [cells_size csize Nat.add]; lia)) as Z20n.
  clear Z17 Z18 Z19a Z19b Z19c Z20; rename Z17n into Z17; rename Z18n into Z18; rename Z19an into Z19a; rename Z19bn into Z19b; rename Z19cn into Z19c; rename Z20n into Z20.
  clear CX78 CX70 CXd0 CXc8 FRM MIc STKc HPc evc CF22 CSa.
  rename CX78n into CX78; rename CX70n into CX70; rename CXd0n into CXd0; rename CXc8n into CXc8; rename FRMn into FRM.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PF FR22 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as PFn.
  clear PF FR22; rename PFn into PF; rename CSn into CSb.
  pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR GG22) as GRn. clear GR GG22; rename GRn into GR.
  change (118 + wA 56) with 119 in GR. change (6 + wB 56) with 6 in GR. change (83768 + wBig 56) with 83768 in GR.
  cret_lit.
  pose proof CSb as (HPc & _ & (evc & _ & _ & STKc & _ & _ & MIc & _) & _).
  match goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => pose proof (munch_refl [(3334144, 3334144+8)] mm) as MUc; pose proof (wmono_refl usegs mm) as WMc end.
  apply climpl_from_evt.
  step. step. step. step. step. step. step. step.
  apply evt_done; cbv beta.
  pose proof (cframe_seg _ _ _ _ _ _ _ _ _ _ _ _ _ PF MUc WMc HPc ltac:(lia)
                ltac:(constructor; [apply cseg_ok_static; [lia | lia | intros aa Ha; cbn [rin_ivs fst snd]; lia] | constructor])) as PFn.
  clear PF; rename PFn into PF.
  rewrite SPm in STKc.
  pose proof (stk_release usegs _ lo (bv_unsigned sp + -32) _ STKc FRM ltac:(lia)) as STKsp.
  cbn [cells_size csize Nat.add] in STKsp.
  replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) in STKsp by lia.
  pose proof (cstate_seg _ _ _ _ _ _ _ _ sp _ _ _ B CSb MUc WMc MIc
                ltac:(constructor; [apply cwin_bss; lia | constructor]) ltac:(lia) ltac:(lia)
                ltac:(cbn [disjoint_from]; unfold LX_FLAGS; split; [lia | exact I]) STKsp SPB) as CSfin.
  pose proof PF as S16.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG15 (ppk_T KP)) CL16 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S15a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S15a S16 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S15x. clear S15a. rename S15x into S15.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG14 (ppk_T KP)) CL15 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S14a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S14a S15 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S14x. clear S14a. rename S14x into S14.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG13 (ppk_T KP)) CL14 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S13a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S13a S14 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S13x. clear S13a. rename S13x into S13.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG12 (ppk_T KP)) CL13 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S12a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S12a S13 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S12x. clear S12a. rename S12x into S12.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG11 (ppk_T KP)) CL12 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S11a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S11a S12 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S11x. clear S11a. rename S11x into S11.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG10 (ppk_T KP)) CL11 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S10a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S10a S11 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S10x. clear S10a. rename S10x into S10.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG9 (ppk_T KP)) CL10 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S9a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S9a S10 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S9x. clear S9a. rename S9x into S9.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG8 (ppk_T KP)) CL9 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S8a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S8a S9 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S8x. clear S8a. rename S8x into S8.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG7 (ppk_T KP)) CL8 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S7a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S7a S8 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S7x. clear S7a. rename S7x into S7.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG6 (ppk_T KP)) CL7 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S6a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S6a S7 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S6x. clear S6a. rename S6x into S6.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG5 (ppk_T KP)) CL6 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S5a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S5a S6 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S5x. clear S5a. rename S5x into S5.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG4 (ppk_T KP)) CL5 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S4a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S4a S5 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S4x. clear S4a. rename S4x into S4.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG3 (ppk_T KP)) CL4 ltac:(lia) ltac:(intros aa [])
                ltac:(intros qq _ _ [])) as S3a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S3a S4 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S3x. clear S3a. rename S3x into S3.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                (CFW (ppk_T KP) [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z [] (bv_unsigned sp) (bv_unsigned sp + -32) _ _ _ _ _ _ _ _ ltac:(lia) ltac:(intros aa []) CL3) S3
                ltac:(lia) ltac:(intros aa HH; exact HH) ltac:(intros qq _ HH; exact HH)) as S2.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG1 (ppk_T KP)) CL2 ltac:(lia) ltac:(intros aa HH; cbn [rin_ivs fst snd] in HH |- *; lia)
                ltac:(intros qq _ _ [])) as S1a.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S1a S2 ltac:(lia) ltac:(intros aa HH; exact HH)
                ltac:(intros qq _ HH; exact HH)) as S1x. clear S1a. rename S1x into S1.
  assert (PRE : LBc16 = [(q16_2, A16_2, 40); (q16_1, A16_1, 16); (q15_1, A15_1, 56); (q14_1, A14_1, 16); (q13_2, A13_2, 128); (q13_1, A13_1, 104); (q12_9, A12_9, 56); (q12_8, A12_8, 16); (q12_7, A12_7, 264); (q12_6, A12_6, 32768); (q12_5, A12_5, 24); (q12_4, A12_4, 40); (q12_3, A12_3, 96); (q12_2, A12_2, 40); (q12_1, A12_1, 40); (q11_8, A11_8, 56); (q11_7, A11_7, 56); (q11_6, A11_6, 128); (q11_5, A11_5, 104); (q11_4, A11_4, 128); (q11_3, A11_3, 104); (q11_2, A11_2, 40); (q11_1, A11_1, 48); (q10_5, A10_5, 40); (q10_4, A10_4, 56); (q10_3, A10_3, 40); (q10_2, A10_2, 56); (q10_1, A10_1, 80); (q9_15, A9_15, 40); (q9_14, A9_14, 40); (q9_13, A9_13, 40); (q9_12, A9_12, 32); (q9_11, A9_11, 40); (q9_10, A9_10, 40); (q9_9, A9_9, 32); (q9_8, A9_8, 40); (q9_7, A9_7, 40); (q9_6, A9_6, 32); (q9_5, A9_5, 40); (q9_4, A9_4, 40); (q9_3, A9_3, 32); (q9_2, A9_2, 384); (q9_1, A9_1, 24); (q8_15, A8_15, 40); (q8_14, A8_14, 40); (q8_13, A8_13, 40); (q8_12, A8_12, 32); (q8_11, A8_11, 40); (q8_10, A8_10, 40); (q8_9, A8_9, 32); (q8_8, A8_8, 40); (q8_7, A8_7, 40); (q8_6, A8_6, 32); (q8_5, A8_5, 40); (q8_4, A8_4, 40); (q8_3, A8_3, 32); (q8_2, A8_2, 384); (q8_1, A8_1, 24); (q7_4, A7_4, 128); (q7_3, A7_3, 104); (q7_2, A7_2, 40); (q7_1, A7_1, 16); (q6_15, A6_15, 40); (q6_14, A6_14, 40); (q6_13, A6_13, 40); (q6_12, A6_12, 32); (q6_11, A6_11, 40); (q6_10, A6_10, 40); (q6_9, A6_9, 32); (q6_8, A6_8, 40); (q6_7, A6_7, 40); (q6_6, A6_6, 32); (q6_5, A6_5, 40); (q6_4, A6_4, 40); (q6_3, A6_3, 32); (q6_2, A6_2, 384); (q6_1, A6_1, 24); (q5_3, A5_3, 40); (q5_2, A5_2, 5); (q5_1, A5_1, 88); (q4_2, A4_2, 40); (q4_1, A4_1, 16); (q3_15, A3_15, 40); (q3_14, A3_14, 40); (q3_13, A3_13, 40); (q3_12, A3_12, 32); (q3_11, A3_11, 40); (q3_10, A3_10, 40); (q3_9, A3_9, 32); (q3_8, A3_8, 40); (q3_7, A3_7, 40); (q3_6, A3_6, 32); (q3_5, A3_5, 40); (q3_4, A3_4, 40); (q3_3, A3_3, 32); (q3_2, A3_2, 384); (q3_1, A3_1, 24); (q2_1, A2_1, 40); (q1_1, A1_1, 40)] ++ LBall) by reflexivity.
  pose proof (cstate_fresh_ids st16 [(q16_2, A16_2, 40); (q16_1, A16_1, 16); (q15_1, A15_1, 56); (q14_1, A14_1, 16); (q13_2, A13_2, 128); (q13_1, A13_1, 104); (q12_9, A12_9, 56); (q12_8, A12_8, 16); (q12_7, A12_7, 264); (q12_6, A12_6, 32768); (q12_5, A12_5, 24); (q12_4, A12_4, 40); (q12_3, A12_3, 96); (q12_2, A12_2, 40); (q12_1, A12_1, 40); (q11_8, A11_8, 56); (q11_7, A11_7, 56); (q11_6, A11_6, 128); (q11_5, A11_5, 104); (q11_4, A11_4, 128); (q11_3, A11_3, 104); (q11_2, A11_2, 40); (q11_1, A11_1, 48); (q10_5, A10_5, 40); (q10_4, A10_4, 56); (q10_3, A10_3, 40); (q10_2, A10_2, 56); (q10_1, A10_1, 80); (q9_15, A9_15, 40); (q9_14, A9_14, 40); (q9_13, A9_13, 40); (q9_12, A9_12, 32); (q9_11, A9_11, 40); (q9_10, A9_10, 40); (q9_9, A9_9, 32); (q9_8, A9_8, 40); (q9_7, A9_7, 40); (q9_6, A9_6, 32); (q9_5, A9_5, 40); (q9_4, A9_4, 40); (q9_3, A9_3, 32); (q9_2, A9_2, 384); (q9_1, A9_1, 24); (q8_15, A8_15, 40); (q8_14, A8_14, 40); (q8_13, A8_13, 40); (q8_12, A8_12, 32); (q8_11, A8_11, 40); (q8_10, A8_10, 40); (q8_9, A8_9, 32); (q8_8, A8_8, 40); (q8_7, A8_7, 40); (q8_6, A8_6, 32); (q8_5, A8_5, 40); (q8_4, A8_4, 40); (q8_3, A8_3, 32); (q8_2, A8_2, 384); (q8_1, A8_1, 24); (q7_4, A7_4, 128); (q7_3, A7_3, 104); (q7_2, A7_2, 40); (q7_1, A7_1, 16); (q6_15, A6_15, 40); (q6_14, A6_14, 40); (q6_13, A6_13, 40); (q6_12, A6_12, 32); (q6_11, A6_11, 40); (q6_10, A6_10, 40); (q6_9, A6_9, 32); (q6_8, A6_8, 40); (q6_7, A6_7, 40); (q6_6, A6_6, 32); (q6_5, A6_5, 40); (q6_4, A6_4, 40); (q6_3, A6_3, 32); (q6_2, A6_2, 384); (q6_1, A6_1, 24); (q5_3, A5_3, 40); (q5_2, A5_2, 5); (q5_1, A5_1, 88); (q4_2, A4_2, 40); (q4_1, A4_1, 16); (q3_15, A3_15, 40); (q3_14, A3_14, 40); (q3_13, A3_13, 40); (q3_12, A3_12, 32); (q3_11, A3_11, 40); (q3_10, A3_10, 40); (q3_9, A3_9, 32); (q3_8, A3_8, 40); (q3_7, A3_7, 40); (q3_6, A3_6, 32); (q3_5, A3_5, 40); (q3_4, A3_4, 40); (q3_3, A3_3, 32); (q3_2, A3_2, 384); (q3_1, A3_1, 24); (q2_1, A2_1, 40); (q1_1, A1_1, 40)] LBall LB L Lc16 mb16 _ tp lo B
                ltac:(rewrite <- PRE; exact CS16) OW0) as FRESH0.
  assert (FRESH : forall qq : bptr, In qq (map blk_id LBall) \/ In qq (map fst L) -> ~ (fun _ : bptr => False) qq -> ~ ppk_T KP qq).
  { intros qq HQ _ HIn. unfold ppk_T, ppk_ids in HIn. cbn [k_ps k_pk k_pl1 k_pb1 k_pl2 k_pb2 k_pq1 k_pq2] in HIn.
    cbn [In] in HIn.
    destruct HIn as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]];
      [ exact (FRESH0 (q11_8, A11_8, 56) ltac:(wp_in_lit) qq HQ (eq_sym E))
      | exact (FRESH0 (q11_7, A11_7, 56) ltac:(wp_in_lit) qq HQ (eq_sym E))
      | exact (FRESH0 (q11_6, A11_6, 128) ltac:(wp_in_lit) qq HQ (eq_sym E))
      | exact (FRESH0 (q11_5, A11_5, 104) ltac:(wp_in_lit) qq HQ (eq_sym E))
      | exact (FRESH0 (q11_4, A11_4, 128) ltac:(wp_in_lit) qq HQ (eq_sym E))
      | exact (FRESH0 (q11_3, A11_3, 104) ltac:(wp_in_lit) qq HQ (eq_sym E))
      | exact (FRESH0 (q11_2, A11_2, 40) ltac:(wp_in_lit) qq HQ (eq_sym E))
      | exact (FRESH0 (q11_1, A11_1, 48) ltac:(wp_in_lit) qq HQ (eq_sym E)) ]. }
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SG0 (fun _ : bptr => False)) CL1 ltac:(lia)
                ltac:(intros aa []) ltac:(intros qq _ _ [])) as FIN0.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIN0 S1 ltac:(lia) ltac:(intros aa HH; exact HH) FRESH) as FIN.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S1) B1_1 I1_1 ltac:(apply (NPK 98%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R1_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S2) B2_1 I2_1 ltac:(apply (NPK 97%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R2_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_1 I3_1 ltac:(apply (NPK 96%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_2 I3_14 ltac:(apply (NPK 83%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_2.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_3 I3_13 ltac:(apply (NPK 84%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_3.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_4 I3_12 ltac:(apply (NPK 85%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_4.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_5 I3_11 ltac:(apply (NPK 86%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_5.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_6 I3_10 ltac:(apply (NPK 87%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_6.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_7 I3_9 ltac:(apply (NPK 88%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_7.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_8 I3_8 ltac:(apply (NPK 89%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_8.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_9 I3_7 ltac:(apply (NPK 90%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_9.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_10 I3_6 ltac:(apply (NPK 91%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_10.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_11 I3_5 ltac:(apply (NPK 92%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_11.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_12 I3_4 ltac:(apply (NPK 93%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_12.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_13 I3_3 ltac:(apply (NPK 94%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_13.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_14 I3_2 ltac:(apply (NPK 95%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_14.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S3) B3_15 I3_15 ltac:(apply (NPK 82%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R3_15.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S4) B4_1 I4_1 ltac:(apply (NPK 81%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R4_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S4) B4_2 I4_2 ltac:(apply (NPK 80%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R4_2.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S5) B5_1 I5_1 ltac:(apply (NPK 79%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R5_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S5) B5_2 I5_2 ltac:(apply (NPK 78%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R5_2.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S5) B5_3 I5_3 ltac:(apply (NPK 77%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R5_3.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_1 I6_1 ltac:(apply (NPK 76%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_2 I6_14 ltac:(apply (NPK 63%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_2.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_3 I6_13 ltac:(apply (NPK 64%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_3.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_4 I6_12 ltac:(apply (NPK 65%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_4.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_5 I6_11 ltac:(apply (NPK 66%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_5.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_6 I6_10 ltac:(apply (NPK 67%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_6.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_7 I6_9 ltac:(apply (NPK 68%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_7.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_8 I6_8 ltac:(apply (NPK 69%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_8.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_9 I6_7 ltac:(apply (NPK 70%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_9.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_10 I6_6 ltac:(apply (NPK 71%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_10.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_11 I6_5 ltac:(apply (NPK 72%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_11.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_12 I6_4 ltac:(apply (NPK 73%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_12.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_13 I6_3 ltac:(apply (NPK 74%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_13.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_14 I6_2 ltac:(apply (NPK 75%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_14.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S6) B6_15 I6_15 ltac:(apply (NPK 62%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R6_15.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_1 I8_1 ltac:(apply (NPK 57%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_2 I8_14 ltac:(apply (NPK 44%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_2.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_3 I8_13 ltac:(apply (NPK 45%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_3.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_4 I8_12 ltac:(apply (NPK 46%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_4.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_5 I8_11 ltac:(apply (NPK 47%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_5.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_6 I8_10 ltac:(apply (NPK 48%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_6.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_7 I8_9 ltac:(apply (NPK 49%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_7.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_8 I8_8 ltac:(apply (NPK 50%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_8.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_9 I8_7 ltac:(apply (NPK 51%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_9.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_10 I8_6 ltac:(apply (NPK 52%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_10.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_11 I8_5 ltac:(apply (NPK 53%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_11.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_12 I8_4 ltac:(apply (NPK 54%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_12.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_13 I8_3 ltac:(apply (NPK 55%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_13.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_14 I8_2 ltac:(apply (NPK 56%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_14.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S8) B8_15 I8_15 ltac:(apply (NPK 43%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R8_15.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_1 I9_1 ltac:(apply (NPK 42%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_2 I9_14 ltac:(apply (NPK 29%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_2.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_3 I9_13 ltac:(apply (NPK 30%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_3.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_4 I9_12 ltac:(apply (NPK 31%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_4.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_5 I9_11 ltac:(apply (NPK 32%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_5.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_6 I9_10 ltac:(apply (NPK 33%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_6.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_7 I9_9 ltac:(apply (NPK 34%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_7.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_8 I9_8 ltac:(apply (NPK 35%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_8.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_9 I9_7 ltac:(apply (NPK 36%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_9.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_10 I9_6 ltac:(apply (NPK 37%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_10.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_11 I9_5 ltac:(apply (NPK 38%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_11.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_12 I9_4 ltac:(apply (NPK 39%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_12.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_13 I9_3 ltac:(apply (NPK 40%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_13.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_14 I9_2 ltac:(apply (NPK 41%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_14.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S9) B9_15 I9_15 ltac:(apply (NPK 28%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R9_15.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S10) B10_1 I10_1 ltac:(apply (NPK 27%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R10_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S10) B10_2 I10_4 ltac:(apply (NPK 24%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R10_2.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S10) B10_3 I10_3 ltac:(apply (NPK 25%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R10_3.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S10) B10_4 I10_2 ltac:(apply (NPK 26%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R10_4.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S10) B10_5 I10_5 ltac:(apply (NPK 23%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R10_5.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S14) B14_1 I14_1 ltac:(apply (NPK 3%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R14_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S15) B15_1 I15_1 ltac:(apply (NPK 2%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R15_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S16) B16_1 I16_1 ltac:(apply (NPK 1%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R16_1.
  pose proof (XB _ _ _ _ _ _ _ _ _ _ (proj1 S16) B16_2 I16_2 ltac:(apply (NPK 0%nat); reflexivity) ltac:(cbn [cells_size csize Nat.add length]; lia)) as R16_2.
  apply climpl_done. unfold cpost.
  do 3 eexists.
  split; [unfold cret; do 14 eexists; reflexivity|].
  split; [lia|].
  split; [exact GR|].
  split; [exact CSfin|].
  split; [exact FIN|].
  unfold context_init_res.
  exists q1_1, A1_1, q2_1, A2_1, q3_1, A3_1, q3_2, A3_2, q3_3, A3_3, q3_4, A3_4, q3_5, A3_5, q3_6, A3_6, q3_7, A3_7, q3_8, A3_8, q3_9, A3_9, q3_10, A3_10, q3_11, A3_11, q3_12, A3_12, q3_13, A3_13, q3_14, A3_14, q3_15, A3_15, q4_1, A4_1, q4_2, A4_2, q5_1, A5_1, q5_2, A5_2, q5_3, A5_3, q6_1, A6_1, q6_2, A6_2, q6_3, A6_3, q6_4, A6_4, q6_5, A6_5, q6_6, A6_6, q6_7, A6_7, q6_8, A6_8, q6_9, A6_9, q6_10, A6_10, q6_11, A6_11, q6_12, A6_12, q6_13, A6_13, q6_14, A6_14, q6_15, A6_15, q7_1, A7_1, q7_2, A7_2, q7_3, A7_3, q7_4, A7_4, q8_1, A8_1, q8_2, A8_2, q8_3, A8_3, q8_4, A8_4, q8_5, A8_5, q8_6, A8_6, q8_7, A8_7, q8_8, A8_8, q8_9, A8_9, q8_10, A8_10, q8_11, A8_11, q8_12, A8_12, q8_13, A8_13, q8_14, A8_14, q8_15, A8_15, q9_1, A9_1, q9_2, A9_2, q9_3, A9_3, q9_4, A9_4, q9_5, A9_5, q9_6, A9_6, q9_7, A9_7, q9_8, A9_8, q9_9, A9_9, q9_10, A9_10, q9_11, A9_11, q9_12, A9_12, q9_13, A9_13, q9_14, A9_14, q9_15, A9_15, q10_1, A10_1, q10_2, A10_2, q10_3, A10_3, q10_4, A10_4, q10_5, A10_5, q11_1, A11_1, q11_2, A11_2, q11_3, A11_3, q11_4, A11_4, q11_5, A11_5, q11_6, A11_6, q11_7, A11_7, q11_8, A11_8, q12_1, A12_1, q12_2, A12_2, q12_3, A12_3, q12_4, A12_4, q12_5, A12_5, q12_6, A12_6, q12_7, A12_7, q12_8, A12_8, q12_9, A12_9, q13_1, A13_1, q13_2, A13_2, q14_1, A14_1, q15_1, A15_1, q16_1, A16_1, q16_2, A16_2, q17_1, A17_1, q18_1, A18_1, q19_1, A19_1, q19_2, A19_2, q19_3, A19_3, q20_1, A20_1, q21_1, A21_1, q21_2, A21_2, q21_3, A21_3, q21_4, A21_4, q21_5, A21_5, q21_6, A21_6, q21_7, A21_7, q21_8, A21_8, q21_9, A21_9, q21_10, A21_10, q21_11, A21_11, q21_12, A21_12, q21_13, A21_13, q21_14, A21_14, q21_15, A21_15, q21_16, A21_16, q21_17, A21_17, q21_18, A21_18, q22_1, A22_1.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact R1_1|].
  split; [exact R2_1|].
  split; [exact R3_1|].
  split; [exact R3_2|].
  split; [exact R3_3|].
  split; [exact R3_4|].
  split; [exact R3_5|].
  split; [exact R3_6|].
  split; [exact R3_7|].
  split; [exact R3_8|].
  split; [exact R3_9|].
  split; [exact R3_10|].
  split; [exact R3_11|].
  split; [exact R3_12|].
  split; [exact R3_13|].
  split; [exact R3_14|].
  split; [exact R3_15|].
  split; [exact R4_1|].
  split; [exact R4_2|].
  split; [exact R5_1|].
  split; [exact R5_2|].
  split; [exact R5_3|].
  split; [exact R6_1|].
  split; [exact R6_2|].
  split; [exact R6_3|].
  split; [exact R6_4|].
  split; [exact R6_5|].
  split; [exact R6_6|].
  split; [exact R6_7|].
  split; [exact R6_8|].
  split; [exact R6_9|].
  split; [exact R6_10|].
  split; [exact R6_11|].
  split; [exact R6_12|].
  split; [exact R6_13|].
  split; [exact R6_14|].
  split; [exact R6_15|].
  split; [exact R8_1|].
  split; [exact R8_2|].
  split; [exact R8_3|].
  split; [exact R8_4|].
  split; [exact R8_5|].
  split; [exact R8_6|].
  split; [exact R8_7|].
  split; [exact R8_8|].
  split; [exact R8_9|].
  split; [exact R8_10|].
  split; [exact R8_11|].
  split; [exact R8_12|].
  split; [exact R8_13|].
  split; [exact R8_14|].
  split; [exact R8_15|].
  split; [exact R9_1|].
  split; [exact R9_2|].
  split; [exact R9_3|].
  split; [exact R9_4|].
  split; [exact R9_5|].
  split; [exact R9_6|].
  split; [exact R9_7|].
  split; [exact R9_8|].
  split; [exact R9_9|].
  split; [exact R9_10|].
  split; [exact R9_11|].
  split; [exact R9_12|].
  split; [exact R9_13|].
  split; [exact R9_14|].
  split; [exact R9_15|].
  split; [exact R10_1|].
  split; [exact R10_2|].
  split; [exact R10_3|].
  split; [exact R10_4|].
  split; [exact R10_5|].
  split; [exact R14_1|].
  split; [exact R15_1|].
  split; [exact R16_1|].
  split; [exact R16_2|].
  split; [exact Z17|].
  split; [exact Z18|].
  split; [exact Z19a|].
  split; [exact Z19b|].
  split; [exact Z19c|].
  split; [exact Z20|].
  split; [exact Z22|].
  split; [exact CX78|].
  split; [exact CX70|].
  split; [exact CXd0|].
  exact CXc8.
Qed.
End WithCeiling0.
