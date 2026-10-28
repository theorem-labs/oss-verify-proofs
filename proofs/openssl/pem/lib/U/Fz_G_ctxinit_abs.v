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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_I3_fxi Fz_I3_top Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Th_mutex Fz_T_lock_new Fz_M_calloc Fz_I1_defs Fz_I1_new Fz_M_aligned Fz_G_ossl_lib_ctx_get_ex_data_global Fz_G_ossl_do_ex_data_init F_memset Fz_T_sa_new Fz_G_ossl_method_store_new Fz_G_ossl_prov_conf_ctx_new. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_strdup Fz_T_atomic Fz_T_once Fz_I3_base Fz_G_ossl_rand_ctx_new Fz_I2_dcache Fz_T_sk Fz_G_OPENSSL_sk_new Fz_G_ossl_provider_store_new Fz_I2_ppi Fz_I2_namemap Fz_I2_pdefns Fz_G_ossl_ctx_global_properties_new Fz_G_ossl_bio_core_globals_new Fz_G_ossl_prov_drbg_nonce_ctx_new Fz_G_ossl_self_test_set_callback_new Fz_G_ossl_indicator_set_callback_new Th_mutex_init Fz_G_ossl_crypto_mutex_new Th_cond Fz_G_ossl_crypto_condvar_new Fz_G_ossl_threads_ctx_new Fz_G_ossl_child_prov_ctx_new Fz_G_COMP_zlib Fz_G_COMP_get_type Fz_G_ossl_load_builtin_compressions Fz_I2_pstring Fz_I2_htnew Fz_T_rcu Fz_M_realloc Fz_kit_ra.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_G_context_init_2 Fz_G_context_init.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition CI_EV_B : nat := 126.
Definition CI_A_B : Z := 119. Definition CI_B_B : Z := 6. Definition CI_BIG_B : Z := 83768. Definition CI_STK_B : Z := 8576.
Definition CI_W_B : list (Z * Z) := [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z.
Definition CI_PRE_B (LBall : list block) (L : @clist bptr) (m : mem) : Prop :=
  rw_cells usegs m 0x32de28 [C1 (Z_to_bv 8 0)] /\ rw_cells usegs m 0x32de40 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] /\ (exists (x_2e82f0 : word), rw_cells usegs m 0x32de80 [C8 x_2e82f0]) /\ rw_cells usegs m 0x351010 [C4 (Z_to_bv 64 0)].
Definition CI_FP_B (a : Z) : Prop := 0x32de28 <= a < 0x32de29 \/ 0x32de40 <= a < 0x32de48 \/ 0x32de80 <= a < 0x32de88 \/ 0x351010 <= a < 0x351014.
Definition CI_RES_B (pk : bptr) (LBall' : list block) (L' : @clist bptr) (m' : mem) : Prop := True.

Lemma ci_w_range_B : forall a, rin_ivs CI_W_B a -> DC_CTX <= a < DC_CTX + 328.
Proof. intros a H. unfold CI_W_B, DC_CTX in *. cbn [rin_ivs fst snd] in H. lia. Qed.
Lemma ci_stk_pos_B : 112 <= CI_STK_B. Proof. unfold CI_STK_B. lia. Qed.
Lemma ci_nums_B : 0 <= CI_A_B /\ 0 <= CI_B_B /\ 0 <= CI_BIG_B. Proof. unfold CI_A_B, CI_B_B, CI_BIG_B. lia. Qed.
Lemma ci_res_cfr_B : forall pk LBall' L' m m' SPX, CI_RES_B pk LBall' L' m -> cfr (fun q => q = pk) FXI_AW SPX LBall' m m' -> CI_RES_B pk LBall' L' m'.
Proof. intros. exact I. Qed.
Lemma ci_fp_ok_B : forall a, CI_FP_B a -> 0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS /\ ~ rin_ivs FXI_PW a.
Proof. intros a H. unfold CI_FP_B in H. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS, FXI_PW, DC_S, RATP. cbn [rin_ivs fst snd]. lia. Qed.
Lemma ci_pre_agree_B : forall LBall L m m', agree_on CI_FP_B m m' -> CI_PRE_B LBall L m -> CI_PRE_B LBall L m'.
Proof. intros LBall L m m' AG (H0 & H1 & H2 & H3). destruct H2 as (x_2e82f0 & H2). assert (K0 : rw_cells usegs m' 0x32de28 [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_agree; [exact AG| exact H0| intros b Hb; unfold CI_FP_B; cbn [cells_size csize Nat.add] in Hb; lia]). assert (K1 : rw_cells usegs m' 0x32de40 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)]) by (eapply rw_cells_agree; [exact AG| exact H1| intros b Hb; unfold CI_FP_B; cbn [cells_size csize Nat.add] in Hb; lia]). assert (K2 : rw_cells usegs m' 0x32de80 [C8 x_2e82f0]) by (eapply rw_cells_agree; [exact AG| exact H2| intros b Hb; unfold CI_FP_B; cbn [cells_size csize Nat.add] in Hb; lia]). assert (K3 : rw_cells usegs m' 0x351010 [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_agree; [exact AG| exact H3| intros b Hb; unfold CI_FP_B; cbn [cells_size csize Nat.add] in Hb; lia]). split; [exact K0|]. split; [exact K1|]. split; [exists x_2e82f0; exact K2|]. exact K3. Qed.
Lemma ci_pre_intro_B : forall LBall L m, ci_site m -> CI_PRE_B LBall L m.
Proof. intros LBall L m (LK1 & LK2 & G & LKe & lh & S0 & S8 & S28 & S32 & S40 & S80 & S96 & T0 & T10 & T14 & T18 & EO & RP). unfold IC_S in *.
  unfold CI_PRE_B. split; [exact S8|]. split; [exact S32|]. split; [eexists; exact S96|]. exact RP. Qed.

Theorem context_init_abs_B : crypto_zalloc_stmt -> crypto_malloc_stmt -> T_lock_new_stmt -> lh_new_stmt -> ossl_property_string_data_new_rep_stmt -> crypto_aligned_alloc_stmt -> ossl_property_parse_init_fp_stmt -> context_init_abs_stmt CI_EV_B CI_A_B CI_B_B CI_BIG_B CI_STK_B CI_W_B CI_PRE_B CI_RES_B.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros B0 B1 B2 B3 B4 B5 B6. unfold context_init_abs_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd Hf ROOM CST SLO SP16 PIN CTX0 PRE.
  destruct CTX0 as (bs & HC). destruct PRE as (P0 & P1 & P2 & P3). destruct P2 as (x_2e82f0 & P2). 
  pose proof (rw_cells_split_CB usegs m DC_CTX [] 328 bs [] [8; 8; 152; 8; 144; 8]%nat HC eq_refl) as HX. cbn [mk_CB_cells app] in HX. unfold DC_CTX in HX. clear HC.
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in HX. destruct HX as [F2e8338 HX]. lazymatch type of HX with rw_cells _ _ ?ad _ => let v := eval vm_compute in ad in change ad with v in HX end.
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in HX. destruct HX as [F2e8340 HX]. lazymatch type of HX with rw_cells _ _ ?ad _ => let v := eval vm_compute in ad in change ad with v in HX end.
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in HX. destruct HX as [F2e8348 HX]. lazymatch type of HX with rw_cells _ _ ?ad _ => let v := eval vm_compute in ad in change ad with v in HX end.
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in HX. destruct HX as [F2e83e0 HX]. lazymatch type of HX with rw_cells _ _ ?ad _ => let v := eval vm_compute in ad in change ad with v in HX end.
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in HX. destruct HX as [F2e83e8 HX]. lazymatch type of HX with rw_cells _ _ ?ad _ => let v := eval vm_compute in ad in change ad with v in HX end.
  rename HX into F2e8478.
  pose proof (context_init_spec B0 B1 B2 B3 B4 B5 B6) as CI. unfold context_init_stmt in CI.
  eapply climpl_mono.
  { eapply CI; [exact Hf| exact ROOM| exact CST| unfold CI_STK_B in SLO; unfold context_init_STACK, PPI_STACK, CRE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; exact SLO| exact SP16| unfold DC_CTX in PIN; exact PIN| exact P0| exact P1| exact P2| exact F2e8338| exact F2e8340| exact F2e83e0| exact F2e83e8| exact P3]. }
  clear CI. intros f' L' s' ms' POST. unfold cpost in POST |- *. destruct POST as (v & m' & LBall' & CRET & FUEL & CG & CST' & CFR & RES).
  exists v, m', LBall'. split; [exact CRET|]. split; [exact FUEL|]. split; [exact CG|]. split; [exact CST'|]. split; [exact CFR|].
  destruct RES as (q1_1 & A1_1 & q2_1 & A2_1 & q3_1 & A3_1 & q3_2 & A3_2 & q3_3 & A3_3 & q3_4 & A3_4 & q3_5 & A3_5 & q3_6 & A3_6 & q3_7 & A3_7 & q3_8 & A3_8 & q3_9 & A3_9 & q3_10 & A3_10 & q3_11 & A3_11 & q3_12 & A3_12 & q3_13 & A3_13 & q3_14 & A3_14 & q3_15 & A3_15 & q4_1 & A4_1 & q4_2 & A4_2 & q5_1 & A5_1 & q5_2 & A5_2 & q5_3 & A5_3 & q6_1 & A6_1 & q6_2 & A6_2 & q6_3 & A6_3 & q6_4 & A6_4 & q6_5 & A6_5 & q6_6 & A6_6 & q6_7 & A6_7 & q6_8 & A6_8 & q6_9 & A6_9 & q6_10 & A6_10 & q6_11 & A6_11 & q6_12 & A6_12 & q6_13 & A6_13 & q6_14 & A6_14 & q6_15 & A6_15 & q7_1 & A7_1 & q7_2 & A7_2 & q7_3 & A7_3 & q7_4 & A7_4 & q8_1 & A8_1 & q8_2 & A8_2 & q8_3 & A8_3 & q8_4 & A8_4 & q8_5 & A8_5 & q8_6 & A8_6 & q8_7 & A8_7 & q8_8 & A8_8 & q8_9 & A8_9 & q8_10 & A8_10 & q8_11 & A8_11 & q8_12 & A8_12 & q8_13 & A8_13 & q8_14 & A8_14 & q8_15 & A8_15 & q9_1 & A9_1 & q9_2 & A9_2 & q9_3 & A9_3 & q9_4 & A9_4 & q9_5 & A9_5 & q9_6 & A9_6 & q9_7 & A9_7 & q9_8 & A9_8 & q9_9 & A9_9 & q9_10 & A9_10 & q9_11 & A9_11 & q9_12 & A9_12 & q9_13 & A9_13 & q9_14 & A9_14 & q9_15 & A9_15 & q10_1 & A10_1 & q10_2 & A10_2 & q10_3 & A10_3 & q10_4 & A10_4 & q10_5 & A10_5 & q11_1 & A11_1 & q11_2 & A11_2 & q11_3 & A11_3 & q11_4 & A11_4 & q11_5 & A11_5 & q11_6 & A11_6 & q11_7 & A11_7 & q11_8 & A11_8 & q12_1 & A12_1 & q12_2 & A12_2 & q12_3 & A12_3 & q12_4 & A12_4 & q12_5 & A12_5 & q12_6 & A12_6 & q12_7 & A12_7 & q12_8 & A12_8 & q12_9 & A12_9 & q13_1 & A13_1 & q13_2 & A13_2 & q14_1 & A14_1 & q15_1 & A15_1 & q16_1 & A16_1 & q16_2 & A16_2 & q17_1 & A17_1 & q18_1 & A18_1 & q19_1 & A19_1 & q19_2 & A19_2 & q19_3 & A19_3 & q20_1 & A20_1 & q21_1 & A21_1 & q21_2 & A21_2 & q21_3 & A21_3 & q21_4 & A21_4 & q21_5 & A21_5 & q21_6 & A21_6 & q21_7 & A21_7 & q21_8 & A21_8 & q21_9 & A21_9 & q21_10 & A21_10 & q21_11 & A21_11 & q21_12 & A21_12 & q21_13 & A21_13 & q21_14 & A21_14 & q21_15 & A21_15 & q21_16 & A21_16 & q21_17 & A21_17 & q21_18 & A21_18 & q22_1 & A22_1 & Hv & HLB & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & C28 & C29 & C30 & C31 & C32 & C33 & C34 & C35 & C36 & C37 & C38 & C39 & C40 & C41 & C42 & C43 & C44 & C45 & C46 & C47 & C48 & C49 & C50 & C51 & C52 & C53 & C54 & C55 & C56 & C57 & C58 & C59 & C60 & C61 & C62 & C63 & C64 & C65 & C66 & C67 & C68 & C69 & C70 & C71 & C72 & C73 & C74 & C75 & C76 & C77 & C78 & C79 & C80 & C81 & C82 & C83 & C84 & C85 & C86).
  split; [exact Hv|]. exists q2_1, A2_1.
  assert (INk : In (q2_1, A2_1, 40) LBall') by (rewrite HLB; do 122 right; left; reflexivity).
  split; [exact INk|]. split; [exact (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST' INk)|].
  split; [unfold mutex_cells; exact C1|]. split; [unfold DC_GLOBAL_LOCK; exact C85|].
  split; [| exact I]. pose proof CST as (_ & OWN & _).
  assert (CSTx : cstate s' ([(q22_1, A22_1, 56); (q21_18, A21_18, 24); (q21_17, A21_17, 18); (q21_16, A21_16, 24); (q21_15, A21_15, 32); (q21_14, A21_14, 19); (q21_13, A21_13, 24); (q21_12, A21_12, 25); (q21_11, A21_11, 24); (q21_10, A21_10, 48); (q21_9, A21_9, 21); (q21_8, A21_8, 24); (q21_7, A21_7, 22); (q21_6, A21_6, 24); (q21_5, A21_5, 20); (q21_4, A21_4, 24); (q21_3, A21_3, 23); (q21_2, A21_2, 24); (q21_1, A21_1, 24); (q20_1, A20_1, 88); (q19_3, A19_3, 48); (q19_2, A19_2, 40); (q19_1, A19_1, 32); (q18_1, A18_1, 8); (q17_1, A17_1, 16); (q16_2, A16_2, 40); (q16_1, A16_1, 16); (q15_1, A15_1, 56); (q14_1, A14_1, 16); (q13_2, A13_2, 128); (q13_1, A13_1, 104); (q12_9, A12_9, 56); (q12_8, A12_8, 16); (q12_7, A12_7, 264); (q12_6, A12_6, 32768); (q12_5, A12_5, 24); (q12_4, A12_4, 40); (q12_3, A12_3, 96); (q12_2, A12_2, 40); (q12_1, A12_1, 40); (q11_8, A11_8, 56); (q11_7, A11_7, 56); (q11_6, A11_6, 128); (q11_5, A11_5, 104); (q11_4, A11_4, 128); (q11_3, A11_3, 104); (q11_2, A11_2, 40); (q11_1, A11_1, 48); (q10_5, A10_5, 40); (q10_4, A10_4, 56); (q10_3, A10_3, 40); (q10_2, A10_2, 56); (q10_1, A10_1, 80); (q9_15, A9_15, 40); (q9_14, A9_14, 40); (q9_13, A9_13, 40); (q9_12, A9_12, 32); (q9_11, A9_11, 40); (q9_10, A9_10, 40); (q9_9, A9_9, 32); (q9_8, A9_8, 40); (q9_7, A9_7, 40); (q9_6, A9_6, 32); (q9_5, A9_5, 40); (q9_4, A9_4, 40); (q9_3, A9_3, 32); (q9_2, A9_2, 384); (q9_1, A9_1, 24); (q8_15, A8_15, 40); (q8_14, A8_14, 40); (q8_13, A8_13, 40); (q8_12, A8_12, 32); (q8_11, A8_11, 40); (q8_10, A8_10, 40); (q8_9, A8_9, 32); (q8_8, A8_8, 40); (q8_7, A8_7, 40); (q8_6, A8_6, 32); (q8_5, A8_5, 40); (q8_4, A8_4, 40); (q8_3, A8_3, 32); (q8_2, A8_2, 384); (q8_1, A8_1, 24); (q7_4, A7_4, 128); (q7_3, A7_3, 104); (q7_2, A7_2, 40); (q7_1, A7_1, 16); (q6_15, A6_15, 40); (q6_14, A6_14, 40); (q6_13, A6_13, 40); (q6_12, A6_12, 32); (q6_11, A6_11, 40); (q6_10, A6_10, 40); (q6_9, A6_9, 32); (q6_8, A6_8, 40); (q6_7, A6_7, 40); (q6_6, A6_6, 32); (q6_5, A6_5, 40); (q6_4, A6_4, 40); (q6_3, A6_3, 32); (q6_2, A6_2, 384); (q6_1, A6_1, 24); (q5_3, A5_3, 40); (q5_2, A5_2, 5); (q5_1, A5_1, 88); (q4_2, A4_2, 40); (q4_1, A4_1, 16); (q3_15, A3_15, 40); (q3_14, A3_14, 40); (q3_13, A3_13, 40); (q3_12, A3_12, 32); (q3_11, A3_11, 40); (q3_10, A3_10, 40); (q3_9, A3_9, 32); (q3_8, A3_8, 40); (q3_7, A3_7, 40); (q3_6, A3_6, 32); (q3_5, A3_5, 40); (q3_4, A3_4, 40); (q3_3, A3_3, 32); (q3_2, A3_2, 384); (q3_1, A3_1, 24); (q2_1, A2_1, 40); (q1_1, A1_1, 40)] ++ LBall) LB L' m' sp tp lo Bd) by (rewrite HLB in CST'; exact CST').
  intros q Hq. exact (cstate_fresh_ids _ _ _ _ _ _ _ _ _ _ _ CSTx OWN (q2_1, A2_1, 40) ltac:(do 122 right; left; reflexivity) q Hq).
Qed.
(* [comment removed for export] *)
Lemma ci_budget_B : (CI_EV_B <= 3415)%nat /\ CI_A_B <= 3852 /\ CI_B_B <= 58 /\ CI_BIG_B <= 500000000 /\ CI_STK_B <= 65264.
Proof. unfold CI_EV_B, CI_A_B, CI_B_B, CI_BIG_B, CI_STK_B. lia. Qed.
End WithCeiling0.
