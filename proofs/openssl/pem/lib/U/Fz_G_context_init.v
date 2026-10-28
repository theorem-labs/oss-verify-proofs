(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Export Fz_G_context_init_2.
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

Theorem context_init_spec : crypto_zalloc_stmt -> crypto_malloc_stmt -> T_lock_new_stmt -> lh_new_stmt -> ossl_property_string_data_new_rep_stmt -> crypto_aligned_alloc_stmt -> ossl_property_parse_init_fp_stmt -> context_init_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros HB_crypto_zalloc_stmt HB_crypto_malloc_stmt HB_T_lock_new_stmt HB_lh_new_stmt HB_ossl_property_string_data_new_rep_stmt HB_crypto_aligned_alloc_stmt HB_ossl_property_parse_init_fp_stmt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x_2e82f0 x_2e8338 x_2e8340 x_2e83e0 x_2e83e8 F fc m st LBall LB L f lo B
         Hf ROOM CST SLO SP16 PIN_a0 SC_2e8298 SC_2e82b0 SC_2e82f0 SC_2e8338 SC_2e8340 SC_2e83e0 SC_2e83e8 SC_2eb2d8. subst a0.
  pose proof CST as (HP & OWN & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold context_init_STACK, PPI_STACK, SNM_STACK, NMN_STACK, PSD_STACK, HTN_STACK, ossl_method_store_new_STACK, ossl_rand_ctx_new_STACK, ossl_provider_store_new_STACK, ossl_do_ex_data_init_STACK, ossl_prov_conf_ctx_new_STACK, DCN_STACK, RCU_STACK, ossl_prov_drbg_nonce_ctx_new_STACK, ossl_load_builtin_compressions_STACK, PDN_STACK, ossl_threads_ctx_new_STACK, LOCK_NEW_STACK, LHN_STACK, ossl_crypto_mutex_new_STACK, CRE_STACK, OPENSSL_sk_new_STACK, ossl_ctx_global_properties_new_STACK, ossl_bio_core_globals_new_STACK, ossl_self_test_set_callback_new_STACK, ossl_indicator_set_callback_new_STACK, ossl_child_prov_ctx_new_STACK, CZ_STACK, RREALLOC_STACK, CM_STACK, RMALLOC_STACK, FZ_G_context_init, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose (LBc0 := LBall). pose (Lc0 := L).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  cprefix. step. carve_frame 32%nat ST. do 3 ths. do 3 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma0 end.
  assert (CSTa0 : cstate st LBc0 LB Lc0 ma0 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m ma0 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST| exact MU0| exact WM0| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF0 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st LBc0 Lc0 m st LBc0 Lc0 ma0).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU0| exact WM0| exact HP| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_nil]. }
  clear MU0 WM0.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (T_lock_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact ROOM| wp_wnorm; wp_lia..]| exact CSTa0| rewrite unsigned_lit by wp_lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f1 L1 st1 ms1 (v1 & mb1 & LB1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (q1_1 & A1_1 & -> & -> & -> & RNG_A1_1 & BC1_0)).
  destruct RET1 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM1 by wp_lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ ma0 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(wp_lia)) as FRs1; clear FRh end.
  match goal with Hs : rw_cells _ ma0 0x32de28 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma0 0x32de40 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma0 0x32de80 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma0 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma0 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma0 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma0 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma0 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by wp_lia.
  pose proof RNG_A1_1 as (P0_A1_1 & _ & _ & PC_A1_1 & _).
  assert (FUc1 : (f <= f1 + 1)%nat) by (clear - FU1; lia).
  unfold mutex_cells in BC1_0.
  change (Z.to_nat 40) with 40%nat in BC1_0.
  pose (LBc1 := (q1_1, A1_1, 40) :: LBc0). pose (Lc1 := (q1_1, 40) :: Lc0).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc1 s_ ms_ Q_) end.
  assert (GRc1 : cgrow L Lc1 1 0 0) by (eapply cgrow_weaken; [exact GR1| wp_wnorm; wp_lia..]).
  assert (IN_A1_1 : In (q1_1, A1_1, 40) LBc1) by (left; reflexivity).
  wp_box1 BC1_0.
  pose proof (conj IN_A1_1 BC1_0) as PK1. clear CSTa0 CFR1 FU1 GR1 IN_A1_1 BC1_0.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dec8, 0x32ded0)]%Z mb1) as MU1. pose proof (wmono_refl usegs mb1) as WM1.
  cprefix. step. wp_brF. step. step. wp_brF. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma1 end.
  assert (CSTa1 : cstate st1 LBc1 LB Lc1 ma1 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb1 ma1 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF1 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st1 LBc1 Lc1 mb1 st1 LBc1 Lc1 ma1).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU1| exact WM1| exact HP1| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST1 HP1 ST1 MI1 MU1 WM1. try clear errv1.
  clear P0_A1_1 PC_A1_1 RNG_A1_1.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_do_ex_data_init_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc1)| wp_wnorm; wp_lia..]| exact CSTa1| rewrite unsigned_lit by wp_lia; unfold ossl_do_ex_data_init_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia| reflexivity| wp_cells]. }
  intros f2 L2 st2 ms2 (v2 & mb2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (q2_1 & A2_1 & -> & -> & -> & RNG_A2_1 & BC2_0 & BC2_1)).
  destruct RET2 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM2 by wp_lia.
  pose proof FRM2 as (CFR2 & _).
  lazymatch goal with FRh : rw_cells _ ma1 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRh ltac:(wp_lia)) as FRs2; clear FRh end.
  match goal with Hs : rw_cells _ ma1 0x32de28 _ |- _ => let Hn := fresh "SK" in cst_static CFR2 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma1 0x32de40 _ |- _ => let Hn := fresh "SK" in cst_static CFR2 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma1 0x32de80 _ |- _ => let Hn := fresh "SK" in cst_static CFR2 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma1 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR2 Hs Hn; clear Hs end.
  try match goal with Hs : rw_cells _ ma1 0x32ded0 _ |- _ => clear Hs end.
  match goal with Hs : rw_cells _ ma1 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR2 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma1 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR2 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma1 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR2 Hs Hn; clear Hs end.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by wp_lia.
  pose proof RNG_A2_1 as (P0_A2_1 & _ & _ & PC_A2_1 & _).
  assert (FUc2 : (f <= f2 + 2)%nat) by (clear - FU2 FUc1; lia).
  change (Z.to_nat 40) with 40%nat in BC2_0, BC2_1.
  pose (LBc2 := (q2_1, A2_1, 40) :: LBc1). pose (Lc2 := (q2_1, 40) :: Lc1).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc2 s_ ms_ Q_) end.
  assert (GRc2 : cgrow L Lc2 2 0 0) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc1 GR2)| wp_wnorm; wp_lia..]).
  assert (IN_A2_1 : In (q2_1, A2_1, 40) LBc2) by (left; reflexivity).
  wp_box1 BC2_1.
  pose proof (conj IN_A2_1 BC2_1) as PK2. clear CSTa1 CFR2 FU2 GR2 FUc1 GRc1 f1 IN_A2_1 BC2_1.
  try (clear u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z mb2) as MU2. pose proof (wmono_refl usegs mb2) as WM2.
  cprefix. step. wp_brF. do 2 step.
  chere.
  assert (CSTa2 : cstate st2 LBc2 LB Lc2 mb2 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb2 mb2 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  clear CST2 HP2 ST2 MI2 MU2 WM2. try clear errv2.
  clear P0_A2_1 PC_A2_1 RNG_A2_1.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_method_store_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc2)| wp_wnorm; wp_lia..]| exact CSTa2| rewrite unsigned_lit by wp_lia; unfold ossl_method_store_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f3 L3 st3 ms3 (v3 & mb3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (q3_1 & A3_1 & q3_2 & A3_2 & q3_3 & A3_3 & q3_4 & A3_4 & q3_5 & A3_5 & q3_6 & A3_6 & q3_7 & A3_7 & q3_8 & A3_8 & q3_9 & A3_9 & q3_10 & A3_10 & q3_11 & A3_11 & q3_12 & A3_12 & q3_13 & A3_13 & q3_14 & A3_14 & q3_15 & A3_15 & -> & -> & -> & RNG_A3_1 & RNG_A3_2 & RNG_A3_3 & RNG_A3_4 & RNG_A3_5 & RNG_A3_6 & RNG_A3_7 & RNG_A3_8 & RNG_A3_9 & RNG_A3_10 & RNG_A3_11 & RNG_A3_12 & RNG_A3_13 & RNG_A3_14 & RNG_A3_15 & BC3_0 & BC3_1 & BC3_2 & BC3_3 & BC3_4 & BC3_5 & BC3_6 & BC3_7 & BC3_8 & BC3_9 & BC3_10 & BC3_11 & BC3_12 & BC3_13 & BC3_14)).
  destruct RET3 as (u0_3 & u1_3 & u2_3 & b1_3 & b2_3 & b3_3 & b4_3 & b5_3 & b6_3 & b7_3 & u3_3 & u4_3 & u5_3 & u6_3 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM3 by wp_lia.
  pose proof FRM3 as (CFR3 & _).
  lazymatch goal with FRh : rw_cells _ mb2 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FRh ltac:(wp_lia)) as FRs3; clear FRh end.
  match goal with Hs : rw_cells _ mb2 0x32de28 _ |- _ => let Hn := fresh "SK" in cst_static CFR3 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb2 0x32de40 _ |- _ => let Hn := fresh "SK" in cst_static CFR3 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb2 0x32de80 _ |- _ => let Hn := fresh "SK" in cst_static CFR3 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb2 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR3 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb2 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR3 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb2 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR3 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb2 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR3 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ mb2 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR3 Hs Hn; clear Hs end.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by wp_lia.
  pose proof RNG_A3_1 as (P0_A3_1 & _ & _ & PC_A3_1 & _).
  pose proof RNG_A3_2 as (P0_A3_2 & _ & _ & PC_A3_2 & _).
  pose proof RNG_A3_3 as (P0_A3_3 & _ & _ & PC_A3_3 & _).
  pose proof RNG_A3_4 as (P0_A3_4 & _ & _ & PC_A3_4 & _).
  pose proof RNG_A3_5 as (P0_A3_5 & _ & _ & PC_A3_5 & _).
  pose proof RNG_A3_6 as (P0_A3_6 & _ & _ & PC_A3_6 & _).
  pose proof RNG_A3_7 as (P0_A3_7 & _ & _ & PC_A3_7 & _).
  pose proof RNG_A3_8 as (P0_A3_8 & _ & _ & PC_A3_8 & _).
  pose proof RNG_A3_9 as (P0_A3_9 & _ & _ & PC_A3_9 & _).
  pose proof RNG_A3_10 as (P0_A3_10 & _ & _ & PC_A3_10 & _).
  pose proof RNG_A3_11 as (P0_A3_11 & _ & _ & PC_A3_11 & _).
  pose proof RNG_A3_12 as (P0_A3_12 & _ & _ & PC_A3_12 & _).
  pose proof RNG_A3_13 as (P0_A3_13 & _ & _ & PC_A3_13 & _).
  pose proof RNG_A3_14 as (P0_A3_14 & _ & _ & PC_A3_14 & _).
  pose proof RNG_A3_15 as (P0_A3_15 & _ & _ & PC_A3_15 & _).
  assert (FUc3 : (f <= f3 + 17)%nat) by (clear - FU3 FUc2; lia).
  change (Z.to_nat 24) with 24%nat in BC3_0, BC3_1, BC3_2, BC3_3, BC3_4, BC3_5, BC3_6, BC3_7, BC3_8, BC3_9, BC3_10, BC3_11, BC3_12, BC3_13, BC3_14.
  change (Z.to_nat 32) with 32%nat in BC3_0, BC3_1, BC3_2, BC3_3, BC3_4, BC3_5, BC3_6, BC3_7, BC3_8, BC3_9, BC3_10, BC3_11, BC3_12, BC3_13, BC3_14.
  change (Z.to_nat 40) with 40%nat in BC3_0, BC3_1, BC3_2, BC3_3, BC3_4, BC3_5, BC3_6, BC3_7, BC3_8, BC3_9, BC3_10, BC3_11, BC3_12, BC3_13, BC3_14.
  change (Z.to_nat 384) with 384%nat in BC3_0, BC3_1, BC3_2, BC3_3, BC3_4, BC3_5, BC3_6, BC3_7, BC3_8, BC3_9, BC3_10, BC3_11, BC3_12, BC3_13, BC3_14.
  pose (LBc3 := (q3_15, A3_15, 40) :: (q3_14, A3_14, 40) :: (q3_13, A3_13, 40) :: (q3_12, A3_12, 32) :: (q3_11, A3_11, 40) :: (q3_10, A3_10, 40) :: (q3_9, A3_9, 32) :: (q3_8, A3_8, 40) :: (q3_7, A3_7, 40) :: (q3_6, A3_6, 32) :: (q3_5, A3_5, 40) :: (q3_4, A3_4, 40) :: (q3_3, A3_3, 32) :: (q3_2, A3_2, 384) :: (q3_1, A3_1, 24) :: LBc2). pose (Lc3 := (q3_15, 40) :: (q3_14, 40) :: (q3_13, 40) :: (q3_12, 32) :: (q3_11, 40) :: (q3_10, 40) :: (q3_9, 32) :: (q3_8, 40) :: (q3_7, 40) :: (q3_6, 32) :: (q3_5, 40) :: (q3_4, 40) :: (q3_3, 32) :: (q3_2, 384) :: (q3_1, 24) :: Lc2).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc3 s_ ms_ Q_) end.
  assert (GRc3 : cgrow L Lc3 16 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc2 GR3)| wp_wnorm; wp_lia..]).
  assert (IN_A3_15 : In (q3_15, A3_15, 40) LBc3) by (left; reflexivity).
  assert (IN_A3_14 : In (q3_14, A3_14, 40) LBc3) by (do 1 right; left; reflexivity).
  assert (IN_A3_13 : In (q3_13, A3_13, 40) LBc3) by (do 2 right; left; reflexivity).
  assert (IN_A3_12 : In (q3_12, A3_12, 32) LBc3) by (do 3 right; left; reflexivity).
  assert (IN_A3_11 : In (q3_11, A3_11, 40) LBc3) by (do 4 right; left; reflexivity).
  assert (IN_A3_10 : In (q3_10, A3_10, 40) LBc3) by (do 5 right; left; reflexivity).
  assert (IN_A3_9 : In (q3_9, A3_9, 32) LBc3) by (do 6 right; left; reflexivity).
  assert (IN_A3_8 : In (q3_8, A3_8, 40) LBc3) by (do 7 right; left; reflexivity).
  assert (IN_A3_7 : In (q3_7, A3_7, 40) LBc3) by (do 8 right; left; reflexivity).
  assert (IN_A3_6 : In (q3_6, A3_6, 32) LBc3) by (do 9 right; left; reflexivity).
  assert (IN_A3_5 : In (q3_5, A3_5, 40) LBc3) by (do 10 right; left; reflexivity).
  assert (IN_A3_4 : In (q3_4, A3_4, 40) LBc3) by (do 11 right; left; reflexivity).
  assert (IN_A3_3 : In (q3_3, A3_3, 32) LBc3) by (do 12 right; left; reflexivity).
  assert (IN_A3_2 : In (q3_2, A3_2, 384) LBc3) by (do 13 right; left; reflexivity).
  assert (IN_A3_1 : In (q3_1, A3_1, 24) LBc3) by (do 14 right; left; reflexivity).
  wp_box1 BC3_0.
  wp_box1 BC3_1.
  wp_box1 BC3_2.
  wp_box1 BC3_3.
  wp_box1 BC3_4.
  wp_box1 BC3_5.
  wp_box1 BC3_6.
  wp_box1 BC3_7.
  wp_box1 BC3_8.
  wp_box1 BC3_9.
  wp_box1 BC3_10.
  wp_box1 BC3_11.
  wp_box1 BC3_12.
  wp_box1 BC3_13.
  wp_box1 BC3_14.
  pose proof (conj IN_A3_15 (conj IN_A3_14 (conj IN_A3_13 (conj IN_A3_12 (conj IN_A3_11 (conj IN_A3_10 (conj IN_A3_9 (conj IN_A3_8 (conj IN_A3_7 (conj IN_A3_6 (conj IN_A3_5 (conj IN_A3_4 (conj IN_A3_3 (conj IN_A3_2 (conj IN_A3_1 (conj BC3_0 (conj BC3_1 (conj BC3_2 (conj BC3_3 (conj BC3_4 (conj BC3_5 (conj BC3_6 (conj BC3_7 (conj BC3_8 (conj BC3_9 (conj BC3_10 (conj BC3_11 (conj BC3_12 (conj BC3_13 BC3_14))))))))))))))))))))))))))))) as PK3. clear CSTa2 CFR3 FU3 GR3 FUc2 GRc2 f2 IN_A3_15 IN_A3_14 IN_A3_13 IN_A3_12 IN_A3_11 IN_A3_10 IN_A3_9 IN_A3_8 IN_A3_7 IN_A3_6 IN_A3_5 IN_A3_4 IN_A3_3 IN_A3_2 IN_A3_1 BC3_0 BC3_1 BC3_2 BC3_3 BC3_4 BC3_5 BC3_6 BC3_7 BC3_8 BC3_9 BC3_10 BC3_11 BC3_12 BC3_13 BC3_14.
  try (clear u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32df78, 0x32df80)]%Z mb3) as MU3. pose proof (wmono_refl usegs mb3) as WM3.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma3 end.
  assert (CSTa3 : cstate st3 LBc3 LB Lc3 ma3 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb3 ma3 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF3 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st3 LBc3 Lc3 mb3 st3 LBc3 Lc3 ma3).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU3| exact WM3| exact HP3| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST3 HP3 ST3 MI3 MU3 WM3. try clear errv3.
  clear P0_A3_1 PC_A3_1 RNG_A3_1 P0_A3_2 PC_A3_2 RNG_A3_2 P0_A3_3 PC_A3_3 RNG_A3_3 P0_A3_4 PC_A3_4 RNG_A3_4 P0_A3_5 PC_A3_5 RNG_A3_5 P0_A3_6 PC_A3_6 RNG_A3_6 P0_A3_7 PC_A3_7 RNG_A3_7 P0_A3_8 PC_A3_8 RNG_A3_8 P0_A3_9 PC_A3_9 RNG_A3_9 P0_A3_10 PC_A3_10 RNG_A3_10 P0_A3_11 PC_A3_11 RNG_A3_11 P0_A3_12 PC_A3_12 RNG_A3_12 P0_A3_13 PC_A3_13 RNG_A3_13 P0_A3_14 PC_A3_14 RNG_A3_14 P0_A3_15 PC_A3_15 RNG_A3_15.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_prov_conf_ctx_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc3)| wp_wnorm; wp_lia..]| exact CSTa3| rewrite unsigned_lit by wp_lia; unfold ossl_prov_conf_ctx_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f4 L4 st4 ms4 (v4 & mb4 & LB4 & RET4 & FU4 & GR4 & CST4 & FRM4 & (q4_1 & A4_1 & q4_2 & A4_2 & -> & -> & -> & RNG_A4_1 & RNG_A4_2 & BC4_0 & BC4_1)).
  destruct RET4 as (u0_4 & u1_4 & u2_4 & b1_4 & b2_4 & b3_4 & b4_4 & b5_4 & b6_4 & b7_4 & u3_4 & u4_4 & u5_4 & u6_4 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM4 by wp_lia.
  pose proof FRM4 as (CFR4 & _).
  lazymatch goal with FRh : rw_cells _ ma3 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 FRh ltac:(wp_lia)) as FRs4; clear FRh end.
  match goal with Hs : rw_cells _ ma3 0x32de28 _ |- _ => let Hn := fresh "SK" in cst_static CFR4 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma3 0x32de40 _ |- _ => let Hn := fresh "SK" in cst_static CFR4 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma3 0x32de80 _ |- _ => let Hn := fresh "SK" in cst_static CFR4 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma3 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR4 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma3 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR4 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma3 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR4 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma3 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR4 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma3 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR4 Hs Hn; clear Hs end.
  pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _).
  rewrite unsigned_lit in ST4 by wp_lia.
  pose proof RNG_A4_1 as (P0_A4_1 & _ & _ & PC_A4_1 & _).
  pose proof RNG_A4_2 as (P0_A4_2 & _ & _ & PC_A4_2 & _).
  assert (FUc4 : (f <= f4 + 19)%nat) by (clear - FU4 FUc3; lia).
  change (Z.to_nat 16) with 16%nat in BC4_0, BC4_1.
  change (Z.to_nat 40) with 40%nat in BC4_0, BC4_1.
  pose (LBc4 := (q4_2, A4_2, 40) :: (q4_1, A4_1, 16) :: LBc3). pose (Lc4 := (q4_2, 40) :: (q4_1, 16) :: Lc3).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc4 s_ ms_ Q_) end.
  assert (GRc4 : cgrow L Lc4 18 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc3 GR4)| wp_wnorm; wp_lia..]).
  assert (IN_A4_2 : In (q4_2, A4_2, 40) LBc4) by (left; reflexivity).
  assert (IN_A4_1 : In (q4_1, A4_1, 16) LBc4) by (do 1 right; left; reflexivity).
  wp_box1 BC4_0.
  wp_box1 BC4_1.
  pose proof (conj IN_A4_2 (conj IN_A4_1 (conj BC4_0 BC4_1))) as PK4. clear CSTa3 CFR4 FU4 GR4 FUc3 GRc3 f3 IN_A4_2 IN_A4_1 BC4_0 BC4_1.
  try (clear u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfb0, 0x32dfb8)]%Z mb4) as MU4. pose proof (wmono_refl usegs mb4) as WM4.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma4 end.
  assert (CSTa4 : cstate st4 LBc4 LB Lc4 ma4 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb4 ma4 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST4| exact MU4| exact WM4| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF4 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st4 LBc4 Lc4 mb4 st4 LBc4 Lc4 ma4).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU4| exact WM4| exact HP4| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST4 HP4 ST4 MI4 MU4 WM4. try clear errv4.
  clear P0_A4_1 PC_A4_1 RNG_A4_1 P0_A4_2 PC_A4_2 RNG_A4_2.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_rand_ctx_new_spec HB_crypto_zalloc_stmt HB_crypto_malloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc4)| wp_wnorm; wp_lia..]| exact CSTa4| rewrite unsigned_lit by wp_lia; unfold ossl_rand_ctx_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia| wp_cells| wp_cells| wp_cells]. }
  intros f5 L5 st5 ms5 (v5 & mb5 & LB5 & RET5 & FU5 & GR5 & CST5 & FRM5 & (q5_1 & A5_1 & q5_2 & A5_2 & q5_3 & A5_3 & -> & -> & -> & RNG_A5_1 & RNG_A5_2 & RNG_A5_3 & BC5_0 & BC5_1 & BC5_2)).
  destruct RET5 as (u0_5 & u1_5 & u2_5 & b1_5 & b2_5 & b3_5 & b4_5 & b5_5 & b6_5 & b7_5 & u3_5 & u4_5 & u5_5 & u6_5 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM5 by wp_lia.
  pose proof FRM5 as (CFR5 & _).
  lazymatch goal with FRh : rw_cells _ ma4 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 FRh ltac:(wp_lia)) as FRs5; clear FRh end.
  try match goal with Hs : rw_cells _ ma4 0x32de28 _ |- _ => clear Hs end.
  try match goal with Hs : rw_cells _ ma4 0x32de40 _ |- _ => clear Hs end.
  try match goal with Hs : rw_cells _ ma4 0x32de80 _ |- _ => clear Hs end.
  match goal with Hs : rw_cells _ ma4 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR5 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma4 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR5 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma4 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR5 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma4 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR5 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma4 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR5 Hs Hn; clear Hs end.
  pose proof CST5 as (HP5 & _ & (errv5 & _ & _ & ST5 & _ & _ & MI5 & _) & _).
  rewrite unsigned_lit in ST5 by wp_lia.
  pose proof RNG_A5_1 as (P0_A5_1 & _ & _ & PC_A5_1 & _).
  pose proof RNG_A5_2 as (P0_A5_2 & _ & _ & PC_A5_2 & _).
  pose proof RNG_A5_3 as (P0_A5_3 & _ & _ & PC_A5_3 & _).
  assert (FUc5 : (f <= f5 + 22)%nat) by (clear - FU5 FUc4; lia).
  change (Z.to_nat 5) with 5%nat in BC5_0, BC5_1, BC5_2.
  change (Z.to_nat 40) with 40%nat in BC5_0, BC5_1, BC5_2.
  change (Z.to_nat 88) with 88%nat in BC5_0, BC5_1, BC5_2.
  pose (LBc5 := (q5_3, A5_3, 40) :: (q5_2, A5_2, 5) :: (q5_1, A5_1, 88) :: LBc4). pose (Lc5 := (q5_3, 40) :: (q5_2, 5) :: (q5_1, 88) :: Lc4).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc5 s_ ms_ Q_) end.
  assert (GRc5 : cgrow L Lc5 21 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc4 GR5)| wp_wnorm; wp_lia..]).
  assert (IN_A5_3 : In (q5_3, A5_3, 40) LBc5) by (left; reflexivity).
  assert (IN_A5_2 : In (q5_2, A5_2, 5) LBc5) by (do 1 right; left; reflexivity).
  assert (IN_A5_1 : In (q5_1, A5_1, 88) LBc5) by (do 2 right; left; reflexivity).
  wp_box1 BC5_0.
  wp_box1 BC5_1.
  wp_box1 BC5_2.
  pose proof (conj IN_A5_3 (conj IN_A5_2 (conj IN_A5_1 (conj BC5_0 (conj BC5_1 BC5_2))))) as PK5. clear CSTa4 CFR5 FU5 GR5 FUc4 GRc4 f4 IN_A5_3 IN_A5_2 IN_A5_1 BC5_0 BC5_1 BC5_2.
  try (clear u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfa0, 0x32dfa8)]%Z mb5) as MU5. pose proof (wmono_refl usegs mb5) as WM5.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma5 end.
  assert (CSTa5 : cstate st5 LBc5 LB Lc5 ma5 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb5 ma5 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST5| exact MU5| exact WM5| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF5 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st5 LBc5 Lc5 mb5 st5 LBc5 Lc5 ma5).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU5| exact WM5| exact HP5| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST5 HP5 ST5 MI5 MU5 WM5. try clear errv5.
  clear P0_A5_1 PC_A5_1 RNG_A5_1 P0_A5_2 PC_A5_2 RNG_A5_2 P0_A5_3 PC_A5_3 RNG_A5_3.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_method_store_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc5)| wp_wnorm; wp_lia..]| exact CSTa5| rewrite unsigned_lit by wp_lia; unfold ossl_method_store_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f6 L6 st6 ms6 (v6 & mb6 & LB6 & RET6 & FU6 & GR6 & CST6 & FRM6 & (q6_1 & A6_1 & q6_2 & A6_2 & q6_3 & A6_3 & q6_4 & A6_4 & q6_5 & A6_5 & q6_6 & A6_6 & q6_7 & A6_7 & q6_8 & A6_8 & q6_9 & A6_9 & q6_10 & A6_10 & q6_11 & A6_11 & q6_12 & A6_12 & q6_13 & A6_13 & q6_14 & A6_14 & q6_15 & A6_15 & -> & -> & -> & RNG_A6_1 & RNG_A6_2 & RNG_A6_3 & RNG_A6_4 & RNG_A6_5 & RNG_A6_6 & RNG_A6_7 & RNG_A6_8 & RNG_A6_9 & RNG_A6_10 & RNG_A6_11 & RNG_A6_12 & RNG_A6_13 & RNG_A6_14 & RNG_A6_15 & BC6_0 & BC6_1 & BC6_2 & BC6_3 & BC6_4 & BC6_5 & BC6_6 & BC6_7 & BC6_8 & BC6_9 & BC6_10 & BC6_11 & BC6_12 & BC6_13 & BC6_14)).
  destruct RET6 as (u0_6 & u1_6 & u2_6 & b1_6 & b2_6 & b3_6 & b4_6 & b5_6 & b6_6 & b7_6 & u3_6 & u4_6 & u5_6 & u6_6 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM6 by wp_lia.
  pose proof FRM6 as (CFR6 & _).
  lazymatch goal with FRh : rw_cells _ ma5 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR6 FRh ltac:(wp_lia)) as FRs6; clear FRh end.
  match goal with Hs : rw_cells _ ma5 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR6 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma5 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR6 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma5 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR6 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma5 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR6 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma5 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR6 Hs Hn; clear Hs end.
  pose proof CST6 as (HP6 & _ & (errv6 & _ & _ & ST6 & _ & _ & MI6 & _) & _).
  rewrite unsigned_lit in ST6 by wp_lia.
  pose proof RNG_A6_1 as (P0_A6_1 & _ & _ & PC_A6_1 & _).
  pose proof RNG_A6_2 as (P0_A6_2 & _ & _ & PC_A6_2 & _).
  pose proof RNG_A6_3 as (P0_A6_3 & _ & _ & PC_A6_3 & _).
  pose proof RNG_A6_4 as (P0_A6_4 & _ & _ & PC_A6_4 & _).
  pose proof RNG_A6_5 as (P0_A6_5 & _ & _ & PC_A6_5 & _).
  pose proof RNG_A6_6 as (P0_A6_6 & _ & _ & PC_A6_6 & _).
  pose proof RNG_A6_7 as (P0_A6_7 & _ & _ & PC_A6_7 & _).
  pose proof RNG_A6_8 as (P0_A6_8 & _ & _ & PC_A6_8 & _).
  pose proof RNG_A6_9 as (P0_A6_9 & _ & _ & PC_A6_9 & _).
  pose proof RNG_A6_10 as (P0_A6_10 & _ & _ & PC_A6_10 & _).
  pose proof RNG_A6_11 as (P0_A6_11 & _ & _ & PC_A6_11 & _).
  pose proof RNG_A6_12 as (P0_A6_12 & _ & _ & PC_A6_12 & _).
  pose proof RNG_A6_13 as (P0_A6_13 & _ & _ & PC_A6_13 & _).
  pose proof RNG_A6_14 as (P0_A6_14 & _ & _ & PC_A6_14 & _).
  pose proof RNG_A6_15 as (P0_A6_15 & _ & _ & PC_A6_15 & _).
  assert (FUc6 : (f <= f6 + 37)%nat) by (clear - FU6 FUc5; lia).
  change (Z.to_nat 24) with 24%nat in BC6_0, BC6_1, BC6_2, BC6_3, BC6_4, BC6_5, BC6_6, BC6_7, BC6_8, BC6_9, BC6_10, BC6_11, BC6_12, BC6_13, BC6_14.
  change (Z.to_nat 32) with 32%nat in BC6_0, BC6_1, BC6_2, BC6_3, BC6_4, BC6_5, BC6_6, BC6_7, BC6_8, BC6_9, BC6_10, BC6_11, BC6_12, BC6_13, BC6_14.
  change (Z.to_nat 40) with 40%nat in BC6_0, BC6_1, BC6_2, BC6_3, BC6_4, BC6_5, BC6_6, BC6_7, BC6_8, BC6_9, BC6_10, BC6_11, BC6_12, BC6_13, BC6_14.
  change (Z.to_nat 384) with 384%nat in BC6_0, BC6_1, BC6_2, BC6_3, BC6_4, BC6_5, BC6_6, BC6_7, BC6_8, BC6_9, BC6_10, BC6_11, BC6_12, BC6_13, BC6_14.
  pose (LBc6 := (q6_15, A6_15, 40) :: (q6_14, A6_14, 40) :: (q6_13, A6_13, 40) :: (q6_12, A6_12, 32) :: (q6_11, A6_11, 40) :: (q6_10, A6_10, 40) :: (q6_9, A6_9, 32) :: (q6_8, A6_8, 40) :: (q6_7, A6_7, 40) :: (q6_6, A6_6, 32) :: (q6_5, A6_5, 40) :: (q6_4, A6_4, 40) :: (q6_3, A6_3, 32) :: (q6_2, A6_2, 384) :: (q6_1, A6_1, 24) :: LBc5). pose (Lc6 := (q6_15, 40) :: (q6_14, 40) :: (q6_13, 40) :: (q6_12, 32) :: (q6_11, 40) :: (q6_10, 40) :: (q6_9, 32) :: (q6_8, 40) :: (q6_7, 40) :: (q6_6, 32) :: (q6_5, 40) :: (q6_4, 40) :: (q6_3, 32) :: (q6_2, 384) :: (q6_1, 24) :: Lc5).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc6 s_ ms_ Q_) end.
  assert (GRc6 : cgrow L Lc6 35 2 17152) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc5 GR6)| wp_wnorm; wp_lia..]).
  assert (IN_A6_15 : In (q6_15, A6_15, 40) LBc6) by (left; reflexivity).
  assert (IN_A6_14 : In (q6_14, A6_14, 40) LBc6) by (do 1 right; left; reflexivity).
  assert (IN_A6_13 : In (q6_13, A6_13, 40) LBc6) by (do 2 right; left; reflexivity).
  assert (IN_A6_12 : In (q6_12, A6_12, 32) LBc6) by (do 3 right; left; reflexivity).
  assert (IN_A6_11 : In (q6_11, A6_11, 40) LBc6) by (do 4 right; left; reflexivity).
  assert (IN_A6_10 : In (q6_10, A6_10, 40) LBc6) by (do 5 right; left; reflexivity).
  assert (IN_A6_9 : In (q6_9, A6_9, 32) LBc6) by (do 6 right; left; reflexivity).
  assert (IN_A6_8 : In (q6_8, A6_8, 40) LBc6) by (do 7 right; left; reflexivity).
  assert (IN_A6_7 : In (q6_7, A6_7, 40) LBc6) by (do 8 right; left; reflexivity).
  assert (IN_A6_6 : In (q6_6, A6_6, 32) LBc6) by (do 9 right; left; reflexivity).
  assert (IN_A6_5 : In (q6_5, A6_5, 40) LBc6) by (do 10 right; left; reflexivity).
  assert (IN_A6_4 : In (q6_4, A6_4, 40) LBc6) by (do 11 right; left; reflexivity).
  assert (IN_A6_3 : In (q6_3, A6_3, 32) LBc6) by (do 12 right; left; reflexivity).
  assert (IN_A6_2 : In (q6_2, A6_2, 384) LBc6) by (do 13 right; left; reflexivity).
  assert (IN_A6_1 : In (q6_1, A6_1, 24) LBc6) by (do 14 right; left; reflexivity).
  wp_box1 BC6_0.
  wp_box1 BC6_1.
  wp_box1 BC6_2.
  wp_box1 BC6_3.
  wp_box1 BC6_4.
  wp_box1 BC6_5.
  wp_box1 BC6_6.
  wp_box1 BC6_7.
  wp_box1 BC6_8.
  wp_box1 BC6_9.
  wp_box1 BC6_10.
  wp_box1 BC6_11.
  wp_box1 BC6_12.
  wp_box1 BC6_13.
  wp_box1 BC6_14.
  pose proof (conj IN_A6_15 (conj IN_A6_14 (conj IN_A6_13 (conj IN_A6_12 (conj IN_A6_11 (conj IN_A6_10 (conj IN_A6_9 (conj IN_A6_8 (conj IN_A6_7 (conj IN_A6_6 (conj IN_A6_5 (conj IN_A6_4 (conj IN_A6_3 (conj IN_A6_2 (conj IN_A6_1 (conj BC6_0 (conj BC6_1 (conj BC6_2 (conj BC6_3 (conj BC6_4 (conj BC6_5 (conj BC6_6 (conj BC6_7 (conj BC6_8 (conj BC6_9 (conj BC6_10 (conj BC6_11 (conj BC6_12 (conj BC6_13 BC6_14))))))))))))))))))))))))))))) as PK6. clear CSTa5 CFR6 FU6 GR6 FUc5 GRc5 f5 IN_A6_15 IN_A6_14 IN_A6_13 IN_A6_12 IN_A6_11 IN_A6_10 IN_A6_9 IN_A6_8 IN_A6_7 IN_A6_6 IN_A6_5 IN_A6_4 IN_A6_3 IN_A6_2 IN_A6_1 BC6_0 BC6_1 BC6_2 BC6_3 BC6_4 BC6_5 BC6_6 BC6_7 BC6_8 BC6_9 BC6_10 BC6_11 BC6_12 BC6_13 BC6_14.
  try (clear u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfc8, 0x32dfd0)]%Z mb6) as MU6. pose proof (wmono_refl usegs mb6) as WM6.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma6 end.
  assert (CSTa6 : cstate st6 LBc6 LB Lc6 ma6 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb6 ma6 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST6| exact MU6| exact WM6| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF6 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st6 LBc6 Lc6 mb6 st6 LBc6 Lc6 ma6).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU6| exact WM6| exact HP6| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST6 HP6 ST6 MI6 MU6 WM6. try clear errv6.
  clear P0_A6_1 PC_A6_1 RNG_A6_1 P0_A6_2 PC_A6_2 RNG_A6_2 P0_A6_3 PC_A6_3 RNG_A6_3 P0_A6_4 PC_A6_4 RNG_A6_4 P0_A6_5 PC_A6_5 RNG_A6_5 P0_A6_6 PC_A6_6 RNG_A6_6 P0_A6_7 PC_A6_7 RNG_A6_7 P0_A6_8 PC_A6_8 RNG_A6_8 P0_A6_9 PC_A6_9 RNG_A6_9 P0_A6_10 PC_A6_10 RNG_A6_10 P0_A6_11 PC_A6_11 RNG_A6_11 P0_A6_12 PC_A6_12 RNG_A6_12 P0_A6_13 PC_A6_13 RNG_A6_13 P0_A6_14 PC_A6_14 RNG_A6_14 P0_A6_15 PC_A6_15 RNG_A6_15.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_decoder_cache_new_fp_spec HB_crypto_malloc_stmt HB_T_lock_new_stmt HB_lh_new_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc6)| wp_wnorm; wp_lia..]| exact CSTa6| rewrite unsigned_lit by wp_lia; unfold DCN_STACK, LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f7 L7 st7 ms7 (v7 & mb7 & LB7 & RET7 & FU7 & GR7 & CST7 & FRM7 & (q7_1 & q7_2 & q7_3 & q7_4 & A7_1 & A7_2 & A7_3 & A7_4 & -> & -> & -> & RNG_A7_1 & RNG_A7_2 & RNG_A7_3 & RNG_A7_4)).
  destruct RET7 as (u0_7 & u1_7 & u2_7 & b1_7 & b2_7 & b3_7 & b4_7 & b5_7 & b6_7 & b7_7 & u3_7 & u4_7 & u5_7 & u6_7 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM7 by wp_lia.
  pose proof FRM7 as (CFR7 & _).
  lazymatch goal with FRh : rw_cells _ ma6 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR7 FRh ltac:(wp_lia)) as FRs7; clear FRh end.
  match goal with Hs : rw_cells _ ma6 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR7 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma6 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR7 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma6 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR7 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma6 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR7 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma6 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR7 Hs Hn; clear Hs end.
  pose proof CST7 as (HP7 & _ & (errv7 & _ & _ & ST7 & _ & _ & MI7 & _) & _).
  rewrite unsigned_lit in ST7 by wp_lia.
  pose proof RNG_A7_1 as (P0_A7_1 & _ & _ & PC_A7_1 & _).
  pose proof RNG_A7_2 as (P0_A7_2 & _ & _ & PC_A7_2 & _).
  pose proof RNG_A7_3 as (P0_A7_3 & _ & _ & PC_A7_3 & _).
  pose proof RNG_A7_4 as (P0_A7_4 & _ & _ & PC_A7_4 & _).
  assert (FUc7 : (f <= f7 + 41)%nat) by (clear - FU7 FUc6; lia).
  change (Z.to_nat 16) with 16%nat in |-.
  change (Z.to_nat 40) with 40%nat in |-.
  change (Z.to_nat 104) with 104%nat in |-.
  change (Z.to_nat 128) with 128%nat in |-.
  pose (LBc7 := (q7_4, A7_4, 128) :: (q7_3, A7_3, 104) :: (q7_2, A7_2, 40) :: (q7_1, A7_1, 16) :: LBc6). pose (Lc7 := (q7_4, 128) :: (q7_3, 104) :: (q7_2, 40) :: (q7_1, 16) :: Lc6).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc7 s_ ms_ Q_) end.
  assert (GRc7 : cgrow L Lc7 39 2 17152) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc6 GR7)| wp_wnorm; wp_lia..]).
  assert (IN_A7_4 : In (q7_4, A7_4, 128) LBc7) by (left; reflexivity).
  assert (IN_A7_3 : In (q7_3, A7_3, 104) LBc7) by (do 1 right; left; reflexivity).
  assert (IN_A7_2 : In (q7_2, A7_2, 40) LBc7) by (do 2 right; left; reflexivity).
  assert (IN_A7_1 : In (q7_1, A7_1, 16) LBc7) by (do 3 right; left; reflexivity).
  pose proof (conj IN_A7_4 (conj IN_A7_3 (conj IN_A7_2 IN_A7_1))) as PK7. clear CSTa6 CFR7 FU7 GR7 FUc6 GRc6 f6 IN_A7_4 IN_A7_3 IN_A7_2 IN_A7_1.
  try (clear u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfd0, 0x32dfd8)]%Z mb7) as MU7. pose proof (wmono_refl usegs mb7) as WM7.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma7 end.
  assert (CSTa7 : cstate st7 LBc7 LB Lc7 ma7 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb7 ma7 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST7| exact MU7| exact WM7| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF7 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st7 LBc7 Lc7 mb7 st7 LBc7 Lc7 ma7).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU7| exact WM7| exact HP7| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST7 HP7 ST7 MI7 MU7 WM7. try clear errv7.
  clear P0_A7_1 PC_A7_1 RNG_A7_1 P0_A7_2 PC_A7_2 RNG_A7_2 P0_A7_3 PC_A7_3 RNG_A7_3 P0_A7_4 PC_A7_4 RNG_A7_4.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_method_store_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc7)| wp_wnorm; wp_lia..]| exact CSTa7| rewrite unsigned_lit by wp_lia; unfold ossl_method_store_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f8 L8 st8 ms8 (v8 & mb8 & LB8 & RET8 & FU8 & GR8 & CST8 & FRM8 & (q8_1 & A8_1 & q8_2 & A8_2 & q8_3 & A8_3 & q8_4 & A8_4 & q8_5 & A8_5 & q8_6 & A8_6 & q8_7 & A8_7 & q8_8 & A8_8 & q8_9 & A8_9 & q8_10 & A8_10 & q8_11 & A8_11 & q8_12 & A8_12 & q8_13 & A8_13 & q8_14 & A8_14 & q8_15 & A8_15 & -> & -> & -> & RNG_A8_1 & RNG_A8_2 & RNG_A8_3 & RNG_A8_4 & RNG_A8_5 & RNG_A8_6 & RNG_A8_7 & RNG_A8_8 & RNG_A8_9 & RNG_A8_10 & RNG_A8_11 & RNG_A8_12 & RNG_A8_13 & RNG_A8_14 & RNG_A8_15 & BC8_0 & BC8_1 & BC8_2 & BC8_3 & BC8_4 & BC8_5 & BC8_6 & BC8_7 & BC8_8 & BC8_9 & BC8_10 & BC8_11 & BC8_12 & BC8_13 & BC8_14)).
  destruct RET8 as (u0_8 & u1_8 & u2_8 & b1_8 & b2_8 & b3_8 & b4_8 & b5_8 & b6_8 & b7_8 & u3_8 & u4_8 & u5_8 & u6_8 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM8 by wp_lia.
  pose proof FRM8 as (CFR8 & _).
  lazymatch goal with FRh : rw_cells _ ma7 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR8 FRh ltac:(wp_lia)) as FRs8; clear FRh end.
  match goal with Hs : rw_cells _ ma7 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR8 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma7 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR8 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma7 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR8 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma7 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR8 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma7 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR8 Hs Hn; clear Hs end.
  pose proof CST8 as (HP8 & _ & (errv8 & _ & _ & ST8 & _ & _ & MI8 & _) & _).
  rewrite unsigned_lit in ST8 by wp_lia.
  pose proof RNG_A8_1 as (P0_A8_1 & _ & _ & PC_A8_1 & _).
  pose proof RNG_A8_2 as (P0_A8_2 & _ & _ & PC_A8_2 & _).
  pose proof RNG_A8_3 as (P0_A8_3 & _ & _ & PC_A8_3 & _).
  pose proof RNG_A8_4 as (P0_A8_4 & _ & _ & PC_A8_4 & _).
  pose proof RNG_A8_5 as (P0_A8_5 & _ & _ & PC_A8_5 & _).
  pose proof RNG_A8_6 as (P0_A8_6 & _ & _ & PC_A8_6 & _).
  pose proof RNG_A8_7 as (P0_A8_7 & _ & _ & PC_A8_7 & _).
  pose proof RNG_A8_8 as (P0_A8_8 & _ & _ & PC_A8_8 & _).
  pose proof RNG_A8_9 as (P0_A8_9 & _ & _ & PC_A8_9 & _).
  pose proof RNG_A8_10 as (P0_A8_10 & _ & _ & PC_A8_10 & _).
  pose proof RNG_A8_11 as (P0_A8_11 & _ & _ & PC_A8_11 & _).
  pose proof RNG_A8_12 as (P0_A8_12 & _ & _ & PC_A8_12 & _).
  pose proof RNG_A8_13 as (P0_A8_13 & _ & _ & PC_A8_13 & _).
  pose proof RNG_A8_14 as (P0_A8_14 & _ & _ & PC_A8_14 & _).
  pose proof RNG_A8_15 as (P0_A8_15 & _ & _ & PC_A8_15 & _).
  assert (FUc8 : (f <= f8 + 56)%nat) by (clear - FU8 FUc7; lia).
  change (Z.to_nat 24) with 24%nat in BC8_0, BC8_1, BC8_2, BC8_3, BC8_4, BC8_5, BC8_6, BC8_7, BC8_8, BC8_9, BC8_10, BC8_11, BC8_12, BC8_13, BC8_14.
  change (Z.to_nat 32) with 32%nat in BC8_0, BC8_1, BC8_2, BC8_3, BC8_4, BC8_5, BC8_6, BC8_7, BC8_8, BC8_9, BC8_10, BC8_11, BC8_12, BC8_13, BC8_14.
  change (Z.to_nat 40) with 40%nat in BC8_0, BC8_1, BC8_2, BC8_3, BC8_4, BC8_5, BC8_6, BC8_7, BC8_8, BC8_9, BC8_10, BC8_11, BC8_12, BC8_13, BC8_14.
  change (Z.to_nat 384) with 384%nat in BC8_0, BC8_1, BC8_2, BC8_3, BC8_4, BC8_5, BC8_6, BC8_7, BC8_8, BC8_9, BC8_10, BC8_11, BC8_12, BC8_13, BC8_14.
  pose (LBc8 := (q8_15, A8_15, 40) :: (q8_14, A8_14, 40) :: (q8_13, A8_13, 40) :: (q8_12, A8_12, 32) :: (q8_11, A8_11, 40) :: (q8_10, A8_10, 40) :: (q8_9, A8_9, 32) :: (q8_8, A8_8, 40) :: (q8_7, A8_7, 40) :: (q8_6, A8_6, 32) :: (q8_5, A8_5, 40) :: (q8_4, A8_4, 40) :: (q8_3, A8_3, 32) :: (q8_2, A8_2, 384) :: (q8_1, A8_1, 24) :: LBc7). pose (Lc8 := (q8_15, 40) :: (q8_14, 40) :: (q8_13, 40) :: (q8_12, 32) :: (q8_11, 40) :: (q8_10, 40) :: (q8_9, 32) :: (q8_8, 40) :: (q8_7, 40) :: (q8_6, 32) :: (q8_5, 40) :: (q8_4, 40) :: (q8_3, 32) :: (q8_2, 384) :: (q8_1, 24) :: Lc7).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc8 s_ ms_ Q_) end.
  assert (GRc8 : cgrow L Lc8 53 3 25728) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc7 GR8)| wp_wnorm; wp_lia..]).
  assert (IN_A8_15 : In (q8_15, A8_15, 40) LBc8) by (left; reflexivity).
  assert (IN_A8_14 : In (q8_14, A8_14, 40) LBc8) by (do 1 right; left; reflexivity).
  assert (IN_A8_13 : In (q8_13, A8_13, 40) LBc8) by (do 2 right; left; reflexivity).
  assert (IN_A8_12 : In (q8_12, A8_12, 32) LBc8) by (do 3 right; left; reflexivity).
  assert (IN_A8_11 : In (q8_11, A8_11, 40) LBc8) by (do 4 right; left; reflexivity).
  assert (IN_A8_10 : In (q8_10, A8_10, 40) LBc8) by (do 5 right; left; reflexivity).
  assert (IN_A8_9 : In (q8_9, A8_9, 32) LBc8) by (do 6 right; left; reflexivity).
  assert (IN_A8_8 : In (q8_8, A8_8, 40) LBc8) by (do 7 right; left; reflexivity).
  assert (IN_A8_7 : In (q8_7, A8_7, 40) LBc8) by (do 8 right; left; reflexivity).
  assert (IN_A8_6 : In (q8_6, A8_6, 32) LBc8) by (do 9 right; left; reflexivity).
  assert (IN_A8_5 : In (q8_5, A8_5, 40) LBc8) by (do 10 right; left; reflexivity).
  assert (IN_A8_4 : In (q8_4, A8_4, 40) LBc8) by (do 11 right; left; reflexivity).
  assert (IN_A8_3 : In (q8_3, A8_3, 32) LBc8) by (do 12 right; left; reflexivity).
  assert (IN_A8_2 : In (q8_2, A8_2, 384) LBc8) by (do 13 right; left; reflexivity).
  assert (IN_A8_1 : In (q8_1, A8_1, 24) LBc8) by (do 14 right; left; reflexivity).
  wp_box1 BC8_0.
  wp_box1 BC8_1.
  wp_box1 BC8_2.
  wp_box1 BC8_3.
  wp_box1 BC8_4.
  wp_box1 BC8_5.
  wp_box1 BC8_6.
  wp_box1 BC8_7.
  wp_box1 BC8_8.
  wp_box1 BC8_9.
  wp_box1 BC8_10.
  wp_box1 BC8_11.
  wp_box1 BC8_12.
  wp_box1 BC8_13.
  wp_box1 BC8_14.
  pose proof (conj IN_A8_15 (conj IN_A8_14 (conj IN_A8_13 (conj IN_A8_12 (conj IN_A8_11 (conj IN_A8_10 (conj IN_A8_9 (conj IN_A8_8 (conj IN_A8_7 (conj IN_A8_6 (conj IN_A8_5 (conj IN_A8_4 (conj IN_A8_3 (conj IN_A8_2 (conj IN_A8_1 (conj BC8_0 (conj BC8_1 (conj BC8_2 (conj BC8_3 (conj BC8_4 (conj BC8_5 (conj BC8_6 (conj BC8_7 (conj BC8_8 (conj BC8_9 (conj BC8_10 (conj BC8_11 (conj BC8_12 (conj BC8_13 BC8_14))))))))))))))))))))))))))))) as PK8. clear CSTa7 CFR8 FU8 GR8 FUc7 GRc7 f7 IN_A8_15 IN_A8_14 IN_A8_13 IN_A8_12 IN_A8_11 IN_A8_10 IN_A8_9 IN_A8_8 IN_A8_7 IN_A8_6 IN_A8_5 IN_A8_4 IN_A8_3 IN_A8_2 IN_A8_1 BC8_0 BC8_1 BC8_2 BC8_3 BC8_4 BC8_5 BC8_6 BC8_7 BC8_8 BC8_9 BC8_10 BC8_11 BC8_12 BC8_13 BC8_14.
  try (clear u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfd8, 0x32dfe0)]%Z mb8) as MU8. pose proof (wmono_refl usegs mb8) as WM8.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma8 end.
  assert (CSTa8 : cstate st8 LBc8 LB Lc8 ma8 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb8 ma8 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST8| exact MU8| exact WM8| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF8 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st8 LBc8 Lc8 mb8 st8 LBc8 Lc8 ma8).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU8| exact WM8| exact HP8| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST8 HP8 ST8 MI8 MU8 WM8. try clear errv8.
  clear P0_A8_1 PC_A8_1 RNG_A8_1 P0_A8_2 PC_A8_2 RNG_A8_2 P0_A8_3 PC_A8_3 RNG_A8_3 P0_A8_4 PC_A8_4 RNG_A8_4 P0_A8_5 PC_A8_5 RNG_A8_5 P0_A8_6 PC_A8_6 RNG_A8_6 P0_A8_7 PC_A8_7 RNG_A8_7 P0_A8_8 PC_A8_8 RNG_A8_8 P0_A8_9 PC_A8_9 RNG_A8_9 P0_A8_10 PC_A8_10 RNG_A8_10 P0_A8_11 PC_A8_11 RNG_A8_11 P0_A8_12 PC_A8_12 RNG_A8_12 P0_A8_13 PC_A8_13 RNG_A8_13 P0_A8_14 PC_A8_14 RNG_A8_14 P0_A8_15 PC_A8_15 RNG_A8_15.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_method_store_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc8)| wp_wnorm; wp_lia..]| exact CSTa8| rewrite unsigned_lit by wp_lia; unfold ossl_method_store_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f9 L9 st9 ms9 (v9 & mb9 & LB9 & RET9 & FU9 & GR9 & CST9 & FRM9 & (q9_1 & A9_1 & q9_2 & A9_2 & q9_3 & A9_3 & q9_4 & A9_4 & q9_5 & A9_5 & q9_6 & A9_6 & q9_7 & A9_7 & q9_8 & A9_8 & q9_9 & A9_9 & q9_10 & A9_10 & q9_11 & A9_11 & q9_12 & A9_12 & q9_13 & A9_13 & q9_14 & A9_14 & q9_15 & A9_15 & -> & -> & -> & RNG_A9_1 & RNG_A9_2 & RNG_A9_3 & RNG_A9_4 & RNG_A9_5 & RNG_A9_6 & RNG_A9_7 & RNG_A9_8 & RNG_A9_9 & RNG_A9_10 & RNG_A9_11 & RNG_A9_12 & RNG_A9_13 & RNG_A9_14 & RNG_A9_15 & BC9_0 & BC9_1 & BC9_2 & BC9_3 & BC9_4 & BC9_5 & BC9_6 & BC9_7 & BC9_8 & BC9_9 & BC9_10 & BC9_11 & BC9_12 & BC9_13 & BC9_14)).
  destruct RET9 as (u0_9 & u1_9 & u2_9 & b1_9 & b2_9 & b3_9 & b4_9 & b5_9 & b6_9 & b7_9 & u3_9 & u4_9 & u5_9 & u6_9 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM9 by wp_lia.
  pose proof FRM9 as (CFR9 & _).
  lazymatch goal with FRh : rw_cells _ ma8 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR9 FRh ltac:(wp_lia)) as FRs9; clear FRh end.
  match goal with Hs : rw_cells _ ma8 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR9 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma8 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR9 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma8 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR9 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma8 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR9 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma8 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR9 Hs Hn; clear Hs end.
  pose proof CST9 as (HP9 & _ & (errv9 & _ & _ & ST9 & _ & _ & MI9 & _) & _).
  rewrite unsigned_lit in ST9 by wp_lia.
  pose proof RNG_A9_1 as (P0_A9_1 & _ & _ & PC_A9_1 & _).
  pose proof RNG_A9_2 as (P0_A9_2 & _ & _ & PC_A9_2 & _).
  pose proof RNG_A9_3 as (P0_A9_3 & _ & _ & PC_A9_3 & _).
  pose proof RNG_A9_4 as (P0_A9_4 & _ & _ & PC_A9_4 & _).
  pose proof RNG_A9_5 as (P0_A9_5 & _ & _ & PC_A9_5 & _).
  pose proof RNG_A9_6 as (P0_A9_6 & _ & _ & PC_A9_6 & _).
  pose proof RNG_A9_7 as (P0_A9_7 & _ & _ & PC_A9_7 & _).
  pose proof RNG_A9_8 as (P0_A9_8 & _ & _ & PC_A9_8 & _).
  pose proof RNG_A9_9 as (P0_A9_9 & _ & _ & PC_A9_9 & _).
  pose proof RNG_A9_10 as (P0_A9_10 & _ & _ & PC_A9_10 & _).
  pose proof RNG_A9_11 as (P0_A9_11 & _ & _ & PC_A9_11 & _).
  pose proof RNG_A9_12 as (P0_A9_12 & _ & _ & PC_A9_12 & _).
  pose proof RNG_A9_13 as (P0_A9_13 & _ & _ & PC_A9_13 & _).
  pose proof RNG_A9_14 as (P0_A9_14 & _ & _ & PC_A9_14 & _).
  pose proof RNG_A9_15 as (P0_A9_15 & _ & _ & PC_A9_15 & _).
  assert (FUc9 : (f <= f9 + 71)%nat) by (clear - FU9 FUc8; lia).
  change (Z.to_nat 24) with 24%nat in BC9_0, BC9_1, BC9_2, BC9_3, BC9_4, BC9_5, BC9_6, BC9_7, BC9_8, BC9_9, BC9_10, BC9_11, BC9_12, BC9_13, BC9_14.
  change (Z.to_nat 32) with 32%nat in BC9_0, BC9_1, BC9_2, BC9_3, BC9_4, BC9_5, BC9_6, BC9_7, BC9_8, BC9_9, BC9_10, BC9_11, BC9_12, BC9_13, BC9_14.
  change (Z.to_nat 40) with 40%nat in BC9_0, BC9_1, BC9_2, BC9_3, BC9_4, BC9_5, BC9_6, BC9_7, BC9_8, BC9_9, BC9_10, BC9_11, BC9_12, BC9_13, BC9_14.
  change (Z.to_nat 384) with 384%nat in BC9_0, BC9_1, BC9_2, BC9_3, BC9_4, BC9_5, BC9_6, BC9_7, BC9_8, BC9_9, BC9_10, BC9_11, BC9_12, BC9_13, BC9_14.
  pose (LBc9 := (q9_15, A9_15, 40) :: (q9_14, A9_14, 40) :: (q9_13, A9_13, 40) :: (q9_12, A9_12, 32) :: (q9_11, A9_11, 40) :: (q9_10, A9_10, 40) :: (q9_9, A9_9, 32) :: (q9_8, A9_8, 40) :: (q9_7, A9_7, 40) :: (q9_6, A9_6, 32) :: (q9_5, A9_5, 40) :: (q9_4, A9_4, 40) :: (q9_3, A9_3, 32) :: (q9_2, A9_2, 384) :: (q9_1, A9_1, 24) :: LBc8). pose (Lc9 := (q9_15, 40) :: (q9_14, 40) :: (q9_13, 40) :: (q9_12, 32) :: (q9_11, 40) :: (q9_10, 40) :: (q9_9, 32) :: (q9_8, 40) :: (q9_7, 40) :: (q9_6, 32) :: (q9_5, 40) :: (q9_4, 40) :: (q9_3, 32) :: (q9_2, 384) :: (q9_1, 24) :: Lc8).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc9 s_ ms_ Q_) end.
  assert (GRc9 : cgrow L Lc9 67 4 34304) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc8 GR9)| wp_wnorm; wp_lia..]).
  assert (IN_A9_15 : In (q9_15, A9_15, 40) LBc9) by (left; reflexivity).
  assert (IN_A9_14 : In (q9_14, A9_14, 40) LBc9) by (do 1 right; left; reflexivity).
  assert (IN_A9_13 : In (q9_13, A9_13, 40) LBc9) by (do 2 right; left; reflexivity).
  assert (IN_A9_12 : In (q9_12, A9_12, 32) LBc9) by (do 3 right; left; reflexivity).
  assert (IN_A9_11 : In (q9_11, A9_11, 40) LBc9) by (do 4 right; left; reflexivity).
  assert (IN_A9_10 : In (q9_10, A9_10, 40) LBc9) by (do 5 right; left; reflexivity).
  assert (IN_A9_9 : In (q9_9, A9_9, 32) LBc9) by (do 6 right; left; reflexivity).
  assert (IN_A9_8 : In (q9_8, A9_8, 40) LBc9) by (do 7 right; left; reflexivity).
  assert (IN_A9_7 : In (q9_7, A9_7, 40) LBc9) by (do 8 right; left; reflexivity).
  assert (IN_A9_6 : In (q9_6, A9_6, 32) LBc9) by (do 9 right; left; reflexivity).
  assert (IN_A9_5 : In (q9_5, A9_5, 40) LBc9) by (do 10 right; left; reflexivity).
  assert (IN_A9_4 : In (q9_4, A9_4, 40) LBc9) by (do 11 right; left; reflexivity).
  assert (IN_A9_3 : In (q9_3, A9_3, 32) LBc9) by (do 12 right; left; reflexivity).
  assert (IN_A9_2 : In (q9_2, A9_2, 384) LBc9) by (do 13 right; left; reflexivity).
  assert (IN_A9_1 : In (q9_1, A9_1, 24) LBc9) by (do 14 right; left; reflexivity).
  wp_box1 BC9_0.
  wp_box1 BC9_1.
  wp_box1 BC9_2.
  wp_box1 BC9_3.
  wp_box1 BC9_4.
  wp_box1 BC9_5.
  wp_box1 BC9_6.
  wp_box1 BC9_7.
  wp_box1 BC9_8.
  wp_box1 BC9_9.
  wp_box1 BC9_10.
  wp_box1 BC9_11.
  wp_box1 BC9_12.
  wp_box1 BC9_13.
  wp_box1 BC9_14.
  pose proof (conj IN_A9_15 (conj IN_A9_14 (conj IN_A9_13 (conj IN_A9_12 (conj IN_A9_11 (conj IN_A9_10 (conj IN_A9_9 (conj IN_A9_8 (conj IN_A9_7 (conj IN_A9_6 (conj IN_A9_5 (conj IN_A9_4 (conj IN_A9_3 (conj IN_A9_2 (conj IN_A9_1 (conj BC9_0 (conj BC9_1 (conj BC9_2 (conj BC9_3 (conj BC9_4 (conj BC9_5 (conj BC9_6 (conj BC9_7 (conj BC9_8 (conj BC9_9 (conj BC9_10 (conj BC9_11 (conj BC9_12 (conj BC9_13 BC9_14))))))))))))))))))))))))))))) as PK9. clear CSTa8 CFR9 FU9 GR9 FUc8 GRc8 f8 IN_A9_15 IN_A9_14 IN_A9_13 IN_A9_12 IN_A9_11 IN_A9_10 IN_A9_9 IN_A9_8 IN_A9_7 IN_A9_6 IN_A9_5 IN_A9_4 IN_A9_3 IN_A9_2 IN_A9_1 BC9_0 BC9_1 BC9_2 BC9_3 BC9_4 BC9_5 BC9_6 BC9_7 BC9_8 BC9_9 BC9_10 BC9_11 BC9_12 BC9_13 BC9_14.
  try (clear u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfe0, 0x32dfe8)]%Z mb9) as MU9. pose proof (wmono_refl usegs mb9) as WM9.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma9 end.
  assert (CSTa9 : cstate st9 LBc9 LB Lc9 ma9 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb9 ma9 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST9| exact MU9| exact WM9| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF9 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st9 LBc9 Lc9 mb9 st9 LBc9 Lc9 ma9).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU9| exact WM9| exact HP9| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST9 HP9 ST9 MI9 MU9 WM9. try clear errv9.
  clear P0_A9_1 PC_A9_1 RNG_A9_1 P0_A9_2 PC_A9_2 RNG_A9_2 P0_A9_3 PC_A9_3 RNG_A9_3 P0_A9_4 PC_A9_4 RNG_A9_4 P0_A9_5 PC_A9_5 RNG_A9_5 P0_A9_6 PC_A9_6 RNG_A9_6 P0_A9_7 PC_A9_7 RNG_A9_7 P0_A9_8 PC_A9_8 RNG_A9_8 P0_A9_9 PC_A9_9 RNG_A9_9 P0_A9_10 PC_A9_10 RNG_A9_10 P0_A9_11 PC_A9_11 RNG_A9_11 P0_A9_12 PC_A9_12 RNG_A9_12 P0_A9_13 PC_A9_13 RNG_A9_13 P0_A9_14 PC_A9_14 RNG_A9_14 P0_A9_15 PC_A9_15 RNG_A9_15.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_provider_store_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc9)| wp_wnorm; wp_lia..]| exact CSTa9| rewrite unsigned_lit by wp_lia; unfold ossl_provider_store_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f10 L10 st10 ms10 (v10 & mb10 & LB10 & RET10 & FU10 & GR10 & CST10 & FRM10 & (q10_1 & A10_1 & q10_2 & A10_2 & q10_3 & A10_3 & q10_4 & A10_4 & q10_5 & A10_5 & -> & -> & -> & RNG_A10_1 & RNG_A10_2 & RNG_A10_3 & RNG_A10_4 & RNG_A10_5 & BC10_0 & BC10_1 & BC10_2 & BC10_3 & BC10_4)).
  destruct RET10 as (u0_10 & u1_10 & u2_10 & b1_10 & b2_10 & b3_10 & b4_10 & b5_10 & b6_10 & b7_10 & u3_10 & u4_10 & u5_10 & u6_10 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM10 by wp_lia.
  pose proof FRM10 as (CFR10 & _).
  lazymatch goal with FRh : rw_cells _ ma9 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR10 FRh ltac:(wp_lia)) as FRs10; clear FRh end.
  match goal with Hs : rw_cells _ ma9 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR10 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma9 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR10 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma9 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR10 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma9 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR10 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma9 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR10 Hs Hn; clear Hs end.
  pose proof CST10 as (HP10 & _ & (errv10 & _ & _ & ST10 & _ & _ & MI10 & _) & _).
  rewrite unsigned_lit in ST10 by wp_lia.
  pose proof RNG_A10_1 as (P0_A10_1 & _ & _ & PC_A10_1 & _).
  pose proof RNG_A10_2 as (P0_A10_2 & _ & _ & PC_A10_2 & _).
  pose proof RNG_A10_3 as (P0_A10_3 & _ & _ & PC_A10_3 & _).
  pose proof RNG_A10_4 as (P0_A10_4 & _ & _ & PC_A10_4 & _).
  pose proof RNG_A10_5 as (P0_A10_5 & _ & _ & PC_A10_5 & _).
  assert (FUc10 : (f <= f10 + 76)%nat) by (clear - FU10 FUc9; lia).
  change (Z.to_nat 40) with 40%nat in BC10_0, BC10_1, BC10_2, BC10_3, BC10_4.
  change (Z.to_nat 56) with 56%nat in BC10_0, BC10_1, BC10_2, BC10_3, BC10_4.
  change (Z.to_nat 80) with 80%nat in BC10_0, BC10_1, BC10_2, BC10_3, BC10_4.
  pose (LBc10 := (q10_5, A10_5, 40) :: (q10_4, A10_4, 56) :: (q10_3, A10_3, 40) :: (q10_2, A10_2, 56) :: (q10_1, A10_1, 80) :: LBc9). pose (Lc10 := (q10_5, 40) :: (q10_4, 56) :: (q10_3, 40) :: (q10_2, 56) :: (q10_1, 80) :: Lc9).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc10 s_ ms_ Q_) end.
  assert (GRc10 : cgrow L Lc10 72 4 34304) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc9 GR10)| wp_wnorm; wp_lia..]).
  assert (IN_A10_5 : In (q10_5, A10_5, 40) LBc10) by (left; reflexivity).
  assert (IN_A10_4 : In (q10_4, A10_4, 56) LBc10) by (do 1 right; left; reflexivity).
  assert (IN_A10_3 : In (q10_3, A10_3, 40) LBc10) by (do 2 right; left; reflexivity).
  assert (IN_A10_2 : In (q10_2, A10_2, 56) LBc10) by (do 3 right; left; reflexivity).
  assert (IN_A10_1 : In (q10_1, A10_1, 80) LBc10) by (do 4 right; left; reflexivity).
  wp_box1 BC10_0.
  wp_box1 BC10_1.
  wp_box1 BC10_2.
  wp_box1 BC10_3.
  wp_box1 BC10_4.
  pose proof (conj IN_A10_5 (conj IN_A10_4 (conj IN_A10_3 (conj IN_A10_2 (conj IN_A10_1 (conj BC10_0 (conj BC10_1 (conj BC10_2 (conj BC10_3 BC10_4))))))))) as PK10. clear CSTa9 CFR10 FU10 GR10 FUc9 GRc9 f9 IN_A10_5 IN_A10_4 IN_A10_3 IN_A10_2 IN_A10_1 BC10_0 BC10_1 BC10_2 BC10_3 BC10_4.
  try (clear u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32df80, 0x32df88)]%Z mb10) as MU10. pose proof (wmono_refl usegs mb10) as WM10.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma10 end.
  assert (CSTa10 : cstate st10 LBc10 LB Lc10 ma10 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb10 ma10 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST10| exact MU10| exact WM10| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF10 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st10 LBc10 Lc10 mb10 st10 LBc10 Lc10 ma10).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU10| exact WM10| exact HP10| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  clear CST10 HP10 ST10 MI10 MU10 WM10. try clear errv10.
  clear P0_A10_1 PC_A10_1 RNG_A10_1 P0_A10_2 PC_A10_2 RNG_A10_2 P0_A10_3 PC_A10_3 RNG_A10_3 P0_A10_4 PC_A10_4 RNG_A10_4 P0_A10_5 PC_A10_5 RNG_A10_5.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply HB_ossl_property_string_data_new_rep_stmt; [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc10)| wp_wnorm; wp_lia..]| exact CSTa10| rewrite unsigned_lit by wp_lia; unfold PSD_STACK, LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f11 L11 st11 ms11 (v11 & mb11 & LB11 & RET11 & FU11 & GR11 & CST11 & FRM11 & (q11_1 & q11_2 & q11_3 & q11_4 & q11_5 & q11_6 & q11_7 & q11_8 & A11_1 & A11_2 & A11_3 & A11_4 & A11_5 & A11_6 & A11_7 & A11_8 & -> & -> & -> & RNG_A11_1 & RNG_A11_2 & RNG_A11_3 & RNG_A11_4 & RNG_A11_5 & RNG_A11_6 & RNG_A11_7 & RNG_A11_8 & XR11_0)).
  destruct RET11 as (u0_11 & u1_11 & u2_11 & b1_11 & b2_11 & b3_11 & b4_11 & b5_11 & b6_11 & b7_11 & u3_11 & u4_11 & u5_11 & u6_11 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM11 by wp_lia.
  pose proof FRM11 as (CFR11 & _).
  lazymatch goal with FRh : rw_cells _ ma10 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR11 FRh ltac:(wp_lia)) as FRs11; clear FRh end.
  match goal with Hs : rw_cells _ ma10 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR11 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma10 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR11 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma10 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR11 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma10 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR11 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma10 0x351010 _ |- _ => let Hn := fresh "SK" in cst_static CFR11 Hs Hn; clear Hs end.
  pose proof CST11 as (HP11 & _ & (errv11 & _ & _ & ST11 & _ & _ & MI11 & _) & _).
  rewrite unsigned_lit in ST11 by wp_lia.
  pose proof RNG_A11_1 as (P0_A11_1 & _ & _ & PC_A11_1 & _).
  pose proof RNG_A11_2 as (P0_A11_2 & _ & _ & PC_A11_2 & _).
  pose proof RNG_A11_3 as (P0_A11_3 & _ & _ & PC_A11_3 & _).
  pose proof RNG_A11_4 as (P0_A11_4 & _ & _ & PC_A11_4 & _).
  pose proof RNG_A11_5 as (P0_A11_5 & _ & _ & PC_A11_5 & _).
  pose proof RNG_A11_6 as (P0_A11_6 & _ & _ & PC_A11_6 & _).
  pose proof RNG_A11_7 as (P0_A11_7 & _ & _ & PC_A11_7 & _).
  pose proof RNG_A11_8 as (P0_A11_8 & _ & _ & PC_A11_8 & _).
  assert (FUc11 : (f <= f11 + 84)%nat) by (clear - FU11 FUc10; lia).
  change (Z.to_nat 40) with 40%nat in |-.
  change (Z.to_nat 48) with 48%nat in |-.
  change (Z.to_nat 56) with 56%nat in |-.
  change (Z.to_nat 104) with 104%nat in |-.
  change (Z.to_nat 128) with 128%nat in |-.
  pose (LBc11 := (q11_8, A11_8, 56) :: (q11_7, A11_7, 56) :: (q11_6, A11_6, 128) :: (q11_5, A11_5, 104) :: (q11_4, A11_4, 128) :: (q11_3, A11_3, 104) :: (q11_2, A11_2, 40) :: (q11_1, A11_1, 48) :: LBc10). pose (Lc11 := (q11_8, 56) :: (q11_7, 56) :: (q11_6, 128) :: (q11_5, 104) :: (q11_4, 128) :: (q11_3, 104) :: (q11_2, 40) :: (q11_1, 48) :: Lc10).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc11 s_ ms_ Q_) end.
  assert (GRc11 : cgrow L Lc11 80 4 34304) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc10 GR11)| wp_wnorm; wp_lia..]).
  assert (IN_A11_8 : In (q11_8, A11_8, 56) LBc11) by (left; reflexivity).
  assert (IN_A11_7 : In (q11_7, A11_7, 56) LBc11) by (do 1 right; left; reflexivity).
  assert (IN_A11_6 : In (q11_6, A11_6, 128) LBc11) by (do 2 right; left; reflexivity).
  assert (IN_A11_5 : In (q11_5, A11_5, 104) LBc11) by (do 3 right; left; reflexivity).
  assert (IN_A11_4 : In (q11_4, A11_4, 128) LBc11) by (do 4 right; left; reflexivity).
  assert (IN_A11_3 : In (q11_3, A11_3, 104) LBc11) by (do 5 right; left; reflexivity).
  assert (IN_A11_2 : In (q11_2, A11_2, 40) LBc11) by (do 6 right; left; reflexivity).
  assert (IN_A11_1 : In (q11_1, A11_1, 48) LBc11) by (do 7 right; left; reflexivity).
  pose proof (conj IN_A11_8 (conj IN_A11_7 (conj IN_A11_6 (conj IN_A11_5 (conj IN_A11_4 (conj IN_A11_3 (conj IN_A11_2 IN_A11_1))))))) as PK11. clear CSTa10 CFR11 FU11 GR11 FUc10 GRc10 f10 IN_A11_8 IN_A11_7 IN_A11_6 IN_A11_5 IN_A11_4 IN_A11_3 IN_A11_2 IN_A11_1.
  try (clear u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32df70, 0x32df78)]%Z mb11) as MU11. pose proof (wmono_refl usegs mb11) as WM11.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma11 end.
  assert (CSTa11 : cstate st11 LBc11 LB Lc11 ma11 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb11 ma11 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST11| exact MU11| exact WM11| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF11 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st11 LBc11 Lc11 mb11 st11 LBc11 Lc11 ma11).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU11| exact WM11| exact HP11| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF11 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST11 HP11 ST11 MI11 MU11 WM11. try clear errv11.
  clear P0_A11_1 PC_A11_1 RNG_A11_1 P0_A11_2 PC_A11_2 RNG_A11_2 P0_A11_3 PC_A11_3 RNG_A11_3 P0_A11_4 PC_A11_4 RNG_A11_4 P0_A11_5 PC_A11_5 RNG_A11_5 P0_A11_6 PC_A11_6 RNG_A11_6 P0_A11_7 PC_A11_7 RNG_A11_7 P0_A11_8 PC_A11_8 RNG_A11_8.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_stored_namemap_new_fp_spec HB_crypto_zalloc_stmt HB_crypto_aligned_alloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc11)| wp_wnorm; wp_lia..]| exact CSTa11| rewrite unsigned_lit by wp_lia; unfold SNM_STACK, NMN_STACK, HTN_STACK, RCU_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia| rewrite ?unsigned_lit by wp_lia; wp_lia| reflexivity| wp_cells]. }
  intros f12 L12 st12 ms12 (v12 & mb12 & LB12 & RET12 & FU12 & GR12 & CST12 & FRM12 & (q12_1 & q12_2 & q12_3 & q12_4 & q12_5 & q12_6 & q12_7 & q12_8 & q12_9 & A12_1 & A12_2 & A12_3 & A12_4 & A12_5 & A12_6 & A12_7 & A12_8 & A12_9 & -> & -> & -> & RNG_A12_1 & RNG_A12_2 & RNG_A12_3 & RNG_A12_4 & RNG_A12_5 & RNG_A12_6 & RNG_A12_7 & RNG_A12_8 & RNG_A12_9)).
  destruct RET12 as (u0_12 & u1_12 & u2_12 & b1_12 & b2_12 & b3_12 & b4_12 & b5_12 & b6_12 & b7_12 & u3_12 & u4_12 & u5_12 & u6_12 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM12 by wp_lia.
  pose proof FRM12 as (CFR12 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM12 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma11 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR12 FRh ltac:(wp_lia)) as FRs12; clear FRh end.
  match goal with Hs : rw_cells _ ma11 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR12 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma11 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR12 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma11 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR12 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma11 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR12 Hs Hn; clear Hs end.
  try match goal with Hs : rw_cells _ ma11 0x351010 _ |- _ => clear Hs end.
  pose proof CST12 as (HP12 & _ & (errv12 & _ & _ & ST12 & _ & _ & MI12 & _) & _).
  rewrite unsigned_lit in ST12 by wp_lia.
  pose proof RNG_A12_1 as (P0_A12_1 & _ & _ & PC_A12_1 & _).
  pose proof RNG_A12_2 as (P0_A12_2 & _ & _ & PC_A12_2 & _).
  pose proof RNG_A12_3 as (P0_A12_3 & _ & _ & PC_A12_3 & _).
  pose proof RNG_A12_4 as (P0_A12_4 & _ & _ & PC_A12_4 & _).
  pose proof RNG_A12_5 as (P0_A12_5 & _ & _ & PC_A12_5 & _).
  pose proof RNG_A12_6 as (P0_A12_6 & _ & _ & PC_A12_6 & _).
  pose proof RNG_A12_7 as (P0_A12_7 & _ & _ & PC_A12_7 & _).
  pose proof RNG_A12_8 as (P0_A12_8 & _ & _ & PC_A12_8 & _).
  pose proof RNG_A12_9 as (P0_A12_9 & _ & _ & PC_A12_9 & _).
  assert (FUc12 : (f <= f12 + 93)%nat) by (clear - FU12 FUc11; lia).
  change (Z.to_nat 16) with 16%nat in |-.
  change (Z.to_nat 24) with 24%nat in |-.
  change (Z.to_nat 40) with 40%nat in |-.
  change (Z.to_nat 56) with 56%nat in |-.
  change (Z.to_nat 96) with 96%nat in |-.
  change (Z.to_nat 264) with 264%nat in |-.
  change (Z.to_nat 32768) with 32768%nat in |-.
  pose (LBc12 := (q12_9, A12_9, 56) :: (q12_8, A12_8, 16) :: (q12_7, A12_7, 264) :: (q12_6, A12_6, 32768) :: (q12_5, A12_5, 24) :: (q12_4, A12_4, 40) :: (q12_3, A12_3, 96) :: (q12_2, A12_2, 40) :: (q12_1, A12_1, 40) :: LBc11). pose (Lc12 := (q12_9, 56) :: (q12_8, 16) :: (q12_7, 264) :: (q12_6, 32816) :: (q12_5, 24) :: (q12_4, 40) :: (q12_3, 96) :: (q12_2, 40) :: (q12_1, 40) :: Lc11).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc12 s_ ms_ Q_) end.
  assert (GRc12 : cgrow L Lc12 87 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc11 GR12)| wp_wnorm; wp_lia..]).
  assert (IN_A12_9 : In (q12_9, A12_9, 56) LBc12) by (left; reflexivity).
  assert (IN_A12_8 : In (q12_8, A12_8, 16) LBc12) by (do 1 right; left; reflexivity).
  assert (IN_A12_7 : In (q12_7, A12_7, 264) LBc12) by (do 2 right; left; reflexivity).
  assert (IN_A12_6 : In (q12_6, A12_6, 32768) LBc12) by (do 3 right; left; reflexivity).
  assert (IN_A12_5 : In (q12_5, A12_5, 24) LBc12) by (do 4 right; left; reflexivity).
  assert (IN_A12_4 : In (q12_4, A12_4, 40) LBc12) by (do 5 right; left; reflexivity).
  assert (IN_A12_3 : In (q12_3, A12_3, 96) LBc12) by (do 6 right; left; reflexivity).
  assert (IN_A12_2 : In (q12_2, A12_2, 40) LBc12) by (do 7 right; left; reflexivity).
  assert (IN_A12_1 : In (q12_1, A12_1, 40) LBc12) by (do 8 right; left; reflexivity).
  pose proof (conj IN_A12_9 (conj IN_A12_8 (conj IN_A12_7 (conj IN_A12_6 (conj IN_A12_5 (conj IN_A12_4 (conj IN_A12_3 (conj IN_A12_2 IN_A12_1)))))))) as PK12. clear CSTa11 CFR12 FU12 GR12 FUc11 GRc11 f11 IN_A12_9 IN_A12_8 IN_A12_7 IN_A12_6 IN_A12_5 IN_A12_4 IN_A12_3 IN_A12_2 IN_A12_1.
  try (clear u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32df88, 0x32df90)]%Z mb12) as MU12. pose proof (wmono_refl usegs mb12) as WM12.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma12 end.
  assert (CSTa12 : cstate st12 LBc12 LB Lc12 ma12 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb12 ma12 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST12| exact MU12| exact WM12| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF12 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st12 LBc12 Lc12 mb12 st12 LBc12 Lc12 ma12).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU12| exact WM12| exact HP12| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF12 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST12 HP12 ST12 MI12 MU12 WM12. try clear errv12.
  clear P0_A12_1 PC_A12_1 RNG_A12_1 P0_A12_2 PC_A12_2 RNG_A12_2 P0_A12_3 PC_A12_3 RNG_A12_3 P0_A12_4 PC_A12_4 RNG_A12_4 P0_A12_5 PC_A12_5 RNG_A12_5 P0_A12_6 PC_A12_6 RNG_A12_6 P0_A12_7 PC_A12_7 RNG_A12_7 P0_A12_8 PC_A12_8 RNG_A12_8 P0_A12_9 PC_A12_9 RNG_A12_9.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_property_defns_new_fp_spec HB_lh_new_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc12)| wp_wnorm; wp_lia..]| exact CSTa12| rewrite unsigned_lit by wp_lia; unfold PDN_STACK, LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f13 L13 st13 ms13 (v13 & mb13 & LB13 & RET13 & FU13 & GR13 & CST13 & FRM13 & (q13_1 & q13_2 & A13_1 & A13_2 & -> & -> & -> & RNG_A13_1 & RNG_A13_2)).
  destruct RET13 as (u0_13 & u1_13 & u2_13 & b1_13 & b2_13 & b3_13 & b4_13 & b5_13 & b6_13 & b7_13 & u3_13 & u4_13 & u5_13 & u6_13 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM13 by wp_lia.
  pose proof FRM13 as (CFR13 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM13 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma12 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR13 FRh ltac:(wp_lia)) as FRs13; clear FRh end.
  match goal with Hs : rw_cells _ ma12 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR13 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma12 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR13 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma12 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR13 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma12 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR13 Hs Hn; clear Hs end.
  pose proof CST13 as (HP13 & _ & (errv13 & _ & _ & ST13 & _ & _ & MI13 & _) & _).
  rewrite unsigned_lit in ST13 by wp_lia.
  pose proof RNG_A13_1 as (P0_A13_1 & _ & _ & PC_A13_1 & _).
  pose proof RNG_A13_2 as (P0_A13_2 & _ & _ & PC_A13_2 & _).
  assert (FUc13 : (f <= f13 + 95)%nat) by (clear - FU13 FUc12; lia).
  change (Z.to_nat 104) with 104%nat in |-.
  change (Z.to_nat 128) with 128%nat in |-.
  pose (LBc13 := (q13_2, A13_2, 128) :: (q13_1, A13_1, 104) :: LBc12). pose (Lc13 := (q13_2, 128) :: (q13_1, 104) :: Lc12).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc13 s_ ms_ Q_) end.
  assert (GRc13 : cgrow L Lc13 89 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc12 GR13)| wp_wnorm; wp_lia..]).
  assert (IN_A13_2 : In (q13_2, A13_2, 128) LBc13) by (left; reflexivity).
  assert (IN_A13_1 : In (q13_1, A13_1, 104) LBc13) by (do 1 right; left; reflexivity).
  pose proof (conj IN_A13_2 IN_A13_1) as PK13. clear CSTa12 CFR13 FU13 GR13 FUc12 GRc12 f12 IN_A13_2 IN_A13_1.
  try (clear u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32df90, 0x32df98)]%Z mb13) as MU13. pose proof (wmono_refl usegs mb13) as WM13.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma13 end.
  assert (CSTa13 : cstate st13 LBc13 LB Lc13 ma13 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb13 ma13 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST13| exact MU13| exact WM13| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF13 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st13 LBc13 Lc13 mb13 st13 LBc13 Lc13 ma13).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU13| exact WM13| exact HP13| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF13 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST13 HP13 ST13 MI13 MU13 WM13. try clear errv13.
  clear P0_A13_1 PC_A13_1 RNG_A13_1 P0_A13_2 PC_A13_2 RNG_A13_2.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_ctx_global_properties_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc13)| wp_wnorm; wp_lia..]| exact CSTa13| rewrite unsigned_lit by wp_lia; unfold ossl_ctx_global_properties_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f14 L14 st14 ms14 (v14 & mb14 & LB14 & RET14 & FU14 & GR14 & CST14 & FRM14 & (q14_1 & A14_1 & -> & -> & -> & RNG_A14_1 & BC14_0)).
  destruct RET14 as (u0_14 & u1_14 & u2_14 & b1_14 & b2_14 & b3_14 & b4_14 & b5_14 & b6_14 & b7_14 & u3_14 & u4_14 & u5_14 & u6_14 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM14 by wp_lia.
  pose proof FRM14 as (CFR14 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM14 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma13 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR14 FRh ltac:(wp_lia)) as FRs14; clear FRh end.
  match goal with Hs : rw_cells _ ma13 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR14 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma13 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR14 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma13 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR14 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma13 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR14 Hs Hn; clear Hs end.
  pose proof CST14 as (HP14 & _ & (errv14 & _ & _ & ST14 & _ & _ & MI14 & _) & _).
  rewrite unsigned_lit in ST14 by wp_lia.
  pose proof RNG_A14_1 as (P0_A14_1 & _ & _ & PC_A14_1 & _).
  assert (FUc14 : (f <= f14 + 96)%nat) by (clear - FU14 FUc13; lia).
  change (Z.to_nat 16) with 16%nat in BC14_0.
  pose (LBc14 := (q14_1, A14_1, 16) :: LBc13). pose (Lc14 := (q14_1, 16) :: Lc13).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc14 s_ ms_ Q_) end.
  assert (GRc14 : cgrow L Lc14 90 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc13 GR14)| wp_wnorm; wp_lia..]).
  assert (IN_A14_1 : In (q14_1, A14_1, 16) LBc14) by (left; reflexivity).
  wp_box1 BC14_0.
  pose proof (conj IN_A14_1 BC14_0) as PK14. clear CSTa13 CFR14 FU14 GR14 FUc13 GRc13 f13 IN_A14_1 BC14_0.
  try (clear u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32df98, 0x32dfa0)]%Z mb14) as MU14. pose proof (wmono_refl usegs mb14) as WM14.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma14 end.
  assert (CSTa14 : cstate st14 LBc14 LB Lc14 ma14 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb14 ma14 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST14| exact MU14| exact WM14| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF14 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st14 LBc14 Lc14 mb14 st14 LBc14 Lc14 ma14).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU14| exact WM14| exact HP14| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF14 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST14 HP14 ST14 MI14 MU14 WM14. try clear errv14.
  clear P0_A14_1 PC_A14_1 RNG_A14_1.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_bio_core_globals_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc14)| wp_wnorm; wp_lia..]| exact CSTa14| rewrite unsigned_lit by wp_lia; unfold ossl_bio_core_globals_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f15 L15 st15 ms15 (v15 & mb15 & LB15 & RET15 & FU15 & GR15 & CST15 & FRM15 & (q15_1 & A15_1 & -> & -> & -> & RNG_A15_1 & BC15_0)).
  destruct RET15 as (u0_15 & u1_15 & u2_15 & b1_15 & b2_15 & b3_15 & b4_15 & b5_15 & b6_15 & b7_15 & u3_15 & u4_15 & u5_15 & u6_15 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM15 by wp_lia.
  pose proof FRM15 as (CFR15 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM15 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma14 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR15 FRh ltac:(wp_lia)) as FRs15; clear FRh end.
  match goal with Hs : rw_cells _ ma14 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR15 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma14 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR15 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma14 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR15 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma14 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR15 Hs Hn; clear Hs end.
  pose proof CST15 as (HP15 & _ & (errv15 & _ & _ & ST15 & _ & _ & MI15 & _) & _).
  rewrite unsigned_lit in ST15 by wp_lia.
  pose proof RNG_A15_1 as (P0_A15_1 & _ & _ & PC_A15_1 & _).
  assert (FUc15 : (f <= f15 + 97)%nat) by (clear - FU15 FUc14; lia).
  change (Z.to_nat 56) with 56%nat in BC15_0.
  pose (LBc15 := (q15_1, A15_1, 56) :: LBc14). pose (Lc15 := (q15_1, 56) :: Lc14).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc15 s_ ms_ Q_) end.
  assert (GRc15 : cgrow L Lc15 91 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc14 GR15)| wp_wnorm; wp_lia..]).
  assert (IN_A15_1 : In (q15_1, A15_1, 56) LBc15) by (left; reflexivity).
  wp_box1 BC15_0.
  pose proof (conj IN_A15_1 BC15_0) as PK15. clear CSTa14 CFR15 FU15 GR15 FUc14 GRc14 f14 IN_A15_1 BC15_0.
  try (clear u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32dfb8, 0x32dfc0)]%Z mb15) as MU15. pose proof (wmono_refl usegs mb15) as WM15.
  cprefix. ths. step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma15 end.
  assert (CSTa15 : cstate st15 LBc15 LB Lc15 ma15 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb15 ma15 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST15| exact MU15| exact WM15| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (SF15 : forall T_ : bptr -> Prop, cframe T_ [(0x32dec8, 0x32ded8); (0x32df70, 0x32e008)]%Z (bv_unsigned sp) st15 LBc15 Lc15 mb15 st15 LBc15 Lc15 ma15).
  { intros T_. eapply cframe_seg; [apply cframe_refl| exact MU15| exact WM15| exact HP15| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 (SF15 (fun _ : bptr => False)) ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  clear CST15 HP15 ST15 MI15 MU15 WM15. try clear errv15.
  clear P0_A15_1 PC_A15_1 RNG_A15_1.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (ossl_prov_drbg_nonce_ctx_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc15)| wp_wnorm; wp_lia..]| exact CSTa15| rewrite unsigned_lit by wp_lia; unfold ossl_prov_drbg_nonce_ctx_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f16 L16 st16 ms16 (v16 & mb16 & LB16 & RET16 & FU16 & GR16 & CST16 & FRM16 & (q16_1 & A16_1 & q16_2 & A16_2 & -> & -> & -> & RNG_A16_1 & RNG_A16_2 & BC16_0 & BC16_1)).
  destruct RET16 as (u0_16 & u1_16 & u2_16 & b1_16 & b2_16 & b3_16 & b4_16 & b5_16 & b6_16 & b7_16 & u3_16 & u4_16 & u5_16 & u6_16 & ->).
  cret_lit. rewrite ?unsigned_lit by wp_lia. rewrite ?unsigned_lit in FRM16 by wp_lia.
  pose proof FRM16 as (CFR16 & _).
  pose proof (psd_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ XR11_0 FRM16 ltac:(intros q_ _ X; exact X)) as XR11_0_. clear XR11_0. rename XR11_0_ into XR11_0.
  lazymatch goal with FRh : rw_cells _ ma15 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR16 FRh ltac:(wp_lia)) as FRs16; clear FRh end.
  match goal with Hs : rw_cells _ ma15 0x32dec8 _ |- _ => let Hn := fresh "SK" in cst_static CFR16 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma15 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR16 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma15 0x32df70 _ |- _ => let Hn := fresh "SK" in cst_static CFR16 Hs Hn; clear Hs end.
  match goal with Hs : rw_cells _ ma15 0x32df78 _ |- _ => let Hn := fresh "SK" in cst_static CFR16 Hs Hn; clear Hs end.
  pose proof CST16 as (HP16 & _ & (errv16 & _ & _ & ST16 & _ & _ & MI16 & _) & _).
  rewrite unsigned_lit in ST16 by wp_lia.
  pose proof RNG_A16_1 as (P0_A16_1 & _ & _ & PC_A16_1 & _).
  pose proof RNG_A16_2 as (P0_A16_2 & _ & _ & PC_A16_2 & _).
  assert (FUc16 : (f <= f16 + 99)%nat) by (clear - FU16 FUc15; lia).
  change (Z.to_nat 16) with 16%nat in BC16_0, BC16_1.
  change (Z.to_nat 40) with 40%nat in BC16_0, BC16_1.
  pose (LBc16 := (q16_2, A16_2, 40) :: (q16_1, A16_1, 16) :: LBc15). pose (Lc16 := (q16_2, 40) :: (q16_1, 16) :: Lc15).
  lazymatch goal with |- climpl ?f_ ?L_ ?s_ ?ms_ ?Q_ => change (climpl f_ L_ s_ ms_ Q_) with (climpl f_ Lc16 s_ ms_ Q_) end.
  assert (GRc16 : cgrow L Lc16 93 6 83768) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc15 GR16)| wp_wnorm; wp_lia..]).
  assert (IN_A16_2 : In (q16_2, A16_2, 40) LBc16) by (left; reflexivity).
  assert (IN_A16_1 : In (q16_1, A16_1, 16) LBc16) by (do 1 right; left; reflexivity).
  wp_box1 BC16_0.
  wp_box1 BC16_1.
  pose proof (conj IN_A16_2 (conj IN_A16_1 (conj BC16_0 BC16_1))) as PK16. clear CSTa15 CFR16 FU16 GR16 FUc15 GRc15 f15 IN_A16_2 IN_A16_1 BC16_0 BC16_1.
  try (clear u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15).
  (* [comment removed for export] *)
  pose proof (context_init_part2 HB_crypto_zalloc_stmt HB_ossl_property_parse_init_fp_stmt) as P2. cbv zeta in P2.
  eapply P2; [exact HB| exact Hf| exact ROOM| exact OWN| wp_lia| exact SP16| exact CST16| wp_cells| wp_cells| wp_cells| wp_cells| wp_cells| exact XR11_0| exact FUc16| exact GRc16| exact PK1| exact PK2| exact PK3| exact PK4| exact PK5| exact PK6| exact PK7| exact PK8| exact PK9| exact PK10| exact PK11| exact PK12| exact PK13| exact PK14| exact PK15| exact PK16| exact SF0| exact SF1| exact SF3| exact SF4| exact SF5| exact SF6| exact SF7| exact SF8| exact SF9| exact SF10| exact SF11| exact SF12| exact SF13| exact SF14| exact SF15| exact FRM1| exact FRM2| exact FRM3| exact FRM4| exact FRM5| exact FRM6| exact FRM7| exact FRM8| exact FRM9| exact FRM10| exact FRM11| exact FRM12| exact FRM13| exact FRM14| exact FRM15| exact FRM16].
Qed.
End WithCeiling0.
