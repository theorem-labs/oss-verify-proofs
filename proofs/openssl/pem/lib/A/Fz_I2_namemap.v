(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_locknew Fz_M_aligned Fz_M_aligned_array Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw Fz_I2_htnew Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_I2_nmw Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).

(* [comment removed for export] *)
Lemma ubs_raw8 : forall p, p mod 8 = 0 -> negb (bv_eqb (Z_to_bv 64 (Z.land p 7)) (Z_to_bv 64 0)) = false.
Proof. intros p H. rewrite (ubs_land7 p H). reflexivity. Qed.

Section NamemapNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM1 : stack_malloc_contract RT 1.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_LN : crypto_lock_new_env_stmt RT.
Hypothesis C_HT : ht_new_stmt RT.
Hypothesis C_SKN : OPENSSL_sk_new_null_stmt RT.
Hypothesis C_SKCMP : OPENSSL_sk_set_cmp_thunks_stmt RT.
Hypothesis C_SKCPY : OPENSSL_sk_set_copy_thunks_stmt RT.
Hypothesis C_SKSET : OPENSSL_sk_set_thunks_stmt RT.

Definition NM_SITES : list (Z * Z) :=
  [(SITE_nm_zalloc, e_namemap_new); (SITE_nm_locknew, e_namemap_new); (SITE_nm_htnew, e_namemap_new); (SITE_nm_sknew, e_namemap_new);
   (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_lock_new); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null)] ++ HT_SITES.
Definition NM_CALLS : list (Z * Z) :=
  [(SITE_nm_zalloc, e_CRYPTO_zalloc); (SITE_nm_locknew, e_lock_new); (SITE_nm_htnew, e_ht_new); (SITE_nm_sknew, e_OPENSSL_sk_new_null);
   (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc)] ++ HT_CALLS.
Definition NM_COST : Z := 1 + mcost 40 + 1 + HT_COST + mcost 56.
Definition nm_sk_cells : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 NM_CMP_THUNK); C8 (Z_to_bv 64 NM_SET_THUNK); C8 (Z_to_bv 64 NM_COPY_THUNK)].

(* [comment removed for export] *)
Definition namemap_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> bv_unsigned a0 <> 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x300 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_namemap_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) NM_SITES NM_CALLS ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 9 <= LIVE_MAX -> NM_COST <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_namemap_new m)))
    (fun c => exists (Σ' : rts RT) (nm lk ht lk2 md q L qp sk : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 nm) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' nm 40 /\ acc asegs m' nm 40
           /\ rw_cells asegs m' nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)]
           /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' ht (ht_tab4 a0 L lk2 md)
           /\ rw_cells asegs m' md [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 511)]
           /\ rw_cells asegs m' lk2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' L (rcu_head a0 qp)
           /\ rw_cells asegs m' (L + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' (L + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' (L + 128) cond_cells
           /\ rw_cells asegs m' (L + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' (L + 216) cond_cells
           /\ rw_cells asegs m' qp [CB 16 (repeat (Z_to_bv 8 0) 16)]
           /\ bytes_at asegs m' q (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))
           /\ rw_cells asegs m' sk nm_sk_cells) c
       /\ rt_live RT Σ' = (sk, 56) :: (qp, 16) :: (L, 264) :: (q, NB_BYTES) :: (md, 24) :: (lk2, 40) :: (ht, 96) :: (lk, 40) :: (nm, 40) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - NM_COST
       /\ 0 < nm /\ nm mod 16 = 0 /\ nm + 40 < USTACK_TOP /\ 0 < lk /\ lk mod 16 = 0 /\ lk + 40 < USTACK_TOP
       /\ 0 < ht /\ ht mod 16 = 0 /\ ht + 96 < USTACK_TOP /\ 0 < lk2 /\ lk2 mod 16 = 0 /\ lk2 + 40 < USTACK_TOP
       /\ 0 < md /\ md mod 16 = 0 /\ md + 24 < USTACK_TOP /\ 0 < q /\ q mod 64 = 0 /\ q + NB_BYTES < USTACK_TOP
       /\ 0 < L /\ L mod 16 = 0 /\ L + 264 < USTACK_TOP /\ 0 < qp /\ qp mod 16 = 0 /\ qp + 16 < USTACK_TOP
       /\ 0 < sk /\ sk mod 16 = 0 /\ sk + 56 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem namemap_new_cps : namemap_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> CTXN ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 176 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -96 - pad).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  unfold NM_COST, HT_COST in Hcr. pose proof (wg_mcost_nonneg 40) as MC1. pose proof (wg_mcost_nonneg 96) as MC2. pose proof (wg_mcost_nonneg 24) as MC3.
  pose proof (wg_mcost_nonneg NB_BYTES) as MC4. pose proof (wg_mcost_nonneg 264) as MC5. pose proof (wg_mcost_nonneg 16) as MC6. pose proof (wg_mcost_nonneg 56) as MC7.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  assert (COK : forall mm Σx, stk asegs mm lo usp1 -> rt_sp0 RT Σx = rt_sp0 RT Σ -> call_ok RT Σx mm (Z_to_bv 64 usp1) lo).
  { intros mm Σx S E. unfold call_ok. rewrite EU1, E. split; [exact S|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|].
    split; [unfold USTACK_TOP in *; lia|]. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (nm_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad
                HP HPM ST ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(lia) ltac:(lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG1) as UWF1.
  (* [comment removed for export] *)
  apply (SM1 Σ PMc (Z_to_bv 64 SITE_nm_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 128) a1' a2' a3 a4 a5 a6 a7
           s2 a0 s4 s5 s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(right; left; reflexivity) eq_refl ltac:(clear - Hfr; lia) ltac:(lia) ART1 MI1
           (COK m1 Σ ST1 eq_refl) _ _ Hc1').
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_nm_smalloc) in Hc2' by (unfold SITE_nm_smalloc; lia).
  assert (INF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 1%nat ART2 INF) as (_ & FLO & _ & _).
  pose proof (af_frames_align RT AF Σ1 m2 f 1%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 1%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 1) with 128 in FLO, FSH, FU, WF2, WS2. change (128 - 8) with 120 in WF2. change (128 / 8) with 16 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 128) = shad f + 16) by (replace (f + 128) with (f + 64 * 2) by lia; rewrite (shad_add64 f 2 F64); lia).
  pose proof (div8_facts f) as Q1.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -96)) by (apply (stk_agree_nw asegs m1 m2 _ _ GAP1); intros x Hx; cbv beta in Hx; apply PRES2; left; unfold USTACK_TOP in *; lia).
  pose proof (cl_env_pres _ _ _ m1 m2 lb canary ENV1 PRES2) as ENV2.
  assert (AG12 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; cbv beta in Ha; apply PRES2; left; unfold usp1; lia).
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AG12) as UWF2.
  destruct (wr_at_rw_CB m2 f 120 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 16 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 120) with 120%nat in FB2. change (Z.to_nat 16) with 16%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (nm_w1 ra sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 a0 s4 s5 s6 s8 s9 s10 s11 u3 u4 u5 u6
                s0 s1 s2 s3 s4 s5 s6 s7 F2 fc2 m2 f lo pad j fj sj HP F0 ltac:(clear - FU; unfold USTACK_TOP in *; lia) ltac:(right; exact FIMG)
                ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; clear - HSTK NUM; unfold RT_STACK in *; lia) ltac:(fold usp; lia)
                ltac:(left; fold usp; clear - FLO LOW HSTK; unfold RT_STACK in *; lia) UT2 FR2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j3 & fj3 & m3 & -> & MU3 & WM3 & MI3 & FR3 & FB3 & SB3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, Hc3'. fold usp1 in Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 96) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; rewrite SHF; unfold shad, SHB; clear - Hin; lia].
    - apply acl_stack. clear - Hin NUM. unfold USTACK_TOP in *. lia. }
  assert (ST3 : stk asegs m3 lo usp1).
  { apply (stk_munch _ m2 m3 lo usp1 ST2 MU3 WM3). intros x Hx. cbn [outside]. unfold usp1 in Hx. clear - Hx FLO LOW NUM SP0R HP. unfold STACK_WIN, USTACK_TOP in *. Z.div_mod_to_equations. lia. }
  assert (GAP3 : stk asegs m3 usp1 (usp + -96)).
  { apply (stk_munch _ m2 m3 _ _ GAP2 MU3 WM3). intros x Hx. cbn [outside]. unfold usp1 in Hx. clear - Hx FLO LOW NUM HSTK SP0R HP. unfold STACK_WIN, RT_STACK, USTACK_TOP in *. Z.div_mod_to_equations. lia. }
  pose proof (cl_env_seg _ m2 m3 _ canary ENV2 MU3 ltac:(cl_fp_lia)) as ENV3.
  assert (AG23 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3).
  { apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside]. clear - Hx FLO LOW NUM HSTK SP0R HP. unfold USTACK_TOP, STACK_WIN, RT_STACK in *. Z.div_mod_to_equations. lia. }
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AG23) as UWF3.
  (* [comment removed for export] *)
  assert (ACC3 : acc asegs m3 (f + 40) 40).
  { destruct (proj1 (rw_cells_app m3 _ [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0)] _) ltac:(unfold nm_shadow in SB3; exact SB3)) as [_ S5].
    destruct (proj1 (rw_cells_app m3 _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] _) S5) as [Z5 _].
    cbn [cells_size csize Nat.add] in Z5.
    replace 40 with (8 * Z.of_nat 5) by lia. apply (acc_zero_run asegs m3 (f + 40) 5); [clear - F64; Z.div_mod_to_equations; lia | lia |].
    replace (shad (f + 40)) with (f / 8 + 2147450880 + 5) by (unfold shad, SHB; clear - Q1 F64; Z.div_mod_to_equations; lia).
    exact (rw_cells_bytes_at asegs m3 _ _ Z5). }
  assert (CHK : checked_dst RT Σ1 m3 (Z_to_bv 64 usp1) (f + 40) 40).
  { split; [| split].
    - intros _. split; [exact ACC3|]. right; left. exists f, 1%nat. split; [exact INF | change (fs_size 1) with 128; lia].
    - intros i Hi. apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; clear - Hi; lia].
    - exact (wr_at_sub m3 f 120 (f + 40) 40 (wr_at_wm m2 m3 _ _ WF2 WM3) ltac:(lia) ltac:(lia) ltac:(lia)). }
  apply (MSET Σ1 PMc (Z_to_bv 64 SITE_nm_memset) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 usp1)
           (Z_to_bv 64 (f + 40)) (Z_to_bv 64 0) (Z_to_bv 64 40) b3 b4 b5 b6 b7 (Z_to_bv 64 f) a0 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 (f + 40) 40 (Z_to_bv 8 0) lo
           FDO MST eq_refl eq_refl eq_refl ltac:(clear - F0 FLO NUM SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) ltac:(clear; lia) CHK ART3 MI3 (COK m3 Σ1 ST3 SP1) _ _ Hc3').
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ZER4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_nm_memset) in Hc4' by (unfold SITE_nm_memset; lia).
  (* [comment removed for export] *)
  assert (AG34 : forall a k, ((usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 120 /\ (a + k <= f + 40 \/ f + 80 <= a)) \/ (shad f <= a /\ a + k <= shad f + 16))
                             -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H x Hx. cbv beta in Hx. apply PRES4.
    - destruct H as [H|[H|H]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; clear - H Hx; lia]
        | apply (acl_fshadow _ _ _ f 1%nat); [exact INF | rewrite SHF; clear - H Hx; lia]].
    - destruct H as [H|[H|H]]; [clear - H Hx FLO LOW HSTK HP; unfold usp1, RT_STACK in *; lia | clear - H Hx; lia | clear - H Hx Q1 F0 FSH; unfold shad, SHB in *; Z.div_mod_to_equations; lia]. }
  assert (FR4 : rw_cells asegs m4 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. apply AG34. left. cbn [cells_size csize Nat.add]. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP4 : stk asegs m4 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m3 m4 _ _ GAP3). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG34. left. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (SB4 : rw_cells asegs m4 (f / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs m3 m4 _ _ SB3); [| exact WM4]. apply AG34. right; right. unfold nm_shadow, shad, SHB. cbn [cells_size csize Nat.add]. clear; lia. }
  pose proof FB3 as FB3'. apply (rw_cells_split_CB asegs _ _ [] 120 _ [] [32; 8; 40; 40]%nat) in FB3'; [| reflexivity]. cbn [mk_CB_cells app] in FB3'.
  destruct (proj1 (rw_cells_app m3 f [_] _) FB3') as [HB3 X1]. cbn [cells_size csize Nat.add] in X1.
  destruct (proj1 (rw_cells_app m3 _ [_] _) X1) as [C83 X2]. cbn [cells_size csize Nat.add] in X2.
  destruct (proj1 (rw_cells_app m3 _ [_] _) X2) as [_ TB3]. cbn [cells_size csize Nat.add] in TB3. clear X1 X2 FB3'.
  replace (f + 32 + 8 + 40) with (f + 80) in TB3 by lia.
  assert (HB4 : rw_cells asegs m4 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m3 m4 _ _ HB3); [| exact WM4]. apply AG34. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (TB4 : rw_cells asegs m4 (f + 80) [CB 40 (firstn 40 (skipn 40 (skipn 8 (skipn 32 fj3))))]).
  { apply (rw_cells_agree asegs m3 m4 _ _ TB3); [| exact WM4]. apply AG34. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (FC4 : rw_cells asegs m4 (f + 32) [CB 8 (firstn 8 (skipn 32 fj3)); CB 40 (repeat (Z_to_bv 8 0) 40)]).
  { apply (proj2 (rw_cells_app m4 (f + 32) [_] _)). split.
    - apply (rw_cells_agree asegs m3 m4 _ _ C83); [| exact WM4]. apply AG34. right; left. cbn [cells_size csize Nat.add]. clear; lia.
    - cbn [cells_size csize Nat.add]. replace (f + 32 + 8) with (f + 40) by lia.
      exact (rw_CB_of_bytes m4 (f + 40) _ ZER4 (wr_at_sub m4 f 120 (f + 40) 40 (wr_at_wm m2 m4 _ _ WF2 (wmono_trans asegs _ _ _ WM3 WM4)) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia))). }
  assert (ENV4 : cl_env m4 lb canary).
  { apply (cl_env_pres_ex _ _ _ _ _ m3 m4 lb canary ENV3 PRES4). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)) as XR. clear - XR FIMG. unfold SEGTOP_A in *. lia. }
  assert (AG34u : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG34. left. clear - HP. unfold usp1. lia. }
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AG34u) as UWF4.
  (* [comment removed for export] *)
  pose proof (nm_w2 sp gp (Z_to_bv 64 TP_A) v0 v1 v2 (Z_to_bv 64 (f + 40)) d1 d2 d3 d4 d5 d6 d7 a0 s4 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 f lo pad _
                F0 FIMG ltac:(clear - FLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) FC4 MI4) as W2.
  fold usp in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (w0 & w1 & w2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m5 & -> & MU5 & WM5 & MI5 & FC5) & Hc5'). clear Hc5.
  fold usp in Hc5'. fold usp1 in Hc5'.
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 usp1 ART4 ltac:(rewrite SP1; clear - NUM HP; unfold usp1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; clear - Hin; lia]. }
  pose proof (cl_env_seg _ m4 m5 _ canary ENV4 MU5 ltac:(cl_fp_lia)) as ENV5.
  assert (AG45 : forall a k, (a + k <= f + 32 \/ f + 80 <= a) -> agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H. apply (agree_of_munch _ m4 m5 _ MU5). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST5 : stk asegs m5 lo usp1).
  { apply (stk_munch _ m4 m5 _ _ ST4 MU5 WM5). intros x Hx. cbn [outside]. clear - Hx FLO LOW HSTK HP. unfold usp1, RT_STACK in *. lia. }
  assert (FR5 : rw_cells asegs m5 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5 _ _ FR4); [| exact WM5]. apply AG45. cbn [cells_size csize Nat.add]. clear - FLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (GAP5 : stk asegs m5 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m4 m5 _ _ GAP4). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG45. clear - FLO LOW HSTK HP. unfold usp1, RT_STACK in *. lia. }
  assert (SB5 : rw_cells asegs m5 (f / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs m4 m5 _ _ SB4); [| exact WM5]. apply AG45. unfold nm_shadow. cbn [cells_size csize Nat.add]. clear - Q1 F0 FIMG FSH. Z.div_mod_to_equations. lia. }
  assert (HB5 : rw_cells asegs m5 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m4 m5 _ _ HB4); [| exact WM5]. apply AG45. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (TB5 : rw_cells asegs m5 (f + 80) [CB 40 (firstn 40 (skipn 40 (skipn 8 (skipn 32 fj3))))]).
  { apply (rw_cells_agree asegs m4 m5 _ _ TB4); [| exact WM5]. apply AG45. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (AG45u : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG45. clear - FLO LOW HSTK. unfold RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AG45u) as UWF5.
  destruct (cl_chain_call (rt_cg RT Σ1) e_namemap_new e_CRYPTO_zalloc SITE_nm_zalloc m5 m5 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG1; exact CTX)
              ltac:(rewrite CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG1; apply (proj2 CGH); wp_in_lit) UWF5 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m5 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR5))
              ltac:(rewrite EU1; fold usp; unfold usp1; clear - HP; lia) SPT) as (CTXc5 & UWCc5).
  (* [comment removed for export] *)
  apply (C_CZ Σ1 PMc (Z_to_bv 64 SITE_nm_zalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 40) (Z_to_bv 64 0x4c680) (Z_to_bv 64 535)
           e3 e4 e5 e6 e7 (Z_to_bv 64 f) a0 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 w3 w4 w5 w6
           F4 fc4 m5 40 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(clear; lia) ART5 MI5 (COK m5 Σ1 ST5 SP1)).
  { rewrite EU1. clear - HSTK HP. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_nm_zalloc) by (unfold SITE_nm_zalloc; lia). exact CTXc5. }
  { exact UWCc5. }
  { rewrite CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV1. clear - Hlen. lia. }
  { rewrite CR1. clear - Hcr MC1 MC2 MC3 MC4 MC5 MC6 MC7. lia. }
  { exact ENV5. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ2 & nm & Hc6 & LV2 & FRS2 & SP2 & CR2 & NM0 & NM16 & NMU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ENV6 & WRn6 & ACCn6 & ZERn6) & Hc6'). clear Hc6.
  destruct RS6 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_nm_zalloc) in Hc6' by (unfold SITE_nm_zalloc; lia).
  assert (INN2 : In (nm, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INF2 : In (f, 1%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2, SP1; exact LOW).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m6 nm 40 ART6 INN2 ltac:(lia)) as NMH.
  pose proof (af_live_range RT AF Σ2 m6 nm 40 ART6 INN2) as (_ & NMLO & _). rewrite SP2, SP1 in NMLO.
  pose proof (af_frames_range RT AF Σ2 m6 f 1%nat ART6 INF2) as (_ & _ & _ & NF). specialize (NF nm 40 INN2). change (fs_size 1) with 128 in NF. wp_box1 NF.
  pose proof (wg_mod16_8 _ NM16) as NMA.
  assert (HNM6 : rw_cells asegs m6 nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { pose proof (wp_zero_rw_CB asegs m6 nm 40 ZERn6 WRn6 ltac:(lia)) as HZ. change (Z.to_nat 40) with 40%nat in HZ.
    apply (rw_cells_recast m6 nm _ _ HZ); [cbn; repeat first [exact I | reflexivity | split] | reflexivity]. }
  assert (AG56 : forall a k, ((usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 120) \/ (shad f <= a /\ a + k <= shad f + 16)) -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H x Hx. cbv beta in Hx. apply PRES6.
    - destruct H as [H|[H|H]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; clear - H Hx; lia]
        | apply (acl_fshadow _ _ _ f 1%nat); [exact INF | rewrite SHF; clear - H Hx; lia]].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H Hx NUM HSTK FIMG Q1 HP. unfold shad, SHB, usp1, USTACK_TOP, RT_STACK in *. Z.div_mod_to_equations. lia. }
  assert (FR6 : rw_cells asegs m6 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m5 m6 _ _ FR5); [| exact WM6]. apply AG56. left. cbn [cells_size csize Nat.add]. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP6 : stk asegs m6 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m5 m6 _ _ GAP5). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG56. left. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (SB6 : rw_cells asegs m6 (f / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs m5 m6 _ _ SB5); [| exact WM6]. apply AG56. right; right. unfold nm_shadow, shad, SHB. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HB6 : rw_cells asegs m6 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m5 m6 _ _ HB5); [| exact WM6]. apply AG56. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (TB6 : rw_cells asegs m6 (f + 80) [CB 40 (firstn 40 (skipn 40 (skipn 8 (skipn 32 fj3))))]).
  { apply (rw_cells_agree asegs m5 m6 _ _ TB5); [| exact WM6]. apply AG56. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (FC6 : rw_cells asegs m6 (f + 32) (nm_conf0 a0)).
  { apply (rw_cells_agree asegs m5 m6 _ _ FC5); [| exact WM6]. apply AG56. right; left. unfold nm_conf0. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (AG56u : agree_on (fun x => usp <= x < USTACK_TOP) m5 m6).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG56. left. clear - HP. unfold usp1. lia. }
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWF5 AG56u) as UWF6.
  pose proof ENV6 as ENV6'.
  (* [comment removed for export] *)
  pose proof (nm_w3 sp gp (Z_to_bv 64 TP_A) x0 x1 x2 g1 g2 g3 g4 g5 g6 g7 a0 s4 s8 s9 s10 s11 x3 x4 x5 x6 F6 fc6 m6 f nm pad NM0 ltac:(clear - NMU; unfold USTACK_TOP in *; lia) MI6) as W3.
  fold usp in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & E7 & Hc7'). clear Hc7. unfold nm_w3_post in E7. subst ms7. fold usp in Hc7'.
  destruct (cl_chain_call (rt_cg RT Σ2) e_namemap_new e_lock_new SITE_nm_locknew m6 m6 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG2, CG1; exact CTX)
              ltac:(rewrite CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF6 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m6 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR6))
              ltac:(rewrite EU1; fold usp; unfold usp1; clear - HP; lia) SPT) as (CTXc6 & UWCc6).
  (* [comment removed for export] *)
  apply (C_LN Σ2 PMc (Z_to_bv 64 SITE_nm_locknew) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) x0 x1 x2 sp (Z_to_bv 64 usp1)
           (Z_to_bv 64 nm) g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 x3 x4 x5 x6
           F6 fc6 m6 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART6 MI6 (COK m6 Σ2 ST6 ltac:(rewrite SP2; exact SP1))).
  { rewrite EU1. clear - HSTK HP. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_nm_locknew) by (unfold SITE_nm_locknew; lia). exact CTXc6. }
  { exact UWCc6. }
  { rewrite CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS2, FRS1. cbn [length]. clear - Hfr. lia. }
  { rewrite LV2, LV1. cbn [length]. clear - Hlen. lia. }
  { rewrite CR2, CR1. clear - Hcr MC1 MC2 MC3 MC4 MC5 MC6 MC7. lia. }
  { exact ENV6. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ3 & lk & Hc8 & LV3 & FRS3 & SP3 & CR3 & LK0 & LK16 & LKU & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m7 & RS8 & (ART7 & MI7 & WM7 & ST7) & PRES7 & ENV7 & HLK7 & ACClk7) & Hc8'). clear Hc8.
  destruct RS8 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F7 & fc7 & ->).
  rewrite EU1 in ST7, PRES7. rewrite (ret_pc_even SITE_nm_locknew) in Hc8' by (unfold SITE_nm_locknew; lia).
  assert (INL3 : In (lk, 40) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
  assert (INN3 : In (nm, 40) (rt_live RT Σ3)) by (rewrite LV3; right; exact INN2).
  assert (INF3 : In (f, 1%nat) (rt_frames RT Σ3)) by (rewrite FRS3; exact INF2).
  assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3; exact LOW2).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m7 lk 40 ART7 INL3 ltac:(lia)) as LKH.
  pose proof (af_live_disj RT AF Σ3 m7 lk 40 nm 40 [] (rt_live RT Σ2) ART7 LV3 INN2) as LKN. wp_box1 LKN.
  pose proof (af_frames_range RT AF Σ3 m7 f 1%nat ART7 INF3) as (_ & _ & _ & LF). specialize (LF lk 40 INL3). change (fs_size 1) with 128 in LF. wp_box1 LF.
  assert (AG67 : forall a k, ((usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 120) \/ (shad f <= a /\ a + k <= shad f + 16) \/ (nm <= a /\ a + k <= nm + 40))
                             -> agree_on (fun x => a <= x < a + k) m6 m7).
  { intros a k H x Hx. cbv beta in Hx. apply PRES7.
    - destruct H as [H|[H|[H|H]]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ f 1%nat); [exact INF2 | change (fs_size 1) with 128; clear - H Hx; lia]
        | apply (acl_fshadow _ _ _ f 1%nat); [exact INF2 | rewrite SHF; clear - H Hx; lia] | apply (acl_live _ _ _ nm 40); [exact INN2 | clear - H Hx; lia]].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H Hx NUM HSTK FIMG Q1 HP NMH. unfold shad, SHB, usp1, USTACK_TOP, RT_STACK in *. Z.div_mod_to_equations. lia. }
  assert (FR7 : rw_cells asegs m7 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m6 m7 _ _ FR6); [| exact WM7]. apply AG67. left. cbn [cells_size csize Nat.add]. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP7 : stk asegs m7 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m6 m7 _ _ GAP6). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG67. left. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (SB7 : rw_cells asegs m7 (f / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs m6 m7 _ _ SB6); [| exact WM7]. apply AG67. right; right; left. unfold nm_shadow, shad, SHB. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HB7 : rw_cells asegs m7 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m6 m7 _ _ HB6); [| exact WM7]. apply AG67. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (TB7 : rw_cells asegs m7 (f + 80) [CB 40 (firstn 40 (skipn 40 (skipn 8 (skipn 32 fj3))))]).
  { apply (rw_cells_agree asegs m6 m7 _ _ TB6); [| exact WM7]. apply AG67. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (FC7 : rw_cells asegs m7 (f + 32) (nm_conf0 a0)).
  { apply (rw_cells_agree asegs m6 m7 _ _ FC6); [| exact WM7]. apply AG67. right; left. unfold nm_conf0. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HNM7 : rw_cells asegs m7 nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m6 m7 _ _ HNM6); [| exact WM7]. apply AG67. right; right; right. cbn [cells_size csize Nat.add]. clear; lia. }
  pose proof (proj2 (af_acc_live RT AF Σ3 m7 nm 40 ART7 INN3)) as ACCn7.
  assert (AG67u : agree_on (fun x => usp <= x < USTACK_TOP) m6 m7).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG67. left. clear - HP. unfold usp1. lia. }
  pose proof (uw_chain_agree outer m6 m7 sp s0 UWF6 AG67u) as UWF7.
  (* [comment removed for export] *)
  pose proof (nm_w4 sp gp (Z_to_bv 64 TP_A) y0 y1 y2 h1 h2 h3 h4 h5 h6 h7 s4 s8 s9 s10 s11 y3 y4 y5 y6 F7 fc7 m7 f nm lk pad
                F0 ltac:(clear - FLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) NMH ltac:(clear - NMU; unfold USTACK_TOP in *; lia) NMA LK0 ltac:(clear - LKU; unfold USTACK_TOP in *; lia) HNM7 ACCn7 MI7) as W4.
  fold usp in W4.
  cl_lift W4 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ3 _ _ c9 Hc9) as (ms9 & (m8 & -> & MU8 & WM8 & MI8 & HNM8) & Hc9'). clear Hc9.
  fold usp in Hc9'. fold usp1 in Hc9'.
  assert (ART8 : ART RT Σ3 m8).
  { apply (af_frame RT AF Σ3 m7 m8 usp1 ART7 ltac:(rewrite SP3, SP2, SP1; clear - NUM HP; unfold usp1; lia)); [| exact WM8].
    intros a Ha. apply MU8. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ nm 40); [exact INN3 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m7 m8 _ canary ENV7 MU8 ltac:(cl_fp_lia)) as ENV8.
  assert (AG78 : forall a k, (a + k <= nm \/ nm + 40 <= a) -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H. apply (agree_of_munch _ m7 m8 _ MU8). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST8 : stk asegs m8 lo usp1).
  { apply (stk_munch _ m7 m8 _ _ ST7 MU8 WM8). intros x Hx. cbn [outside]. clear - Hx NMLO LOW HSTK HP. unfold usp1, RT_STACK in *. lia. }
  assert (FR8 : rw_cells asegs m8 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m7 m8 _ _ FR7); [| exact WM8]. apply AG78. cbn [cells_size csize Nat.add]. clear - NMLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (GAP8 : stk asegs m8 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m7 m8 _ _ GAP7). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG78. clear - NMLO LOW HSTK HP. unfold usp1, RT_STACK in *. lia. }
  assert (SB8 : rw_cells asegs m8 (f / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs m7 m8 _ _ SB7); [| exact WM8]. apply AG78. unfold nm_shadow. cbn [cells_size csize Nat.add]. clear - Q1 F0 NMH FLO SP0R. unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  assert (HB8 : rw_cells asegs m8 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m7 m8 _ _ HB7); [| exact WM8]. apply AG78. cbn [cells_size csize Nat.add]. clear - NF. unfold wp_box in *. lia. }
  assert (TB8 : rw_cells asegs m8 (f + 80) [CB 40 (firstn 40 (skipn 40 (skipn 8 (skipn 32 fj3))))]).
  { apply (rw_cells_agree asegs m7 m8 _ _ TB7); [| exact WM8]. apply AG78. cbn [cells_size csize Nat.add]. clear - NF. unfold wp_box in *. lia. }
  assert (FC8 : rw_cells asegs m8 (f + 32) (ht_conf a0)).
  { apply (rw_cells_recast m8 (f + 32) (nm_conf0 a0) (ht_conf a0)); [| cbn; repeat first [exact I | reflexivity | split] | unfold nm_conf0, ht_conf; cbn [cells_bytes cbytes app]; f_equal; vm_compute; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); reflexivity].
    apply (rw_cells_agree asegs m7 m8 _ _ FC7); [| exact WM8]. apply AG78. unfold nm_conf0. cbn [cells_size csize Nat.add]. clear - NF. unfold wp_box in *. lia. }
  assert (HLK8 : rw_cells asegs m8 lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m7 m8 _ _ HLK7); [| exact WM8]. apply AG78. unfold mutex_cells. cbn [cells_size csize Nat.add]. clear - LKN. unfold wp_box in *. lia. }
  assert (AG78u : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG78. clear - NMLO LOW HSTK. unfold RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m7 m8 sp s0 UWF7 AG78u) as UWF8.
  (* [comment removed for export] *)
  assert (ACF8 : acc asegs m8 (f + 32) 48).
  { destruct (proj1 (rw_cells_app m8 _ [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _) ltac:(unfold nm_shadow in SB8; exact SB8)) as [_ S4].
    destruct (proj1 (rw_cells_app m8 _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] _) S4) as [Z6 _].
    cbn [cells_size csize Nat.add] in Z6.
    replace 48 with (8 * Z.of_nat 6) by lia. apply (acc_zero_run asegs m8 (f + 32) 6); [clear - F64; Z.div_mod_to_equations; lia | lia |].
    replace (shad (f + 32)) with (f / 8 + 2147450880 + 4) by (unfold shad, SHB; clear - Q1 F64; Z.div_mod_to_equations; lia).
    exact (rw_cells_bytes_at asegs m8 _ _ Z6). }
  destruct (cl_chain_call (rt_cg RT Σ3) e_namemap_new e_ht_new SITE_nm_htnew m8 m8 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG3, CG2, CG1; exact CTX)
              ltac:(rewrite CG3, CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG3, CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF8 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m8 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR8))
              ltac:(rewrite EU1; fold usp; unfold usp1; clear - HP; lia) SPT) as (CTXc8 & UWCc8).
  (* [comment removed for export] *)
  apply (C_HT Σ3 PMc (Z_to_bv 64 SITE_nm_htnew) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) y0 y1 y2 sp (Z_to_bv 64 usp1)
           (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (nm + 16)) (Z_to_bv 64 0) h3 h4 h5 h6 h7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 y3 y4 y5 y6 F7 fc7 m8 lo (bv_unsigned ra :: outer) (f + 32) f 1%nat a0 (Z_to_bv 8 1) canary
           FDO MST eq_refl eq_refl INF3 ltac:(clear; lia) ltac:(change (fs_size 1) with 128; clear; lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) FC8 ACF8 CTXN ART8 MI8
           (COK m8 Σ3 ST8 ltac:(rewrite SP3, SP2; exact SP1))).
  { rewrite EU1. clear - HSTK HP. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_nm_htnew) by (unfold SITE_nm_htnew; lia). exact CTXc8. }
  { exact UWCc8. }
  { rewrite CG3, CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS3, FRS2, FRS1. cbn [length]. clear - Hfr. lia. }
  { rewrite LV3, LV2, LV1. cbn [length]. clear - Hlen. lia. }
  { rewrite CR3, CR2, CR1. unfold HT_COST. clear - Hcr MC1 MC2 MC3 MC4 MC5 MC6 MC7. lia. }
  { exact ENV8. }
  { exact Hc9'. }
  clear Hc9'. intros c10 (Σ4 & ht & lk2 & md & q & L & qp & Hc10 & LV4 & FRS4 & SP4 & CR4 & HT0 & HT16 & HTU & LK20 & LK216 & LK2U & MD0 & MD16 & MDU & Q0 & Q64 & QU & L0 & L16 & LU & QP0 & QP16 & QPU & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c10 Hc10) as (ms10 & (m9 & RS10 & (ART9 & MI9 & WM9 & ST9) & PRES9 & ENV9 & WRh9 & ACCh9 & HT9 & HMD9 & HLK29 & CL0 & CLM1 & CLM2 & CLC1 & CLM3 & CLC2 & CLQ & ZERq9) & Hc10'). clear Hc10.
  destruct RS10 as (z0 & z1 & z2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z3 & z4 & z5 & z6 & F9 & fc9 & ->).
  rewrite EU1 in ST9, PRES9. rewrite (ret_pc_even SITE_nm_htnew) in Hc10' by (unfold SITE_nm_htnew; lia).
  assert (INH4 : In (ht, 96) (rt_live RT Σ4)) by (rewrite LV4; do 5 right; left; reflexivity).
  assert (INN4 : In (nm, 40) (rt_live RT Σ4)) by (rewrite LV4; do 6 right; exact INN3).
  assert (INL4 : In (lk, 40) (rt_live RT Σ4)) by (rewrite LV4; do 6 right; exact INL3).
  assert (INF4 : In (f, 1%nat) (rt_frames RT Σ4)) by (rewrite FRS4; exact INF3).
  assert (LOW4 : rt_sp0 RT Σ4 - STACK_WIN <= lo) by (rewrite SP4; exact LOW3).
  pose proof (afp_live_hi RT GOBJ AFP Σ4 m9 ht 96 ART9 INH4 ltac:(lia)) as HTH.
  assert (AG89 : forall a k, ((usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 120) \/ (shad f <= a /\ a + k <= shad f + 16) \/ (nm <= a /\ a + k <= nm + 40) \/ (lk <= a /\ a + k <= lk + 40))
                             -> agree_on (fun x => a <= x < a + k) m8 m9).
  { intros a k H x Hx. cbv beta in Hx. apply PRES9.
    - destruct H as [H|[H|[H|[H|H]]]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ f 1%nat); [exact INF3 | change (fs_size 1) with 128; clear - H Hx; lia]
        | apply (acl_fshadow _ _ _ f 1%nat); [exact INF3 | rewrite SHF; clear - H Hx; lia] | apply (acl_live _ _ _ nm 40); [exact INN3 | clear - H Hx; lia]
        | apply (acl_live _ _ _ lk 40); [exact INL3 | clear - H Hx; lia]].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H Hx NUM HSTK FIMG Q1 HP NMH LKH. unfold shad, SHB, usp1, USTACK_TOP, RT_STACK in *. Z.div_mod_to_equations. lia. }
  assert (FR9 : rw_cells asegs m9 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m8 m9 _ _ FR8); [| exact WM9]. apply AG89. left. cbn [cells_size csize Nat.add]. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP9 : stk asegs m9 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m8 m9 _ _ GAP8). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG89. left. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (SB9 : rw_cells asegs m9 (f / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs m8 m9 _ _ SB8); [| exact WM9]. apply AG89. right; right; left. unfold nm_shadow, shad, SHB. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HB9 : rw_cells asegs m9 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m8 m9 _ _ HB8); [| exact WM9]. apply AG89. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (TB9 : rw_cells asegs m9 (f + 80) [CB 40 (firstn 40 (skipn 40 (skipn 8 (skipn 32 fj3))))]).
  { apply (rw_cells_agree asegs m8 m9 _ _ TB8); [| exact WM9]. apply AG89. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (FC9 : rw_cells asegs m9 (f + 32) (ht_conf a0)).
  { apply (rw_cells_agree asegs m8 m9 _ _ FC8); [| exact WM9]. apply AG89. right; left. unfold ht_conf. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HNM9 : rw_cells asegs m9 nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m8 m9 _ _ HNM8); [| exact WM9]. apply AG89. right; right; right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HLK9 : rw_cells asegs m9 lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m8 m9 _ _ HLK8); [| exact WM9]. apply AG89. right; right; right; right. unfold mutex_cells. cbn [cells_size csize Nat.add]. clear; lia. }
  pose proof (proj2 (af_acc_live RT AF Σ4 m9 nm 40 ART9 INN4)) as ACCn9.
  assert (AG89u : agree_on (fun x => usp <= x < USTACK_TOP) m8 m9).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG89. left. clear - HP. unfold usp1. lia. }
  pose proof (uw_chain_agree outer m8 m9 sp s0 UWF8 AG89u) as UWF9.
  (* [comment removed for export] *)
  pose proof (nm_w5 sp gp (Z_to_bv 64 TP_A) z0 z1 z2 k1 k2 k3 k4 k5 k6 k7 s4 s8 s9 s10 s11 z3 z4 z5 z6 F9 fc9 m9 f nm lk ht pad
                F0 ltac:(clear - FLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) NMH ltac:(clear - NMU; unfold USTACK_TOP in *; lia) NMA HT0 ltac:(clear - HTU; unfold USTACK_TOP in *; lia) HNM9 ACCn9 MI9) as W5.
  fold usp in W5.
  cl_lift W5 Hc10' c11 Hc11.
  destruct (ASTA_unpack RT Σ4 _ _ c11 Hc11) as (ms11 & (m10 & -> & MU10 & WM10 & MI10 & HNM10) & Hc11'). clear Hc11.
  fold usp in Hc11'. fold usp1 in Hc11'.
  assert (ART10 : ART RT Σ4 m10).
  { apply (af_frame RT AF Σ4 m9 m10 usp1 ART9 ltac:(rewrite SP4, SP3, SP2, SP1; clear - NUM HP; unfold usp1; lia)); [| exact WM10].
    intros a Ha. apply MU10. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ nm 40); [exact INN4 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m9 m10 _ canary ENV9 MU10 ltac:(cl_fp_lia)) as ENV10.
  assert (AG910 : forall a k, (a + k <= nm \/ nm + 40 <= a) -> agree_on (fun x => a <= x < a + k) m9 m10).
  { intros a k H. apply (agree_of_munch _ m9 m10 _ MU10). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST10 : stk asegs m10 lo usp1).
  { apply (stk_munch _ m9 m10 _ _ ST9 MU10 WM10). intros x Hx. cbn [outside]. clear - Hx NMLO LOW HSTK HP. unfold usp1, RT_STACK in *. lia. }
  assert (FR10 : rw_cells asegs m10 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m9 m10 _ _ FR9); [| exact WM10]. apply AG910. cbn [cells_size csize Nat.add]. clear - NMLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (GAP10 : stk asegs m10 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m9 m10 _ _ GAP9). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG910. clear - NMLO LOW HSTK HP. unfold usp1, RT_STACK in *. lia. }
  assert (SB10 : rw_cells asegs m10 (f / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs m9 m10 _ _ SB9); [| exact WM10]. apply AG910. unfold nm_shadow. cbn [cells_size csize Nat.add]. clear - Q1 F0 NMH FLO SP0R. unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  assert (HB10 : rw_cells asegs m10 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m9 m10 _ _ HB9); [| exact WM10]. apply AG910. cbn [cells_size csize Nat.add]. clear - NF. unfold wp_box in *. lia. }
  assert (AG910u : agree_on (fun x => usp <= x < USTACK_TOP) m9 m10).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG910. clear - NMLO LOW HSTK. unfold RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m9 m10 sp s0 UWF9 AG910u) as UWF10.
  destruct (cl_chain_call (rt_cg RT Σ4) e_namemap_new e_OPENSSL_sk_new_null SITE_nm_sknew m10 m10 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG4, CG3, CG2, CG1; exact CTX)
              ltac:(rewrite CG4, CG3, CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG4, CG3, CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF10 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m10 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR10))
              ltac:(rewrite EU1; fold usp; unfold usp1; clear - HP; lia) SPT) as (CTXc10 & UWCc10).
  (* [comment removed for export] *)
  apply (C_SKN Σ4 PMc (Z_to_bv 64 SITE_nm_sknew) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) z0 z1 z2 sp (Z_to_bv 64 usp1)
           (Z_to_bv 64 ht) (Z_to_bv 64 (nm + 8)) (Z_to_bv 64 0) k3 k4 k5 k6 k7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 z3 z4 z5 z6 F9 fc9 m10 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART10 MI10
           (COK m10 Σ4 ST10 ltac:(rewrite SP4, SP3, SP2; exact SP1))).
  { rewrite EU1. clear - HSTK HP. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_nm_sknew) by (unfold SITE_nm_sknew; lia). exact CTXc10. }
  { exact UWCc10. }
  { rewrite CG4, CG3, CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV4, LV3, LV2, LV1. cbn [length]. clear - Hlen. lia. }
  { rewrite CR4, CR3, CR2, CR1. unfold HT_COST. clear - Hcr MC1 MC2 MC3 MC4 MC5 MC6 MC7. lia. }
  { exact ENV10. }
  { exact Hc11'. }
  clear Hc11'. intros c12 (Σ5 & sk & Hc12 & LV5 & FRS5 & SP5 & CR5 & SK0 & SK16 & SKU & CG5).
  destruct (ASTA_unpack RT Σ5 _ _ c12 Hc12) as (ms12 & (m11 & RS12 & (ART11 & MI11 & WM11 & ST11) & PRES11 & ENV11 & WRs11 & ACCs11 & HSK11) & Hc12'). clear Hc12.
  destruct RS12 as (w0' & w1' & w2' & e1' & e2' & e3' & e4' & e5' & e6' & e7' & w3' & w4' & w5' & w6' & F11 & fc11 & ->).
  rewrite EU1 in ST11, PRES11. rewrite (ret_pc_even SITE_nm_sknew) in Hc12' by (unfold SITE_nm_sknew; lia).
  assert (INS5 : In (sk, 56) (rt_live RT Σ5)) by (rewrite LV5; left; reflexivity).
  assert (INN5 : In (nm, 40) (rt_live RT Σ5)) by (rewrite LV5; right; exact INN4).
  assert (INF5 : In (f, 1%nat) (rt_frames RT Σ5)) by (rewrite FRS5; exact INF4).
  assert (LOW5 : rt_sp0 RT Σ5 - STACK_WIN <= lo) by (rewrite SP5; exact LOW4).
  assert (SP5' : rt_sp0 RT Σ5 = rt_sp0 RT Σ) by (rewrite SP5, SP4, SP3, SP2; exact SP1).
  pose proof (afp_live_hi RT GOBJ AFP Σ5 m11 sk 56 ART11 INS5 ltac:(lia)) as SKH.
  pose proof (af_live_range RT AF Σ5 m11 sk 56 ART11 INS5) as (_ & SKLO & _). rewrite SP5' in SKLO.
  pose proof (af_live_disj RT AF Σ5 m11 sk 56 nm 40 [] (rt_live RT Σ4) ART11 LV5 INN4) as SKN. wp_box1 SKN.
  assert (FR11 : rw_cells asegs m11 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m10 m11 _ _ FR10); [| exact WM11]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply PRES11; [left; clear - Hx HP NUM; unfold usp1; lia|].
    cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - Hx NUM HSTK. unfold USTACK_TOP, RT_STACK in *. lia. }
  assert (ST11' : stk asegs m11 lo usp1) by exact ST11.
  assert (AG1011u : agree_on (fun x => usp <= x < USTACK_TOP) m10 m11).
  { intros a Ha. cbv beta in Ha. apply PRES11; [left; clear - Ha HP NUM; unfold usp1; lia|]. cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - Ha NUM HSTK. unfold USTACK_TOP, RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m10 m11 sp s0 UWF10 AG1011u) as UWF11.
  (* [comment removed for export] *)
  pose proof (nm_w6 sp gp (Z_to_bv 64 TP_A) w0' w1' w2' e1' e2' e3' e4' e5' e6' e7' s4 s8 s9 s10 s11 w3' w4' w5' w6' F11 fc11 m11 f nm sk pad MI11) as W6.
  fold usp in W6.
  cl_lift W6 Hc12' c13 Hc13.
  destruct (ASTA_unpack RT Σ5 _ _ c13 Hc13) as (ms13 & E13 & Hc13'). clear Hc13. unfold nm_w6_post in E13. subst ms13. fold usp in Hc13'. fold usp1 in Hc13'.
  apply (C_SKCMP Σ5 PMc (Z_to_bv 64 SITE_nm_cmp) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0' w1' w2' sp (Z_to_bv 64 usp1)
           (Z_to_bv 64 sk) (Z_to_bv 64 NM_CMP_THUNK) e2' e3' e4' e5' e6' e7' (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 w3' w4' w5' w6' F11 fc11 m11 lo sk
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
           FDO MST eq_refl eq_refl ART11 MI11 (COK m11 Σ5 ST11 SP5') ltac:(rewrite EU1; clear - HSTK HP; unfold usp1, RT_STACK in *; lia) INS5 SK16 HSK11 (ubs_raw8 sk (wg_mod16_8 _ SK16)) _ _ Hc13').
  clear Hc13'. intros c14 Hc14.
  destruct (ASTA_unpack RT Σ5 _ _ c14 Hc14) as (ms14 & (m12 & RS14 & (ART12 & MI12 & WM12 & ST12) & PRES12 & HSK12) & Hc14'). clear Hc14.
  destruct RS14 as (o0 & o1 & o2 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & o3 & o4 & o5 & o6 & F12 & fc12 & ->).
  rewrite EU1 in ST12, PRES12. rewrite (ret_pc_even SITE_nm_cmp) in Hc14' by (unfold SITE_nm_cmp; lia).
  (* [comment removed for export] *)
  assert (SAG : forall mA mB, rt_pres_fp (rt_live RT Σ5) (rt_frames RT Σ5) usp1 [(sk, sk + 56)] mA mB ->
            forall a k, ((usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 120) \/ (shad f <= a /\ a + k <= shad f + 16) \/ (nm <= a /\ a + k <= nm + 40))
            -> agree_on (fun x => a <= x < a + k) mA mB).
  { intros mA mB P a k H x Hx. cbv beta in Hx. apply P.
    - destruct H as [H|[H|[H|H]]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ f 1%nat); [exact INF5 | change (fs_size 1) with 128; clear - H Hx; lia]
        | apply (acl_fshadow _ _ _ f 1%nat); [exact INF5 | rewrite SHF; clear - H Hx; lia] | apply (acl_live _ _ _ nm 40); [exact INN5 | clear - H Hx; lia]].
    - cbn [outside]. split; [| exact I].
      destruct H as [H|[H|[H|H]]]; [clear - H Hx SKLO LOW HSTK HP; unfold usp1, RT_STACK in *; lia | | clear - H Hx SKH Q1 F0 FLO SP0R; unfold shad, SHB, USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia | clear - H Hx SKN; unfold wp_box in *; lia].
      pose proof (af_frames_range RT AF Σ5 m11 f 1%nat ART11 INF5) as (_ & _ & _ & SF). specialize (SF sk 56 INS5). change (fs_size 1) with 128 in SF. clear - H Hx SF. lia. }
  assert (SAGu : forall mA mB, rt_pres_fp (rt_live RT Σ5) (rt_frames RT Σ5) usp1 [(sk, sk + 56)] mA mB -> agree_on (fun x => usp <= x < USTACK_TOP) mA mB).
  { intros mA mB P. replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply (SAG mA mB P). left. clear - HP. unfold usp1. lia. }
  pose proof (uw_chain_agree outer m11 m12 sp s0 UWF11 (SAGu _ _ PRES12)) as UWF12.
  (* [comment removed for export] *)
  pose proof (nm_w7 sp gp (Z_to_bv 64 TP_A) o0 o1 o2 p1 p2 p3 p4 p5 p6 p7 s8 s9 s10 s11 o3 o4 o5 o6 F12 fc12 m12 f nm sk pad MI12) as W7.
  fold usp in W7.
  cl_lift W7 Hc14' c15 Hc15.
  destruct (ASTA_unpack RT Σ5 _ _ c15 Hc15) as (ms15 & E15 & Hc15'). clear Hc15. unfold nm_w7_post in E15. subst ms15. fold usp in Hc15'. fold usp1 in Hc15'.
  apply (C_SKCPY Σ5 PMc (Z_to_bv 64 SITE_nm_copy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) o0 o1 o2 sp (Z_to_bv 64 usp1)
           (Z_to_bv 64 sk) (Z_to_bv 64 NM_COPY_THUNK) p2 p3 p4 p5 p6 p7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 o3 o4 o5 o6 F12 fc12 m12 lo sk
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 NM_CMP_THUNK) (Z_to_bv 64 0) (Z_to_bv 64 0)
           FDO MST eq_refl eq_refl ART12 MI12 (COK m12 Σ5 ST12 SP5') ltac:(rewrite EU1; clear - HSTK HP; unfold usp1, RT_STACK in *; lia) INS5 SK16 HSK12 (ubs_raw8 sk (wg_mod16_8 _ SK16)) _ _ Hc15').
  clear Hc15'. intros c16 Hc16.
  destruct (ASTA_unpack RT Σ5 _ _ c16 Hc16) as (ms16 & (m13 & RS16 & (ART13 & MI13 & WM13 & ST13) & PRES13 & HSK13) & Hc16'). clear Hc16.
  destruct RS16 as (o0' & o1' & o2' & p1' & p2' & p3' & p4' & p5' & p6' & p7' & o3' & o4' & o5' & o6' & F13 & fc13 & ->).
  rewrite EU1 in ST13, PRES13. rewrite (ret_pc_even SITE_nm_copy) in Hc16' by (unfold SITE_nm_copy; lia).
  pose proof (uw_chain_agree outer m12 m13 sp s0 UWF12 (SAGu _ _ PRES13)) as UWF13.
  (* [comment removed for export] *)
  pose proof (nm_w8 sp gp (Z_to_bv 64 TP_A) o0' o1' o2' p1' p2' p3' p4' p5' p6' p7' s8 s9 s10 s11 o3' o4' o5' o6' F13 fc13 m13 f nm sk pad MI13) as W8.
  fold usp in W8.
  cl_lift W8 Hc16' c17 Hc17.
  destruct (ASTA_unpack RT Σ5 _ _ c17 Hc17) as (ms17 & E17 & Hc17'). clear Hc17. unfold nm_w8_post in E17. subst ms17. fold usp in Hc17'. fold usp1 in Hc17'.
  apply (C_SKSET Σ5 PMc (Z_to_bv 64 SITE_nm_set) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) o0' o1' o2' sp (Z_to_bv 64 usp1)
           (Z_to_bv 64 sk) (Z_to_bv 64 NM_SET_THUNK) p2' p3' p4' p5' p6' p7' (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 o3' o4' o5' o6' F13 fc13 m13 lo sk
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 NM_CMP_THUNK) (Z_to_bv 64 0) (Z_to_bv 64 NM_COPY_THUNK)
           FDO MST eq_refl eq_refl ART13 MI13 (COK m13 Σ5 ST13 SP5') ltac:(rewrite EU1; clear - HSTK HP; unfold usp1, RT_STACK in *; lia) INS5 SK16 HSK13 (ubs_raw8 sk (wg_mod16_8 _ SK16)) _ _ Hc17').
  clear Hc17'. intros c18 Hc18.
  destruct (ASTA_unpack RT Σ5 _ _ c18 Hc18) as (ms18 & (m14 & RS18 & (ART14 & MI14 & WM14 & ST14) & PRES14 & HSK14) & Hc18'). clear Hc18.
  destruct RS18 as (o0'' & o1'' & o2'' & p1'' & p2'' & p3'' & p4'' & p5'' & p6'' & p7'' & o3'' & o4'' & o5'' & o6'' & F14 & fc14 & ->).
  rewrite EU1 in ST14, PRES14. rewrite (ret_pc_even SITE_nm_set) in Hc18' by (unfold SITE_nm_set; lia).
  pose proof (uw_chain_agree outer m13 m14 sp s0 UWF13 (SAGu _ _ PRES14)) as UWF14.
  (* [comment removed for export] *)
  assert (AG1011 : forall a k, ((usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 120) \/ (shad f <= a /\ a + k <= shad f + 16) \/ (nm <= a /\ a + k <= nm + 40) \/ (lk <= a /\ a + k <= lk + 40))
                               -> agree_on (fun x => a <= x < a + k) m10 m11).
  { intros a k H x Hx. cbv beta in Hx. apply PRES11.
    - destruct H as [H|[H|[H|[H|H]]]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ f 1%nat); [exact INF4 | change (fs_size 1) with 128; clear - H Hx; lia]
        | apply (acl_fshadow _ _ _ f 1%nat); [exact INF4 | rewrite SHF; clear - H Hx; lia] | apply (acl_live _ _ _ nm 40); [exact INN4 | clear - H Hx; lia]
        | apply (acl_live _ _ _ lk 40); [exact INL4 | clear - H Hx; lia]].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H Hx NUM HSTK FIMG Q1 HP NMH LKH. unfold shad, SHB, usp1, USTACK_TOP, RT_STACK in *. Z.div_mod_to_equations. lia. }
  assert (HNM14 : rw_cells asegs m14 nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m13 m14); [apply (rw_cells_agree asegs m12 m13); [apply (rw_cells_agree asegs m11 m12); [apply (rw_cells_agree asegs m10 m11 _ _ HNM10); [| exact WM11] | | exact WM12] | | exact WM13] | | exact WM14].
    - apply AG1011. right; right; right; left. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES12). right; right; right. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES13). right; right; right. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES14). right; right; right. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (FR14 : rw_cells asegs m14 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m13 m14); [apply (rw_cells_agree asegs m12 m13); [apply (rw_cells_agree asegs m11 m12 _ _ FR11); [| exact WM12] | | exact WM13] | | exact WM14].
    - apply (SAG _ _ PRES12). left. cbn [cells_size csize Nat.add]. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia.
    - apply (SAG _ _ PRES13). left. cbn [cells_size csize Nat.add]. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia.
    - apply (SAG _ _ PRES14). left. cbn [cells_size csize Nat.add]. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP14 : stk asegs m14 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m13 m14); [apply (stk_agree_nw asegs m12 m13); [apply (stk_agree_nw asegs m11 m12); [apply (stk_agree_nw asegs m10 m11 _ _ GAP10)|]|]|].
    all: replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia.
    - apply AG1011. left. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia.
    - apply (SAG _ _ PRES12). left. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia.
    - apply (SAG _ _ PRES13). left. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia.
    - apply (SAG _ _ PRES14). left. clear - NUM HP. unfold usp1, USTACK_TOP in *. lia. }
  assert (SB14 : rw_cells asegs m14 (f / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs m13 m14); [apply (rw_cells_agree asegs m12 m13); [apply (rw_cells_agree asegs m11 m12); [apply (rw_cells_agree asegs m10 m11 _ _ SB10); [| exact WM11] | | exact WM12] | | exact WM13] | | exact WM14].
    - apply AG1011. right; right; left. unfold nm_shadow, shad, SHB. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES12). right; right; left. unfold nm_shadow, shad, SHB. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES13). right; right; left. unfold nm_shadow, shad, SHB. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES14). right; right; left. unfold nm_shadow, shad, SHB. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HB14 : rw_cells asegs m14 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m13 m14); [apply (rw_cells_agree asegs m12 m13); [apply (rw_cells_agree asegs m11 m12); [apply (rw_cells_agree asegs m10 m11 _ _ HB10); [| exact WM11] | | exact WM12] | | exact WM13] | | exact WM14].
    - apply AG1011. right; left. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES12). right; left. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES13). right; left. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (SAG _ _ PRES14). right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  pose proof (proj2 (af_acc_live RT AF Σ5 m14 nm 40 ART14 (ltac:(rewrite LV5; right; exact INN4)))) as ACCn14.
  assert (ENV14 : cl_env m14 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m13 m14); [apply (cl_env_agree m12 m13); [apply (cl_env_agree m11 m12 _ _ ENV11)|]|].
    all: intros a Ha; pose proof (client_static_range _ (cl_cell_static _ Ha)) as XR.
    - apply PRES12; [right; left; exact (cl_cell_static _ Ha) | cbn [outside]; split; [| exact I]; clear - XR SKH; unfold SEGTOP_A in *; lia].
    - apply PRES13; [right; left; exact (cl_cell_static _ Ha) | cbn [outside]; split; [| exact I]; clear - XR SKH; unfold SEGTOP_A in *; lia].
    - apply PRES14; [right; left; exact (cl_cell_static _ Ha) | cbn [outside]; split; [| exact I]; clear - XR SKH; unfold SEGTOP_A in *; lia]. }
  (* [comment removed for export] *)
  pose proof (nm_w9 sp gp (Z_to_bv 64 TP_A) o0'' o1'' o2'' p1'' p2'' p3'' p4'' p5'' p6'' p7'' s8 s9 s10 s11 o3'' o4'' o5'' o6'' F14 fc14 m14 f nm lk ht sk pad
                F0 ltac:(clear - FLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) NMH ltac:(clear - NMU; unfold USTACK_TOP in *; lia) NMA SK0 ltac:(clear - SKU; unfold USTACK_TOP in *; lia) HNM14 ACCn14 MI14) as W9.
  fold usp in W9.
  cl_lift W9 Hc18' c19 Hc19.
  destruct (ASTA_unpack RT Σ5 _ _ c19 Hc19) as (ms19 & (m15 & -> & MU15 & WM15 & MI15 & HNM15) & Hc19'). clear Hc19.
  fold usp in Hc19'. fold usp1 in Hc19'.
  assert (ART15 : ART RT Σ5 m15).
  { apply (af_frame RT AF Σ5 m14 m15 usp1 ART14 ltac:(rewrite SP5'; clear - NUM HP; unfold usp1; lia)); [| exact WM15].
    intros a Ha. apply MU15. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ nm 40); [exact INN5 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m14 m15 _ canary ENV14 MU15 ltac:(cl_fp_lia)) as ENV15.
  assert (AG1415 : forall a k, (a + k <= nm \/ nm + 40 <= a) -> agree_on (fun x => a <= x < a + k) m14 m15).
  { intros a k H. apply (agree_of_munch _ m14 m15 _ MU15). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST15 : stk asegs m15 lo usp1).
  { apply (stk_munch _ m14 m15 _ _ ST14 MU15 WM15). intros x Hx. cbn [outside]. clear - Hx NMLO LOW HSTK HP. unfold usp1, RT_STACK in *. lia. }
  assert (FR15 : rw_cells asegs m15 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m14 m15 _ _ FR14); [| exact WM15]. apply AG1415. cbn [cells_size csize Nat.add]. clear - NMLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (GAP15 : stk asegs m15 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m14 m15 _ _ GAP14). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG1415. clear - NMLO LOW HSTK HP. unfold usp1, RT_STACK in *. lia. }
  assert (SB15 : rw_cells asegs m15 (f / 8 + 2147450880) [CB 16 (cells_bytes nm_shadow)]).
  { apply (rw_cells_agree asegs m14 m15 _ _ (rw_cells_blur_all' _ _ _ SB14)); [| exact WM15]. apply AG1415. unfold nm_shadow. cbn [cells_size csize Nat.add]. clear - Q1 F0 NMH FLO SP0R. unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  assert (HB15 : rw_cells asegs m15 f [CB 32 (firstn 32 fj3)]).
  { apply (rw_cells_agree asegs m14 m15 _ _ HB14); [| exact WM15]. apply AG1415. cbn [cells_size csize Nat.add]. clear - NF. unfold wp_box in *. lia. }
  (* [comment removed for export] *)
  pose proof (nm_w10 sp gp (Z_to_bv 64 TP_A) o0'' o1'' o2'' (Z_to_bv 64 sk) (Z_to_bv 64 (nm + 24)) (Z_to_bv 64 0) p3'' p4'' p5'' p6'' p7'' s8 s9 s10 s11 o3'' o4'' o5'' o6'' F14 fc14 m15 f nm sk lo pad _ _
                ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) F0 FIMG ltac:(clear - FLO LOW; lia) ltac:(destruct FSH; [left | right]; lia) ST15 HB15 SB15 MI15) as W10.
  fold usp in W10.
  cl_lift W10 Hc19' c20 Hc20.
  destruct (ASTA_unpack RT Σ5 _ _ c20 Hc20) as (ms20 & (a0' & hj16 & sj16 & m16 & -> & MU16 & WM16 & MI16 & ST16 & HB16 & SB16) & Hc20'). clear Hc20.
  fold usp in Hc20'. fold usp1 in ST16, Hc20'.
  assert (ART16 : ART RT Σ5 m16).
  { apply (af_frame RT AF Σ5 m15 m16 usp1 ART15 ltac:(rewrite SP5'; clear - NUM HP; unfold usp1; lia)); [| exact WM16].
    intros a Ha. apply MU16. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 1%nat); [exact INF5 | change (fs_size 1) with 128; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ f 1%nat); [exact INF5 | rewrite SHF; unfold shad, SHB; clear - Hin; lia]. }
  pose proof (cl_env_seg _ m15 m16 _ canary ENV15 MU16 ltac:(cl_fp_lia)) as ENV16.
  assert (AG1516 : forall a k, (a + k <= f \/ f + 32 <= a) -> (a + k <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= a) -> agree_on (fun x => a <= x < a + k) m15 m16).
  { intros a k H1 H2. apply (agree_of_munch _ m15 m16 _ MU16). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H1 H2 Hx. lia. }
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000).
  { clear - F0 FLO SP0R Q1. unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  assert (FR16 : rw_cells asegs m16 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m15 m16 _ _ FR15); [| exact WM16]. apply AG1516; cbn [cells_size csize Nat.add]; clear - FLO LOW HSTK SHR NUM; unfold RT_STACK in *; lia. }
  assert (GAP16 : stk asegs m16 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m15 m16 _ _ GAP15). replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG1516; clear - FLO LOW HSTK SHR NUM HP; unfold usp1, RT_STACK in *; lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ5 m16 f 1%nat (rt_frames RT Σ) ART16 ltac:(rewrite FRS5, FRS4, FRS3, FRS2; exact FRS1)) as (Σ6 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 1) with 128 in FW. replace (f + 128 - 8) with (f + 120) in FW by lia. rewrite SP5' in FLW.
  (* [comment removed for export] *)
  pose proof (nm_w11 ra sp gp (Z_to_bv 64 TP_A) o0'' o1'' o2'' a0' (Z_to_bv 64 (nm + 24)) (Z_to_bv 64 0) p3'' p4'' p5'' p6'' p7'' s8 s9 s10 s11 o3'' o4'' o5'' o6''
                s0 s1 s2 s3 s4 s5 s6 s7 F14 fc14 m16 nm f sk fl lo pad j3
                HP ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) F0 ltac:(clear - FLO LOW; lia) FL0 ltac:(clear - FLW LOW; lia) ST16 GAP16 FR16 FW FLC MI16) as W11.
  fold usp usp1 in W11.
  cl_lift W11 Hc20' c21 Hc21.
  destruct (ASTA_unpack RT Σ5 _ _ c21 Hc21) as (ms21 & (m17 & -> & MU17 & WM17 & MI17 & ST17 & FLC17) & Hc21'). clear Hc21.
  fold usp in ST17.
  destruct (REL m17 MU17 WM17 FLC17) as (ART17 & FRS6 & LV6 & SP6 & CR6 & AL6 & AM6 & CG6).
  (* [comment removed for export] *)
  assert (LV6' : rt_live RT Σ6 = (sk, 56) :: (qp, 16) :: (L, 264) :: (q, NB_BYTES) :: (md, 24) :: (lk2, 40) :: (ht, 96) :: (lk, 40) :: (nm, 40) :: rt_live RT Σ)
    by (rewrite LV6, LV5, LV4, LV3, LV2, LV1; reflexivity).
  assert (NFL : forall x, aclient (rt_live RT Σ5) (rt_frames RT Σ5) usp1 x -> x <> fl).
  { intros x Hx E. subst x. apply NAC. destruct Hx as [H|H]; [exfalso; clear - H FLW LOW HSTK HP; unfold usp1, RT_STACK in *; lia | right; exact H]. }
  assert (AG1617 : forall a k, (forall x, a <= x < a + k -> x <> fl) -> agree_on (fun x => a <= x < a + k) m16 m17).
  { intros a k H. apply (agree_of_munch _ m16 m17 _ MU17). intros x Hx. cbv beta in Hx. specialize (H x Hx). cbn [outside]. clear - H. lia. }
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Σ4 m9 f 1%nat ART9 INF4) as (_ & _ & _ & PF4). change (fs_size 1) with 128 in PF4.
  assert (HEAP : forall p n, In (p, n) (rt_live RT Σ4) -> n <= 64512 -> (p + n <= nm \/ nm + 40 <= p) -> forall a k, p <= a -> a + k <= p + n -> agree_on (fun x => a <= x < a + k) m9 m17).
  { intros p n INp Hn Dn a k H1 H2 x Hx. cbv beta in Hx.
    pose proof (afp_live_hi RT GOBJ AFP Σ4 m9 p n ART9 INp Hn) as PH.
    pose proof (af_live_disj RT AF Σ5 m11 sk 56 p n [] (rt_live RT Σ4) ART11 LV5 INp) as PS.
    pose proof (PF4 p n INp) as PFp.
    assert (INp5 : In (p, n) (rt_live RT Σ5)) by (rewrite LV5; right; exact INp).
    pose proof (NFL (bv_unsigned x) (acl_live _ _ _ p n (bv_unsigned x) INp5 ltac:(clear - H1 H2 Hx; lia))) as Nf.
    rewrite (MU17 x ltac:(cbn [outside]; split; [clear - Nf; lia | exact I])).
    rewrite (MU16 x ltac:(cbn [outside]; clear - H1 H2 Hx PFp PH SHR; lia)).
    rewrite (MU15 x ltac:(cbn [outside]; clear - H1 H2 Hx Dn; lia)).
    rewrite (PRES14 x (acl_live _ _ _ p n (bv_unsigned x) INp5 ltac:(clear - H1 H2 Hx; lia)) ltac:(cbn [outside]; clear - H1 H2 Hx PS; lia)).
    rewrite (PRES13 x (acl_live _ _ _ p n (bv_unsigned x) INp5 ltac:(clear - H1 H2 Hx; lia)) ltac:(cbn [outside]; clear - H1 H2 Hx PS; lia)).
    rewrite (PRES12 x (acl_live _ _ _ p n (bv_unsigned x) INp5 ltac:(clear - H1 H2 Hx; lia)) ltac:(cbn [outside]; clear - H1 H2 Hx PS; lia)).
    rewrite (PRES11 x (acl_live _ _ _ p n (bv_unsigned x) INp ltac:(clear - H1 H2 Hx; lia)) ltac:(cbn [outside]; unfold G_ALLOW_CUST; clear - H1 H2 Hx PH; lia)).
    apply (MU10 x). cbn [outside]. clear - H1 H2 Hx Dn. lia. }
  assert (WM917 : wmono asegs m9 m17).
  { exact (wmono_trans asegs _ _ _ WM10 (wmono_trans asegs _ _ _ WM11 (wmono_trans asegs _ _ _ WM12 (wmono_trans asegs _ _ _ WM13 (wmono_trans asegs _ _ _ WM14
          (wmono_trans asegs _ _ _ WM15 (wmono_trans asegs _ _ _ WM16 WM17))))))). }
  assert (WM017 : wmono asegs m m17).
  { exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5
          (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 (wmono_trans asegs _ _ _ WM9 WM917))))))))). }
  (* [comment removed for export] *)
  assert (NMD : forall p n, In (p, n) [(qp, 16); (L, 264); (q, NB_BYTES); (md, 24); (lk2, 40); (ht, 96); (lk, 40)] -> p + n <= nm \/ nm + 40 <= p).
  { intros p n Hin. destruct (af_live_disj RT AF Σ4 m9 nm 40 p n [(qp, 16); (L, 264); (q, NB_BYTES); (md, 24); (lk2, 40); (ht, 96); (lk, 40)] (rt_live RT Σ) ART9
              ltac:(rewrite LV4, LV3, LV2, LV1; reflexivity) ltac:(apply in_or_app; left; exact Hin)); [right | left]; lia. }
  apply Hk. exists Σ6, nm, lk, ht, lk2, md, q, L, qp, sk.
  split; [| split; [exact LV6' | split; [rewrite FRS6; reflexivity | split; [rewrite SP6; exact SP5' | split; [rewrite CR6, CR5, CR4, CR3, CR2, CR1; unfold NM_COST; clear; lia |]]]]].
  2: { repeat (split; [assumption|]). rewrite CG6, CG5, CG4, CG3, CG2; exact CG1. }
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ5 Σ6 PMc _ c21 Hc21' AL6 AM6)|]. intros ms <-. exists m17.
  split; [exists o0'', o1'', o2'', (Z_to_bv 64 (nm + 24)), (Z_to_bv 64 0), p3'', p4'', p5'', p6'', p7'', o3'', o4'', o5'', o6'', F14, fc14; reflexivity|].
  split; [split; [exact ART17 | split; [exact MI17 | split; [exact WM017 | exact ST17]]]|].
  split.
  { intros a Ha Ho.
    assert (A0' : aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | clear - HP; unfold usp1; lia]).
    assert (A1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A0'); [rewrite LV1; auto | rewrite FRS1; intros e He; right; exact He | clear; lia]).
    assert (A2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A1); [rewrite LV2; intros e He; right; exact He | rewrite FRS2; auto | clear; lia]).
    assert (A3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A2); [rewrite LV3; intros e He; right; exact He | rewrite FRS3; auto | clear; lia]).
    assert (A4 : aclient (rt_live RT Σ4) (rt_frames RT Σ4) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A3); [rewrite LV4; intros e He; do 6 right; exact He | rewrite FRS4; auto | clear; lia]).
    assert (A5 : aclient (rt_live RT Σ5) (rt_frames RT Σ5) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A4); [rewrite LV5; intros e He; right; exact He | rewrite FRS5; auto | clear; lia]).
    destruct (newframe_apart RT AF Σ Σ1 m2 f 1%nat usp _ ART2 FRS1 LV1 SP1 ltac:(clear - NUM; lia) Ha) as (N1 & N2).
    change (fs_size 1) with 128 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    pose proof (newchunk_apart RT AF Σ1 Σ2 m6 nm 40 usp1 _ ART6 LV2 FRS2 SP2 ltac:(rewrite SP1; clear - NUM HP; unfold usp1; lia) ltac:(clear; lia) A1) as Nn.
    pose proof (newchunk_apart RT AF Σ4 Σ5 m11 sk 56 usp1 _ ART11 LV5 FRS5 SP5 ltac:(rewrite SP4, SP3, SP2, SP1; clear - NUM HP; unfold usp1; lia) ltac:(clear; lia) A4) as Ns.
    pose proof (cl_split RT AF Σ m usp 96 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Ha) as N5.
    pose proof (NFL _ A5) as N6.
    rewrite (MU17 a ltac:(cbn [outside]; split; [clear - N6; lia | exact I])).
    rewrite (MU16 a ltac:(cbn [outside]; clear - N1 N2; lia)).
    rewrite (MU15 a ltac:(cbn [outside]; clear - Nn; lia)).
    rewrite (PRES14 a A5 ltac:(cbn [outside]; clear - Ns; split; [lia | exact I])).
    rewrite (PRES13 a A5 ltac:(cbn [outside]; clear - Ns; split; [lia | exact I])).
    rewrite (PRES12 a A5 ltac:(cbn [outside]; clear - Ns; split; [lia | exact I])).
    rewrite (PRES11 a A4 Ho).
    rewrite (MU10 a ltac:(cbn [outside]; clear - Nn; lia)).
    rewrite (PRES9 a A3 Ho).
    rewrite (MU8 a ltac:(cbn [outside]; clear - Nn; lia)).
    rewrite (PRES7 a A2 Ho).
    rewrite (PRES6 a A1 Ho).
    rewrite (MU5 a ltac:(cbn [outside]; clear - N1; lia)).
    rewrite (PRES4 a A1 ltac:(clear - N1; lia)).
    rewrite (MU3 a ltac:(cbn [outside]; unfold usp1 in *; clear - N1 N2 N5 HP; lia)).
    rewrite (PRES2 a A0').
    exact (PR1 a Ha I). }
  split.
  { apply (cl_env_agree m16 m17 _ _ ENV16). intros a Ha'. apply MU17. cbn [outside]. split; [| exact I].
    pose proof (NFL (bv_unsigned a) ltac:(right; left; exact (cl_cell_static _ Ha'))) as Nf. clear - Nf. lia. }
  pose proof (af_acc_live RT AF Σ6 m17 nm 40 ART17 ltac:(rewrite LV6'; do 8 right; left; reflexivity)) as (WRn17 & ACCn17).
  split; [exact WRn17|]. split; [exact ACCn17|].
  split.
  { apply (rw_cells_agree asegs m15 m17 _ _ HNM15); [| exact (wmono_trans asegs _ _ _ WM16 WM17)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (NFL (bv_unsigned x) (acl_live _ _ _ nm 40 (bv_unsigned x) INN5 ltac:(clear - Hx; lia))) as Nf.
    rewrite (MU17 x ltac:(cbn [outside]; split; [clear - Nf; lia | exact I])).
    apply (MU16 x). cbn [outside]. unfold wp_box in NF. clear - Hx NF NMH SHR. lia. }
  assert (INs : forall p n, In (p, n) [(qp, 16); (L, 264); (q, NB_BYTES); (md, 24); (lk2, 40); (ht, 96); (lk, 40)] -> In (p, n) (rt_live RT Σ4)).
  { intros p n Hin. rewrite LV4, LV3. cbn [In app] in Hin |- *. clear - Hin. tauto. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ HLK9); [| exact WM917]. apply (HEAP lk 40 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold mutex_cells; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ HT9); [| exact WM917]. apply (HEAP ht 96 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold ht_tab4; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ HMD9); [| exact WM917]. apply (HEAP md 24 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ HLK29); [| exact WM917]. apply (HEAP lk2 40 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold mutex_cells; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ CL0); [| exact WM917]. apply (HEAP L 264 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold rcu_head; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ CLM1); [| exact WM917]. apply (HEAP L 264 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold mutex_cells; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ CLM2); [| exact WM917]. apply (HEAP L 264 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold mutex_cells; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ CLC1); [| exact WM917]. apply (HEAP L 264 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold cond_cells; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ CLM3); [| exact WM917]. apply (HEAP L 264 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold mutex_cells; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ CLC2); [| exact WM917]. apply (HEAP L 264 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); unfold cond_cells; cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (rw_cells_agree asegs m9 m17 _ _ CLQ); [| exact WM917]. apply (HEAP qp 16 ltac:(apply INs; clear; cbn; tauto) ltac:(clear; lia) ltac:(apply NMD; clear; cbn; tauto)); cbn [cells_size csize Nat.add]; clear; lia. }
  split.
  { apply (bytes_at_agree asegs m9 m17 _ _ ZERq9). rewrite repeat_length, Z2Nat.id by (unfold NB_BYTES; clear; lia).
    apply (HEAP q NB_BYTES ltac:(apply INs; clear; cbn; tauto) ltac:(unfold NB_BYTES; clear; lia) ltac:(apply NMD; clear; cbn; tauto)); clear; lia. }
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Σ5 m11 f 1%nat ART11 INF5) as (_ & _ & _ & SF). specialize (SF sk 56 INS5). change (fs_size 1) with 128 in SF.
  apply (rw_cells_agree asegs m14 m17 _ _ HSK14); [| exact (wmono_trans asegs _ _ _ WM15 (wmono_trans asegs _ _ _ WM16 WM17))]. unfold NM_CMP_THUNK, NM_SET_THUNK, NM_COPY_THUNK.
  intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
  pose proof (NFL (bv_unsigned x) (acl_live _ _ _ sk 56 (bv_unsigned x) INS5 ltac:(clear - Hx; lia))) as Nf.
  rewrite (MU17 x ltac:(cbn [outside]; split; [clear - Nf; lia | exact I])).
  rewrite (MU16 x ltac:(cbn [outside]; clear - Hx SF SKH SHR; lia)).
  apply (MU15 x). cbn [outside]. unfold wp_box in SKN. clear - Hx SKN. lia.
Qed.
End NamemapNew.
