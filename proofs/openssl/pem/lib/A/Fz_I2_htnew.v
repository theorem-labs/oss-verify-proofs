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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_locknew Fz_M_aligned Fz_M_aligned_array Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).

(* [comment removed for export] *)
Lemma memalign_plain_nb : memalign_plain 64 NB_BYTES.
Proof. unfold memalign_plain, NB_BYTES. repeat split; vm_compute; try reflexivity; try lia; discriminate. Qed.

(* [comment removed for export] *)
Lemma rw_CB_of_bytes : forall (m : mem) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) -> rw_cells asegs m a [CB (length bs) bs].
Proof.
  intros m a bs BA WR. split.
  - split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
Qed.

Section HtNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_LN : crypto_lock_new_env_stmt RT.
Hypothesis C_ANL : anl_stmt RT.
Hypothesis C_RCU : rcu_lock_new_stmt RT.

Definition HT_SITES : list (Z * Z) :=
  [(SITE_ht_zalloc1, e_ht_new); (SITE_ht_locknew, e_ht_new); (SITE_ht_zalloc2, e_ht_new); (SITE_ht_anl, e_ht_new); (SITE_ht_rcu, e_ht_new);
   (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_lock_new)] ++ ANL_SITES ++ RCU_SITES.
Definition HT_CALLS : list (Z * Z) :=
  [(SITE_ht_zalloc1, e_CRYPTO_zalloc); (SITE_ht_locknew, e_lock_new); (SITE_ht_zalloc2, e_CRYPTO_zalloc); (SITE_ht_anl, e_anl); (SITE_ht_rcu, e_rcu_lock_new);
   (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc)] ++ ANL_CALLS ++ RCU_CALLS.
Definition HT_COST : Z := mcost 96 + 1 + mcost 24 + (1 + mcost NB_BYTES) + (1 + mcost 264 + mcost 16).

(* [comment removed for export] *)
Definition ht_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (conf fcf : Z) (kcf : nat) (ctx : word) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 conf ->
  In (fcf, kcf) (rt_frames RT Σ) -> fcf <= conf -> conf + 48 <= fcf + fs_size kcf - 8 -> conf mod 8 = 0 ->
  rw_cells asegs m conf (ht_conf ctx) -> acc asegs m conf 48 -> bv_unsigned ctx <> 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x290 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ht_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) HT_SITES HT_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 6 <= LIVE_MAX -> HT_COST <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ht_new m)))
    (fun c => exists (Σ' : rts RT) (nw lk md q L qp : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 nw) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' nw 96 /\ acc asegs m' nw 96
           /\ rw_cells asegs m' nw (ht_tab4 ctx L lk md)
           /\ rw_cells asegs m' md [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 511)]
           /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' L (rcu_head ctx qp)
           /\ rw_cells asegs m' (L + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' (L + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' (L + 128) cond_cells
           /\ rw_cells asegs m' (L + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' (L + 216) cond_cells
           /\ rw_cells asegs m' qp [CB 16 (repeat (Z_to_bv 8 0) 16)]
           /\ bytes_at asegs m' q (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))) c
       /\ rt_live RT Σ' = (qp, 16) :: (L, 264) :: (q, NB_BYTES) :: (md, 24) :: (lk, 40) :: (nw, 96) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - HT_COST
       /\ 0 < nw /\ nw mod 16 = 0 /\ nw + 96 < USTACK_TOP /\ 0 < lk /\ lk mod 16 = 0 /\ lk + 40 < USTACK_TOP
       /\ 0 < md /\ md mod 16 = 0 /\ md + 24 < USTACK_TOP /\ 0 < q /\ q mod 64 = 0 /\ q + NB_BYTES < USTACK_TOP
       /\ 0 < L /\ L mod 16 = 0 /\ L + 264 < USTACK_TOP /\ 0 < qp /\ qp mod 16 = 0 /\ qp + 16 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ht_new_cps : ht_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer conf fcf kcf ctx lb canary
    FDO MST -> -> INFC FC1 FC2 CAL HC0 ACF0 CTXN ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-96) EU1.
  unfold HT_COST in Hcr. pose proof (wg_mcost_nonneg 96) as MC1. pose proof (wg_mcost_nonneg 24) as MC2. pose proof (wg_mcost_nonneg NB_BYTES) as MC3.
  pose proof (wg_mcost_nonneg 264) as MC4. pose proof (wg_mcost_nonneg 16) as MC5.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Σ m fcf kcf ART0 INFC) as (FCF0 & FCFLO & FCFIMG & FCFP).
  pose proof (af_frames_align RT AF Σ m fcf kcf ART0 INFC) as (_ & FCFSEG). unfold SEGTOP_A in FCFSEG.
  assert (CLO : conf + 48 <= lo) by lia.
  (* [comment removed for export] *)
  pose proof (ht_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 conf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(unfold RT_STACK in *; lia) ltac:(lia) ltac:(lia) UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG1) as UWF1.
  assert (HC1 : rw_cells asegs m1 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m m1 _ _ HC0); [| exact WM1]. apply (agree_of_munch _ m m1 _ MU1). intros x Hx. unfold ht_conf in Hx. cbn [cells_size csize Nat.add outside app] in *. unfold RT_STACK in *. lia. }
  destruct (cl_chain_call (rt_cg RT Σ) e_ht_new e_CRYPTO_zalloc SITE_ht_zalloc1 m1 m1 ra s0 sp (Z_to_bv 64 (usp + -96)) outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWF1 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_CZ Σ PMc (Z_to_bv 64 SITE_ht_zalloc1) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp s1 (Z_to_bv 64 96) (Z_to_bv 64 0x4c8c0) (Z_to_bv 64 186)
           a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 conf) s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 96 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 6. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ht_zalloc1) by (unfold SITE_ht_zalloc1; lia). exact CTXc1. }
  { exact UWCc1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { lia. }
  { lia. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & nw & Hc2 & LV1 & FRS1 & SP1 & CR1 & NW0 & NW16 & NWU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ENV2 & WRn2 & ACCn2 & ZERn2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ht_zalloc1) in Hc2' by (unfold SITE_ht_zalloc1; lia).
  assert (INN1 : In (nw, 96) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INFC1 : In (fcf, kcf) (rt_frames RT Σ1)) by (rewrite FRS1; exact INFC).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 nw 96 ART2 INN1 ltac:(lia)) as NWH.
  pose proof (af_live_range RT AF Σ1 m2 nw 96 ART2 INN1) as (_ & NWLO & _). rewrite SP1 in NWLO.
  pose proof (af_frames_range RT AF Σ1 m2 fcf kcf ART2 INFC1) as (_ & _ & _ & FCFP1). specialize (FCFP1 nw 96 INN1). wp_box1 FCFP1.
  pose proof (wg_mod16_8 _ NW16) as NWA.
  assert (AG12 : forall a k, (usp + -96 <= a /\ a + k <= USTACK_TOP) \/ (fcf <= a /\ a + k <= fcf + fs_size kcf - 8) -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H x Hx. cbv beta in Hx. apply PRES2.
    - destruct H as [H|H]; [left; lia | apply (acl_frame _ _ _ fcf kcf); [exact INFC | lia]].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H Hx NUM HSTK FCFSEG. unfold USTACK_TOP, RT_STACK in *. lia. }
  clear FCFP.
  assert (FR2 : rw_cells asegs m2 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply AG12. left. cbn [cells_size csize Nat.add]. clear - NUM. unfold USTACK_TOP in *. lia. }
  assert (HC2 : rw_cells asegs m2 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m1 m2 _ _ HC1); [| exact WM2]. apply AG12. right. unfold ht_conf. cbn [cells_size csize Nat.add]. clear - FC1 FC2. lia. }
  (* [comment removed for export] *)
  assert (SHCF : forall x, shad conf <= x <= shad (conf + 48 - 1) -> shad fcf <= x < shad (fcf + fs_size kcf)).
  { intros x Hx. unfold shad, SHB in *. clear - Hx FC1 FC2 FCF0. Z.div_mod_to_equations. lia. }
  assert (ACF2 : acc asegs m2 conf 48).
  { apply (acc_agree m m2 _ _ ACF0 ltac:(lia)). intros x Hx. cbv beta in Hx. pose proof (SHCF (bv_unsigned x) Hx) as Sx.
    rewrite (PRES2 x ltac:(apply (acl_fshadow _ _ _ fcf kcf); [exact INFC | exact Sx]) ltac:(cbn [outside]; unfold G_ALLOW_CUST, shad, SHB in *; lia)).
    apply MU1. cbn [outside]. split; [| exact I]. unfold shad, SHB in *. clear - Sx FCFLO NUM LOW HSTK. unfold USTACK_TOP, RT_STACK, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  assert (AG12u : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG12. left. clear; lia. }
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AG12u) as UWF2.
  (* [comment removed for export] *)
  pose proof (ht_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s5 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 nw conf ctx
                NW0 ltac:(unfold USTACK_TOP in *; lia) NWA ltac:(clear - FC1 FCF0; lia) ltac:(unfold USTACK_TOP, STACK_WIN in *; lia) CAL HC2 ACF2 MI2) as W1.
  fold usp in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & E3 & Hc3'). clear Hc3. unfold ht_w1_post in E3. subst ms3. fold usp in Hc3'.
  destruct (cl_chain_call (rt_cg RT Σ1) e_ht_new e_lock_new SITE_ht_locknew m2 m2 ra s0 sp (Z_to_bv 64 (usp + -96)) outer ltac:(rewrite CG1; exact CTX)
              ltac:(rewrite CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG1; apply (proj2 CGH); wp_in_lit) UWF2 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m2 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc2 & UWCc2).
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  (* [comment removed for export] *)
  apply (C_LN Σ1 PMc (Z_to_bv 64 SITE_ht_locknew) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 nw)
           (Z_to_bv 64 0) (Z_to_bv 64 0) b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf) s5 (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) s8 s9 s10 s11 u3 u4 u5 u6
           F2 fc2 m2 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART2 MI2).
  { fold usp in SPA. cl_call_ok EU1 ST2 LOW1 SPA 6. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ht_locknew) by (unfold SITE_ht_locknew; lia). exact CTXc2. }
  { exact UWCc2. }
  { rewrite CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS1. exact Hfr. }
  { rewrite LV1. cbn [length]. lia. }
  { rewrite CR1. lia. }
  { exact ENV2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & lk & Hc4 & LV2 & FRS2 & SP2 & CR2 & LK0 & LK16 & LKU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ENV4 & HLK4 & ACCl4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ht_locknew) in Hc4' by (unfold SITE_ht_locknew; lia).
  assert (INN2 : In (nw, 96) (rt_live RT Σ2)) by (rewrite LV2; right; exact INN1).
  assert (INL2 : In (lk, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INFC2 : In (fcf, kcf) (rt_frames RT Σ2)) by (rewrite FRS2; exact INFC1).
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW1).
  pose proof (af_live_disj RT AF Σ2 m4 lk 40 nw 96 [] (rt_live RT Σ1) ART4 LV2 INN1) as LKN. wp_box1 LKN.
  assert (AG24 : forall a k, (usp + -96 <= a /\ a + k <= USTACK_TOP) \/ (fcf <= a /\ a + k <= fcf + fs_size kcf - 8) \/ (nw <= a /\ a + k <= nw + 96)
                             -> agree_on (fun x => a <= x < a + k) m2 m4).
  { intros a k H x Hx. cbv beta in Hx. apply PRES4.
    - destruct H as [H|[H|H]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ fcf kcf); [exact INFC1 | clear - H Hx; lia] | apply (acl_live _ _ _ nw 96); [exact INN1 | clear - H Hx; lia]].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H Hx NUM HSTK FCFSEG NWH. unfold USTACK_TOP, RT_STACK in *. lia. }
  assert (FR4 : rw_cells asegs m4 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m2 m4 _ _ FR2); [| exact WM4]. apply AG24. left. cbn [cells_size csize Nat.add]. clear - NUM. unfold USTACK_TOP in *. lia. }
  assert (HC4 : rw_cells asegs m4 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m2 m4 _ _ HC2); [| exact WM4]. apply AG24. right; left. unfold ht_conf. cbn [cells_size csize Nat.add]. clear - FC1 FC2. lia. }
  (* [comment removed for export] *)
  assert (HT4 : rw_cells asegs m4 nw ht_tab0).
  { assert (HZ : rw_cells asegs m2 nw [CB (Z.to_nat 96) (repeat (Z_to_bv 8 0) (Z.to_nat 96))]) by exact (wp_zero_rw_CB asegs m2 nw 96 ZERn2 WRn2 ltac:(lia)).
    apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [48; 8; 8; 8; 8; 16]%nat) in HZ; [| reflexivity]. cbn [mk_CB_cells app firstn skipn repeat] in HZ.
    apply (rw_cells_agree asegs m2 m4 _ _ (rw_cells_recast m2 nw _ ht_tab0 HZ ltac:(cbn; repeat first [exact I | reflexivity | split]) ltac:(reflexivity))); [| exact WM4].
    apply AG24. right; right. unfold ht_tab0. cbn [cells_size csize Nat.add]. clear; lia. }
  pose proof (af_acc_live RT AF Σ2 m4 nw 96 ART4 INN2) as (WRn4 & ACCn4).
  assert (AG24u : agree_on (fun x => usp <= x < USTACK_TOP) m2 m4).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG24. left. clear; lia. }
  pose proof (uw_chain_agree outer m2 m4 sp s0 UWF2 AG24u) as UWF4.
  (* [comment removed for export] *)
  pose proof (ht_w2 sp gp (Z_to_bv 64 TP_A) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s5 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 nw conf lk
                NWH ltac:(unfold USTACK_TOP in *; lia) NWA LK0 ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(unfold USTACK_TOP, STACK_WIN in *; lia) HT4 ACCn4 MI4) as W2.
  fold usp in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & HT5) & Hc5'). clear Hc5.
  fold usp in Hc5'.
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 (usp + -96) ART4 ltac:(rewrite SP2, SP1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ nw 96); [exact INN2 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m4 m5 _ canary ENV4 MU5 ltac:(cl_fp_lia)) as ENV5.
  assert (AG45 : forall a k, (a + k <= nw \/ nw + 96 <= a) -> agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H. apply (agree_of_munch _ m4 m5 _ MU5). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST5 : stk asegs m5 lo (usp + -96)).
  { apply (stk_munch _ m4 m5 _ _ ST4 MU5 WM5). intros x Hx. cbn [outside]. clear - Hx NWLO LOW. lia. }
  assert (FR5 : rw_cells asegs m5 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5 _ _ FR4); [| exact WM5]. apply AG45. cbn [cells_size csize Nat.add]. clear - NWLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (HC5 : rw_cells asegs m5 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m4 m5 _ _ HC4); [| exact WM5]. apply AG45. unfold ht_conf. cbn [cells_size csize Nat.add]. clear - FCFP1 FC1 FC2. unfold wp_box in *. lia. }
  assert (ACF5 : acc asegs m5 conf 48).
  { apply (acc_agree m2 m5 _ _ ACF2 ltac:(lia)). intros x Hx. cbv beta in Hx. pose proof (SHCF (bv_unsigned x) Hx) as Sx.
    rewrite (MU5 x ltac:(cbn [outside]; split; [unfold shad, SHB in *; clear - Sx NWH FCFLO NUM; unfold STACK_WIN in *; Z.div_mod_to_equations; lia | exact I])).
    apply PRES4; [apply (acl_fshadow _ _ _ fcf kcf); [exact INFC1 | exact Sx] | cbn [outside]; unfold G_ALLOW_CUST, shad, SHB in *; lia]. }
  assert (AG45u : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG45. clear - NWLO LOW HSTK. unfold RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AG45u) as UWF5.
  (* [comment removed for export] *)
  assert (BSC : bytes_at asegs m5 conf (cells_bytes (ht_conf ctx))) by exact (rw_cells_bytes_at asegs m5 conf _ HC5).
  assert (LEN48 : Z.of_nat (length (cells_bytes (ht_conf ctx))) = 48) by reflexivity.
  assert (CHS : checked_src RT Σ2 m5 (Z_to_bv 64 (usp + -96)) lo conf (Z.of_nat (length (cells_bytes (ht_conf ctx))))).
  { rewrite LEN48. split.
    - intros _. split; [exact ACF5|]. right; left. exists fcf, kcf. split; [exact INFC2 | clear - FC1 FC2; lia].
    - left. clear - CLO; lia. }
  assert (CHD : checked_dst RT Σ2 m5 (Z_to_bv 64 (usp + -96)) nw (Z.of_nat (length (cells_bytes (ht_conf ctx))))).
  { rewrite LEN48. split; [| split].
    - intros _. split; [exact (acc_sub asegs m5 nw 96 nw 48 (proj2 (af_acc_live RT AF Σ2 m5 nw 96 ART5 INN2)) ltac:(lia) ltac:(lia))|].
      left. exists nw, 96. split; [exact INN2 | clear; lia].
    - intros i Hi. apply (acl_live _ _ _ nw 96); [exact INN2 | clear - Hi; lia].
    - exact (wr_at_sub m5 nw 96 nw 48 (proj1 (af_acc_live RT AF Σ2 m5 nw 96 ART5 INN2)) ltac:(lia) ltac:(lia) ltac:(lia)). }
  apply (MCP Σ2 PMc (Z_to_bv 64 SITE_ht_memcpy) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) v0 v1 v2 sp (Z_to_bv 64 nw)
           (Z_to_bv 64 nw) (Z_to_bv 64 conf) (Z_to_bv 64 48) d3 d4 d5 d6 d7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf) s5 (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) s8 s9 s10 s11 v3 v4 v5 v6
           F4 fc4 m5 nw conf (cells_bytes (ht_conf ctx)) lo FDO MST eq_refl eq_refl ltac:(rewrite LEN48; reflexivity)
           ltac:(clear - NWH NWLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) ltac:(clear - FCFSEG FC1 FC2 FCFLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) ltac:(rewrite LEN48; clear; lia) BSC CHS CHD
           ltac:(rewrite LEN48; clear - FCFP1 FC1 FC2; unfold wp_box in *; lia) ART5 MI5).
  { fold usp in SPA. cl_call_ok EU1 ST5 LOW2 SPA 6. }
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & CPY6) & Hc6'). clear Hc6.
  destruct RS6 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_ht_memcpy) in Hc6' by (unfold SITE_ht_memcpy; lia). rewrite LEN48 in PRES6.
  assert (AG56 : forall a k, ((usp + -96 <= a /\ a + k <= USTACK_TOP) \/ (fcf <= a /\ a + k <= fcf + fs_size kcf - 8) \/ (nw + 48 <= a /\ a + k <= nw + 96)
                              \/ (shad fcf <= a /\ a + k <= shad (fcf + fs_size kcf))) -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H x Hx. cbv beta in Hx. apply PRES6.
    - destruct H as [H|[H|[H|H]]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ fcf kcf); [exact INFC2 | clear - H Hx; lia] | apply (acl_live _ _ _ nw 96); [exact INN2 | clear - H Hx; lia] | apply (acl_fshadow _ _ _ fcf kcf); [exact INFC2 | clear - H Hx; lia]].
    - destruct H as [H|[H|[H|H]]]; [clear - H Hx NWLO LOW HSTK; unfold RT_STACK in *; lia | clear - H Hx FCFP1 FC1 FC2; unfold wp_box in *; lia | clear - H Hx; lia | unfold shad, SHB in *; clear - H Hx NWH FCFLO SP0R NUM; unfold USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia]. }
  assert (FR6 : rw_cells asegs m6 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m5 m6 _ _ FR5); [| exact WM6]. apply AG56. left. cbn [cells_size csize Nat.add]. clear - NUM. unfold USTACK_TOP in *. lia. }
  assert (HC6 : rw_cells asegs m6 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m5 m6 _ _ HC5); [| exact WM6]. apply AG56. right; left. unfold ht_conf. cbn [cells_size csize Nat.add]. clear - FC1 FC2. lia. }
  assert (ACF6 : acc asegs m6 conf 48).
  { apply (acc_agree m5 m6 _ _ ACF5 ltac:(lia)). intros x Hx. cbv beta in Hx. pose proof (SHCF (bv_unsigned x) Hx) as Sx.
    apply PRES6; [apply (acl_fshadow _ _ _ fcf kcf); [exact INFC2 | exact Sx] |].
    unfold shad, SHB in *. clear - Sx NWH FCFLO SP0R NUM. unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (HT6 : rw_cells asegs m6 nw (ht_tab1 ctx lk)).
  { destruct (proj1 (rw_cells_app m5 nw [CB 48 (repeat (Z_to_bv 8 0) 48)] _) HT5) as [_ TL5]. cbn [cells_size csize Nat.add] in TL5.
    assert (TL6 : rw_cells asegs m6 (nw + 48) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16)]).
    { apply (rw_cells_agree asegs m5 m6 _ _ TL5); [| exact WM6]. apply AG56. right; right; left. cbn [cells_size csize Nat.add]. clear; lia. }
    pose proof (rw_CB_of_bytes m6 nw _ CPY6 ltac:(rewrite LEN48; exact (wr_at_sub m6 nw 96 nw 48 (proj1 (af_acc_live RT AF Σ2 m6 nw 96 ART6 INN2)) ltac:(lia) ltac:(lia) ltac:(lia)))) as HD6.
    pose proof (rw_cells_recast m6 nw _ (ht_conf ctx) HD6 ltac:(cbn; repeat first [exact I | reflexivity | split]) ltac:(reflexivity)) as HD6'.
    unfold ht_tab1. change (rw_cells asegs m6 nw (ht_conf ctx ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16)])).
    apply (proj2 (rw_cells_app m6 nw (ht_conf ctx) _)). split; [exact HD6'|]. cbn [cells_size csize Nat.add ht_conf]. exact TL6. }
  assert (ENV6 : cl_env m6 (Z_to_bv 8 1) canary).
  { apply (cl_env_pres_ex _ _ _ _ _ m5 m6 _ canary ENV5 PRES6). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)) as XR. clear - XR NWH. unfold SEGTOP_A in *. lia. }
  assert (AG56u : agree_on (fun x => usp <= x < USTACK_TOP) m5 m6).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG56. left. clear; lia. }
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWF5 AG56u) as UWF6.
  pose proof (proj2 (af_acc_live RT AF Σ2 m6 nw 96 ART6 INN2)) as ACCn6.
  (* [comment removed for export] *)
  pose proof (ht_w3 sp gp (Z_to_bv 64 TP_A) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 s5 s8 s9 s10 s11 w3 w4 w5 w6 F6 fc6 m6 nw conf lk ctx
                NWH ltac:(unfold USTACK_TOP in *; lia) NWA ltac:(lia) ltac:(unfold USTACK_TOP, STACK_WIN in *; lia) HT6 ACCn6 MI6) as W3.
  fold usp in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & HT7) & Hc7'). clear Hc7.
  fold usp in Hc7'.
  assert (ART7 : ART RT Σ2 m7).
  { apply (af_frame RT AF Σ2 m6 m7 (usp + -96) ART6 ltac:(rewrite SP2, SP1; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ nw 96); [exact INN2 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m6 m7 _ canary ENV6 MU7 ltac:(cl_fp_lia)) as ENV7.
  assert (AG67 : forall a k, (a + k <= nw \/ nw + 96 <= a) -> agree_on (fun x => a <= x < a + k) m6 m7).
  { intros a k H. apply (agree_of_munch _ m6 m7 _ MU7). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST7 : stk asegs m7 lo (usp + -96)).
  { apply (stk_munch _ m6 m7 _ _ ST6 MU7 WM7). intros x Hx. cbn [outside]. clear - Hx NWLO LOW. lia. }
  assert (FR7 : rw_cells asegs m7 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m6 m7 _ _ FR6); [| exact WM7]. apply AG67. cbn [cells_size csize Nat.add]. clear - NWLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (HC7 : rw_cells asegs m7 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m6 m7 _ _ HC6); [| exact WM7]. apply AG67. unfold ht_conf. cbn [cells_size csize Nat.add]. clear - FCFP1 FC1 FC2. unfold wp_box in *. lia. }
  assert (ACF7 : acc asegs m7 conf 48).
  { apply (acc_agree m6 m7 _ _ ACF6 ltac:(lia)). intros x Hx. cbv beta in Hx. pose proof (SHCF (bv_unsigned x) Hx) as Sx.
    apply MU7. cbn [outside]. split; [| exact I]. unfold shad, SHB in *. clear - Sx NWH FCFLO NUM; unfold STACK_WIN in *; Z.div_mod_to_equations; lia. }
  assert (AG67u : agree_on (fun x => usp <= x < USTACK_TOP) m6 m7).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG67. clear - NWLO LOW HSTK. unfold RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m6 m7 sp s0 UWF6 AG67u) as UWF7.
  destruct (cl_chain_call (rt_cg RT Σ2) e_ht_new e_CRYPTO_zalloc SITE_ht_zalloc2 m7 m7 ra s0 sp (Z_to_bv 64 (usp + -96)) outer ltac:(rewrite CG2, CG1; exact CTX)
              ltac:(rewrite CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF7 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m7 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR7))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc7 & UWCc7).
  (* [comment removed for export] *)
  apply (C_CZ Σ2 PMc (Z_to_bv 64 SITE_ht_zalloc2) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 nw) (Z_to_bv 64 24) (Z_to_bv 64 0x4c8c0) (Z_to_bv 64 218)
           e3 e4 e5 e6 e7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf) (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) s9 s10 s11 w3 w4 w5 w6
           F6 fc6 m7 24 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl ltac:(lia) ART7 MI7).
  { fold usp in SPA. cl_call_ok EU1 ST7 LOW2 SPA 6. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ht_zalloc2) by (unfold SITE_ht_zalloc2; lia). exact CTXc7. }
  { exact UWCc7. }
  { rewrite CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV2, LV1. cbn [length]. lia. }
  { rewrite CR2, CR1. lia. }
  { exact ENV7. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ3 & md & Hc8 & LV3 & FRS3 & SP3 & CR3 & MD0 & MD16 & MDU & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ENV8 & WRm8 & ACCm8 & ZERm8) & Hc8'). clear Hc8.
  destruct RS8 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F8 & fc8 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_ht_zalloc2) in Hc8' by (unfold SITE_ht_zalloc2; lia).
  assert (INM3 : In (md, 24) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
  assert (INN3 : In (nw, 96) (rt_live RT Σ3)) by (rewrite LV3; right; exact INN2).
  assert (INFC3 : In (fcf, kcf) (rt_frames RT Σ3)) by (rewrite FRS3; exact INFC2).
  assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3; exact LOW2).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m8 md 24 ART8 INM3 ltac:(lia)) as MDH.
  pose proof (af_live_range RT AF Σ3 m8 md 24 ART8 INM3) as (_ & MDLO & _). rewrite SP3, SP2, SP1 in MDLO.
  pose proof (af_live_disj RT AF Σ3 m8 md 24 nw 96 [] (rt_live RT Σ2) ART8 LV3 INN2) as MDN. wp_box1 MDN.
  pose proof (af_frames_range RT AF Σ3 m8 fcf kcf ART8 INFC3) as (_ & _ & _ & FCFP3). specialize (FCFP3 md 24 INM3). wp_box1 FCFP3.
  pose proof (wg_mod16_8 _ MD16) as MDA.
  assert (AG78 : forall a k, ((usp + -96 <= a /\ a + k <= USTACK_TOP) \/ (fcf <= a /\ a + k <= fcf + fs_size kcf - 8) \/ (nw <= a /\ a + k <= nw + 96)
                              \/ (shad fcf <= a /\ a + k <= shad (fcf + fs_size kcf))) -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H x Hx. cbv beta in Hx. apply PRES8.
    - destruct H as [H|[H|[H|H]]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ fcf kcf); [exact INFC2 | clear - H Hx; lia] | apply (acl_live _ _ _ nw 96); [exact INN2 | clear - H Hx; lia] | apply (acl_fshadow _ _ _ fcf kcf); [exact INFC2 | clear - H Hx; lia]].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I].
      destruct H as [H|[H|[H|H]]]; [clear - H Hx NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia | clear - H Hx FCFSEG; lia | clear - H Hx NWH; lia | unfold shad, SHB in *; clear - H Hx FCFSEG; Z.div_mod_to_equations; lia]. }
  assert (FR8 : rw_cells asegs m8 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m7 m8 _ _ FR7); [| exact WM8]. apply AG78. left. cbn [cells_size csize Nat.add]. clear - NUM. unfold USTACK_TOP in *. lia. }
  assert (HC8 : rw_cells asegs m8 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m7 m8 _ _ HC7); [| exact WM8]. apply AG78. right; left. unfold ht_conf. cbn [cells_size csize Nat.add]. clear - FC1 FC2. lia. }
  assert (HT8 : rw_cells asegs m8 nw (ht_tab2 ctx lk)).
  { apply (rw_cells_agree asegs m7 m8 _ _ HT7); [| exact WM8]. apply AG78. right; right; left. unfold ht_tab2. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (ACF8 : acc asegs m8 conf 48).
  { apply (acc_agree m7 m8 _ _ ACF7 ltac:(lia)). intros x Hx. cbv beta in Hx. pose proof (SHCF (bv_unsigned x) Hx) as Sx.
    apply PRES8; [apply (acl_fshadow _ _ _ fcf kcf); [exact INFC2 | exact Sx] | cbn [outside]; unfold G_ALLOW_CUST, shad, SHB in *; lia]. }
  assert (HMD8 : rw_cells asegs m8 md [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { pose proof (wp_zero_rw_CB asegs m8 md 24 ZERm8 WRm8 ltac:(lia)) as HZ. change (Z.to_nat 24) with 24%nat in HZ.
    apply (rw_cells_recast m8 md _ _ HZ); [cbn; repeat first [exact I | reflexivity | split] | reflexivity]. }
  pose proof (proj2 (af_acc_live RT AF Σ3 m8 nw 96 ART8 INN3)) as ACCn8.
  assert (AG78u : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG78. left. clear; lia. }
  pose proof (uw_chain_agree outer m7 m8 sp s0 UWF7 AG78u) as UWF8.
  (* [comment removed for export] *)
  pose proof (ht_w4 sp gp (Z_to_bv 64 TP_A) x0 x1 x2 g1 g2 g3 g4 g5 g6 g7 s9 s10 s11 x3 x4 x5 x6 F8 fc8 m8 nw conf lk md ctx
                NWH ltac:(clear - NWU; unfold USTACK_TOP in *; lia) NWA ltac:(clear - FCFSEG FC1; lia) ltac:(clear - FC1 FC2 FCFLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) MD0 ltac:(clear - MDU; unfold USTACK_TOP in *; lia) MDA HT8 ACCn8 MI8) as W4.
  fold usp in W4.
  cl_lift W4 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ3 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & HT9) & Hc9'). clear Hc9.
  fold usp in Hc9'.
  assert (ART9 : ART RT Σ3 m9).
  { apply (af_frame RT AF Σ3 m8 m9 (usp + -96) ART8 ltac:(rewrite SP3, SP2, SP1; lia)); [| exact WM9].
    intros a Ha. apply MU9. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ nw 96); [exact INN3 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m8 m9 _ canary ENV8 MU9 ltac:(cl_fp_lia)) as ENV9.
  assert (AG89 : forall a k, (a + k <= nw + 64 \/ nw + 72 <= a) -> agree_on (fun x => a <= x < a + k) m8 m9).
  { intros a k H. apply (agree_of_munch _ m8 m9 _ MU9). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST9 : stk asegs m9 lo (usp + -96)).
  { apply (stk_munch _ m8 m9 _ _ ST8 MU9 WM9). intros x Hx. cbn [outside]. clear - Hx NWLO LOW. lia. }
  assert (FR9 : rw_cells asegs m9 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m8 m9 _ _ FR8); [| exact WM9]. apply AG89. cbn [cells_size csize Nat.add]. clear - NWLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (HC9 : rw_cells asegs m9 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m8 m9 _ _ HC8); [| exact WM9]. apply AG89. unfold ht_conf. cbn [cells_size csize Nat.add]. clear - FCFP1 FC1 FC2. unfold wp_box in *. lia. }
  assert (HMD9 : rw_cells asegs m9 md [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m8 m9 _ _ HMD8); [| exact WM9]. apply AG89. cbn [cells_size csize Nat.add]. clear - MDN. unfold wp_box in *. lia. }
  assert (ACF9 : acc asegs m9 conf 48).
  { apply (acc_agree m8 m9 _ _ ACF8 ltac:(lia)). intros x Hx. cbv beta in Hx. pose proof (SHCF (bv_unsigned x) Hx) as Sx.
    apply MU9. cbn [outside]. split; [| exact I]. unfold shad, SHB in *. clear - Sx NWH FCFLO SP0R NUM; unfold USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia. }
  assert (AG89u : agree_on (fun x => usp <= x < USTACK_TOP) m8 m9).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG89. clear - NWLO LOW HSTK. unfold RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m8 m9 sp s0 UWF8 AG89u) as UWF9.
  destruct (cl_chain_call (rt_cg RT Σ3) e_ht_new e_anl SITE_ht_anl m9 m9 ra s0 sp (Z_to_bv 64 (usp + -96)) outer ltac:(rewrite CG3, CG2, CG1; exact CTX)
              ltac:(rewrite CG3, CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG3, CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF9 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m9 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR9))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc9 & UWCc9).
  (* [comment removed for export] *)
  apply (C_ANL Σ3 PMc (Z_to_bv 64 SITE_ht_anl) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) x0 x1 x2 sp (Z_to_bv 64 nw)
           (Z_to_bv 64 512) (Z_to_bv 64 (md + 8)) (Z_to_bv 64 512) g3 g4 g5 g6 g7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf)
           (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 64) 3 + 2147450880))  s10 s11 x3 x4 x5 x6 F8 fc8 m9 lo (bv_unsigned ra :: outer) (md + 8) md 24 (Z_to_bv 8 1) canary
           FDO MST eq_refl eq_refl eq_refl memalign_plain_nb INM3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - MDA; Z.div_mod_to_equations; lia) ART9 MI9).
  { fold usp in SPA. cl_call_ok EU1 ST9 LOW3 SPA 6. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ht_anl) by (unfold SITE_ht_anl; lia). exact CTXc9. }
  { exact UWCc9. }
  { rewrite CG3, CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS3, FRS2, FRS1. exact Hfr. }
  { rewrite LV3, LV2, LV1. cbn [length]. lia. }
  { rewrite CR3, CR2, CR1. lia. }
  { exact ENV9. }
  { exact Hc9'. }
  clear Hc9'. intros c10 (Σ4 & q & Hc10 & LV4 & FRS4 & SP4 & CR4 & Q0 & Q64 & QU & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c10 Hc10) as (ms10 & (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & ENV10 & WRq10 & ACCq10 & FPC10 & ZERq10) & Hc10'). clear Hc10.
  destruct RS10 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F10 & fc10 & ->).
  rewrite EU1 in ST10, PRES10. rewrite (ret_pc_even SITE_ht_anl) in Hc10' by (unfold SITE_ht_anl; lia).
  assert (INQ4 : In (q, NB_BYTES) (rt_live RT Σ4)) by (rewrite LV4; left; reflexivity).
  assert (INM4 : In (md, 24) (rt_live RT Σ4)) by (rewrite LV4; right; exact INM3).
  assert (INN4 : In (nw, 96) (rt_live RT Σ4)) by (rewrite LV4; right; exact INN3).
  assert (INFC4 : In (fcf, kcf) (rt_frames RT Σ4)) by (rewrite FRS4; exact INFC3).
  assert (LOW4 : rt_sp0 RT Σ4 - STACK_WIN <= lo) by (rewrite SP4; exact LOW3).
  pose proof (afp_live_hi RT GOBJ AFP Σ4 m10 q NB_BYTES ART10 INQ4 ltac:(unfold NB_BYTES; lia)) as QHH.
  pose proof (af_live_range RT AF Σ4 m10 q NB_BYTES ART10 INQ4) as (_ & QLO & _). rewrite SP4, SP3, SP2, SP1 in QLO.
  pose proof (af_live_disj RT AF Σ4 m10 q NB_BYTES nw 96 [] (rt_live RT Σ3) ART10 LV4 INN3) as QN. wp_box1 QN.
  pose proof (af_live_disj RT AF Σ4 m10 q NB_BYTES md 24 [] (rt_live RT Σ3) ART10 LV4 INM3) as QM. wp_box1 QM.
  pose proof (af_frames_range RT AF Σ4 m10 fcf kcf ART10 INFC4) as (_ & _ & _ & FCFP4). specialize (FCFP4 q NB_BYTES INQ4). wp_box1 FCFP4.
  assert (AG910 : forall a k, ((usp + -96 <= a /\ a + k <= USTACK_TOP) \/ (fcf <= a /\ a + k <= fcf + fs_size kcf - 8) \/ (nw <= a /\ a + k <= nw + 96)
                               \/ (md <= a /\ a + k <= md + 24 /\ (a + k <= md + 8 \/ md + 16 <= a)) \/ (shad fcf <= a /\ a + k <= shad (fcf + fs_size kcf)))
                              -> agree_on (fun x => a <= x < a + k) m9 m10).
  { intros a k H x Hx. cbv beta in Hx. apply PRES10.
    - destruct H as [H|[H|[H|[H|H]]]]; [left; clear - H Hx; lia | apply (acl_frame _ _ _ fcf kcf); [exact INFC3 | clear - H Hx; lia] | apply (acl_live _ _ _ nw 96); [exact INN3 | clear - H Hx; lia]
        | apply (acl_live _ _ _ md 24); [exact INM3 | clear - H Hx; lia] | apply (acl_fshadow _ _ _ fcf kcf); [exact INFC3 | clear - H Hx; lia]].
    - cbn [outside]. split; [| exact I].
      destruct H as [H|[H|[H|[H|H]]]]; [clear - H Hx MDLO LOW HSTK; unfold RT_STACK in *; lia | clear - H Hx FCFP3 FC1 FC2; unfold wp_box in *; lia | clear - H Hx MDN; unfold wp_box in *; lia | clear - H Hx; lia | unfold shad, SHB in *; clear - H Hx MDH FCFLO SP0R NUM; unfold USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia]. }
  assert (FR10 : rw_cells asegs m10 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m9 m10 _ _ FR9); [| exact WM10]. apply AG910. left. cbn [cells_size csize Nat.add]. clear - NUM. unfold USTACK_TOP in *. lia. }
  assert (HC10 : rw_cells asegs m10 conf (ht_conf ctx)).
  { apply (rw_cells_agree asegs m9 m10 _ _ HC9); [| exact WM10]. apply AG910. right; left. unfold ht_conf. cbn [cells_size csize Nat.add]. clear - FC1 FC2. lia. }
  assert (HT10 : rw_cells asegs m10 nw (ht_tab3 ctx lk md)).
  { apply (rw_cells_agree asegs m9 m10 _ _ HT9); [| exact WM10]. apply AG910. right; right; left. unfold ht_tab3. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (ACF10 : acc asegs m10 conf 48).
  { apply (acc_agree m9 m10 _ _ ACF9 ltac:(lia)). intros x Hx. cbv beta in Hx. pose proof (SHCF (bv_unsigned x) Hx) as Sx.
    apply PRES10; [apply (acl_fshadow _ _ _ fcf kcf); [exact INFC3 | exact Sx] | cbn [outside]; split; [| exact I]; unfold shad, SHB in *; clear - Sx MDH FCFLO SP0R NUM; unfold USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia]. }
  assert (HMD10 : rw_cells asegs m10 md [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 0)]).
  { destruct (proj1 (rw_cells_app m9 md [C8 (Z_to_bv 64 0)] _) HMD9) as [M0 M12]. cbn [cells_size csize Nat.add] in M12.
    destruct (proj1 (rw_cells_app m9 (md + 8) [C8 (Z_to_bv 64 0)] _) M12) as [_ M2]. cbn [cells_size csize Nat.add] in M2.
    apply (proj2 (rw_cells_app m10 md [C8 (Z_to_bv 64 0)] _)). cbn [cells_size csize Nat.add]. split.
    - apply (rw_cells_agree asegs m9 m10 _ _ M0); [| exact WM10]. apply AG910. right; right; right; left. cbn [cells_size csize Nat.add]. clear; lia.
    - apply (proj2 (rw_cells_app m10 (md + 8) [C8 (Z_to_bv 64 q)] _)). cbn [cells_size csize Nat.add]. split; [exact FPC10|].
      replace (md + 8 + 8) with (md + 16) by lia. replace (md + 8 + 8) with (md + 16) in M2 by lia.
      apply (rw_cells_agree asegs m9 m10 _ _ M2); [| exact WM10]. apply AG910. right; right; right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  pose proof (proj2 (af_acc_live RT AF Σ4 m10 nw 96 ART10 INN4)) as ACCn10.
  pose proof (proj2 (af_acc_live RT AF Σ4 m10 md 24 ART10 INM4)) as ACCm10.
  assert (AG910u : agree_on (fun x => usp <= x < USTACK_TOP) m9 m10).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG910. left. clear; lia. }
  pose proof (uw_chain_agree outer m9 m10 sp s0 UWF9 AG910u) as UWF10.
  (* [comment removed for export] *)
  pose proof (ht_w5 sp gp (Z_to_bv 64 TP_A) y0 y1 y2 h1 h2 h3 h4 h5 h6 h7 s10 s11 y3 y4 y5 y6 F10 fc10 m10 nw conf lk md q ctx
                NWH ltac:(clear - NWU; unfold USTACK_TOP in *; lia) NWA ltac:(clear - FCFSEG FC1; lia) ltac:(clear - FC1 FC2 FCFLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia) CAL MDH ltac:(clear - MDU; unfold USTACK_TOP in *; lia) MDA
                Q0 ltac:(clear - QU; unfold NB_BYTES, USTACK_TOP in *; lia) ltac:(clear - MDN; unfold wp_box in *; lia) ltac:(clear - FCFP1 FC1 FC2; unfold wp_box in *; lia) ltac:(clear - FCFP3 FC1 FC2; unfold wp_box in *; lia)
                HT10 ACCn10 HMD10 ACCm10 HC10 ACF10 MI10) as W5.
  fold usp in W5.
  cl_lift W5 Hc10' c11 Hc11.
  destruct (ASTA_unpack RT Σ4 _ _ c11 Hc11) as (ms11 & (a2' & m11 & -> & MU11 & WM11 & MI11 & HMD11) & Hc11'). clear Hc11.
  fold usp in Hc11'.
  assert (ART11 : ART RT Σ4 m11).
  { apply (af_frame RT AF Σ4 m10 m11 (usp + -96) ART10 ltac:(rewrite SP4, SP3, SP2, SP1; lia)); [| exact WM11].
    intros a Ha. apply MU11. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ md 24); [exact INM4 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m10 m11 _ canary ENV10 MU11 ltac:(cl_fp_lia)) as ENV11.
  assert (AG1011 : forall a k, (a + k <= md \/ md + 24 <= a) -> agree_on (fun x => a <= x < a + k) m10 m11).
  { intros a k H. apply (agree_of_munch _ m10 m11 _ MU11). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST11 : stk asegs m11 lo (usp + -96)).
  { apply (stk_munch _ m10 m11 _ _ ST10 MU11 WM11). intros x Hx. cbn [outside]. clear - Hx MDLO LOW. lia. }
  assert (FR11 : rw_cells asegs m11 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m10 m11 _ _ FR10); [| exact WM11]. apply AG1011. cbn [cells_size csize Nat.add]. clear - MDLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (HT11 : rw_cells asegs m11 nw (ht_tab3 ctx lk md)).
  { apply (rw_cells_agree asegs m10 m11 _ _ HT10); [| exact WM11]. apply AG1011. unfold ht_tab3. cbn [cells_size csize Nat.add]. clear - MDN. unfold wp_box in *. lia. }
  assert (ZERq11 : bytes_at asegs m11 q (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))).
  { apply (bytes_at_agree asegs m10 m11 _ _ ZERq10). rewrite repeat_length, Z2Nat.id by (unfold NB_BYTES; lia). apply AG1011. clear - QM. unfold wp_box in *. lia. }
  assert (AG1011u : agree_on (fun x => usp <= x < USTACK_TOP) m10 m11).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG1011. clear - MDLO LOW HSTK. unfold RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m10 m11 sp s0 UWF10 AG1011u) as UWF11.
  destruct (cl_chain_call (rt_cg RT Σ4) e_ht_new e_rcu_lock_new SITE_ht_rcu m11 m11 ra s0 sp (Z_to_bv 64 (usp + -96)) outer ltac:(rewrite CG4, CG3, CG2, CG1; exact CTX)
              ltac:(rewrite CG4, CG3, CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG4, CG3, CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF11 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m11 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR11))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc11 & UWCc11).
  (* [comment removed for export] *)
  apply (C_RCU Σ4 PMc (Z_to_bv 64 SITE_ht_rcu) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) y0 y1 y2 sp (Z_to_bv 64 nw)
           (Z_to_bv 64 1) ctx a2' h3 h4 h5 h6 h7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf)
           (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 64) 3 + 2147450880))  s10 s11 y3 y4 y5 y6 F10 fc10 m11 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl CTXN ART11 MI11).
  { fold usp in SPA. cl_call_ok EU1 ST11 LOW4 SPA 6. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ht_rcu) by (unfold SITE_ht_rcu; lia). exact CTXc11. }
  { exact UWCc11. }
  { rewrite CG4, CG3, CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS4, FRS3, FRS2, FRS1. exact Hfr. }
  { rewrite LV4, LV3, LV2, LV1. cbn [length]. lia. }
  { rewrite CR4, CR3, CR2, CR1. lia. }
  { exact ENV11. }
  { exact Hc11'. }
  clear Hc11'. intros c12 (Σ5 & L & qp & Hc12 & LV5 & FRS5 & SP5 & CR5 & L0 & L16 & LU & QP0 & QP16 & QPU & CG5).
  destruct (ASTA_unpack RT Σ5 _ _ c12 Hc12) as (ms12 & (m12 & RS12 & (ART12 & MI12 & WM12 & ST12) & PRES12 & ENV12 & WRL12 & ACCL12 & WRp12 & ACCp12 & CL0 & CLM1 & CLM2 & CLC1 & CLM3 & CLC2 & CLQ) & Hc12'). clear Hc12.
  destruct RS12 as (z0 & z1 & z2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z3 & z4 & z5 & z6 & F12 & fc12 & ->).
  rewrite EU1 in ST12, PRES12. rewrite (ret_pc_even SITE_ht_rcu) in Hc12' by (unfold SITE_ht_rcu; lia).
  assert (INL5 : In (lk, 40) (rt_live RT Σ5)) by (rewrite LV5, LV4, LV3; do 4 right; exact INL2).
  assert (INN5 : In (nw, 96) (rt_live RT Σ5)) by (rewrite LV5; do 2 right; exact INN4).
  assert (INM5 : In (md, 24) (rt_live RT Σ5)) by (rewrite LV5; do 2 right; exact INM4).
  assert (INQ5 : In (q, NB_BYTES) (rt_live RT Σ5)) by (rewrite LV5; do 2 right; exact INQ4).
  assert (INLL5 : In (L, 264) (rt_live RT Σ5)) by (rewrite LV5; right; left; reflexivity).
  assert (INQP5 : In (qp, 16) (rt_live RT Σ5)) by (rewrite LV5; left; reflexivity).
  pose proof (af_live_disj RT AF Σ5 m12 qp 16 nw 96 [] _ ART12 LV5 ltac:(right; exact INN4)) as QPN. wp_box1 QPN.
  pose proof (af_live_disj RT AF Σ5 m12 L 264 nw 96 [(qp, 16)] _ ART12 LV5 ltac:(right; exact INN4)) as LN. wp_box1 LN.
  pose proof (af_live_disj RT AF Σ3 m8 md 24 lk 40 [] (rt_live RT Σ2) ART8 LV3 INL2) as MDL. wp_box1 MDL.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 lk 40 ART4 INL2 ltac:(lia)) as LKH.
  assert (AG1112 : forall a k, ((usp + -96 <= a /\ a + k <= USTACK_TOP) \/ (nw <= a /\ a + k <= nw + 96) \/ (md <= a /\ a + k <= md + 24) \/ (q <= a /\ a + k <= q + NB_BYTES) \/ (lk <= a /\ a + k <= lk + 40))
                               -> agree_on (fun x => a <= x < a + k) m11 m12).
  { intros a k H x Hx. cbv beta in Hx. apply PRES12.
    - destruct H as [H|[H|[H|[H|H]]]]; [left; clear - H Hx; lia | apply (acl_live _ _ _ nw 96); [exact INN4 | clear - H Hx; lia] | apply (acl_live _ _ _ md 24); [exact INM4 | clear - H Hx; lia]
        | apply (acl_live _ _ _ q NB_BYTES); [exact INQ4 | clear - H Hx; lia] | apply (acl_live _ _ _ lk 40); [rewrite LV4, LV3; do 2 right; exact INL2 | clear - H Hx; lia]].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H Hx NWH MDH QHH LKH NUM HSTK. unfold USTACK_TOP, RT_STACK, NB_BYTES in *. lia. }
  assert (FR12 : rw_cells asegs m12 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m11 m12 _ _ FR11); [| exact WM12]. apply AG1112. left. cbn [cells_size csize Nat.add]. clear - NUM. unfold USTACK_TOP in *. lia. }
  assert (HT12 : rw_cells asegs m12 nw (ht_tab3 ctx lk md)).
  { apply (rw_cells_agree asegs m11 m12 _ _ HT11); [| exact WM12]. apply AG1112. right; left. unfold ht_tab3. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HMD12 : rw_cells asegs m12 md [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 511)]).
  { apply (rw_cells_agree asegs m11 m12 _ _ HMD11); [| exact WM12]. apply AG1112. right; right; left. cbn [cells_size csize Nat.add]. clear; lia. }
  assert (ZERq12 : bytes_at asegs m12 q (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))).
  { apply (bytes_at_agree asegs m11 m12 _ _ ZERq11). rewrite repeat_length, Z2Nat.id by (unfold NB_BYTES; lia). apply AG1112. right; right; right; left. clear; lia. }
  pose proof (proj2 (af_acc_live RT AF Σ5 m12 nw 96 ART12 INN5)) as ACCn12.
  (* [comment removed for export] *)
  pose proof (ht_w6 ra sp gp (Z_to_bv 64 TP_A) z0 z1 z2 k1 k2 k3 k4 k5 k6 k7 s10 s11 z3 z4 z5 z6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F12 fc12 m12 nw conf L lk md lo ctx j
                ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) NWH ltac:(clear - NWLO LOW; lia) NWA ltac:(clear - FCFSEG FC1; lia) ltac:(clear - FC1 FC2 FCFLO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia)
                L0 ltac:(clear - LU; unfold USTACK_TOP in *; lia) ST12 FR12 HT12 ACCn12 MI12) as W6.
  fold usp in W6.
  cl_lift W6 Hc12' c13 Hc13.
  destruct (ASTA_unpack RT Σ5 _ _ c13 Hc13) as (ms13 & (a1' & m13 & -> & MU13 & WM13 & MI13 & ST13 & HT13) & Hc13'). clear Hc13.
  fold usp in ST13.
  assert (ART13 : ART RT Σ5 m13).
  { apply (af_frame RT AF Σ5 m12 m13 usp ART12 ltac:(rewrite SP5, SP4, SP3, SP2, SP1; lia)); [| exact WM13].
    intros a Ha. apply MU13. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ nw 96); [exact INN5 | clear - Hin; lia]. }
  assert (AG1213 : forall a k, (a + k <= nw \/ nw + 96 <= a) -> agree_on (fun x => a <= x < a + k) m12 m13).
  { intros a k H. apply (agree_of_munch _ m12 m13 _ MU13). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (WM013 : wmono asegs m m13).
  { exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6
          (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 (wmono_trans asegs _ _ _ WM9 (wmono_trans asegs _ _ _ WM10 (wmono_trans asegs _ _ _ WM11
          (wmono_trans asegs _ _ _ WM12 WM13))))))))))). }
  apply Hk. exists Σ5, nw, lk, md, q, L, qp.
  split; [| split; [rewrite LV5, LV4, LV3, LV2, LV1; reflexivity | split; [rewrite FRS5, FRS4, FRS3, FRS2; exact FRS1 | split; [rewrite SP5, SP4, SP3, SP2; exact SP1 |
            split; [rewrite CR5, CR4, CR3, CR2, CR1; unfold HT_COST; lia | ]]]]].
  2: { repeat (split; [assumption|]). rewrite CG5, CG4, CG3, CG2; exact CG1. }
  eapply ASTA_conseq; [exact Hc13'|]. intros ms <-. exists m13.
  split; [exists z0, z1, z2, a1', (Z_to_bv 64 0), k3, k4, k5, k6, k7, z3, z4, z5, z6, F12, fc12; reflexivity|].
  split; [split; [exact ART13 | split; [exact MI13 | split; [exact WM013 | exact ST13]]]|].
  split.
  { intros a Ha Ho.
    assert (A0' : aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -96) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | clear; lia]).
    assert (A1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ A0'); [rewrite LV1; intros e He; right; exact He | rewrite FRS1; auto | clear; lia]).
    assert (A2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -96) (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ A1); [rewrite LV2; intros e He; right; exact He | rewrite FRS2; auto | clear; lia]).
    assert (A3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -96) (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ A2); [rewrite LV3; intros e He; right; exact He | rewrite FRS3; auto | clear; lia]).
    assert (A4 : aclient (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -96) (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ A3); [rewrite LV4; intros e He; right; exact He | rewrite FRS4; auto | clear; lia]).
    pose proof (newchunk_apart RT AF Σ Σ1 m2 nw 96 (usp + -96) _ ART2 LV1 FRS1 SP1 ltac:(clear - NUM; lia) ltac:(clear; lia) A0') as Nn.
    pose proof (newchunk_apart RT AF Σ2 Σ3 m8 md 24 (usp + -96) _ ART8 LV3 FRS3 SP3 ltac:(rewrite SP2, SP1; clear - NUM; lia) ltac:(clear; lia) A2) as Nm.
    rewrite (MU13 a ltac:(cbn [outside]; clear - Nn; lia)).
    rewrite (PRES12 a A4 Ho).
    rewrite (MU11 a ltac:(cbn [outside]; clear - Nm; lia)).
    rewrite (PRES10 a A3 ltac:(cbn [outside]; clear - Nm; split; [lia | exact I])).
    rewrite (MU9 a ltac:(cbn [outside]; clear - Nn; lia)).
    rewrite (PRES8 a A2 Ho).
    rewrite (MU7 a ltac:(cbn [outside]; clear - Nn; lia)).
    rewrite (PRES6 a A2 ltac:(clear - Nn; lia)).
    rewrite (MU5 a ltac:(cbn [outside]; clear - Nn; lia)).
    rewrite (PRES4 a A1 Ho).
    rewrite (PRES2 a A0' Ho).
    exact (PR1 a Ha I). }
  split; [exact (cl_env_seg _ m12 m13 _ canary ENV12 MU13 ltac:(cl_fp_lia))|].
  pose proof (af_acc_live RT AF Σ5 m13 nw 96 ART13 INN5) as (WRn13 & ACCn13).
  split; [exact WRn13|]. split; [exact ACCn13|].
  split; [exact HT13|].
  split; [apply (rw_cells_agree asegs m12 m13 _ _ HMD12); [apply AG1213; cbn [cells_size csize Nat.add]; clear - MDN; unfold wp_box in *; lia | exact WM13]|].
  split.
  { apply (rw_cells_agree asegs m4 m13 _ _ HLK4); [| exact (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8
             (wmono_trans asegs _ _ _ WM9 (wmono_trans asegs _ _ _ WM10 (wmono_trans asegs _ _ _ WM11 (wmono_trans asegs _ _ _ WM12 WM13))))))))].
    intros x Hx. unfold mutex_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (MU13 x ltac:(cbn [outside]; clear - Hx LKN; unfold wp_box in *; lia)).
    rewrite (PRES12 x ltac:(apply (acl_live _ _ _ lk 40); [rewrite LV4, LV3; do 2 right; exact INL2 | clear - Hx; lia]) ltac:(cbn [outside]; unfold G_ALLOW_CUST; clear - Hx LKH; lia)).
    rewrite (MU11 x ltac:(cbn [outside]; clear - Hx MDL; unfold wp_box in *; lia)).
    rewrite (PRES10 x ltac:(apply (acl_live _ _ _ lk 40); [rewrite LV3; right; exact INL2 | clear - Hx; lia]) ltac:(cbn [outside]; clear - Hx MDL; unfold wp_box in *; split; [lia | exact I])).
    rewrite (MU9 x ltac:(cbn [outside]; clear - Hx LKN; unfold wp_box in *; lia)).
    rewrite (PRES8 x ltac:(apply (acl_live _ _ _ lk 40); [exact INL2 | clear - Hx; lia]) ltac:(cbn [outside]; unfold G_ALLOW_CUST; clear - Hx LKH; lia)).
    rewrite (MU7 x ltac:(cbn [outside]; clear - Hx LKN; unfold wp_box in *; lia)).
    rewrite (PRES6 x ltac:(apply (acl_live _ _ _ lk 40); [exact INL2 | clear - Hx; lia]) ltac:(clear - Hx LKN; unfold wp_box in *; lia)).
    apply (MU5 x). cbn [outside]. clear - Hx LKN. unfold wp_box in *. lia. }
  assert (AGL : forall a k, (L <= a /\ a + k <= L + 264) \/ (qp <= a /\ a + k <= qp + 16) -> agree_on (fun x => a <= x < a + k) m12 m13).
  { intros a k H. apply AG1213. clear - H LN QPN. unfold wp_box in *. lia. }
  split; [apply (rw_cells_agree asegs m12 m13 _ _ CL0); [apply AGL; left; unfold rcu_head; cbn [cells_size csize Nat.add]; lia | exact WM13]|].
  split; [apply (rw_cells_agree asegs m12 m13 _ _ CLM1); [apply AGL; left; unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | exact WM13]|].
  split; [apply (rw_cells_agree asegs m12 m13 _ _ CLM2); [apply AGL; left; unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | exact WM13]|].
  split; [apply (rw_cells_agree asegs m12 m13 _ _ CLC1); [apply AGL; left; unfold cond_cells; cbn [cells_size csize Nat.add]; lia | exact WM13]|].
  split; [apply (rw_cells_agree asegs m12 m13 _ _ CLM3); [apply AGL; left; unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | exact WM13]|].
  split; [apply (rw_cells_agree asegs m12 m13 _ _ CLC2); [apply AGL; left; unfold cond_cells; cbn [cells_size csize Nat.add]; lia | exact WM13]|].
  split; [apply (rw_cells_agree asegs m12 m13 _ _ CLQ); [apply AGL; right; cbn [cells_size csize Nat.add]; lia | exact WM13]|].
  apply (bytes_at_agree asegs m12 m13 _ _ ZERq12). rewrite repeat_length, Z2Nat.id by (unfold NB_BYTES; lia). apply AG1213. clear - QN. unfold wp_box in *. lia.
Qed.
End HtNew.
