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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).

Section RcuLockNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM1 : stack_malloc_contract RT 1.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.

Definition RCU_SITES : list (Z * Z) :=
  [(SITE_rcu_zalloc, e_rcu_lock_new); (SITE_rcu_calloc, e_rcu_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition RCU_CALLS : list (Z * Z) :=
  [(SITE_rcu_zalloc, e_CRYPTO_zalloc); (SITE_rcu_calloc, e_CRYPTO_calloc); (SITE_rcu_calloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].

(* [comment removed for export] *)
Definition rcu_lock_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 1 -> bv_unsigned a1 <> 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x1d0 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_rcu_lock_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) RCU_SITES RCU_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> 1 + mcost 264 + mcost 16 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rcu_lock_new m)))
    (fun c => exists (Σ' : rts RT) (p q : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' p 264 /\ acc asegs m' p 264 /\ wr_at asegs m' q 16 /\ acc asegs m' q 16
           /\ rw_cells asegs m' p (rcu_head a1 q)
           /\ rw_cells asegs m' (p + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' (p + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' (p + 128) cond_cells
           /\ rw_cells asegs m' (p + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' (p + 216) cond_cells
           /\ rw_cells asegs m' q [CB 16 (repeat (Z_to_bv 8 0) 16)]) c
       /\ rt_live RT Σ' = (q, 16) :: (p, 264) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 - (mcost 264 + mcost 16)
       /\ 0 < p /\ p mod 16 = 0 /\ p + 264 < USTACK_TOP /\ 0 < q /\ q mod 16 = 0 /\ q + 16 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem rcu_lock_new_cps : rcu_lock_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> -> Ha1 ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 240 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -160 - pad).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (WHLO : lo <= usp - 176 - 64) by (unfold RT_STACK in *; lia).
  pose proof (wg_mcost_nonneg 264) as MC1. pose proof (wg_mcost_nonneg 16) as MC2.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  (* [comment removed for export] *)
  assert (COK : forall mm Σx, stk asegs mm lo usp1 -> rt_sp0 RT Σx = rt_sp0 RT Σ -> call_ok RT Σx mm (Z_to_bv 64 usp1) lo).
  { intros mm Σx S E. unfold call_ok. rewrite EU1, E. split; [exact S|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|].
    split; [unfold USTACK_TOP in *; lia|]. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (rcu_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad
                HP HPM ST ltac:(lia) ltac:(lia) ltac:(lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 160 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 160 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG1) as UWF1.
  (* [comment removed for export] *)
  apply (SM1 Σ PMc (Z_to_bv 64 SITE_rcu_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 96) a1' a2' a3 a4 a5 a6 a7
           s2 a1 (Z_to_bv 64 1) s5 s6 s7 s8 s9 (Z_to_bv 64 0x7fff8000) s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(right; left; reflexivity) eq_refl Hfr ltac:(lia) ART1 MI1
           (COK m1 Σ ST1 eq_refl) _ _ Hc1').
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_rcu_smalloc) in Hc2' by (unfold SITE_rcu_smalloc; lia).
  assert (INF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 1%nat ART2 INF) as (_ & FLO & _ & _).
  pose proof (af_frames_align RT AF Σ1 m2 f 1%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 1%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 1) with 128 in FLO, FSH, FU, WF2, WS2. change (128 - 8) with 120 in WF2. change (128 / 8) with 16 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 128) = shad f + 16) by (replace (f + 128) with (f + 64 * 2) by lia; rewrite (shad_add64 f 2 F64); lia).
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -160)) by (apply (stk_agree_nw asegs m1 m2 _ _ GAP1); intros x Hx; cbv beta in Hx; apply PRES2; left; unfold USTACK_TOP in *; lia).
  pose proof (cl_env_pres _ _ _ m1 m2 lb canary ENV1 PRES2) as ENV2.
  assert (AG12 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; cbv beta in Ha; apply PRES2; left; unfold usp1; lia).
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AG12) as UWF2.
  destruct (wr_at_rw_CB m2 f 120 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 16 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 120) with 120%nat in FB2. change (Z.to_nat 16) with 16%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (rcu_w1 ra sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 a1 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s11 u3 u4 u5 u6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 f lo pad j fj sj HP F0 ltac:(unfold USTACK_TOP in *; lia) ltac:(right; exact FIMG)
                ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(fold usp; lia)
                ltac:(left; fold usp; unfold RT_STACK in *; lia) UT2 FR2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (a3' & j3 & fj3 & sj3 & m3 & -> & MU3 & WM3 & MI3 & FR3 & FB3 & SB3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, Hc3'. fold usp1 in Hc3'.
  assert (Q1 := div8_facts f).
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 160) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; lia].
    - apply (acl_fshadow _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; rewrite SHF; unfold shad, SHB; lia].
    - apply acl_stack. unfold USTACK_TOP in *. lia. }
  assert (ST3 : stk asegs m3 lo usp1).
  { apply (stk_munch _ m2 m3 lo usp1 ST2 MU3 WM3). intros x Hx. cbn [outside]. unfold usp1 in Hx. lia. }
  assert (GAP3 : stk asegs m3 usp1 (usp + -160)).
  { apply (stk_munch _ m2 m3 _ _ GAP2 MU3 WM3). intros x Hx. cbn [outside]. unfold usp1 in Hx. lia. }
  pose proof (cl_env_seg _ m2 m3 _ canary ENV2 MU3 ltac:(cl_fp_lia)) as ENV3.
  assert (AG23 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3).
  { apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside]. unfold USTACK_TOP in *. lia. }
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AG23) as UWF3.
  (* [comment removed for export] *)
  assert (CHK : checked_dst RT Σ1 m3 (Z_to_bv 64 usp1) (usp1 + 40) 16).
  { split; [| split].
    - intros _. split.
      + apply (af_acc_stack RT AF Σ1 m3 _ _ ART3); rewrite ?SP1; unfold usp1, USTACK_TOP in *; lia.
      + right; right; left. rewrite SP1. unfold usp1, USTACK_TOP in *. lia.
    - intros i Hi. rewrite EU1. left. unfold usp1, USTACK_TOP in *. lia.
    - apply (stk_wr_at m3 _ _ _ _ (stk_of_rw_cells asegs m3 _ _ FR3)); cbn [cells_size csize Nat.add]; unfold usp1; lia. }
  apply (MSET Σ1 PMc (Z_to_bv 64 SITE_rcu_memset) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 usp1)
           (Z_to_bv 64 (usp1 + 40)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3' b4 b5 b6 b7 (Z_to_bv 64 f) a1 (Z_to_bv 64 1) s5 s6 s7
           (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s11 u3 u4 u5 u6 F2 fc2 m3 (usp1 + 40) 16 (Z_to_bv 8 0) lo
           FDO MST eq_refl eq_refl eq_refl ltac:(unfold usp1, USTACK_TOP in *; lia) ltac:(lia) CHK ART3 MI3 (COK m3 Σ1 ST3 SP1) _ _ Hc3').
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ZER4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_rcu_memset) in Hc4' by (unfold SITE_rcu_memset; lia).
  (* [comment removed for export] *)
  destruct (proj1 (rw_cells_app m3 (usp + -160) [CB 56 j3] _) FR3) as [_ FRr3]. cbn [cells_size csize Nat.add] in FRr3.
  assert (FRr4 : rw_cells asegs m4 (usp + -160 + 56) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m3 m4 _ _ FRr3); [| exact WM4]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply PRES4; [left; unfold usp1; unfold USTACK_TOP in *; lia | unfold usp1; lia]. }
  assert (WRj3 : wr_at asegs m3 (usp + -160) 56).
  { pose proof (stk_of_rw_cells asegs m3 _ _ FR3) as S3. cbn [cells_size csize Nat.add] in S3. apply (stk_wr_at m3 _ _ _ _ S3); lia. }
  destruct (wr_at_rw_CB m4 (usp + -160) 56 (wr_at_wm m3 m4 _ _ WRj3 WM4) ltac:(lia)) as (j4 & FRj4). clear WRj3.
  change (Z.to_nat 56) with 56%nat in FRj4.
  pose proof (proj2 (rw_cells_app m4 (usp + -160) [CB 56 j4] _) (conj FRj4 FRr4)) as FR4. clear FRj4 FRr4 FRr3. cbn [app] in FR4.
  assert (WM24 : wmono asegs m2 m4) by exact (wmono_trans asegs _ _ _ WM3 WM4).
  destruct (wr_at_rw_CB m4 f 120 (wr_at_wm m2 m4 _ _ WF2 WM24) ltac:(lia)) as (fj4 & FB4).
  destruct (wr_at_rw_CB m4 (f / 8 + 2147450880) 16 (wr_at_wm m2 m4 _ _ WS2 WM24) ltac:(lia)) as (sj4 & SB4).
  change (Z.to_nat 120) with 120%nat in FB4. change (Z.to_nat 16) with 16%nat in SB4.
  assert (GAP4 : stk asegs m4 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m3 m4 _ _ GAP3). intros x Hx. cbv beta in Hx. apply PRES4; [left; unfold USTACK_TOP in *; lia | unfold usp1 in *; lia]. }
  assert (ENV4 : cl_env m4 lb canary).
  { apply (cl_env_pres_ex _ _ _ _ _ m3 m4 lb canary ENV3 PRES4). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)). unfold usp1, SEGTOP_A in *. lia. }
  assert (AG34 : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4).
  { intros a Ha. cbv beta in Ha. apply PRES4; [left; unfold usp1; lia | unfold usp1; lia]. }
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AG34) as UWF4.
  (* [comment removed for export] *)
  pose proof (rcu_w2 sp gp (Z_to_bv 64 TP_A) v0 v1 v2 (Z_to_bv 64 (usp1 + 40)) d1 d2 d3 d4 d5 d6 d7 a1 s5 s6 s7 s11 v3 v4 v5 v6 F4 fc4 m4 f lo pad fj4 sj4
                HP WHLO ltac:(lia) ltac:(lia) F0 ltac:(lia) ltac:(destruct FSH; [left | right]; lia) Ha1 ST4 FB4 SB4 MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (w0 & w1 & w2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & fj5 & sj5 & m5 & -> & MU5 & WM5 & MI5 & ST5 & FB5 & SB5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, Hc5'. fold usp1 in MU5, ST5, Hc5'.
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 (usp1 - 16) ART4 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; lia].
    - apply (acl_fshadow _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; rewrite SHF; unfold shad, SHB; lia].
    - apply acl_stack. unfold usp1, USTACK_TOP in *. lia. }
  pose proof (cl_env_seg _ m4 m5 _ canary ENV4 MU5 ltac:(cl_fp_lia)) as ENV5.
  assert (AG45 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) -> agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H. apply (agree_of_munch _ m4 m5 _ MU5). intros x Hx. cbv beta in Hx. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK in *. lia. }
  assert (FR5 : rw_cells asegs m5 (usp + -160) [CB 56 j4; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5 _ _ FR4); [| exact WM5]. apply AG45. cbn [cells_size csize Nat.add]. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP5 : stk asegs m5 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m4 m5 _ _ GAP4). replace (usp + -160) with (usp1 + (usp + -160 - usp1)) by lia. apply AG45. unfold usp1, USTACK_TOP in *. lia. }
  assert (AG45u : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG45. unfold usp1. lia. }
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AG45u) as UWF5.
  destruct (cl_chain_call (rt_cg RT Σ1) e_rcu_lock_new e_CRYPTO_zalloc SITE_rcu_zalloc m5 m5 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG1; exact CTX)
              ltac:(rewrite CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG1; apply (proj2 CGH); wp_in_lit) UWF5 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -160 + Z.of_nat (cells_size [CB 56 j4; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m5 (usp + -160) [CB 56 j4; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR5))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTXc5 & UWCc5).
  (* [comment removed for export] *)
  apply (C_CZ Σ1 PMc (Z_to_bv 64 SITE_rcu_zalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 264) (Z_to_bv 64 0x491e0) (Z_to_bv 64 575)
           e3 e4 e5 e6 e7 (Z_to_bv 64 f) a1 (Z_to_bv 64 2) a1 s6 s7 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s11 w3 w4 w5 w6
           F4 fc4 m5 264 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART5 MI5 (COK m5 Σ1 ST5 SP1)).
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_rcu_zalloc) by (unfold SITE_rcu_zalloc; lia). exact CTXc5. }
  { exact UWCc5. }
  { rewrite CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV1. lia. }
  { rewrite CR1. lia. }
  { exact ENV5. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ2 & p & Hc6 & LV2 & FRS2 & SP2 & CR2 & P0 & P16 & PU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ENV6 & WR6 & ACC6 & ZER6) & Hc6'). clear Hc6.
  destruct RS6 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_rcu_zalloc) in Hc6' by (unfold SITE_rcu_zalloc; lia).
  assert (INP2 : In (p, 264) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INF2 : In (f, 1%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m6 p 264 ART6 INP2 ltac:(lia)) as PHH.
  pose proof (af_live_range RT AF Σ2 m6 p 264 ART6 INP2) as (_ & PLO & _). rewrite SP2, SP1 in PLO.
  assert (PSTK : p + 264 <= lo) by (unfold STACK_WIN in *; lia).
  pose proof (af_frames_range RT AF Σ2 m6 f 1%nat ART6 INF2) as (_ & _ & _ & PF). specialize (PF p 264 INP2). change (fs_size 1) with 128 in PF.
  pose proof (wg_mod16_8 _ P16) as PAL.
  pose proof (wp_cells_congr asegs m6 p [CB (Z.to_nat 264) (repeat (Z_to_bv 8 0) (Z.to_nat 264))] [CB 264 (repeat (Z_to_bv 8 0) 264)] ltac:(reflexivity) ltac:(reflexivity)
                ltac:(cbn; repeat first [exact I | reflexivity | split]) (wp_zero_rw_CB asegs m6 p 264 ZER6 WR6 ltac:(lia))) as HB6.
  assert (AG56 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 120) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 16)
                             -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H x Hx. cbv beta in Hx. apply PRES6.
    - destruct H as [H|[H|H]].
      + left. lia.
      + apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; lia].
      + apply (acl_fshadow _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; rewrite SHF; unfold shad, SHB; lia].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. unfold USTACK_TOP, RT_STACK, usp1 in *. lia. }
  assert (FR6 : rw_cells asegs m6 (usp + -160) [CB 56 j4; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m5 m6 _ _ FR5); [| exact WM6]. apply AG56. left. cbn [cells_size csize Nat.add]. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP6 : stk asegs m6 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m5 m6 _ _ GAP5). replace (usp + -160) with (usp1 + (usp + -160 - usp1)) by lia. apply AG56. left. unfold usp1, USTACK_TOP in *. lia. }
  assert (WM46 : wmono asegs m4 m6) by exact (wmono_trans asegs _ _ _ WM5 WM6).
  assert (WM26 : wmono asegs m2 m6) by exact (wmono_trans asegs _ _ _ WM24 WM46).
  destruct (wr_at_rw_CB m6 f 120 (wr_at_wm m2 m6 _ _ WF2 WM26) ltac:(lia)) as (fj6 & FB6). change (Z.to_nat 120) with 120%nat in FB6.
  destruct (af_client_consts RT AF Σ2 m6 ART6) as (_ & _ & _ & _ & UT6).
  pose proof (cl_env_ssp m6 _ canary UT6 ENV6) as SSP6.
  assert (AG56u : agree_on (fun x => usp <= x < USTACK_TOP) m5 m6).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG56. left. unfold usp1. lia. }
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWF5 AG56u) as UWF6.
  (* [comment removed for export] *)
  pose proof (rcu_w3 ra sp gp (Z_to_bv 64 TP_A) x0 x1 x2 g1 g2 g3 g4 g5 g6 g7 a1 s6 s7 s11 x3 x4 x5 x6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F6 fc6 m6 p f lo pad j4 fj6 canary
                HP WHLO ltac:(lia) ltac:(lia) PHH PSTK PAL F0 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(destruct PF; [right | left]; lia) ST6 FR6 FB6 HB6 ACC6 SSP6 MI6) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (y0 & y1 & y2 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & j7 & fj7 & m7 & -> & MU7 & WM7 & MI7 & ST7 & SSP7 & FR7 & FB7 & HB07 & PM1 & PM2 & QC1 & PM3 & QC2) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, FR7, Hc7'. fold usp1 in MU7, ST7, Hc7'.
  assert (ART7 : ART RT Σ2 m7).
  { apply (af_frame RT AF Σ2 m6 m7 (usp1 - 64) ART6 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. split; [| split; [| split; [| split; [| exact I]]]]; intros Hin; apply Ha.
    - apply (acl_live _ _ _ p 264); [exact INP2 | lia].
    - apply (acl_frame _ _ _ f 1%nat); [exact INF2 | change (fs_size 1) with 128; lia].
    - apply acl_stack. unfold usp1, USTACK_TOP in *. lia.
    - apply acl_stack. unfold usp1, USTACK_TOP in *. lia. }
  pose proof (cl_env_seg _ m6 m7 _ canary ENV6 MU7 ltac:(cl_fp_lia)) as ENV7.
  assert (AG67u : agree_on (fun x => usp <= x < USTACK_TOP) m6 m7).
  { apply (agree_of_munch _ m6 m7 _ MU7). intros x Hx. cbv beta in Hx. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m6 m7 sp s0 UWF6 AG67u) as UWF7.
  destruct (cl_chain_call (rt_cg RT Σ2) e_rcu_lock_new e_CRYPTO_calloc SITE_rcu_calloc m7 m7 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG2, CG1; exact CTX)
              ltac:(rewrite CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF7 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -160 + Z.of_nat (cells_size [CB 56 j7; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m7 (usp + -160) [CB 56 j7; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR7))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTXc7 & UWCc7).
  (* [comment removed for export] *)
  apply (C_CALLOC Σ2 PMc (Z_to_bv 64 SITE_rcu_calloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) y0 y1 y2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 2) (Z_to_bv 64 8) (Z_to_bv 64 0x491e0) (Z_to_bv 64 460)
           h4 h5 h6 h7 (Z_to_bv 64 f) (Z_to_bv 64 p) (Z_to_bv 64 2) (Z_to_bv 64 (p + 16)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (p + 128)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (f + 64)) y3 y4 y5 y6 F6 fc6 m7 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl
           ltac:(rewrite ?unsigned_lit by lia; lia) ltac:(vm_compute; reflexivity) ART7 MI7 (COK m7 Σ2 ST7 ltac:(rewrite SP2; exact SP1))).
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_rcu_calloc) by (unfold SITE_rcu_calloc; lia). exact CTXc7. }
  { exact UWCc7. }
  { rewrite (unsigned_lit SITE_rcu_calloc) by (unfold SITE_rcu_calloc; lia). rewrite CG2, CG1. apply (proj2 CGH). wp_in_lit. }
  { rewrite CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV2, LV1. cbn [length]. lia. }
  { rewrite ?(unsigned_lit 2), ?(unsigned_lit 8) by lia. change (2 * 8) with 16. rewrite CR2, CR1. lia. }
  { exact ENV7. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ3 & q & Hc8 & LV3 & FRS3 & SP3 & CR3 & Q0 & Q16 & QU & CG3).
  rewrite ?(unsigned_lit 2), ?(unsigned_lit 8) in LV3, CR3, QU, Hc8 by lia. change (2 * 8) with 16 in LV3, CR3, QU, Hc8.
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ENV8 & WRq & ACCq & ZERq) & Hc8'). clear Hc8.
  destruct RS8 as (z0 & z1 & z2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z3 & z4 & z5 & z6 & F8 & fc8 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_rcu_calloc) in Hc8' by (unfold SITE_rcu_calloc; lia).
  assert (INQ3 : In (q, 16) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
  assert (INP3 : In (p, 264) (rt_live RT Σ3)) by (rewrite LV3; right; exact INP2).
  assert (INF3 : In (f, 1%nat) (rt_frames RT Σ3)) by (rewrite FRS3; exact INF2).
  pose proof (af_live_range RT AF Σ3 m8 q 16 ART8 INQ3) as (_ & QLO & _). rewrite SP3, SP2, SP1 in QLO.
  assert (QSTK : q + 16 <= lo) by (unfold STACK_WIN in *; lia).
  pose proof (wp_cells_congr asegs m8 q [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))] [CB 16 (repeat (Z_to_bv 8 0) 16)] ltac:(reflexivity) ltac:(reflexivity)
                ltac:(cbn; repeat first [exact I | reflexivity | split]) (wp_zero_rw_CB asegs m8 q 16 ZERq WRq ltac:(lia))) as HBq8.
  assert (AG78 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) \/ (p <= a /\ a + k <= p + 264) \/ (f <= a /\ a + k <= f + 120) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 16)
                             -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H x Hx. cbv beta in Hx. apply PRES8.
    - destruct H as [H|[H|[H|H]]].
      + left. lia.
      + apply (acl_live _ _ _ p 264); [exact INP2 | lia].
      + apply (acl_frame _ _ _ f 1%nat); [exact INF2 | change (fs_size 1) with 128; lia].
      + apply (acl_fshadow _ _ _ f 1%nat); [exact INF2 | change (fs_size 1) with 128; rewrite SHF; unfold shad, SHB; lia].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. unfold USTACK_TOP, RT_STACK, usp1 in *. lia. }
  assert (FR8 : rw_cells asegs m8 (usp + -160) [CB 56 j7; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m7 m8 _ _ FR7); [| exact WM8]. apply AG78. left. cbn [cells_size csize Nat.add]. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP7 : stk asegs m7 usp1 (usp + -160)).
  { apply (stk_munch _ m6 m7 _ _ GAP6 MU7 WM7). intros x Hx. cbn [outside]. unfold usp1 in *. lia. }
  assert (GAP8 : stk asegs m8 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m7 m8 _ _ GAP7). replace (usp + -160) with (usp1 + (usp + -160 - usp1)) by lia. apply AG78. left. unfold usp1, USTACK_TOP in *. lia. }
  assert (HB08 : rw_cells asegs m8 p (rcu_head_a a1)).
  { apply (rw_cells_agree asegs m7 m8 _ _ HB07); [| exact WM8]. apply AG78. right; left. unfold rcu_head_a. cbn [cells_size csize Nat.add]. lia. }
  assert (PM1' : rw_cells asegs m8 (p + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)))
    by (apply (rw_cells_agree asegs m7 m8 _ _ PM1); [| exact WM8]; apply AG78; right; left; unfold mutex_cells; cbn [cells_size csize Nat.add]; lia).
  assert (PM2' : rw_cells asegs m8 (p + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)))
    by (apply (rw_cells_agree asegs m7 m8 _ _ PM2); [| exact WM8]; apply AG78; right; left; unfold mutex_cells; cbn [cells_size csize Nat.add]; lia).
  assert (QC1' : rw_cells asegs m8 (p + 128) cond_cells)
    by (apply (rw_cells_agree asegs m7 m8 _ _ QC1); [| exact WM8]; apply AG78; right; left; unfold cond_cells; cbn [cells_size csize Nat.add]; lia).
  assert (PM3' : rw_cells asegs m8 (p + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)))
    by (apply (rw_cells_agree asegs m7 m8 _ _ PM3); [| exact WM8]; apply AG78; right; left; unfold mutex_cells; cbn [cells_size csize Nat.add]; lia).
  assert (QC2' : rw_cells asegs m8 (p + 216) cond_cells)
    by (apply (rw_cells_agree asegs m7 m8 _ _ QC2); [| exact WM8]; apply AG78; right; left; unfold cond_cells; cbn [cells_size csize Nat.add]; lia).
  clear PM1 PM2 PM3 QC1 QC2 HB07.
  pose proof (proj2 (af_acc_live RT AF Σ3 m8 p 264 ART8 INP3)) as ACC8.
  assert (AG78u : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG78. left. unfold usp1. lia. }
  pose proof (uw_chain_agree outer m7 m8 sp s0 UWF7 AG78u) as UWF8.
  assert (WM68 : wmono asegs m6 m8) by exact (wmono_trans asegs _ _ _ WM7 WM8).
  assert (WM28 : wmono asegs m2 m8) by exact (wmono_trans asegs _ _ _ WM26 WM68).
  (* [comment removed for export] *)
  pose proof (rcu_w4 sp gp (Z_to_bv 64 TP_A) z0 z1 z2 k1 k2 k3 k4 k5 k6 k7 a1 z3 z4 z5 z6 F8 fc8 m8 p q f lo pad
                ltac:(lia) ltac:(lia) ltac:(lia) PHH PSTK PAL Q0 QSTK F0 ltac:(lia) ST8 HB08 ACC8 MI8) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ3 _ _ c9 Hc9) as (ms9 & (i1 & i2 & m9 & -> & MU9 & WM9 & MI9 & ST9 & HB9) & Hc9'). clear Hc9.
  fold usp in Hc9'. fold usp1 in ST9, Hc9'.
  assert (ART9 : ART RT Σ3 m9).
  { apply (af_frame RT AF Σ3 m8 m9 usp1 ART8 ltac:(rewrite SP3, SP2, SP1; unfold usp1; lia)); [| exact WM9].
    intros a Ha. apply MU9. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ p 264); [exact INP3 | lia]. }
  pose proof (cl_env_seg _ m8 m9 _ canary ENV8 MU9 ltac:(cl_fp_lia)) as ENV9.
  assert (AG89 : forall a k, (a + k <= p \/ p + 48 <= a) -> agree_on (fun x => a <= x < a + k) m8 m9).
  { intros a k H. apply (agree_of_munch _ m8 m9 _ MU9). intros x Hx. cbv beta in Hx. cbn [outside]. lia. }
  assert (FR9 : rw_cells asegs m9 (usp + -160) [CB 56 j7; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m8 m9 _ _ FR8); [| exact WM9]. apply AG89. cbn [cells_size csize Nat.add]. unfold usp1, USTACK_TOP in *. lia. }
  assert (GAP9 : stk asegs m9 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m8 m9 _ _ GAP8). replace (usp + -160) with (usp1 + (usp + -160 - usp1)) by lia. apply AG89. unfold usp1, USTACK_TOP in *. lia. }
  assert (WM29 : wmono asegs m2 m9) by exact (wmono_trans asegs _ _ _ WM28 WM9).
  destruct (wr_at_rw_CB m9 f 120 (wr_at_wm m2 m9 _ _ WF2 WM29) ltac:(lia)) as (fj9 & FB9). change (Z.to_nat 120) with 120%nat in FB9.
  destruct (wr_at_rw_CB m9 (f / 8 + 2147450880) 16 (wr_at_wm m2 m9 _ _ WS2 WM29) ltac:(lia)) as (sj9 & SB9). change (Z.to_nat 16) with 16%nat in SB9.
  assert (AG89u : agree_on (fun x => usp <= x < USTACK_TOP) m8 m9).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG89. unfold usp1, USTACK_TOP in *. lia. }
  pose proof (uw_chain_agree outer m8 m9 sp s0 UWF8 AG89u) as UWF9.
  (* [comment removed for export] *)
  pose proof (rcu_w5 sp gp (Z_to_bv 64 TP_A) z0 z1 z2 (Z_to_bv 64 q) i1 i2 k3 k4 k5 k6 k7 a1 z3 z4 z5 z6 F8 fc8 m9 p f lo pad fj9 sj9
                ltac:(lia) ltac:(lia) ltac:(lia) F0 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ST9 FB9 SB9 MI9) as W5.
  fold usp usp1 in W5.
  cl_lift W5 Hc9' c10 Hc10.
  destruct (ASTA_unpack RT Σ3 _ _ c10 Hc10) as (ms10 & (i0 & fj10 & sj10 & m10 & -> & MU10 & WM10 & MI10 & ST10 & FB10 & SB10) & Hc10'). clear Hc10.
  fold usp in Hc10'. fold usp1 in ST10, Hc10'.
  assert (ART10 : ART RT Σ3 m10).
  { apply (af_frame RT AF Σ3 m9 m10 usp1 ART9 ltac:(rewrite SP3, SP2, SP1; unfold usp1; lia)); [| exact WM10].
    intros a Ha. apply MU10. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 1%nat); [exact INF3 | change (fs_size 1) with 128; lia].
    - apply (acl_fshadow _ _ _ f 1%nat); [exact INF3 | change (fs_size 1) with 128; rewrite SHF; unfold shad, SHB; lia]. }
  pose proof (cl_env_seg _ m9 m10 _ canary ENV9 MU10 ltac:(cl_fp_lia)) as ENV10.
  assert (AG910 : forall a k, (a + k <= f \/ f + 120 <= a) -> (a + k <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= a) -> agree_on (fun x => a <= x < a + k) m9 m10).
  { intros a k H1 H2. apply (agree_of_munch _ m9 m10 _ MU10). intros x Hx. cbv beta in Hx. cbn [outside]. lia. }
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 16 <= 2^44) by (clear - F0 FLO NUM LOW HSTK; unfold USTACK_TOP in *; Z.div_mod_to_equations; lia). lia. }
  assert (FR10 : rw_cells asegs m10 (usp + -160) [CB 56 j7; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m9 m10 _ _ FR9); [| exact WM10]. apply AG910; cbn [cells_size csize Nat.add]; unfold usp1, USTACK_TOP in *; lia. }
  assert (GAP10 : stk asegs m10 usp1 (usp + -160)).
  { apply (stk_agree_nw asegs m9 m10 _ _ GAP9). replace (usp + -160) with (usp1 + (usp + -160 - usp1)) by lia. apply AG910; unfold usp1, USTACK_TOP in *; lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ3 m10 f 1%nat (rt_frames RT Σ) ART10 ltac:(rewrite FRS3, FRS2; exact FRS1)) as (Σ4 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 1) with 128 in FW. replace (f + 128 - 8) with (f + 120) in FW by lia. rewrite SP3, SP2, SP1 in FLW.
  (* [comment removed for export] *)
  pose proof (rcu_w6 ra sp gp (Z_to_bv 64 TP_A) z0 z1 z2 i0 i1 i2 k3 k4 k5 k6 k7 z3 z4 z5 z6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F8 fc8 m10 p f fl lo pad j7
                HP ltac:(lia) ltac:(lia) ltac:(lia) F0 ltac:(lia) FL0 ltac:(lia) ST10 GAP10 FR10 FW FLC MI10) as W6.
  fold usp usp1 in W6.
  cl_lift W6 Hc10' c11 Hc11.
  destruct (ASTA_unpack RT Σ3 _ _ c11 Hc11) as (ms11 & (m11 & -> & MU11 & WM11 & MI11 & ST11 & FLC11) & Hc11'). clear Hc11.
  fold usp in ST11.
  destruct (REL m11 MU11 WM11 FLC11) as (ART11 & FRS4 & LV4 & SP4 & CR4 & AL4 & AM4 & CG4).
  assert (LV4' : rt_live RT Σ4 = (q, 16) :: (p, 264) :: rt_live RT Σ) by (rewrite LV4, LV3, LV2, LV1; reflexivity).
  assert (INP4 : In (p, 264) (rt_live RT Σ4)) by (rewrite LV4'; right; left; reflexivity).
  assert (INQ4 : In (q, 16) (rt_live RT Σ4)) by (rewrite LV4'; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m8 q 16 ART8 INQ3 ltac:(lia)) as QHH.
  pose proof (af_live_disj RT AF Σ3 m8 q 16 p 264 [] (rt_live RT Σ2) ART8 LV3 INP2) as QP.
  pose proof (af_frames_range RT AF Σ3 m8 f 1%nat ART8 INF3) as (_ & _ & _ & QF). specialize (QF q 16 INQ3). change (fs_size 1) with 128 in QF.
  (* [comment removed for export] *)
  assert (NFL : forall x, aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp1 x -> x <> fl).
  { intros x Hx E. subst x. apply NAC. destruct Hx as [H|H]; [exfalso; unfold usp1, RT_STACK in *; lia | right; exact H]. }
  assert (AG1011 : forall a k, (forall x, a <= x < a + k -> x <> fl) -> agree_on (fun x => a <= x < a + k) m10 m11).
  { intros a k H. apply (agree_of_munch _ m10 m11 _ MU11). intros x Hx. cbv beta in Hx. specialize (H x Hx). cbn [outside]. lia. }
  assert (AG911 : forall a k, (p <= a /\ a + k <= p + 264) \/ (q <= a /\ a + k <= q + 16) -> agree_on (fun x => a <= x < a + k) m9 m11).
  { intros a k H x Hx. cbv beta in Hx.
    rewrite (AG1011 a k ltac:(intros y Hy; apply NFL; destruct H as [H|H]; [apply (acl_live _ _ _ p 264); [exact INP3 | lia] | apply (acl_live _ _ _ q 16); [exact INQ3 | lia]]) x Hx).
    apply (AG910 a k); [clear - H PF QF; lia | clear - H PHH QHH SHR; lia | exact Hx]. }
  assert (AG811 : forall a k, (p <= a /\ a + k <= p + 264 /\ p + 48 <= a) \/ (q <= a /\ a + k <= q + 16) -> agree_on (fun x => a <= x < a + k) m8 m11).
  { intros a k H x Hx. cbv beta in Hx. rewrite (AG911 a k ltac:(clear - H; lia) x Hx). apply (AG89 a k); [clear - H QP; lia | exact Hx]. }
  assert (WM911 : wmono asegs m9 m11) by exact (wmono_trans asegs _ _ _ WM10 WM11).
  assert (WM811 : wmono asegs m8 m11) by exact (wmono_trans asegs _ _ _ WM9 WM911).
  assert (WM011 : wmono asegs m m11).
  { exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM28 WM811))). }
  apply Hk. exists Σ4, p, q.
  split; [| split; [exact LV4' | split; [rewrite FRS4; reflexivity | split; [rewrite SP4, SP3, SP2; exact SP1 | split; [rewrite CR4, CR3, CR2, CR1; lia |
            split; [exact P0 | split; [exact P16 | split; [exact PU | split; [exact Q0 | split; [exact Q16 | split; [exact QU | rewrite CG4, CG3, CG2; exact CG1]]]]]]]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ3 Σ4 PMc _ c11 Hc11' AL4 AM4)|]. intros ms <-. exists m11.
  split; [exists z0, z1, z2, i1, i2, k3, k4, k5, k6, k7, z3, z4, z5, z6, F8, fc8; reflexivity|].
  split; [split; [exact ART11 | split; [exact MI11 | split; [exact WM011 | exact ST11]]]|].
  split.
  { intros a Ha Ho.
    assert (A1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto | rewrite FRS1; intros e He; right; exact He | unfold usp1; lia]).
    assert (A2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ A1); [rewrite LV2; intros e He; right; exact He | rewrite FRS2; auto | lia]).
    assert (A3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp1 (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ A2); [rewrite LV3; intros e He; right; exact He | rewrite FRS3; auto | lia]).
    destruct (newframe_apart RT AF Σ Σ1 m2 f 1%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (N1 & N2).
    change (fs_size 1) with 128 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    pose proof (newchunk_apart RT AF Σ1 Σ2 m6 p 264 usp1 _ ART6 LV2 FRS2 SP2 ltac:(rewrite SP1; unfold usp1; lia) ltac:(lia) A1) as N3.
    pose proof (cl_split RT AF Σ m usp 240 _ ART0 ltac:(lia) ltac:(lia) Ha) as N5.
    pose proof (NFL _ A3) as N6.
    rewrite (MU11 a ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (MU10 a ltac:(cbn [outside]; clear - N1 N2; lia)).
    rewrite (MU9 a ltac:(cbn [outside]; clear - N3; lia)).
    rewrite (PRES8 a A2 Ho).
    rewrite (MU7 a ltac:(cbn [outside]; unfold usp1 in *; clear - N1 N3 N5 HP; lia)).
    rewrite (PRES6 a A1 Ho).
    rewrite (MU5 a ltac:(cbn [outside]; unfold usp1 in *; clear - N1 N2 N5 HP; lia)).
    rewrite (PRES4 a A1 ltac:(unfold usp1 in *; clear - N5 HP; lia)).
    rewrite (MU3 a ltac:(cbn [outside]; unfold usp1 in *; clear - N1 N2 N5 HP; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | unfold usp1; lia])).
    exact (PR1 a Ha I). }
  split.
  { apply (cl_env_agree m10 m11 _ _ ENV10). intros a Ha'. apply MU11. cbn [outside]. split; [| exact I].
    pose proof (NFL (bv_unsigned a) ltac:(right; left; exact (cl_cell_static _ Ha'))). lia. }
  pose proof (af_acc_live RT AF Σ4 m11 p 264 ART11 INP4) as (WRp & ACCp).
  pose proof (af_acc_live RT AF Σ4 m11 q 16 ART11 INQ4) as (WRq' & ACCq').
  split; [exact WRp|]. split; [exact ACCp|]. split; [exact WRq'|]. split; [exact ACCq'|].
  split.
  { apply (rw_cells_agree asegs m9 m11 _ _ HB9); [| exact WM911]. apply AG911. left. unfold rcu_head. cbn [cells_size csize Nat.add]. lia. }
  split.
  { apply (rw_cells_agree asegs m8 m11 _ _ PM1'); [| exact WM811]. apply AG811. left. unfold mutex_cells. cbn [cells_size csize Nat.add]. lia. }
  split.
  { apply (rw_cells_agree asegs m8 m11 _ _ PM2'); [| exact WM811]. apply AG811. left. unfold mutex_cells. cbn [cells_size csize Nat.add]. lia. }
  split.
  { apply (rw_cells_agree asegs m8 m11 _ _ QC1'); [| exact WM811]. apply AG811. left. unfold cond_cells. cbn [cells_size csize Nat.add]. lia. }
  split.
  { apply (rw_cells_agree asegs m8 m11 _ _ PM3'); [| exact WM811]. apply AG811. left. unfold mutex_cells. cbn [cells_size csize Nat.add]. lia. }
  split.
  { apply (rw_cells_agree asegs m8 m11 _ _ QC2'); [| exact WM811]. apply AG811. left. unfold cond_cells. cbn [cells_size csize Nat.add]. lia. }
  apply (rw_cells_agree asegs m8 m11 _ _ HBq8); [| exact WM811]. apply AG811. right. cbn [cells_size csize Nat.add]. lia.
Qed.
End RcuLockNew.
