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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_locknew Fz_M_aligned Fz_M_aligned_array Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw Fz_I2_htnew Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_I2_nmw Fz_I2_namemap Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tslia ::= wp_tslia.
Notation TP_A := (0xba3ef0)%Z (only parsing).
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ifF | ifT | ubs_if] end).
Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

Definition e_stored_namemap_new : Z := 0x218168.
Definition SITE_snm_nm : Z := 0x21818c.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition snm_cells (ht lk sk : Z) : list cell :=
  [C1 (Z_to_bv 8 1); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition snm_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_snm_nm) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 0x7fff8000) a0 a1' a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_namemap_new) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma snm_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (snm_w0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_stored_namemap_new) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_stored_namemap_new, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia.
  carve_frame 32%nat ST.
  zgo 0x2181cc.
  lazymatch goal with FRH : rw_cells asegs ?mm (SP + -32) (CB 8 ?jj :: ?rest) |- _ => set (j := jj) in FRH end.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold snm_w0_post, SITE_snm_nm, e_namemap_new. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition snm_w1_post (ra0 sp gp tp s0' s1' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm ht lk sk lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 nm) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(nm, nm + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' nm (snm_cells ht lk sk).

Lemma snm_w1 : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s0' s1' : word)
    (F : bvmap 5 word) fc (m : mem) (nm ht lk sk lo : Z) (j : list byte),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0x10007fff8000 <= nm -> nm + 40 <= 2^47 -> nm mod 8 = 0 -> nm + 40 <= lo ->
  stk asegs m lo (bv_unsigned sp + -32) ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 j; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m nm [C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)] ->
  acc asegs m nm 40 -> mem_inv asegs m ->
  evt asegs (snm_w1_post ra0 sp gp tp s0' s1' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc nm ht lk sk lo m)
    (MS (mkR (Z_to_bv 64 SITE_snm_nm) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_snm_nm) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH NMH NMT NMA NSTK ST FR HN ACn MI. unfold SITE_snm_nm in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(nm, nm + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUn : bv_unsigned (Z_to_bv 64 nm) = nm) by (apply unsigned_lit; lia).
  zgo 0x21819c. zsh.
  zgo 0x2181b8.
  release_frame FR ST SP.
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold snm_w1_post, snm_cells. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact ST| exact HN].
Qed.

Lemma NM_COST_nonneg : 0 <= NM_COST.
Proof.
  unfold NM_COST, HT_COST. pose proof (wg_mcost_nonneg 40). pose proof (wg_mcost_nonneg 96). pose proof (wg_mcost_nonneg 24).
  pose proof (wg_mcost_nonneg NB_BYTES). pose proof (wg_mcost_nonneg 264). pose proof (wg_mcost_nonneg 16). pose proof (wg_mcost_nonneg 56). lia.
Qed.

Section StoredNamemapNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_NM : namemap_new_stmt RT.

Definition SNM_SITES : list (Z * Z) := (SITE_snm_nm, e_stored_namemap_new) :: NM_SITES.
Definition SNM_CALLS : list (Z * Z) := (SITE_snm_nm, e_namemap_new) :: NM_CALLS.

(* [comment removed for export] *)
Definition stored_namemap_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> bv_unsigned a0 <> 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x320 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_stored_namemap_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) SNM_SITES SNM_CALLS ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 9 <= LIVE_MAX -> NM_COST <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stored_namemap_new m)))
    (fun c => exists (Σ' : rts RT) (nm lk ht lk2 md q L qp sk : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 nm) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' nm 40 /\ acc asegs m' nm 40
           /\ rw_cells asegs m' nm (snm_cells ht lk sk)
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
       /\ rt_live RT Σ' = (sk, 56) :: (qp, 16) :: (L, 264) :: (q, 32768) :: (md, 24) :: (lk2, 40) :: (ht, 96) :: (lk, 40) :: (nm, 40) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - NM_COST
       /\ 0 < nm /\ nm mod 16 = 0 /\ nm + 40 < USTACK_TOP /\ 0 < lk /\ lk mod 16 = 0 /\ lk + 40 < USTACK_TOP
       /\ 0 < ht /\ ht mod 16 = 0 /\ ht + 96 < USTACK_TOP /\ 0 < lk2 /\ lk2 mod 16 = 0 /\ lk2 + 40 < USTACK_TOP
       /\ 0 < md /\ md mod 16 = 0 /\ md + 24 < USTACK_TOP /\ 0 < q /\ q mod 16 = 0 /\ q + 32768 < USTACK_TOP
       /\ 0 < L /\ L mod 16 = 0 /\ L + 264 < USTACK_TOP /\ 0 < qp /\ qp mod 16 = 0 /\ qp + 16 < USTACK_TOP
       /\ 0 < sk /\ sk mod 16 = 0 /\ sk + 56 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem stored_namemap_new_cps : stored_namemap_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> CTXN ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -32).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  (* [comment removed for export] *)
  pose proof (snm_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(lia) ltac:(lia) UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  destruct (cl_chain_call (rt_cg RT Σ) e_stored_namemap_new e_namemap_new SITE_snm_nm m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWC AG1
              ltac:(fold usp; replace (usp - 16) with (usp + -32 + Z.of_nat (cells_size [CB 8 j; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -32) [CB 8 j; C8 s1] [C8 s0; C8 ra] FR1))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_NM Σ PMc (Z_to_bv 64 SITE_snm_nm) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 0x7fff8000) a0 a1' a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl CTXN ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_snm_nm) by (unfold SITE_snm_nm; lia). exact CTXc1. }
  { exact UWCc1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact Hfr. }
  { exact Hlen. }
  { exact Hcr. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & nm & lk & ht & lk2 & md & q & L & qp & sk & Hc2 & LV1 & FRS1 & SP1 & CR1 & NM0 & NM16 & NMU & LK0 & LK16 & LKU & HT0 & HT16 & HTU
                       & LK20 & LK216 & LK2U & MD0 & MD16 & MDU & Q0 & Q64 & QU & L0 & L16 & LU & QP0 & QP16 & QPU & SK0 & SK16 & SKU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ENV2 & WRn2 & ACCn2 & HNM2 & HLK2 & HHT2 & HMD2 & HLK22
                       & CL0 & CLM1 & CLM2 & CLC1 & CLM3 & CLC2 & CLQ & ZERq & HSK2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_snm_nm) in Hc2' by (unfold SITE_snm_nm; lia).
  assert (INN1 : In (nm, 40) (rt_live RT Σ1)) by (rewrite LV1; do 8 right; left; reflexivity).
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 nm 40 ART2 INN1 ltac:(lia)) as NMH.
  pose proof (af_live_range RT AF Σ1 m2 nm 40 ART2 INN1) as (_ & NMLO & _). rewrite SP1 in NMLO.
  pose proof (wg_mod16_8 _ NM16) as NMA.
  assert (HNM2' : rw_cells asegs m2 nm [C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast m2 nm _ _ HNM2); [cbn; repeat first [exact I | reflexivity | split] | reflexivity]. }
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; clear - H1 H2 Hx; lia |].
    cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H1 Hx NUM HSTK. unfold usp1, USTACK_TOP, RT_STACK in *. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  (* [comment removed for export] *)
  pose proof (snm_w1 ra sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 s0 s1 F2 fc2 m2 nm ht lk sk lo j
                ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(lia) ltac:(lia) NMH ltac:(clear - NMU; unfold USTACK_TOP in *; lia) NMA
                ltac:(clear - NMLO LOW HSTK; unfold RT_STACK in *; lia) ST2 FR2 HNM2' ACCn2 MI2) as W1.
  fold usp in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3 & HNM3) & Hc3'). clear Hc3.
  fold usp in ST3, Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; clear - NUM; unfold usp1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ nm 40); [exact INN1 | clear - Hin; lia]. }
  (* [comment removed for export] *)
  assert (Q16 : q mod 16 = 0) by (clear - Q64; Z.div_mod_to_equations; lia).
  apply Hk. exists Σ1, nm, lk, ht, lk2, md, q, L, qp, sk.
  split; [| split; [exact LV1 | split; [exact FRS1 | split; [exact SP1 | split; [exact CR1 |]]]]].
  2: { repeat (split; [assumption|]). exact CG1. }
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists u0, u1, u2, (Z_to_bv 64 1), b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) | exact ST3]]]|].
  split.
  { intros a Ha Ho.
    pose proof (wg_newchunk_apart RT AF Σ Σ1 m2 [(sk, 56); (qp, 16); (L, 264); (q, NB_BYTES); (md, 24); (lk2, 40); (ht, 96); (lk, 40); (nm, 40)] nm 40 usp (bv_unsigned a)
                  ART2 ltac:(rewrite LV1; reflexivity) ltac:(do 8 right; left; reflexivity) FRS1 SP1 ltac:(clear - NUM; lia) ltac:(clear; lia) Ha) as Nn.
    rewrite (MU3 a ltac:(cbn [outside]; split; [clear - Nn; lia | exact I])).
    assert (A0' : aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | clear; unfold usp1; lia]).
    rewrite (PRES2 a A0' Ho).
    exact (PR1 a Ha I). }
  split; [exact (cl_env_seg _ m2 m3 _ canary ENV2 MU3 ltac:(cl_fp_lia))|].
  pose proof (af_acc_live RT AF Σ1 m3 nm 40 ART3 INN1) as (WRn3 & ACCn3).
  split; [exact WRn3|]. split; [exact ACCn3|]. split; [exact HNM3|].
  assert (AG23 : forall a k, (a + k <= nm \/ nm + 1 <= a) -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H. apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (NMD : forall p n, In (p, n) [(sk, 56); (qp, 16); (L, 264); (q, NB_BYTES); (md, 24); (lk2, 40); (ht, 96); (lk, 40)] -> p + n <= nm \/ nm + 1 <= p).
  { intros p n Hin. destruct (af_live_disj RT AF Σ1 m2 nm 40 p n [(sk, 56); (qp, 16); (L, 264); (q, NB_BYTES); (md, 24); (lk2, 40); (ht, 96); (lk, 40)] (rt_live RT Σ) ART2
              ltac:(rewrite LV1; reflexivity) ltac:(apply in_or_app; left; exact Hin)); [right | left]; clear - H; lia. }
  split; [apply (rw_cells_agree asegs m2 m3 _ _ HLK2); [| exact WM3]; apply AG23; pose proof (NMD lk 40 ltac:(clear; cbn; tauto)) as D; unfold mutex_cells; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ HHT2); [| exact WM3]; apply AG23; pose proof (NMD ht 96 ltac:(clear; cbn; tauto)) as D; unfold ht_tab4; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ HMD2); [| exact WM3]; apply AG23; pose proof (NMD md 24 ltac:(clear; cbn; tauto)) as D; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ HLK22); [| exact WM3]; apply AG23; pose proof (NMD lk2 40 ltac:(clear; cbn; tauto)) as D; unfold mutex_cells; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ CL0); [| exact WM3]; apply AG23; pose proof (NMD L 264 ltac:(clear; cbn; tauto)) as D; unfold rcu_head; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ CLM1); [| exact WM3]; apply AG23; pose proof (NMD L 264 ltac:(clear; cbn; tauto)) as D; unfold mutex_cells; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ CLM2); [| exact WM3]; apply AG23; pose proof (NMD L 264 ltac:(clear; cbn; tauto)) as D; unfold mutex_cells; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ CLC1); [| exact WM3]; apply AG23; pose proof (NMD L 264 ltac:(clear; cbn; tauto)) as D; unfold cond_cells; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ CLM3); [| exact WM3]; apply AG23; pose proof (NMD L 264 ltac:(clear; cbn; tauto)) as D; unfold mutex_cells; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ CLC2); [| exact WM3]; apply AG23; pose proof (NMD L 264 ltac:(clear; cbn; tauto)) as D; unfold cond_cells; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ CLQ); [| exact WM3]; apply AG23; pose proof (NMD qp 16 ltac:(clear; cbn; tauto)) as D; cbn [cells_size csize Nat.add]; clear - D; lia|].
  split.
  { apply (bytes_at_agree asegs m2 m3 _ _ ZERq). rewrite repeat_length, Z2Nat.id by (unfold NB_BYTES; clear; lia).
    apply AG23. pose proof (NMD q NB_BYTES ltac:(clear; cbn; tauto)) as D. clear - D. unfold NB_BYTES in *. lia. }
  apply (rw_cells_agree asegs m2 m3 _ _ HSK2); [| exact WM3]. apply AG23. pose proof (NMD sk 56 ltac:(clear; cbn; tauto)) as D. unfold nm_sk_cells. cbn [cells_size csize Nat.add]. clear - D. lia.
Qed.
End StoredNamemapNew.
