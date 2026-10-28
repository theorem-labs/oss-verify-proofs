(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_locknew Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_local Fz_T_initthread Fz_T_master1 Fz_G_OPENSSL_cpuid_setup Fz_I3_ibasew.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation DTOR_KEY := (0x5a9f20)%Z (only parsing).
Notation DTOR_FN := (0x1f3fb8)%Z (only parsing).

Section IBase.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_LKN : crypto_lock_new_env_stmt RT.
Hypothesis C_CPU : OPENSSL_cpuid_setup_stmt RT.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition LKN_SITES : list (Z * Z) := [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition LKN_CALLS : list (Z * Z) := [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].
Definition IB_SITES : list (Z * Z) := (SITE_ib_lk1, e_ibase) :: (SITE_ib_lk2, e_ibase) :: LKN_SITES.
Definition IB_CALLS : list (Z * Z) := (SITE_ib_lk1, e_lock_new) :: (SITE_ib_lk2, e_lock_new) :: LKN_CALLS.
(* [comment removed for export] *)
Definition IB_W (j1 j2 : Z) : list (Z * Z) :=
  [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (G_IC_OPTS_LOCK, G_IC_OPTS_LOCK + 8); (G_IC_INIT_LOCK, G_IC_INIT_LOCK + 8); (DTOR_KEY, DTOR_KEY + 4); (G_IC_IICL_KEY, G_IC_IICL_KEY + 4);
   (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j1, KEYS + 8 * j1 + 8); (KEYS + 8 * j2, KEYS + 8 * j2 + 8); (G_IC_BASE_INITED, G_IC_BASE_INITED + 1); (G_IC_BASE_RET, G_IC_BASE_RET + 4)].

(* [comment removed for export] *)
Definition ibase_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (nk j1 j2 : Z) (o1 o2 sh kold1 kold2 w r0 : word) (b0 : byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x220 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ibase (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) IB_SITES IB_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 1 < LIVE_MAX -> 2 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  rw_cells asegs m G_IC_OPTS_LOCK [C8 o1] -> rw_cells asegs m G_IC_INIT_LOCK [C8 o2] ->
  rw_cells asegs m DTOR_KEY [C4 kold1] -> rw_cells asegs m G_IC_IICL_KEY [C4 kold2] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j1) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] -> ((j1 = nk /\ w = z64) \/ (j1 = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
  j2 = (j1 + 1) mod 128 -> rw_cells asegs m (KEYS + 8 * j2) [C8 z64] ->
  rw_cells asegs m G_IC_BASE_INITED [C1 b0] -> rw_cells asegs m G_IC_BASE_RET [C4 r0] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ibase m)))
    (fun c => exists (Σ' : rts RT) (p1 p2 : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (IB_W j1 j2) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' G_IC_OPTS_LOCK [C8 (Z_to_bv 64 p1)] /\ rw_cells asegs m' G_IC_INIT_LOCK [C8 (Z_to_bv 64 p2)]
           /\ rw_cells asegs m' p1 (mutex_cells z64 z64) /\ rw_cells asegs m' p2 (mutex_cells z64 z64)
           /\ rw_cells asegs m' DTOR_KEY [C4 (Z_to_bv 64 j1)] /\ rw_cells asegs m' G_IC_IICL_KEY [C4 (Z_to_bv 64 j2)]
           /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j2)] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
           /\ rw_cells asegs m' (KEYS + 8 * j1) [C8 (Z_to_bv 64 DTOR_FN)] /\ rw_cells asegs m' (KEYS + 8 * j2) [C8 (Z_to_bv 64 NODTOR)]
           /\ rw_cells asegs m' G_IC_BASE_INITED [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]) c
       /\ rt_live RT Σ' = (p2, 40) :: (p1, 40) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 2 /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < p1 /\ p1 mod 16 = 0 /\ p1 + 40 < USTACK_TOP /\ 0 < p2 /\ p2 mod 16 = 0 /\ p2 + 40 < USTACK_TOP).

Theorem ibase_cps : ibase_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary nk j1 j2 o1 o2 sh kold1 kold2 w r0 b0
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr CLE OLC ILC DK IK NK HNK KL KJ1 PROBE CASE EJ2 KJ2 BI BR.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA). unfold RT_STACK in HSTK.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 0x220 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  set (usp1 := usp + -32). cl_eu usp (-32) EU1. fold usp1 in EU1.
  assert (HLOS : 0x10007fff8000 <= lo) by exact (proj1 (proj2 NUM)).
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  assert (HJ1 : 0 <= j1 < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  assert (HJ2 : 0 <= j2 < 128 /\ j2 <> j1) by (subst j2; split; [apply Z.mod_pos_bound; lia | clear - HJ1; Z.div_mod_to_equations; lia]).
  unfold G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET in *.
  (* [comment removed for export] *)
  pose proof (ib_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST HLOS ltac:(fold usp; unfold RT_STACK in *; lia) SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (BELOW1 : forall Q : Z -> Prop, (forall x, Q x -> x < usp - 32) -> agree_on Q m m1) by (intros Q HQ a Ha; apply MU1; cbn [outside]; pose proof (HQ _ Ha); split; [lia| exact I]).
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0xbc6000 -> rw_cells asegs m1 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m m1 _ _ X); [| exact WM1]. apply BELOW1. intros; lia. }
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (AGS1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; cbv beta in Ha; apply PR1; [left; exact Ha| exact I]).
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia). exact (rw_cells_skip m1 usp1 [C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ibase e_lock_new SITE_ib_lk1 m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AGS1 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  (* [comment removed for export] *)
  apply (C_LKN Σ PMc (Z_to_bv 64 SITE_ib_lk1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_ib_lk1) by (unfold SITE_ib_lk1; lia). exact CTX1. }
  { exact UWC1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact Hfr. } { lia. } { lia. }
  { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & p1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & P10 & P116 & P1U & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & MC2 & ACC2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ib_lk1) in Hc2' by (unfold SITE_ib_lk1; lia).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 p1 40 ART2 ltac:(rewrite LV1; left; reflexivity) ltac:(clear; lia)) as P1HI.
  assert (AG2 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 x /\ x <> G_ALLOW_CUST) -> agree_on Q m1 m2).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). apply PRES2; [exact X1| cbn [outside]; split; [lia| exact I]]. }
  assert (STAT2 : forall a cs, rw_cells asegs m1 a cs -> ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298)) ->
            (a + Z.of_nat (cells_size cs) <= G_ALLOW_CUST \/ G_ALLOW_CUST + 1 <= a) -> rw_cells asegs m2 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree asegs m1 m2 _ _ X); [| exact WM2]. apply AG2. intros x Hx. cbv beta in Hx. clear - H1 H2 Hx.
    split; [right; left; apply client_static_intro; lia| unfold G_ALLOW_CUST in *; lia]. }
  assert (FR2 : rw_cells asegs m2 usp1 [C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. clear - Hx NUM HLOS HSTK. unfold usp1, G_ALLOW_CUST in *. split; [left; unfold USTACK_TOP in *; lia | lia]. }
  assert (UWC2 : uw_chain m2 sp s0 outer).
  { apply (uw_chain_agree _ m m2 _ _ UWC). intros a Ha. cbv beta in Ha. fold usp in Ha. rewrite (PRES2 a ltac:(left; unfold usp1; lia) ltac:(cbn [outside]; unfold G_ALLOW_CUST, USTACK_TOP in *; split; [lia| exact I])). apply PR1; [left; exact Ha| exact I]. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (ib_w1 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo p1 o1
                ltac:(clear - P10 P1U; unfold USTACK_TOP in *; lia) (STAT2 _ _ (STAT1 _ _ OLC ltac:(cbn; lia)) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) UT2
                ltac:(rewrite EU1; exact ST2) HLOS ltac:(rewrite EU1; unfold usp1 in *; lia) ltac:(rewrite EU1; unfold usp1; lia) MI2) as W1.
  rewrite (ret_pc_even SITE_ib_lk1) in W1 by (unfold SITE_ib_lk1; lia).
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & OLC3 & ST3) & Hc3'). clear Hc3. rewrite EU1 in ST3. unfold G_IC_OPTS_LOCK in MU3, OLC3.
  assert (MU3' : munch ([(0xb9f220, 0xb9f220 + 8)] ++ [(usp1 - 0, usp1)]) m2 m3) by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ1 m2 m3 usp1 0 _ ART2 ltac:(rewrite SP1; unfold usp1; lia) ltac:(unfold usp1, USTACK_TOP in *; lia) MU3' ltac:(intros x Hx; apply client_static_intro; cbn [outside app] in Hx; lia) WM3) as ART3.
  assert (OFF3 : forall Q : Z -> Prop, (forall x, Q x -> ~ (0xb9f220 <= x < 0xb9f220 + 8)) -> agree_on Q m2 m3) by (intros Q HQ a Ha; apply MU3; cbn [outside]; split; [exact (HQ _ Ha)| exact I]).
  assert (STAT3 : forall a cs, rw_cells asegs m2 a cs -> (a + Z.of_nat (cells_size cs) <= 0xb9f220 \/ 0xb9f220 + 8 <= a) -> rw_cells asegs m3 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m2 m3 _ _ X); [| exact WM3]. apply OFF3. clear - H1. intros; lia. }
  pose proof (cl_env_seg _ m2 m3 _ canary CLE2 MU3 ltac:(cl_fp_lia)) as CLE3.
  assert (AGS3 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros a Ha. cbv beta in Ha. rewrite (MU3 a ltac:(cbn [outside]; clear - Ha HSTK HLOS; split; [lia| exact I])).
    rewrite (PRES2 a ltac:(left; unfold usp1; lia) ltac:(cbn [outside]; clear - Ha HSTK HLOS; unfold G_ALLOW_CUST; split; [lia| exact I])). apply PR1; [left; exact Ha| exact I]. }
  assert (FR3 : rw_cells asegs m3 usp1 [C8 s2; C8 s1; C8 s0; C8 ra]) by (apply (STAT3 _ _ FR2); cbn; clear - HSTK HLOS; unfold usp1; lia).
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia). exact (rw_cells_skip m3 usp1 [C8 s2; C8 s1] [C8 s0; C8 ra] FR3). }
  rewrite <- CG1 in CGH, CTX.
  destruct (cl_chain_call (rt_cg RT Σ1) e_ibase e_lock_new SITE_ib_lk2 m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; left; reflexivity)) UWC AGS3 FRR3 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX3 & UWC3).
  (* [comment removed for export] *)
  apply (C_LKN Σ1 PMc (Z_to_bv 64 SITE_ib_lk2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 IB_S1) (Z_to_bv 64 p1) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 IB_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
           F2 fc2 m3 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART3 MI3).
  { assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    unfold call_ok. rewrite EU1. split; [exact ST3|]. split; [exact LOW1|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_ib_lk2) by (unfold SITE_ib_lk2; lia). exact CTX3. }
  { exact UWC3. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS1. exact Hfr. } { rewrite LV1. cbn [length]. lia. } { rewrite CR1. lia. }
  { exact CLE3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & p2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & P20 & P216 & P2U & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & MC4 & ACC4) & Hc4'). clear Hc4.
  destruct RS4 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ib_lk2) in Hc4' by (unfold SITE_ib_lk2; lia).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 p2 40 ART4 ltac:(rewrite LV2; left; reflexivity) ltac:(clear; lia)) as P2HI.
  assert (INP1 : In (p1, 40) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 p1 40 ART2 INP1) as (_ & P1LO & _). rewrite SP1 in P1LO.
  assert (AG4 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x /\ x <> G_ALLOW_CUST) -> agree_on Q m3 m4).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). apply PRES4; [exact X1| cbn [outside]; split; [lia| exact I]]. }
  assert (STAT4 : forall a cs, rw_cells asegs m3 a cs -> ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298)) ->
            (a + Z.of_nat (cells_size cs) <= G_ALLOW_CUST \/ G_ALLOW_CUST + 1 <= a) -> rw_cells asegs m4 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG4. intros x Hx. cbv beta in Hx. clear - H1 H2 Hx.
    split; [right; left; apply client_static_intro; lia| unfold G_ALLOW_CUST in *; lia]. }
  assert (FR4 : rw_cells asegs m4 usp1 [C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. clear - Hx NUM HLOS HSTK. unfold usp1, G_ALLOW_CUST in *. split; [left; unfold USTACK_TOP in *; lia | lia]. }
  assert (MC14 : rw_cells asegs m4 p1 (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m3 m4 _ _ (STAT3 _ _ MC2 ltac:(cbn [cells_size csize Nat.add mutex_cells]; clear - P1HI; lia))); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add mutex_cells]. intros x Hx.
    clear - Hx INP1 P1HI. split; [right; right; left; exists p1, 40; split; [exact INP1| lia] | unfold G_ALLOW_CUST; lia]. }
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & _ & _ & _ & UT4).
  (* [comment removed for export] *)
  pose proof (ib_w2 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp d1 d2 d3 d4 d5 d6 d7 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 lo p2 o2
                ltac:(clear - P20 P2U; unfold USTACK_TOP in *; lia) (STAT4 _ _ (STAT3 _ _ (STAT2 _ _ (STAT1 _ _ ILC ltac:(cbn; lia)) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) ltac:(cbn; lia)) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) UT4
                ltac:(rewrite EU1; exact ST4) HLOS ltac:(rewrite EU1; unfold usp1 in *; lia) ltac:(rewrite EU1; unfold usp1; lia) MI4) as W2.
  rewrite (ret_pc_even SITE_ib_lk2) in W2 by (unfold SITE_ib_lk2; lia).
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (rax & m5 & -> & RAX & MU5 & WM5 & MI5 & ILC5 & ST5) & Hc5'). clear Hc5. rewrite EU1 in ST5. unfold G_IC_INIT_LOCK in MU5, ILC5.
  assert (MU5' : munch ([(0xb9f240, 0xb9f240 + 8)] ++ [(usp1 - 0, usp1)]) m4 m5) by (eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ2 m4 m5 usp1 0 _ ART4 ltac:(rewrite SP2, SP1; unfold usp1; lia) ltac:(unfold usp1, USTACK_TOP in *; lia) MU5' ltac:(intros x Hx; apply client_static_intro; cbn [outside app] in Hx; lia) WM5) as ART5.
  assert (OFF5 : forall Q : Z -> Prop, (forall x, Q x -> ~ (0xb9f240 <= x < 0xb9f240 + 8)) -> agree_on Q m4 m5) by (intros Q HQ a Ha; apply MU5; cbn [outside]; split; [exact (HQ _ Ha)| exact I]).
  assert (STAT5 : forall a cs, rw_cells asegs m4 a cs -> (a + Z.of_nat (cells_size cs) <= 0xb9f240 \/ 0xb9f240 + 8 <= a) -> rw_cells asegs m5 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m4 m5 _ _ X); [| exact WM5]. apply OFF5. clear - H1. intros; lia. }
  pose proof (cl_env_seg _ m4 m5 _ canary CLE4 MU5 ltac:(cl_fp_lia)) as CLE5.
  (* [comment removed for export] *)
  apply (C_CPU Σ2 PMc rax (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 IB_S1) (Z_to_bv 64 p2) d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 IB_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6
           F4 fc4 m5 lo FDO MST eq_refl ART5 MI5).
  { assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2, SP1; exact LOW).
    unfold call_ok. rewrite EU1. split; [exact ST5|]. split; [exact LOW2|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1 in *. clear - HSTK. lia. }
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6) & Hc6'). clear Hc6.
  destruct RS6 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite <- (Z_to_bv_bv_unsigned rax), RAX in Hc6'.
  assert (AG6 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x) -> agree_on Q m5 m6).
  { intros Q HQ a Ha. apply PRES6; [exact (HQ _ Ha)| exact I]. }
  assert (STAT6 : forall a cs, rw_cells asegs m5 a cs -> ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298)) -> rw_cells asegs m6 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m5 m6 _ _ X); [| exact WM6]. apply AG6. intros x Hx. cbv beta in Hx. clear - H1 Hx. right; left; apply client_static_intro; lia. }
  assert (FR6 : rw_cells asegs m6 usp1 [C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m5 m6 _ _ (STAT5 _ _ FR4 ltac:(cbn; clear - HSTK HLOS; unfold usp1; lia))); [| exact WM6]. apply AG6. cbn [cells_size csize Nat.add]. intros x Hx. clear - Hx NUM HLOS HSTK. left. unfold usp1, USTACK_TOP in *. lia. }
  (* [comment removed for export] *)
  assert (ST06 : forall a cs, rw_cells asegs m a cs -> ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298)) ->
            (a + Z.of_nat (cells_size cs) <= 0xb9f220 \/ 0xb9f240 + 8 <= a) -> (a + Z.of_nat (cells_size cs) <= G_ALLOW_CUST \/ G_ALLOW_CUST + 1 <= a) -> rw_cells asegs m6 a cs).
  { intros a cs X H1 H2 H3. apply (STAT6 _ _ (STAT5 _ _ (STAT4 _ _ (STAT3 _ _ (STAT2 _ _ (STAT1 _ _ X ltac:(clear - H1; lia)) H1 H3) ltac:(clear - H2; lia)) H1 H3) ltac:(clear - H2; lia)) H1). }
  pose proof (ST06 _ _ DK ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) as DK6.
  pose proof (ST06 _ _ IK ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) as IK6.
  pose proof (ST06 _ _ NK ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) as NK6.
  pose proof (ST06 _ _ KL ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) as KL6.
  pose proof (ST06 _ _ KJ1 ltac:(cbn; clear - HJ1; lia) ltac:(cbn; clear - HJ1; lia) ltac:(cbn; clear - HJ1; unfold G_ALLOW_CUST; lia)) as KJ16.
  pose proof (ST06 _ _ KJ2 ltac:(cbn; clear - HJ2; lia) ltac:(cbn; clear - HJ2; lia) ltac:(cbn; clear - HJ2; unfold G_ALLOW_CUST; lia)) as KJ26.
  pose proof (ST06 _ _ BI ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) as BI6.
  pose proof (ST06 _ _ BR ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) as BR6.
  assert (PROBE6 : ro_cells asegs m6 (KEYS + 8 * nk) [C8 w]).
  { assert (X : rw_cells asegs m (KEYS + 8 * nk) [C8 w] \/ True) by (right; exact I). clear X.
    apply (ro_cells_agree asegs m m6 _ _ PROBE). cbn [cells_size csize Nat.add]. intros x Hx.
    rewrite (PRES6 x ltac:(right; left; apply client_static_intro; clear - Hx HNK; lia) I).
    rewrite (MU5 x ltac:(cbn [outside]; clear - Hx HNK; split; [lia| exact I])).
    rewrite (PRES4 x ltac:(right; left; apply client_static_intro; clear - Hx HNK; lia) ltac:(cbn [outside]; clear - Hx HNK; unfold G_ALLOW_CUST; split; [lia| exact I])).
    rewrite (MU3 x ltac:(cbn [outside]; clear - Hx HNK; split; [lia| exact I])).
    rewrite (PRES2 x ltac:(right; left; apply client_static_intro; clear - Hx HNK; lia) ltac:(cbn [outside]; clear - Hx HNK; unfold G_ALLOW_CUST; split; [lia| exact I])).
    apply MU1. cbn [outside]. clear - Hx HNK HSTK HLOS. split; [lia| exact I]. }
  pose proof (TSD Σ2 m6 ART6) as TSD6.
  (* [comment removed for export] *)
  pose proof (ib_w3 sp gp x0 x1 x2 (Z_to_bv 64 p2) g1 g2 g3 g4 g5 g6 g7 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 (Z_to_bv 64 SITE_ib_cpu) ra s0 s1 s2 F6 fc6 m6 lo nk j1 j2 sh kold1 kold2 w r0 b0
                DK6 IK6 (proj1 TSD6) NK6 HNK KL6 KJ16 PROBE6 CASE EJ2 KJ26 BI6 BR6 ltac:(fold usp usp1; exact FR6)
                ltac:(fold usp usp1; exact ST6) HLOS ltac:(fold usp; lia) SPH MI6) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & DK7 & IK7 & NK7 & KL7 & KJ17 & KJ27 & BI7 & BR7) & Hc7'). clear Hc7.
  unfold G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET in MU7, IK7, BI7, BR7. fold usp in MU7, ST7.
  (* [comment removed for export] *)
  assert (MU7' : munch ([(DTOR_KEY, DTOR_KEY + 4); (0xb9f260, 0xb9f260 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j1, KEYS + 8 * j1 + 8); (KEYS + 8 * j2, KEYS + 8 * j2 + 8);
                         (0xb9f1c0, 0xb9f1c0 + 1); (0xb9f2e0, 0xb9f2e0 + 4)] ++ [(usp - 160, usp)]) m6 m7).
  { eapply munch_weaken; [| exact MU7]. unfold sub_fp. cbn [outside app]. clear. intros x Hx. tauto. }
  pose proof (cl_seg_ART RT AF Σ2 m6 m7 usp 160 _ ART6 ltac:(rewrite SP2, SP1; lia) ltac:(unfold USTACK_TOP in *; lia) MU7'
                ltac:(intros x Hx; apply client_static_intro; cbn [outside app] in Hx; clear - Hx HJ1 HJ2; lia) WM7) as ART7.
  assert (OUT7 : forall Q : Z -> Prop, (forall x, Q x -> ~ (usp - 160 <= x < usp) /\ ~ (DTOR_KEY <= x < DTOR_KEY + 4) /\ ~ (0xb9f260 <= x < 0xb9f260 + 4) /\ ~ (NEXT_KEY <= x < NEXT_KEY + 12)
                 /\ ~ (KEYS + 8 * j1 <= x < KEYS + 8 * j1 + 8) /\ ~ (KEYS + 8 * j2 <= x < KEYS + 8 * j2 + 8) /\ ~ (0xb9f1c0 <= x < 0xb9f1c0 + 1) /\ ~ (0xb9f2e0 <= x < 0xb9f2e0 + 4)) -> agree_on Q m6 m7).
  { intros Q HQ a Ha. pose proof (HQ _ Ha) as X. clear HQ Ha. apply MU7. cbn [outside]. clear - X. repeat split; try exact I; tauto. }
  assert (INP1' : In (p1, 40) (rt_live RT Σ2)) by (rewrite LV2; right; exact INP1).
  assert (INP2 : In (p2, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 p2 40 ART4 INP2) as (_ & P2LO & _). rewrite SP2, SP1 in P2LO.
  assert (OLC7 : rw_cells asegs m7 0xb9f220 [C8 (Z_to_bv 64 p1)]).
  { apply (rw_cells_agree asegs m6 m7 _ _ (STAT6 _ _ (STAT5 _ _ (STAT4 _ _ OLC3 ltac:(cbn; lia) ltac:(cbn; unfold G_ALLOW_CUST; lia)) ltac:(cbn; lia)) ltac:(cbn; lia))); [| exact WM7].
    apply OUT7. cbn [cells_size csize Nat.add]. intros x Hx. clear - Hx HJ1 HJ2 HSTK HLOS. repeat split; lia. }
  assert (ILC7 : rw_cells asegs m7 0xb9f240 [C8 (Z_to_bv 64 p2)]).
  { apply (rw_cells_agree asegs m6 m7 _ _ (STAT6 _ _ ILC5 ltac:(cbn; lia))); [| exact WM7]. apply OUT7. cbn [cells_size csize Nat.add]. intros x Hx. clear - Hx HJ1 HJ2 HSTK HLOS. repeat split; lia. }
  assert (LIVE67 : forall p cs, In (p, 40) (rt_live RT Σ2) -> 0x10007fff8000 <= p -> p + 40 <= rt_sp0 RT Σ - STACK_WIN -> rw_cells asegs m4 p cs -> Z.of_nat (cells_size cs) <= 40 -> rw_cells asegs m7 p cs).
  { intros p cs Hin Hhi Hlo X Hsz.
    assert (X5 : rw_cells asegs m5 p cs) by (apply (STAT5 _ _ X); clear - Hhi; lia).
    assert (X6 : rw_cells asegs m6 p cs).
    { apply (rw_cells_agree asegs m5 m6 _ _ X5); [| exact WM6]. apply AG6. intros x Hx. cbv beta in Hx. right; right; left. exists p, 40. split; [exact Hin| clear - Hx Hsz; lia]. }
    apply (rw_cells_agree asegs m6 m7 _ _ X6); [| exact WM7]. apply OUT7. intros x Hx. cbv beta in Hx. clear - Hx Hsz Hhi Hlo NUM HJ1 HJ2. unfold STACK_WIN in *. repeat split; lia. }
  pose proof (LIVE67 p1 _ INP1' P1HI P1LO MC14 ltac:(cbn; lia)) as MC17.
  pose proof (LIVE67 p2 _ INP2 P2HI P2LO MC4 ltac:(cbn; lia)) as MC27.
  assert (CLE6 : cl_env m6 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m5 m6 _ _ CLE5). intros a Ha. apply PRES6; [| exact I]. right; left. exact (cl_cell_static _ Ha). }
  assert (CLE7 : cl_env m7 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m6 m7 _ _ CLE6). intros a Ha. apply MU7. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR.
    unfold cl_cell, in_ranges, CL_CELLS in Ha. destruct Ha as (lo' & hi' & Hin & R). cbn in Hin. cbn [outside].
    clear - Hin R CR HJ1 HJ2 NUM HLOS HSTK. unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard, SEGTOP_A, USTACK_TOP, STACK_WIN in *.
    decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try contradiction; repeat split; try exact I; try lia. }
  (* [comment removed for export] *)
  apply Hk. exists Σ2, p1, p2.
  split.
  2:{ split; [rewrite LV2, LV1; reflexivity|]. split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. split; [rewrite CR2, CR1; lia|]. split; [rewrite CG2; exact CG1|].
      repeat split; assumption. }
  apply (ASTA_conseq RT Σ2 PMc _ _ c7 Hc7'). intros ms <-. exists m7.
  split; [exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, y3, y4, y5, y6, F6, fc6; reflexivity|].
  split; [split; [exact ART7|]; split; [exact MI7|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 WM7)))))) | exact ST7]|].
  split.
  { intros a Ha Ho. unfold IB_W, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET in Ho. cbn [outside] in Ho.
    destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & _).
    pose proof (cl_split RT AF Σ m usp 0x220 _ ART0 ltac:(lia) ltac:(lia) Ha) as A8.
    rewrite (MU7 a). 2:{ cbn [outside]. clear - A8 O4 O5 O6 O7 O8 O9 O10. repeat split; try exact I; lia. }
    assert (X1 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV2, LV1; right; right; exact Hy | rewrite FRS2, FRS1; intros y Hy; exact Hy | unfold usp1; lia]. }
    rewrite (PRES6 a X1 I).
    rewrite (MU5 a). 2:{ cbn [outside]. clear - O3. split; [lia| exact I]. }
    assert (X3 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV1; right; exact Hy | rewrite FRS1; intros y Hy; exact Hy | unfold usp1; lia]. }
    rewrite (PRES4 a X3). 2:{ cbn [outside]. clear - O1. split; [lia| exact I]. }
    rewrite (MU3 a). 2:{ cbn [outside]. clear - O2. split; [lia| exact I]. }
    assert (X5 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; exact Hy | intros y Hy; exact Hy | unfold usp1; lia]. }
    rewrite (PRES2 a X5). 2:{ cbn [outside]. clear - O1. split; [lia| exact I]. }
    exact (PR1 a Ha I). }
  split; [exact CLE7|].
  split; [exact OLC7|]. split; [exact ILC7|]. split; [exact MC17|]. split; [exact MC27|].
  split; [exact DK7|]. split; [exact IK7|]. split; [exact NK7|]. split; [exact KL7|]. split; [exact KJ17|]. split; [exact KJ27|]. split; [exact BI7|]. exact BR7.
Qed.
End IBase.
