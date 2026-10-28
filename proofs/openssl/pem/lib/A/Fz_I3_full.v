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
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_atomic Fz_T_once Fz_T_lock Fz_T_local Fz_T_initthread Fz_T_master1 Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_slx Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_loadw Fz_I1_errload Fz_I1_efirst Fz_I1_crypto Fz_I3_shelve Fz_I3_loadstrw Fz_I3_loadstr Fz_I3_ibasew Fz_I3_ibase Fz_I3_fullw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).

Section ICFull.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis C_IB : ibase_stmt RT.
Hypothesis C_LS : loadstr_stmt RT GOBJ.
Hypothesis GO_optsdone : GOBJ G_IC_OPTSDONE 8.

Definition ICF_SITES : list (Z * Z) := IB_SITES ++ LS_SITES.
Definition ICF_CALLS : list (Z * Z) := (ONCE_RET_INIT, e_ibase) :: (ONCE_RET_INIT, e_loadstr) :: IB_CALLS ++ LS_CALLS.
(* [comment removed for export] *)
Definition ICF_W (j1 : Z) : list (Z * Z) :=
  [(G_IC_BASE_ONCE, G_IC_BASE_ONCE + 4); (G_LS_ONCE, G_LS_ONCE + 4); (G_IC_OPTSDONE, G_IC_OPTSDONE + 8); (TP_A + -96, TP_A + -88)] ++ IB_W j1 (j1 + 1) ++ LS_W (j1 + 2).

(* [comment removed for export] *)
Definition init_crypto_full_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (lb : byte) (canary : word) (nk j1 : Z) (w e sh kold oldcb lk0 h0 f0 r0 r1 o1 o2 kold1 kold2 : word) (ib u b0 : byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 OPT_LOAD_STRINGS ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x430 <= bv_unsigned sp ->
  cg_has (rt_cg RT Σ) ICF_SITES ICF_CALLS ->
  (length (rt_frames RT Σ) + 2 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4329 < LIVE_MAX -> 41 <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) -> cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 z64] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 z64] -> rw_cells asegs m G_IC_BASE_RET [C4 r0] ->
  rw_cells asegs m G_LS_ONCE [C4 z64] -> rw_cells asegs m G_LS_RET [C4 r1] ->
  rw_cells asegs m G_IC_OPTS_LOCK [C8 o1] -> rw_cells asegs m G_IC_INIT_LOCK [C8 o2] ->
  rw_cells asegs m DTOR_KEY [C4 kold1] -> rw_cells asegs m G_IC_IICL_KEY [C4 kold2] -> rw_cells asegs m G_IC_BASE_INITED [C1 b0] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  ro_cells asegs m (KEYS + 8 * nk) [C8 w] -> ((j1 = nk /\ w = z64) \/ (j1 = nk + 1 /\ bv_unsigned w <> 0)) -> j1 + 2 < 128 ->
  rw_cells asegs m (KEYS + 8 * j1) [C8 z64] -> rw_cells asegs m (KEYS + 8 * (j1 + 1)) [C8 z64] -> rw_cells asegs m (KEYS + 8 * (j1 + 2)) [C8 z64] ->
  rw_cells asegs m ERRNO_A [C4 e] -> rw_cells asegs m MK_ONCE [C4 z64] -> rw_cells asegs m MK_INIT [C1 ib] -> rw_cells asegs m MK_KEY [C4 kold] ->
  rw_cells asegs m (TSD_MAIN + 8 * (j1 + 2)) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  rw_cells asegs m G_ERR_ONCE [C4 z64] -> rw_cells asegs m G_ERR_LOCK [C8 lk0] -> rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_init_crypto m)))
    (fun c => exists (Σ' : rts RT) (p1 p2 MK SA P pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' u' : byte) (e' top' : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (ICF_W j1) m m'
           /\ cl_env m' lb' canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)]
           /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' G_LS_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_LS_RET [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' G_IC_OPTS_LOCK [C8 (Z_to_bv 64 p1)] /\ rw_cells asegs m' G_IC_INIT_LOCK [C8 (Z_to_bv 64 p2)]
           /\ rw_cells asegs m' p1 (mutex_cells z64 z64) /\ rw_cells asegs m' p2 (mutex_cells z64 z64)
           /\ rw_cells asegs m' DTOR_KEY [C4 (Z_to_bv 64 j1)] /\ rw_cells asegs m' G_IC_IICL_KEY [C4 (Z_to_bv 64 (j1 + 1))] /\ rw_cells asegs m' G_IC_BASE_INITED [C1 (Z_to_bv 8 1)]
           /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 (j1 + 2))] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
           /\ rw_cells asegs m' (KEYS + 8 * j1) [C8 (Z_to_bv 64 DTOR_FN)] /\ rw_cells asegs m' (KEYS + 8 * (j1 + 1)) [C8 (Z_to_bv 64 NODTOR)] /\ rw_cells asegs m' (KEYS + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK_CLEAN)]
           /\ rw_cells asegs m' ERRNO_A [C4 e']
           /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 (j1 + 2))]
           /\ rw_cells asegs m' (TSD_MAIN + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK)] /\ rw_cells asegs m' (TP_A + -150) [C1 u'] /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
           /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 top' (Z_to_bv 64 0) (Z_to_bv 64 P)) /\ bv_unsigned top' = 0
           /\ rw_cells asegs m' P [C8 z64; CB 120 (zeros 120)]
           /\ err_statics m' pk lh /\ rw_cells asegs m' pk (mutex_cells z64 z64) /\ lh_repE GOBJ m' L' lh B g' bks') c
       /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ)
       /\ Z.of_nat (length L') <= 4320 /\ 0 <= g_items g' <= 4318
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 41 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < p1 /\ p1 mod 16 = 0 /\ p1 + 40 < USTACK_TOP /\ 0 < p2 /\ p2 mod 16 = 0 /\ p2 + 40 < USTACK_TOP
       /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP
       /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP).

Theorem init_crypto_full_cps : init_crypto_full_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lb canary nk j1 w e sh kold oldcb lk0 h0 f0 r0 r1 o1 o2 kold1 kold2 ib u b0
    FDO MST -> -> ART0 MI0 CALL HSTK CGH Hfr Hlen Hcr POS CLE STP OD ONCE BRET LSO LSR OLC ILC DK IK BI NK HNK KL PROBE CASE HJ K0 K1 K2 ERC OC IC KC SLOT UC CBC ONC LKC LHC FLC.
  assert (HJ0 : 0 <= j1) by (clear - CASE HNK; lia).
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 0x430 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  set (usp1 := usp + -96 - pad).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  set (usp2 := usp1 + -128).
  assert (EU2 : bv_unsigned (Z_to_bv 64 usp2) = usp2) by (apply unsigned_lit; unfold usp2, usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLOS : 0x10007fff8000 <= lo) by exact (proj1 (proj2 NUM)).
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET, G_LS_ONCE, G_LS_RET, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED in *.
  unfold G_ERR_ONCE in ONC. unfold G_ERR_LOCK in LKC. unfold G_ERR_HASH in LHC. unfold G_ERR_FLAG in FLC.
  (* [comment removed for export] *)
  pose proof (icb_s0_walk ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad OPT_LOAD_STRINGS
                HP HPM ltac:(unfold OPT_LOAD_STRINGS; lia) ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_icb_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 OPT_LOAD_STRINGS) a1 s5 s6 s7 (Z_to_bv 64 0x7fff8000) s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_icb_smalloc) in Hc2' by (unfold SITE_icb_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & FAP).
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2, FAP. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG. rewrite LV1 in FAP.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (WM02 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
  (* [comment removed for export] *)
  assert (PR2 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros ? X; exact X| intros ? X; exact X| unfold usp1; lia])). exact (PR1 a Ha I). }
  assert (STAT2 : forall a cs, rw_cells asegs m a cs ->
            ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298)
             \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0)) -> rw_cells asegs m2 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m m2 _ _ H); [| exact WM02]. intros x Hx. cbv beta in Hx. apply PR2. right; left. apply client_static_intro; clear - H1 Hx; lia. }

  pose proof (afp_acc_global RT GOBJ AFP Σ1 m2 _ _ 0xb9f2a0 8 ART2 GO_optsdone ltac:(unfold G_IC_OPTSDONE; lia) ltac:(unfold G_IC_OPTSDONE; lia)) as ACCO2.
  pose proof (cl_env_pres _ _ _ m m2 lb canary CLE PR2) as CLE2.
  pose proof (cl_env_ssp m2 lb canary UT2 CLE2) as SSP2.
  (* [comment removed for export] *)
  pose proof (if_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 a1 s5 s6 s7 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F2 fc2 m2 f lo pad fj sj oldcb canary HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia)
                ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH eq_refl UT2 SHC2 FR2 GAP2 ST2 FB2 SB2
                (STAT2 _ _ STP ltac:(cbn; lia)) (STAT2 _ _ OD ltac:(cbn; lia)) ACCO2 (STAT2 _ _ ONCE ltac:(cbn; lia)) SSP2 (STAT2 _ _ CBC ltac:(cbn; lia)) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & v3 & j8 & fr8 & fr16 & junk & m3 & -> & MU3 & WM3 & MI3 & FR3 & FB3 & TMP3 & FB43 & SB3 & GAP3 & ST3 & ODR3 & SSP3 & ONCE3 & CBC3 & OF3 & PO3 & FRR3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, ST3, OF3, PO3, FRR3, CBC3, Hc3'. fold usp1 in GAP3, ST3, OF3, PO3, FRR3, CBC3, Hc3'. fold usp2 in ST3, OF3, CBC3, Hc3'.
  unfold G_IC_BASE_ONCE, G_IC_OPTSDONE in *.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  pose proof (div8_facts f) as Q1.
  (* [comment removed for export] *)
  assert (FKEEP : forall (ma mb : mem) W, ART RT Σ1 ma -> munch W ma mb -> wmono asegs ma mb ->
            (forall x, ~ outside W x -> (f <= x < f + 56) \/ (shad f <= x < shad f + 8) \/ (usp - 0x430 <= x < usp - 88)
                                     \/ (0xb9f2c0 <= x < 0xb9f2c4) \/ (0xb9f300 <= x < 0xb9f304) \/ (0xb9f2a0 <= x < 0xb9f2a8) \/ (TP_A + -96 <= x < TP_A + -88)) ->
            ART RT Σ1 mb /\ (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) ->
                               ~ (0xb9f2c0 <= bv_unsigned a < 0xb9f2c4) -> ~ (0xb9f300 <= bv_unsigned a < 0xb9f304) -> ~ (0xb9f2a0 <= bv_unsigned a < 0xb9f2a8) ->
                               ~ (TP_A + -96 <= bv_unsigned a < TP_A + -88) -> mb a = ma a)).
  { intros ma mb W HAx MUx WMx HW. split.
    - apply (af_frame RT AF Σ1 ma mb (usp - 0x430) HAx ltac:(rewrite SP1; lia)); [| exact WMx].
      intros a Ha. apply MUx. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso. apply Ha.
      destruct (HW _ O) as [X|[X|[X|[X|[X|[X|X]]]]]].
      + apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
      + apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; lia].
      + apply acl_stack. unfold USTACK_TOP in *. lia.
      + apply acl_static. apply client_static_intro. lia.
      + apply acl_static. apply client_static_intro. lia.
      + apply acl_static. apply client_static_intro. lia.
      + apply acl_static. apply client_static_intro. lia.
    - intros a Ha N1 N2 N3 N4. apply MUx. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso.
      destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (M1 & M2). change (fs_size 0) with 64 in M1, M2. rewrite SHF in M2.
      pose proof (cl_split RT AF Σ m usp 0x430 _ ART0 ltac:(lia) ltac:(lia) Ha) as M4.
      destruct (HW _ O) as [X|[X|[X|[X|[X|[X|X]]]]]]; lia. }
  lazymatch type of MU3 with munch ?W _ _ => assert (HW3 : forall x, ~ outside W x -> (f <= x < f + 56) \/ (shad f <= x < shad f + 8) \/ (usp - 0x430 <= x < usp - 88)
                                     \/ (0xb9f2c0 <= x < 0xb9f2c4) \/ (0xb9f300 <= x < 0xb9f304) \/ (0xb9f2a0 <= x < 0xb9f2a8) \/ (TP_A + -96 <= x < TP_A + -88))
    by (intros x Hx; cbn [outside] in Hx; unfold shad, SHB, usp2, usp1 in *; clear - Hx HP; lia) end.
  destruct (FKEEP m2 m3 _ ART2 MU3 WM3 HW3) as [ART3 PR3]. clear HW3.
  assert (WM03 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM02 WM3).
  assert (PR03 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) ->
                   ~ (0xb9f2c0 <= bv_unsigned a < 0xb9f2c4) -> ~ (0xb9f300 <= bv_unsigned a < 0xb9f304) -> ~ (0xb9f2a0 <= bv_unsigned a < 0xb9f2a8) ->
                   ~ (TP_A + -96 <= bv_unsigned a < TP_A + -88) -> m3 a = m a) by (intros a Ha N1 N2 N3 N4; rewrite (PR3 a Ha N1 N2 N3 N4); exact (PR2 a Ha)).
  assert (STAT3 : forall a cs, rw_cells asegs m a cs ->
            ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f2a0) \/ (0xb9f2c4 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f300)
             \/ (0xb9f304 <= a /\ a + Z.of_nat (cells_size cs) <= TP_A + -96) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0))
            -> rw_cells asegs m3 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m m3 _ _ H); [| exact WM03]. intros x Hx. cbv beta in Hx. apply PR03; [right; left; apply client_static_intro|..]; clear - H1 Hx; lia. }
  assert (CLE3 : cl_env m3 lb canary).
  { apply (cl_env_agree m m3 _ _ CLE). intros a Ha. pose proof (cl_cell_static _ Ha) as CS. apply PR03; [right; left; exact CS|..];
    unfold cl_cell, in_ranges, CL_CELLS in Ha; destruct Ha as (lo' & hi' & Hin & R); cbn in Hin;
    unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in *;
    decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try contradiction; clear - R; lia. }

  (* [comment removed for export] *)
  rewrite <- CG1 in CGH.
  apply (C_IB Σ1 PMc (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 usp2) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 0xb9f2c0) (Z_to_bv 64 e_ibase) v0 v1 v2 v3 b4 b5 b6 b7
           (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 u3 u4 u5 u6
           F2 fc2 m3 lo [] lb canary nk j1 (j1 + 1) o1 o2 sh kold1 kold2 w r0 b0 FDO MST eq_refl ART3 MI3).
  { assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    unfold call_ok. rewrite EU2. split; [exact ST3|]. split; [exact LOW1|]. split; [unfold usp2, usp1, RT_STACK in *; lia|]. split; [unfold usp2, usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP. unfold usp2, usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU2. unfold usp2, usp1, RT_STACK in *. clear - HSTK HP. lia. }
  { rewrite (unsigned_lit ONCE_RET_INIT) by (unfold ONCE_RET_INIT; lia). split; [| exact I]. apply (proj2 CGH). left. reflexivity. }
  { cbn [uw_chain]. left. rewrite (unsigned_lit 0xb9f2c0), EU2 by lia. unfold usp2, usp1, RT_STACK in *. lia. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS1. cbn [length]. lia. }
  { rewrite LV1. lia. }
  { rewrite CR1. lia. }
  { exact CLE3. }
  { exact (STAT3 _ _ OLC ltac:(cbn; lia)). }
  { exact (STAT3 _ _ ILC ltac:(cbn; lia)). }
  { exact (STAT3 _ _ DK ltac:(cbn; lia)). }
  { exact (STAT3 _ _ IK ltac:(cbn; lia)). }
  { exact (STAT3 _ _ NK ltac:(cbn; lia)). }
  { exact HNK. }
  { exact (STAT3 _ _ KL ltac:(cbn; lia)). }
  { exact (STAT3 _ _ K0 ltac:(cbn; lia)). }
  { apply (ro_cells_agree asegs m m3 _ _ PROBE). cbn [cells_size csize Nat.add]. intros x Hx. apply PR03; [right; left; apply client_static_intro|..]; clear - Hx HNK; lia. }
  { destruct CASE as [[E1 E2]|[E1 E2]]; [left; split; [exact E1| exact E2] | right; split; [rewrite Z.mod_small by lia; exact E1| exact E2]]. }
  { rewrite Z.mod_small by lia. reflexivity. }
  { exact (STAT3 _ _ K1 ltac:(cbn; lia)). }
  { exact (STAT3 _ _ BI ltac:(cbn; lia)). }
  { exact (STAT3 _ _ BRET ltac:(cbn; lia)). }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & p1 & p2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2 & P10 & P116 & P1U & P20 & P216 & P2U).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & OLC4 & ILC4 & MC14 & MC24 & DK4 & IK4 & NK4 & KL4 & K04 & K14 & BI4 & BRET4) & Hc4'). clear Hc4.
  destruct RS4 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even ONCE_RET_INIT) in Hc4' by (unfold ONCE_RET_INIT; lia).

  (* [comment removed for export] *)
  assert (AG34 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp2 x /\ outside (IB_W j1 (j1 + 1)) x) -> agree_on Q m3 m4).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). exact (PRES4 a X1 X2). }
  assert (STAT34 : forall a cs, rw_cells asegs m3 a cs ->
            ((0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f1c0) \/ (0xb9f1c1 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f220) \/ (0xb9f268 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f2e0)
             \/ (0xb9f2e4 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f7c0) \/ (0xb9f7c1 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= KEYS + 8 * j1)
             \/ (KEYS + 8 * j1 + 16 <= a /\ a + Z.of_nat (cells_size cs) <= NEXT_KEY) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0)) -> rw_cells asegs m4 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG34. intros x Hx. cbv beta in Hx. clear - H1 Hx HJ HJ0. split; [right; left; apply client_static_intro; lia|].
    unfold IB_W, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET. cbn [outside]. repeat split; try exact I; lia. }
  assert (STK34 : forall a cs, rw_cells asegs m3 a cs -> usp2 <= a -> a + Z.of_nat (cells_size cs) <= usp -> rw_cells asegs m4 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG34. intros x Hx. cbv beta in Hx. clear - H1 H2 Hx NUM HSTK HP HJ HJ0. split; [left; unfold usp2, usp1, USTACK_TOP in *; lia|].
    unfold IB_W, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET. cbn [outside]. unfold usp2, usp1, USTACK_TOP, RT_STACK in *. repeat split; try exact I; lia. }
  pose proof (STAT34 _ _ ONCE3 ltac:(cbn; lia)) as ONCE4. pose proof (STAT34 _ _ CBC3 ltac:(cbn; lia)) as CBC4.
  assert (LSO3 : rw_cells asegs m3 0xb9f300 [C4 z64]).
  { apply (rw_cells_agree asegs m2 m3 _ _ (STAT2 _ _ LSO ltac:(cbn; lia))); [| exact WM3]. apply (agree_of_munch _ m2 m3 _ MU3). cbn [cells_size csize Nat.add outside Z.of_nat Pos.of_succ_nat Pos.succ]. intros x Hx.
    unfold shad, SHB, usp2, usp1, usp, RT_STACK in *. clear - Hx F0 FIMG HLOS HSTK HP. repeat split; try exact I; lia. }
  pose proof (STAT34 _ _ LSO3 ltac:(cbn; lia)) as LSO4.
  pose proof (STK34 _ _ OF3 ltac:(lia) ltac:(cbn [cells_size csize Nat.add once_full_cells]; unfold usp2, usp1; lia)) as OF4.
  pose proof (STK34 _ _ PO3 ltac:(unfold usp2, usp1; lia) ltac:(cbn; unfold usp2, usp1; lia)) as PO4.
  pose proof (STK34 _ _ FRR3 ltac:(unfold usp2, usp1; lia) ltac:(cbn; unfold usp2, usp1; lia)) as FRR4.
  pose proof (STK34 _ _ FR3 ltac:(unfold usp2, usp1; lia) ltac:(cbn; unfold usp2, usp1; lia)) as FR4.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (cl_env_ssp m4 _ canary UT4 CLE4) as SSP4.
  (* [comment removed for export] *)
  pose proof (if_w2 sp gp (Z_to_bv 64 TP_A) w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 a1 s6 s10 s11 w3 w4 w5 w6 F4 fc4 m4 f lo pad junk oldcb canary (Z_to_bv 64 usp2)
                HP F0 ltac:(lia) ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH eq_refl UT4 ONCE4 SSP4 CBC4) as W2.
  fold usp usp1 usp2 in W2.
  specialize (W2 OF4 PO4 FRR4 ST4 BRET4 LSO4 MI4).
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (x0 & x1 & x2 & x3 & junk2 & m5 & -> & MU5 & WM5 & MI5 & ST5 & SSP5 & ONCE5 & LSO5 & CBC5 & OF5 & PO5 & FRR5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, CBC5, OF5, PO5, FRR5, Hc5'. fold usp1 in MU5, ST5, CBC5, OF5, PO5, FRR5, Hc5'. fold usp2 in ST5, CBC5, OF5, Hc5'.

  (* [comment removed for export] *)
  unfold G_IC_BASE_ONCE, G_LS_ONCE in *.
  assert (OUT5 : forall Q : Z -> Prop, (forall x, Q x -> ~ (usp1 - 160 <= x < usp1) /\ ~ (0xb9f2c0 <= x < 0xb9f2c4) /\ ~ (0xb9f300 <= x < 0xb9f304) /\ ~ (TP_A + -96 <= x < TP_A + -88)) -> agree_on Q m4 m5).
  { intros Q HQ a Ha. apply MU5. cbn [outside]. destruct (HQ _ Ha) as (X1 & X2 & X3 & X4). unfold usp1 in *. repeat split; try exact I; lia. }
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 (usp1 - 160) ART4 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. repeat split; try exact I; intros Hin; apply Ha.
    - left. unfold usp1, USTACK_TOP in *. lia.
    - right; left. apply client_static_intro. lia.
    - right; left. apply client_static_intro. lia.
    - right; left. apply client_static_intro. lia. }
  assert (STAT45 : forall a cs, rw_cells asegs m4 a cs ->
            ((0x500000 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f2c0) \/ (0xb9f2c4 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f300) \/ (0xb9f304 <= a /\ a + Z.of_nat (cells_size cs) <= TP_A + -96)
             \/ (TP_A + -88 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0)) -> rw_cells asegs m5 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m4 m5 _ _ X); [| exact WM5]. apply OUT5. intros x Hx. cbv beta in Hx. clear - H1 Hx HSTK HLOS HP. unfold usp1, RT_STACK in *. repeat split; lia. }
  assert (CLE5 : cl_env m5 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m4 m5 _ canary CLE4 MU5); cl_fp_lia).
  assert (OD3 : rw_cells asegs m3 0xb9f2a0 [C8 z64]).
  { apply (rw_cells_agree asegs m2 m3 _ _ (STAT2 _ _ OD ltac:(cbn; lia))); [| exact WM3]. apply (agree_of_munch _ m2 m3 _ MU3). cbn [cells_size csize Nat.add outside Z.of_nat Pos.of_succ_nat Pos.succ]. intros x Hx.
    unfold shad, SHB, usp2, usp1, usp, RT_STACK in *. clear - Hx F0 FIMG HLOS HSTK HP. repeat split; try exact I; lia. }
  pose proof (STAT45 _ _ (STAT34 _ _ OD3 ltac:(cbn; lia)) ltac:(cbn; lia)) as OD5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ STP ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as STP5.
  unfold G_IC_BASE_RET, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED in *.
  pose proof (STAT45 _ _ BRET4 ltac:(cbn; lia)) as BRET5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ ERC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as ERC5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ OC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as OC5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ IC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as IC5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ KC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as KC5.
  pose proof (STAT45 _ _ NK4 ltac:(cbn; lia)) as NK5.
  pose proof (STAT45 _ _ KL4 ltac:(cbn; lia)) as KL5.
  pose proof (STAT45 _ _ K14 ltac:(cbn; lia)) as K15.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ K2 ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as K25.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ SLOT ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as SLOT5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ UC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as UC5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ ONC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as ONC5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ LKC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as LKC5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ LHC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as LHC5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ FLC ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as FLC5.
  pose proof (STAT45 _ _ (STAT34 _ _ (STAT3 _ _ LSR ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as LSR5.
  rewrite <- CG2 in CGH.
  (* [comment removed for export] *)
  apply (C_LS Σ2 PMc (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 usp2) gp (Z_to_bv 64 TP_A) w0 w1 w2 (Z_to_bv 64 0xb9f300) (Z_to_bv 64 e_loadstr) x0 x1 x2 x3 d4 d5 d6 d7
           (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 w3 w4 w5 w6
           F4 fc4 m5 lo [] (Z_to_bv 8 1) canary (j1 + 1) (j1 + 2) e z64 sh kold (Z_to_bv 64 NODTOR) (Z_to_bv 64 usp2) lk0 h0 f0 r1 ib u FDO MST eq_refl ART5 MI5).
  { assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2, SP1; exact LOW).
    unfold call_ok. rewrite EU2. split; [exact ST5|]. split; [exact LOW2|]. split; [unfold usp2, usp1, RT_STACK in *; lia|]. split; [unfold usp2, usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP. unfold usp2, usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU2. unfold usp2, usp1, RT_STACK in *. clear - HSTK HP. lia. }
  { rewrite (unsigned_lit ONCE_RET_INIT) by (unfold ONCE_RET_INIT; lia). split; [| exact I]. apply (proj2 CGH). right; left. reflexivity. }
  { cbn [uw_chain]. left. rewrite (unsigned_lit 0xb9f300), EU2 by lia. unfold usp2, usp1, RT_STACK in *. lia. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS2, FRS1. cbn [length]. lia. }
  { rewrite LV2, LV1. cbn [length]. lia. }
  { rewrite CR2, CR1. lia. }
  { rewrite LV2, LV1. constructor; [cbn; lia|]. constructor; [cbn; lia|]. exact POS. }
  { exact CLE5. }
  { exact STP5. } { exact OD5. } { exact ONCE5. } { exact BRET5. }
  { exact ERC5. } { exact OC5. } { exact IC5. } { exact KC5. }
  { exact NK5. } { clear - HJ HJ0; lia. } { exact KL5. }
  { exact K25. } { exact (proj1 K15). }
  { right. split; [rewrite Z.mod_small by (clear - HJ HJ0; lia); clear; lia|]. rewrite (unsigned_lit NODTOR) by lia. lia. }
  { clear - HJ0; lia. }
  { exact SLOT5. } { exact UC5. } { exact CBC5. }
  { exact ONC5. } { exact LKC5. } { exact LHC5. } { exact FLC5. }
  { exact LSR5. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & MK & SA & P & pk & lh & B & L' & g' & bks' & lb' & u' & e' & top' & v & Hc6 & PERM3 & LL3 & IT3 & FRS3 & SP3 & CR3 & CG3
                        & MK0 & MK16 & MKU & SA0 & SA16 & SAU & P0 & P16 & PU & PK0 & PK16 & PKU).
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & CLE6 & STP6 & OD6 & ONCE6 & BRET6 & ERC6 & OC6 & IC6 & KC6 & NK6 & KL6 & K26 & CBC6 & SLOT6 & UC6
                        & MKC6 & SAC6 & TOP6 & PC6 & STC6 & MC6 & REPE6 & LSR6) & Hc6'). clear Hc6.
  destruct RS6 as (y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & F6 & fc6 & ->).
  rewrite EU2 in ST6, PRES6. rewrite (ret_pc_even ONCE_RET_INIT) in Hc6' by (unfold ONCE_RET_INIT; lia).

  (* [comment removed for export] *)
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET, G_LS_RET in STP6, OD6, ONCE6, BRET6, LSR6.
  assert (FRIN4 : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  assert (AG56 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp2 x /\ outside (LS_W (j1 + 2)) x) -> agree_on Q m5 m6).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). exact (PRES6 a X1 X2). }
  assert (STAT56 : forall a cs, rw_cells asegs m5 a cs ->
            ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f320) \/ (0xb9f324 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f500)
             \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= KEYS + 8 * j1 + 16)) -> rw_cells asegs m6 a cs).
  { intros a cs X H1. apply (rw_cells_agree_nw asegs m5 m6 _ _ X). apply AG56. intros x Hx. cbv beta in Hx. clear - H1 Hx HJ HJ0. split; [right; left; apply client_static_intro; lia|].
    unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. repeat split; try exact I; lia. }
  assert (STK56 : forall a cs, rw_cells asegs m5 a cs -> usp2 <= a -> a + Z.of_nat (cells_size cs) <= usp -> rw_cells asegs m6 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree_nw asegs m5 m6 _ _ X). apply AG56. intros x Hx. cbv beta in Hx. clear - H1 H2 Hx NUM HSTK HP HJ HJ0. split; [left; unfold usp2, usp1, USTACK_TOP in *; lia|].
    unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. unfold usp2, usp1, USTACK_TOP, RT_STACK in *. repeat split; try exact I; lia. }
  pose proof (STAT56 _ _ LSO5 ltac:(cbn; lia)) as LSO6.
  pose proof (STAT56 _ _ (STAT45 _ _ OLC4 ltac:(cbn; lia)) ltac:(cbn; lia)) as OLC6.
  pose proof (STAT56 _ _ (STAT45 _ _ ILC4 ltac:(cbn; lia)) ltac:(cbn; lia)) as ILC6.
  pose proof (STAT56 _ _ (STAT45 _ _ DK4 ltac:(cbn; lia)) ltac:(cbn; lia)) as DK6.
  pose proof (STAT56 _ _ (STAT45 _ _ IK4 ltac:(cbn; lia)) ltac:(cbn; lia)) as IK6.
  pose proof (STAT56 _ _ (STAT45 _ _ BI4 ltac:(cbn; lia)) ltac:(cbn; lia)) as BI6.
  pose proof (STAT56 _ _ (STAT45 _ _ K04 ltac:(cbn; lia)) ltac:(cbn; lia)) as K06.
  pose proof (STAT56 _ _ K15 ltac:(cbn; lia)) as K16.
  pose proof (STK56 _ _ OF5 ltac:(lia) ltac:(cbn [cells_size csize Nat.add once_full_cells]; unfold usp2, usp1; lia)) as OF6.
  pose proof (STK56 _ _ PO5 ltac:(unfold usp2, usp1; lia) ltac:(cbn; unfold usp2, usp1; lia)) as PO6.
  pose proof (STK56 _ _ FRR5 ltac:(unfold usp2, usp1; lia) ltac:(cbn; unfold usp2, usp1; lia)) as FRR6.
  assert (FR5 : rw_cells asegs m5 (usp + -96) [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5 _ _ FR4); [| exact WM5]. apply OUT5. cbn [cells_size csize Nat.add]. intros x Hx. unfold usp1, usp in *. clear - Hx HSTK HLOS HP. unfold RT_STACK in *. repeat split; lia. }
  pose proof (STK56 _ _ FR5 ltac:(unfold usp2, usp1; lia) ltac:(cbn; lia)) as FR6.

  (* [comment removed for export] *)
  assert (FK36 : forall a : word, (f <= bv_unsigned a < f + 56) \/ (shad f <= bv_unsigned a < shad f + 8) -> m6 a = m3 a).
  { intros a Ha.
    assert (X1 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp2 (bv_unsigned a)).
    { destruct Ha as [Ha|Ha]; [apply (acl_frame _ _ _ f 0%nat); [exact FRIN4| change (fs_size 0) with 64; lia] | apply (acl_fshadow _ _ _ f 0%nat); [exact FRIN4| change (fs_size 0) with 64; rewrite SHF; lia]]. }
    assert (X3 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp2 (bv_unsigned a)).
    { destruct Ha as [Ha|Ha]; [apply (acl_frame _ _ _ f 0%nat); [exact INF| change (fs_size 0) with 64; lia] | apply (acl_fshadow _ _ _ f 0%nat); [exact INF| change (fs_size 0) with 64; rewrite SHF; lia]]. }
    unfold shad, SHB in Ha.
    rewrite (PRES6 a X1). 2:{ unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET; cbn [outside]; clear - Ha F0 FIMG HJ HJ0; repeat split; try exact I; lia. }
    rewrite (MU5 a). 2:{ cbn [outside]. unfold usp1, usp, RT_STACK in *. clear - Ha F0 FIMG FLO HLOS HSTK HP LOW. repeat split; try exact I; lia. }
    apply (PRES4 a X3). unfold IB_W, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET; cbn [outside]; clear - Ha F0 FIMG HJ HJ0; repeat split; try exact I; lia. }
  assert (TMP6 : rw_cells asegs m6 (f + 32) [C8 z64]).
  { apply (rw_cells_agree_nw asegs m3 m6 _ _ TMP3). cbn [cells_size csize Nat.add]. intros x Hx. apply FK36. left. lia. }
  eassert (SB6 : rw_cells asegs m6 (f / 8 + 2147450880) _).
  { apply (rw_cells_agree_nw asegs m3 m6 _ _ SB3). cbn [cells_size csize Nat.add]. intros x Hx. apply FK36. right. unfold shad, SHB. lia. }
  assert (FM6 : rw_cells asegs m6 f [C8 (Z_to_bv 64 ICB_MAGIC)]).
  { apply (rw_cells_agree_nw asegs m3 m6 _ _ (rw_cells_head m3 _ _ _ FB3)). cbn [cells_size csize Nat.add]. intros x Hx. apply FK36. left. lia. }
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  pose proof (cl_env_ssp m6 _ canary UT6 CLE6) as SSP6.
  pose proof (afp_acc_global RT GOBJ AFP Σ3 m6 _ _ 0xb9f2a0 8 ART6 GO_optsdone ltac:(lia) ltac:(lia)) as ACCO6.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m3 p1 40) as P1H0.
  (* [comment removed for export] *)
  pose proof (if_w3 sp gp (Z_to_bv 64 TP_A) y0 y1 y2 v g1 g2 g3 g4 g5 g6 g7 a1 s10 s11 y3 y4 y5 y6 F6 fc6 m6 f lo pad p1 junk2 oldcb canary (Z_to_bv 64 usp2) (Z_to_bv 64 ICB_MAGIC)
                (Z_to_bv 8 (-13)) (Z_to_bv 8 (-13)) (Z_to_bv 8 (-13))
                HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH eq_refl UT6 SHC6 LSO6 SSP6 CBC6) as W3.
  fold usp usp1 usp2 in W3.
  specialize (W3 OF6 PO6 FRR6 ST6 LSR6 OLC6 ltac:(clear - P10 P1U; unfold USTACK_TOP in *; lia) OD6 ACCO6 TMP6 SB6 FM6 MI6).
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (z0 & z1 & z2 & z3 & z4 & m7 & -> & MU7 & WM7 & MI7 & ST7 & SSP7 & LSO7 & CBC7 & OD7 & TMP7 & FM7 & SB7) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, Hc7'. fold usp1 in MU7, ST7, Hc7'.

  (* [comment removed for export] *)
  unfold G_LS_ONCE, G_IC_OPTSDONE in MU7, LSO7, OD7.
  assert (OUT7 : forall Q : Z -> Prop, (forall x, Q x -> ~ (usp1 - 160 <= x < usp1) /\ ~ (0xb9f300 <= x < 0xb9f304) /\ ~ (TP_A + -96 <= x < TP_A + -88) /\ ~ (0xb9f2a0 <= x < 0xb9f2a8)
                                                  /\ ~ (f <= x < f + 8) /\ ~ (f + 32 <= x < f + 40) /\ ~ (shad f <= x < shad f + 8)) -> agree_on Q m6 m7).
  { intros Q HQ a Ha. apply MU7. cbn [outside]. destruct (HQ _ Ha) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). unfold shad, SHB, usp1 in *. repeat split; try exact I; lia. }
  assert (FRIN6 : In (f, 0%nat) (rt_frames RT Σ3)) by (rewrite FRS3; exact FRIN4).
  assert (ART7 : ART RT Σ3 m7).
  { apply (af_frame RT AF Σ3 m6 m7 (usp1 - 160) ART6 ltac:(rewrite SP3, SP2, SP1; unfold usp1; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. repeat split; try exact I; intros Hin; apply Ha.
    - left. unfold usp1, USTACK_TOP in *. lia.
    - right; left. apply client_static_intro. lia.
    - right; left. apply client_static_intro. lia.
    - right; left. apply client_static_intro. lia.
    - apply (acl_frame _ _ _ f 0%nat); [exact FRIN6| change (fs_size 0) with 64; lia].
    - apply (acl_frame _ _ _ f 0%nat); [exact FRIN6| change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact FRIN6| change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB in *; lia]. }
  (* [comment removed for export] *)
  assert (GAP4 : stk asegs m4 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m3 m4 _ _ GAP3). apply AG34. intros x Hx. cbv beta in Hx. clear - Hx NUM HSTK HLOS HP HJ HJ0. split; [left; unfold usp2, usp1, USTACK_TOP in *; lia|].
    unfold IB_W, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET. cbn [outside]. unfold usp2, usp1, RT_STACK in *. repeat split; try exact I; lia. }
  assert (GAP5 : stk asegs m5 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m4 m5 _ _ GAP4). apply OUT5. intros x Hx. cbv beta in Hx. clear - Hx HSTK HLOS HP. unfold usp1, RT_STACK in *. repeat split; lia. }
  assert (GAP6 : stk asegs m6 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m5 m6 _ _ GAP5). apply AG56. intros x Hx. cbv beta in Hx. clear - Hx NUM HSTK HLOS HP HJ HJ0. split; [left; unfold usp2, usp1, USTACK_TOP in *; lia|].
    unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. unfold usp2, usp1, RT_STACK in *. repeat split; try exact I; lia. }
  assert (GAP7 : stk asegs m7 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m6 m7 _ _ GAP6). apply OUT7. intros x Hx. cbv beta in Hx. clear - Hx HSTK HLOS HP F0 FLO LOW FIMG. unfold shad, SHB, usp1, RT_STACK in *. repeat split; lia. }
  eassert (FR7 : rw_cells asegs m7 (usp + -96) _).
  { apply (rw_cells_agree asegs m6 m7 _ _ FR6); [| exact WM7]. apply OUT7. cbn [cells_size csize Nat.add]. intros x Hx. clear - Hx HSTK HLOS HP F0 FLO LOW FIMG. unfold shad, SHB, usp1, usp, RT_STACK in *. repeat split; lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ3 m7 f 0%nat (rt_frames RT Σ) ART7 ltac:(rewrite FRS3, FRS2; exact FRS1)) as (Σ4 & fl & FLG & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP3, SP2, SP1 in FLW.
  (* [comment removed for export] *)
  pose proof (icb_s2_walk (Z_to_bv 64 SITE_icf_or) ra sp gp (Z_to_bv 64 TP_A) y0 y1 y2 z0 z1 z2 z3 z4 g5 g6 g7 (Z_to_bv 64 OPT_LOAD_STRINGS) a1 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 1)
                (Z_to_bv 64 (f / 8 + 2147450880)) s10 s11 y3 y4 y5 y6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F6 fc6 m7 f fl lo pad j8
                HP ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH F0 ltac:(lia) FL0 ltac:(lia) ST7 GAP7 FR7 FW FLG MI7) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc7' c8 Hc8.
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (q0 & q1 & q2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & q3 & q4 & q5 & q6 & m8 & -> & MU8 & WM8 & MI8 & ST8 & FL8) & Hc8'). clear Hc8.
  fold usp in ST8.
  destruct (REL m8 MU8 WM8 FL8) as (ART8 & FRS4 & LV4 & SP4 & CR4 & AL4 & AM4 & CG4).

  (* [comment removed for export] *)
  assert (NFLs : forall x, client_static x -> x <> fl) by (intros x Hx E; subst x; apply NAC; right; left; exact Hx).
  assert (NFL3 : forall p n x, In (p, n) (rt_live RT Σ3) -> p <= x < p + n -> x <> fl) by (intros p n x Hin R E; subst x; apply NAC; right; right; left; exists p, n; split; [exact Hin| exact R]).
  assert (WM68 : wmono asegs m6 m8) by exact (wmono_trans asegs _ _ _ WM7 WM8).
  assert (AG68 : forall Q : Z -> Prop, (forall x, Q x -> ~ (usp1 - 160 <= x < usp1) /\ ~ (0xb9f300 <= x < 0xb9f304) /\ ~ (TP_A + -96 <= x < TP_A + -88) /\ ~ (0xb9f2a0 <= x < 0xb9f2a8)
                                                  /\ ~ (f <= x < f + 8) /\ ~ (f + 32 <= x < f + 40) /\ ~ (shad f <= x < shad f + 8) /\ x <> fl) -> agree_on Q m6 m8).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8). clear HQ Ha. unfold shad, SHB in X7.
    rewrite (MU8 a). 2:{ cbn [outside]. clear - X8. split; [lia| exact I]. }
    apply MU7. cbn [outside]. unfold usp1 in *. clear - X1 X2 X3 X4 X5 X6 X7. repeat split; try exact I; lia. }
  assert (AG78 : forall Q : Z -> Prop, (forall x, Q x -> x <> fl) -> agree_on Q m7 m8).
  { intros Q HQ a Ha. apply MU8. cbn [outside]. pose proof (HQ _ Ha). clear - H. split; [lia| exact I]. }
  assert (STAT68 : forall a cs, rw_cells asegs m6 a cs ->
            ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f2a0) \/ (0xb9f2a8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f300)
             \/ (0xb9f304 <= a /\ a + Z.of_nat (cells_size cs) <= TP_A + -96) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0))
            -> rw_cells asegs m8 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m6 m8 _ _ X); [| exact WM68]. apply AG68. intros x Hx. cbv beta in Hx.
    assert (CSx : client_static x) by (clear - H1 Hx; apply client_static_intro; lia). pose proof (NFLs x CSx) as NX.
    clear - H1 Hx NX FIMG F0 HLOS HSTK HP. unfold shad, SHB, usp1, usp, RT_STACK in *. repeat split; lia. }
  assert (STAT78 : forall a cs, rw_cells asegs m7 a cs -> 0x5a9d08 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 -> (a + Z.of_nat (cells_size cs) <= 0xba3e98 \/ 0xbc41b8 <= a) ->
            (a + Z.of_nat (cells_size cs) <= 0xbc5298 \/ 0xbc52a0 <= a) -> (a + Z.of_nat (cells_size cs) <= 0x6694d8 \/ 0xb8f190 <= a) -> rw_cells asegs m8 a cs).
  { intros a cs X H1 H2 H3 H4 H5. apply (rw_cells_agree asegs m7 m8 _ _ X); [| exact WM8]. apply AG78. intros x Hx. cbv beta in Hx. apply NFLs. clear - H1 H2 H3 H4 H5 Hx. apply client_static_intro; lia. }
  (* [comment removed for export] *)
  assert (IN23 : forall x, In x (rt_live RT Σ2) -> In x (rt_live RT Σ3)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; right; right; right; right; exact Hx]).
  assert (INP12 : In (p1, 40) (rt_live RT Σ2)) by (rewrite LV2; right; left; reflexivity).
  assert (INP22 : In (p2, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INMK3 : In (MK, 72) (rt_live RT Σ3)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; right; right; right; left; reflexivity]).
  assert (INSA3 : In (SA, 32) (rt_live RT Σ3)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; right; right; left; reflexivity]).
  assert (INPP3 : In (P, 128) (rt_live RT Σ3)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; right; left; reflexivity]).
  assert (INPK3 : In (pk, 40) (rt_live RT Σ3)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; right; left; reflexivity]).
  destruct (af_frames_range RT AF Σ3 m6 f 0%nat ART6 FRIN6) as (_ & _ & _ & FAP3). change (fs_size 0) with 64 in FAP3.
  pose proof (af_fshadow_apart RT AF Σ3 m6 f 0%nat ART6 FRIN6) as FSA3. change (fs_size 0) with 64 in FSA3.
  assert (BLK68 : forall p n cs, In (p, n) (rt_live RT Σ3) -> rw_cells asegs m6 p cs -> Z.of_nat (cells_size cs) <= n -> n <= 64512 -> rw_cells asegs m8 p cs).
  { intros p n cs Hin X Hsz Hn. pose proof (af_live_range RT AF Σ3 m6 p n ART6 Hin) as (P0' & PLO' & _). rewrite SP3, SP2, SP1 in PLO'.
    pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 p n ART6 Hin ltac:(exact Hn)) as PHI'.
    pose proof (FAP3 _ _ Hin) as PF. pose proof (proj1 FSA3 _ _ Hin) as PS. rewrite SHF in PS.
    apply (rw_cells_agree asegs m6 m8 _ _ X); [| exact WM68]. apply AG68. intros x Hx. cbv beta in Hx.
    pose proof (NFL3 p n x Hin ltac:(clear - Hx Hsz; lia)) as NX.
    clear - Hx Hsz NX P0' PLO' PHI' PF PS NUM HLOS HSTK HP F0. unfold shad, SHB, usp1, usp, RT_STACK, STACK_WIN, USTACK_TOP in *. repeat split; try lia. }

  (* [comment removed for export] *)
  assert (BLK46 : forall p cs, In (p, 40) (rt_live RT Σ2) -> rw_cells asegs m4 p cs -> Z.of_nat (cells_size cs) <= 40 -> rw_cells asegs m6 p cs).
  { intros p cs Hin X Hsz. pose proof (af_live_range RT AF Σ2 m4 p 40 ART4 Hin) as (P0' & PLO' & _). rewrite SP2, SP1 in PLO'.
    pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 p 40 ART4 Hin ltac:(clear; lia)) as PHI'.
    assert (X5 : rw_cells asegs m5 p cs).
    { apply (rw_cells_agree asegs m4 m5 _ _ X); [| exact WM5]. apply OUT5. intros x Hx. cbv beta in Hx. clear - Hx Hsz PLO' PHI' NUM HLOS HSTK HP. unfold usp1, usp, RT_STACK, STACK_WIN in *. repeat split; lia. }
    apply (rw_cells_agree_nw asegs m5 m6 _ _ X5). apply AG56. intros x Hx. cbv beta in Hx. clear - Hx Hsz Hin PLO' PHI' HJ HJ0. split; [right; right; left; exists p, 40; split; [exact Hin| lia]|].
    unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (BLK68 p1 40 _ (IN23 _ INP12) (BLK46 p1 _ INP12 MC14 ltac:(cbn; lia)) ltac:(cbn; lia) ltac:(lia)) as MC18.
  pose proof (BLK68 p2 40 _ (IN23 _ INP22) (BLK46 p2 _ INP22 MC24 ltac:(cbn; lia)) ltac:(cbn; lia) ltac:(lia)) as MC28.
  pose proof (BLK68 MK 72 _ INMK3 MKC6 ltac:(cbn; lia) ltac:(lia)) as MKC8.
  pose proof (BLK68 SA 32 _ INSA3 SAC6 ltac:(cbn; lia) ltac:(lia)) as SAC8.
  pose proof (BLK68 P 128 _ INPP3 PC6 ltac:(cbn; lia) ltac:(lia)) as PC8.
  pose proof (BLK68 pk 40 _ INPK3 MC6 ltac:(cbn [cells_size csize Nat.add mutex_cells]; lia) ltac:(lia)) as MC8.
  assert (CLE8 : cl_env m8 lb' canary).
  { apply (cl_env_agree m6 m8 _ _ CLE6). intros a Ha. apply (AG68 cl_cell); [| exact Ha]. intros x Hx.
    pose proof (cl_cell_static _ Hx) as CS. pose proof (NFLs _ CS) as NX. pose proof (client_static_range _ CS) as CR.
    unfold cl_cell, in_ranges, CL_CELLS in Hx. destruct Hx as (lo' & hi' & Hin & R). cbn in Hin.
    clear - Hin R NX CR FIMG F0 NUM HLOS HSTK HP. unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard, shad, SHB, usp1, usp, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try contradiction; repeat split; try lia. }
  assert (STC8 : err_statics m8 pk lh).
  { destruct STC6 as (Y1 & Y2 & Y3 & Y4). unfold err_statics, G_ERR_ONCE, G_ERR_FLAG, G_ERR_LOCK, G_ERR_HASH in *.
    exact (conj (STAT68 _ _ Y1 ltac:(cbn; lia)) (conj (STAT68 _ _ Y2 ltac:(cbn; lia)) (conj (STAT68 _ _ Y3 ltac:(cbn; lia)) (STAT68 _ _ Y4 ltac:(cbn; lia))))). }
  assert (REPE8 : lh_repE GOBJ m8 L' lh B g' bks').
  { destruct REPE6 as (REP & PERML & ALN). split; [| exact (conj PERML ALN)]. pose proof (lh_geo_bounds g' (proj1 REP)) as GB.
    eapply lh_rep_agree; [exact REP| | intros ? ? ? ? _ X; exact X]. intros a Ra Ha.
    assert (INa : exists p n, In (p, n) L' /\ p <= a < p + n /\ n <= 64512).
    { destruct Ha as [X|[X|(q & A & Hq & X)]]; [exists lh, 104| exists B, (8 * g_na g')| exists A, 24]; (split; [| split; [lia | clear - GB; lia]]).
      - eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity].
      - eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity].
      - destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _]. exact O. }
    destruct INa as (p & n & Hin & R & NSZ).
    assert (INp3 : In (p, n) (rt_live RT Σ3)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM3| apply in_or_app; left; exact Hin]).
    pose proof (af_live_range RT AF Σ3 m6 p n ART6 INp3) as (_ & PLO' & _). rewrite SP3, SP2, SP1 in PLO'.
    assert (Hn1 : 0 < n) by (clear - R; lia). pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 p n ART6 INp3 NSZ) as PHI'.
    pose proof (FAP3 _ _ INp3) as PF. pose proof (proj1 FSA3 _ _ INp3) as PS. rewrite SHF in PS.
    pose proof (NFL3 p n a INp3 R) as NX.
    assert (E : m8 (wa a) = m6 (wa a)); [| split; [exact E| intros Hw; apply WM68; exact Hw]].
    apply (AG68 (fun x => x = a)); [| unfold wa; rewrite unsigned_lit by (clear - Ra; lia); reflexivity]. intros x ->.
    clear - R PLO' PHI' PF PS NX NUM HLOS HSTK HP F0. unfold shad, SHB, usp1, usp, USTACK_TOP, RT_STACK, STACK_WIN in *. repeat split; lia. }

  (* [comment removed for export] *)
  assert (INL3 : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ3)) by (intros x Hx; apply IN23; rewrite LV2, LV1; right; right; exact Hx).
  apply Hk. exists Σ4, p1, p2, MK, SA, P, pk, lh, B, L', g', bks', lb', u', e', top'.
  split.
  2:{ split; [rewrite LV4; rewrite LV2, LV1 in PERM3; exact PERM3|].
      split; [exact LL3|]. split; [exact IT3|].
      split; [exact FRS4|]. split; [rewrite SP4, SP3, SP2; exact SP1|]. split; [rewrite CR4; clear - CR3 CR2 CR1; lia|]. split; [rewrite CG4, CG3, CG2; exact CG1|].
      repeat split; assumption. }
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ3 Σ4 PMc _ c8 Hc8' AL4 AM4)|]. intros ms <-. exists m8.
  split; [exists q0, q1, q2, e1, e2, e3, e4, e5, e6, e7, q3, q4, q5, q6, F6, fc6; reflexivity|].
  split; [exact (conj ART8 (conj MI8 ST8))|].
  split.
  { intros a Ha Ho. unfold ICF_W, IB_W, LS_W, G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET,
      G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET in Ho. cbn [outside app] in Ho.
    destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 & O19 & O20 & O21 & O22 & O23 & O24 & O25 & O26 & O27 & O28 & O29 & _).
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (N1 & N2). change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2.
    pose proof (cl_split RT AF Σ m usp 0x430 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
    assert (NF : bv_unsigned a <> fl).
    { intros E. destruct Ha as [H|H]; [clear - H E FLW NUM; unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia|]. apply NAC. rewrite <- E. right.
      destruct H as [H|[H|[H|H]]]; [left; exact H | right; left; destruct H as (p' & n' & Hin & R); exists p', n'; split; [exact (INL3 _ Hin)| exact R]
        | right; right; left; destruct H as (f' & k' & Hin & R); exists f', k'; split; [rewrite FRS3, FRS2, FRS1; right; exact Hin | exact R]
        | right; right; right; destruct H as (f' & k' & Hin & R); exists f', k'; split; [rewrite FRS3, FRS2, FRS1; right; exact Hin | exact R]]. }
    rewrite (MU8 a). 2:{ cbn [outside]. clear - NF. split; [lia| exact I]. }
    rewrite (MU7 a). 2:{ cbn [outside]. unfold shad, SHB in N2. unfold usp1. clear - N1 N2 N4 O2 O3 O4 HP. repeat split; try exact I; lia. }
    assert (X1 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp2 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV2, LV1; right; right; exact Hy | rewrite FRS2, FRS1; intros y Hy; right; exact Hy | clear - HP; unfold usp2, usp1; lia]. }
    assert (X2 : outside (LS_W (j1 + 2)) (bv_unsigned a)) by (unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET; cbn [outside]; clear - O15 O16 O17 O18 O19 O20 O21 O22 O23 O24 O25 O26 O27 O28 O29; repeat split; try exact I; lia).
    rewrite (PRES6 a X1 X2).
    rewrite (MU5 a). 2:{ cbn [outside]. unfold usp1. clear - N4 O1 O2 O4 HP. repeat split; try exact I; lia. }
    assert (X3 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp2 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV1; exact Hy | rewrite FRS1; intros y Hy; right; exact Hy | clear - HP; unfold usp2, usp1; lia]. }
    assert (X4 : outside (IB_W j1 (j1 + 1)) (bv_unsigned a)) by (unfold IB_W, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET; cbn [outside]; clear - O5 O6 O7 O8 O9 O10 O11 O12 O13 O14; repeat split; try exact I; lia).
    rewrite (PRES4 a X3 X4). exact (PR03 a Ha O1 O2 O3 O4). }
  split; [exact CLE8|].
  split; [exact (STAT68 _ _ STP6 ltac:(cbn; lia))|].
  split; [exact (STAT78 _ _ OD7 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ ONCE6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ BRET6 ltac:(cbn; lia))|].
  split; [exact (STAT78 _ _ LSO7 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ LSR6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ OLC6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ ILC6 ltac:(cbn; lia))|].
  split; [exact MC18|]. split; [exact MC28|].
  split; [exact (STAT68 _ _ DK6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ IK6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ BI6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ NK6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ KL6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ K06 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ K16 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ K26 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ ERC6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ OC6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ IC6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ KC6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ SLOT6 ltac:(cbn; lia))|].
  split; [exact (STAT68 _ _ UC6 ltac:(cbn; lia))|].
  split; [exact (STAT78 _ _ CBC7 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [exact MKC8|]. split; [exact SAC8|]. split; [exact TOP6|]. split; [exact PC8|].
  split; [exact STC8|]. split; [exact MC8|]. exact REPE8.
Qed.
End ICFull.

