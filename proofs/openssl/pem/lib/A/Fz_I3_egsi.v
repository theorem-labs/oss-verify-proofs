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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_mtl Fz_T_its Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_I3_glx0 Fz_G_OSSL_ERR_STATE_new Fz_I3_icfast Fz_I3_egsiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).

Section EgsiFirst.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ICB : init_crypto_base_stmt RT.
Hypothesis C_NEW : OSSL_ERR_STATE_new_stmt RT.
Hypothesis C_ITS : its_first_stmt RT.
Hypothesis C_ICF : init_crypto_fast_stmt RT.
Hypothesis GO_mkey : GOBJ MK_KEY 4.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition EG_SITES : list (Z * Z) := [(SITE_eg_new, e_get_state); (SITE_eg_its, e_get_state)] ++ (* [comment removed for export] *) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)] ++ ITS_SITES.
Definition EG_CALLS : list (Z * Z) := [(SITE_eg_new, e_OSSL_ERR_STATE_new); (SITE_eg_new, e_CRYPTO_zalloc); (SITE_eg_its, e_its)] ++ [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ++ ITS_CALLS.
Definition EG_W (kd SA P : Z) : list (Z * Z) := (SA + 8, SA + 24) :: (P, P + 8) :: (G_ALLOW_CUST, G_ALLOW_CUST + 1) :: MTL_W kd.   (* [comment removed for export] *)

Definition egsi_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (k kd MK SA P : Z) (pad top : word) (jm1 jm2 jp : list byte) (u : byte) (r0 g0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x360 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_get_state (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) EG_SITES EG_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX -> 3 + mcost 904 <= rt_credit RT Σ -> cl_env m lb canary ->
  (* [comment removed for export] *)
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 (Z_to_bv 64 2)] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  (* [comment removed for export] *)
  rw_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
  rw_cells asegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] -> In (MK, 72) (rt_live RT Σ) -> In (SA, 32) (rt_live RT Σ) -> In (P, 128) (rt_live RT Σ) ->
  MK mod 16 = 0 -> SA mod 16 = 0 -> P mod 16 = 0 -> (SA + 32 <= P \/ P + 128 <= SA) -> (SA + 32 <= MK \/ MK + 72 <= SA) -> (P + 128 <= MK \/ MK + 72 <= P) ->
  rw_cells asegs m MK [CB 24 jm1; C8 (Z_to_bv 64 SA); CB 40 jm2] ->
  rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top (Z_to_bv 64 0) (Z_to_bv 64 P)) -> rw_cells asegs m P [C8 (Z_to_bv 64 0); CB 120 jp] ->
  (* [comment removed for export] *)
  rw_cells asegs m DTOR_KEY [C4 (Z_to_bv 64 kd); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= kd < 128 -> k <> kd -> rw_cells asegs m (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (TP_A + -150) [C1 u] -> rw_cells asegs m TEV_ONCE [C4 (Z_to_bv 64 0)] -> rw_cells asegs m TEV_RET [C4 r0] -> rw_cells asegs m TEV_REG [C8 g0] ->
  rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_get_state m)))
    (fun c => exists (Σ' : rts RT) (E N H G SK LK D : Z) (u' : byte) (top' : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 2)]
           /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 1) (Z_to_bv 64 P)) /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
           /\ rw_cells asegs m' P [C8 (Z_to_bv 64 E); CB 120 jp]
           /\ bytes_at asegs m' E (repeat (Z_to_bv 8 0) (Z.to_nat 904)) /\ acc asegs m' E 904
           /\ rw_cells asegs m' (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 H)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
           /\ rw_cells asegs m' TEV_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' TEV_RET [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' TEV_REG [C8 (Z_to_bv 64 G)]
           /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
           /\ rw_cells asegs m' H [C8 (Z_to_bv 64 N)] /\ rw_cells asegs m' N [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ERR_DEL_THREAD_STATE); C8 (Z_to_bv 64 0)]
           /\ rw_cells asegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)] /\ rw_cells asegs m' LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' D [C8 (Z_to_bv 64 H); CB 24 (repeat (Z_to_bv 8 0) 24)]) c
       /\ rt_live RT Σ' = [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ (E, 904) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 3 - mcost 904 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < E /\ E mod 16 = 0 /\ E + 904 < USTACK_TOP).

Theorem egsi_first_cps : egsi_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary k kd MK SA P pad top jm1 jm2 jp u r0 g0 oldcb
    FDO MST -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr CLE STP OD ONCE BRET OC KC HK TSK INMK INSA INP MK16 SA16 P16 DISJ MKS MKP MKC SAC PC DK HKD KKD TSL UC TVO TVR TVG CBC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 0x360 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  set (usp1 := usp + -48).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLOS : 0x10007fff8000 <= lo) by exact (proj1 (proj2 NUM)).
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in *.
  (* [comment removed for export] *)
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INMK) as (MK0 & MKLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m MK 72 ART0 INMK ltac:(lia)) as MKHI.
  pose proof (af_live_range RT AF Σ m SA 32 ART0 INSA) as (SA0 & SALO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m SA 32 ART0 INSA ltac:(lia)) as SAHI.
  pose proof (af_live_range RT AF Σ m P 128 ART0 INP) as (P0 & PLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m P 128 ART0 INP ltac:(lia)) as PHI.
  (* [comment removed for export] *)
  pose proof (gsi0_s0_walk ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (PR1' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m1 a = m a) by (intros a Ha; exact (PR1 a Ha I)).
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) -> rw_cells asegs m1 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m m1 _ _ H); [| exact WM1]. intros x Hx. cbv beta in Hx. apply PR1'. exact (H1 _ Hx). }
  (* [comment removed for export] *)
  apply (C_ICB Σ PMc (Z_to_bv 64 SITE_gsi_icb) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 0) (Z_to_bv 64 OPT_BASE_ONLY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (Z_to_bv 64 2) FDO MST eq_refl eq_refl ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { exact Hfr. }
  { clear - Hcr. unfold mcost in *. cbn in *. lia. }
  { apply (STAT1 _ _ STP). cbn. intros x Hx. right; left. apply client_static_intro. lia. }
  { apply (STAT1 _ _ OD). cbn. intros x Hx. right; left. apply client_static_intro. lia. }
  { apply (STAT1 _ _ ONCE). cbn. intros x Hx. right; left. apply client_static_intro. lia. }
  { apply (STAT1 _ _ BRET). cbn. intros x Hx. right; left. apply client_static_intro. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & STP2 & OD2 & ONCE2 & BRET2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_gsi_icb) in Hc2' by (unfold SITE_gsi_icb; lia).
  (* [comment removed for export] *)
  assert (PR02 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros ? X; exact X| intros ? X; exact X| unfold usp1; lia])). exact (PR1' a Ha). }
  assert (WM02 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
  assert (STAT2 : forall a cs, rw_cells asegs m a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) -> rw_cells asegs m2 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m m2 _ _ H); [| exact WM02]. intros x Hx. cbv beta in Hx. apply PR02. exact (H1 _ Hx). }
  assert (ROT2 : forall a cs, ro_cells asegs m a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) -> ro_cells asegs m2 a cs).
  { intros a cs H H1. apply (ro_cells_agree asegs m m2 _ _ H). intros x Hx. apply PR02. exact (H1 _ Hx). }
  assert (ACS : forall a n x, a <= x < a + n -> 0xb9f200 <= a -> a + n <= 0xba3e98 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros a n x Hx H1 H2. right; left. apply client_static_intro. lia. }
  assert (ACB : forall p n x, In (p, n) (rt_live RT Σ) -> p <= x < p + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros p n x Hin Hx. right; right; left. exists p, n. split; [exact Hin| exact Hx]. }
  pose proof (STAT2 _ _ OC ltac:(cbn; intros x Hx; apply (ACS MK_ONCE 4 x Hx); lia)) as OC2.
  pose proof (STAT2 _ _ KC ltac:(cbn; intros x Hx; apply (ACS MK_KEY 4 x Hx); lia)) as KC2.
  assert (TSK2 : rw_cells asegs m2 (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)]).
  { apply (STAT2 _ _ TSK). cbn. intros x Hx. right; left. apply client_static_intro. lia. }
  pose proof (STAT2 _ _ MKC ltac:(cbn; intros x Hx; apply (ACB MK 72 x INMK); lia)) as MKC2.
  pose proof (STAT2 _ _ SAC ltac:(unfold sa_hdr; cbn; intros x Hx; apply (ACB SA 32 x INSA); lia)) as SAC2.
  pose proof (STAT2 _ _ PC ltac:(cbn; intros x Hx; apply (ACB P 128 x INP); lia)) as PC2.
  assert (SLOT2 : ro_cells asegs m2 (MK + 24) [C8 (Z_to_bv 64 SA)]).
  { pose proof (rw_cells_skip m2 MK [CB 24 jm1] [C8 (Z_to_bv 64 SA); CB 40 jm2] MKC2) as X. cbn [cells_size csize Nat.add] in X. replace (MK + Z.of_nat 24) with (MK + 24) in X by lia.
    exact (proj1 (rw_cells_head m2 _ _ _ X)). }
  pose proof (rw_cells_head m2 _ _ _ PC2) as PC02.
  assert (INMK1 : In (MK, 72) (rt_live RT Σ1)) by (rewrite LV1; exact INMK). assert (INSA1 : In (SA, 32) (rt_live RT Σ1)) by (rewrite LV1; exact INSA). assert (INP1 : In (P, 128) (rt_live RT Σ1)) by (rewrite LV1; exact INP).
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 MK 72 ART2 INMK1)) as ACCM2. pose proof (proj2 (af_acc_live RT AF Σ1 m2 SA 32 ART2 INSA1)) as ACCS2. pose proof (proj2 (af_acc_live RT AF Σ1 m2 P 128 ART2 INP1)) as ACCP2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m2 _ _ MK_KEY ART2 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB2. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB2.
  pose proof (TSD Σ1 m2 ART2) as TSD2.
  (* [comment removed for export] *)
  pose proof (eg_w1 sp gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo k MK SA P pad top
                ST2 ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH UT2 SHC2 (proj1 OC2) (proj1 KC2) HK KSB2 (proj1 TSD2) (proj1 TSK2)
                MKHI ltac:(clear - MK16; Z.div_mod_to_equations; lia) ltac:(clear - MKLO LOW; lia) ACCM2 SLOT2
                SAHI ltac:(clear - SA16; Z.div_mod_to_equations; lia) ltac:(clear - SALO LOW; lia) ACCS2 SAC2
                PHI ltac:(clear - P16; Z.div_mod_to_equations; lia) ltac:(clear - PLO LOW; lia) ACCP2 PC02 DISJ MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (v1 & x1 & x2 & x3 & x4 & x5 & x6 & top1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & HT3 & SAC3 & PC3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3'. fold usp1 in ST3, Hc3'.
  (* [comment removed for export] *)
  assert (OUT3 : forall Q : Z -> Prop, (forall x, Q x -> ~ (usp - 160 <= x < usp - 48) /\ ~ (SA + 8 <= x < SA + 24) /\ ~ (P <= x < P + 8)) -> agree_on Q m2 m3).
  { intros Q HQ a Ha. apply MU3. cbn [outside]. destruct (HQ _ Ha) as (X1 & X2 & X3). repeat split; try exact I; lia. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 160) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. repeat split; try exact I; intros Hin; apply Ha.
    - left. unfold USTACK_TOP in *. lia.
    - right; right; left. exists SA, 32. split; [exact INSA1| lia].
    - right; right; left. exists P, 128. split; [exact INP1| lia]. }
  assert (STAT3 : forall a cs, rw_cells asegs m2 a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 -> rw_cells asegs m3 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree asegs m2 m3 _ _ X); [| exact WM3]. apply OUT3. intros x Hx. cbv beta in Hx. clear - H1 H2 Hx SAHI PHI HSTK HLOS. unfold usp, RT_STACK in *. repeat split; lia. }
  eassert (FR3 : rw_cells asegs m3 (usp + -48) _).
  { apply (rw_cells_agree asegs m2 m3 _ _ (rw_cells_agree asegs m1 m2 _ _ FR1 ltac:(intros x Hx; cbv beta in Hx; cbn [cells_size csize Nat.add] in Hx; apply PRES2; left; unfold usp1, USTACK_TOP in *; lia) WM2)); [| exact WM3].
    apply OUT3. cbn [cells_size csize Nat.add]. intros x Hx. clear - Hx SALO PLO NUM HSTK HLOS. unfold usp1, usp, RT_STACK, STACK_WIN in *. repeat split; lia. }
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m3 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3). }
  assert (AGS3 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros a Ha. cbv beta in Ha. rewrite (MU3 a). 2:{ cbn [outside]. unfold usp in *. clear - Ha SALO PLO SP0R NUM. unfold USTACK_TOP, STACK_WIN in *. repeat split; try exact I; lia. } apply PR02. left. exact Ha. }
  rewrite <- CG1 in CGH, CTX.
  destruct (cl_chain_call (rt_cg RT Σ1) e_get_state e_OSSL_ERR_STATE_new SITE_eg_new m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AGS3 FRR3 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX3 & UWC3).
  assert (CLE3 : cl_env m3 lb canary).
  { apply (cl_env_agree m m3 _ _ CLE). intros a Ha. pose proof (cl_cell_static _ Ha) as CS. pose proof (client_static_range _ CS) as CR.
    rewrite (MU3 a). 2:{ cbn [outside]. unfold usp in *. clear - CR SAHI PHI HSTK HLOS. unfold SEGTOP_A, RT_STACK in *. repeat split; try exact I; lia. }
    apply PR02. right; left. exact CS. }
  (* [comment removed for export] *)
  apply (C_NEW Σ1 PMc (Z_to_bv 64 SITE_eg_new) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 v1 u2 sp (Z_to_bv 64 0) (Z_to_bv 64 1) x1 x2 x3 x4 x5 x6 b7
           (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl ART3 MI3).
  { assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    unfold call_ok. rewrite EU1. split; [exact ST3|]. split; [exact LOW1|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_eg_new) by (unfold SITE_eg_new; lia). exact CTX3. }
  { exact UWC3. }
  { rewrite (unsigned_lit SITE_eg_new) by (unfold SITE_eg_new; lia). apply (proj2 CGH). right; left. reflexivity. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV1. lia. }
  { rewrite CR1. clear - Hcr. lia. }
  { exact CLE3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & E & Hc4 & LV2 & FRS2 & SP2 & CR2 & E0 & E16 & EU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & WR4 & ACC4 & BY4) & Hc4'). clear Hc4.
  destruct RS4 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_eg_new) in Hc4' by (unfold SITE_eg_new; lia).
  (* [comment removed for export] *)
  assert (EHI : E + 904 < 2 ^ 64) by (clear - EU; unfold USTACK_TOP in *; lia).
  pose proof (eg_w2 sp gp (Z_to_bv 64 TP_A) w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 E ltac:(clear - E0 EHI; lia) MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  assert (AG34 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) -> agree_on Q m3 m4).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). exact (PRES4 a X1 X2). }
  assert (STAT34 : forall a cs, rw_cells asegs m3 a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> client_static x /\ x <> G_ALLOW_CUST) -> rw_cells asegs m4 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG34. intros x Hx. cbv beta in Hx. destruct (H1 _ Hx) as [C N]. split; [right; left; exact C|]. unfold G_ALLOW_CUST in *. cbn [outside]. split; [lia| exact I]. }
  assert (CST : forall a n x, a <= x < a + n -> ((0x5a9d08 <= a /\ a + n <= 0x6694d8) \/ (0xb8f190 <= a /\ a + n <= 0xb9f7c0) \/ (0xb9f7c1 <= a /\ a + n <= 0xba3e98) \/ (0xbc52a0 <= a /\ a + n <= 0xbc57d0)) -> client_static x /\ x <> G_ALLOW_CUST).
  { intros a n x Hx H. unfold G_ALLOW_CUST. split; [apply client_static_intro; lia| lia]. }
  assert (TR04 : forall a cs, rw_cells asegs m a cs -> ((0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f7c0) \/ (0xb9f7c1 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0)) -> rw_cells asegs m4 a cs).
  { intros a cs X H. apply (STAT34 _ _ (STAT3 _ _ (STAT2 _ _ X ltac:(intros x Hx; right; left; exact (proj1 (CST _ _ x Hx H)))) ltac:(clear - H; lia) ltac:(clear - H; lia))). intros x Hx. exact (CST _ _ x Hx H). }
  pose proof (TR04 _ _ DK ltac:(cbn; lia)) as DK4. pose proof (TR04 _ _ TSL ltac:(cbn; lia)) as TSL4. pose proof (TR04 _ _ UC ltac:(cbn; lia)) as UC4.
  pose proof (TR04 _ _ TVO ltac:(cbn; lia)) as TVO4. pose proof (TR04 _ _ TVR ltac:(cbn; lia)) as TVR4. pose proof (TR04 _ _ TVG ltac:(cbn; lia)) as TVG4. pose proof (TR04 _ _ CBC ltac:(cbn; lia)) as CBC4.
  assert (AGS4 : agree_on (fun x => usp <= x < USTACK_TOP) m m4).
  { intros a Ha. cbv beta in Ha. rewrite (PRES4 a ltac:(left; unfold usp1; lia) ltac:(unfold G_ALLOW_CUST; cbn [outside]; clear - Ha HSTK HLOS; unfold usp, RT_STACK in *; split; [lia| exact I])). exact (AGS3 a Ha). }
  assert (FRR4 : rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m3 m4 _ _ FRR3); [| exact WM4]. apply AG34. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST; cbn [outside]. clear - Hx HSTK HLOS. unfold usp, RT_STACK in *. split; [lia| exact I]. }
  eassert (FR4 : rw_cells asegs m4 (usp + -48) _).
  { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. apply AG34. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST; cbn [outside]. clear - Hx HSTK HLOS. unfold usp, RT_STACK in *. split; [lia| exact I]. }
  rewrite <- CG2 in CGH, CTX3.
  destruct (cl_chain_call (rt_cg RT Σ2) e_get_state e_its SITE_eg_its m m4 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG2; exact CTX)
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; right; left; reflexivity)) UWC AGS4 FRR4 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX4 & UWC4).
  (* [comment removed for export] *)
  apply (C_ITS Σ2 PMc (Z_to_bv 64 SITE_eg_its) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 ERR_DEL_THREAD_STATE) d3 d4 d5 d6 d7
           (Z_to_bv 64 E) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary kd u r0 g0 oldcb
           FDO MST eq_refl ART4 MI4).
  { assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2, SP1; exact LOW).
    unfold call_ok. rewrite EU1. split; [exact ST4|]. split; [exact LOW2|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_eg_its) by (unfold SITE_eg_its; lia). exact CTX4. }
  { exact UWC4. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS2, FRS1. exact Hfr. }
  { rewrite LV2, LV1. cbn [length]. lia. }
  { rewrite CR2, CR1. clear - Hcr. lia. }
  { exact CLE4. }
  { exact DK4. } { exact HKD. } { exact TSL4. } { exact UC4. } { exact TVO4. } { exact TVR4. } { exact TVG4. } { exact CBC4. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & N & H & G & SK & LK & D & u' & Hc6 & LV3 & FRS3 & SP3 & CR3 & CG3 & FA3).
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & CLE6 & TSL6 & UC6 & TVO6 & TVR6 & TVG6 & CBC6 & HC6 & NC6 & GC6 & SKC6 & LKC6 & DC6) & Hc6'). clear Hc6.
  destruct RS6 as (y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_eg_its) in Hc6' by (unfold SITE_eg_its; lia).
  (* [comment removed for export] *)
  assert (AG46 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x /\ outside (MTL_W kd) x) -> agree_on Q m4 m6).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). exact (PRES6 a X1 X2). }
  assert (STAT46 : forall a cs, rw_cells asegs m4 a cs ->
            ((0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f4a0) \/ (0xb9f4e8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f7c0) \/ (0xb9f7c1 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e5a) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298)
             \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0 /\ (a + Z.of_nat (cells_size cs) <= TSD_MAIN + 8 * kd \/ TSD_MAIN + 8 * kd + 8 <= a))) -> rw_cells asegs m6 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m4 m6 _ _ X); [| exact WM6]. apply AG46. intros x Hx. cbv beta in Hx. clear - H1 Hx HKD. split; [right; left; apply client_static_intro; lia|].
    unfold MTL_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
  assert (BLK46 : forall p n cs, In (p, n) (rt_live RT Σ) -> rw_cells asegs m4 p cs -> Z.of_nat (cells_size cs) <= n -> n <= 64512 -> rw_cells asegs m6 p cs).
  { intros p n cs Hin X Hsz Hn. pose proof (afp_live_hi RT GOBJ AFP Σ m p n ART0 Hin ltac:(exact Hn)) as PH'.
    apply (rw_cells_agree asegs m4 m6 _ _ X); [| exact WM6]. apply AG46. intros x Hx. cbv beta in Hx. clear - Hin Hx Hsz PH' HKD LV1 LV2.
    split; [right; right; left; exists p, n; split; [rewrite LV2, LV1; right; exact Hin| lia]|]. unfold MTL_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
  assert (TR06 : forall a cs, rw_cells asegs m a cs -> ((0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f4a0) \/ (0xb9f4e8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f7c0)) -> rw_cells asegs m6 a cs).
  { intros a cs X Hw. apply (STAT46 _ _ (TR04 _ _ X ltac:(clear - Hw; lia))). clear - Hw. lia. }
  pose proof (TR06 _ _ OC ltac:(cbn; lia)) as OC6. pose proof (TR06 _ _ KC ltac:(cbn; lia)) as KC6.
  assert (TSK6 : rw_cells asegs m6 (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)]).
  { apply (STAT46 _ _ (TR04 _ _ TSK ltac:(cbn; clear - HK; lia))). cbn. clear - HK HKD KKD. lia. }
  assert (BLK24 : forall p n cs, In (p, n) (rt_live RT Σ) -> rw_cells asegs m3 p cs -> Z.of_nat (cells_size cs) <= n -> n <= 64512 -> rw_cells asegs m4 p cs).
  { intros p n cs Hin X Hsz Hn. pose proof (afp_live_hi RT GOBJ AFP Σ m p n ART0 Hin ltac:(exact Hn)) as PH'.
    apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG34. intros x Hx. cbv beta in Hx. clear - Hin Hx Hsz PH' LV1.
    split; [right; right; left; exists p, n; split; [rewrite LV1; exact Hin| lia]|]. unfold G_ALLOW_CUST. cbn [outside]. split; [lia| exact I]. }
  assert (MKC3 : rw_cells asegs m3 MK [CB 24 jm1; C8 (Z_to_bv 64 SA); CB 40 jm2]).
  { apply (rw_cells_agree asegs m2 m3 _ _ MKC2); [| exact WM3]. apply OUT3. cbn [cells_size csize Nat.add]. intros x Hx. unfold usp in *. clear - Hx MKS MKP MKLO SP0R NUM. unfold STACK_WIN in *. repeat split; lia. }
  pose proof (BLK46 MK 72 _ INMK (BLK24 MK 72 _ INMK MKC3 ltac:(cbn; lia) ltac:(lia)) ltac:(cbn; lia) ltac:(lia)) as MKC6.
  pose proof (BLK46 SA 32 _ INSA (BLK24 SA 32 _ INSA SAC3 ltac:(unfold sa_hdr; cbn; lia) ltac:(lia)) ltac:(unfold sa_hdr; cbn; lia) ltac:(lia)) as SAC6.
  pose proof (BLK46 P 128 _ INP (BLK24 P 128 _ INP PC3 ltac:(cbn; lia) ltac:(lia)) ltac:(cbn; lia) ltac:(lia)) as PC6.
  assert (SLOT6 : ro_cells asegs m6 (MK + 24) [C8 (Z_to_bv 64 SA)]).
  { pose proof (rw_cells_skip m6 MK [CB 24 jm1] [C8 (Z_to_bv 64 SA); CB 40 jm2] MKC6) as X. cbn [cells_size csize Nat.add] in X. replace (MK + Z.of_nat 24) with (MK + 24) in X by lia.
    exact (proj1 (rw_cells_head m6 _ _ _ X)). }
  assert (IN3 : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ3)) by (intros x Hx; rewrite LV3, LV2, LV1; apply in_or_app; right; right; exact Hx).
  pose proof (proj2 (af_acc_live RT AF Σ3 m6 MK 72 ART6 (IN3 _ INMK))) as ACCM6. pose proof (proj2 (af_acc_live RT AF Σ3 m6 SA 32 ART6 (IN3 _ INSA))) as ACCS6. pose proof (proj2 (af_acc_live RT AF Σ3 m6 P 128 ART6 (IN3 _ INP))) as ACCP6.
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ3 m6 _ _ MK_KEY ART6 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB6. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB6.
  pose proof (TSD Σ3 m6 ART6) as TSD6.
  (* [comment removed for export] *)
  pose proof (eg_w3 sp gp y0 y1 y2 g1 g2 g3 g4 g5 g6 g7 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F6 fc6 m6 lo k MK SA P E pad top1
                ST6 ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH UT6 SHC6 (proj1 OC6) (proj1 KC6) HK KSB6 (proj1 TSD6) (proj1 TSK6)
                MKHI ltac:(clear - MK16; Z.div_mod_to_equations; lia) ltac:(clear - MKLO LOW; lia) ACCM6 SLOT6
                SAHI ltac:(clear - SA16; Z.div_mod_to_equations; lia) ltac:(clear - SALO LOW; lia) ACCS6 SAC6
                PHI ltac:(clear - P16; Z.div_mod_to_equations; lia) ltac:(clear - PLO LOW; lia) ACCP6 PC6 DISJ ltac:(clear - E0 EHI; lia) MI6) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (v2 & z2 & z3 & top2 & m7 & -> & MU7 & WM7 & MI7 & ST7 & HT7 & SAC7 & PC7) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, Hc7'. fold usp1 in ST7, Hc7'.
  (* [comment removed for export] *)
  assert (OUT7 : forall Q : Z -> Prop, (forall x, Q x -> ~ (usp - 160 <= x < usp - 48) /\ ~ (SA + 8 <= x < SA + 24) /\ ~ (P <= x < P + 8)) -> agree_on Q m6 m7).
  { intros Q HQ a Ha. apply MU7. cbn [outside]. destruct (HQ _ Ha) as (X1 & X2 & X3). repeat split; try exact I; lia. }
  assert (ART7 : ART RT Σ3 m7).
  { apply (af_frame RT AF Σ3 m6 m7 (usp - 160) ART6 ltac:(rewrite SP3, SP2, SP1; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. repeat split; try exact I; intros Hin; apply Ha.
    - left. unfold USTACK_TOP in *. lia.
    - right; right; left. exists SA, 32. split; [exact (IN3 _ INSA)| lia].
    - right; right; left. exists P, 128. split; [exact (IN3 _ INP)| lia]. }
  assert (STAT67 : forall a cs, rw_cells asegs m6 a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 -> rw_cells asegs m7 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree asegs m6 m7 _ _ X); [| exact WM7]. apply OUT7. intros x Hx. cbv beta in Hx. clear - H1 H2 Hx SAHI PHI HSTK HLOS. unfold usp, RT_STACK in *. repeat split; lia. }
  pose proof (STAT67 _ _ (STAT46 _ _ (TR04 _ _ STP ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(lia) ltac:(cbn; lia)) as STP7.
  pose proof (STAT67 _ _ (STAT46 _ _ (TR04 _ _ OD ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(lia) ltac:(cbn; lia)) as OD7.
  (* [comment removed for export] *)
  apply (C_ICF Σ3 PMc (Z_to_bv 64 SITE_eg_icf) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) y0 v2 y2 sp (Z_to_bv 64 0) (Z_to_bv 64 2) (Z_to_bv 64 0) z2 z3 g4 g5 g6 g7
           (Z_to_bv 64 E) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F6 fc6 m7 lo (Z_to_bv 64 2) 2 FDO MST eq_refl eq_refl ltac:(lia)
           ltac:(rewrite (unsigned_lit 2) by lia; reflexivity) ART7 MI7).
  { assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3, SP2, SP1; exact LOW).
    unfold call_ok. rewrite EU1. split; [exact ST7|]. split; [exact LOW3|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite FRS3, FRS2, FRS1. exact Hfr. }
  { rewrite CR3, CR2, CR1. clear - Hcr. unfold mcost in *. cbn in *. lia. }
  { exact STP7. }
  { exact OD7. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ4 & Hc8 & LV4 & FRS4 & SP4 & CR4 & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & STP8 & OD8) & Hc8'). clear Hc8.
  destruct RS8 as (q0 & q1 & q2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & q3 & q4 & q5 & q6 & F8 & fc8 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_eg_icf) in Hc8' by (unfold SITE_eg_icf; lia).
  (* [comment removed for export] *)
  assert (PR68 : forall a : word, aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp1 (bv_unsigned a) -> ~ (usp - 160 <= bv_unsigned a < usp - 48) -> ~ (SA + 8 <= bv_unsigned a < SA + 24) -> ~ (P <= bv_unsigned a < P + 8) -> m8 a = m6 a).
  { intros a Ha N1 N2 N3. rewrite (PRES8 a Ha). apply MU7. cbn [outside]. repeat split; try exact I; lia. }
  eassert (FR8 : rw_cells asegs m8 (usp + -48) _).
  { assert (FR6 : rw_cells asegs m6 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs m4 m6 _ _ FR4); [| exact WM6]. apply AG46. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia|].
      unfold MTL_W, G_ALLOW_CUST. cbn [outside]. clear - Hx HSTK HLOS HKD. unfold usp, RT_STACK in *. repeat split; try exact I; lia. }
    apply (rw_cells_agree asegs m6 m8 _ _ FR6); [| exact (wmono_trans asegs _ _ _ WM7 WM8)]. cbn [cells_size csize Nat.add]. intros x Hx. apply PR68; [left; unfold usp1, USTACK_TOP in *; lia| | |]; clear - Hx SALO PLO NUM; unfold usp, STACK_WIN in *; lia. }
  (* [comment removed for export] *)
  pose proof (eg_w4 ra sp gp (Z_to_bv 64 TP_A) q0 q1 q2 s0 s1 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6 F8 fc8 m8 lo E
                ST8 ltac:(fold usp; unfold RT_STACK in *; lia) HLOS SPH FR8 MI8) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ4 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & ST9) & Hc9'). clear Hc9.
  fold usp in ST9.
  assert (E98 : forall a, m9 a = m8 a) by (intros a; apply MU9; exact I).
  assert (ART9 : ART RT Σ4 m9) by (apply (af_frame RT AF Σ4 m8 m9 usp1 ART8 ltac:(rewrite SP4, SP3, SP2, SP1; unfold usp1; lia)); [intros a _; apply E98| exact WM9]).
  (* [comment removed for export] *)
  assert (INSA1' : In (SA, 32) ((E, 904) :: rt_live RT Σ1)) by (right; exact INSA1). assert (INP1' : In (P, 128) ((E, 904) :: rt_live RT Σ1)) by (right; exact INP1).
  rewrite <- LV2 in INSA1', INP1'.
  assert (DJ : forall X n l1 l2, rt_live RT Σ3 = l1 ++ (X, n) :: l2 -> In (SA, 32) (l1 ++ l2) -> In (P, 128) (l1 ++ l2) -> (X + n <= SA \/ SA + 32 <= X) /\ (X + n <= P \/ P + 128 <= X)).
  { intros X n l1 l2 HL I1 I2. split; [exact (af_live_disj RT AF Σ3 m6 X n SA 32 l1 l2 ART6 HL I1)| exact (af_live_disj RT AF Σ3 m6 X n P 128 l1 l2 ART6 HL I2)]. }
  destruct (DJ N 32 [] ([(D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ2) ltac:(rewrite LV3; reflexivity) ltac:(apply in_or_app; right; apply in_or_app; right; exact INSA1') ltac:(apply in_or_app; right; apply in_or_app; right; exact INP1')) as [DN1 DN2].
  destruct (DJ D 32 [(N, 32)] ([(LK, 40); (SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ2) ltac:(rewrite LV3; reflexivity) ltac:(apply in_or_app; right; apply in_or_app; right; exact INSA1') ltac:(apply in_or_app; right; apply in_or_app; right; exact INP1')) as [DD1 DD2].
  destruct (DJ LK 40 [(N, 32); (D, 32)] ([(SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ2) ltac:(rewrite LV3; reflexivity) ltac:(apply in_or_app; right; apply in_or_app; right; exact INSA1') ltac:(apply in_or_app; right; apply in_or_app; right; exact INP1')) as [DL1 DL2].
  destruct (DJ SK 56 [(N, 32); (D, 32); (LK, 40)] ([(G, 16); (H, 8)] ++ rt_live RT Σ2) ltac:(rewrite LV3; reflexivity) ltac:(apply in_or_app; right; apply in_or_app; right; exact INSA1') ltac:(apply in_or_app; right; apply in_or_app; right; exact INP1')) as [DS1 DS2].
  destruct (DJ G 16 [(N, 32); (D, 32); (LK, 40); (SK, 56)] ([(H, 8)] ++ rt_live RT Σ2) ltac:(rewrite LV3; reflexivity) ltac:(apply in_or_app; right; apply in_or_app; right; exact INSA1') ltac:(apply in_or_app; right; apply in_or_app; right; exact INP1')) as [DG1 DG2].
  destruct (DJ H 8 [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16)] (rt_live RT Σ2) ltac:(rewrite LV3; reflexivity) ltac:(apply in_or_app; right; exact INSA1') ltac:(apply in_or_app; right; exact INP1')) as [DH1 DH2].
  pose proof (af_live_disj RT AF Σ2 m4 E 904 SA 32 [] (rt_live RT Σ1) ART4 LV2 INSA1) as DE1. pose proof (af_live_disj RT AF Σ2 m4 E 904 P 128 [] (rt_live RT Σ1) ART4 LV2 INP1) as DE2.
  (* [comment removed for export] *)
  assert (IN34 : forall x, In x (rt_live RT Σ3) -> In x (rt_live RT Σ4)) by (intros x Hx; rewrite LV4; exact Hx).
  assert (BLK69 : forall p n cs, In (p, n) (rt_live RT Σ3) -> (p + n <= SA \/ SA + 32 <= p) -> (p + n <= P \/ P + 128 <= p) -> rw_cells asegs m6 p cs -> Z.of_nat (cells_size cs) <= n -> rw_cells asegs m9 p cs).
  { intros p n cs Hin D1 D2 X Hsz. pose proof (af_live_range RT AF Σ3 m6 p n ART6 Hin) as (P0' & PLO' & _). rewrite SP3, SP2, SP1 in PLO'.
    apply (rw_cells_agree asegs m6 m9 _ _ X); [| exact (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 WM9))]. intros x Hx. cbv beta in Hx. rewrite E98.
    apply PR68; [right; right; left; exists p, n; split; [exact Hin| lia] | | |]; clear - Hx Hsz D1 D2 PLO' NUM; unfold usp, STACK_WIN in *; lia. }
  assert (STAT69 : forall a cs, rw_cells asegs m6 a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> client_static x) -> rw_cells asegs m9 a cs).
  { intros a cs X H1 H2 H3'. apply (rw_cells_agree asegs m6 m9 _ _ X); [| exact (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 WM9))]. intros x Hx. cbv beta in Hx. rewrite E98.
    apply PR68; [right; left; exact (H3' _ Hx) | | |]; clear - Hx H1 H2 SAHI PHI HSTK HLOS; unfold usp, RT_STACK in *; lia. }
  assert (CS1 : forall a n x, a <= x < a + n -> ((0x5a9d08 <= a /\ a + n <= 0x6694d8) \/ (0xb8f190 <= a /\ a + n <= 0xba3e98) \/ (0xbc52a0 <= a /\ a + n <= 0xbc57d0)) -> client_static x).
  { intros a n x Hx Hw. apply client_static_intro. destruct Hw as [Hw|[Hw|Hw]]; [left; lia | right; left; lia | do 6 right; lia]. }
  (* [comment removed for export] *)
  apply Hk. exists Σ4, E, N, H, G, SK, LK, D, u', top2.
  split.
  2:{ split; [rewrite LV4, LV3, LV2, LV1; reflexivity|]. split; [rewrite FRS4, FRS3, FRS2; exact FRS1|]. split; [rewrite SP4, SP3, SP2; exact SP1|].
      split; [rewrite CR4, CR3, CR2, CR1; clear; lia|]. split; [rewrite CG4, CG3, CG2; exact CG1|]. repeat split; assumption. }
  eapply ASTA_conseq; [exact Hc9'|]. intros ms <-. exists m9.
  split; [exists q0, q1, q2, e1, e2, e3, e4, e5, e6, e7, q3, q4, q5, q6, F8, fc8; reflexivity|].
  split; [split; [exact ART9| split; [exact MI9| split; [| exact ST9]]]|].
  { exact (wmono_trans asegs _ _ _ WM02 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 WM9)))))). }
  split.
  { intros a Ha Ho. unfold EG_W, MTL_W, G_ALLOW_CUST in Ho. cbn [outside app] in Ho. destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & _).
    pose proof (cl_split RT AF Σ m usp 0x360 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
    rewrite E98.
    assert (X3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; apply IN3; exact Hy | rewrite FRS3, FRS2, FRS1; intros y Hy; exact Hy | unfold usp1; lia]. }
    rewrite (PR68 a X3); [| clear - N4; unfold usp; lia| exact O1| exact O2].
    assert (X2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV2, LV1; right; exact Hy | rewrite FRS2, FRS1; intros y Hy; exact Hy | unfold usp1; lia]. }
    rewrite (PRES6 a X2). 2:{ unfold MTL_W, G_ALLOW_CUST; cbn [outside]; clear - O4 O5 O6 O7 O8 O9 O10; repeat split; try exact I; lia. }
    assert (X1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV1; exact Hy | rewrite FRS1; intros y Hy; exact Hy | unfold usp1; lia]. }
    rewrite (PRES4 a X1 ltac:(unfold G_ALLOW_CUST; cbn [outside]; clear - O3; split; [lia| exact I])).
    rewrite (MU3 a ltac:(cbn [outside]; clear - N4 O1 O2; unfold usp; repeat split; try exact I; lia)).
    exact (PR02 a Ha). }
  assert (CLE9 : cl_env m9 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m6 m9 _ _ CLE6). intros a Ha. pose proof (cl_cell_static _ Ha) as CS. pose proof (client_static_range _ CS) as CR. rewrite E98.
    apply PR68; [right; left; exact CS| | |]; clear - CR SAHI PHI HSTK HLOS; unfold usp, SEGTOP_A, RT_STACK in *; lia. }
  split; [exact CLE9|].
  assert (T89 : forall a cs, rw_cells asegs m8 a cs -> rw_cells asegs m9 a cs) by (intros a cs X; apply (rw_cells_agree asegs m8 m9 _ _ X); [intros y _; apply E98| exact WM9]).
  assert (B79 : forall p n q cs, In (p, n) (rt_live RT Σ3) -> rw_cells asegs m7 q cs -> p <= q -> q + Z.of_nat (cells_size cs) <= p + n -> rw_cells asegs m9 q cs).
  { intros p n q cs Hin X H1 H2. apply T89. apply (rw_cells_agree asegs m7 m8 _ _ X); [| exact WM8]. intros y Hy. cbv beta in Hy. apply PRES8. right; right; left. exists p, n. split; [exact Hin| lia]. }
  assert (INL3 : forall x, In x [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] -> In x (rt_live RT Σ3)) by (intros x Hx; rewrite LV3; apply in_or_app; left; exact Hx).
  split; [exact (T89 _ _ STP8)|].
  split; [exact (T89 _ _ OD8)|].
  split; [exact (STAT69 _ _ (STAT46 _ _ (TR04 _ _ ONCE ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; intros x Hx; apply (CS1 0xb9f2c0 4 x Hx); lia))|].
  split; [exact (STAT69 _ _ (STAT46 _ _ (TR04 _ _ BRET ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; intros x Hx; apply (CS1 0xb9f2e0 4 x Hx); lia))|].
  split; [exact (B79 SA 32 SA _ (IN3 _ INSA) SAC7 ltac:(lia) ltac:(unfold sa_hdr; cbn; lia))|].
  split; [clear - HT7 HT3; lia|].
  split.
  { change [C8 (Z_to_bv 64 E); CB 120 jp] with ([C8 (Z_to_bv 64 E)] ++ [CB 120 jp]). apply (proj2 (rw_cells_app _ _ _ _)). split; [exact (B79 P 128 P _ (IN3 _ INP) PC7 ltac:(lia) ltac:(cbn; lia))|].
    cbn [cells_size csize Nat.add]. pose proof (rw_cells_skip m2 P [C8 (Z_to_bv 64 0)] [CB 120 jp] PC2) as PT2. cbn [cells_size csize Nat.add] in PT2.
    assert (PT3 : rw_cells asegs m3 (P + 8) [CB 120 jp]).
    { apply (rw_cells_agree asegs m2 m3 _ _ PT2); [| exact WM3]. apply OUT3. cbn [cells_size csize Nat.add]. intros y Hy. unfold usp in *. clear - Hy DISJ PLO NUM. unfold STACK_WIN in *. repeat split; lia. }
    assert (PT4 : rw_cells asegs m4 (P + 8) [CB 120 jp]).
    { apply (rw_cells_agree asegs m3 m4 _ _ PT3); [| exact WM4]. apply AG34. cbn [cells_size csize Nat.add]. intros y Hy. split; [right; right; left; exists P, 128; split; [exact INP1| clear - Hy; lia]|].
      unfold G_ALLOW_CUST. cbn [outside]. clear - Hy PHI. split; [lia| exact I]. }
    assert (PT6 : rw_cells asegs m6 (P + 8) [CB 120 jp]).
    { apply (rw_cells_agree asegs m4 m6 _ _ PT4); [| exact WM6]. apply AG46. cbn [cells_size csize Nat.add]. intros y Hy. split; [right; right; left; exists P, 128; split; [rewrite LV2, LV1; right; exact INP| clear - Hy; lia]|].
      unfold MTL_W, G_ALLOW_CUST. cbn [outside]. clear - Hy PHI HKD. repeat split; try exact I; lia. }
    apply (rw_cells_agree asegs m6 m9 _ _ PT6); [| exact (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 WM9))]. cbn [cells_size csize Nat.add]. intros y Hy. rewrite E98.
    apply PR68; [right; right; left; exists P, 128; split; [exact (IN3 _ INP)| clear - Hy; lia] | | |]; clear - Hy DISJ PLO NUM; unfold usp, STACK_WIN in *; lia. }
  assert (INE2 : In (E, 904) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 E 904 ART4 INE2 ltac:(clear; lia)) as EHI2. pose proof (af_live_range RT AF Σ2 m4 E 904 ART4 INE2) as (_ & ELO & _). rewrite SP2, SP1 in ELO.
  split.
  { apply (bytes_at_agree asegs m4 m9 _ _ BY4). rewrite repeat_length. change (Z.of_nat (Z.to_nat 904)) with 904. intros y Hy. cbv beta in Hy. rewrite E98.
    rewrite (PR68 y); [| | clear - Hy ELO NUM; unfold usp, STACK_WIN in *; lia | clear - Hy DE1; lia | clear - Hy DE2; lia].
    - apply PRES6; [right; right; left; exists E, 904; split; [exact INE2| exact Hy]|]. unfold MTL_W, G_ALLOW_CUST. cbn [outside]. clear - Hy EHI2 HKD. repeat split; try exact I; lia.
    - right; right; left. exists E, 904. split; [rewrite LV3; apply in_or_app; right; exact INE2| exact Hy]. }
  split; [exact (proj2 (af_acc_live RT AF Σ4 m9 E 904 ART9 ltac:(rewrite LV4, LV3; apply in_or_app; right; exact INE2)))|].
  split; [exact (STAT69 _ _ TSL6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; intros x Hx; apply (CS1 (TSD_MAIN + 8 * kd) 8 x Hx); lia))|].
  split; [exact (STAT69 _ _ UC6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; intros x Hx; apply (CS1 (TP_A + -150) 1 x Hx); lia))|].
  split; [exact (STAT69 _ _ TVO6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; intros x Hx; apply (CS1 TEV_ONCE 4 x Hx); lia))|].
  split; [exact (STAT69 _ _ TVR6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; intros x Hx; apply (CS1 TEV_RET 4 x Hx); lia))|].
  split; [exact (STAT69 _ _ TVG6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; intros x Hx; apply (CS1 TEV_REG 8 x Hx); lia))|].
  split; [exact (STAT69 _ _ CBC6 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; intros x Hx; apply (CS1 (TP_A + -96) 8 x Hx); lia))|].
  split; [exact (BLK69 H 8 _ (INL3 _ ltac:(do 5 right; left; reflexivity)) DH1 DH2 HC6 ltac:(cbn; lia))|].
  split; [exact (BLK69 N 32 _ (INL3 _ ltac:(left; reflexivity)) DN1 DN2 NC6 ltac:(cbn; lia))|].
  split; [exact (BLK69 G 16 _ (INL3 _ ltac:(do 4 right; left; reflexivity)) DG1 DG2 GC6 ltac:(cbn; lia))|].
  split; [exact (BLK69 LK 40 _ (INL3 _ ltac:(do 2 right; left; reflexivity)) DL1 DL2 LKC6 ltac:(cbn [cells_size csize Nat.add mutex_cells]; lia))|].
  exact (BLK69 D 32 _ (INL3 _ ltac:(right; left; reflexivity)) DD1 DD2 DC6 ltac:(cbn; lia)).
Qed.
End EgsiFirst.
