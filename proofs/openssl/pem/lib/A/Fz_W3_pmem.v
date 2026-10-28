(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_malloc Fz_M_free Fz_M_cleanse Fz_M_clear_free Fz_M_secure Fz_W1_defs Fz_W1_ctrl Fz_W3_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

Definition PM_FILE : Z := 0xa18c0.
Lemma land1_odd : forall a, Z.land a 1 = (if Z.odd a then 1 else 0).
Proof. intros a. rewrite <- Zmod_odd. exact (Z.land_ones a 1 ltac:(lia)). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pm_post (ra sp gp tp t0 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (flags lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t1' : word) (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 a0 (wz PM_FILE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz (if Z.odd flags then e_CRYPTO_secure_malloc else e_CRYPTO_malloc)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma pm_walk : forall ra sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (flags lo : Z),
  lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  0 <= flags < 2 ^ 32 -> mem_inv asegs m ->
  evt asegs (pm_post ra sp gp (wz TP_A) t0 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc flags lo m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 (wz flags) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_PEM_MALLOC) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT FL MI. unfold FZ_PEM_MALLOC, TP_A, pm_post in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 16, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 16, SP)]) by sh_fp_lia.
  assert (EUf : bv_unsigned (Z_to_bv 64 flags) = flags) by (apply unsigned_lit; lia).
  th_frame 16%nat [8; 8]%nat ST.
  zstep. zstep. zstep. zstep. zstep. rewrite (land1_odd flags).
  destruct (Z.odd flags).
  - zstep. th_if_lit. zstep. zstep. zstep. zstep. th_release FR SP. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned. unfold e_CRYPTO_secure_malloc, PM_FILE. apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption.
  - zstep. th_if_lit. zstep. zstep. zstep. zstep. th_release FR SP. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned. unfold e_CRYPTO_malloc, PM_FILE. apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition pf_post (ra sp gp tp t0 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (flags lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t1' : word) (m' : mem),
    ms = (if Z.odd flags
          then MS (mkR ra sp gp tp t0 t1' t2 s0 s1 a0 a2 (wz PM_FILE) a3 (wz PM_FILE) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_CRYPTO_secure_clear_free) fc None m' (seg_rom asegs)
          else MS (mkR ra sp gp tp t0 t1' t2 s0 s1 a0 (wz PM_FILE) a3 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_CRYPTO_free) fc None m' (seg_rom asegs))
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma pf_walk : forall ra sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (flags lo : Z),
  lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  0 <= flags < 2 ^ 32 -> mem_inv asegs m ->
  evt asegs (pf_post ra sp gp (wz TP_A) t0 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc flags lo m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 (wz flags) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_PEM_FREE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT FL MI. unfold FZ_PEM_FREE, TP_A, pf_post in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 16, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 16, SP)]) by sh_fp_lia.
  assert (EUf : bv_unsigned (Z_to_bv 64 flags) = flags) by (apply unsigned_lit; lia).
  th_frame 16%nat [8; 8]%nat ST.
  zstep. zstep. zstep. zstep. zstep. rewrite (land1_odd flags).
  destruct (Z.odd flags).
  - zstep. th_if_lit. zstep. zstep. zstep. zstep. zstep. zstep. th_release FR SP. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned. unfold e_CRYPTO_secure_clear_free, PM_FILE. apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption.
  - zstep. th_if_lit. zstep. zstep. zstep. zstep. zstep. th_release FR SP. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned. unfold e_CRYPTO_free, PM_FILE. apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition cm0_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (a1' a2' a3' : word) (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma cm0_walk : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)] -> mem_inv asegs m ->
  evt asegs (cm0_post ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_CRYPTO_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT MIMP MI. unfold e_CRYPTO_malloc, TP_A, cm0_post, G_MALLOC_IMPL in *.
  pose proof (got_cmalloc_ut m UT) as GOT. unfold G_GOT_CMALLOC, e_CRYPTO_malloc in GOT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 48, SP)]) by sh_fp_lia.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 5 zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. th_if_lit. zstep. th_if_lit. zstep.
  do 5 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition scf0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma scf0_walk : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m -> mem_inv asegs m ->
  evt asegs (scf0_post ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_CRYPTO_secure_clear_free) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT MI. unfold e_CRYPTO_secure_clear_free, TP_A, scf0_post in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 48, SP)]) by sh_fp_lia.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 5 zstep. zstep.
  zstep. th_if_lit.
  do 5 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma outside_latch : forall LBL x, outside (lib_W LBL) x -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x.
Proof.
  intros LBL x Ho. unfold lib_W, LIB_W in Ho. cbn [outside app] in Ho. destruct Ho as (_ & _ & X & _). cbn. split; [| exact I]. unfold G_ALLOW_CUST. clear - X. lia.
Qed.

Lemma rw_CB_len' : forall (m : mem) a n bs, rw_cells asegs m a [CB n bs] -> length bs = n.
Proof. intros m a n bs [[WF _] _]. cbn in WF. exact (proj1 WF). Qed.

Section CPmem.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis C_CSM : crypto_secure_malloc_env_stmt RT.
Hypothesis C_CF : crypto_free_env_stmt RT.
Hypothesis C_CFN : crypto_free_null_env_stmt RT.
Hypothesis C_SCF : crypto_secure_clear_free_env_stmt RT.
Hypothesis HCG : cg_sub [(SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cm_malloc, e_malloc)] FZ_SITES FZ_CALLS.

(* [comment removed for export] *)
Lemma libenv_keep_latch : forall Σ (m m' : mem) LBL E usp,
  ART RT Σ m -> libenv m LBL E -> incl_live LBL (rt_live RT Σ) ->
  (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] (bv_unsigned a) -> m' a = m a) ->
  libenv m' LBL E.
Proof using AF libenv_agree libenv_fp_where.
  intros Σ m m' LBL E usp ART0 LE INCL AG. eapply libenv_agree; [exact LE|]. intros a Ha.
  destruct (libenv_fp_where _ _ Ha) as [(_ & CS & NC)|(p & n & Hin & Hp)].
  - apply AG; [apply acl_static; exact CS|]. cbn. split; [| exact I]. intros R. apply NC. exists G_ALLOW_CUST, (G_ALLOW_CUST + 1). split; [unfold CL_CELLS; cbn; tauto| exact R].
  - apply AG; [apply (acl_live _ _ _ p n); [exact (INCL _ Hin)| exact Hp]|]. cbn. split; [| exact I].
    pose proof (af_live_range RT AF Σ m p n ART0 (INCL _ Hin)) as (_ & _ & R). unfold G_ALLOW_CUST, SEGTOP_A in *. lia.
Qed.
Lemma sec_off_keep_latch : forall Σ (m m' : mem) usp,
  sec_off m -> (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] (bv_unsigned a) -> m' a = m a) ->
  sec_off m'.
Proof.
  intros Σ m m' usp SEC AG. apply (sec_off_agree m m' SEC). intros a Ha. apply AG; [apply acl_static; rewrite Ha; exact sec_init_static|].
  cbn. rewrite Ha. unfold SEC_INIT, G_ALLOW_CUST. split; [lia| exact I].
Qed.

Theorem pem_malloc_proof : pem_malloc_stmt RT libenv FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL E n flags
         FDO MST -> -> -> Hn FL LE INCL ART0 MI0 CALL HSTK CLE SEC CTX UWC CGH TL1 TL2 Hlen Hcr.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, PMAL_STACK in *; lia).
  assert (HLO1 : lo <= usp - 16) by (clear - HSTK; unfold RT_STACK, PMAL_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (pm_walk ra sp gp t0 t1 t2 s0 s1 (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags lo HLO1 HLOS SPH ST UT FL MI0) as W0.
  fold usp in W0. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  assert (LE1 : libenv m1 LBL E) by (eapply (libenv_keep_latch Σ m m1); [exact ART0| exact LE| exact INCL| intros a Ha _; exact (PR1 a Ha I)]).
  assert (SEC1 : sec_off m1) by (eapply (sec_off_keep_latch Σ m m1); [exact SEC| intros a Ha _; exact (PR1 a Ha I)]).
  pose proof (cg_has_of_sub _ _ _ _ _ CGH HCG) as CGB.
  (* [comment removed for export] *)
  assert (FIN : forall c2,
    (exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp (wz TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m1 m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m1 m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ wr_at asegs m' p n /\ acc asegs m' p n) c2
       /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ) ->
    realizes asegs c2 T).
  { intros c2 (Σ' & p & Hc2 & LV' & FRS' & SP' & CR' & P0 & P16 & PTOP & CG'). apply Hk.
    destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & CLE2 & WR & ACC) & Hc2'). clear Hc2.
    destruct (wr_at_rw_CB m2 p n WR ltac:(lia)) as [junk JC].
    exists Σ', p, junk. split; [| exact (conj LV' (conj FRS' (conj SP' (conj CR' (conj CG' (conj P0 (conj P16 PTOP)))))))].
    eapply ASTA_conseq; [exact Hc2'|]. cbv beta. intros ms <-. exists (Z_to_bv 64 p), m2. fold usp in PRES.
    assert (AG02 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] (bv_unsigned x) -> m2 x = m x).
    { intros x Hx Ho. rewrite (PRES x Hx Ho). apply PR1; [exact Hx | exact I]. }
    split; [exact RS|]. split; [exact (conj ART2 (conj MI2 ST2))|].
    split; [intros a Ha Ho; exact (AG02 a Ha (outside_latch _ _ Ho))|]. split; [exact CLE2|].
    split; [reflexivity|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
    split; [exact (libenv_keep_latch Σ m m2 LBL E usp ART0 LE INCL AG02)|]. split; [exact (sec_off_keep_latch Σ m m2 usp SEC AG02)|].
    split; [exact (rw_CB_len' _ _ _ _ JC)| exact JC]. }
  destruct (Z.odd flags).
  - apply (C_CSM Σ PMc ra sp gp (wz TP_A) t0 t1' t2 s0 s1 (wz n) (wz PM_FILE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo outer (Z_to_bv 8 1) canary
             FDO MST eq_refl eq_refl ltac:(clear - Hn; lia) ART1 MI1 CO1 ltac:(clear - HSTK; unfold PMAL_STACK in HSTK; lia) (conj TL2 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) TL1 CGB Hlen Hcr CLE1 SEC1).
    { exact Hc1'. }
    intros c2 (Σ' & p & Hc2 & REST). apply FIN. exists Σ', p. split; [| exact REST].
    eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & RA & PRES & CLE2 & _ & WR & ACC). exists m2.
    split; [exact RS|]. split; [exact RA|]. split; [exact PRES|]. split; [exact CLE2|]. exact (conj WR ACC).
  - apply (C_CM Σ PMc ra sp gp (wz TP_A) t0 t1' t2 s0 s1 (wz n) (wz PM_FILE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo outer (Z_to_bv 8 1) canary
             FDO MST eq_refl eq_refl ltac:(clear - Hn; lia) ART1 MI1 CO1 ltac:(clear - HSTK; unfold PMAL_STACK in HSTK; lia) (conj TL1 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) CGB Hlen Hcr CLE1).
    { exact Hc1'. }
    intros c2 (Σ' & p & Hc2 & REST). apply FIN. exists Σ', p. split; [| exact REST].
    eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & RA & PRES & CLE2 & WR & ACC). exists m2.
    split; [exact RS|]. split; [exact RA|]. split; [exact PRES|]. split; [exact CLE2|]. exact (conj WR ACC).
Qed.

(* [comment removed for export] *)
Lemma munch_below : forall (m1 m2 m3 : mem) usp d1 d2 d, munch [(usp - d1, usp)] m1 m2 -> munch [(usp - d2, usp)] m2 m3 -> d1 <= d -> d2 <= d -> munch [(usp - d, usp)] m1 m3.
Proof.
  intros m1 m2 m3 usp d1 d2 d M1 M2 H1 H2. apply (munch_trans _ m1 m2 m3).
  - eapply munch_weaken; [| exact M1]. intros x Hx. cbn in Hx |- *. split; [lia| exact I].
  - eapply munch_weaken; [| exact M2]. intros x Hx. cbn in Hx |- *. split; [lia| exact I].
Qed.

Theorem pem_malloc0_proof : pem_malloc0_stmt RT libenv.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL E flags
         FDO MST -> -> -> FL LE INCL ART0 MI0 CALL HSTK CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 176 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, PMAL_STACK in *; lia).
  assert (HLO1 : lo <= usp - 176) by (clear - HSTK; unfold RT_STACK, PMAL_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (pm_walk ra sp gp t0 t1 t2 s0 s1 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags lo ltac:(lia) HLOS SPH ST UT FL MI0) as W0.
  fold usp in W0. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (ut_munch _ m m1 UT MU1 ltac:(ut_fp_lia)) as UT1.
  (* [comment removed for export] *)
  assert (FIN : forall c2 (a1' a2' a3' t1'' : word) (m2 : mem),
    munch [(usp - 176, usp)] m m2 -> wmono asegs m m2 -> mem_inv asegs m2 -> stk asegs m2 lo usp ->
    ASTA RT Σ PMc (eq (MS (mkR ra sp gp (wz TP_A) t0 t1'' t2 s0 s1 (wz 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m2 (seg_rom asegs))) c2 ->
    realizes asegs c2 T).
  { intros c2 a1' a2' a3' t1'' m2 MU2 WM2 MI2 ST2 Hc2. apply Hk. exists Σ.
    pose proof (cl_seg_ART RT AF Σ m m2 usp 176 [] ART0 ltac:(lia) ltac:(lia) MU2 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
    pose proof (cl_seg_pres RT AF Σ m m2 usp 176 [] ART0 ltac:(lia) ltac:(lia) MU2) as PR2.
    split; [| repeat split; try reflexivity; clear; lia].
    eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms <-. exists (Z_to_bv 64 0), m2.
    split; [do 16 eexists; reflexivity|]. split; [exact (conj ART2 (conj MI2 ST2))|].
    split; [intros a Ha _; exact (PR2 a Ha I)|]. split; [exact (cl_env_seg _ m m2 _ canary CLE MU2 ltac:(cl_fp_lia))|].
    split; [reflexivity|]. split; [exact WM2|].
    split; [exact (libenv_keep_latch Σ m m2 LBL E usp ART0 LE INCL (fun a Ha _ => PR2 a Ha I))| exact (sec_off_keep_latch Σ m m2 usp SEC (fun a Ha _ => PR2 a Ha I))]. }
  destruct (Z.odd flags).
  - (* [comment removed for export] *)
    pose proof (sec_off_agree m m1 SEC (fun a Ha => MU1 a ltac:(cbn; rewrite Ha; unfold SEC_INIT; split; [clear - HLO1 HLOS; lia| exact I]))) as SEC1.
    pose proof (sm_walk ra sp gp t0 t1' t2 s0 s1 (wz 0) (wz PM_FILE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo ltac:(clear - HLO1; lia) HLOS SPH ST1 UT1 SEC1 MI1) as W1.
    fold usp in W1. cl_lift W1 Hc1' c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & -> & MU2 & WM2 & MI2 & ST2) & Hc2'). clear Hc2 Hc1'. fold usp in MU2, ST2.
    pose proof (ut_munch _ m1 m2 UT1 MU2 ltac:(ut_fp_lia)) as UT2.
    pose proof (cm0_walk ra sp gp t0 t1' t2 s0 s1 (wz PM_FILE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo ltac:(clear - HLO1; lia) HLOS SPH ST2 UT2
                  (cl_env_mimp _ _ _ (cl_env_seg _ m m2 _ canary CLE (munch_below m m1 m2 usp 16 160 160 MU1 MU2 ltac:(lia) ltac:(lia)) ltac:(cl_fp_lia))) MI2) as W2.
    fold usp in W2. cl_lift W2 Hc2' c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (a1' & a2' & a3' & m3 & -> & MU3 & WM3 & MI3 & ST3) & Hc3'). clear Hc3 Hc2'. fold usp in MU3, ST3.
    exact (FIN c3 a1' a2' a3' t1' m3 (munch_below m m2 m3 usp 160 48 176 (munch_below m m1 m2 usp 16 160 160 MU1 MU2 ltac:(lia) ltac:(lia)) MU3 ltac:(lia) ltac:(lia))
             (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM1 WM2) WM3) MI3 ST3 Hc3').
  - (* [comment removed for export] *)
    pose proof (cm0_walk ra sp gp t0 t1' t2 s0 s1 (wz PM_FILE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo ltac:(clear - HLO1; lia) HLOS SPH ST1 UT1
                  (cl_env_mimp _ _ _ (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia))) MI1) as W1.
    fold usp in W1. cl_lift W1 Hc1' c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (a1' & a2' & a3' & m2 & -> & MU2 & WM2 & MI2 & ST2) & Hc2'). clear Hc2 Hc1'. fold usp in MU2, ST2.
    exact (FIN c2 a1' a2' a3' t1' m2 (munch_below m m1 m2 usp 16 48 176 MU1 MU2 ltac:(lia) ltac:(lia)) (wmono_trans asegs _ _ _ WM1 WM2) MI2 ST2 Hc2').
Qed.

Theorem pem_free_proof : pem_free_stmt RT libenv FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL E p n num flags
         FDO MST -> -> -> -> NUM N40 HN FL INP NLB LE INCL ART0 MI0 CALL HSTK CLE SEC CTX UWC CGH TL1 TL2 TL3.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM0 : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, PFREE_STACK in *; lia).
  assert (HLO1 : lo <= usp - 16) by (clear - HSTK; unfold RT_STACK, PFREE_STACK in *; lia). pose proof (proj1 (proj2 NUM0)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM0; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (pf_walk ra sp gp t0 t1 t2 s0 s1 (wz p) (wz num) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags lo HLO1 HLOS SPH ST UT FL MI0) as W0.
  fold usp in W0. unfold pf_post in W0. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  assert (SEC1 : sec_off m1) by (eapply (sec_off_keep_latch Σ m m1); [exact SEC| intros a Ha _; exact (PR1 a Ha I)]).
  (* [comment removed for export] *)
  assert (FIN : forall c2 (Σ' : rts RT) (v : word),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp (wz TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
        /\ rt_after_f RT Σ' (bv_unsigned sp) lo m1 m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m1 m' /\ cl_env m' (Z_to_bv 8 1) canary) c2 ->
    rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ' = rt_credit RT Σ -> rt_cg RT Σ' = rt_cg RT Σ ->
    realizes asegs c2 T).
  { intros c2 Σ' v Hc2 LV' FRS' SP' CR' CG'. apply Hk. exists Σ'. split; [| exact (conj LV' (conj FRS' (conj SP' (conj CR' CG'))))].
    eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & RA & PRES & CLE2). exists v, m2. fold usp in PRES.
    assert (AG02 : forall x : word, aclient (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> m2 x = m x).
    { intros x Hx. rewrite <- LV' in Hx. rewrite (PRES x Hx). apply PR1; [| exact I]. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV'; intros e He; exact (live_remove_sub _ _ _ He)| auto| lia]. }
    split; [exact RS|]. split; [exact RA|]. split; [intros a Ha _; exact (AG02 a Ha)|]. split; [exact CLE2|].
    split.
    - eapply libenv_agree; [exact LE|]. intros a Ha. destruct (libenv_fp_where _ _ Ha) as [(_ & CS & _)|(q & k & Hin & Hq)]; [apply AG02; apply acl_static; exact CS|].
      apply AG02. apply (acl_live _ _ _ q k); [| exact Hq]. apply live_remove_keep; [exact (INCL _ Hin)|]. cbn [fst]. intros ->.
      destruct (live_ne_apart RT AF Σ m p n p k ART0 INP (INCL _ Hin) ltac:(intros EE; apply NLB; rewrite EE; exact Hin)); lia.
    - apply (sec_off_agree m m2 SEC). intros a Ha. apply AG02. apply acl_static. rewrite Ha. exact sec_init_static. }
  destruct (Z.odd flags).
  - (* [comment removed for export] *)
    apply (C_SCF Σ PMc ra sp gp (wz TP_A) t0 t1' t2 s0 s1 (wz p) (wz num) (wz PM_FILE) a3 (wz PM_FILE) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p n num lo outer (Z_to_bv 8 1) canary
             FDO MST eq_refl eq_refl eq_refl INP NUM HN N40 ART1 MI1 CO1 ltac:(clear - HSTK; unfold PFREE_STACK in HSTK; lia)
             (conj TL3 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) TL1 TL2 CLE1 SEC1).
    { exact Hc1'. }
    intros c2 (Σ' & v & Hc2 & LV' & FRS' & SP' & CR' & CG'). apply (FIN c2 Σ' v); [| exact LV'| exact FRS'| exact SP'| exact CR'| exact CG'].
    eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & RA & PRES & CLE2 & _). exists m2. exact (conj RS (conj RA (conj PRES CLE2))).
  - (* [comment removed for export] *)
    apply (C_CF Σ PMc ra sp gp (wz TP_A) t0 t1' t2 s0 s1 (wz p) (wz PM_FILE) a3 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p n lo outer (Z_to_bv 8 1) canary
             FDO MST eq_refl eq_refl INP ART1 MI1 CO1 (conj TL1 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) TL2 CLE1).
    { exact Hc1'. }
    intros c2 (Σ' & v & Hc2 & LV' & FRS' & SP' & CR' & CG'). exact (FIN c2 Σ' v Hc2 LV' FRS' SP' CR' CG').
Qed.

Theorem pem_free_null_proof : pem_free_null_stmt RT libenv FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL E num flags
         FDO MST -> -> -> -> NUM FL LE INCL ART0 MI0 CALL HSTK CLE SEC CTX UWC CGH TL1 TL2 TL3.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM0 : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, PFREE_STACK in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - HSTK; unfold RT_STACK, PFREE_STACK in *; lia). pose proof (proj1 (proj2 NUM0)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM0; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (pf_walk ra sp gp t0 t1 t2 s0 s1 (wz 0) (wz num) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags lo ltac:(lia) HLOS SPH ST UT FL MI0) as W0.
  fold usp in W0. unfold pf_post in W0. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (ut_munch _ m m1 UT MU1 ltac:(ut_fp_lia)) as UT1.
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  (* [comment removed for export] *)
  assert (FIN : forall c2 (v : word) (m2 : mem),
    munch [(usp - 64, usp)] m m2 -> wmono asegs m m2 -> mem_inv asegs m2 -> stk asegs m2 lo usp ->
    ASTA RT Σ PMc (fun ms => ret_st ra sp gp (wz TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m2 ms) c2 ->
    realizes asegs c2 T).
  { intros c2 v m2 MU2 WM2 MI2 ST2 Hc2. apply Hk. exists Σ.
    pose proof (cl_seg_ART RT AF Σ m m2 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU2 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
    pose proof (cl_seg_pres RT AF Σ m m2 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU2) as PR2.
    split; [| repeat split; try reflexivity; clear; lia].
    eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms RS. exists v, m2.
    split; [exact RS|]. split; [exact (conj ART2 (conj MI2 ST2))|].
    split; [intros a Ha _; exact (PR2 a Ha I)|]. split; [exact (cl_env_seg _ m m2 _ canary CLE MU2 ltac:(cl_fp_lia))|].
    split; [exact WM2|].
    split; [exact (libenv_keep_latch Σ m m2 LBL E usp ART0 LE INCL (fun a Ha _ => PR2 a Ha I))| exact (sec_off_keep_latch Σ m m2 usp SEC (fun a Ha _ => PR2 a Ha I))]. }
  destruct (Z.odd flags).
  - (* [comment removed for export] *)
    pose proof (scf0_walk ra sp gp t0 t1' t2 s0 s1 (wz num) (wz PM_FILE) a3 (wz PM_FILE) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo ltac:(clear - HLO1; lia) HLOS SPH ST1 UT1 MI1) as W1.
    fold usp in W1. cl_lift W1 Hc1' c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & -> & MU2 & WM2 & MI2 & ST2) & Hc2'). clear Hc2 Hc1'. fold usp in MU2, ST2.
    apply (FIN c2 (wz 0) m2 (munch_below m m1 m2 usp 16 48 64 MU1 MU2 ltac:(lia) ltac:(lia)) (wmono_trans asegs _ _ _ WM1 WM2) MI2 ST2).
    eapply ASTA_conseq; [exact Hc2'|]. cbv beta. intros ms <-. do 16 eexists. reflexivity.
  - (* [comment removed for export] *)
    pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
    pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
    assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
    assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
    apply (C_CFN Σ PMc ra sp gp (wz TP_A) t0 t1' t2 s0 s1 (wz 0) (wz PM_FILE) a3 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo outer (Z_to_bv 8 1) canary
             FDO MST eq_refl eq_refl ART1 MI1 CO1 (conj TL1 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) TL2 CLE1).
    { exact Hc1'. }
    intros c2 (v & Hc2). apply Hk. exists Σ. split; [| repeat split; try reflexivity; clear; lia].
    eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & CLE2). exists v, m2. fold usp in PRES.
    assert (AG02 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m2 x = m x).
    { intros x Hx. rewrite (PRES x Hx). apply PR1; [exact Hx| exact I]. }
    split; [exact RS|]. split; [exact (conj ART2 (conj MI2 ST2))|]. split; [intros a Ha _; exact (AG02 a Ha)|]. split; [exact CLE2|].
    split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
    split; [exact (libenv_keep_latch Σ m m2 LBL E usp ART0 LE INCL (fun a Ha _ => AG02 a Ha))| exact (sec_off_keep_latch Σ m m2 usp SEC (fun a Ha _ => AG02 a Ha))].
Qed.
End CPmem.
