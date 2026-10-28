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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_malloc Fz_M_free Fz_M_cleanse Fz_M_clear_free Fz_M_secure Fz_M_zalloc Fz_W1_defs Fz_W1_ctrl Fz_W3_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

Definition EVP_FILE : Z := 0xa40c0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition en_post (ra sp gp tp t0 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t1' : word) (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (wz ECTX) (wz EVP_FILE) (wz 112) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma en_walk : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m -> mem_inv asegs m ->
  evt asegs (en_post ra sp gp (wz TP_A) t0 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_EVP_CTX_NEW) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT MI. unfold FZ_EVP_CTX_NEW, TP_A, en_post in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 16, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 16, SP)]) by sh_fp_lia.
  th_frame 16%nat [8; 8]%nat ST.
  do 10 zstep. th_release FR SP. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned. unfold e_CRYPTO_zalloc, ECTX, EVP_FILE. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition ef_post (ra sp gp tp t0 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t1' : word) (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 a0 (wz EVP_FILE) (wz 117) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma ef_walk : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m -> mem_inv asegs m ->
  evt asegs (ef_post ra sp gp (wz TP_A) t0 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_EVP_CTX_FREE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT MI. unfold FZ_EVP_CTX_FREE, TP_A, ef_post in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 16, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 16, SP)]) by sh_fp_lia.
  th_frame 16%nat [8; 8]%nat ST.
  do 9 zstep. th_release FR SP. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned. unfold e_CRYPTO_free, EVP_FILE. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma rw_CB_of_bytes_e : forall (m : mem) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) -> rw_cells asegs m a [CB (length bs) bs].
Proof.
  intros m a bs HB HW. split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]| cbn [cells_size csize]; rewrite Nat.add_0_r; exact HW].
Qed.

Section CEvp.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_CF : crypto_free_env_stmt RT.
Hypothesis C_CFN : crypto_free_null_env_stmt RT.
Hypothesis HCG : cg_sub [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] FZ_SITES FZ_CALLS.

Theorem evp_ctx_new_proof : evp_ctx_new_stmt RT FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary
         FDO MST -> ART0 MI0 CALL HSTK CLE CTX UWC CGH TL Hlen Hcr.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 16) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (en_walk ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HLO1 HLOS SPH ST UT MI0) as W0.
  fold usp in W0. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  assert (MC0 : mcost ECTX = 0) by reflexivity.
  apply (C_CZ Σ PMc ra sp gp (wz TP_A) t0 t1' t2 s0 s1 (wz ECTX) (wz EVP_FILE) (wz 112) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 ECTX lo outer (Z_to_bv 8 1) canary
           FDO MST eq_refl eq_refl ltac:(unfold ECTX; clear; lia) ART1 MI1 CO1 ltac:(clear - HSTK; lia) (conj TL (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1)
           (cg_has_of_sub _ _ _ _ _ CGH HCG) Hlen ltac:(rewrite MC0; exact Hcr) CLE1).
  { exact Hc1'. }
  intros c2 (Σ' & p & Hc2 & LV' & FRS' & SP' & CR' & P0 & P16 & PTOP & CG'). apply Hk. exists Σ', p.
  rewrite MC0, Z.sub_0_r in CR'. split; [| exact (conj LV' (conj FRS' (conj SP' (conj CR' (conj CG' (conj P0 (conj P16 PTOP)))))))].
  eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & CLE2 & WR & ACC & BZ). exists (Z_to_bv 64 p), m2. fold usp in PRES.
  split; [exact RS|]. split; [exact (conj ART2 (conj MI2 ST2))|].
  split; [intros a Ha Ho; rewrite (PRES a Ha Ho); exact (PR1 a Ha I)|]. split; [exact CLE2|].
  split; [reflexivity|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
  pose proof (rw_CB_of_bytes_e m2 p _ BZ ltac:(rewrite repeat_length, Z2Nat.id by (unfold ECTX; lia); exact WR)) as C. rewrite repeat_length in C. exact C.
Qed.

Theorem evp_ctx_free_proof : evp_ctx_free_stmt RT FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary p
         FDO MST -> -> INP ART0 MI0 CALL HSTK CLE CTX UWC CGH TL1 TL2.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 16) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (ef_walk ra sp gp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HLO1 HLOS SPH ST UT MI0) as W0.
  fold usp in W0. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  apply (C_CF Σ PMc ra sp gp (wz TP_A) t0 t1' t2 s0 s1 (wz p) (wz EVP_FILE) (wz 117) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p ECTX lo outer (Z_to_bv 8 1) canary
           FDO MST eq_refl eq_refl INP ART1 MI1 CO1 (conj TL1 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) TL2 CLE1).
  { exact Hc1'. }
  intros c2 (Σ' & v & Hc2 & LV' & FRS' & SP' & CR' & CG'). apply Hk. exists Σ'. split; [| exact (conj LV' (conj FRS' (conj SP' (conj CR' CG'))))].
  eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & RA & PRES & CLE2). exists v, m2. fold usp in PRES.
  split; [exact RS|]. split; [exact RA|].
  split; [| exact (conj CLE2 I)]. intros a Ha _. rewrite <- LV' in Ha. rewrite (PRES a Ha). apply PR1; [| exact I].
  apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV'; intros e He; exact (live_remove_sub _ _ _ He)| auto| lia].
Qed.

Theorem evp_ctx_free_null_proof : evp_ctx_free_null_stmt RT FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary
         FDO MST -> -> ART0 MI0 CALL HSTK CLE CTX UWC CGH TL1 TL2.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 16) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (ef_walk ra sp gp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HLO1 HLOS SPH ST UT MI0) as W0.
  fold usp in W0. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  apply (C_CFN Σ PMc ra sp gp (wz TP_A) t0 t1' t2 s0 s1 (wz 0) (wz EVP_FILE) (wz 117) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo outer (Z_to_bv 8 1) canary
           FDO MST eq_refl eq_refl ART1 MI1 CO1 (conj TL1 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) TL2 CLE1).
  { exact Hc1'. }
  intros c2 (v & Hc2). apply Hk.
  eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & CLE2). exists v, m2. fold usp in PRES.
  split; [exact RS|]. split; [exact (conj ART2 (conj MI2 ST2))|].
  split; [intros a Ha _; rewrite (PRES a Ha); exact (PR1 a Ha I)|]. split; [exact CLE2|]. exact (wmono_trans asegs _ _ _ WM1 WM2).
Qed.
End CEvp.
