(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem Fz_kit Fz_chk Fz_M_malloc Fz_env.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition cfree_post (ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a4' : word) (m' : mem),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 e_CRYPTO_free) t2 s0 s1 a0 a1 a2 (Z_to_bv 64 e_CRYPTO_free) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma cfree_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 ->
  ro_cells asegs m CL_FREE_IMPL [C8 (Z_to_bv 64 e_CRYPTO_free)] -> img_untouched m -> mem_inv asegs m ->
  evt asegs (cfree_post ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_free) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG SPH FIMP UT MI. unfold e_CRYPTO_free, CL_FREE_IMPL, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 16, SP)]) by ut_fp_lia.
  carve_frame 16%nat ST.
  do 8 zstep. zstep. ifT.
  do 3 zstep.
  release_frame FR ST SP.
  zstep.
  unfold cfree_post, e_free. apply evt_done. do 2 eexists. split; [subst SP; rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (unsigned_lit SP) by lia. replace (SP - 16) with (SP + -16) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CFree.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRC : free_contract RT.
Hypothesis FRN : free_null_contract RT.

(* [comment removed for export] *)
Definition crypto_free_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0xba3ef0 -> In (p, n) (rt_live RT Σ) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_free m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ cl_env m' lb canary) c
       /\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_free_cps : crypto_free_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo outer lb canary
    FDO MST -> -> Hin ART0 MI0 CALL CTX UWC TAIL ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (cfree_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI ltac:(fold usp; unfold USTACK_TOP in *; lia) (cl_env_fimp m lb canary ENV) UT MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a4' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  (* [comment removed for export] *)
  apply (FRC Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 (Z_to_bv 64 e_CRYPTO_free) t2 s0 s1 (Z_to_bv 64 p) a1 a2 (Z_to_bv 64 e_CRYPTO_free) a4' a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p n lo FDO MST Hin eq_refl eq_refl ART1 MI1).
  { unfold call_ok. split; [exact ST1|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact SPT | exact SPA]. }
  { right. exists outer. split; [split; [exact TAIL | exact (proj2 CTX)] | exact (uw_chain_agree outer m m1 sp s0 UWC AG1)]. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ' & v & Hc2 & LV & FRS & SP0 & CR & CG).
  apply Hk. exists Σ', v. split; [| exact (conj LV (conj FRS (conj SP0 (conj CR CG))))].
  apply (ASTA_conseq RT Σ' PMc _ _ c2 Hc2). intros ms (m2 & RS & AFT & PRES). exists m2.
  split; [exact RS|]. split; [exact AFT|].
  split.
  { intros a Ha. rewrite (PRES a Ha). apply PR1; [| exact I].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV; intros e He; exact (live_remove_sub _ _ _ He) | auto | lia]. }
  exact (cl_env_pres _ _ _ m1 m2 lb canary ENV1 PRES).
Qed.

(* [comment removed for export] *)
Definition crypto_free_null_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_free m)))
    (fun c => exists (v : word),
       ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after RT Σ (bv_unsigned sp) lo m m'
           /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ cl_env m' lb canary) c).

Theorem crypto_free_null_cps : crypto_free_null_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> -> ART0 MI0 CALL CTX UWC TAIL ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (cfree_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI ltac:(fold usp; unfold USTACK_TOP in *; lia) (cl_env_fimp m lb canary ENV) UT MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a4' & m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  apply (FRN Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 (Z_to_bv 64 e_CRYPTO_free) t2 s0 s1 (Z_to_bv 64 0) a1 a2 (Z_to_bv 64 e_CRYPTO_free) a4' a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST eq_refl eq_refl ART1 MI1).
  { unfold call_ok. split; [exact ST1|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact SPT | exact SPA]. }
  { right. exists outer. split; [split; [exact TAIL | exact (proj2 CTX)] | exact (uw_chain_agree outer m m1 sp s0 UWC AG1)]. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (v & Hc2).
  apply Hk. exists v.
  apply (ASTA_conseq RT Σ PMc _ _ c2 Hc2). intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & _). exists m2.
  split; [exact RS|]. split; [exact (conj ART2 (conj MI2 (conj (wmono_trans asegs _ _ _ WM1 WM2) ST2)))|].
  assert (PRES' : rt_pres (rt_live RT Σ) (rt_frames RT Σ) usp m1 m2) by (intros a Ha; apply PRES; [exact Ha | lia]).
  split; [intros a Ha; rewrite (PRES' a Ha); exact (PR1 a Ha I)|].
  exact (cl_env_pres _ _ _ m1 m2 lb canary ENV1 PRES').
Qed.

End CFree.
