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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem Fz_kit Fz_chk Fz_M_malloc Fz_env Fz_mkit Fz_M_free Fz_M_cleanse.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_CRYPTO_clear_free : Z := 0x1fc578.
Definition SITE_ccf_cleanse : Z := 0x1fc5b0.

(* [comment removed for export] *)
Definition ccf_s0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p len lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ccf_cleanse) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a3
                 (Z_to_bv 64 p) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 a2 (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OPENSSL_cleanse) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ccf_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p len lo : Z),
  0 < p < 2^63 -> 0 < len < 2^63 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SEGTOP_A <= lo -> mem_inv asegs m ->
  evt asegs (ccf_s0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p len lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_clear_free) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hp Hl ST HLO HIMG MI. unfold e_CRYPTO_clear_free, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 40%nat ST. carve_frame 8%nat ST.
  do 7 zstep. zstep. ifF. do 3 zstep. zstep. ifF. do 2 zstep.
  unfold ccf_s0_post, SITE_ccf_cleanse, e_OPENSSL_cleanse. apply evt_done.
  lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -48) [CB 8 ?j] |- _ => exists j; eexists end.
  split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [| eassumption].
  lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -48) [CB 8 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -40) ?cs |- _ =>
    pose proof (rw_cells_app mm (bv_unsigned sp + -48) [CB 8 j] cs) as X; cbn [cells_size csize Nat.add app] in X;
    replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in X by lia; exact (proj2 X (conj H1 H2)) end.
Qed.

(* [comment removed for export] *)
Definition ccf_s1_post (ra sp gp tp t0 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' : word) (m' : mem),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 e_CRYPTO_free) t2 s0 s1 (Z_to_bv 64 p) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma ccf_s1_walk : forall ra0 ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p lo : Z) (j : list byte),
  0 < p < 2^63 ->
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp + -48 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m CL_FREE_IMPL [C8 (Z_to_bv 64 e_CRYPTO_free)] -> img_untouched m -> mem_inv asegs m ->
  evt asegs (ccf_s1_post ra sp gp tp t0 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ccf_cleanse) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros Hp ST HLO HIMG SPH FR FIMP UT MI. unfold SITE_ccf_cleanse, e_CRYPTO_free, CL_FREE_IMPL, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia.
  do 4 zstep. zstep. ifT.
  do 7 zstep.
  release_frame FR ST SP.
  zstep.
  unfold ccf_s1_post, e_free. apply evt_done. do 2 eexists. split; [subst SP; rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (unsigned_lit SP) by lia. replace (SP - 48) with (SP + -48) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CClearFree.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRC : free_contract RT.
Hypothesis C_CL : openssl_cleanse_env_stmt RT.

(* [comment removed for export] *)
Definition crypto_clear_free_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n len lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 len -> tp = Z_to_bv 64 0xba3ef0 ->
  In (p, n) (rt_live RT Σ) -> 1 <= len <= n -> len < 2^40 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 48 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_clear_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_clear_free m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ cl_env m' lb canary) c
       /\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_clear_free_cps : crypto_clear_free_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n len lo outer lb canary
    FDO MST -> -> -> Hin Hlen Hl40 ART0 MI0 CALL HSTK CTX UWC TAIL ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (Pp0 & PLO & PIMG).
  assert (Pp63 : 0 < p < 2^63) by (unfold USTACK_TOP, STACK_WIN in *; lia).
  cl_eu usp (-48) EU1.
  (* [comment removed for export] *)
  pose proof (ccf_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p len lo
                Pp63 ltac:(lia) ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  (* [comment removed for export] *)
  assert (OFF : forall x, cl_cell x -> ~ (p <= x < p + len)).
  { intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)). unfold SEGTOP_A in *. lia. }
  apply (C_CL Σ PMc (Z_to_bv 64 SITE_ccf_cleanse) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp a3 (Z_to_bv 64 p) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
           a2 (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p len lo lb canary FDO MST eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold USTACK_TOP, STACK_WIN in *; lia) ltac:(lia)
           (live_checked_dst RT AF Σ m1 _ p n p len ART1 Hin ltac:(lia) ltac:(lia) ltac:(lia)) OFF ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ZER2 & ENV2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ccf_cleanse) in Hc2' by (unfold SITE_ccf_cleanse; lia).
  (* [comment removed for export] *)
  assert (AG2 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia | lia]. }
  cl_keep FR1 AG2 WM2 FR2.
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  pose proof (ccf_s1_walk (Z_to_bv 64 SITE_ccf_cleanse) ra sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp a3 (Z_to_bv 64 p) b1 b2 b3 b4 b5 b6 b7 a2
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 p lo j Pp63 ST2 ltac:(fold usp; unfold RT_STACK in *; lia) HLOI ltac:(fold usp; unfold USTACK_TOP in *; lia)
                FR2 (cl_env_fimp m2 lb canary ENV2) UT2 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (a1' & m3 & -> & MU3 & WM3 & MI3 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3.
  pose proof (cl_seg_ART RT AF Σ m2 m3 usp 48 [] ART2 ltac:(lia) ltac:(lia) MU3 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM3) as ART3.
  pose proof (cl_seg_pres RT AF Σ m2 m3 usp 48 [] ART2 ltac:(lia) ltac:(lia) MU3) as PR3.
  pose proof (cl_env_seg _ m2 m3 lb canary ENV2 MU3 ltac:(cl_fp_lia)) as ENV3.
  assert (AG03 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros a Ha. cbv beta in Ha. rewrite (PR3 a ltac:(left; exact Ha) I). rewrite (PRES2 a ltac:(left; lia) ltac:(lia)). exact (AG1 a Ha). }
  (* [comment removed for export] *)
  apply (FRC Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) u0 (Z_to_bv 64 e_CRYPTO_free) u2 s0 s1 (Z_to_bv 64 p) a1' b2 b3 b4 b5 b6 b7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 p n lo FDO MST Hin eq_refl eq_refl ART3 MI3).
  { unfold call_ok. split; [exact ST3|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact SPT | exact SPA]. }
  { right. exists outer. split; [split; [exact TAIL | exact (proj2 CTX)] | exact (uw_chain_agree outer m m3 sp s0 UWC AG03)]. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ' & v & Hc4 & LV & FRS & SP0 & CR & CG).
  apply Hk. exists Σ', v. split; [| exact (conj LV (conj FRS (conj SP0 (conj CR CG))))].
  apply (ASTA_conseq RT Σ' PMc _ _ c4 Hc4). intros ms (m4 & RS & AFT & PRES). exists m4.
  split; [exact RS|]. split; [exact AFT|].
  split.
  { intros a Ha. rewrite (PRES a Ha).
    assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV; intros e He; exact (live_remove_sub _ _ _ He) | auto | lia]).
    rewrite LV in Ha. pose proof (removed_apart RT AF Σ m p n usp _ ART0 Hin ltac:(lia) Ha) as NP.
    rewrite (PR3 a Ha0 I).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha0); [auto | auto | lia]) ltac:(lia)).
    exact (PR1 a Ha0 I). }
  exact (cl_env_pres _ _ _ m3 m4 lb canary ENV3 PRES).
Qed.

End CClearFree.
