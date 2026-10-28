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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem Fz_kit Fz_chk Fz_M_malloc Fz_env Fz_mkit Fz_M_free Fz_M_cleanse Fz_M_clear_free.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_CRYPTO_clear_realloc : Z := 0x1fc474.
Definition SITE_ccr_malloc : Z := 0x1fc51c.
Definition SITE_ccr_memcpy : Z := 0x1fc530.
Definition SITE_ccr_cfree : Z := 0x1fc544.

(* [comment removed for export] *)
Definition ccr_s0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p old num lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ccr_malloc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 p)
                 (Z_to_bv 64 num) a3 a4 a3 a4 a5 a6 a7 a4 a3 (Z_to_bv 64 old) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_malloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ccr_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p old num lo : Z),
  0 < p < 2^63 -> 0 < old <= num -> num < 2^63 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> SEGTOP_A <= lo -> mem_inv asegs m ->
  evt asegs (ccr_s0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p old num lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 old) (Z_to_bv 64 num) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_clear_realloc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hp Ho Hn ST HLO HIMG MI. unfold e_CRYPTO_clear_realloc, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 56%nat ST. carve_frame 8%nat ST.
  do 9 zstep. do 2 zstep. zstep. ifF. do 2 zstep. zstep. ifF. zstep. ifT. do 4 zstep.
  unfold ccr_s0_post, SITE_ccr_malloc, e_CRYPTO_malloc. apply evt_done.
  lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -64) [CB 8 ?j] |- _ => exists j; eexists end.
  split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [| eassumption].
  lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -64) [CB 8 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -56) ?cs |- _ =>
    pose proof (rw_cells_app mm (bv_unsigned sp + -64) [CB 8 j] cs) as X; cbn [cells_size csize Nat.add app] in X;
    replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in X by lia; exact (proj2 X (conj H1 H2)) end.
Qed.

(* [comment removed for export] *)
Definition ccr_s1_post (sp gp tp t0 t1 t2 s0' s2' s3' s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p old q : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ccr_memcpy) sp gp tp t0 t1 t2 s0' (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 p) (Z_to_bv 64 old) a3 a4 a5 a6 a7
                         s2' s3' (Z_to_bv 64 old) (Z_to_bv 64 q) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 e_asan_memcpy) fc None m (seg_rom asegs).

Lemma ccr_s1_walk : forall ra0 sp gp tp t0 t1 t2 s0' a1 a2 a3 a4 a5 a6 a7 s2' s3' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p old q : Z),
  0 < q < 2^63 -> mem_inv asegs m ->
  evt asegs (ccr_s1_post sp gp tp t0 t1 t2 s0' s2' s3' s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p old q m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' (Z_to_bv 64 p) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2' s3' (Z_to_bv 64 old) s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ccr_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until q. intros Hq MI. unfold SITE_ccr_malloc.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. ifF. do 4 zstep.
  unfold ccr_s1_post, SITE_ccr_memcpy, e_asan_memcpy. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ccr_s2_post (sp gp tp t0 t1 t2 s0' s2' s3' s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p old q : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ccr_cfree) sp gp tp t0 t1 t2 s0' (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 old) s3' s2' a4 a5 a6 a7
                         s2' s3' (Z_to_bv 64 old) (Z_to_bv 64 q) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 e_CRYPTO_clear_free) fc None m (seg_rom asegs).

Lemma ccr_s2_walk : forall ra0 sp gp tp t0 t1 t2 s0' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p old q : Z),
  mem_inv asegs m ->
  evt asegs (ccr_s2_post sp gp tp t0 t1 t2 s0' s2' s3' s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 F fc p old q m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' (Z_to_bv 64 old) (Z_to_bv 64 q) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ccr_memcpy) fc None m (seg_rom asegs)).
Proof.
  intros until q. intros MI. unfold SITE_ccr_memcpy.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 5 zstep.
  unfold ccr_s2_post, SITE_ccr_cfree, e_CRYPTO_clear_free. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ccr_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma ccr_s3_walk : forall ra0 ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo : Z) (j : list byte),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp + -64 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv asegs m ->
  evt asegs (ccr_s3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc q lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' (Z_to_bv 64 q) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ccr_cfree) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros ST HLO HIMG SPH FR MI. unfold SITE_ccr_cfree, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 3 zstep. do 8 zstep.
  release_frame FR ST SP.
  zstep.
  unfold ccr_s3_post. apply evt_done. eexists. split; [subst SP; rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (unsigned_lit SP) by lia. replace (SP - 64) with (SP + -64) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CClearRealloc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_CCF : crypto_clear_free_env_stmt RT.

(* [comment removed for export] *)
Definition crypto_clear_realloc_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n0 old num lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 old -> a2 = Z_to_bv 64 num -> tp = Z_to_bv 64 0xba3ef0 ->
  In (p, n0) (rt_live RT Σ) -> 1 <= old <= n0 -> old <= num <= 0x8000000 -> old < 2^40 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 64 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_clear_realloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ccr_malloc, e_CRYPTO_clear_realloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ccr_cfree, e_CRYPTO_clear_realloc)]
                      [(SITE_ccr_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ccr_cfree, e_CRYPTO_clear_free); (SITE_ccr_cfree, e_free)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost num <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_clear_realloc m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ wr_at asegs m' q num /\ acc asegs m' q num
           /\ (forall bs, bytes_at asegs m p bs -> Z.of_nat (length bs) = old -> bytes_at asegs m' q bs)) c
       /\ rt_live RT Σ' = (q, num) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost num /\ 0 < q /\ q mod 16 = 0 /\ q + num < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_clear_realloc_cps : crypto_clear_realloc_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 old num lo outer lb canary
    FDO MST -> -> -> -> Hin Hold Hnum Ho40 ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m p n0 ART0 Hin) as (Pp0 & PLO & PIMG).
  assert (Pp63 : 0 < p < 2^63) by (unfold USTACK_TOP, STACK_WIN in *; lia).
  cl_eu usp (-64) EU1.
  (* [comment removed for export] *)
  pose proof (ccr_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p old num lo
                Pp63 ltac:(lia) ltac:(lia) ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  assert (FRR : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m1 (usp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_CRYPTO_clear_realloc e_CRYPTO_malloc SITE_ccr_malloc m m1 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG1 FRR ltac:(rewrite EU1; fold usp; lia) SPT) as (CTX1 & UWC1).
  (* [comment removed for export] *)
  apply (C_CM Σ PMc (Z_to_bv 64 SITE_ccr_malloc) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 p) (Z_to_bv 64 num) a3 a4 a3 a4 a5 a6 a7
           a4 a3 (Z_to_bv 64 old) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 num lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ccr_malloc) by (unfold SITE_ccr_malloc; lia). exact CTX1. }
  { exact UWC1. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [In] in Hx |- *; tauto. }
  { exact Hlen. } { exact Hcr. } { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q & Hc2 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ENV2 & WR2 & ACC2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ccr_malloc) in Hc2' by (unfold SITE_ccr_malloc; lia).
  assert (INQ1 : In (q, num) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INP1 : In (p, n0) (rt_live RT Σ1)) by (rewrite LV1; right; exact Hin).
  pose proof (af_live_range RT AF Σ1 m2 q num ART2 INQ1) as (_ & QLO & _). rewrite SP1 in QLO.
  pose proof (af_live_disj RT AF Σ1 m2 q num p n0 [] (rt_live RT Σ) ART2 LV1 Hin) as QP.
  (* [comment removed for export] *)
  pose proof (ccr_s1_walk (Z_to_bv 64 SITE_ccr_malloc) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp b1 b2 b3 b4 b5 b6 b7 a4 a3 s5
                s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 p old q ltac:(unfold USTACK_TOP in *; lia) MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  destruct (wr_at_bytes m2 p old (wr_at_sub m2 p n0 p old (proj1 (af_acc_live RT AF Σ1 m2 p n0 ART2 INP1)) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (ob & OB & OBL).
  assert (CO2 : call_ok RT Σ1 m2 (Z_to_bv 64 (usp + -64)) lo).
  { fold usp in SPA. rewrite <- SP1 in LOW. cl_call_ok EU1 ST2 LOW SPA 4. }
  apply (MCP Σ1 PMc (Z_to_bv 64 SITE_ccr_memcpy) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 p) (Z_to_bv 64 old)
           b3 b4 b5 b6 b7 a4 a3 (Z_to_bv 64 old) (Z_to_bv 64 q) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 q p ob lo FDO MST eq_refl eq_refl
           ltac:(rewrite OBL; reflexivity) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP, STACK_WIN in *; lia) ltac:(rewrite OBL; exact Ho40) OB).
  { rewrite OBL. exact (live_checked_src RT AF Σ1 m2 _ lo p n0 p old ART2 INP1 ltac:(lia) ltac:(lia) ltac:(rewrite SP1; exact LOW)). }
  { rewrite OBL. exact (live_checked_dst RT AF Σ1 m2 _ q num q old ART2 INQ1 ltac:(lia) ltac:(lia) ltac:(lia)). }
  { rewrite OBL. destruct QP; [left | right]; lia. }
  { exact ART2. } { exact MI2. } { exact CO2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & CPY3) & Hc4'). clear Hc4.
  destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite OBL in PRES3. rewrite (ret_pc_even SITE_ccr_memcpy) in Hc4' by (unfold SITE_ccr_memcpy; lia).
  (* [comment removed for export] *)
  pose proof (ccr_s2_walk (Z_to_bv 64 SITE_ccr_memcpy) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 q) d1 d2 d3 d4 d5 d6 d7 a4 a3
                s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3 p old q MI3) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  assert (AG2 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. cbn [outside]. unfold G_ALLOW_CUST. split; [unfold USTACK_TOP, RT_STACK in *; lia | exact I]. }
  assert (AG3 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES3; [left; lia | unfold RT_STACK in *; lia]. }
  cl_keep FR1 AG2 WM2 FR2. cl_keep FR2 AG3 WM3 FR3.
  assert (AG03 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros a Ha. cbv beta in Ha. rewrite (AG3 usp (USTACK_TOP - usp) ltac:(lia) ltac:(lia) a ltac:(cbv beta; lia)).
    rewrite (AG2 usp (USTACK_TOP - usp) ltac:(lia) ltac:(lia) a ltac:(cbv beta; lia)). exact (AG1 a Ha). }
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m3 (usp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3). }
  destruct (cl_chain_call (rt_cg RT Σ) e_CRYPTO_clear_realloc e_CRYPTO_clear_free SITE_ccr_cfree m m3 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTX
              (proj1 CGH _ ltac:(right; right; left; reflexivity)) (proj2 CGH _ ltac:(right; right; left; reflexivity)) UWC AG03 FRR3
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTX3 & UWC3).
  assert (ENV3 : cl_env m3 (Z_to_bv 8 1) canary).
  { apply (cl_env_pres_ex _ _ _ q old m2 m3 (Z_to_bv 8 1) canary ENV2 PRES3).
    intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)). unfold SEGTOP_A in *.
    pose proof (af_live_range RT AF Σ1 m2 q num ART2 INQ1) as (_ & _ & QI). unfold SEGTOP_A in QI. lia. }
  (* [comment removed for export] *)
  rewrite <- CG1 in CTX3, CGH.
  apply (C_CCF Σ1 PMc (Z_to_bv 64 SITE_ccr_cfree) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 old) a3 a4
           d4 d5 d6 d7 a4 a3 (Z_to_bv 64 old) (Z_to_bv 64 q) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3 p n0 old lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           FDO MST eq_refl eq_refl eq_refl INP1 Hold Ho40 ART3 MI3).
  { fold usp in SPA. rewrite <- SP1 in LOW. cl_call_ok EU1 ST3 LOW SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ccr_cfree) by (unfold SITE_ccr_cfree; lia). exact CTX3. }
  { exact UWC3. }
  { rewrite (unsigned_lit SITE_ccr_cfree) by (unfold SITE_ccr_cfree; lia). apply (proj2 CGH). cbn [In]. tauto. }
  { exact ENV3. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ2 & v & Hc6 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & ENV4) & Hc6'). clear Hc6.
  destruct RS4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ccr_cfree) in Hc6' by (unfold SITE_ccr_cfree; lia).
  (* [comment removed for export] *)
  assert (FR4 : rw_cells asegs m4 (usp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FR3). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply PRES4. left. unfold USTACK_TOP in *. lia. }
  pose proof (ccr_s3_walk (Z_to_bv 64 SITE_ccr_cfree) ra sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 p) v e1 e2 e3 e4 e5 e6 e7 a4 a3 (Z_to_bv 64 old)
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 q lo j ST4 ltac:(fold usp; unfold RT_STACK in *; lia) HLOI
                ltac:(fold usp; unfold USTACK_TOP in *; lia) FR4 MI4) as W3.
  cl_lift W3 Hc6' c7 Hc7.
  assert (QNE : q <> p) by (destruct QP; lia).
  assert (LV2' : rt_live RT Σ2 = (q, num) :: live_remove p (rt_live RT Σ)) by (rewrite LV2, LV1; exact (live_remove_cons_ne p q num _ QNE)).
  apply Hk. exists Σ2, q.
  split; [| split; [exact LV2' | split; [rewrite FRS2; exact FRS1 | split; [rewrite SP2; exact SP1 | split; [rewrite CR2; exact CR1 |
            split; [exact Q0 | split; [exact Q16 | split; [exact QU | rewrite CG2; exact CG1]]]]]]]].
  apply (ASTA_conseq RT Σ2 PMc _ _ c7 Hc7). intros ms7 (m5 & -> & MU5 & WM5 & MI5 & ST5). exists m5. fold usp in MU5, ST5.
  split; [exists w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F4, fc4; reflexivity|].
  pose proof (cl_seg_ART RT AF Σ2 m4 m5 usp 64 [] ART4 ltac:(rewrite SP2, SP1; lia) ltac:(lia) MU5 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM5) as ART5.
  split; [exact (conj ART5 (conj MI5 ST5))|].
  assert (INQ2 : In (q, num) (rt_live RT Σ2)) by (rewrite LV2'; left; reflexivity).
  split.
  { intros a Ha Ho.
    assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (live_remove_sub _ _ _ He) | auto | lia]).
    pose proof (cl_split RT AF Σ m usp 64 _ ART0 ltac:(lia) ltac:(lia) Ha0) as N4.
    pose proof (newchunk_apart RT AF Σ Σ1 m2 q num usp _ ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Ha0) as NQ.
    rewrite (MU5 a ltac:(cbn [app outside]; split; [lia | exact I])).
    rewrite (PRES4 a ltac:(rewrite LV2', FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; right; exact He | auto | lia])).
    rewrite (PRES3 a ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha0); [intros e He; right; exact He | auto | lia]) ltac:(lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha0); [auto | auto | lia]) Ho).
    exact (PR1 a Ha0 I). }
  split; [apply (cl_env_seg _ m4 m5 (Z_to_bv 8 1) canary ENV4 MU5); cl_fp_lia|].
  pose proof (af_acc_live RT AF Σ2 m5 q num ART5 INQ2) as (WR5 & ACC5).
  split; [exact WR5|]. split; [exact ACC5|].
  intros bs Hbs Hbl.
  assert (Hb2 : bytes_at asegs m2 p bs).
  { apply (bytes_at_agree asegs m1 m2 p bs); [apply (bytes_at_agree asegs m m1 p bs Hbs)|].
    - intros a Ha. cbv beta in Ha. apply PR1; [| exact I]. right; right; left. exists p, n0. split; [exact Hin | lia].
    - intros a Ha. cbv beta in Ha. apply PRES2; [right; right; left; exists p, n0; split; [exact Hin | lia]|].
      cbn [outside]. unfold G_ALLOW_CUST, SEGTOP_A in *. split; [lia | exact I]. }
  assert (Ebs : bs = ob) by (apply (bytes_at_inj m2 p bs ob Hb2 OB); lia). subst bs.
  assert (Hb4 : bytes_at asegs m4 q ob).
  { apply (bytes_at_agree asegs m3 m4 q ob CPY3). intros a Ha. cbv beta in Ha. apply PRES4.
    right; right; left. exists q, num. split; [exact INQ2 | lia]. }
  apply (bytes_at_transport asegs _ m4 m5 q ob Hb4 MU5). cbn [app disjoint_from]. split; [left; lia | exact I].
Qed.

End CClearRealloc.
