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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_aligned Fz_M_aligned_array.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tslia ::= wp_tslia.
Notation TP_A := (0xba3ef0)%Z (only parsing).
(* [comment removed for export] *)
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ifF | ifT] end).

Definition e_anl : Z := 0x21a520.
Definition SITE_anl_aaa : Z := 0x21a574.      (* [comment removed for export] *)
Definition SITE_anl_memset : Z := 0x21a5c0.   (* [comment removed for export] *)
Definition NB_BYTES : Z := 32768.

(* [comment removed for export] *)
Definition anl_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_anl_aaa) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a1
                 a0 (Z_to_bv 64 64) (Z_to_bv 64 64) a1 (Z_to_bv 64 0x4c8c0) (Z_to_bv 64 160) a6 a7 a0 s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_aligned_alloc_array) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma anl_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (anl_w0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_anl) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_anl, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia.
  carve_frame 48%nat ST.
  zgo 0x201614.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold anl_w0_post, SITE_anl_aaa, e_CRYPTO_aligned_alloc_array. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR| assumption].
Qed.

(* [comment removed for export] *)
Definition anl_w1_post (sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fp : Z) (F : bvmap 5 word) (fc : bv 32)
    (q : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_anl_memset) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 fp)
                 (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 NB_BYTES) a3 a4 a5 a6 a7 (Z_to_bv 64 512) (Z_to_bv 64 q) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memset) fc None m (seg_rom asegs).

Lemma anl_w1 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (fp q : Z),
  0 < q -> q < 2^64 -> mem_inv asegs m ->
  evt asegs (anl_w1_post sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fp F fc q m)
    (MS (mkR (Z_to_bv 64 SITE_anl_aaa) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 fp)
             (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 512) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_anl_aaa) fc None m (seg_rom asegs)).
Proof.
  intros until q. intros Q0 QH MI. unfold SITE_anl_aaa in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zgo 0x1c1dbc.
  unfold anl_w1_post, SITE_anl_memset, e_asan_memset, NB_BYTES. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition anl_w2_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma anl_w2 : forall ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s0' s1' s2' s3' s4' : word)
    (F : bvmap 5 word) fc (m : mem) (q lo : Z),
  lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> 0 < q -> q < 2^64 ->
  stk asegs m lo (bv_unsigned sp + -48) ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] -> mem_inv asegs m ->
  evt asegs (anl_w2_post ra0 sp gp tp s0' s1' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc q lo m)
    (MS (mkR (Z_to_bv 64 SITE_anl_memset) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1
             a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 q) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_anl_memset) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH Q0 QH ST1 FR MI. unfold SITE_anl_memset in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zgo 0x21a5e0.
  release_frame FR ST1 SP.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold anl_w2_post. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

Section Anl.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis C_AAA : crypto_aligned_alloc_array_env_stmt RT.

Definition ANL_SITES : list (Z * Z) := [(SITE_anl_aaa, e_anl); (SITE_aa_memalign, e_CRYPTO_aligned_alloc)].
Definition ANL_CALLS : list (Z * Z) := [(SITE_anl_aaa, e_CRYPTO_aligned_alloc_array); (SITE_anl_aaa, e_CRYPTO_aligned_alloc); (SITE_aa_memalign, e_posix_memalign)].

(* [comment removed for export] *)
Definition anl_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (fp pb nb : Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 512 -> a1 = Z_to_bv 64 fp ->
  memalign_plain 64 NB_BYTES ->
  In (pb, nb) (rt_live RT Σ) -> nb <= 64512 -> pb <= fp -> fp + 8 <= pb + nb -> fp mod 8 = 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x230 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_anl (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) ANL_SITES ANL_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> 1 + mcost NB_BYTES <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_anl m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(fp, fp + 8)] m m'
           /\ cl_env m' lb canary
           /\ wr_at asegs m' q NB_BYTES /\ acc asegs m' q NB_BYTES
           /\ rw_cells asegs m' fp [C8 (Z_to_bv 64 q)]
           /\ bytes_at asegs m' q (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))) c
       /\ rt_live RT Σ' = (q, NB_BYTES) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 - mcost NB_BYTES
       /\ 0 < q /\ q mod 64 = 0 /\ q + NB_BYTES < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem anl_cps : anl_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer fp pb nb lb canary
    FDO MST -> -> -> MP INB NBS FP1 FP2 FPA ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-48) EU1.
  pose proof (wg_mcost_nonneg NB_BYTES) as MC1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m pb nb ART0 INB) as (PB0 & PBH & _).
  (* [comment removed for export] *)
  pose proof (anl_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 512) (Z_to_bv 64 fp) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(unfold RT_STACK in *; lia) ltac:(lia) ltac:(lia) UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG1) as UWF1.
  destruct (cl_chain_call (rt_cg RT Σ) e_anl e_CRYPTO_aligned_alloc_array SITE_anl_aaa m1 m1 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWF1 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_AAA Σ PMc (Z_to_bv 64 SITE_anl_aaa) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 fp)
           (Z_to_bv 64 512) (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 fp) (Z_to_bv 64 0x4c8c0) (Z_to_bv 64 160) a6 a7 (Z_to_bv 64 512) s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 512 64 fp pb nb lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(change (512 * 64) with NB_BYTES; exact MP) INB NBS FP1 FP2 FPA ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_anl_aaa) by (unfold SITE_anl_aaa; lia). destruct CTXc1 as [CS LK]. split; [| exact LK].
    apply (proj2 CGH). unfold SITE_anl_aaa. wp_in_lit. }
  { exact UWCc1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact Hfr. }
  { lia. }
  { change (512 * 64) with NB_BYTES. lia. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q & Hc2 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q64 & QU & CG1).
  change (512 * 64) with NB_BYTES in LV1, CR1, QU, Hc2.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ENV2 & FPC2 & WRq2 & ACCq2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_anl_aaa) in Hc2' by (unfold SITE_anl_aaa; lia).
  change (512 * 64) with NB_BYTES in WRq2, ACCq2.
  assert (INQ1 : In (q, NB_BYTES) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INB1 : In (pb, nb) (rt_live RT Σ1)) by (rewrite LV1; right; exact INB).
  pose proof (af_live_range RT AF Σ1 m2 q NB_BYTES ART2 INQ1) as (_ & QLO & _). rewrite SP1 in QLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 q NB_BYTES ART2 INQ1 ltac:(unfold NB_BYTES; lia)) as QHH.
  pose proof (af_live_disj RT AF Σ1 m2 q NB_BYTES pb nb [] (rt_live RT Σ) ART2 LV1 INB) as QP.
  assert (AG12 : forall a k, (usp + -48 <= a /\ a + k <= USTACK_TOP) -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H x Hx. cbv beta in Hx. apply PRES2; [left; lia | unfold NB_BYTES, USTACK_TOP, STACK_WIN in *; lia]. }
  assert (FR2 : rw_cells asegs m2 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply AG12. cbn [cells_size csize Nat.add]. unfold USTACK_TOP in *. lia. }
  assert (AG12u : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG12. lia. }
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AG12u) as UWF2.
  (* [comment removed for export] *)
  pose proof (anl_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 fp q
                Q0 ltac:(unfold NB_BYTES, USTACK_TOP in *; lia) MI2) as W1.
  fold usp in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & E3 & Hc3'). clear Hc3. unfold anl_w1_post in E3. subst ms3. fold usp in Hc3'.
  (* [comment removed for export] *)
  assert (CHK : checked_dst RT Σ1 m2 (Z_to_bv 64 (usp + -48)) q NB_BYTES).
  { split; [| split].
    - intros _. split; [exact ACCq2|]. left. exists q, NB_BYTES. split; [exact INQ1 | lia].
    - intros i Hi. apply (acl_live _ _ _ q NB_BYTES); [exact INQ1 | lia].
    - exact WRq2. }
  apply (MSET Σ1 PMc (Z_to_bv 64 SITE_anl_memset) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 fp)
           (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 NB_BYTES) b3 b4 b5 b6 b7 (Z_to_bv 64 512) (Z_to_bv 64 q) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
           F2 fc2 m2 q NB_BYTES (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl ltac:(unfold NB_BYTES, USTACK_TOP in *; lia) ltac:(unfold NB_BYTES; lia) CHK ART2 MI2).
  { assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW). fold usp in SPA. cl_call_ok EU1 ST2 LOW1 SPA 3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ZER4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_anl_memset) in Hc4' by (unfold SITE_anl_memset; lia).
  assert (AG24 : forall a k, ((usp + -48 <= a /\ a + k <= USTACK_TOP) \/ (pb <= a /\ a + k <= pb + nb)) -> agree_on (fun x => a <= x < a + k) m2 m4).
  { intros a k H x Hx. cbv beta in Hx. apply PRES4.
    - destruct H as [H|H]; [left; lia | apply (acl_live _ _ _ pb nb); [exact INB1 | lia]].
    - clear - H Hx QP NUM QLO LOW HSTK. unfold USTACK_TOP, STACK_WIN, RT_STACK in *. lia. }
  assert (FR4 : rw_cells asegs m4 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m2 m4 _ _ FR2); [| exact WM4]. apply AG24. left. cbn [cells_size csize Nat.add]. unfold USTACK_TOP in *. lia. }
  assert (FPC4 : rw_cells asegs m4 fp [C8 (Z_to_bv 64 q)]).
  { apply (rw_cells_agree asegs m2 m4 _ _ FPC2); [| exact WM4]. apply AG24. right. cbn [cells_size csize Nat.add]. lia. }
  assert (ENV4 : cl_env m4 lb canary).
  { apply (cl_env_pres_ex _ _ _ _ _ m2 m4 lb canary ENV2 PRES4). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)). unfold SEGTOP_A, STACK_WIN in *. lia. }
  assert (AG24u : agree_on (fun x => usp <= x < USTACK_TOP) m2 m4).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG24. left. lia. }
  pose proof (uw_chain_agree outer m2 m4 sp s0 UWF2 AG24u) as UWF4.
  (* [comment removed for export] *)
  pose proof (anl_w2 ra sp gp (Z_to_bv 64 TP_A) v0 v1 v2 (Z_to_bv 64 q) d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 fp) (Z_to_bv 64 512) s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
                s0 s1 s2 s3 s4 F4 fc4 m4 q lo ltac:(unfold RT_STACK in *; lia) ltac:(lia) ltac:(lia) Q0 ltac:(unfold NB_BYTES, USTACK_TOP in *; lia) ST4 FR4 MI4) as W2.
  fold usp in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & ST5) & Hc5'). clear Hc5.
  fold usp in ST5.
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 usp ART4 ltac:(rewrite SP1; lia)); [| exact WM5]. intros a Ha. apply MU5. exact I. }
  assert (AG45 : forall P, agree_on P m4 m5) by (intros P x _; apply MU5; exact I).
  apply Hk. exists Σ1, q.
  split; [| split; [exact LV1 | split; [exact FRS1 | split; [exact SP1 | split; [exact CR1 | split; [exact Q0 | split; [exact Q64 | split; [exact QU | exact CG1]]]]]]]].
  eapply ASTA_conseq; [exact Hc5'|]. intros ms <-. exists m5.
  split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F4, fc4; reflexivity|].
  split; [split; [exact ART5 | split; [exact MI5 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM4 WM5))) | exact ST5]]]|].
  split.
  { intros a Ha Ho. cbn [outside] in Ho.
    assert (A1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -48) (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; right; exact He | rewrite FRS1; auto | lia]).
    assert (A0' : aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -48) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | lia]).
    pose proof (newchunk_apart RT AF Σ Σ1 m2 q NB_BYTES (usp + -48) _ ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(unfold NB_BYTES; lia) A0') as N3.
    pose proof (cl_split RT AF Σ m usp 48 _ ART0 ltac:(lia) ltac:(lia) Ha) as N5.
    rewrite (MU5 a I).
    rewrite (PRES4 a A1 N3).
    rewrite (PRES2 a A0' ltac:(lia)).
    exact (PR1 a Ha I). }
  split; [exact (cl_env_agree m4 m5 _ _ ENV4 (fun a _ => MU5 a I))|].
  pose proof (af_acc_live RT AF Σ1 m5 q NB_BYTES ART5 INQ1) as (WRq5 & ACCq5).
  split; [exact WRq5|]. split; [exact ACCq5|].
  split; [exact (rw_cells_agree asegs m4 m5 _ _ FPC4 (AG45 _) WM5)|].
  apply (bytes_at_agree asegs m4 m5 _ _ ZER4). apply AG45.
Qed.
End Anl.
