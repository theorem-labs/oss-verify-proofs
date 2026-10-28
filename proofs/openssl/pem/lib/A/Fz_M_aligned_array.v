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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_M_malloc Fz_env Fz_mkit Fz_M_aligned.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Definition e_CRYPTO_aligned_alloc_array : Z := 0x201614.

(* [comment removed for export] *)
Definition aaa_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (n : Z) (al fp file line : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) al fp file line line a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_aligned_alloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma aaa_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (num size : Z) (al fp file line : word) (lo : Z),
  0 <= num < 2^64 -> 0 <= size < 2^64 -> num * size < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (aaa_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 F fc (num * size) al fp file line lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 num) (Z_to_bv 64 size) al fp file line a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_aligned_alloc_array) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hn Hs Hm ST HLO HIMG SPH MI. unfold e_CRYPTO_aligned_alloc_array, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 8 zstep. do 4 zstep. zstep.
  rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (num * size)) by (split; [apply Z.mul_nonneg_nonneg; lia | lia]).
  ifT.
  do 5 zstep. do 7 zstep.
  replace (SP + -48 + 48) with SP by lia.
  release_frame FR ST SP.
  zstep.
  unfold aaa_post, e_CRYPTO_aligned_alloc. apply evt_done. eexists. split; [subst SP; rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (unsigned_lit SP) by lia. replace (SP - 48) with (SP + -48) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CAlignedArray.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis C_AA : crypto_aligned_alloc_env_stmt RT.

(* [comment removed for export] *)
Definition crypto_aligned_alloc_array_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (num size fp pb nb lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 num -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 64 -> a3 = Z_to_bv 64 fp -> tp = Z_to_bv 64 0xba3ef0 ->
  0 <= num < 2^64 -> 0 <= size < 2^64 -> num * size < 2^64 ->
  memalign_plain 64 (num * size) ->
  In (pb, nb) (rt_live RT Σ) -> nb <= 64512 -> pb <= fp -> fp + 8 <= pb + nb -> fp mod 8 = 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x200 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_aligned_alloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_aa_memalign, e_CRYPTO_aligned_alloc)] [(SITE_aa_memalign, e_posix_memalign)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 1 + mcost (num * size) <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_aligned_alloc_array m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) fp 8 m m'
           /\ cl_env m' lb canary /\ rw_cells asegs m' fp [C8 (Z_to_bv 64 q)] /\ wr_at asegs m' q (num * size) /\ acc asegs m' q (num * size)) c
       /\ rt_live RT Σ' = (q, num * size) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 - mcost (num * size) /\ 0 < q /\ q mod 64 = 0 /\ q + num * size < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_aligned_alloc_array_cps : crypto_aligned_alloc_array_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m num size fp pb nb lo outer lb canary
    FDO MST -> -> -> -> -> Hnum Hsize Hmul PLAIN Hin Hnb Hfp1 Hfp2 Hfp8 ART0 MI0 CALL HSTK CTX UWC CGH HFR Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  pose proof (aaa_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m num size (Z_to_bv 64 64) (Z_to_bv 64 fp) a4 a5 lo
                Hnum Hsize Hmul ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI ltac:(fold usp; unfold USTACK_TOP in *; lia) MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG1) as UWC1.
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  apply (C_AA Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 (num * size)) (Z_to_bv 64 64) (Z_to_bv 64 fp) a4 a5 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (num * size) fp pb nb lo outer lb canary FDO MST eq_refl eq_refl eq_refl eq_refl
           PLAIN Hin Hnb Hfp1 Hfp2 Hfp8 ART1 MI1 CO1 HSTK CTX UWC1 CGH HFR Hlen Hcr ENV1).
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q & Hc2 & REST).
  apply Hk. exists Σ1, q. split; [| exact REST].
  apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2). intros ms2 (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ENV2 & FPC & WR2 & ACC2). exists m2.
  split; [exact RS2|]. split; [exact (conj ART2 (conj MI2 (conj (wmono_trans asegs m m1 m2 WM1 WM2) ST2)))|].
  split; [| exact (conj ENV2 (conj FPC (conj WR2 ACC2)))].
  intros a Ha Ho. rewrite (PRES2 a Ha Ho). exact (PR1 a Ha I).
Qed.

End CAlignedArray.
