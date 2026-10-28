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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_M_malloc Fz_env Fz_mkit Fz_M_realloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_CRYPTO_realloc_array : Z := 0x2016f0.

(* [comment removed for export] *)
Definition cra_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n : Z) (file line : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) file line line a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_realloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma cra_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p num size : Z) (file line : word) (lo : Z),
  0 <= p < 2^64 -> 0 <= num < 2^64 -> 0 <= size < 2^64 -> num * size < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (cra_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t3 t4 t5 t6 F fc p (num * size) file line lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 num) (Z_to_bv 64 size) file line a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_realloc_array) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hp Hn Hs Hm ST HLO HIMG SPH MI. unfold e_CRYPTO_realloc_array, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  do 6 zstep. do 2 zstep. zstep. zstep.
  try (rewrite Z.shiftr_div_pow2 by lia; rewrite (Z.div_small (num * size)) by (split; [apply Z.mul_nonneg_nonneg; lia | lia])).
  ifT.
  do 3 zstep. do 5 zstep.
  replace (SP + -32 + 32) with SP by lia.
  release_frame FR ST SP.
  zstep.
  unfold cra_post, e_CRYPTO_realloc. apply evt_done. eexists. split; [subst SP; rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (unsigned_lit SP) by lia. replace (SP - 32) with (SP + -32) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CReallocArray.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis C_CR : crypto_realloc_env_stmt RT.

(* [comment removed for export] *)
Definition crypto_realloc_array_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n0 num size lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 num -> a2 = Z_to_bv 64 size -> tp = Z_to_bv 64 0xba3ef0 ->
  0 <= num < 2^64 -> 0 <= size < 2^64 ->
  In (p, n0) (rt_live RT Σ) -> 1 <= num * size <= 64512 -> 1 <= n0 <= 64512 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 48 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_realloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_cr_realloc, e_CRYPTO_realloc)] [(SITE_cr_realloc, e_realloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (num * size) <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_realloc_array m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ cl_env m' lb canary /\ wr_at asegs m' q (num * size) /\ acc asegs m' q (num * size)
           /\ (forall bs, bytes_at asegs m p bs -> Z.of_nat (length bs) = Z.min n0 (num * size) -> bytes_at asegs m' q bs)) c
       /\ rt_live RT Σ' = (q, num * size) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (num * size) /\ 0 < q /\ q mod 16 = 0 /\ q + num * size < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_realloc_array_cps : crypto_realloc_array_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 num size lo outer lb canary
    FDO MST -> -> -> -> Hnum Hsize Hin Hn Hn0 ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m p n0 ART0 Hin) as (Pp0 & PLO & _).
  pose proof (cra_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p num size a3 a4 lo
                ltac:(unfold STACK_WIN, USTACK_TOP in *; lia) Hnum Hsize ltac:(lia) ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI
                ltac:(fold usp; unfold USTACK_TOP in *; lia) MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG1) as UWC1.
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  apply (C_CR Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (num * size)) a3 a4 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p n0 (num * size) lo outer lb canary FDO MST eq_refl eq_refl eq_refl
           Hin Hn Hn0 ART1 MI1 CO1 HSTK CTX UWC1 CGH Hlen Hcr ENV1).
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q & Hc2 & REST).
  apply Hk. exists Σ1, q. split; [| exact REST].
  apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2). intros ms2 (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & ENV2 & WR2 & ACC2 & CPY). exists m2.
  split; [exact RS2|]. split; [exact (conj ART2 (conj MI2 ST2))|].
  split.
  { intros a Ha. rewrite (PRES2 a Ha). apply PR1; [| exact I].
    destruct Ha as [H|[H|[H|[H|H]]]]; [left; exact H| right; left; exact H| right; right; left| do 3 right; left; exact H| do 4 right; exact H].
    destruct H as (p' & n' & Hin' & Hx). exists p', n'. split; [exact (live_remove_sub _ _ _ Hin')| exact Hx]. }
  split; [exact ENV2|]. split; [exact WR2|]. split; [exact ACC2|].
  intros bs Hbs Hl. apply (CPY bs); [| exact Hl]. apply (bytes_at_agree asegs m m1 _ _ Hbs). intros a Ha. apply PR1; [| exact I].
  right; right; left. exists p, n0. split; [exact Hin|]. cbv beta in Ha. lia.
Qed.

End CReallocArray.
