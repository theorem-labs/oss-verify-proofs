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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem Fz_kit Fz_chk Fz_M_malloc Fz_env Fz_mkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_CRYPTO_strdup : Z := 0x202ecc.
Definition SITE_sd_strlen : Z := 0x202f00.
Definition SITE_sd_malloc : Z := 0x202f14.
Definition SITE_sd_memcpy : Z := 0x202f28.

(* [comment removed for export] *)
Definition sd_s0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : Z) (file line : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_sd_strlen) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 s)
                 (Z_to_bv 64 s) file line a3 a4 a5 a6 a7 line s3 file s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_strlen) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma sd_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (file line : word) (lo : Z),
  0 < s < 2^63 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SEGTOP_A <= lo -> mem_inv asegs m ->
  evt asegs (sd_s0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc s file line lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) file line a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_strdup) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hs ST HLO HIMG MI. unfold e_CRYPTO_strdup, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 8 zstep. zstep. ifF. do 4 zstep.
  unfold sd_s0_post, SITE_sd_strlen, e_strlen. apply evt_done. eexists.
  split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption.
Qed.

(* [comment removed for export] *)
Definition sd_s1_post (sp gp tp t0 t1 t2 s0' s1' s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (file line : word) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_sd_malloc) sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 (len + 1)) file line a3 a4 a5 a6 a7
                         line (Z_to_bv 64 (len + 1)) file s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 e_CRYPTO_malloc) fc None m (seg_rom asegs).

Lemma sd_s1_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s3' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (len : Z) (file line : word),
  0 <= len < 2^62 -> mem_inv asegs m ->
  evt asegs (sd_s1_post sp gp tp t0 t1 t2 s0' s1' s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc len file line m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 line s3' file s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sd_strlen) fc None m (seg_rom asegs)).
Proof.
  intros until line. intros Hl MI. unfold SITE_sd_strlen.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 5 zstep.
  unfold sd_s1_post, SITE_sd_malloc, e_CRYPTO_malloc. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition sd_s2_post (sp gp tp t0 t1 t2 s0' s4' s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (s n q : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_sd_memcpy) sp gp tp t0 t1 t2 s0' (Z_to_bv 64 s) (Z_to_bv 64 q) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                         (Z_to_bv 64 q) (Z_to_bv 64 n) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 e_asan_memcpy) fc None m (seg_rom asegs).

Lemma sd_s2_walk : forall ra0 sp gp tp t0 t1 t2 s0' a1 a2 a3 a4 a5 a6 a7 s2' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s n q : Z),
  0 < q < 2^63 -> mem_inv asegs m ->
  evt asegs (sd_s2_post sp gp tp t0 t1 t2 s0' s4' s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc s n q m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' (Z_to_bv 64 s) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2' (Z_to_bv 64 n) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sd_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until q. intros Hq MI. unfold SITE_sd_malloc.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. ifF. do 4 zstep.
  unfold sd_s2_post, SITE_sd_memcpy, e_asan_memcpy. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition sd_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma sd_s3_walk : forall ra0 ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s3' s4' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp + -48 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv asegs m ->
  evt asegs (sd_s3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc q lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 q) s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sd_memcpy) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG SPH FR MI. unfold SITE_sd_memcpy, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 2 zstep. do 7 zstep.
  replace (SP + -48 + 48) with SP by lia.
  release_frame FR ST SP.
  zstep.
  unfold sd_s3_post. apply evt_done. eexists. split; [subst SP; rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (unsigned_lit SP) by lia. replace (SP - 48) with (SP + -48) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CStrdup.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SLC : strlen_icontract RT.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.

(* [comment removed for export] *)
Definition crypto_strdup_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (s b sz : Z) (str slack : list byte) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> tp = Z_to_bv 64 0xba3ef0 ->
  ro_bytes asegs s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 <= 0x4000000 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  GOBJ b sz -> b <= s -> s + Z.of_nat (length str) + 1 <= b + sz ->
  0x10000 <= s -> s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= SEGTOP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 48 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_strdup (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_sd_malloc, e_CRYPTO_strdup); (SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_sd_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (Z.of_nat (length str) + 1) <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_strdup m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ wr_at asegs m' q (Z.of_nat (length str) + 1) /\ acc asegs m' q (Z.of_nat (length str) + 1)
           /\ bytes_at asegs m' q (str ++ [Z_to_bv 8 0])) c
       /\ rt_live RT Σ' = (q, Z.of_nat (length str) + 1) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (Z.of_nat (length str) + 1) /\ 0 < q /\ q mod 16 = 0
       /\ q + (Z.of_nat (length str) + 1) < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_strdup_cps : crypto_strdup_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s b sz str slack lo outer lb canary
    FDO MST -> -> ROB NOZ Hn SLK HG Hbs Hse HS0 HSE ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (len := Z.of_nat (length str)) in *. assert (Hl0 : 0 <= len) by (unfold len; lia).
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  assert (Hs63 : 0 < s < 2^63) by (unfold SEGTOP_A in *; lia).
  assert (LENS : Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) = len + 1 + Z.of_nat (length slack)) by (rewrite app_length; cbn [length]; unfold len; lia).
  assert (BYT : forall mm : mem, mem_inv asegs mm -> bytes_at asegs mm s (str ++ Z_to_bv 8 0 :: slack)).
  { intros mm MIm. apply ro_bytes_at; [exact MIm | lia | rewrite LENS; unfold SEGTOP_A in *; lia | exact ROB]. }
  assert (CHK : forall (Σx : rts RT) (mx : mem) (spx : word), ART RT Σx mx -> checked_src RT Σx mx spx lo s (len + 1)).
  { intros Σx mx spx ARTx. split; [intros _; split | left; unfold SEGTOP_A in *; lia].
    - exact (afp_acc_global RT GOBJ AFP Σx mx b sz s (len + 1) ARTx HG Hbs ltac:(lia)).
    - right; right; right. unfold SEGTOP_A in *. lia. }
  cl_eu usp (-48) EU1.
  (* [comment removed for export] *)
  pose proof (sd_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s a1 a2 lo
                Hs63 ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  (* [comment removed for export] *)
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 (usp + -48)) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  apply (SLC Σ PMc (Z_to_bv 64 SITE_sd_strlen) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 s) (Z_to_bv 64 s) a1 a2 a3 a4 a5 a6 a7
           a2 s3 a1 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 s str slack lo FDO MST eq_refl (BYT m1 MI1) NOZ ltac:(fold len; lia) SLK
           ltac:(unfold SEGTOP_A in *; lia) ltac:(left; fold len; unfold SEGTOP_A in *; lia) ltac:(fold len; exact (CHK Σ m1 _ ART1)) ART1 MI1 CO1).
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_sd_strlen) in Hc2' by (unfold SITE_sd_strlen; lia).
  fold len in Hc2'.
  (* [comment removed for export] *)
  pose proof (sd_s1_walk (Z_to_bv 64 SITE_sd_strlen) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 s) b1 b2 b3 b4 b5 b6 b7 s3
                s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 len a1 a2 ltac:(lia) MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  assert (AG2 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia | lia]. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2).
  { intros a Ha. cbv beta in Ha. rewrite (AG2 usp (USTACK_TOP - usp) ltac:(lia) ltac:(lia) a ltac:(cbv beta; lia)). exact (AG1 a Ha). }
  assert (FRR2 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m2 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR2). }
  destruct (cl_chain_call (rt_cg RT Σ) e_CRYPTO_strdup e_CRYPTO_malloc SITE_sd_malloc m m2 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG02 FRR2 ltac:(rewrite EU1; fold usp; lia) SPT) as (CTX2 & UWC2).
  assert (ENV2 : cl_env m2 lb canary).
  { apply (cl_env_pres_ex _ _ _ 0 0 m1 m2 lb canary ENV1 PRES2). intros x _. lia. }
  (* [comment removed for export] *)
  apply (C_CM Σ PMc (Z_to_bv 64 SITE_sd_malloc) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 s) (Z_to_bv 64 (len + 1)) a1 a2 b3 b4 b5 b6 b7
           a2 (Z_to_bv 64 (len + 1)) a1 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 (len + 1) lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART2 MI2).
  { fold usp in SPA. cl_call_ok EU1 ST2 LOW SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_sd_malloc) by (unfold SITE_sd_malloc; lia). exact CTX2. }
  { exact UWC2. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [In] in Hx |- *; tauto. }
  { exact Hlen. } { exact Hcr. } { exact ENV2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ1 & q & Hc4 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & ENV3 & WR3 & ACC3) & Hc4'). clear Hc4.
  destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite (ret_pc_even SITE_sd_malloc) in Hc4' by (unfold SITE_sd_malloc; lia).
  assert (INQ1 : In (q, len + 1) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m3 q (len + 1) ART3 INQ1) as (_ & QLO & QI). rewrite SP1 in QLO.
  (* [comment removed for export] *)
  pose proof (sd_s2_walk (Z_to_bv 64 SITE_sd_malloc) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp d1 d2 d3 d4 d5 d6 d7 a2 a1
                s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3 s (len + 1) q ltac:(unfold USTACK_TOP in *; lia) MI3) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  assert (SB : bytes_at asegs m3 s (str ++ [Z_to_bv 8 0])).
  { pose proof (BYT m3 MI3) as X. change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [Z_to_bv 8 0] ++ slack) in X. rewrite app_assoc in X.
    exact (proj1 (proj1 (bytes_at_app asegs m3 s _ _) X)). }
  assert (SBL : Z.of_nat (length (str ++ [Z_to_bv 8 0])) = len + 1) by (rewrite app_length; cbn [length]; unfold len; lia).
  assert (CO3 : call_ok RT Σ1 m3 (Z_to_bv 64 (usp + -48)) lo).
  { fold usp in SPA. rewrite <- SP1 in LOW. cl_call_ok EU1 ST3 LOW SPA 3. }
  apply (MCP Σ1 PMc (Z_to_bv 64 SITE_sd_memcpy) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 s) (Z_to_bv 64 q) (Z_to_bv 64 s) (Z_to_bv 64 (len + 1))
           d3 d4 d5 d6 d7 (Z_to_bv 64 q) (Z_to_bv 64 (len + 1)) a1 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3 q s (str ++ [Z_to_bv 8 0]) lo FDO MST eq_refl eq_refl
           ltac:(rewrite SBL; reflexivity) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold SEGTOP_A in *; lia) ltac:(rewrite SBL; lia) SB).
  { rewrite SBL. exact (CHK Σ1 m3 _ ART3). }
  { rewrite SBL. exact (live_checked_dst RT AF Σ1 m3 _ q (len + 1) q (len + 1) ART3 INQ1 ltac:(lia) ltac:(lia) ltac:(lia)). }
  { rewrite SBL. unfold SEGTOP_A in *. destruct QI; [left | right]; lia. }
  { exact ART3. } { exact MI3. } { exact CO3. }
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CPY4) & Hc6'). clear Hc6.
  destruct RS4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite SBL in PRES4. rewrite (ret_pc_even SITE_sd_memcpy) in Hc6' by (unfold SITE_sd_memcpy; lia).
  (* [comment removed for export] *)
  assert (AG3 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES3; [left; lia|]. cbn [outside]. unfold G_ALLOW_CUST. split; [unfold USTACK_TOP, RT_STACK in *; lia | exact I]. }
  assert (AG4 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; lia | unfold RT_STACK in *; lia]. }
  cl_keep FR2 AG3 WM3 FR3. cl_keep FR3 AG4 WM4 FR4.
  pose proof (sd_s3_walk (Z_to_bv 64 SITE_sd_memcpy) ra sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 s) (Z_to_bv 64 q) e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 (len + 1)) a1
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 q lo ST4 ltac:(fold usp; unfold RT_STACK in *; lia) HLOI
                ltac:(fold usp; unfold USTACK_TOP in *; lia) FR4 MI4) as W3.
  cl_lift W3 Hc6' c7 Hc7.
  apply Hk. exists Σ1, q.
  split; [| split; [exact LV1 | split; [exact FRS1 | split; [exact SP1 | split; [exact CR1 | split; [exact Q0 | split; [exact Q16 | split; [exact QU | exact CG1]]]]]]]].
  apply (ASTA_conseq RT Σ1 PMc _ _ c7 Hc7). intros ms7 (m5 & -> & MU5 & WM5 & MI5 & ST5). exists m5. fold usp in MU5, ST5.
  split; [exists w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F4, fc4; reflexivity|].
  pose proof (cl_seg_ART RT AF Σ1 m4 m5 usp 48 [] ART4 ltac:(rewrite SP1; lia) ltac:(lia) MU5 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM5) as ART5.
  assert (WM05 : wmono asegs m m5).
  { apply (wmono_trans asegs m m4 m5); [| exact WM5]. apply (wmono_trans asegs m m3 m4); [| exact WM4]. apply (wmono_trans asegs m m2 m3); [| exact WM3].
    apply (wmono_trans asegs m m1 m2); [exact WM1 | exact WM2]. }
  split; [exact (conj ART5 (conj MI5 (conj WM05 ST5)))|].
  split.
  { intros a Ha Ho.
    pose proof (cl_split RT AF Σ m usp 48 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
    pose proof (newchunk_apart RT AF Σ Σ1 m3 q (len + 1) usp _ ART3 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Ha) as NQ.
    rewrite (MU5 a ltac:(cbn [app outside]; split; [lia | exact I])).
    rewrite (PRES4 a ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; right; exact He | auto | lia]) ltac:(lia)).
    rewrite (PRES3 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | lia]) Ho).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | lia]) ltac:(lia)).
    exact (PR1 a Ha I). }
  assert (ENV4 : cl_env m4 (Z_to_bv 8 1) canary).
  { apply (cl_env_pres_ex _ _ _ q (len + 1) m3 m4 (Z_to_bv 8 1) canary ENV3 PRES4).
    intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)). unfold SEGTOP_A in *. lia. }
  split; [apply (cl_env_seg _ m4 m5 (Z_to_bv 8 1) canary ENV4 MU5); cl_fp_lia|].
  pose proof (af_acc_live RT AF Σ1 m5 q (len + 1) ART5 INQ1) as (WR5 & ACC5).
  split; [exact WR5|]. split; [exact ACC5|].
  apply (bytes_at_transport asegs _ m4 m5 q _ CPY4 MU5). cbn [app disjoint_from]. rewrite SBL. split; [left; lia | exact I].
Qed.

End CStrdup.
