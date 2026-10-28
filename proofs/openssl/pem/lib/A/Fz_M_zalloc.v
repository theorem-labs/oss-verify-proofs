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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit Fz_M_malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_CRYPTO_zalloc : Z := 0x1fbfec.
Definition SITE_cz_malloc : Z := 0x1fc00c.
Definition SITE_cz_memset : Z := 0x1fc024.

(* [comment removed for export] *)
Definition czalloc_s0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_cz_malloc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 n)
                 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_malloc) fc None m' (seg_rom asegs)
    /\ munch ([] ++ [(bv_unsigned sp - 32, bv_unsigned sp)]) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma czalloc_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> SEGTOP_A <= lo -> mem_inv asegs m ->
  evt asegs (czalloc_s0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG MI. unfold e_CRYPTO_zalloc, SEGTOP_A in *. cbn [app].
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  do 8 zstep.
  unfold czalloc_s0_post, SITE_cz_malloc, e_CRYPTO_malloc. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. eassumption.
Qed.

(* [comment removed for export] *)
Definition czalloc_s1_post (sp gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_cz_memset) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 n)
                         (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 e_asan_memset) fc None m (seg_rom asegs).

Lemma czalloc_s1_walk : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p n : Z),
  0 < p < 2 ^ 64 -> mem_inv asegs m ->
  evt asegs (czalloc_s1_post sp gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p n m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_cz_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros Hp MI. unfold SITE_cz_malloc.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. ifF. do 4 zstep.
  unfold czalloc_s1_post, SITE_cz_memset, e_asan_memset. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition czalloc_s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ([] ++ [(bv_unsigned sp - 32, bv_unsigned sp)]) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma czalloc_s2_walk : forall ra0 ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p lo : Z),
  stk asegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp + -32 -> SEGTOP_A <= lo ->
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv asegs m ->
  evt asegs (czalloc_s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_cz_memset) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG FR MI. unfold SITE_cz_memset, SEGTOP_A in *. cbn [app].
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 6 zstep.
  release_frame FR ST SP.
  zstep.
  unfold czalloc_s2_post. apply evt_done. eexists. split; [reflexivity|].
  rewrite (unsigned_lit SP) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CZalloc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis C_CM : crypto_malloc_stmt RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.

Definition crypto_zalloc_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (n lo : Z) (outer : list Z) (lb : byte),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 -> 1 <= n <= 0x4000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_zalloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ro_cells asegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)] -> ro_cells asegs m G_GOT_CMALLOC [C8 (Z_to_bv 64 e_CRYPTO_malloc)] ->
  rw_cells asegs m G_ALLOW_CUST [C1 lb] -> (lb = Z_to_bv 8 0 \/ lb = Z_to_bv 8 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_zalloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ rw_cells asegs m' G_ALLOW_CUST [C1 (Z_to_bv 8 1)] /\ wr_at asegs m' p n /\ acc asegs m' p n
           /\ bytes_at asegs m' p (repeat (Z_to_bv 8 0) (Z.to_nat n))) c
       /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_zalloc_cps : crypto_zalloc_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo outer lb
    FDO MST -> -> Hn ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr MIMP GOT LAT HLB.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0xb9f7c1 < usp - 32 /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  cl_eu usp (-32) EU1.
  (* [comment removed for export] *)
  pose proof (czalloc_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  destruct (cl_chain_call (rt_cg RT Σ) e_CRYPTO_zalloc e_CRYPTO_malloc SITE_cz_malloc m m1 ra s0 sp (Z_to_bv 64 (usp + -32)) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG1
              ltac:(fold usp; replace (usp - 16) with (usp + -32 + Z.of_nat (cells_size [C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -32) [C8 s2; C8 s1] [C8 s0; C8 ra] FR))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTX1 & UWC1).
  (* [comment removed for export] *)
  assert (MIMP1 : ro_cells asegs m1 G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)])
    by (apply (ro_cells_transport asegs _ m m1 _ _ MIMP MU1); cbn [app disjoint_from cells_size csize Nat.add]; unfold G_MALLOC_IMPL; split; [lia | exact I]).
  assert (GOT1 : ro_cells asegs m1 G_GOT_CMALLOC [C8 (Z_to_bv 64 e_CRYPTO_malloc)])
    by (apply (ro_cells_transport asegs _ m m1 _ _ GOT MU1); cbn [app disjoint_from cells_size csize Nat.add]; unfold G_GOT_CMALLOC; split; [lia | exact I]).
  assert (LAT1 : rw_cells asegs m1 G_ALLOW_CUST [C1 lb])
    by (apply (rw_cells_transport asegs _ m m1 _ _ LAT MU1 WM1); cbn [app disjoint_from cells_size csize Nat.add]; unfold G_ALLOW_CUST; split; [lia | exact I]).
  apply (C_CM Σ PMc (Z_to_bv 64 SITE_cz_malloc) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 n) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo (bv_unsigned ra :: outer) lb FDO MST eq_refl eq_refl ltac:(clear - Hn; lia) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_cz_malloc) by (unfold SITE_cz_malloc; lia). exact CTX1. }
  { exact UWC1. }
  { exact (proj1 CGH _ ltac:(right; left; reflexivity)). }
  { exact (proj2 CGH _ ltac:(right; left; reflexivity)). }
  { exact Hlen. } { exact Hcr. } { exact MIMP1. } { exact GOT1. } { exact LAT1. } { exact HLB. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & Pp0 & Pp16 & PpU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & LAT2 & WR2 & ACC2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_cz_malloc) in Hc2' by (unfold SITE_cz_malloc; lia).
  (* [comment removed for export] *)
  pose proof (czalloc_s1_walk (Z_to_bv 64 SITE_cz_malloc) sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                F2 fc2 m2 p n ltac:(unfold USTACK_TOP in *; lia) MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  assert (INP : In (p, n) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 p n ART2 INP) as (_ & PHI & _). rewrite SP1 in PHI.
  apply (MSET Σ1 PMc (Z_to_bv 64 SITE_cz_memset) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 n) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 n)
           b3 b4 b5 b6 b7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 p n (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl
           ltac:(unfold USTACK_TOP in *; lia) ltac:(lia)).
  { split; [intros _; split; [exact ACC2|]; left; exists p, n; split; [exact INP | lia]|].
    split; [intros i Hi; right; right; left; exists p, n; split; [exact INP | lia] | exact WR2]. }
  { exact ART2. } { exact MI2. }
  { fold usp in SPA. rewrite <- SP1 in LOW. unfold call_ok. rewrite EU1. split; [exact ST2|]. split; [exact LOW|]. split; [unfold RT_STACK in *; lia|].
    split; [unfold USTACK_TOP in *; lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 2). lia. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & ZER3) & Hc4'). clear Hc4.
  destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite (ret_pc_even SITE_cz_memset) in Hc4' by (unfold SITE_cz_memset; lia).
  (* [comment removed for export] *)
  assert (AG2 : forall a k, usp + -32 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (AG3 : forall a k, usp + -32 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES3; [left; lia|]. unfold RT_STACK in *. lia. }
  cl_keep FR AG2 WM2 FR2. cl_keep FR2 AG3 WM3 FR3.
  pose proof (czalloc_s2_walk (Z_to_bv 64 SITE_cz_memset) ra sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 n) (Z_to_bv 64 p) d1 d2 d3 d4 d5 d6 d7
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3 p lo ST3 ltac:(fold usp; unfold RT_STACK in *; lia) HLOI FR3 MI3) as W2.
  cl_lift W2 Hc4' c5 Hc5. apply Hk. exists Σ1, p.
  split; [|exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 (conj Pp0 (conj Pp16 (conj PpU CG1)))))))].
  apply (ASTA_conseq RT Σ1 PMc _ _ c5 Hc5). intros ms5 (m4 & -> & MU4 & WM4 & MI4 & ST4). exists m4. fold usp in MU4, ST4.
  split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F3, fc3; reflexivity|].
  pose proof (cl_seg_ART RT AF Σ1 m3 m4 usp 32 [] ART3 ltac:(rewrite SP1; lia) ltac:(lia) MU4 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM4) as ART4.
  split; [split; [exact ART4|]; split; [exact MI4|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4))) | exact ST4]|].
  assert (SPL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> usp <= x \/ x < usp - 32)
    by (intros x Hx; exact (cl_split RT AF Σ m usp 32 x ART0 ltac:(lia) ltac:(lia) Hx)).
  split.
  { intros a Ha Ho. cbn [outside] in Ho.
    rewrite (MU4 a ltac:(cbn [app outside]; split; [destruct (SPL _ Ha); lia | exact I])).
    rewrite (PRES3 a ltac:(destruct Ha as [H|H]; [left; lia | right; rewrite LV1, FRS1; destruct H as [H|[H|H]]; [left; exact H | right; left; destruct H as (p' & n' & Hin & Hx); exists p', n'; split; [right; exact Hin | exact Hx] | right; right; exact H]])
               (newchunk_apart RT AF Σ Σ1 m2 p n usp _ ART2 LV1 FRS1 SP1 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha)).
    rewrite (PRES2 a ltac:(destruct Ha as [H|H]; [left; lia | right; exact H]) Ho).
    exact (PR1 a Ha I). }
  pose proof (af_acc_live RT AF Σ1 m4 p n ART4 INP) as (WR4 & ACC4).
  split.
  { assert (LAT3 : rw_cells asegs m3 G_ALLOW_CUST [C1 (Z_to_bv 8 1)]).
    { apply (rw_cells_agree asegs m2 m3 _ _ LAT2); [|exact WM3]. intros a Ha. cbv beta in Ha. cbn [cells_size csize Nat.add] in Ha.
      destruct (af_live_range RT AF Σ1 m2 p n ART2 INP) as (_ & _ & X).
      apply PRES3; [right; left; apply client_static_intro; unfold G_ALLOW_CUST in *; lia | unfold G_ALLOW_CUST, SEGTOP_A in *; lia]. }
    apply (rw_cells_transport asegs _ m3 m4 _ _ LAT3 MU4 WM4).
    cbn [app disjoint_from cells_size csize Nat.add]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  split; [exact WR4|]. split; [exact ACC4|].
  apply (bytes_at_transport asegs _ m3 m4 p _ ZER3 MU4). rewrite repeat_length, Z2Nat.id by lia.
  cbn [app disjoint_from]. split; [left; unfold RT_STACK in *; lia | exact I].
Qed.

End CZalloc.
