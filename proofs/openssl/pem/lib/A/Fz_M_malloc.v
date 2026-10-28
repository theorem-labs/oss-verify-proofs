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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_CRYPTO_malloc : Z := 0x1fbf20.
Definition G_MALLOC_IMPL : Z := 0x5a9f40.     (* [comment removed for export] *)
Definition G_GOT_CMALLOC : Z := 0x5a5bc0.     (* [comment removed for export] *)
Definition G_ALLOW_CUST : Z := 0xb9f7c0.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cmalloc_A_post' (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' a3' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 0x1fbf98) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a2
                 (Z_to_bv 64 n) a1' a2' a3' a4 a5 a6 a7 a1 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_malloc) fc None m' (seg_rom asegs)
    /\ munch [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j] /\ rw_cells asegs m' (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' G_ALLOW_CUST [C1 (Z_to_bv 8 1)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma cmalloc_A_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (n lo : Z) (lb : byte),
  1 <= n < 2 ^ 63 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SEGTOP_A <= lo ->
  ro_cells asegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)] -> ro_cells asegs m G_GOT_CMALLOC [C8 (Z_to_bv 64 e_CRYPTO_malloc)] ->
  rw_cells asegs m G_ALLOW_CUST [C1 lb] -> (lb = Z_to_bv 8 0 \/ lb = Z_to_bv 8 1) ->
  mem_inv asegs m ->
  evt asegs (cmalloc_A_post' ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until lb. intros Hn ST HLO HIMG MIMP GOT LAT HLB MI.
  unfold e_CRYPTO_malloc, G_MALLOC_IMPL, G_GOT_CMALLOC, G_ALLOW_CUST, SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f7c0, 0xb9f7c0 + 1); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 40%nat ST. carve_frame 8%nat ST.
  do 6 zstep. do 8 zstep.
  zstep. ifT. zstep. ifF. zstep. zstep.
  destruct HLB as [-> | ->].
  - zstep. ifF. zstep. zstep; fix_lit_store. zstep. zstep.
    unfold cmalloc_A_post', e_malloc, G_ALLOW_CUST. apply evt_done.
    lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -48) [CB 8 ?j] |- _ => do 3 eexists; exists j; eexists end.
    split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
  - zstep. ifT. zstep. zstep.
    unfold cmalloc_A_post', e_malloc, G_ALLOW_CUST. apply evt_done.
    lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -48) [CB 8 ?j] |- _ => do 3 eexists; exists j; eexists end.
    split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.
(* [comment removed for export] *)
Definition cmalloc_B_post' (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma cmalloc_B_walk : forall ra0 ra sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p lo : Z) (j : list byte),
  0 < p < 2 ^ 64 ->
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp + -48 -> SEGTOP_A <= lo ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j] -> rw_cells asegs m (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (cmalloc_B_post' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1fbf98) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros Hp ST HLO HIMG FRj FR MI. unfold SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. ifT.
  do 6 zstep.
  release_frame FRj ST (SP + -40). release_frame FR ST SP.
  zstep.
  unfold cmalloc_B_post'. apply evt_done. eexists. split; [reflexivity|].
  rewrite (unsigned_lit SP) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.
Definition SITE_cm_malloc : Z := 0x1fbf98.

Section CMalloc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MAL : malloc_contract RT.

Definition crypto_malloc_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (n lo : Z) (outer : list Z) (lb : byte),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 -> 1 <= n <= 0x8000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 48 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_malloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  In (SITE_cm_malloc, e_CRYPTO_malloc) (cg_site (rt_cg RT Σ)) -> In (SITE_cm_malloc, e_malloc) (cg_call (rt_cg RT Σ)) ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ro_cells asegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)] -> ro_cells asegs m G_GOT_CMALLOC [C8 (Z_to_bv 64 e_CRYPTO_malloc)] ->
  rw_cells asegs m G_ALLOW_CUST [C1 lb] -> (lb = Z_to_bv 8 0 \/ lb = Z_to_bv 8 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_malloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ rw_cells asegs m' G_ALLOW_CUST [C1 (Z_to_bv 8 1)] /\ wr_at asegs m' p n /\ acc asegs m' p n) c
       /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_malloc_cps : crypto_malloc_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo outer lb
    FDO MST -> -> Hn ART0 MI0 CALL HSTK CTX UWC SITE1 CALL1 Hlen Hcr MIMP GOT LAT HLB.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0xb9f7c1 < usp - 48 /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  cl_eu usp (-48) EU1.
  (* [comment removed for export] *)
  pose proof (cmalloc_A_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo lb
                ltac:(lia) ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI MIMP GOT LAT HLB MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & a3' & j & m1 & -> & MU1 & WM1 & MI1 & FRj & FR & LAT1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FRj, FR, ST1, Hc1'.
  assert (CSW : forall x, ~ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x -> client_static x)
    by (intros x Hx; apply client_static_intro; unfold G_ALLOW_CUST in *; cbn [outside] in Hx; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] ART0 ltac:(lia) ltac:(lia) MU1 CSW WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (MAL Σ PMc (Z_to_bv 64 0x1fbf98) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp a2 (Z_to_bv 64 n) a1' a2' a3' a4 a5 a6 a7
           a1 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo FDO MST ltac:(lia) eq_refl eq_refl Hlen Hcr ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { apply (cl_unwind_call (rt_cg RT Σ) e_CRYPTO_malloc e_malloc 0x1fbf98 m m1 ra s0 sp _ outer CTX SITE1 CALL1 ltac:(lia) UWC);
      [intros a Ha; apply PR1; [left; exact Ha | cbn [outside]; unfold G_ALLOW_CUST; cbv beta in Ha; fold usp in Ha; lia] | | rewrite EU1; fold usp; lia | exact SPT].
    fold usp. replace (usp - 16) with (usp + -40 + Z.of_nat (cells_size [C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m1 (usp + -40) [C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR). }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & Pp0 & Pp16 & PpU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even 0x1fbf98) in Hc2' by lia.
  (* [comment removed for export] *)
  assert (AG2 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2)
    by (intros a k H1 H2 x Hx; apply PRES2; left; cbv beta in Hx; lia).
  cl_keep FRj AG2 WM2 FRj2. cl_keep FR AG2 WM2 FR2.
  pose proof (cmalloc_B_walk (Z_to_bv 64 0x1fbf98) ra sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp a2 b1 b2 b3 b4 b5 b6 b7 a1 (Z_to_bv 64 n)
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 p lo j ltac:(unfold USTACK_TOP in *; lia) ST2
                ltac:(fold usp; unfold RT_STACK in *; lia) HLOI FRj2 FR2 MI2) as W2.
  cl_lift W2 Hc2' c3 Hc3. apply Hk. exists Σ1, p.
  split; [|exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 (conj Pp0 (conj Pp16 (conj PpU CG1)))))))].
  apply (ASTA_conseq RT Σ1 PMc _ _ c3 Hc3). intros ms3 (m3 & -> & MU3 & WM3 & MI3 & ST3). exists m3.
  split; [exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2; reflexivity|].
  fold usp in MU3, ST3.
  pose proof (cl_seg_ART RT AF Σ1 m2 m3 usp 48 [] ART2 ltac:(rewrite SP1; lia) ltac:(lia) MU3 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM3) as ART3.
  split; [split; [exact ART3|]; split; [exact MI3|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) | exact ST3]|].
  assert (PR3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m2 m3).
  { apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3). intros x Hx _. cbn [outside]. split; [destruct (cl_split RT AF Σ m usp 48 x ART0 ltac:(lia) ltac:(lia) Hx); lia | exact I]. }
  split; [apply (pres_fp_trans _ _ _ _ m m1 m3 PR1), (pres_fp_trans _ _ _ _ m1 m2 m3); [|exact PR3];
          apply pres_fp_of_pres; intros a Ha; apply PRES2; destruct Ha as [H|H]; [left; lia | right; exact H]|].
  split.
  { apply (rw_cells_transport asegs [(usp - 48, usp)] m2 m3 _ _ (rw_cells_agree asegs m1 m2 _ _ LAT1 ltac:(intros a Ha; apply PRES2; right; left; cbv beta in Ha; cbn [cells_size csize Nat.add] in Ha; apply client_static_intro; unfold G_ALLOW_CUST in *; lia) WM2) MU3 WM3).
    cbn [disjoint_from cells_size csize Nat.add]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  pose proof (af_live_range RT AF Σ1 m2 p n ART2 ltac:(rewrite LV1; left; reflexivity)) as (_ & PHI & _).
  split; [exact (wr_at_wm m2 m3 _ _ WR2 WM3)|].
  apply (acc_agree m2 m3 p n ACC2 ltac:(lia)). intros a Ha. cbv beta in Ha. apply MU3. cbn [outside]. split; [|exact I].
  assert (shad (p + n - 1) < usp - 48); [|lia]. unfold shad, SHB. rewrite SP1 in PHI. unfold STACK_WIN, RT_STACK in *.
  assert ((p + n - 1) / 8 <= p + n) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

End CMalloc.
