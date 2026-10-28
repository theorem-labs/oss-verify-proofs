(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_env Fz_M_malloc Fz_M_zalloc Fz_G_CRYPTO_calloc Fz_G_OPENSSL_LH_set_thunks Fz_G_OPENSSL_LH_new Fz_I1_first.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition e_pdefns : Z := 0x20d2a8.             (* [comment removed for export] *)
Definition SITE_pdefns_lhn : Z := 0x20d2cc.      (* [comment removed for export] *)
Definition e_pd_hash : Z := 0x20d2fc.            (* [comment removed for export] *)
Definition e_pd_cmp : Z := 0x20d340.             (* [comment removed for export] *)
Definition e_pd_t1 : Z := 0x20d950.              (* [comment removed for export] *)
Definition e_pd_t2 : Z := 0x20d970.              (* [comment removed for export] *)
Definition e_pd_t3 : Z := 0x20d990.              (* [comment removed for export] *)
Definition e_pd_t4 : Z := 0x20d9b0.              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pd_w0_post (sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_pdefns_lhn) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 e_pd_hash) (Z_to_bv 64 e_pd_cmp) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OPENSSL_LH_new) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -16).

Lemma pd_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (pd_w0_post sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_pdefns) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP MI.
  unfold e_pdefns.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 9 zstep.
  apply evt_done. unfold pd_w0_post, SITE_pdefns_lhn, e_OPENSSL_LH_new, e_pd_hash, e_pd_cmp. eexists.
  split; [cbv delta [mkR]; replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma pd_w1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rav s0v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z),
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -16) [C8 s0v; C8 rav] ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1 a0 (Z_to_bv 64 e_pd_t1) (Z_to_bv 64 e_pd_t2) (Z_to_bv 64 e_pd_t3) (Z_to_bv 64 e_pd_t4) a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_OPENSSL_LH_set_thunks) fc None m (seg_rom asegs)
                      /\ stk asegs m lo (bv_unsigned sp))
      (MS (mkR (Z_to_bv 64 SITE_pdefns_lhn) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_pdefns_lhn) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP FR MI.
  unfold SITE_pdefns_lhn in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-16) EU1.
  do 8 zstep.
  do 2 zstep.
  pose proof FR as FR'. eapply stk_release in FR'; [| exact ST| lia]. cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in FR' by lia.
  zstep. zstep.
  apply evt_done. unfold e_OPENSSL_LH_set_thunks, e_pd_t1, e_pd_t2, e_pd_t3, e_pd_t4.
  split; [cbv delta [mkR]; replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity| exact FR'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PDefns.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_LHN : OPENSSL_LH_new_stmt RT.

Definition PDEFNS_SITES : list (Z * Z) :=
  [(SITE_pdefns_lhn, e_pdefns); (SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new);
   (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition PDEFNS_CALLS : list (Z * Z) :=
  [(SITE_pdefns_lhn, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc);
   (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].

(* [comment removed for export] *)
Definition pdefns_cells (B : Z) : list cell :=
  [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 e_pd_cmp); C8 (Z_to_bv 64 e_pd_hash);
   C8 (Z_to_bv 64 e_pd_t1); C8 (Z_to_bv 64 e_pd_t2); C8 (Z_to_bv 64 e_pd_t3); C8 (Z_to_bv 64 e_pd_t4);
   CB 48 (le4 (Z_to_bv 64 8) ++ le4 (Z_to_bv 64 16) ++ repeat (Z_to_bv 8 0) 4 ++ le4 (Z_to_bv 64 8) ++ le8 (Z_to_bv 64 512) ++ le8 (Z_to_bv 64 256) ++ repeat (Z_to_bv 8 0) 16)].

Definition pdefns_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x150 + 16 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_pdefns (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) PDEFNS_SITES PDEFNS_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> mcost 104 + mcost 128 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pdefns m)))
    (fun c => exists (Σ' : rts RT) (lh B : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 lh) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' lh 104 /\ acc asegs m' lh 104 /\ wr_at asegs m' B 128 /\ acc asegs m' B 128
           /\ rw_cells asegs m' lh (pdefns_cells B)
           /\ rw_cells asegs m' B [CB 128 (repeat (Z_to_bv 8 0) 128)]) c
       /\ rt_live RT Σ' = (B, 128) :: (lh, 104) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - (mcost 104 + mcost 128) /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < lh /\ lh mod 16 = 0 /\ lh + 104 < USTACK_TOP /\ 0 < B /\ B mod 16 = 0 /\ B + 128 < USTACK_TOP).

Local Ltac closed_bytes := vm_compute; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); reflexivity.

Theorem pdefns_cps : pdefns_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 368 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-16) EU1.
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  pose proof (pd_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 16, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 16) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (ABOVE1 : forall P : Z -> Prop, (forall x, P x -> usp <= x) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (ENV1 : cl_env m1 lb canary).
  { apply (cl_env_agree m m1 lb canary ENV). intros a Ha. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. unfold SEGTOP_A in *.
    apply MU1. cbn [outside]. split; [lia| exact I]. }
  pose proof (uw_chain_agree outer m m1 sp s0 UWC ltac:(apply ABOVE1; cbv beta; unfold USTACK_TOP in *; intros; lia)) as UWC1.
  (* [comment removed for export] *)
  assert (FR16 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]) by (replace (usp - 16) with (usp + -16) by lia; exact FR1).
  destruct (cl_chain_call (rt_cg RT Σ) e_pdefns e_OPENSSL_LH_new SITE_pdefns_lhn m1 m1 ra s0 sp (Z_to_bv 64 (usp + -16)) outer CTX
              (proj1 CGH (SITE_pdefns_lhn, e_pdefns) ltac:(left; reflexivity)) (proj2 CGH (SITE_pdefns_lhn, e_OPENSSL_LH_new) ltac:(left; reflexivity)) UWC1 ltac:(intros a _; reflexivity)
              FR16 ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
  apply (C_LHN Σ PMc (Z_to_bv 64 SITE_pdefns_lhn) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 e_pd_hash) (Z_to_bv 64 e_pd_cmp) a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 1. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_pdefns_lhn) by (unfold SITE_pdefns_lhn; lia). exact CTXc. }
  { exact UWCc. }
  { clear - CGH. unfold PDEFNS_SITES, PDEFNS_CALLS in *. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In app] in Hx |- *; tauto. }
  { exact Hlen. }
  { exact Hcr. }
  { exact ENV1. }
  { reflexivity. }
  { reflexivity. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ2 & lh & B & Hc2 & LV2 & FRS2 & SP2 & CR2 & LH0 & LH16 & LHHI & B0 & B16 & BHI & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM12 & ST2) & PRES2 & ENV2 & WRL & ACCL & WRB & ACCB & SC2 & ZB2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. fold usp in ST2, PRES2. rewrite (ret_pc_even SITE_pdefns_lhn) in Hc2' by (unfold SITE_pdefns_lhn; lia).
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp - 16) x /\ x <> G_ALLOW_CUST) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). apply PRES2; [| cbn [outside]; split; [lia| exact I]].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  eassert (FR2 : rw_cells asegs m2 (usp + -16) _).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM12]. apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia| unfold G_ALLOW_CUST, STACK_WIN in *; lia]. }
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWC1 ltac:(apply AG2; intros x Hx; split; [left; lia| unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN in *; lia])) as UWC2.
  pose proof (af_live_range RT AF Σ2 m2 lh 104 ART2 ltac:(rewrite LV2; right; left; reflexivity)) as (_ & LHLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m2 lh 104 ART2 ltac:(rewrite LV2; right; left; reflexivity) ltac:(lia)) as LHH.
  pose proof (af_live_range RT AF Σ2 m2 B 128 ART2 ltac:(rewrite LV2; left; reflexivity)) as (_ & BLO & _).
  rewrite SP2 in LHLO, BLO.
  destruct (af_client_consts RT AF Σ2 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (cells_mid_congr m2 lh [] [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 e_pd_cmp); C8 (Z_to_bv 64 e_pd_hash); CB 32 (repeat (Z_to_bv 8 0) 32)]
                [CB 24 (le8 (Z_to_bv 64 B) ++ le8 (Z_to_bv 64 e_pd_cmp) ++ le8 (Z_to_bv 64 e_pd_hash)); C8 z64; C8 z64; C8 z64; C8 z64]
                [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); CB 16 (repeat (Z_to_bv 8 0) 16)]
                ltac:(cbn [cells_bytes cbytes app]; rewrite <- !app_assoc; reflexivity) eq_refl ltac:(cbn; repeat split; reflexivity) SC2) as SC2'.
  cbn [app] in SC2'.
  pose proof (cells_mid_congr m2 lh [CB 24 (le8 (Z_to_bv 64 B) ++ le8 (Z_to_bv 64 e_pd_cmp) ++ le8 (Z_to_bv 64 e_pd_hash)); C8 z64; C8 z64; C8 z64; C8 z64]
                [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); CB 16 (repeat (Z_to_bv 8 0) 16)]
                [CB 48 (le4 (Z_to_bv 64 8) ++ le4 (Z_to_bv 64 16) ++ repeat (Z_to_bv 8 0) 4 ++ le4 (Z_to_bv 64 8) ++ le8 (Z_to_bv 64 512) ++ le8 (Z_to_bv 64 256) ++ repeat (Z_to_bv 8 0) 16)] []
                ltac:(closed_bytes) eq_refl ltac:(cbn; repeat split; reflexivity) ltac:(rewrite app_nil_r; exact SC2')) as SC2''.
  rewrite app_nil_r in SC2''. cbn [app] in SC2''.
  (* [comment removed for export] *)
  pose proof (pd_w1 sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp s1 (Z_to_bv 64 lh) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F2 fc2 m2 lo
                ST2 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 FR2 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & (-> & ST3) & Hc3'). clear Hc3. fold usp in ST3.
  (* [comment removed for export] *)
  epose proof (lhst_walk ra sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 s0 s1
                (Z_to_bv 64 e_pd_t1) (Z_to_bv 64 e_pd_t2) (Z_to_bv 64 e_pd_t3) (Z_to_bv 64 e_pd_t4) b5 b6 b7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 lh _ _ z64 z64 z64 z64 F2 fc2 m2 lo) as WT.
  specialize (WT ST3 ltac:(fold usp; unfold RT_STACK in *; lia) LO0 HT1 UT2 SHC2 SC2'' ACCL ltac:(clear - LH16; Z.div_mod_to_equations; lia)
                  LHH ltac:(unfold USTACK_TOP in *; lia) ltac:(fold usp; lia) MI2).
  cl_lift WT Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & -> & MU4 & WM4 & MI4 & SC4 & ST4) & Hc4'). clear Hc4.
  fold usp in MU4, ST4.
  assert (ART4 : ART RT Σ2 m4).
  { apply (af_frame RT AF Σ2 m2 m4 (usp - 16) ART2 ltac:(rewrite SP2; lia)); [| exact WM4]. intros a Ha. apply MU4. cbn [outside].
    split; [intros X; apply Ha; right; right; left; exists lh, 104; split; [rewrite LV2; right; left; reflexivity| lia]|].
    split; [| exact I]. intros X. apply Ha. left. unfold USTACK_TOP in *. lia. }
  assert (OFF4 : forall P : Z -> Prop, (forall x, P x -> ~ (lh + 24 <= x < lh + 56) /\ ~ (usp - 16 <= x < usp)) -> agree_on P m2 m4).
  { intros P HP a Ha. apply MU4. cbn [outside]. destruct (HP _ Ha) as [X1 X2]. repeat split; try exact I; lia. }
  pose proof (Fz_I1_defs.live_apart RT AF Σ2 m2 (lh, 104) (B, 128) ART2 ltac:(rewrite LV2; right; left; reflexivity) ltac:(rewrite LV2; left; reflexivity)
                ltac:(intros E; injection E; lia)) as ALB. cbn [fst snd] in ALB.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m2 B 128 ART2 ltac:(rewrite LV2; left; reflexivity) ltac:(lia)) as BH.
  assert (ZB4 : rw_cells asegs m4 B [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (rw_cells_agree asegs m2 m4 _ _ ZB2); [apply OFF4; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM4]).
  assert (ENV4 : cl_env m4 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m2 m4 _ canary ENV2 MU4); cl_fp_lia).
  (* [comment removed for export] *)
  apply Hk. exists Σ2, lh, B.
  split.
  - apply (ASTA_conseq RT Σ2 PMc _ _ c4 Hc4'). intros ms4 <-. exists m4.
    split; [exists u0, u1, u2, (Z_to_bv 64 (lh + 48)), (Z_to_bv 64 0), (Z_to_bv 64 e_pd_t3), (Z_to_bv 64 e_pd_t4), (Z_to_bv 64 0), (Z_to_bv 64 SHB), (Z_to_bv 64 0), u3, u4, u5, u6, F2, fc2; reflexivity|].
    split; [exact (conj ART4 (conj MI4 (conj (wmono_trans asegs m m2 m4 (wmono_trans asegs m m1 m2 WM1 WM12) WM4) ST4)))|].
    split. { intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (O1 & _). unfold G_ALLOW_CUST in O1.
             pose proof (cl_split RT AF Σ m usp 368 _ ART0 ltac:(lia) ltac:(lia) Ha) as OFFa.
             assert (Ha' : aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -16) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]).
             pose proof (newchunk_apart_gen RT AF Σ Σ2 m2 [(B, 128)] lh 104 usp (bv_unsigned a) ART2 LV2 FRS2 SP2 ltac:(lia) ltac:(lia) Ha) as NLH.
             rewrite (MU4 a ltac:(cbn [outside]; unfold STACK_WIN in *; repeat split; try exact I; lia)).
             rewrite (PRES2 a Ha' ltac:(cbn [outside]; unfold G_ALLOW_CUST; split; [lia| exact I])).
             apply MU1. cbn [outside]. destruct OFFa; split; try exact I; lia. }
    split; [exact ENV4|].
    split; [exact (wr_at_wm m2 m4 lh 104 WRL WM4)|].
    split. { apply (acc_agree m2 m4 lh 104 ACCL ltac:(lia)). apply OFF4. cbv beta. unfold shad, SHB, USTACK_TOP, STACK_WIN in *. intros x Hx.
             Z.div_mod_to_equations. lia. }
    split; [exact (wr_at_wm m2 m4 B 128 WRB WM4)|].
    split. { apply (acc_agree m2 m4 B 128 ACCB ltac:(lia)). apply OFF4. cbv beta. unfold shad, SHB, USTACK_TOP, STACK_WIN in *. intros x Hx.
             Z.div_mod_to_equations. lia. }
    split; [| exact ZB4].
    unfold pdefns_cells.
    apply (cells_mid_congr m4 lh [] [CB 24 (le8 (Z_to_bv 64 B) ++ le8 (Z_to_bv 64 e_pd_cmp) ++ le8 (Z_to_bv 64 e_pd_hash))]
             [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 e_pd_cmp); C8 (Z_to_bv 64 e_pd_hash)]
             [C8 (Z_to_bv 64 e_pd_t1); C8 (Z_to_bv 64 e_pd_t2); C8 (Z_to_bv 64 e_pd_t3); C8 (Z_to_bv 64 e_pd_t4);
              CB 48 (le4 (Z_to_bv 64 8) ++ le4 (Z_to_bv 64 16) ++ repeat (Z_to_bv 8 0) 4 ++ le4 (Z_to_bv 64 8) ++ le8 (Z_to_bv 64 512) ++ le8 (Z_to_bv 64 256) ++ repeat (Z_to_bv 8 0) 16)]);
      [cbn [cells_bytes cbytes app]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn; tauto|]. cbn [app]. exact SC4.
  - split; [exact LV2|]. split; [exact FRS2|]. split; [exact SP2|]. split; [exact CR2|]. split; [exact CG2|].
    split; [lia|]. split; [exact LH16|]. split; [exact LHHI|]. split; [lia|]. split; [exact B16| exact BHI].
Qed.
End PDefns.
