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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_M_malloc Fz_M_zalloc Fz_env.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac wg_T := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifT | |- _ => idtac end.
Local Ltac wg_F := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifF | |- _ => idtac end.
Local Ltac zstore := zstep; fix_lit_store.
Local Ltac wg_raw H := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => rewrite H; cbv iota end.
Local Ltac wg_at p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => unify p q | |- _ => fail "wgen: unexpected pc" end.

Definition e_ossl_child_prov_ctx_new : Z := 0x215384.

(* [comment removed for export] *)
Definition ossl_child_prov_ctx_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 88) (Z_to_bv 64 312064) (Z_to_bv 64 39) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2080748) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma ossl_child_prov_ctx_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ossl_child_prov_ctx_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x215384) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  zstep.
  do 2 zstore.
  do 9 zstep.
  release_frame FR ST (bv_unsigned sp).
  unfold ossl_child_prov_ctx_new_s0_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section ossl_child_prov_ctx_new_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CRYPTO_zalloc : crypto_zalloc_env_stmt RT.

Definition ossl_child_prov_ctx_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x110 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_child_prov_ctx_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  In (bv_unsigned ra, e_CRYPTO_zalloc) (cg_call (rt_cg RT Σ)) ->
  cg_has (rt_cg RT Σ) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                      [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost 88 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_child_prov_ctx_new m)))
    (fun c => exists (Σ' : rts RT) (q1 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' q1 88
           /\ acc asegs m' q1 88
           /\ bytes_at asegs m' q1 (repeat (Z_to_bv 8 0) (Z.to_nat 88))) c
       /\ rt_live RT Σ' = (q1, 88) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost 88 /\ 0 < q1 /\ q1 mod 16 = 0 /\ q1 + 88 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_child_prov_ctx_new_cps : ossl_child_prov_ctx_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC TCALL0 CGH Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 < usp - 16 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-16) EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (wg_mcost_nonneg 88) as MC_88.
  (* [comment removed for export] *)
  pose proof (ossl_child_prov_ctx_new_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; lia) MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1'.
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1); [|exact WM1].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  assert (AGs1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply MU1; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AGs1) as UWF1.
  (* [comment removed for export] *)
  apply (C_CRYPTO_zalloc Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 88) (Z_to_bv 64 312064) (Z_to_bv 64 39) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 88 lo outer lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { unfold call_ok. fold usp. split; [exact ST1|]. split; [exact LOW|]. split; [unfold RT_STACK in *; lia|]. split; [exact SPT | exact SPA]. }
  { fold usp. unfold RT_STACK in *. lia. }
  { destruct CTX as [_ LK]. split; [exact TCALL0 | exact LK]. }
  { exact UWF1. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [In] in Hx |- *; tauto. }
  { lia. }
  { lia. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & v1 & Hc2 & LV2 & FRS2 & SP2 & CR2 & P0_v1 & P16_v1 & PU_v1 & CG2).
  apply Hk. exists Σ1, v1.
  split; [| split; [rewrite LV2; reflexivity|]; split; [rewrite FRS2; reflexivity|]; split; [rewrite SP2; reflexivity|]; split; [lia|]; split; [exact P0_v1|]; split; [exact P16_v1|]; split; [exact PU_v1|]; rewrite CG2; reflexivity].
  apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2). intros ms2 (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & Gt_ENVp & Gt_WR & Gt_ACC & Gt_ZER).
  exists m2.
  split; [exact RS2|].
  split; [split; [exact ART2|]; split; [exact MI2|]; split; [exact (wmono_trans asegs _ _ _ WM1 WM2) | exact ST2]|].
  split.
  { intros a Ha Ho.
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV2; do 1 right; exact He | rewrite FRS2; intros e He; exact He | lia]).
    assert (NA_v1 : ~ (v1 <= bv_unsigned a < v1 + 88)) by exact (wg_newchunk_apart RT AF Σ Σ1 m2 [(v1, 88)] v1 88 usp _ ART2 LV2 ltac:(left; reflexivity) FRS2 SP2 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha).
    pose proof (cl_split RT AF Σ m usp 16 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL.
    rewrite (PRES2 a ltac:(exact Ha) ltac:(cbn [app outside] in Ho |- *; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I)).
    rewrite (MU1 a ltac:(cbn [app outside] in Ho |- *; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I)).
    reflexivity. }
  split; [exact Gt_ENVp|]. split; [exact Gt_WR|]. split; [exact Gt_ACC|]. exact Gt_ZER.
Qed.
End ossl_child_prov_ctx_new_cps.
