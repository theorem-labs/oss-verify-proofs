(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freeC RT_freeD RT_refreekA RT_refreekC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma se_shad_des_r : forall (Σ : rtsA) j0 jB st0 stB usp, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
  nth_error (r_st (pr Σ 24)) jB = Some stB -> l_ACEIL (lay Σ) + 0xFFB0 <= usp ->
  forall j st, nth_error (r_st (pr Σ 24)) j = Some st ->
  disjoint_from (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp) (shad (p_abeg (l_SB (lay Σ)) 24 j)) 1024.
Proof.
  intros Σ j0 jB st0 stB usp HG Hj0 HjB Hsp j st Hj.
  pose proof (se_geo_r Σ j0 jB st0 stB HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj_r Σ HG) as (T5 & T4 & ATP).
  pose proof (fk_slot Σ HG 24 j st ltac:(lia) Hj) as (Z1 & Z2 & Z3 & Z4). change (ClassSize 24) with 8192 in *.
  pose proof (shad_lo (p_abeg (l_SB (lay Σ)) 24 j) ltac:(clear - Z1 K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (fk_shad_le2 (p_abeg (l_SB (lay Σ)) 24 j) 8192 ltac:(clear - Z1 K1 K5; unfold rb in *; lia) ltac:(lia)) as E1. change (8192 / 8) with 1024 in E1.
  pose proof (shad_hi (p_abeg (l_SB (lay Σ)) 24 j + 8192) ltac:(clear - Z1 Z2 Z3 K4 K5 K6 K16; unfold rb, kUserCap in *; lia)) as Q2.
  unfold W_E. cbn [disjoint_from].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - K3 K5 K7 Q2 E1; unfold K_HIGH_SHADOW_hi, SHB, rb in *; lia|].
  split; [clear - K3 K5 K9 Q2 E1; unfold K_HIGH_SHADOW_hi, SHB, rb in *; lia|].
  split; [clear - Q2 E1 K15 Hsp; unfold SHB in *; lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma se_grant67_r : forall (Σ : rtsA) j0 jB st0 stB usp, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
  nth_error (r_st (pr Σ 24)) jB = Some stB -> l_ACEIL (lay Σ) + 0xFFB0 <= usp ->
  forall j b gn a k, nth_error (startup_grants (lay Σ)) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat -> b <= a -> a + k <= b + gn ->
  disjoint_from (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp) a k.
Proof.
  intros Σ j0 jB st0 stB usp HG Hj0 HjB Hsp j b gn a k Hj Hjr H1 H2.
  pose proof (se_geo_r Σ j0 jB st0 stB HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (g_grant Σ HG b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (HT1 : apart b gn (l_T (lay Σ)) 4096).
  { pose proof (g_apart Σ HG 2 j (l_T (lay Σ), 4096) (b, gn) ltac:(lia) eq_refl Hj) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  assert (HT2 : apart b gn (l_PRB (lay Σ)) 0x2000011000).
  { pose proof (g_apart Σ HG 0 j (l_PRB (lay Σ), 0x2000011000) (b, gn) ltac:(lia) eq_refl Hj) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  unfold W_E. cbn [disjoint_from]. unfold apart in *.
  split; [clear - H1 H2 HT1; lia|]. split; [clear - H1 H2 HT1; lia|]. split; [clear - H1 H2 HT1; lia|].
  split; [clear - H1 H2 HT2 K5 K6 K7 K8 K11 K12; unfold rb, kUserCap in *; lia|].
  split; [clear - H1 H2 HT2 K5 K6 K9 K10 K11 K12; unfold rb, kUserCap in *; lia|].
  split; [clear - H2 B3 Hsp; lia | exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)