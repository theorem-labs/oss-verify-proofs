(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition W_E (T b0 bB usp : Z) : list ivl :=
  [(T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (b0, b0 + 8192); (bB, bB + 8192); (usp - 2400, usp)].
Definition TZ_E (T : Z) : list ivl := [(T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792)].

Section SegE.
Variables (Σ : rtsA) (j0 jB : nat) (st0 stB : ckst) (usp : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis HjB : nth_error (r_st (pr Σ 24)) jB = Some stB.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).
#[local] Notation D := [(24, j0); (24, jB)].
#[local] Notation TZ := (TZ_E (l_T (lay Σ))).

(* [comment removed for export] *)
Lemma se_geo :
  0 < PRB /\ SEGTOP_A <= PRB /\ K_HIGH_SHADOW_hi <= PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000
  /\ rb SB 24 <= b0 /\ b0 + 8192 <= rb SB 24 + kUserCap /\ rb SB 24 <= bB /\ bB + 8192 <= rb SB 24 + kUserCap
  /\ rb SB 24 + kUserCap <= SB + 2 ^ 37 /\ 0 <= rb SB 24
  /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof using HG Hj0 HjB.
  clear - HG Hj0 HjB.
  pose proof (fk_slot Σ HG 24 j0 st0 ltac:(lia) Hj0) as (A1 & A2 & A3 & _). pose proof (fk_slot Σ HG 24 jB stB ltac:(lia) HjB) as (B1 & B2 & B3 & _).
  pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
  pose proof (g_grant Σ HG PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & PG4 & _).
  pose proof (fk_aceil Σ HG) as (X1 & X2).
  pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
  change (ClassSize 24) with 8192 in *.
  unfold rb, kUserCap, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. repeat split; lia.
Qed.

Lemma se_disj :
  (T + 4096 <= 0x10000 \/ SEGTOP_A <= T) /\ (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T)
  /\ (T + 4096 <= PRB \/ PRB + 0x2000011000 <= T).
Proof using HG.
  clear - HG.
  pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & _ & GT4 & GT5).
  pose proof (g_apart Σ HG 0 2 _ _ ltac:(lia) eq_refl eq_refl) as A02. cbn [fst snd] in *. unfold apart in *.
  split; [exact GT5|]. split; [exact GT4|]. lia.
Qed.

Ltac geo := pose proof se_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16);
  pose proof se_disj as (T5 & T4 & ATP).
Ltac dj := unfold fa, RIS_of in *; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, rb, kUserCap, kFaCap, apart in *; lia.
Ltac w6 t1 t2 t3 t4 t5 t6 := unfold W_E; cbn [disjoint_from];
  split; [t1|]; split; [t2|]; split; [t3|]; split; [t4|]; split; [t5|]; split; [t6 | exact I].

Lemma se_apart : forall j j' g1 g2, j <> j' -> nth_error (startup_grants L) j = Some g1 -> nth_error (startup_grants L) j' = Some g2 ->
  apart (fst g1) (snd g1) (fst g2) (snd g2).
Proof using HG.
  clear - HG. intros j j' g1 g2 Hne H1 H2. destruct (Nat.lt_ge_cases j j') as [Hl|Hl]; [exact (g_apart Σ HG j j' g1 g2 Hl H1 H2)|].
  pose proof (g_apart Σ HG j' j g2 g1 ltac:(lia) H2 H1) as X. unfold apart in *. lia.
Qed.

Lemma se_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from [] a k -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros a k H1 H2 _. geo.
  w6 ltac:(clear - H1 H2 T5; dj) ltac:(clear - H1 H2 T5; dj) ltac:(clear - H1 H2 T5; dj) ltac:(clear - K12 K11 K6 H2 K2 K5 K7; dj)
     ltac:(clear - K12 K11 K6 H2 K2 K5 K9; dj) ltac:(clear - H2 K15 Hsp; dj).
Qed.

Lemma se_Tz : forall a k, T <= a -> a + k <= T + 4096 -> disjoint_from TZ a k -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros a k H1 H2 HZ. geo. unfold TZ_E in HZ. cbn [disjoint_from] in HZ. destruct HZ as (Z1 & Z2 & Z3 & _).
  w6 ltac:(clear - Z1; dj) ltac:(clear - Z2; dj) ltac:(clear - Z3; dj) ltac:(clear - H1 H2 ATP K5 K6 K7 K8 K11 K12; dj)
     ltac:(clear - H1 H2 ATP K5 K6 K9 K10 K11 K12; dj) ltac:(clear - H2 K14 Hsp; dj).
Qed.

Lemma se_grant : forall j b gn a k, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros j b gn a k Hj Hjr H1 H2. geo. pose proof (g_grant Σ HG b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (Hj2 : j <> 2%nat) by (clear - Hjr; lia). assert (Hj0' : j <> 0%nat) by (clear - Hjr; lia).
  pose proof (se_apart j 2 (b, gn) (T, 4096) Hj2 Hj eq_refl) as HT1. pose proof (se_apart j 0 (b, gn) (PRB, 0x2000011000) Hj0' Hj eq_refl) as HT2.
  cbn [fst snd] in HT1, HT2.
  w6 ltac:(clear - H1 H2 HT1; dj) ltac:(clear - H1 H2 HT1; dj) ltac:(clear - H1 H2 HT1; dj) ltac:(clear - K6 H1 H2 HT2 K5 K7 K8 K11 K12; dj)
     ltac:(clear - K6 H1 H2 HT2 K5 K9 K10 K11 K12; dj) ltac:(clear - H2 B3 Hsp; dj).
Qed.

Lemma se_ris : forall a k, RIS_of SB <= a -> a + k <= RIS_of SB + 4096 -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros a k H1 H2. geo.
  w6 ltac:(clear - H1 H2 ATP K5 K6; dj) ltac:(clear - H1 H2 ATP K5 K6; dj) ltac:(clear - H1 H2 ATP K5 K6; dj) ltac:(clear - H1 K8 K11; dj)
     ltac:(clear - H1 K10 K11; dj) ltac:(clear - H2 K4 K6 Hsp; dj).
Qed.

Lemma se_fa : forall c' a k, 1 <= c' <= 31 -> fa SB c' <= a -> a + k <= fa SB c' + kFaCap -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros c' a k Hc' H1 H2. geo.
  w6 ltac:(clear - Hc' H1 H2 ATP K5 K6; dj) ltac:(clear - Hc' H1 H2 ATP K5 K6; dj) ltac:(clear - Hc' H1 H2 ATP K5 K6; dj)
     ltac:(clear - K11 K6 K5 Hc' H1 H2 K7 K8 K12; dj) ltac:(clear - K11 K6 K5 Hc' H1 H2 K9 K10 K12; dj) ltac:(clear - Hc' H2 K4 K6 Hsp; dj).
Qed.

Lemma se_slot : forall c' i' st a k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  p_abeg SB c' i' <= a -> a + k <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros c' i' st a k Hc' Hn' HD H1 H2. geo.
  assert (Hne0 : c' <> 24 \/ i' <> j0) by (destruct (Z.eq_dec c' 24) as [->|X]; [right; intros ->; apply HD; left; reflexivity | left; exact X]).
  assert (HneB : c' <> 24 \/ i' <> jB) by (destruct (Z.eq_dec c' 24) as [->|X]; [right; intros ->; apply HD; right; left; reflexivity | left; exact X]).
  pose proof (g_slot_apart Σ HG 24 j0 c' i' _ _ ltac:(lia) Hc' Hj0 Hn' ltac:(destruct Hne0; [left; congruence | right; congruence])) as Y0.
  pose proof (g_slot_apart Σ HG 24 jB c' i' _ _ ltac:(lia) Hc' HjB Hn' ltac:(destruct HneB; [left; congruence | right; congruence])) as YB.
  change (ClassSize 24) with 8192 in Y0, YB.
  pose proof (fk_slot Σ HG c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (Z5 : PRB <= p_abeg SB c' i' /\ p_abeg SB c' i' + ClassSize c' <= PRB + 0x2000011000) by (clear - Hc' Z1 Z2 Z3 K5 K6; unfold rb, kUserCap in *; lia). destruct Z5 as (Z5 & Z6).
  w6 ltac:(clear - H1 H2 ATP Z5 Z6; dj) ltac:(clear - H1 H2 ATP Z5 Z6; dj) ltac:(clear - H1 H2 ATP Z5 Z6; dj) ltac:(clear - H1 H2 Y0; dj)
     ltac:(clear - H1 H2 YB; dj) ltac:(clear - H2 K4 Z6 Hsp; dj).
Qed.

Lemma se_shad_slot : forall c' i' st a k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  shad (p_abeg SB c' i') <= a -> a + k <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros c' i' st a k Hc' Hn' HD H1 H2. geo.
  pose proof (fk_slot Σ HG c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  pose proof (shad_lo (p_abeg SB c' i') ltac:(clear - Hc' Z1 K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (shad_hi (p_abeg SB c' i' + ClassSize c') ltac:(clear - Hc' Z1 Z2 Z3 K4 K5 K6 K16; unfold rb, kUserCap in *; lia)) as Q2.
  w6 ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - K12 K11 K6 K5 H2 K3 K7 Q2; dj)
     ltac:(clear - K12 K11 K6 K5 H2 K3 K9 Q2; dj) ltac:(clear - H2 Q2 K15 Hsp; dj).
Qed.

Lemma se_shad_reg : forall c' a k, 1 <= c' <= 31 -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + k <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros c' a k Hc' H1 H2. geo.
  assert (Hau : 0 <= ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) by (clear - Hc'; apply Z.mul_nonneg_nonneg; pose proof (ClassSize_range c' Hc'); lia).
  pose proof (shad_lo (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) ltac:(clear - Hc' Hau K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (shad_hi (rb SB c' + 2 ^ 32) ltac:(clear - Hc' K4 K5 K6 K16; unfold rb in *; lia)) as Q2.
  w6 ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - K12 K11 K6 K5 H2 K3 K7 Q2; dj)
     ltac:(clear - K12 K11 K6 K5 H2 K3 K9 Q2; dj) ltac:(clear - H2 Q2 K15 Hsp; dj).
Qed.

Lemma se_shad_app : forall lo hi a k, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= PRB \/ PRB + 0x2000011000 <= lo) ->
  (forall k' s', nth_error (sec Σ) k' = Some s' -> In k' [] -> hi <= s_mb s' \/ s_mb s' + smsz (s_n s') <= lo) ->
  shad lo <= a -> a + k <= shad hi -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros lo hi a k H0 H47 Hoff _ H1 H2. geo.
  pose proof (shad_lo lo H0) as Q1. pose proof (shad_hi hi H47) as Q2.
  w6 ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - K12 K11 K6 K5 H2 K3 K7 Q2; dj)
     ltac:(clear - K12 K11 K6 K5 H2 K3 K9 Q2; dj) ltac:(clear - H2 Q2 K15 Hsp; dj).
Qed.

Lemma se_secmap : forall k s a k', nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + k' <= s_mb s + smsz (s_n s) ->
  disjoint_from W a k'.
Proof using HG Hj0 HjB Hsp.
  intros k s a k' Hk _ H1 H2. geo. pose proof (fk_map Σ HG k s Hk) as (Hn' & Y1 & Y3 & Y5 & Yp & _ & YG & _).
  pose proof (proj1 (Forall_forall _ _) YG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as YT.
  cbn [fst snd] in *.
  w6 ltac:(clear - H1 H2 YT; dj) ltac:(clear - H1 H2 YT; dj) ltac:(clear - H1 H2 YT; dj) ltac:(clear - K6 H1 H2 Yp K5 K7 K8 K11 K12; dj)
     ltac:(clear - K6 H1 H2 Yp K5 K9 K10 K11 K12; dj) ltac:(clear - H2 Y3 Hsp; dj).
Qed.

Lemma se_stack : forall a k, usp <= a -> a + k <= USTACK_TOP -> disjoint_from W a k.
Proof using HG Hj0 HjB Hsp.
  intros a k H1 H2. geo.
  w6 ltac:(clear - H1 K14 Hsp; dj) ltac:(clear - H1 K14 Hsp; dj) ltac:(clear - H1 K14 Hsp; dj) ltac:(clear - H1 K4 K6 K8 K11 Hsp; dj)
     ltac:(clear - H1 K4 K6 K10 K11 Hsp; dj) ltac:(clear - H1; dj).
Qed.

End SegE.
