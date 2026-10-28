(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition W_mal (T c DNB SSB AB S ACEIL usp : Z) : list ivl :=
  [(pc_addr T c, pc_addr T c + 4); (T + 2768, T + 3168); (0x7758c8, 0xb858f0); (DNB, DNB + 2 ^ 20); (SSB, SSB + 2 ^ 23);
   (AB, AB + S); (shad AB, shad (AB + S)); (ACEIL, usp)].

Lemma firstn_removelast_map : forall {X Y} (f : X -> Y) (l : list X) (chs : list Y), firstn (length l) chs = map f l ->
  firstn (length (removelast l)) chs = map f (removelast l).
Proof.
  intros X Y f l. induction l as [|x l IH]; intros chs H; [reflexivity|]. destruct chs as [|y chs]; [discriminate H|].
  cbn [length firstn map] in H. injection H as Hy H. destruct l as [|x' l]; [reflexivity|].
  cbn [removelast length firstn map]. rewrite Hy. f_equal. exact (IH chs H).
Qed.

Lemma stk_wr_at' : forall (m : mem) a k, stk bsegs m a (a + k) -> wr_at bsegs m a k.
Proof. intros m a k (H0 & H1 & H). split; [lia|]. split; [lia|]. intros j Hj. exact (proj1 (H (a + j) ltac:(lia))). Qed.

Section MalArt.
Variables (Σ : rtsA) (mX : mem) (c n usp : Z).
Hypothesis HA : ART_A Σ mX.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hne : ca Σ c <> [].
Hypothesis Hn1 : 1 <= n.
Hypothesis Hfit : rz_size n + n <= ClassSize c.
Hypothesis Hsp : l_ACEIL (lay Σ) <= usp.
Hypothesis Husp : usp <= USTACK_TOP.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation i := (Z.to_nat (last (ca Σ c) 0)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c (Z.to_nat (last (ca Σ c) 0))).
#[local] Notation S := (ClassSize c).
#[local] Notation W := (W_mal (l_T (lay Σ)) c (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c (Z.to_nat (last (ca Σ c) 0)))
                          (ClassSize c) (l_ACEIL (lay Σ)) usp).
#[local] Notation D := [(c, Z.to_nat (last (ca Σ c) 0))].
#[local] Notation TZ := [(pc_addr (l_T (lay Σ)) c, pc_addr (l_T (lay Σ)) c + 4); (l_T (lay Σ) + 2768, l_T (lay Σ) + 3168)].

(* [comment removed for export] *)
Lemma ma_slot0 : nth_error (r_st (pr Σ c)) i = Some CkIdle.
Proof.
  pose proof (ART_wf Σ mX HA) as (_ & HR & _). destruct HR as (_ & _ & HC & _). destruct (HC c Hc) as (_ & _ & Hall).
  assert (Hin : In (last (ca Σ c) 0) (ca Σ c)) by (rewrite (app_removelast_last (ca Σ c) 0 Hne) at 2; apply in_or_app; right; left; reflexivity).
  exact (proj2 (proj1 (Forall_forall _ _) Hall _ Hin)).
Qed.

(* [comment removed for export] *)
Lemma ma_geo :
  0 < PRB /\ SEGTOP_A <= PRB /\ K_HIGH_SHADOW_hi <= PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000
  /\ rb SB c <= AB /\ AB + S <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))) /\ rb SB c + kUserCap <= SB + 2 ^ 37
  /\ ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= kUserCap
  /\ SHB <= shad AB /\ shad (AB + S) <= 2 ^ 44 + SHB /\ 32 <= S
  /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ 0 < DNB /\ SEGTOP_A <= DNB /\ DNB + 2 ^ 20 <= l_ACEIL L /\ 0 < SSB /\ SEGTOP_A <= SSB
  /\ SSB + 2 ^ 23 <= l_ACEIL L /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ 0 <= rb SB c
  /\ PRB <= AB /\ AB + S <= PRB + 0x2000011000 /\ shad AB <= shad (AB + S) /\ pc_addr T c + 80 <= T + 2768 /\ T + 208 <= pc_addr T c.
Proof.
  pose proof (fk_slot Σ (geo_of_ART Σ mX HA) c i _ Hc ma_slot0) as (S1 & S2 & S3 & S4). pose proof (fk_prb Σ (geo_of_ART Σ mX HA)) as (P0 & P1 & P2 & P3 & P4).
  pose proof (geo_grant Σ mX HA PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & PG4 & _).
  pose proof (fk_aceil Σ (geo_of_ART Σ mX HA)) as (X1 & X2).
  pose proof (geo_grant Σ mX HA T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
  pose proof (geo_grant Σ mX HA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as (GD1 & _ & GD3 & _ & GD5).
  pose proof (geo_grant Σ mX HA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as (GS1 & _ & GS3 & _ & GS5).
  assert (HAB : 0 <= AB) by (unfold rb in S1; lia).
  pose proof (shad_rng AB ltac:(unfold rb, kUserCap in *; lia)) as (Q4 & _). pose proof (shad_rng (AB + S) ltac:(unfold rb, kUserCap in *; lia)) as (_ & Q5).
  assert (Q3 : shad AB <= shad (AB + S)) by (apply fk_shad_mono; lia).
  unfold rb, kUserCap, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, pc_addr in *. repeat split; try lia.
Qed.

Ltac geo := pose proof ma_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
  & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29);
  pose proof (sa_disj Σ mX HA) as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
Ltac dj := unfold fa, RIS_of in *; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, rb, kUserCap, kFaCap, apart, pc_addr in *; lia.
Ltac w8 t1 t2 t3 t4 t5 t6 t7 t8 := unfold W_mal; cbn [disjoint_from];
  split; [t1|]; split; [t2|]; split; [t3|]; split; [t4|]; split; [t5|]; split; [t6|]; split; [t7|]; split; [t8 | exact I].

Lemma ma_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from IZ_A a k -> disjoint_from W a k.
Proof.
  intros a k H1 H2 HZ. geo. cbn [IZ_A disjoint_from] in HZ. destruct HZ as [HZ _].
  w8 ltac:(clear - H1 H2 T5 K28 K29; dj) ltac:(clear - H1 H2 T5; dj) ltac:(clear - HZ; dj) ltac:(clear - H2 K17; dj) ltac:(clear - H2 K20; dj)
     ltac:(clear - H2 K2 K25; dj) ltac:(clear - H2 K11; dj) ltac:(clear - H2 K22; dj).
Qed.

Lemma ma_Tz : forall a k, T <= a -> a + k <= T + 4096 -> disjoint_from TZ a k -> disjoint_from W a k.
Proof.
  intros a k H1 H2 HZ. geo. cbn [disjoint_from] in HZ. destruct HZ as (HZ1 & HZ2 & _).
  w8 ltac:(clear - HZ1; dj) ltac:(clear - HZ2; dj) ltac:(clear - H1 H2 T5; dj) ltac:(clear - H1 H2 ATD; dj) ltac:(clear - H1 H2 ATS; dj)
     ltac:(clear - H1 H2 ATP K25 K26; dj) ltac:(clear - H1 H2 T4 K11 K12 K27; dj) ltac:(clear - H2 K15; dj).
Qed.

Lemma ma_grant : forall j b gn a k, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from W a k.
Proof.
  intros j b gn a k Hj Hjr H1 H2. geo. pose proof (geo_grant Σ mX HA b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (Hj2 : j <> 2%nat) by (clear - Hjr; lia). assert (Hj0 : j <> 0%nat) by (clear - Hjr; lia).
  assert (Hj6 : j <> 6%nat) by (clear - Hjr; lia). assert (Hj7 : j <> 7%nat) by (clear - Hjr; lia).
  pose proof (sa_apart Σ mX HA j 2 (b, gn) (T, 4096) Hj2 Hj eq_refl) as HT1.
  pose proof (sa_apart Σ mX HA j 0 (b, gn) (PRB, 0x2000011000) Hj0 Hj eq_refl) as HT2.
  pose proof (sa_apart Σ mX HA j 6 (b, gn) (DNB, 0x100000) Hj6 Hj eq_refl) as HT3.
  pose proof (sa_apart Σ mX HA j 7 (b, gn) (SSB, 0x800000) Hj7 Hj eq_refl) as HT4.
  cbn [fst snd] in HT1, HT2, HT3, HT4.
  w8 ltac:(clear - H1 H2 HT1 K28 K29; dj) ltac:(clear - H1 H2 HT1; dj) ltac:(clear - H1 H2 B1 B5; dj) ltac:(clear - H1 H2 HT3; dj)
     ltac:(clear - H1 H2 HT4; dj) ltac:(clear - H1 H2 HT2 K25 K26; dj) ltac:(clear - H1 H2 B1 B4 K11 K12 K27; dj) ltac:(clear - H2 B3; dj).
Qed.

Lemma ma_ris : forall a k, RIS_of SB <= a -> a + k <= RIS_of SB + 4096 -> disjoint_from W a k.
Proof.
  intros a k H1 H2. geo.
  w8 ltac:(clear - H1 H2 ATP K5 K6 K28 K29; dj) ltac:(clear - H1 H2 ATP K5 K6; dj) ltac:(clear - H1 K2 K5; dj) ltac:(clear - H1 H2 APD K5 K6; dj)
     ltac:(clear - H1 H2 APS K5 K6; dj) ltac:(clear - Hc H1 K7 K8 K9 K10; dj) ltac:(clear - H1 K3 K5 K12; dj) ltac:(clear - H2 K4 K6; dj).
Qed.

Lemma ma_fa : forall c' a k, 1 <= c' <= 31 -> fa SB c' <= a -> a + k <= fa SB c' + kFaCap -> disjoint_from W a k.
Proof.
  intros c' a k Hc' H1 H2. geo.
  w8 ltac:(clear - Hc' H1 H2 ATP K5 K6 K28 K29; dj) ltac:(clear - Hc' H1 H2 ATP K5 K6; dj) ltac:(clear - Hc' H1 K2 K5; dj)
     ltac:(clear - Hc' H1 H2 APD K5 K6; dj) ltac:(clear - Hc' H1 H2 APS K5 K6; dj)
     ltac:(clear - Hc Hc' H1 H2 K7 K8 K9 K10; dj) ltac:(clear - Hc' H1 K3 K5 K12; dj) ltac:(clear - Hc' H2 K4 K6; dj).
Qed.

Lemma ma_slot : forall c' i' st a k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  p_abeg SB c' i' <= a -> a + k <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a k.
Proof.
  intros c' i' st a k Hc' Hn' HD H1 H2. geo.
  assert (Hne' : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [<-|X]; [right; intros E; apply HD; left; rewrite E; reflexivity | left; exact X]).
  pose proof (slot_apart Σ mX HA c i c' i' _ _ Hc Hc' ma_slot0 Hn' Hne') as Y.
  pose proof (fk_slot Σ (geo_of_ART Σ mX HA) c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (Z5 : PRB <= p_abeg SB c' i' /\ p_abeg SB c' i' + ClassSize c' <= PRB + 0x2000011000) by (clear - Hc' Z1 Z2 Z3 K5 K6; unfold rb, kUserCap in *; lia). destruct Z5 as (Z5 & Z6).
  w8 ltac:(clear - H1 H2 ATP Z5 Z6 K28 K29; dj) ltac:(clear - H1 H2 ATP Z5 Z6; dj) ltac:(clear - H1 K2 Z5; dj) ltac:(clear - H1 H2 APD Z5 Z6; dj)
     ltac:(clear - H1 H2 APS Z5 Z6; dj) ltac:(clear - H1 H2 Y; dj) ltac:(clear - H1 K3 Z5 K12; dj) ltac:(clear - H2 K4 Z6; dj).
Qed.

Lemma ma_shad_slot : forall c' i' st a k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  shad (p_abeg SB c' i') <= a -> a + k <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a k.
Proof.
  intros c' i' st a k Hc' Hn' HD H1 H2. geo.
  assert (Hne' : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [<-|X]; [right; intros E; apply HD; left; rewrite E; reflexivity | left; exact X]).
  pose proof (slot_apart Σ mX HA c i c' i' _ _ Hc Hc' ma_slot0 Hn' Hne') as Y.
  pose proof (fk_slot Σ (geo_of_ART Σ mX HA) c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (Ysh : shad (p_abeg SB c' i' + ClassSize c') <= shad AB \/ shad (AB + S) <= shad (p_abeg SB c' i')) by (destruct Y as [Y|Y]; [right | left]; apply fk_shad_mono; exact Y).
  pose proof (shad_lo (p_abeg SB c' i') ltac:(clear - Hc' Z1 K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (shad_hi (p_abeg SB c' i' + ClassSize c') ltac:(clear - Hc' Z1 Z2 Z3 K4 K5 K6 K23; unfold rb, kUserCap in *; lia)) as Q2.
  w8 ltac:(clear - H1 H2 T4 Q1 Q2 K28 K29; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 Q1; dj) ltac:(clear - H1 H2 D4 Q1 Q2; dj)
     ltac:(clear - H1 H2 S4 Q1 Q2; dj) ltac:(clear - H2 K3 K25 Q2; dj) ltac:(clear - H1 H2 Ysh; dj) ltac:(clear - H2 Q2 K22; dj).
Qed.

Lemma ma_shad_reg : forall c' a k, 1 <= c' <= 31 -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + k <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a k.
Proof.
  intros c' a k Hc' H1 H2. geo.
  assert (Hau : 0 <= ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) by (clear - Hc'; apply Z.mul_nonneg_nonneg; pose proof (ClassSize_range c' Hc'); lia).
  assert (Hr : shad (rb SB c' + 2 ^ 32) <= shad AB \/ shad (AB + S) <= shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c'))))).
  { destruct (Z.eq_dec c' c) as [->|X]; [right; apply fk_shad_mono; clear - K8; lia|].
    assert (c' < c \/ c < c') by (clear - X; lia). destruct H; [left | right]; apply fk_shad_mono; clear - H K7 K8 K10 Hau; unfold rb, kUserCap in *; lia. }
  pose proof (shad_lo (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) ltac:(clear - Hc' Hau K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (shad_hi (rb SB c' + 2 ^ 32) ltac:(clear - Hc' K4 K5 K6 K23; unfold rb in *; lia)) as Q2.
  w8 ltac:(clear - H1 H2 T4 Q1 Q2 K28 K29; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 Q1; dj) ltac:(clear - H1 H2 D4 Q1 Q2; dj)
     ltac:(clear - H1 H2 S4 Q1 Q2; dj) ltac:(clear - H2 K3 K25 Q2; dj) ltac:(clear - H1 H2 Hr; dj) ltac:(clear - H2 Q2 K22; dj).
Qed.

Lemma ma_shad_app : forall lo hi a k, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= PRB \/ PRB + 0x2000011000 <= lo) ->
  (forall k' s', nth_error (sec Σ) k' = Some s' -> In k' [] -> hi <= s_mb s' \/ s_mb s' + smsz (s_n s') <= lo) ->
  shad lo <= a -> a + k <= shad hi -> disjoint_from W a k.
Proof.
  intros lo hi a k H0 H47 Hoff _ H1 H2. geo.
  assert (Hr : shad hi <= shad AB \/ shad (AB + S) <= shad lo).
  { destruct Hoff as [Ho|Ho]; [left | right]; apply fk_shad_mono; clear - Ho K25 K26; lia. }
  pose proof (shad_lo lo H0) as Q1. pose proof (shad_hi hi H47) as Q2.
  w8 ltac:(clear - H1 H2 T4 Q1 Q2 K28 K29; dj) ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 Q1; dj) ltac:(clear - H1 H2 D4 Q1 Q2; dj)
     ltac:(clear - H1 H2 S4 Q1 Q2; dj) ltac:(clear - H2 K3 K25 Q2; dj) ltac:(clear - H1 H2 Hr; dj) ltac:(clear - H2 Q2 K22; dj).
Qed.

Lemma ma_secmap : forall k s a k', nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + k' <= s_mb s + smsz (s_n s) ->
  disjoint_from W a k'.
Proof.
  intros k s a k' Hk _ H1 H2. geo. pose proof (fk_map Σ (geo_of_ART Σ mX HA) k s Hk) as (Hn' & Y1 & Y3 & Y5 & Yp & _ & YG & _).
  pose proof (proj1 (Forall_forall _ _) YG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as YT.
  pose proof (proj1 (Forall_forall _ _) YG (DNB, 0x100000) ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as YD.
  pose proof (proj1 (Forall_forall _ _) YG (SSB, 0x800000) ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as YS.
  pose proof (geo_wf Σ mX HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (_ & _ & _ & Y4 & _) & _).
  cbn [fst snd] in *.
  w8 ltac:(clear - H1 H2 YT K28 K29; dj) ltac:(clear - H1 H2 YT; dj) ltac:(clear - H1 H2 Y5 Y1; dj) ltac:(clear - H1 H2 YD; dj)
     ltac:(clear - H1 H2 YS; dj) ltac:(clear - H1 H2 Yp K25 K26; dj) ltac:(clear - H1 H2 Y1 Y4 K11 K12 K27; dj) ltac:(clear - H2 Y3; dj).
Qed.

Lemma ma_stack : forall a k, usp <= a -> a + k <= USTACK_TOP -> disjoint_from W a k.
Proof.
  intros a k H1 H2. geo.
  w8 ltac:(clear - H1 K15 K28 K29 Hsp; dj) ltac:(clear - H1 K15 Hsp; dj) ltac:(clear - H1 K22 Hsp; dj) ltac:(clear - H1 K18 Hsp; dj)
     ltac:(clear - H1 K21 Hsp; dj) ltac:(clear - H1 K4 K26 Hsp; dj) ltac:(clear - H1 K12 K22 Hsp; dj) ltac:(clear - H1; dj).
Qed.

(* [comment removed for export] *)
Lemma ma_pclass : forall c', 1 <= c' <= 31 -> c' <> c -> disjoint_from TZ (pc_addr T c') 80.
Proof. intros c' Hc' Hcc. cbn [disjoint_from]. unfold pc_addr. split; [lia|]. split; [lia | exact I]. Qed.

(* [comment removed for export] *)
Lemma ma_client : forall x, aclient (live Σ) (frames Σ) usp x -> outside W x.
Proof using HA Hc Hne Hn1 Hfit Hsp Husp.
  intros x Hx. apply (kv_client Σ W D [] IZ_A usp (geo_of_ART Σ mX HA) ma_img ma_grant ma_slot ma_shad_app ma_secmap ma_stack
                        (dsjb_all IZ_A CLIENT_STATIC ltac:(vm_compute; reflexivity)) (live Σ)); [|exact Hx].
  intros p' n' Hin. pose proof (ART_wf Σ mX HA) as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
  destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
  + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
    intros [E|[]]. injection E as <- <-. rewrite ma_slot0 in Hn'. discriminate.
  + right. destruct (In_nth_error _ _ Hs) as (k & Hk). exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|].
    split; [reflexivity | intros []].
Qed.

(* [comment removed for export] *)
Lemma ma_consts : forall (m' : mem), munch W mX m' -> wmono bsegs mX m' -> consts_rep L m'.
Proof.
  intros m' MU WM. apply (consts_rep_frame L mX m' (ART_consts Σ mX HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply ma_Tz; [lia | lia|]. cbn. unfold pc_addr. split; [lia|]. split; [lia | exact I].
  + apply (kv_consts Σ W TZ IZ_A ma_img ma_Tz ma_grant); [apply dsjb_all; vm_compute; reflexivity | cbn; unfold pc_addr; split; [lia|split; [lia | exact I]] | exact Ha | exact NE].
Qed.

Lemma ma_wf_prem : ca_init Σ = true /\ Z.of_nat (length (removelast (ca Σ c))) = Z.of_nat (length (ca Σ c)) - 1.
Proof.
  split.
  - pose proof (ART_wf Σ mX HA) as (_ & HR & _). destruct HR as (_ & _ & _ & HI & _).
    destruct (ca_init Σ) eqn:E; [reflexivity|]. exfalso. exact (Hne (HI eq_refl c)).
  - rewrite (app_removelast_last (ca Σ c) 0 Hne) at 2. rewrite length_app. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Theorem mal_ART : forall (m' : mem) (D' : depot), munch W mX m' -> wmono bsegs mX m' ->
  ahdr m' (AB + rz_size n - 16) n -> lch_if m' AB (AB + rz_size n - 16) n ->
  bytes_at bsegs m' (shad AB) (farun (rz_size n / 8) ++ ushadow n) ->
  bytes_at bsegs m' (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  pc_cells m' (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  depot_rep D' (DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB m' -> hash_of (d_hs D') 1 = hash_of (d_hs (dep Σ)) 1 ->
  rt_wf (mal_hit Σ c n D') ->
  ART_A (mal_hit Σ c n D') m'.
Proof using HA Hc Hne Hn1 Hfit Hsp Husp.
  intros m' D' MU WM HD HL SH1 SH2 PC DR Dh WF.
  assert (HDS : forall k s, nth_error (sec Σ) k = Some s -> ~ In k []) by (intros k s _ []).
  pose proof (kv_reg Σ W [] (geo_of_ART Σ mX HA) (ris_of_whole SB W [] ma_ris) (fun c0 a k Hc0 _ => ma_fa c0 a k Hc0)
                (fun c0 a k Hc0 _ => ma_shad_reg c0 a k Hc0)) as KR.
  pose proof (kv_pchunk Σ W D (geo_of_ART Σ mX HA) ma_slot ma_shad_slot) as KP.
  pose proof (kv_schunk Σ W [] (geo_of_ART Σ mX HA) ma_shad_app ma_secmap) as KS.
  pose proof ma_wf_prem as (Hinit & Hlen).
  apply ART_intro; [exact WF | | | | | | | | | | |]; cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 ia_init credit live frames mal_hit].
  - exact (ma_consts m' MU WM).
  - intros c' Hc'. unfold mal_hit. cbn [pr]. destruct (Z.eqb_spec c' c) as [->|Hcc].
    + apply reg_rep_upd. exact (reg_rep_transport W _ c _ mX m' (ART_prim Σ mX HA c Hc) MU WM (KR c Hc ltac:(intros []))).
    + exact (reg_rep_transport W _ c' _ mX m' (ART_prim Σ mX HA c' Hc') MU WM (KR c' Hc' ltac:(intros []))).
  - intros c' Hc'. unfold mal_hit. cbn [ca ca_init]. destruct (Z.eqb_spec c' c) as [->|Hcc].
    + (* [comment removed for export] *)
      pose proof (ART_cache Σ mX HA c Hc) as (_ & chs & CH1 & CH2 & CH3). rewrite Hinit in *. split; [rewrite Hlen; exact PC|].
      exists chs. split; [|split; [exact CH2 | exact (firstn_removelast_map (cpw c) (ca Σ c) chs CH3)]].
      apply (u32arr_transport bsegs W mX m' _ _ CH1 MU WM). rewrite CH2. change (4 * Z.of_nat 16) with 64. geo.
      w8 ltac:(clear; unfold pc_addr; lia) ltac:(clear - K28; unfold pc_addr in *; lia) ltac:(clear - K14 K15 T5 K28 K29; dj)
         ltac:(clear - K14 K15 ATD K28 K29; dj) ltac:(clear - K14 K15 ATS K28 K29; dj)
         ltac:(clear - K14 K15 ATP K25 K26 K28 K29; dj) ltac:(clear - K14 K15 T4 K11 K12 K27 K28 K29; dj) ltac:(clear - K15 K28 K29; dj).
    + exact (pclass_rep_transport W _ c' _ _ mX m' (ART_cache Σ mX HA c' Hc') MU WM (kv_pclass Σ W TZ ma_Tz c' Hc' (ma_pclass c' Hc' Hcc))).
  - destruct (ART_chunk Σ mX HA) as [P Sc]. split.
    + intros c' i' st Hc' Hn'. unfold mal_hit in Hn'. cbn [pr] in Hn'. destruct (Z.eqb_spec c' c) as [->|Hcc].
      * unfold upd_reg in Hn'. cbn [r_st] in Hn'. rewrite nth_error_upd_ck in Hn'. destruct (Nat.eqb_spec i i') as [<-|Hii].
        -- destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); [injection Hn' as <- | discriminate].
           (* [comment removed for export] *)
           destruct (P c i CkIdle Hc ma_slot0) as (St & _).
           split; [apply (wr_at_wmono mX m' _ _ (stk_wr_at' mX _ _ St) WM)|]. split; [exact HD|]. split; [exact HL|].
           split; [exact SH1 | exact SH2].
        -- exact (pchunk_transport W _ c i' st mX m' (P c i' st Hc Hn') MU WM (KP c i' st Hc Hn' ltac:(intros [E|[]]; injection E as E2; exact (Hii E2)))).
      * exact (pchunk_transport W _ c' i' st mX m' (P c' i' st Hc' Hn') MU WM (KP c' i' st Hc' Hn' ltac:(intros [E|[]]; injection E as E1 E2; exact (Hcc (eq_sym E1))))).
    + intros k s Hk. exact (schunk_transport W k s mX m' (Sc k s Hk) MU WM (KS k s Hk (HDS k s Hk))).
  - exact (sec_rep_transport W Σ mX m' (ART_sec Σ mX HA) MU WM (kv_sec Σ W IZ_A (geo_of_ART Σ mX HA) ma_img ma_grant ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (quar_rep_transport W Σ mX m' (ART_quar Σ mX HA) MU WM
             (kv_quar Σ W D TZ IZ_A (geo_of_ART Σ mX HA) ma_img ma_Tz ma_slot ltac:(cbn; unfold qcacheT, pc_addr; split; [lia|split; [lia | exact I]])
                ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros i' Hi' [E|[]]; injection E as E1 E2; pose proof ma_slot0 as X; rewrite E2 in X; rewrite E1 in X; rewrite X in Hi'; discriminate)
                ltac:(pose proof (ART_wf Σ mX HA) as (_ & _ & _ & _ & HQw & _); exact (proj1 (proj2 (proj2 HQw)))))).
  - unfold dep_rep. rewrite Dh. exact DR.
  - exact (fs_rep_transport W Σ mX m' (ART_fs Σ mX HA) MU WM (kv_fs Σ W [] TZ IZ_A (geo_of_ART Σ mX HA) ma_img ma_Tz ma_grant ma_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(cbn; unfold pc_addr; split; [lia|split; [lia | exact I]]))).
  - exact (ia_rep_transport W Σ mX m' (ART_ia Σ mX HA) MU WM (kv_ia W IZ_A ma_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ mX m' (ART_shadow Σ mX HA) MU WM (kv_shadow Σ W [] (geo_of_ART Σ mX HA) ma_shad_app)).
  - exact (vis_rep_wmono _ mX m' (ART_vis Σ mX HA) WM).
Qed.

End MalArt.
