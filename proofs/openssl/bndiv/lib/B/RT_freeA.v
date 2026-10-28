(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition W_A1 (T DNB SSB M n usp : Z) : list ivl :=
  [(T + 2824, T + 2840); (0x7758c8, 0xb858f0); (DNB, DNB + 2 ^ 20); (SSB, SSB + 2 ^ 23); (M, M + 24);
   (shad (M + 16), shad (M + 16) + ru8 n / 8); (usp - 2400, usp - 2128)].
Definition IZ_A : list ivl := [(0x7758c8, 0xb858f0)].

Lemma shad_add8' : forall a x, a mod 8 = 0 -> x mod 8 = 0 -> shad (a + x) = shad a + x / 8.
Proof.
  intros a x Ha Hx. unfold shad. apply Z.mod_divide in Ha, Hx; try (clear; lia). destruct Ha as [qa Ea]. destruct Hx as [qx Ex]. subst a x.
  replace (qa * 8 + qx * 8) with ((qa + qx) * 8) by ring. rewrite !Z.div_mul by lia. lia.
Qed.

Lemma shad_lo : forall x, 0 <= x -> SHB <= shad x.
Proof. intros x Hx. unfold shad. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma shad_hi : forall x, x <= 2 ^ 47 -> shad x <= 2 ^ 44 + SHB.
Proof. intros x Hx. unfold shad. assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. Qed.

Lemma shad_rng : forall x, 0 <= x <= 2 ^ 47 -> SHB <= shad x <= 2 ^ 44 + SHB.
Proof. intros x Hx. unfold shad. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. Qed.

Section SegA.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis Hn1 : 1 <= n.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation S := (ClassSize c).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation W := (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp).
#[local] Notation D := [(c, i)].
#[local] Notation TZ := [(l_T (lay Σ) + 2824, l_T (lay Σ) + 2840)].

(* [comment removed for export] *)
Lemma sa_geo :
  0 < PRB /\ SEGTOP_A <= PRB /\ K_HIGH_SHADOW_hi <= PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000
  /\ rb SB c <= AB /\ AB + S <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))) /\ rb SB c + kUserCap <= SB + 2 ^ 37
  /\ ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= kUserCap
  /\ 16 <= rz_size n /\ rz_size n + ru8 n <= S /\ 8 <= ru8 n /\ n <= ru8 n
  /\ shad (M + 16) = shad AB + rz_size n / 8 /\ shad (M + 16) + ru8 n / 8 <= shad (AB + S) /\ SHB <= shad AB /\ shad (AB + S) <= 2 ^ 44 + SHB
  /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ 0 < DNB /\ SEGTOP_A <= DNB /\ DNB + 2 ^ 20 <= l_ACEIL L /\ 0 < SSB /\ SEGTOP_A <= SSB
  /\ SSB + 2 ^ 23 <= l_ACEIL L /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ 0 <= rb SB c
  /\ SHB <= shad (M + 16) /\ shad (M + 16) + ru8 n / 8 <= 2 ^ 44 + SHB /\ PRB <= M /\ M + 24 <= PRB + 0x2000011000 /\ shad AB <= shad (M + 16)
  /\ shad (M + 16) + ru8 n / 8 = shad (AB + rz_size n + ru8 n) /\ 32 <= S /\ (16 < rz_size n -> 32 <= rz_size n)
  /\ PRB <= AB /\ AB + S <= PRB + 0x2000011000 /\ 0 <= ru8 n / 8 /\ 0 <= rz_size n / 8.
Proof.
  pose proof (fk_slot Σ (geo_of_ART Σ m HA) c i _ Hc Hn) as (S1 & S2 & S3 & S4). pose proof (fk_prb Σ (geo_of_ART Σ m HA)) as (P0 & P1 & P2 & P3 & P4).
  pose proof (geo_grant Σ m HA PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & PG4 & _).
  pose proof (live_in_slot Σ m HA c i n Hc Hn) as (_ & R16 & F & F0). pose proof (rz_facts n) as (R1 & R2).
  pose proof (fl_slot_room c n Hc F0 F) as (R3 & R4). pose proof (abeg_mod8 Σ m HA c i Hc) as M8.
  pose proof (fk_aceil Σ (geo_of_ART Σ m HA)) as (X1 & X2).
  pose proof (geo_grant Σ m HA T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
  pose proof (geo_grant Σ m HA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as (GD1 & _ & GD3 & _ & GD5).
  pose proof (geo_grant Σ m HA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as (GS1 & _ & GS3 & _ & GS5).
  assert (U : n <= ru8 n /\ 8 <= ru8 n /\ ru8 n mod 8 = 0).
  { unfold ru8. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
    split; [lia|]. split; [assert (1 <= (n + 7) / 8) by (apply Z.div_le_lower_bound; lia); lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  destruct U as (U1 & U2 & U3).
  assert (R8 : rz_size n mod 8 = 0) by (apply (mod8_of _ 16 ltac:(lia) R1); exists 2; reflexivity).
  assert (Q1 : shad (AB + rz_size n) = shad AB + rz_size n / 8) by exact (shad_add8' AB (rz_size n) M8 R8).
  assert (Q2 : shad (AB + rz_size n + ru8 n) = shad (AB + rz_size n) + ru8 n / 8).
  { apply shad_add8'; [rewrite Z.add_mod, M8, R8 by lia; reflexivity | exact U3]. }
  assert (Q3 : shad (AB + rz_size n + ru8 n) <= shad (AB + S)) by (apply fk_shad_mono; lia).
  replace (M + 16) with (AB + rz_size n) by ring.
  assert (HAB : 0 <= AB) by (unfold rb in S1; lia).
  pose proof (shad_rng AB ltac:(unfold rb, kUserCap in *; lia)) as (Q4 & _). pose proof (shad_rng (AB + S) ltac:(unfold rb, kUserCap in *; lia)) as (_ & Q5).
  pose proof (Z.div_pos (rz_size n) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (ru8 n) 8 ltac:(lia) ltac:(lia)).
  assert (R32 : 16 < rz_size n -> 32 <= rz_size n) by (intros Hr; apply Z.mod_divide in R1; [|lia]; destruct R1 as [q Hq]; lia).
  unfold rb, kUserCap, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. repeat split; try lia.
Qed.

Lemma sa_disj :
  (T + 4096 <= 0x10000 \/ SEGTOP_A <= T) /\ (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T)
  /\ (DNB + 2 ^ 20 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= DNB) /\ (SSB + 2 ^ 23 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= SSB)
  /\ (T + 4096 <= PRB \/ PRB + 0x2000011000 <= T) /\ (T + 4096 <= DNB \/ DNB + 2 ^ 20 <= T) /\ (T + 4096 <= SSB \/ SSB + 2 ^ 23 <= T)
  /\ (PRB + 0x2000011000 <= DNB \/ DNB + 2 ^ 20 <= PRB) /\ (PRB + 0x2000011000 <= SSB \/ SSB + 2 ^ 23 <= PRB).
Proof.
  pose proof (geo_grant Σ m HA T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & _ & GT4 & GT5).
  pose proof (geo_grant Σ m HA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as (_ & _ & _ & GD4 & _).
  pose proof (geo_grant Σ m HA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as (_ & _ & _ & GS4 & _).
  pose proof (geo_apart Σ m HA 0 2 _ _ ltac:(lia) eq_refl eq_refl) as A02. pose proof (geo_apart Σ m HA 2 6 _ _ ltac:(lia) eq_refl eq_refl) as A26.
  pose proof (geo_apart Σ m HA 2 7 _ _ ltac:(lia) eq_refl eq_refl) as A27. pose proof (geo_apart Σ m HA 0 6 _ _ ltac:(lia) eq_refl eq_refl) as A06.
  pose proof (geo_apart Σ m HA 0 7 _ _ ltac:(lia) eq_refl eq_refl) as A07. cbn [fst snd] in *. unfold apart in *.
  split; [exact GT5|]. split; [exact GT4|]. split; [exact GD4|]. split; [exact GS4|]. split; [lia|]. split; [exact A26|]. split; [exact A27|].
  split; [exact A06 | exact A07].
Qed.

Ltac geo := pose proof sa_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
  & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41);
  pose proof sa_disj as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
(* [comment removed for export] *)
Ltac dj := unfold fa, RIS_of in *; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, rb, kUserCap, kFaCap, apart in *; lia.
Ltac w7 t1 t2 t3 t4 t5 t6 t7 := unfold W_A1; cbn [disjoint_from];
  split; [t1|]; split; [t2|]; split; [t3|]; split; [t4|]; split; [t5|]; split; [t6|]; split; [t7 | exact I].

Lemma sa_apart : forall j j' g1 g2, j <> j' -> nth_error (startup_grants L) j = Some g1 -> nth_error (startup_grants L) j' = Some g2 ->
  apart (fst g1) (snd g1) (fst g2) (snd g2).
Proof.
  intros j j' g1 g2 Hne H1 H2. destruct (Nat.lt_ge_cases j j') as [Hl|Hl]; [exact (geo_apart Σ m HA j j' g1 g2 Hl H1 H2)|].
  pose proof (geo_apart Σ m HA j' j g2 g1 ltac:(lia) H2 H1) as X. unfold apart in *. lia.
Qed.

Lemma sa_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from IZ_A a k -> disjoint_from W a k.
Proof.
  intros a k H1 H2 HZ. geo. cbn [IZ_A disjoint_from] in HZ. destruct HZ as [HZ _].
  w7 ltac:(clear - H1 H2 T5; dj) ltac:(clear - HZ; dj) ltac:(clear - H2 K22; dj) ltac:(clear - H2 K25; dj)
     ltac:(clear - H2 K2 K32; dj) ltac:(clear - H2 K30; dj) ltac:(clear - H2 K27 Hsp; dj).
Qed.

Lemma sa_Tz : forall a k, T <= a -> a + k <= T + 4096 -> disjoint_from TZ a k -> disjoint_from W a k.
Proof.
  intros a k H1 H2 HZ. geo. cbn [disjoint_from] in HZ. destruct HZ as [HZ _].
  w7 ltac:(clear - HZ; dj) ltac:(clear - H1 H2 T5; dj) ltac:(clear - H1 H2 ATD; dj) ltac:(clear - H1 H2 ATS; dj)
     ltac:(clear - H1 H2 ATP K32 K33; dj) ltac:(clear - H1 H2 T4 K30 K31 K40; dj) ltac:(clear - H2 K20 Hsp; dj).
Qed.

Lemma sa_grant : forall j b gn a k, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from W a k.
Proof.
  intros j b gn a k Hj Hjr H1 H2. geo. pose proof (geo_grant Σ m HA b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (Hj2 : j <> 2%nat) by (clear - Hjr; lia). assert (Hj0 : j <> 0%nat) by (clear - Hjr; lia).
  assert (Hj6 : j <> 6%nat) by (clear - Hjr; lia). assert (Hj7 : j <> 7%nat) by (clear - Hjr; lia).
  pose proof (sa_apart j 2 (b, gn) (T, 4096) Hj2 Hj eq_refl) as HT1. pose proof (sa_apart j 0 (b, gn) (PRB, 0x2000011000) Hj0 Hj eq_refl) as HT2.
  pose proof (sa_apart j 6 (b, gn) (DNB, 0x100000) Hj6 Hj eq_refl) as HT3. pose proof (sa_apart j 7 (b, gn) (SSB, 0x800000) Hj7 Hj eq_refl) as HT4.
  cbn [fst snd] in HT1, HT2, HT3, HT4.
  w7 ltac:(clear - H1 H2 HT1; dj) ltac:(clear - H1 H2 B1 B5; dj) ltac:(clear - H1 H2 HT3; dj) ltac:(clear - H1 H2 HT4; dj)
     ltac:(clear - H1 H2 HT2 K32 K33; dj) ltac:(clear - H1 H2 B1 B4 K30 K31 K40; dj) ltac:(clear - H2 B3 Hsp; dj).
Qed.

Lemma sa_ris : forall a k, RIS_of SB <= a -> a + k <= RIS_of SB + 4096 -> disjoint_from W a k.
Proof.
  intros a k H1 H2. geo.
  w7 ltac:(clear - H1 H2 ATP K5 K6; dj) ltac:(clear - H1 K2 K5; dj) ltac:(clear - H1 H2 APD K5 K6; dj) ltac:(clear - H1 H2 APS K5 K6; dj)
     ltac:(clear - H1 K8 K9 K10 K12 K13; dj) ltac:(clear - H1 K3 K5 K31; dj) ltac:(clear - H2 K4 K6 Hsp; dj).
Qed.

Lemma sa_fa : forall c' a k, 1 <= c' <= 31 -> fa SB c' <= a -> a + k <= fa SB c' + kFaCap -> disjoint_from W a k.
Proof.
  intros c' a k Hc' H1 H2. geo.
  w7 ltac:(clear - Hc' H1 H2 ATP K5 K6; dj) ltac:(clear - Hc' H1 K2 K5; dj) ltac:(clear - Hc' H1 H2 APD K5 K6; dj) ltac:(clear - Hc' H1 H2 APS K5 K6; dj)
     ltac:(clear - Hc Hc' H1 H2 K7 K8 K10 K11 K12 K13; dj) ltac:(clear - Hc' H1 K3 K5 K31; dj) ltac:(clear - Hc' H2 K4 K6 Hsp; dj).
Qed.

Lemma sa_slot : forall c' i' st a k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  p_abeg SB c' i' <= a -> a + k <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a k.
Proof.
  intros c' i' st a k Hc' Hn' HD H1 H2. geo.
  assert (Hne : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [<-|X]; [right; intros <-; apply HD; left; reflexivity | left; exact X]).
  pose proof (slot_apart Σ m HA c i c' i' _ _ Hc Hc' Hn Hn' Hne) as Y.
  pose proof (fk_slot Σ (geo_of_ART Σ m HA) c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (Z5 : PRB <= p_abeg SB c' i' /\ p_abeg SB c' i' + ClassSize c' <= PRB + 0x2000011000) by (clear - Hc' Z1 Z2 Z3 K5 K6; unfold rb, kUserCap in *; lia). destruct Z5 as (Z5 & Z6).
  w7 ltac:(clear - H1 H2 ATP Z5 Z6; dj) ltac:(clear - H1 K2 Z5; dj) ltac:(clear - H1 H2 APD Z5 Z6; dj) ltac:(clear - H1 H2 APS Z5 Z6; dj)
     ltac:(clear - H1 H2 Y K11 K12 K13; dj) ltac:(clear - H1 K3 Z5 K31; dj) ltac:(clear - H2 K4 Z6 Hsp; dj).
Qed.

Lemma sa_shad_slot : forall c' i' st a k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  shad (p_abeg SB c' i') <= a -> a + k <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a k.
Proof.
  intros c' i' st a k Hc' Hn' HD H1 H2. geo.
  assert (Hne : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [<-|X]; [right; intros <-; apply HD; left; reflexivity | left; exact X]).
  pose proof (slot_apart Σ m HA c i c' i' _ _ Hc Hc' Hn Hn' Hne) as Y.
  pose proof (fk_slot Σ (geo_of_ART Σ m HA) c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (Ysh : shad (p_abeg SB c' i' + ClassSize c') <= shad AB \/ shad (AB + S) <= shad (p_abeg SB c' i')) by (destruct Y as [Y|Y]; [right | left]; apply fk_shad_mono; exact Y).
  pose proof (shad_lo (p_abeg SB c' i') ltac:(clear - Hc' Z1 K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (shad_hi (p_abeg SB c' i' + ClassSize c') ltac:(clear - Hc' Z1 Z2 Z3 K4 K5 K6 K28; unfold rb, kUserCap in *; lia)) as Q2.
  w7 ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 Q1; dj) ltac:(clear - H1 H2 D4 Q1 Q2; dj) ltac:(clear - H1 H2 S4 Q1 Q2; dj)
     ltac:(clear - H2 K3 K32 Q2; dj) ltac:(clear - H1 H2 Ysh K16 K34; dj) ltac:(clear - H2 Q2 K27 Hsp; dj).
Qed.

Lemma sa_shad_reg : forall c' a k, 1 <= c' <= 31 -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + k <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a k.
Proof.
  intros c' a k Hc' H1 H2. geo.
  assert (Hau : 0 <= ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) by (clear - Hc'; apply Z.mul_nonneg_nonneg; pose proof (ClassSize_range c' Hc'); lia).
  assert (Hr : shad (rb SB c' + 2 ^ 32) <= shad AB \/ shad (AB + S) <= shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c'))))).
  { destruct (Z.eq_dec c' c) as [->|X]; [right; apply fk_shad_mono; clear - K8; lia|].
    assert (c' < c \/ c < c') by (clear - X; lia). destruct H; [left | right]; apply fk_shad_mono; clear - H K7 K8 K10 Hau; unfold rb, kUserCap in *; lia. }
  pose proof (shad_lo (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) ltac:(clear - Hc' Hau K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (shad_hi (rb SB c' + 2 ^ 32) ltac:(clear - Hc' K4 K5 K6 K28; unfold rb in *; lia)) as Q2.
  w7 ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 Q1; dj) ltac:(clear - H1 H2 D4 Q1 Q2; dj) ltac:(clear - H1 H2 S4 Q1 Q2; dj)
     ltac:(clear - H2 K3 K32 Q2; dj) ltac:(clear - H1 H2 Hr K16 K34; dj) ltac:(clear - H2 Q2 K27 Hsp; dj).
Qed.

Lemma sa_shad_app : forall lo hi a k, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= PRB \/ PRB + 0x2000011000 <= lo) ->
  (forall k' s', nth_error (sec Σ) k' = Some s' -> In k' [] -> hi <= s_mb s' \/ s_mb s' + smsz (s_n s') <= lo) ->
  shad lo <= a -> a + k <= shad hi -> disjoint_from W a k.
Proof.
  intros lo hi a k H0 H47 Hoff _ H1 H2. geo.
  assert (Hr : shad hi <= shad AB \/ shad (AB + S) <= shad lo).
  { destruct Hoff as [Ho|Ho]; [left | right]; apply fk_shad_mono; clear - Ho Hc K5 K6 K7 K8 K9 K10; unfold rb, kUserCap in *; lia. }
  pose proof (shad_lo lo H0) as Q1. pose proof (shad_hi hi H47) as Q2.
  w7 ltac:(clear - H1 H2 T4 Q1 Q2; dj) ltac:(clear - H1 Q1; dj) ltac:(clear - H1 H2 D4 Q1 Q2; dj) ltac:(clear - H1 H2 S4 Q1 Q2; dj)
     ltac:(clear - H2 K3 K32 Q2; dj) ltac:(clear - H1 H2 Hr K16 K34; dj) ltac:(clear - H2 Q2 K27 Hsp; dj).
Qed.

Lemma sa_secmap : forall k s a k', nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + k' <= s_mb s + smsz (s_n s) ->
  disjoint_from W a k'.
Proof.
  intros k s a k' Hk _ H1 H2. geo. pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (Hn' & Y1 & Y3 & Y5 & Yp & _ & YG & _).
  pose proof (proj1 (Forall_forall _ _) YG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as YT.
  pose proof (proj1 (Forall_forall _ _) YG (DNB, 0x100000) ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as YD.
  pose proof (proj1 (Forall_forall _ _) YG (SSB, 0x800000) ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as YS.
  pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (_ & _ & _ & Y4 & _) & _).
  cbn [fst snd] in *.
  w7 ltac:(clear - H1 H2 YT; dj) ltac:(clear - H1 H2 Y5 Y1; dj) ltac:(clear - H1 H2 YD; dj) ltac:(clear - H1 H2 YS; dj)
     ltac:(clear - H1 H2 Yp K32 K33; dj) ltac:(clear - H1 H2 Y1 Y4 K30 K31 K40; dj) ltac:(clear - H2 Y3 Hsp; dj).
Qed.

Lemma sa_stack : forall a k, usp <= a -> a + k <= USTACK_TOP -> disjoint_from W a k.
Proof.
  intros a k H1 H2. geo.
  w7 ltac:(clear - H1 K20 Hsp; dj) ltac:(clear - H1 K27 Hsp; dj) ltac:(clear - H1 K23 Hsp; dj) ltac:(clear - H1 K26 Hsp; dj)
     ltac:(clear - H1 K4 K33 Hsp; dj) ltac:(clear - H1 K31 K27 Hsp; dj) ltac:(clear - H1; dj).
Qed.

(* [comment removed for export] *)
Lemma sa_lch : 16 < rz_size n -> disjoint_from W AB 16.
Proof.
  intros Hr. geo. pose proof (K37 Hr) as R32.
  w7 ltac:(clear - ATP K38 K39 K36; dj) ltac:(clear - K2 K38; dj) ltac:(clear - APD K38 K39 K36; dj)
     ltac:(clear - APS K38 K39 K36; dj) ltac:(clear - R32; dj) ltac:(clear - K3 K38 K31; dj) ltac:(clear - K4 K39 K36 Hsp; dj).
Qed.

Lemma sa_sh1 : disjoint_from W (shad AB) (rz_size n / 8).
Proof.
  geo. pose proof (Z.div_pos (rz_size n) 8 ltac:(clear - K11; lia) ltac:(clear; lia)).
  w7 ltac:(clear - T4 K17 K15 K31 K40; dj) ltac:(clear - K17; dj) ltac:(clear - D4 K17 K15 K31 K40; dj) ltac:(clear - S4 K17 K15 K31 K40; dj)
     ltac:(clear - K3 K32 K15 K31 K40; dj) ltac:(clear - K15; dj) ltac:(clear - K27 K15 K31 K40 Hsp; dj).
Qed.

Lemma sa_sh3 : disjoint_from W (shad (AB + rz_size n + ru8 n)) ((S - rz_size n - ru8 n) / 8).
Proof.
  geo. pose proof (Z.div_pos (S - rz_size n - ru8 n) 8 ltac:(clear - K12; lia) ltac:(clear; lia)).
  pose proof (fk_shad_le2 (AB + rz_size n + ru8 n) (S - rz_size n - ru8 n) ltac:(clear - Hc K1 K5 K7 K11 K13; unfold rb in *; lia) ltac:(clear - K12; lia)) as E.
  replace (AB + rz_size n + ru8 n + (S - rz_size n - ru8 n)) with (AB + S) in E by ring.
  w7 ltac:(clear - T4 K30 K35 K40 K18 E; dj) ltac:(clear - K30 K35 K40; dj) ltac:(clear - D4 K30 K35 K40 K18 E; dj) ltac:(clear - S4 K30 K35 K40 K18 E; dj)
     ltac:(clear - K3 K32 K18 E; dj) ltac:(clear - K35; dj) ltac:(clear - K27 K18 E Hsp; dj).
Qed.

Lemma reg_rep_upd : forall SB' c' r i' st (m' : mem), reg_rep SB' c' r m' -> reg_rep SB' c' (upd_reg r i' st) m'.
Proof. intros SB' c' r i' st m' H. unfold reg_rep, upd_reg in *. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length. exact H. Qed.

(* [comment removed for export] *)
Lemma sa_client : forall x, aclient (live_remove (AB + rz_size n) (live Σ)) (frames Σ) usp x -> outside W x.
Proof.
  intros x Hx. apply (kv_client Σ W D [] IZ_A usp (geo_of_ART Σ m HA) sa_img sa_grant sa_slot sa_shad_app sa_secmap sa_stack
                        (dsjb_all IZ_A CLIENT_STATIC ltac:(vm_compute; reflexivity)) (live_remove (AB + rz_size n) (live Σ))); [|exact Hx].
  intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
  pose proof (ART_wf Σ m HA) as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
  destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
  + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
    intros [E|[]]. injection E as <- <-. rewrite Hn in Hn'. injection Hn' as <-. exact (Hne eq_refl).
  + right. destruct (In_nth_error _ _ Hs) as (k & Hk). exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|].
    split; [reflexivity | intros []].
Qed.

(* [comment removed for export] *)
Lemma sa_consts : forall (m' : mem), munch W m m' -> wmono bsegs m m' -> consts_rep L m'.
Proof.
  intros m' MU WM. apply (consts_rep_frame L m m' (ART_consts Σ m HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply sa_Tz; [lia | lia|]. cbn. split; [lia | exact I].
  + apply (kv_consts Σ W TZ IZ_A sa_img sa_Tz sa_grant); [apply dsjb_all; vm_compute; reflexivity | cbn; split; [lia | exact I] | exact Ha | exact NE].
Qed.

(* [comment removed for export] *)
Theorem segA_ART : forall (m' : mem) (D' : depot), munch W m m' -> wmono bsegs m m' -> qhdr3 m' M n ->
  rw_cells bsegs m' (shad (M + 16)) [CB (Z.to_nat (ru8 n / 8)) (repeat (Z_to_bv 8 253) (Z.to_nat (ru8 n / 8)))] ->
  depot_rep D' (DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB m' -> depot_ok D' DNB SSB (l_ACEIL L) -> dep_inv D' ->
  hash_of (d_hs D') 1 = hash_of (d_hs (dep Σ)) 1 ->
  ARTc (free_p Σ c i n (AB + rz_size n) D') m'.
Proof.
  intros m' D' MU WM HQ SH DR Dok Dinv Dh.
  assert (HDS : forall k s, nth_error (sec Σ) k = Some s -> ~ In k []) by (intros k s _ []).
  pose proof (kv_reg Σ W [] (geo_of_ART Σ m HA) (ris_of_whole SB W [] sa_ris) (fun c0 a k Hc0 _ => sa_fa c0 a k Hc0)
                (fun c0 a k Hc0 _ => sa_shad_reg c0 a k Hc0)) as KR.
  pose proof (kv_pchunk Σ W [(c, i)] (geo_of_ART Σ m HA) sa_slot sa_shad_slot) as KP.
  pose proof (kv_schunk Σ W [] (geo_of_ART Σ m HA) sa_shad_app sa_secmap) as KS.
  apply ARTc_intro; cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 ia_init credit live frames free_p].
  - exact (sa_consts m' MU WM).
  - intros c' Hc'. unfold free_p. cbn [pr]. destruct (Z.eqb_spec c' c) as [->|Hcc].
    + apply reg_rep_upd. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m HA c Hc) MU WM (KR c Hc ltac:(intros []))).
    + exact (reg_rep_transport W _ c' _ m m' (ART_prim Σ m HA c' Hc') MU WM (KR c' Hc' ltac:(intros []))).
  - intros c' Hc'. exact (pclass_rep_transport W _ c' _ _ m m' (ART_cache Σ m HA c' Hc') MU WM
                           (kv_pclass Σ W TZ sa_Tz c' Hc' ltac:(cbn; split; [unfold pc_addr; lia | exact I]))).
  - destruct (ART_chunk Σ m HA) as [P Sc]. split.
    + intros c' i' st Hc' Hn'. unfold free_p in Hn'. cbn [pr] in Hn'. destruct (Z.eqb_spec c' c) as [->|Hcc].
      * unfold upd_reg in Hn'. cbn [r_st] in Hn'. rewrite nth_error_upd_ck in Hn'. destruct (Nat.eqb_spec i i') as [<-|Hii].
        -- destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); [injection Hn' as <- | discriminate].
           (* [comment removed for export] *)
           destruct (P c i (CkAlloc n) Hc Hn) as (Wr & _ & Hl & B1 & B2). geo.
           split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact HQ|]. split.
           { intros Hr. pose proof (Hl Hr) as X. unfold lch in *. apply (rw_cells_transport bsegs W m m' _ _ X MU WM).
             cbn [cells_size csize Nat.add]. exact (sa_lch Hr). }
           unfold pshadow_quar, pshadow_alloc in *. apply bytes_at_app. split.
           { apply bytes_at_app in B1 as [B1 _]. apply (bytes_at_transport bsegs W m m' _ _ B1 MU). rewrite farun_lenZ by (apply Z.div_pos; lia). exact sa_sh1. }
           rewrite farun_lenZ by (apply Z.div_pos; lia). rewrite <- K15. apply bytes_at_app. split.
           { destruct SH as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. unfold fdrun. exact Hb. }
           rewrite fdrun_lenZ by (apply Z.div_pos; lia). rewrite K35.
           apply (bytes_at_transport bsegs W m m' _ _ B2 MU). rewrite farun_lenZ by (apply Z.div_pos; lia). exact sa_sh3.
        -- exact (pchunk_transport W _ c i' st m m' (P c i' st Hc Hn') MU WM (KP c i' st Hc Hn' ltac:(intros [E|[]]; injection E as E2; exact (Hii E2)))).
      * exact (pchunk_transport W _ c' i' st m m' (P c' i' st Hc' Hn') MU WM (KP c' i' st Hc' Hn' ltac:(intros [E|[]]; injection E as E1 E2; exact (Hcc (eq_sym E1))))).
    + intros k s Hk. exact (schunk_transport W k s m m' (Sc k s Hk) MU WM (KS k s Hk (HDS k s Hk))).
  - exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM (kv_sec Σ W IZ_A (geo_of_ART Σ m HA) sa_img sa_grant ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM
             (kv_quar Σ W [(c, i)] TZ IZ_A (geo_of_ART Σ m HA) sa_img sa_Tz sa_slot ltac:(cbn; split; [unfold qcacheT; lia | exact I])
                ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros i' Hi' [E|[]]; injection E as E1 E2; subst c; rewrite <- E2, Hn in Hi'; discriminate)
                ltac:(pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & (_ & _ & HBt & _) & _); exact HBt))).
  - unfold dep_rep. rewrite Dh. exact DR.
  - exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM (kv_fs Σ W [] TZ IZ_A (geo_of_ART Σ m HA) sa_img sa_Tz sa_grant sa_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(cbn; split; [lia | exact I]))).
  - exact (ia_rep_transport W Σ m m' (ART_ia Σ m HA) MU WM (kv_ia W IZ_A sa_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ m m' (ART_shadow Σ m HA) MU WM (kv_shadow Σ W [] (geo_of_ART Σ m HA) sa_shad_app)).
  - exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

End SegA.
