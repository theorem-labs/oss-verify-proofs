(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeS RT_drain_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma ss_stk_wmono : forall (m m' : mem) lo hi, stk bsegs m lo hi -> wmono bsegs m m' -> img_hull_hi <= lo -> stk bsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) WM Hi. split; [lia|]. split; [lia|]. intros x Hx.
  pose proof (proj1 (H x Hx)) as X. pose proof (WM (wa x) X) as X'. split; [exact X'|].
  unfold mrd. unfold wview in X'. destruct (m' (wa x)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply X'. rewrite find_segment_above; [reflexivity| rewrite wa_unsigned by lia; lia|].
  rewrite wa_unsigned by lia. apply (forallb_mono_top bsegs img_hull_hi); [lia | exact asegs_top].
Qed.

Lemma map_upd' : forall {X Y} (f : X -> Y) (l : list X) i x, map f (upd l i x) = upd (map f l) i (f x).
Proof. intros X Y f l. induction l as [|y l IH]; intros [|i] x; cbn; [reflexivity | reflexivity | reflexivity | f_equal; apply IH]. Qed.

Lemma upd_nth_id : forall {X} (l : list X) i x, nth_error l i = Some x -> upd l i x = l.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate; [injection H as ->; reflexivity | f_equal; exact (IH i x H)]. Qed.

Lemma sec_rep_fs : forall Σ k s D' (m : mem), nth_error (sec Σ) k = Some s -> sec_rep Σ m -> sec_rep (free_s Σ k s D') m.
Proof.
  intros Σ k s D' m Hk H. unfold sec_rep, free_s in *. cbn [sec sec_nres lay] in *. rewrite upd_length.
  rewrite map_upd'. rewrite (upd_nth_id (map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σ)) k (Z_to_bv 64 (s_mb s))) by (rewrite nth_error_map, Hk; reflexivity).
  exact H.
Qed.

Section SegAS.
Variables (Σ : rtsA) (m : mem) (k : nat) (s : secst) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hq : s_quar s = false.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).
#[local] Notation n := (s_n s).
#[local] Notation M := (s_mb s + 6128).
#[local] Notation W := (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (s_mb s + 6128) (s_n s) usp).
#[local] Notation TZ := [(l_T (lay Σ) + 2824, l_T (lay Σ) + 2840)].

Let HG : geo_ok Σ := geo_of_ART Σ m HA.

Lemma ss_geo :
  0 < PRB /\ SEGTOP_A <= PRB /\ K_HIGH_SHADOW_hi <= PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000
  /\ 0 < MB /\ MB + MSZ <= l_ACEIL L /\ (MB + MSZ <= 0x10000 \/ SEGTOP_A <= MB)
  /\ (MB + MSZ <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= MB) /\ (MB + MSZ <= PRB \/ PRB + 0x2000011000 <= MB)
  /\ (MB + MSZ <= T \/ T + 4096 <= MB) /\ (MB + MSZ <= DNB \/ DNB + 0x100000 <= MB) /\ (MB + MSZ <= SSB \/ SSB + 0x800000 <= MB)
  /\ 64513 <= n /\ 6144 + ru8 n <= MSZ /\ n <= ru8 n /\ 8 <= ru8 n /\ 0 <= ru8 n / 8
  /\ SHB <= shad MB /\ shad MB <= shad (M + 16) /\ shad (M + 16) + ru8 n / 8 <= shad (MB + MSZ) /\ shad (MB + MSZ) <= 2 ^ 44 + SHB
  /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ 0 < DNB /\ SEGTOP_A <= DNB /\ DNB + 2 ^ 20 <= l_ACEIL L /\ 0 < SSB /\ SEGTOP_A <= SSB
  /\ SSB + 2 ^ 23 <= l_ACEIL L /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ M mod 16 = 0.
Proof.
  clear - HA Hk. pose proof (geo_of_ART Σ m HA) as HG0.
  pose proof (fk_prb Σ HG0) as (P0 & P1 & P2 & P3 & P4).
  pose proof (geo_grant Σ m HA PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & PG4 & _).
  pose proof (dk_map Σ HG0 k s Hk) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof (fk_map Σ HG0 k s Hk) as (Y1 & _ & _ & _ & _ & _ & YG & Y8 & Y9 & _).
  pose proof (Q7 6%nat DNB 0x100000 eq_refl) as QD. pose proof (Q7 7%nat SSB 0x800000 eq_refl) as QS.
  pose proof (fk_aceil Σ HG0) as (X1 & X2).
  pose proof (geo_grant Σ m HA T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
  pose proof (geo_grant Σ m HA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as (GD1 & _ & GD3 & _ & GD5).
  pose proof (geo_grant Σ m HA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as (GS1 & _ & GS3 & _ & GS5).
  pose proof HG0 as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & G2 & G3 & G4 & G5) & _).
  assert (U : 8 <= ru8 n /\ ru8 n mod 8 = 0).
  { unfold ru8. split; [assert (1 <= (n + 7) / 8) by (apply Z.div_le_lower_bound; lia); lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  destruct U as (U1 & U2).
  assert (MB8 : MB mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
  assert (Q10 : shad (M + 16) = shad MB + 6144 / 8).
  { replace (M + 16) with (MB + 6144) by lia. apply shad_add8'; [exact MB8 | reflexivity]. }
  assert (Q11 : shad (M + 16) + ru8 n / 8 = shad (MB + 6144 + ru8 n)).
  { rewrite (shad_add8' (MB + 6144) (ru8 n)); [replace (MB + 6144) with (M + 16) by lia; reflexivity | | exact U2].
    rewrite Z.add_mod, MB8 by lia. reflexivity. }
  pose proof (fk_shad_mono (MB + 6144 + ru8 n) (MB + MSZ) ltac:(lia)) as Q12.
  pose proof (shad_lo MB ltac:(lia)) as Q13. pose proof (shad_hi (MB + MSZ) ltac:(lia)) as Q14.
  pose proof (Z.div_pos (ru8 n) 8 ltac:(lia) ltac:(lia)) as Q15.
  assert (HM16 : M mod 16 = 0).
  { apply Z.mod_divide in G2; [|lia]. destruct G2 as (q & Eq). rewrite Eq. apply Z.mod_divide; [lia|]. exists (q * 256 + 383). lia. }
  cbn [fst snd] in QD, QS. unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  repeat split; lia.
Qed.

Ltac geoS := pose proof ss_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34);
  pose proof (sa_disj Σ m HA) as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
Ltac ssdj := unfold fa, RIS_of in *; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, rb, kUserCap, kFaCap, apart in *; lia.
Ltac ssw7 t1 t2 t3 t4 t5 t6 t7 := unfold W_A1; cbn [disjoint_from];
  split; [t1|]; split; [t2|]; split; [t3|]; split; [t4|]; split; [t5|]; split; [t6|]; split; [t7 | exact I].

Lemma ss_img : forall a k', 0x10000 <= a -> a + k' <= SEGTOP_A -> disjoint_from IZ_A a k' -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros a k' H1 H2 HZ. geoS. cbn [IZ_A disjoint_from] in HZ. destruct HZ as [HZ _].
  ssw7 ltac:(clear - H1 H2 T5; ssdj) ltac:(clear - HZ; ssdj) ltac:(clear - H2 K27; ssdj) ltac:(clear - H2 K30; ssdj)
       ltac:(clear - H1 H2 K9 K16 K18; ssdj) ltac:(clear - H2 K20 K21; ssdj) ltac:(clear - H2 K32 Hsp; ssdj).
Qed.

Lemma ss_Tz : forall a k', T <= a -> a + k' <= T + 4096 -> disjoint_from TZ a k' -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros a k' H1 H2 HZ. geoS. cbn [disjoint_from] in HZ. destruct HZ as [HZ _].
  ssw7 ltac:(clear - HZ; ssdj) ltac:(clear - H1 H2 T5; ssdj) ltac:(clear - H1 H2 ATD; ssdj) ltac:(clear - H1 H2 ATS; ssdj)
       ltac:(clear - H1 H2 K12 K16 K18; ssdj) ltac:(clear - H1 H2 T4 K20 K21 K22 K23; ssdj) ltac:(clear - H2 K25 Hsp; ssdj).
Qed.

Lemma ss_grant : forall j b gn a k', nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + k' <= b + gn -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros j b gn a k' Hj Hjr H1 H2. geoS. pose proof (geo_grant Σ m HA b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (Hj2 : j <> 2%nat) by (clear - Hjr; lia). assert (Hj6 : j <> 6%nat) by (clear - Hjr; lia). assert (Hj7 : j <> 7%nat) by (clear - Hjr; lia).
  pose proof (sa_apart Σ m HA j 2 (b, gn) (T, 4096) Hj2 Hj eq_refl) as HT1.
  pose proof (sa_apart Σ m HA j 6 (b, gn) (DNB, 0x100000) Hj6 Hj eq_refl) as HT3. pose proof (sa_apart Σ m HA j 7 (b, gn) (SSB, 0x800000) Hj7 Hj eq_refl) as HT4.
  pose proof (dk_map Σ HG k s Hk) as (_ & _ & _ & _ & _ & _ & Q7 & _). pose proof (Q7 j b gn Hj) as HM.
  cbn [fst snd] in HT1, HT3, HT4.
  ssw7 ltac:(clear - H1 H2 HT1; ssdj) ltac:(clear - H1 H2 B1 B5; ssdj) ltac:(clear - H1 H2 HT3; ssdj) ltac:(clear - H1 H2 HT4; ssdj)
       ltac:(clear - H1 H2 HM K16 K18; ssdj) ltac:(clear - H1 H2 B1 B4 K20 K21 K22 K23; ssdj) ltac:(clear - H2 B3 Hsp; ssdj).
Qed.

Lemma ss_ris : forall a k', RIS_of SB <= a -> a + k' <= RIS_of SB + 4096 -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros a k' H1 H2. geoS.
  ssw7 ltac:(clear - H1 H2 ATP K5 K6; ssdj) ltac:(clear - H1 K2 K5; ssdj) ltac:(clear - H1 H2 APD K5 K6; ssdj) ltac:(clear - H1 H2 APS K5 K6; ssdj)
       ltac:(clear - H1 H2 K11 K5 K6 K16 K18; ssdj) ltac:(clear - H1 K3 K5 K20 K21 K22 K23; ssdj) ltac:(clear - H2 K4 K6 Hsp; ssdj).
Qed.

Lemma ss_fa : forall c' a k', 1 <= c' <= 31 -> fa SB c' <= a -> a + k' <= fa SB c' + kFaCap -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros c' a k' Hc' H1 H2. geoS.
  ssw7 ltac:(clear - Hc' H1 H2 ATP K5 K6; ssdj) ltac:(clear - Hc' H1 K2 K5; ssdj) ltac:(clear - Hc' H1 H2 APD K5 K6; ssdj)
       ltac:(clear - Hc' H1 H2 APS K5 K6; ssdj) ltac:(clear - Hc' H1 H2 K11 K5 K6 K16 K18; ssdj)
       ltac:(clear - Hc' H1 K3 K5 K20 K21 K22 K23; ssdj) ltac:(clear - Hc' H2 K4 K6 Hsp; ssdj).
Qed.

Lemma ss_slot : forall c' i' st a k', 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') ([] : list (Z * nat)) ->
  p_abeg SB c' i' <= a -> a + k' <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros c' i' st a k' Hc' Hn' _ H1 H2. geoS.
  pose proof (fk_slot Σ HG c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (Z5 : PRB <= p_abeg SB c' i' /\ p_abeg SB c' i' + ClassSize c' <= PRB + 0x2000011000) by (clear - Hc' Z1 Z2 Z3 K5 K6; unfold rb, kUserCap in *; lia).
  destruct Z5 as (Z5 & Z6).
  ssw7 ltac:(clear - H1 H2 ATP Z5 Z6; ssdj) ltac:(clear - H1 K2 Z5; ssdj) ltac:(clear - H1 H2 APD Z5 Z6; ssdj) ltac:(clear - H1 H2 APS Z5 Z6; ssdj)
       ltac:(clear - H1 H2 K11 Z5 Z6 K16 K18; ssdj) ltac:(clear - H1 K3 Z5 K20 K21 K22 K23; ssdj) ltac:(clear - H2 K4 Z6 Hsp; ssdj).
Qed.

Lemma ss_shad_off : forall lo hi, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= MB \/ MB + MSZ <= lo) ->
  shad hi <= shad (M + 16) \/ shad (M + 16) + ru8 n / 8 <= shad lo.
Proof using HA Hk.
  intros lo hi H0 H47 Hoff. geoS. destruct Hoff as [Ho|Ho].
  - left. pose proof (fk_shad_mono hi MB Ho). lia.
  - right. pose proof (fk_shad_mono (MB + MSZ) lo Ho). lia.
Qed.

Lemma ss_shad_slot : forall c' i' st a k', 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') ([] : list (Z * nat)) ->
  shad (p_abeg SB c' i') <= a -> a + k' <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros c' i' st a k' Hc' Hn' _ H1 H2. geoS.
  pose proof (fk_slot Σ HG c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (Z5 : PRB <= p_abeg SB c' i' /\ p_abeg SB c' i' + ClassSize c' <= PRB + 0x2000011000) by (clear - Hc' Z1 Z2 Z3 K5 K6; unfold rb, kUserCap in *; lia).
  destruct Z5 as (Z5 & Z6).
  pose proof (ss_shad_off (p_abeg SB c' i') (p_abeg SB c' i' + ClassSize c') ltac:(clear - Z5 K1; lia) ltac:(clear - Z6 K4 K33; lia)
                ltac:(clear - K11 Z5 Z6; ssdj)) as Ysh.
  pose proof (shad_lo (p_abeg SB c' i') ltac:(clear - Z5 K1; lia)) as Q1.
  pose proof (shad_hi (p_abeg SB c' i' + ClassSize c') ltac:(clear - Z6 K4 K33; lia)) as Q2.
  ssw7 ltac:(clear - H1 H2 T4 Q1 Q2; ssdj) ltac:(clear - H1 Q1; ssdj) ltac:(clear - H1 H2 D4 Q1 Q2; ssdj) ltac:(clear - H1 H2 S4 Q1 Q2; ssdj)
       ltac:(clear - H1 H2 K10 K7 K16 K18 Q1 Q2; ssdj) ltac:(clear - H1 H2 Ysh; ssdj) ltac:(clear - H2 Q2 K32 Hsp; ssdj).
Qed.

Lemma ss_shad_reg : forall c' a k', 1 <= c' <= 31 -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + k' <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros c' a k' Hc' H1 H2. geoS.
  assert (Hau : 0 <= ClassSize c' * Z.of_nat (length (r_st (pr Σ c'))) <= kUserCap) by exact (dk_auser Σ HG c' Hc').
  pose proof (ss_shad_off (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) (rb SB c' + 2 ^ 32)
                ltac:(clear - Hc' Hau K1 K5; unfold rb in *; lia) ltac:(clear - Hc' K4 K5 K6 K33; unfold rb in *; lia)
                ltac:(clear - K11 Hc' Hau K5 K6; ssdj)) as Ysh.
  pose proof (shad_lo (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) ltac:(clear - Hc' Hau K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (shad_hi (rb SB c' + 2 ^ 32) ltac:(clear - Hc' K4 K5 K6 K33; unfold rb in *; lia)) as Q2.
  ssw7 ltac:(clear - H1 H2 T4 Q1 Q2; ssdj) ltac:(clear - H1 Q1; ssdj) ltac:(clear - H1 H2 D4 Q1 Q2; ssdj) ltac:(clear - H1 H2 S4 Q1 Q2; ssdj)
       ltac:(clear - H1 H2 K10 K7 K16 K18 Q1 Q2; ssdj) ltac:(clear - H1 H2 Ysh; ssdj) ltac:(clear - H2 Q2 K32 Hsp; ssdj).
Qed.

Lemma ss_shad_app : forall lo hi a k', 0 <= lo -> hi <= 2 ^ 47 -> (hi <= PRB \/ PRB + 0x2000011000 <= lo) ->
  (forall k'' s', nth_error (sec Σ) k'' = Some s' -> In k'' [k] -> hi <= s_mb s' \/ s_mb s' + smsz (s_n s') <= lo) ->
  shad lo <= a -> a + k' <= shad hi -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros lo hi a k' H0 H47 Hoff HDS H1 H2. geoS.
  pose proof (ss_shad_off lo hi H0 H47 (HDS k s Hk (or_introl eq_refl))) as Ysh.
  pose proof (shad_lo lo H0) as Q1. pose proof (shad_hi hi H47) as Q2.
  ssw7 ltac:(clear - H1 H2 T4 Q1 Q2; ssdj) ltac:(clear - H1 Q1; ssdj) ltac:(clear - H1 H2 D4 Q1 Q2; ssdj) ltac:(clear - H1 H2 S4 Q1 Q2; ssdj)
       ltac:(clear - H1 H2 K10 K7 K16 K18 Q1 Q2; ssdj) ltac:(clear - H1 H2 Ysh; ssdj) ltac:(clear - H2 Q2 K32 Hsp; ssdj).
Qed.

Lemma ss_secmap : forall k' s' a k'', nth_error (sec Σ) k' = Some s' -> ~ In k' [k] -> s_mb s' <= a -> a + k'' <= s_mb s' + smsz (s_n s') ->
  disjoint_from W a k''.
Proof using HA Hk Hsp.
  intros k' s' a k'' Hk' HDk H1 H2. geoS.
  pose proof (dk_map Σ HG k' s' Hk') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  assert (Hne : k <> k') by (intros ->; exact (HDk (or_introl eq_refl))).
  pose proof (Q9 k s Hk Hne) as AP. pose proof (Q7 6%nat DNB 0x100000 eq_refl) as QD. pose proof (Q7 7%nat SSB 0x800000 eq_refl) as QS.
  ssw7 ltac:(clear - H1 H2 Q6; ssdj) ltac:(clear - H1 H2 Q3; ssdj) ltac:(clear - H1 H2 QD; ssdj) ltac:(clear - H1 H2 QS; ssdj)
       ltac:(clear - H1 H2 AP K16 K18; ssdj) ltac:(clear - H1 H2 Q4 Q1 K20 K21 K22 K23; ssdj) ltac:(clear - H2 Q2 Hsp; ssdj).
Qed.

Lemma ss_stack : forall a k', usp <= a -> a + k' <= USTACK_TOP -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros a k' H1 H2. geoS.
  ssw7 ltac:(clear - H1 K25 Hsp; ssdj) ltac:(clear - H1 K32 Hsp; ssdj) ltac:(clear - H1 K28 Hsp; ssdj) ltac:(clear - H1 K31 Hsp; ssdj)
       ltac:(clear - H1 K8 K16 K18 Hsp; ssdj) ltac:(clear - H1 K22 K23 K32 Hsp; ssdj) ltac:(clear - H1; ssdj).
Qed.

Lemma ss_client : forall x, aclient (live_remove (s_ubeg s) (live Σ)) (frames Σ) usp x -> outside W x.
Proof using HA Hk Hsp.
  intros x Hx. apply (kv_client Σ W [] [k] IZ_A usp HG ss_img ss_grant ss_slot ss_shad_app ss_secmap ss_stack
                        (dsjb_all IZ_A CLIENT_STATIC ltac:(vm_compute; reflexivity)) (live_remove (s_ubeg s) (live Σ))); [|exact Hx].
  intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
  pose proof (ART_wf Σ m HA) as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
  destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(t & Ht & Htq & Htn & ->)].
  + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
  + right. destruct (In_nth_error _ _ Ht) as (k' & Hk'). exists k', t. split; [exact Hk'|]. split; [exact Htq|]. split; [exact Htn|].
    split; [reflexivity|]. intros [E|[]]. subst k'. rewrite Hk in Hk'. injection Hk' as <-. exact (Hne eq_refl).
Qed.

Lemma ss_consts : forall (m' : mem), munch W m m' -> wmono bsegs m m' -> consts_rep L m'.
Proof using HA Hk Hsp.
  intros m' MU WM. apply (consts_rep_frame L m m' (ART_consts Σ m HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply ss_Tz; [lia | lia|]. cbn. split; [lia | exact I].
  + apply (kv_consts Σ W TZ IZ_A ss_img ss_Tz ss_grant); [apply dsjb_all; vm_compute; reflexivity | cbn; split; [lia | exact I] | exact Ha | exact NE].
Qed.

Lemma ss_map_lo : forall a k', MB <= a -> a + k' <= M -> 0 <= k' -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros a k' H1 H2 H3. geoS.
  ssw7 ltac:(clear - H1 H2 K12 K16 K18; ssdj) ltac:(clear - H1 H2 K9 K16 K18; ssdj) ltac:(clear - H1 H2 K13 K16 K18; ssdj)
       ltac:(clear - H1 H2 K14 K16 K18; ssdj) ltac:(clear - H2; ssdj) ltac:(clear - H1 H2 K10 K7 K16 K18 K20 K21 K22 K23; ssdj)
       ltac:(clear - H2 K8 K16 K18 Hsp; ssdj).
Qed.

Lemma ss_shmap_lo : forall a k', shad MB <= a -> a + k' <= shad (M + 16) -> 0 <= k' -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros a k' H1 H2 H3. geoS.
  ssw7 ltac:(clear - H1 H2 T4 K19 K20 K21 K22 K23; ssdj) ltac:(clear - H1 K20; ssdj) ltac:(clear - H1 H2 D4 K19 K20 K21 K22 K23; ssdj)
       ltac:(clear - H1 H2 S4 K19 K20 K21 K22 K23; ssdj) ltac:(clear - H1 H2 K10 K7 K16 K18 K19 K20 K21 K22 K23; ssdj) ltac:(clear - H2; ssdj)
       ltac:(clear - H2 K19 K21 K22 K23 K32 Hsp; ssdj).
Qed.

Lemma ss_shmap_hi : forall a k', shad (M + 16) + ru8 n / 8 <= a -> a + k' <= shad (MB + MSZ) -> 0 <= k' -> disjoint_from W a k'.
Proof using HA Hk Hsp.
  intros a k' H1 H2 H3. geoS.
  ssw7 ltac:(clear - H1 H2 T4 K20 K21 K22 K23 K19; ssdj) ltac:(clear - H1 K20 K21 K19; ssdj) ltac:(clear - H1 H2 D4 K20 K21 K22 K23 K19; ssdj)
       ltac:(clear - H1 H2 S4 K20 K21 K22 K23 K19; ssdj) ltac:(clear - H1 H2 K10 K7 K16 K18 K20 K21 K22 K23 K19; ssdj) ltac:(clear - H1; ssdj)
       ltac:(clear - H2 K22 K23 K32 Hsp; ssdj).
Qed.

Theorem segA_ART_s : forall (m' : mem) (D' : depot), munch W m m' -> wmono bsegs m m' -> qhdr3 m' M n ->
  rw_cells bsegs m' (shad (M + 16)) [CB (Z.to_nat (ru8 n / 8)) (repeat (Z_to_bv 8 253) (Z.to_nat (ru8 n / 8)))] ->
  depot_rep D' (DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB m' -> depot_ok D' DNB SSB (l_ACEIL L) -> dep_inv D' ->
  hash_of (d_hs D') 1 = hash_of (d_hs (dep Σ)) 1 ->
  ARTc (free_s Σ k s D') m'.
Proof using HA Hk Hq Hsp.
  intros m' D' MU WM HQ SH DR Dok Dinv Dh.
  pose proof (kv_reg Σ W [] HG (ris_of_whole SB W [] ss_ris) (fun c0 a k' Hc0 _ => ss_fa c0 a k' Hc0)
                (fun c0 a k' Hc0 _ => ss_shad_reg c0 a k' Hc0)) as KR.
  pose proof (kv_pchunk Σ W [] HG ss_slot ss_shad_slot) as KP.
  pose proof (kv_schunk Σ W [k] HG ss_shad_app ss_secmap) as KS.
  apply ARTc_intro.
  - exact (ss_consts m' MU WM).
  - intros c' Hc'. exact (reg_rep_transport W _ c' _ m m' (ART_prim Σ m HA c' Hc') MU WM (KR c' Hc' ltac:(intros []))).
  - intros c' Hc'. exact (pclass_rep_transport W _ c' _ _ m m' (ART_cache Σ m HA c' Hc') MU WM
                           (kv_pclass Σ W TZ ss_Tz c' Hc' ltac:(cbn; split; [unfold pc_addr; lia | exact I]))).
  - destruct (ART_chunk Σ m HA) as [P Sc]. split.
    + intros c' i' st Hc' Hn'. exact (pchunk_transport W _ c' i' st m m' (P c' i' st Hc' Hn') MU WM (KP c' i' st Hc' Hn' (fun X => X))).
    + intros k' t Hk'. destruct (fs_nth Σ k s Hk k' t Hk') as [(-> & ->)|(Hne & Hk0)].
      *
        pose proof (Sc k s Hk) as X. unfold schunk in X.
        replace (s_mb s + 4096 + 2032) with M in X by lia. replace (s_mb s + 4096 + 2048) with (M + 16) in X by lia.
        destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8). rewrite Hq in X4, X7.
        geoS. unfold schunk. cbn [s_mb s_n s_quar].
        replace (s_mb s + 4096 + 2032) with M by lia. replace (s_mb s + 4096 + 2048) with (M + 16) by lia.
        split; [apply (rw_cells_transport bsegs W m m' _ _ X1 MU WM); cbn [cells_size csize Nat.add Z.of_nat]; apply ss_map_lo; lia|].
        split; [exact (wr_at_wmono m m' _ _ X2 WM)|].
        split; [apply (lch_transport W m m' _ _ X3 MU WM); apply ss_map_lo; lia|].
        split; [exact HQ|].
        split; [apply (ss_stk_wmono m m' _ _ X5 WM); unfold img_hull_hi, SHB in *; lia|].
        assert (MB8 : s_mb s mod 8 = 0).
        { clear - K34. apply Z.mod_divide in K34; [|lia]. destruct K34 as (q & Eq). apply Z.mod_divide; [lia|]. exists (2 * q - 766). lia. }
        assert (Q1 : shad (M + 16) = shad (s_mb s) + 768).
        { replace (M + 16) with (s_mb s + 6144) by lia. rewrite (shad_add8' (s_mb s) 6144 MB8 eq_refl). reflexivity. }
        change ((4096 + 2048) / 8) with 768 in X6 |- *.
        split; [apply (bytes_at_transport bsegs W m m' _ _ X6 MU); rewrite farun_lenZ by lia; apply ss_shmap_lo; lia|].
        split.
        { destruct SH as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. unfold fdrun, K_kAsanHeapFreeMagic. exact Hb. }
        apply (bytes_at_transport bsegs W m m' _ _ X8 MU). rewrite farun_lenZ by (apply Z.div_pos; lia).
        pose proof (shad_add8' (M + 16) (ru8 n) ltac:(replace (M + 16) with (s_mb s + 6144) by lia; rewrite Z.add_mod, MB8 by lia; reflexivity)
                      ltac:(unfold ru8; rewrite Z.mul_comm; apply Z.mod_mul; lia)) as Q2.
        pose proof (fk_shad_le2 (M + 16 + ru8 n) (smsz n - 4096 - 2048 - ru8 n) ltac:(lia) ltac:(lia)) as Q3.
        replace (M + 16 + ru8 n + (smsz n - 4096 - 2048 - ru8 n)) with (s_mb s + smsz n) in Q3 by lia.
        apply ss_shmap_hi; [lia | lia | apply Z.div_pos; lia].
      * exact (schunk_transport W k' t m m' (Sc k' t Hk0) MU WM (KS k' t Hk0 ltac:(intros [E|[]]; exact (Hne (eq_sym E))))).
  - exact (sec_rep_fs Σ k s D' m' Hk (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM
             (kv_sec Σ W IZ_A HG ss_img ss_grant ltac:(apply dsjb_all'; vm_compute; reflexivity)))).
  - exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM
             (kv_quar Σ W [] TZ IZ_A HG ss_img ss_Tz ss_slot ltac:(cbn; split; [unfold qcacheT; lia | exact I])
                ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(intros i' Hi' [])
                ltac:(pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & (_ & _ & HBt & _) & _); exact HBt))).
  - unfold dep_rep. rewrite Dh. exact DR.
  - exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM (kv_fs Σ W [k] TZ IZ_A HG ss_img ss_Tz ss_grant ss_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(cbn; split; [lia | exact I]))).
  - exact (ia_rep_transport W Σ m m' (ART_ia Σ m HA) MU WM (kv_ia W IZ_A ss_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ m m' (ART_shadow Σ m HA) MU WM (kv_shadow Σ W [k] HG ss_shad_app)).
  - exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

End SegAS.

End GWIN.
