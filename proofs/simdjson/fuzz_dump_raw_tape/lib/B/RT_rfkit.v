(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Definition W_R (T SB c au usp : Z) : list ivl :=
  [(T + 208, T + 3168); (rinfo (RIS_of SB) c, rinfo (RIS_of SB) c + 128); (rb SB c + au, rb SB c + 2 ^ 32);
   (shad (rb SB c + au), shad (rb SB c + 2 ^ 32)); (usp - 1024, usp)].
Definition TZ_R (T : Z) : list ivl := [(T + 208, T + 3168)].

Section RfZ.
Variables (Σ : rtsA) (c usp : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x400 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
#[local] Notation W := (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) usp).

Lemma rz_geo :
  0 < PRB /\ SEGTOP_A <= PRB /\ K_HIGH_SHADOW_hi <= PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ PRB <= SB
  /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000 /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47
  /\ 0 <= au <= kUserCap.
Proof using HG Hc.
  clear - HG Hc. pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
  pose proof (g_grant Σ HG PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & PG4 & _).
  pose proof (fk_aceil Σ HG) as (X1 & X2).
  pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
  pose proof HG as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & _ & W3 & _).
  pose proof (ClassSize_range c Hc) as (HS & _).
  unfold kUserCap, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. repeat split; first [lia | nia].
Qed.

Ltac rgeo := pose proof rz_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12);
  pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
Ltac rdj := unfold fa, RIS_of, rinfo in *; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, rb, kUserCap, kFaCap, apart in *; lia.
Ltac w5 t1 t2 t3 t4 t5 := unfold W_R; cbn [disjoint_from];
  split; [t1|]; split; [t2|]; split; [t3|]; split; [t4|]; split; [t5 | exact I].

Lemma rz_shad : SHB <= shad (rb SB c + au) /\ shad (rb SB c + 2 ^ 32) <= 2 ^ 44 + SHB.
Proof using HG Hc.
  rgeo. split; [apply shad_lo; clear - K5 K1 K11 Hc; unfold rb; lia | apply shad_hi; clear - K6 K4 K10 Hc; unfold rb; lia].
Qed.

Lemma rz_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from [] a k -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros a k H1 H2 _. rgeo. pose proof rz_shad as (Q1 & _).
  unfold W_R; cbn [disjoint_from].
  w5 ltac:(clear - H1 H2 T5; rdj) ltac:(clear - H2 K2 K5 K6 Hc; rdj) ltac:(clear - H2 K2 K5 K11 Hc; rdj) ltac:(clear - H2 Q1; rdj)
     ltac:(clear - H2 K9 Hsp; rdj).
Qed.

Lemma rz_T : forall a k, T <= a -> a + k <= T + 4096 -> disjoint_from (TZ_R T) a k -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros a k H1 H2 HZ. rgeo. pose proof rz_shad as (Q1 & Q2). unfold TZ_R in HZ. cbn [disjoint_from] in HZ. destruct HZ as (Z1 & _).
  w5 ltac:(clear - Z1; rdj) ltac:(clear - H1 H2 ATP K5 K6 Hc; rdj) ltac:(clear - H1 H2 ATP K5 K6 K11 Hc; rdj) ltac:(clear - H1 H2 T4 Q1 Q2; rdj)
     ltac:(clear - H2 K8 Hsp; rdj).
Qed.

Lemma rz_grant : forall j b gn a k, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros j b gn a k Hj Hjr H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2). pose proof (g_grant Σ HG b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (Hj2 : j <> 2%nat) by (clear - Hjr; lia). assert (Hj0 : j <> 0%nat) by (clear - Hjr; lia).
  pose proof (se_apart Σ HG j 2 (b, gn) (T, 4096) Hj2 Hj eq_refl) as HT1. pose proof (se_apart Σ HG j 0 (b, gn) (PRB, 0x2000011000) Hj0 Hj eq_refl) as HT2.
  cbn [fst snd] in HT1, HT2.
  w5 ltac:(clear - H1 H2 HT1; rdj) ltac:(clear - H1 H2 HT2 K5 K6 Hc; rdj) ltac:(clear - H1 H2 HT2 K5 K6 K11 Hc; rdj) ltac:(clear - H1 H2 B4 Q1 Q2; rdj)
     ltac:(clear - H2 B3 Hsp; rdj).
Qed.

Lemma rz_grant67 : forall j b gn a k, nth_error (startup_grants L) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros j b gn a k Hj Hjr H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2). pose proof (g_grant Σ HG b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (Hj2 : j <> 2%nat) by (clear - Hjr; lia). assert (Hj0 : j <> 0%nat) by (clear - Hjr; lia).
  pose proof (se_apart Σ HG j 2 (b, gn) (T, 4096) Hj2 Hj eq_refl) as HT1. pose proof (se_apart Σ HG j 0 (b, gn) (PRB, 0x2000011000) Hj0 Hj eq_refl) as HT2.
  cbn [fst snd] in HT1, HT2.
  w5 ltac:(clear - H1 H2 HT1; rdj) ltac:(clear - H1 H2 HT2 K5 K6 Hc; rdj) ltac:(clear - H1 H2 HT2 K5 K6 K11 Hc; rdj) ltac:(clear - H1 H2 B4 Q1 Q2; rdj)
     ltac:(clear - H2 B3 Hsp; rdj).
Qed.

Lemma rz_ris : forall c' a k, 1 <= c' <= 31 -> ~ In c' [c] -> rinfo (RIS_of SB) c' <= a -> a + k <= rinfo (RIS_of SB) c' + 120 ->
  disjoint_from W a k.
Proof using HG Hc Hsp.
  intros c' a k Hc' HD H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2). assert (Hne : c' <> c) by (intros ->; apply HD; left; reflexivity).
  unfold W_R; cbn [disjoint_from].
  split; [clear - H1 H2 ATP K5 K6 Hc'; rdj|].
  split; [clear - H1 H2 Hne; unfold RIS_of, rinfo in *; destruct (Z_lt_ge_dec c' c) as [X|X]; [left | right; assert (c' > c) by lia]; lia|].
  split; [clear - H1 Hc Hc'; rdj|].
  split; [clear - H1 Q2 K3 K5 Hc'; rdj|].
  split; [clear - H2 K4 K6 Hsp Hc'; rdj | exact I].
Qed.

Lemma rz_fa : forall c' a k, 1 <= c' <= 31 -> ~ In c' [c] -> fa SB c' <= a -> a + k <= fa SB c' + kFaCap -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros c' a k Hc' HD H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2). assert (Hne : c' <> c) by (intros ->; apply HD; left; reflexivity).
  w5 ltac:(clear - H1 H2 ATP K5 K6 Hc'; rdj) ltac:(clear - H2 Hc' Hc; rdj)
     ltac:(clear - H1 H2 Hne K11 Hc Hc'; unfold fa, rb, kFaCap, kUserCap in *; destruct (Z_lt_ge_dec c' c) as [X|X]; [left | right; assert (c' > c) by lia]; nia)
     ltac:(clear - H1 Q2 K3 K5 Hc'; rdj)
     ltac:(clear - H2 K4 K6 Hsp Hc'; rdj).
Qed.

Lemma rz_slot : forall c' i' st a k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') [] ->
  p_abeg SB c' i' <= a -> a + k <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros c' i' st a k Hc' Hn' _ H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2).
  pose proof (fk_slot Σ HG c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (Z5 : PRB <= p_abeg SB c' i' /\ p_abeg SB c' i' + ClassSize c' <= PRB + 0x2000011000) by (clear - Hc' Z1 Z2 Z3 K5 K6; unfold rb, kUserCap in *; lia).
  destruct Z5 as (Z5 & Z6).
  assert (Hreg : p_abeg SB c' i' + ClassSize c' <= rb SB c + au \/ rb SB c + 2 ^ 32 <= p_abeg SB c' i').
  { destruct (Z.eq_dec c' c) as [->|Hne]; [left; exact Z2|]. clear - Z1 Z2 Z3 Hne Hc Hc' K11. unfold rb, kUserCap in *.
    destruct (Z_lt_ge_dec c' c) as [X|X]; [left | right; assert (c' > c) by lia]; lia. }
  w5 ltac:(clear - H1 H2 ATP Z5 Z6; rdj) ltac:(clear - H2 Z2 Z3 Hc' Hc; rdj) ltac:(clear - H1 H2 Hreg; rdj) ltac:(clear - H1 Q2 K3 Z5; rdj)
     ltac:(clear - H2 K4 Z6 Hsp; rdj).
Qed.

Lemma rz_shad_slot : forall c' i' st a k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') [] ->
  shad (p_abeg SB c' i') <= a -> a + k <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros c' i' st a k Hc' Hn' _ H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2).
  pose proof (fk_slot Σ HG c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  pose proof (shad_lo (p_abeg SB c' i') ltac:(clear - Hc' Z1 K1 K5; unfold rb in *; lia)) as R1.
  pose proof (shad_hi (p_abeg SB c' i' + ClassSize c') ltac:(clear - Hc' Z1 Z2 Z3 K4 K5 K6 K10; unfold rb, kUserCap in *; lia)) as R2.
  assert (Hreg : p_abeg SB c' i' + ClassSize c' <= rb SB c + au \/ rb SB c + 2 ^ 32 <= p_abeg SB c' i').
  { destruct (Z.eq_dec c' c) as [->|Hne]; [left; exact Z2|]. clear - Z1 Z2 Z3 Hne Hc Hc' K11. unfold rb, kUserCap in *.
    destruct (Z_lt_ge_dec c' c) as [X|X]; [left | right; assert (c' > c) by lia]; lia. }
  assert (Hsh : shad (p_abeg SB c' i' + ClassSize c') <= shad (rb SB c + au) \/ shad (rb SB c + 2 ^ 32) <= shad (p_abeg SB c' i')).
  { destruct Hreg as [X|X]; [left | right]; apply fk_shad_mono; exact X. }
  w5 ltac:(clear - H1 H2 T4 R1 R2; rdj) ltac:(clear - H2 R2 K3 K5 Hc; rdj) ltac:(clear - H2 R2 K3 K5 K11 Hc; rdj) ltac:(clear - H1 H2 Hsh; rdj)
     ltac:(clear - H2 R2 K9 Hsp; rdj).
Qed.

Lemma rz_shad_reg : forall c' a k, 1 <= c' <= 31 -> ~ In c' [c] -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + k <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros c' a k Hc' HD H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2). assert (Hne : c' <> c) by (intros ->; apply HD; left; reflexivity).
  assert (Hau : 0 <= ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) by (clear - Hc'; apply Z.mul_nonneg_nonneg; pose proof (ClassSize_range c' Hc'); lia).
  pose proof (shad_lo (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) ltac:(clear - Hc' Hau K1 K5; unfold rb in *; lia)) as R1.
  pose proof (shad_hi (rb SB c' + 2 ^ 32) ltac:(clear - Hc' K4 K5 K6 K10; unfold rb in *; lia)) as R2.
  assert (Hsh : shad (rb SB c' + 2 ^ 32) <= shad (rb SB c + au) \/ shad (rb SB c + 2 ^ 32) <= shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c'))))).
  { destruct (Z_lt_ge_dec c' c) as [X|X]; [left; apply fk_shad_mono; clear - X K11 Hau; unfold rb in *; nia | right; assert (X2 : c' > c) by lia; apply fk_shad_mono; clear - X2 K11 Hau; unfold rb in *; nia]. }
  w5 ltac:(clear - H1 H2 T4 R1 R2; rdj) ltac:(clear - H2 R2 K3 K5 Hc; rdj) ltac:(clear - H2 R2 K3 K5 K11 Hc; rdj) ltac:(clear - H1 H2 Hsh; rdj)
     ltac:(clear - H2 R2 K9 Hsp; rdj).
Qed.

Lemma rz_shad_app : forall lo hi a k, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= PRB \/ PRB + 0x2000011000 <= lo) ->
  (forall k' s', nth_error (sec Σ) k' = Some s' -> In k' [] -> hi <= s_mb s' \/ s_mb s' + smsz (s_n s') <= lo) ->
  shad lo <= a -> a + k <= shad hi -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros lo hi a k H0 H47 Hoff _ H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2).
  pose proof (shad_lo lo H0) as R1. pose proof (shad_hi hi H47) as R2.
  assert (Hsh : shad hi <= shad (rb SB c + au) \/ shad (rb SB c + 2 ^ 32) <= shad lo).
  { destruct Hoff as [X|X]; [left | right]; apply fk_shad_mono; clear - X K5 K6 K11 Hc; unfold rb, kUserCap in *; lia. }
  w5 ltac:(clear - H1 H2 T4 R1 R2; rdj) ltac:(clear - H2 R2 K3 K5 Hc; rdj) ltac:(clear - H2 R2 K3 K5 K11 Hc; rdj) ltac:(clear - H1 H2 Hsh; rdj)
     ltac:(clear - H2 R2 K9 Hsp; rdj).
Qed.

Lemma rz_secmap : forall k s a k', nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + k' <= s_mb s + smsz (s_n s) ->
  disjoint_from W a k'.
Proof using HG Hc Hsp.
  intros k s a k' Hk _ H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2). pose proof (fk_map Σ HG k s Hk) as (Hn' & Y1 & Y3 & Y5 & Yp & _ & YG & _).
  pose proof (proj1 (Forall_forall _ _) YG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as YT.
  pose proof HG as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (_ & _ & _ & G4 & _) & _).
  cbn [fst snd] in *.
  w5 ltac:(clear - H1 H2 YT; rdj) ltac:(clear - H1 H2 Yp K5 K6 Hc; rdj) ltac:(clear - H1 H2 Yp K5 K6 K11 Hc; rdj) ltac:(clear - H1 H2 G4 Q1 Q2; rdj)
     ltac:(clear - H2 Y3 Hsp; rdj).
Qed.

Lemma rz_stack : forall a k, usp <= a -> a + k <= USTACK_TOP -> disjoint_from W a k.
Proof using HG Hc Hsp.
  intros a k H1 H2. rgeo. pose proof rz_shad as (Q1 & Q2).
  w5 ltac:(clear - H1 K8 Hsp; rdj) ltac:(clear - H1 K4 K6 Hsp Hc; rdj) ltac:(clear - H1 K4 K6 Hsp Hc; rdj) ltac:(clear - H1 Q2 K9 Hsp; rdj)
     ltac:(clear - H1; rdj).
Qed.

End RfZ.

End GWIN.
