(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import MState Mem Frame Cells Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_thread R_tlsgetaddr R_glue_defs R_sec_defs R_fs_defs RT_state RT_rep RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_sys_stmt RT_vis RT_malsec_state.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma allowed_of_window : forall A lo hi p, In (lo, hi) A -> lo <= p -> p + 4096 <= hi -> 0 <= p < 2 ^ 64 ->
  page_allowedb A (Z_to_bv 64 p) = true.
Proof.
  intros A lo hi p Hin H1 H2 H3. unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact Hin|].
  cbn [fst snd]. rewrite unsigned_lit by exact H3. unfold page_size. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma page_meet : forall p s e lo hi, p mod 4096 = 0 -> lo <= s -> e <= hi -> p < e -> s < p + 4096 ->
  pg_dn lo <= p /\ p + 4096 <= pg_up hi.
Proof.
  intros p s e lo hi Hp H1 H2 H3 H4. unfold pg_dn, pg_up. apply Z.mod_divide in Hp; [|lia]. destruct Hp as [q ->].
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod (hi + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (hi + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma pg_dn_facts : forall x, 0 <= x -> pg_dn x <= x < pg_dn x + 4096 /\ pg_dn x mod 4096 = 0 /\ 0 <= pg_dn x.
Proof.
  intros x Hx. unfold pg_dn. pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
  split; [lia|]. split; [apply Z.mod_mul; lia|]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.

Lemma pg_up_facts : forall x, 0 <= x -> x <= pg_up x < x + 4096 /\ pg_up x mod 4096 = 0.
Proof.
  intros x Hx. unfold pg_up. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)).
  split; [lia|]. apply Z.mod_mul. lia.
Qed.

Lemma page_base_Z : forall a : word, bv_unsigned (page_base a) = pg_dn (bv_unsigned a).
Proof.
  intros a. unfold page_base, page_base_of, page_size, pg_dn. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)).
  rewrite unsigned_lit by (split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]). reflexivity.
Qed.

Lemma page_base_eq : forall a : word, page_base a = Z_to_bv 64 (pg_dn (bv_unsigned a)).
Proof. intros a. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition p_first (P : Z) : Z := pg_dn (shad P).
Definition p_last (P n : Z) : Z := pg_dn (shad (P + smsz n) - 1).

Definition W_rev (Σ : rtsA) (P n : Z) : list ivl :=
  [(shad P, shad (P + smsz n))]
  ++ (if page_allowedb (rtA_allow Σ) (Z_to_bv 64 (p_first P)) then [] else [(p_first P, p_first P + 4096)])
  ++ (if page_allowedb (rtA_allow Σ) (Z_to_bv 64 (p_last P n)) then [] else [(p_last P n, p_last P n + 4096)]).

Section Rev.
Variables (Σ : rtsA) (m : mem) (P n : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis Hn : 64512 < n <= 0x8000000.
#[local] Notation L := (lay Σ).
#[local] Notation A := (rtA_allow Σ).
#[local] Notation msz := (smsz n).

(* [comment removed for export] *)
Lemma rv_map : 0 < P /\ P mod 4096 = 0 /\ P + msz <= l_ACEIL L /\ (P + msz <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= P)
  /\ SEGTOP_A <= P /\ 72704 <= msz /\ msz mod 4096 = 0 /\ msz <= 0x8004000 /\ l_ACEIL L <= 2 ^ 47 - 0x800000.
Proof using HA HG Hn.
  pose proof (rta_sp0 Σ m HA) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_hi in W2. clear HA.
  assert (AC : l_ACEIL L <= 2 ^ 47 - 0x800000) by (unfold l_ACEIL, STACK_WIN; lia).
  destruct HG as ((G1 & G2 & G3 & G4 & G5) & _).
  assert (RZ : rz_size n = 2048) by (apply rz_size_big; lia).
  assert (ND : needed n = 8 * ((n + 7) / 8) + 2048) by (unfold needed, rounded; rewrite RZ, !Z.max_l by lia; reflexivity).
  assert (E : msz = pg_up (needed n + 2048) + 4096) by (unfold smsz; rewrite RZ; reflexivity).
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  pose proof (pg_up_facts (needed n + 2048) ltac:(lia)) as (U1 & U2).
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [destruct G5 as [G5|G5]; [rewrite E in G5; lia | exact G5]|].
  split; [lia|]. split; [rewrite E, Z.add_mod, U2 by lia; reflexivity|]. split; [lia | exact AC].
Qed.

(* [comment removed for export] *)
Lemma rv_shad : shad P mod 512 = 0 /\ shad (P + msz) = shad P + msz / 8 /\ msz / 8 mod 512 = 0 /\ 9088 <= msz / 8
  /\ SHB <= shad P /\ shad (P + msz) <= K_HIGH_SHADOW_hi
  /\ (shad (P + msz) <= 0x8fff6e00 \/ K_HIGH_SHADOW_lo <= shad P).
Proof using HA HG Hn.
  pose proof rv_map as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). clear HA HG.
  unfold shad, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  apply Z.mod_divide in M2; [|lia]. apply Z.mod_divide in M7; [|lia]. destruct M2 as [q1 E1]. destruct M7 as [q2 E2].
  rewrite E1, E2 in *.
  assert (D12 : (q1 * 4096 + q2 * 4096) / 8 = (q1 + q2) * 512) by (replace (q1 * 4096 + q2 * 4096) with ((q1 + q2) * 512 * 8) by ring; apply Z.div_mul; lia).
  assert (D1 : q1 * 4096 / 8 = q1 * 512) by (replace (q1 * 4096) with (q1 * 512 * 8) by ring; apply Z.div_mul; lia).
  assert (D2 : q2 * 4096 / 8 = q2 * 512) by (replace (q2 * 4096) with (q2 * 512 * 8) by ring; apply Z.div_mul; lia).
  rewrite D12, D1, D2.
  split; [rewrite Z.add_mod, Z.mod_mul by lia; reflexivity|]. split; [ring|].
  split; [apply Z.mod_mul; lia|]. lia.
Qed.

Lemma rv_pages : p_first P <= shad P < p_first P + 4096 /\ p_first P mod 4096 = 0
  /\ p_last P n < shad (P + msz) <= p_last P n + 4096 /\ p_last P n mod 4096 = 0
  /\ shad P + 4096 <= p_last P n
  /\ ((K_LOW_SHADOW_lo <= p_first P /\ p_last P n + 4096 <= K_LOW_SHADOW_hi)
      \/ (K_HIGH_SHADOW_lo <= p_first P /\ p_last P n + 4096 <= K_HIGH_SHADOW_hi)).
Proof using HA HG Hn.
  pose proof rv_shad as (S1 & S2 & S3 & S4 & S5 & S6 & S7). clear HA HG.
  unfold p_first, p_last. rewrite S2 in *.
  pose proof (pg_dn_facts (shad P) ltac:(unfold SHB in *; lia)) as (D1 & D2 & D3).
  pose proof (pg_dn_facts (shad P + msz / 8 - 1) ltac:(unfold SHB in *; lia)) as (E1 & E2 & E3).
  set (x := pg_dn (shad P)) in *. set (y := pg_dn (shad P + msz / 8 - 1)) in *.
  split; [lia|]. split; [exact D2|]. split; [lia|]. split; [exact E2|].
  unfold SHB, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  apply Z.mod_divide in D2, E2; try lia. destruct D2 as [qx Ex]. destruct E2 as [qy Ey]. rewrite Ex, Ey in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rev_munch_hyp : forall a : word, page_allowedb [shw P n] (page_base a) = true -> page_allowedb A (page_base a) = false ->
  ~ outside (W_rev Σ P n) (bv_unsigned a).
Proof using HA HG Hn.
  intros a H1 H2. pose proof rv_pages as ((R1 & R2) & R3 & (R4 & R5) & R6 & R7 & _). pose proof rv_shad as (_ & S2 & _ & S4 & S5 & _).
  clear HA HG.
  unfold page_allowedb in H1. cbn [existsb] in H1. rewrite orb_false_r in H1. unfold shw in H1. cbn [fst snd] in H1.
  apply andb_prop in H1 as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. unfold page_size in X2.
  rewrite page_base_Z in X1, X2. pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn [Z.of_N] in RA.
  pose proof (pg_dn_facts (bv_unsigned a) ltac:(lia)) as ((Q1 & Q1') & Q2 & Q3).
  pose proof (pg_up_facts (shad (P + msz)) ltac:(unfold SHB in *; lia)) as (U1 & U2).
  fold (p_first P) in X1. set (x := bv_unsigned a) in *. set (pb := pg_dn x) in *.
  unfold W_rev. intros Ho. apply outside_app_inv in Ho as [Ho1 Ho2]. apply outside_app_inv in Ho2 as [Ho2 Ho3].
  cbn [outside] in Ho1. destruct Ho1 as [Ho1 _].
  assert (Hx : x < shad P \/ shad (P + msz) <= x) by lia. clear Ho1.
  apply Z.mod_divide in R3, R6, Q2, U2; try lia.
  destruct R3 as [q1 E1]. destruct R6 as [q2 E2]. destruct Q2 as [q3 E3]. destruct U2 as [q4 E4].
  destruct Hx as [Hx|Hx].
  - assert (Ep : pb = p_first P) by lia. rewrite page_base_eq in H2. fold x in H2. fold pb in H2. rewrite Ep in H2. rewrite H2 in Ho2.
    cbn [outside] in Ho2. destruct Ho2 as [Ho2 _]. lia.
  - assert (Ep : pb = p_last P n) by lia. rewrite page_base_eq in H2. fold x in H2. fold pb in H2. rewrite Ep in H2. rewrite H2 in Ho3.
    cbn [outside] in Ho3. destruct Ho3 as [Ho3 _]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dsj_within : forall (W : list ivl) lo hi a k, Forall (fun p => lo <= fst p /\ snd p <= hi) W -> (a + k <= lo \/ hi <= a) ->
  disjoint_from W a k.
Proof.
  induction W as [|[x y] W IH]; intros lo hi a k HF H; [exact I|]. apply Forall_cons_iff in HF as [[H1 H2] HF]. cbn [fst snd] in H1, H2.
  cbn [disjoint_from]. split; [lia | exact (IH lo hi a k HF H)].
Qed.

Lemma rv_within : Forall (fun p => p_first P <= fst p /\ snd p <= p_last P n + 4096) (W_rev Σ P n).
Proof using HA HG Hn.
  pose proof rv_pages as ((R1 & R2) & R3 & (R4 & R5) & R6 & R7 & _). unfold W_rev.
  apply Forall_app. split; [apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]|].
  apply Forall_app. split; [destruct (page_allowedb _ _); [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]]|].
  destruct (page_allowedb _ _); [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]].
Qed.

(* [comment removed for export] *)
Lemma rv_app : forall a k, (a + k <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= a) -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H. pose proof rv_pages as (_ & _ & _ & _ & _ & X). apply (dsj_within _ _ _ a k rv_within).
  unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_grant_apart : forall b gn, In (b, gn) (startup_grants L) -> apart P msz b gn.
Proof using HA HG.
  intros b gn Hin. destruct HG as (_ & Hap). pose proof (ART_wf Σ m HA) as (HL & _).
  assert (HM : maps0_ok L).
  { unfold layout_ok in HL. destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM. }
  destruct HM as (HM & _). pose proof (proj1 (Forall_forall _ _) HM (b, gn) ltac:(apply in_or_app; left; exact Hin)) as Hin'.
  cbn [fst snd] in Hin'. pose proof (proj1 (Forall_forall _ _) Hap _ ltac:(unfold rt_maps; apply in_or_app; right; exact Hin')) as X.
  cbn [fst snd] in X. pose proof (g_grant Σ (geo_of_ART Σ m HA) b gn Hin) as (G1 & _ & G3 & _).
  pose proof (rta_sp0 Σ m HA) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_hi, l_ACEIL, STACK_WIN in *.
  assert (Hgn : 0 < gn) by (unfold startup_grants in Hin; destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as _ <-; lia).
  rewrite !unsigned_lit in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma dsj_pad : forall p a k slo shi, In (pg_dn slo, pg_up shi) A -> slo <= a -> a + k <= shi -> p mod 4096 = 0 -> 0 <= p ->
  p + 4096 < 2 ^ 64 -> disjoint_from (if page_allowedb A (Z_to_bv 64 p) then [] else [(p, p + 4096)]) a k.
Proof.
  intros p a k slo shi Hin H1 H2 Hp0 Hp1 Hp2. destruct (page_allowedb A (Z_to_bv 64 p)) eqn:E; [exact I|].
  cbn [disjoint_from]. split; [|exact I]. destruct (Z_le_gt_dec (a + k) p) as [X|X]; [left; exact X|].
  destruct (Z_le_gt_dec (p + 4096) a) as [Y|Y]; [right; exact Y|]. exfalso.
  pose proof (page_meet p a (a + k) slo shi Hp0 H1 H2 ltac:(lia) ltac:(lia)) as (Q1 & Q2).
  rewrite (allowed_of_window A _ _ p Hin Q1 Q2 ltac:(lia)) in E. discriminate.
Qed.

Lemma dsj_win : forall a k slo shi, In (pg_dn slo, pg_up shi) A -> slo <= a -> a + k <= shi ->
  (shi <= shad P \/ shad (P + msz) <= slo) -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k slo shi Hin H1 H2 H3. pose proof rv_pages as ((R1 & R2) & R3 & (R4 & R5) & R6 & R7 & R8).
  assert (B8 : p_last P n + 4096 < 2 ^ 64) by (unfold K_LOW_SHADOW_hi, K_HIGH_SHADOW_hi in *; lia).
  assert (B0 : 0 <= p_first P) by (unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_lo in *; lia).
  unfold W_rev. apply dsj_app; [cbn [disjoint_from]; split; [lia | exact I]|].
  apply dsj_app; [apply (dsj_pad _ a k slo shi Hin H1 H2 R3 B0); lia | apply (dsj_pad _ a k slo shi Hin H1 H2 R6); lia].
Qed.

(* [comment removed for export] *)
Lemma rv_prb_app : forall a k, l_PRB L <= a -> a + k <= l_PRB L + 0x2000011000 -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H1 H2. apply rv_app.
  pose proof (g_grant Σ (geo_of_ART Σ m HA) (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & G4 & _). lia.
Qed.

Lemma rv_prim_shad : forall a k, shad (l_SB L) <= a -> a + k <= shad (l_SB L + 2 ^ 37) -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H1 H2. pose proof rv_pages as ((R1 & R2) & R3 & (R4 & R5) & R6 & R7 & _). pose proof rv_shad as (S1 & S2 & S3 & S4 & S5 & _).
  pose proof rv_map as (M1 & M2 & _ & _ & _ & _ & M7 & _).
  pose proof (rv_grant_apart (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as Ap.
  pose proof (g_prb Σ (geo_of_ART Σ m HA)) as (P1 & P2 & P3).
  apply (dsj_within _ _ _ a k rv_within). unfold apart in Ap.
  apply Z.mod_divide in P3, R3, R6, M2, M7; try lia. destruct P3 as [q1 E1]. destruct R3 as [q2 E2]. destruct R6 as [q3 E3].
  destruct M2 as [q4 E4]. destruct M7 as [q5 E5].
  assert (D1 : shad (l_SB L) = q1 * 8192 + SHB) by (unfold shad; rewrite E1; replace (q1 * 2 ^ 16) with (q1 * 8192 * 8) by ring; rewrite Z.div_mul by lia; reflexivity).
  assert (D2 : shad (l_SB L + 2 ^ 37) = q1 * 8192 + 2 ^ 34 + SHB)
    by (unfold shad; rewrite E1; replace (q1 * 2 ^ 16 + 2 ^ 37) with ((q1 * 8192 + 2 ^ 34) * 8) by ring; rewrite Z.div_mul by lia; reflexivity).
  assert (D3 : shad P = q4 * 512 + SHB) by (unfold shad; rewrite E4; replace (q4 * 4096) with (q4 * 512 * 8) by ring; rewrite Z.div_mul by lia; reflexivity).
  assert (D4 : msz / 8 = q5 * 512) by (rewrite E5; replace (q5 * 4096) with (q5 * 512 * 8) by ring; apply Z.div_mul; lia).
  rewrite S2, D3, D4 in R4. rewrite D3 in R1, R2. rewrite D1 in H1. rewrite D2 in H2. rewrite E2 in *. rewrite E3 in *.
  clear - H1 H2 R1 R2 R4 Ap P1 P2 E1 E4 E5. unfold SHB in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from [] a k -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn. intros a k H1 H2 _. apply rv_app. unfold SEGTOP_A, K_LOW_SHADOW_lo in *. lia. Qed.

Lemma rv_grant : forall i b gn a k, nth_error (startup_grants L) i = Some (b, gn) -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros i b gn a k Hi _ H1 H2. pose proof (g_grant Σ (geo_of_ART Σ m HA) b gn (nth_error_In _ _ Hi)) as (G1 & _ & _ & G4 & _).
  apply rv_app. lia.
Qed.

Lemma rv_T : forall a k, l_T L <= a -> a + k <= l_T L + 4096 -> disjoint_from [] a k -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H1 H2 _. pose proof (g_grant Σ (geo_of_ART Σ m HA) (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _).
  apply rv_app. lia.
Qed.

Lemma rv_ris : forall a k, RIS_of (l_SB L) <= a -> a + k <= RIS_of (l_SB L) + 4096 -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H1 H2. pose proof (fk_prb Σ (geo_of_ART Σ m HA)) as (X1 & X2 & X3 & X4 & X5). unfold RIS_of in *.
  apply rv_prb_app; lia.
Qed.

Lemma rv_fa : forall c a k, 1 <= c <= 31 -> ~ In c [] -> fa (l_SB L) c <= a -> a + k <= fa (l_SB L) c + kFaCap -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros c a k Hc _ H1 H2. pose proof (fk_prb Σ (geo_of_ART Σ m HA)) as (X1 & X2 & X3 & X4 & X5). unfold fa, rb, kFaCap in *.
  apply rv_prb_app; lia.
Qed.

Lemma rv_slot : forall c i st a k, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) [] ->
  p_abeg (l_SB L) c i <= a -> a + k <= p_abeg (l_SB L) c i + ClassSize c -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros c i st a k Hc Hi _ H1 H2. pose proof (fk_prb Σ (geo_of_ART Σ m HA)) as (X1 & X2 & X3 & X4 & X5).
  pose proof (fk_slot Σ (geo_of_ART Σ m HA) c i st Hc Hi) as (Y1 & Y2 & Y3 & Y4). unfold rb, kUserCap in *.
  apply rv_prb_app; lia.
Qed.

Lemma rv_shad_slot : forall c i st a k, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) [] ->
  shad (p_abeg (l_SB L) c i) <= a -> a + k <= shad (p_abeg (l_SB L) c i + ClassSize c) -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros c i st a k Hc Hi _ H1 H2.
  pose proof (fk_slot Σ (geo_of_ART Σ m HA) c i st Hc Hi) as (Y1 & Y2 & Y3 & Y4). unfold rb, kUserCap in *.
  apply rv_prim_shad; [eapply Z.le_trans; [apply (fk_shad_mono (l_SB L) (p_abeg (l_SB L) c i)); lia | exact H1]|].
  eapply Z.le_trans; [exact H2|]. apply fk_shad_mono. lia.
Qed.

Lemma rv_shad_reg : forall c a k, 1 <= c <= 31 -> ~ In c [] ->
  shad (rb (l_SB L) c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= a -> a + k <= shad (rb (l_SB L) c + 2 ^ 32) ->
  disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros c a k Hc _ H1 H2. pose proof (ClassSize_range c Hc) as (C1 & _).
  apply rv_prim_shad; [eapply Z.le_trans; [|exact H1]; apply fk_shad_mono; unfold rb; lia|].
  eapply Z.le_trans; [exact H2|]. apply fk_shad_mono. unfold rb. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_sec_app : forall k s, nth_error (sec Σ) k = Some s ->
  (s_mb s + smsz (s_n s) <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= s_mb s) /\ 0 < s_mb s /\ 0 <= smsz (s_n s).
Proof using HA.
  intros k s Hk. pose proof (ART_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (G1 & _ & G3 & G4 & _) & _).
  pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (Hn1 & _ & _ & _ & _ & _ & _ & Hr & Hu & _). split; [exact G4|]. lia.
Qed.

Lemma rv_secmap : forall k s a k', nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + k' <= s_mb s + smsz (s_n s) ->
  disjoint_from (W_rev Σ P n) a k'.
Proof using HA HG Hn. intros k s a k' Hk _ H1 H2. pose proof (rv_sec_app k s Hk) as (X & _). apply rv_app. lia. Qed.

Lemma in_allow_main : forall w, In w (allow_main L) -> In w A.
Proof. intros w Hw. unfold rtA_allow. apply in_or_app. right. apply in_or_app. right. exact Hw. Qed.

(* [comment removed for export] *)
Lemma rv_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid (W_rev Σ P n) s.
Proof using HA HG Hn.
  intros k s Hk. pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (Hn1 & G1 & G3 & G5 & Hp & _ & _ & Hroom & Hu & _).
  pose proof (rv_sec_app k s Hk) as (X & _ & _).
  assert (Hin : In (pg_dn (shad (s_mb s)), pg_up (shad (s_mb s + smsz (s_n s)))) A).
  { pose proof (ART_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & _ & _ & HG3).
    unfold rtA_allow. apply in_or_app. left. exact (proj1 (Forall_forall _ _) HG3 s (nth_error_In _ _ Hk)). }
  assert (Hap : apart P msz (s_mb s) (smsz (s_n s))).
  { destruct HG as (_ & Hap). pose proof (proj1 (Forall_forall _ _) Hap (secmap s) ltac:(unfold rt_maps; apply in_or_app; left;
      apply in_map; apply (proj1 (in_rev (sec Σ) s)); exact (nth_error_In _ _ Hk))) as Y.
    unfold secmap in Y. cbn [fst snd] in Y. pose proof (fk_aceil Σ (geo_of_ART Σ m HA)) as (_ & Z1).
    rewrite !unsigned_lit in Y by lia. exact Y. }
  pose proof rv_map as (M1 & _ & M3 & _).
  assert (Hsh : shad (s_mb s + smsz (s_n s)) <= shad P \/ shad (P + msz) <= shad (s_mb s)).
  { unfold apart in Hap. destruct Hap as [Y|Y]; [right | left]; apply fk_shad_mono; lia. }
  assert (SH : forall a k', shad (s_mb s) <= a -> a + k' <= shad (s_mb s + smsz (s_n s)) -> disjoint_from (W_rev Σ P n) a k')
    by (intros a k' H1 H2; exact (dsj_win a k' _ _ Hin H1 H2 Hsh)).
  assert (Hu8 : 0 <= ru8 (s_n s)) by lia.
  unfold schunk_avoid.
  split; [apply (rv_secmap k s); [exact Hk | intros [] | lia | lia]|].
  split; [apply (rv_secmap k s); [exact Hk | intros [] | lia | lia]|].
  split; [apply (rv_secmap k s); [exact Hk | intros [] | lia | destruct (s_quar s); lia]|].
  pose proof (fk_shad_le2 (s_mb s) 6144 ltac:(lia) ltac:(lia)) as E1. change (6144 / 8) with 768 in E1.
  pose proof (fk_shad_le2 (s_mb s + 6144) (ru8 (s_n s)) ltac:(lia) Hu8) as E2.
  pose proof (fk_shad_le2 (s_mb s + 6144 + ru8 (s_n s)) (smsz (s_n s) - 6144 - ru8 (s_n s)) ltac:(lia) ltac:(lia)) as E3.
  replace (s_mb s + 6144 + ru8 (s_n s) + (smsz (s_n s) - 6144 - ru8 (s_n s))) with (s_mb s + smsz (s_n s)) in E3 by ring.
  assert (0 <= (smsz (s_n s) - 6144 - ru8 (s_n s)) / 8) by (apply Z.div_pos; lia). assert (0 <= ru8 (s_n s) / 8) by (apply Z.div_pos; lia).
  pose proof (fk_shad_mono (s_mb s + 6144 + ru8 (s_n s)) (s_mb s + smsz (s_n s)) ltac:(lia)) as E4.
  pose proof (fk_shad_mono (s_mb s) (s_mb s + 6144) ltac:(lia)) as E5.
  pose proof (fk_shad_mono (s_mb s + 6144) (s_mb s + 6144 + ru8 (s_n s)) ltac:(lia)) as E6.
  replace (s_mb s + 4096 + 2048) with (s_mb s + 6144) by ring.
  split; [change ((4096 + 2048) / 8) with 768; apply SH; [lia | rewrite Z.max_r by lia; lia]|].
  split.
  - apply SH; [lia|]. destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
  - apply SH; [lia | ]. replace (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) with (smsz (s_n s) - 6144 - ru8 (s_n s)) by ring.
    rewrite Z.max_r by (apply Z.div_pos; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma rv_fsb : forall a k, l_FSB L <= a -> a + k <= l_FSB L + 0xb09000 -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn. intros a k H1 H2. exact (rv_grant 5 (l_FSB L) 0xb09000 a k eq_refl ltac:(lia) H1 H2). Qed.

Lemma rv_fshad : forall f k, l_FSB L <= f -> f + k <= l_FSB L + 0xb09000 -> 0 <= k ->
  disjoint_from (W_rev Σ P n) (shad f) (k / 8).
Proof using HA HG Hn.
  intros f k H1 H2 Hk. pose proof (rv_grant_apart (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as Ap.
  pose proof (g_grant Σ (geo_of_ART Σ m HA) (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  pose proof rv_map as (M1 & _).
  apply (dsj_win _ _ (shad (l_FSB L)) (shad (l_FSB L + 0xb09000))).
  - apply in_allow_main. unfold allow_main. right; right; left; reflexivity.
  - apply fk_shad_mono. lia.
  - pose proof (fk_shad_le2 f k ltac:(lia) Hk) as E. pose proof (fk_shad_mono (f + k) (l_FSB L + 0xb09000) ltac:(lia)). lia.
  - unfold apart in Ap. destruct Ap as [Y|Y]; [right | left]; apply fk_shad_mono; lia.
Qed.

Lemma rv_fs_cls : forall k, (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4)%nat -> fs_cls_avoid (W_rev Σ P n) (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof using HA HG Hn.
  intros k Hk. pose proof (geo_of_ART Σ m HA) as HGo. pose proof HGo as (_ & _ & _ & HF). destruct HF as (F0 & F2 & (F4 & Fc1 & Fc3) & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; [exact (proj1 F0) | exact (proj1 Fc1) | exact (proj1 F2) | exact (proj1 Fc3) | exact (proj1 F4)]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 1 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3 \/ Z.of_nat k = 4) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
  pose proof (fl_flags_range _ Hc) as (R1 & R2).
  unfold fs_cls_avoid. split; [apply rv_fsb; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia|]. split.
  - rewrite Hlen. apply rv_fsb; unfold fl_base; lia.
  - intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
    assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
    split; [apply rv_fsb; lia|]. apply rv_fshad; lia.
Qed.

Lemma rv_fs : fs_avoid (W_rev Σ P n) Σ.
Proof using HA HG Hn.
  pose proof (geo_of_ART Σ m HA) as HGo.
  pose proof (g_grant Σ HGo (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split; [apply rv_fsb; lia|].
  split; [exact (rv_fs_cls 0%nat ltac:(lia))|]. split; [exact (rv_fs_cls 2%nat ltac:(lia))|]. split; [exact (conj (rv_fs_cls 4%nat ltac:(lia)) (conj (rv_fs_cls 1%nat ltac:(lia)) (rv_fs_cls 3%nat ltac:(lia))))|].
  split.
  { apply Forall_forall. intros r Hr. apply rv_app. left.
      unfold fs_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
      g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls,
      K_LOW_SHADOW_lo; lia|]); destruct Hr. }
  split; [apply (rv_grant 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
  split; [apply rv_T; [lia | lia | exact I]|].
  apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (g_frame Σ HGo f k Hin) as (X1 & X2 & X3). apply rv_fsb; lia.
Qed.

(* [comment removed for export] *)
Lemma rv_shadow : shadow_avoid (W_rev Σ P n) L.
Proof using HA HG Hn.
  pose proof (fk_aceil Σ (geo_of_ART Σ m HA)) as (X1 & X2). pose proof rv_map as (M1 & M2 & M3 & M4 & M5 & _).
  split.
  - apply (dsj_win _ _ (shad (l_ACEIL L)) (shad (2 ^ 47))).
    + apply in_allow_main. unfold allow_main. right; right; right; left; reflexivity.
    + lia.
    + pose proof (fk_shad_le2 (l_ACEIL L) (2 ^ 47 - l_ACEIL L) ltac:(unfold SHB in *; lia) ltac:(lia)) as E.
      replace (l_ACEIL L + (2 ^ 47 - l_ACEIL L)) with (2 ^ 47) in E by ring. rewrite Z.max_r by (apply Z.div_pos; lia). lia.
    + right. apply fk_shad_mono. lia.
  - apply Forall_forall. intros r Hr.
    assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0xbcacd0) by (unfold SH_RNGS, IMG_HULL, GD_IMG_END, CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply (dsj_win _ _ (shad 0x10000) (shad SEGTOP_A)).
    + apply in_allow_main. unfold allow_main. left; reflexivity.
    + apply fk_shad_mono; lia.
    + assert ((snd r - 1) / 8 < 1545728) by (apply Z.div_lt_upper_bound; lia).
      assert (shad (snd r - 1) + 1 <= shad SEGTOP_A) by (unfold shad, SEGTOP_A; change (0xbcb000 / 8) with 1545728; lia). lia.
    + left. apply fk_shad_mono. lia.
Qed.

Lemma dsj_nil_all : forall l : list (Z * Z), Forall (fun r => disjoint_from [] (fst r) (snd r)) l.
Proof. intros l. apply Forall_forall. intros r _. exact I. Qed.
Lemma dsj_nil_all' : forall l : list (Z * Z), Forall (fun r => disjoint_from [] (fst r) (snd r - fst r)) l.
Proof. intros l. apply Forall_forall. intros r _. exact I. Qed.

(* [comment removed for export] *)
Theorem rev_avoid : art_avoid (W_rev Σ P n) Σ.
Proof using HA HG Hn.
  pose proof (geo_of_ART Σ m HA) as HGo.
  split.
  { apply Forall_forall. intros r Hr. apply rv_app.
    destruct (consts_rngs_kind L r Hr) as [Hl|[(H1 & H2)|[Er|(H1 & H2)]]].
    - left. unfold CONSTS_LITS in Hl. repeat (destruct Hl as [<-|Hl]; [cbn [fst snd]; unfold K_LOW_SHADOW_lo; lia|]). destruct Hl.
    - pose proof (g_grant Σ HGo (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _). lia.
    - rewrite Er. cbn [fst snd].
      pose proof (g_grant Σ HGo (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _). lia.
    - pose proof (g_grant Σ HGo (l_TCX L) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _). lia. }
  split.
  { intros c Hc. split.
    - exact (kv_reg Σ (W_rev Σ P n) [] HGo (ris_of_whole (l_SB L) (W_rev Σ P n) [] rv_ris) rv_fa rv_shad_reg c Hc (fun X => X)).
    - exact (kv_pclass Σ (W_rev Σ P n) [] rv_T c Hc I). }
  split; [intros c i st Hc Hi; exact (kv_pchunk Σ (W_rev Σ P n) [] HGo rv_slot rv_shad_slot c i st Hc Hi (fun X => X))|].
  split; [exact rv_schunk|].
  split; [exact (kv_sec Σ (W_rev Σ P n) [] HGo rv_img rv_grant (dsj_nil_all _))|].
  split.
  { apply (kv_quar Σ (W_rev Σ P n) [] [] [] HGo rv_img rv_T rv_slot I (dsj_nil_all _) (fun _ _ X => X)).
    pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & HQw & _). exact (proj1 (proj2 (proj2 HQw))). }
  split.
  { apply (kv_dep Σ (W_rev Σ P n) [] rv_img (dsj_nil_all _)).
    intros i b gn a k Hi _ H1 H2. pose proof (g_grant Σ HGo b gn (nth_error_In _ _ Hi)) as (_ & _ & _ & G4 & _). apply rv_app. lia. }
  split; [exact rv_fs|].
  split; [exact (kv_ia (W_rev Σ P n) [] rv_img (dsj_nil_all _))|].
  exact rv_shadow.
Qed.
End Rev.
