(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs RT_state RT_rep RT_trans RT_freelift RT_geo0 RT_fkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Definition dzone (Σ : rtsA) (D DSH : list (Z * nat)) (DS : list nat) (TZ IZ : list ivl) (DC : list Z) (zlo zhi : Z) (iv : ivl) : Prop :=
  (exists z, In z IZ /\ fst z <= fst iv /\ snd iv <= snd z)
  \/ (exists z, In z TZ /\ fst z <= fst iv /\ snd iv <= snd z)
  \/ (exists c i, In (c, i) D /\ p_abeg (l_SB (lay Σ)) c i <= fst iv /\ snd iv <= p_abeg (l_SB (lay Σ)) c i + ClassSize c)
  \/ (exists c i, In (c, i) DSH /\ shad (p_abeg (l_SB (lay Σ)) c i) <= fst iv /\ snd iv <= shad (p_abeg (l_SB (lay Σ)) c i + ClassSize c))
  \/ (exists c, In c DC /\ rinfo (RIS_of (l_SB (lay Σ))) c <= fst iv /\ snd iv <= rinfo (RIS_of (l_SB (lay Σ))) c + 128)
  \/ (exists c, In c DC /\ fa (l_SB (lay Σ)) c <= fst iv /\ snd iv <= fa (l_SB (lay Σ)) c + kFaCap)
  \/ (exists c, In c DC /\ shad (rb (l_SB (lay Σ)) c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= fst iv
                        /\ snd iv <= shad (rb (l_SB (lay Σ)) c + 2 ^ 32))
  \/ (exists k s, In k DS /\ nth_error (sec Σ) k = Some s /\ s_mb s <= fst iv /\ snd iv <= s_mb s + smsz (s_n s))
  \/ (exists k s, In k DS /\ nth_error (sec Σ) k = Some s /\ shad (s_mb s) <= fst iv /\ snd iv <= shad (s_mb s + smsz (s_n s)))
  \/ (zlo <= fst iv /\ snd iv <= zhi).

Lemma dsj_forall : forall (W : list ivl) a n, Forall (fun iv => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|]. inversion H; subst. split; [exact H2 | apply IH; exact H3].
Qed.

Lemma dsj_Forall : forall (W : list ivl) a n, disjoint_from W a n -> Forall (fun iv => a + n <= fst iv \/ snd iv <= a) W.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from] in H; [constructor|]. destruct H as (H1 & H2).
  constructor; [exact H1 | apply IH; exact H2].
Qed.

Lemma dsj_in : forall (Z0 : list ivl) z a n, disjoint_from Z0 a n -> In z Z0 -> a + n <= fst z \/ snd z <= a.
Proof. intros Z0 z a n H Hz. exact (proj1 (Forall_forall _ _) (dsj_Forall Z0 a n H) z Hz). Qed.

Section DKit.
Variables (Σ : rtsA) (D DSH : list (Z * nat)) (DS : list nat) (TZ IZ : list ivl) (DC : list Z) (zlo zhi : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis HD : forall c i, In (c, i) D -> 1 <= c <= 31 /\ exists st, nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis HDSH : forall c i, In (c, i) DSH -> 1 <= c <= 31 /\ exists st, nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis HDC : forall c, In c DC -> 1 <= c <= 31.
Hypothesis HIZ : Forall (fun z => 0x10000 <= fst z /\ snd z <= SEGTOP_A) IZ.
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation zone := (dzone Σ D DSH DS TZ IZ DC zlo zhi).

Lemma dk_geo : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ 0 < PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ SEGTOP_A <= PRB
  /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000 /\ K_HIGH_SHADOW_hi <= PRB.
Proof using HG.
  clear - HG. pose proof (fk_aceil Σ HG) as (A1 & A2). pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
  pose proof (g_grant Σ HG PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & G4 & _).
  unfold K_LOW_SHADOW_lo in G4. repeat split; try lia.
Qed.

Lemma dk_T : 0 < T /\ T + 4096 <= l_ACEIL L /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T) /\ (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T)
  /\ (T + 4096 <= PRB \/ PRB + 0x2000011000 <= T).
Proof using HG.
  clear - HG. pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (G1 & _ & G3 & G4 & G5).
  pose proof (g_apart Σ HG 0 2 _ _ ltac:(lia) eq_refl eq_refl) as A. cbn [fst snd] in A. unfold apart in A.
  unfold SEGTOP_A in *. repeat split; try lia.
Qed.

Lemma dk_grant : forall j b gn, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8)%nat ->
  0 < b /\ b + gn <= l_ACEIL L /\ (b + gn <= 0x10000 \/ SEGTOP_A <= b) /\ (b + gn <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= b)
  /\ (b + gn <= PRB \/ PRB + 0x2000011000 <= b) /\ (b + gn <= T \/ T + 4096 <= b) /\ 0 < gn.
Proof using HG.
  clear - HG. intros j b gn Hj Hjr. pose proof (g_grant Σ HG b gn (nth_error_In _ _ Hj)) as (G1 & _ & G3 & G4 & G5).
  assert (Ap : forall j', j' <> j -> forall g, nth_error (startup_grants L) j' = Some g -> apart b gn (fst g) (snd g)).
  { intros j' Hne g Hg. destruct (Nat.lt_ge_cases j j') as [Hl|Hl].
    - exact (g_apart Σ HG j j' (b, gn) g Hl Hj Hg).
    - pose proof (g_apart Σ HG j' j g (b, gn) ltac:(lia) Hg Hj) as X. unfold apart in *. cbn [fst snd] in X. lia. }
  pose proof (Ap 0%nat ltac:(lia) _ eq_refl) as A0. pose proof (Ap 2%nat ltac:(lia) _ eq_refl) as A2. cbn [fst snd] in A0, A2. unfold apart in A0, A2.
  assert (0 < gn) by (destruct Hjr as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn in Hj; injection Hj as <- <-; lia).
  repeat split; try lia.
Qed.

Lemma dk_slot : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))
  /\ ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= kUserCap /\ 32 <= ClassSize c.
Proof using HG. clear - HG. intros c i st Hc Hn. pose proof (fk_slot Σ HG c i st Hc Hn) as (S1 & S2 & S3 & S4). repeat split; lia. Qed.

Lemma dk_rb : forall c, 1 <= c <= 31 -> PRB <= rb SB c /\ rb SB c + 2 ^ 32 <= SB + 2 ^ 37 /\ fa SB c + kFaCap <= rb SB c + 2 ^ 32
  /\ rb SB c + kUserCap = fa SB c.
Proof using HG. clear - HG. intros c Hc. pose proof dk_geo as (_ & _ & _ & _ & _ & G6 & G7 & _). unfold fa, rb, kFaCap, kUserCap. repeat split; lia. Qed.

Lemma dk_auser : forall c, 1 <= c <= 31 -> 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= kUserCap.
Proof using HG.
  clear - HG. intros c Hc. pose proof HG as (_ & (HR & _) & _). pose proof (HR c Hc) as (W1 & _ & W3 & _).
  pose proof (ClassSize_range c Hc) as ((Hcs & _) & _). split; [apply Z.mul_nonneg_nonneg; lia | lia].
Qed.

Lemma dk_map : forall k s, nth_error (sec Σ) k = Some s ->
  0 < s_mb s /\ s_mb s + smsz (s_n s) <= l_ACEIL L /\ (s_mb s + smsz (s_n s) <= 0x10000 \/ SEGTOP_A <= s_mb s)
  /\ (s_mb s + smsz (s_n s) <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= s_mb s)
  /\ (s_mb s + smsz (s_n s) <= PRB \/ PRB + 0x2000011000 <= s_mb s) /\ (s_mb s + smsz (s_n s) <= T \/ T + 4096 <= s_mb s)
  /\ (forall j b gn, nth_error (startup_grants L) j = Some (b, gn) -> s_mb s + smsz (s_n s) <= b \/ b + gn <= s_mb s)
  /\ 0 < smsz (s_n s)
  /\ (forall k' s', nth_error (sec Σ) k' = Some s' -> k' <> k -> s_mb s + smsz (s_n s) <= s_mb s' \/ s_mb s' + smsz (s_n s') <= s_mb s).
Proof using HG.
  clear - HG. intros k s Hk. pose proof (fk_map Σ HG k s Hk) as (Hn & G1 & G3 & G5 & Hp & _ & HGs & Hroom & Hu & HSP).
  pose proof (HG) as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (_ & _ & _ & G4 & _) & _).
  pose proof (proj1 (Forall_forall _ _) HGs (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as AT.
  unfold apart in *. cbn [fst snd] in AT.
  split; [exact G1|]. split; [exact G3|]. split; [exact G5|]. split; [exact G4|]. split; [lia|]. split; [lia|].
  split; [intros j b gn Hj; pose proof (proj1 (Forall_forall _ _) HGs (b, gn) (nth_error_In _ _ Hj)) as X; unfold apart in X; cbn [fst snd] in X; lia|].
  split; [lia|]. intros k' s' Hk' Hne. pose proof (HSP k' s' Hk' Hne) as X. unfold apart in X. lia.
Qed.

Lemma dk_shad_rng : forall x, 0 <= x <= 2 ^ 47 -> SHB <= shad x <= 2 ^ 44 + SHB.
Proof. intros x Hx. unfold shad. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. Qed.

Lemma zone_cases : forall iv, zone iv ->
  (exists z, In z IZ /\ fst z <= fst iv /\ snd iv <= snd z /\ 0x10000 <= fst z /\ snd z <= SEGTOP_A)
  \/ (exists z, In z TZ /\ fst z <= fst iv /\ snd iv <= snd z /\ T <= fst z /\ snd z <= T + 4096)
  \/ (exists c i st, In (c, i) D /\ 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some st
        /\ p_abeg SB c i <= fst iv /\ snd iv <= p_abeg SB c i + ClassSize c)
  \/ (exists c i st, In (c, i) DSH /\ 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some st
        /\ shad (p_abeg SB c i) <= fst iv /\ snd iv <= shad (p_abeg SB c i + ClassSize c))
  \/ (exists c, In c DC /\ 1 <= c <= 31 /\ rinfo (RIS_of SB) c <= fst iv /\ snd iv <= rinfo (RIS_of SB) c + 128)
  \/ (exists c, In c DC /\ 1 <= c <= 31 /\ fa SB c <= fst iv /\ snd iv <= fa SB c + kFaCap)
  \/ (exists c, In c DC /\ 1 <= c <= 31 /\ shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= fst iv
                        /\ snd iv <= shad (rb SB c + 2 ^ 32))
  \/ (exists k s, In k DS /\ nth_error (sec Σ) k = Some s /\ s_mb s <= fst iv /\ snd iv <= s_mb s + smsz (s_n s))
  \/ (exists k s, In k DS /\ nth_error (sec Σ) k = Some s /\ shad (s_mb s) <= fst iv /\ snd iv <= shad (s_mb s + smsz (s_n s)))
  \/ (zlo <= fst iv /\ snd iv <= zhi).
Proof using HD HDSH HDC HIZ HTZ.
  clear - HD HDSH HDC HIZ HTZ. intros iv Hz.
  destruct Hz as [(z & Hz & X)|[(z & Hz & X)|[(c & i & Hci & X)|[(c & i & Hci & X)|[(c & Hc & X)|[(c & Hc & X)|[(c & Hc & X)|[X|[X|X]]]]]]]]].
  - left. exists z. pose proof (proj1 (Forall_forall _ _) HIZ z Hz) as Y. destruct X as (X1 & X2). destruct Y as (Y1 & Y2).
    exact (conj Hz (conj X1 (conj X2 (conj Y1 Y2)))).
  - right; left. exists z. pose proof (proj1 (Forall_forall _ _) HTZ z Hz) as Y. destruct X as (X1 & X2). destruct Y as (Y1 & Y2).
    exact (conj Hz (conj X1 (conj X2 (conj Y1 Y2)))).
  - right; right; left. destruct (HD c i Hci) as (Hc & st & Hst). exists c, i, st. destruct X as (X1 & X2).
    exact (conj Hci (conj Hc (conj Hst (conj X1 X2)))).
  - right; right; right; left. destruct (HDSH c i Hci) as (Hc & st & Hst). exists c, i, st. destruct X as (X1 & X2).
    exact (conj Hci (conj Hc (conj Hst (conj X1 X2)))).
  - right; right; right; right; left. exists c. pose proof (HDC c Hc) as Y. destruct X as (X1 & X2). exact (conj Hc (conj Y (conj X1 X2))).
  - right; right; right; right; right; left. exists c. pose proof (HDC c Hc) as Y. destruct X as (X1 & X2). exact (conj Hc (conj Y (conj X1 X2))).
  - right; right; right; right; right; right; left. exists c. pose proof (HDC c Hc) as Y. destruct X as (X1 & X2). exact (conj Hc (conj Y (conj X1 X2))).
  - do 7 right. left. exact X.
  - do 8 right. left. exact X.
  - do 9 right. exact X.
Qed.

Section W.
Variable W : list ivl.
Hypothesis HW : Forall zone W.

Lemma dk_all : forall a n, (forall iv, zone iv -> a + n <= fst iv \/ snd iv <= a) -> disjoint_from W a n.
Proof using HW. intros a n H. apply dsj_forall. apply Forall_forall. intros iv Hiv. exact (H iv (proj1 (Forall_forall _ _) HW iv Hiv)). Qed.

Lemma dk_shad_mono : forall x y, x <= y -> shad x <= shad y.
Proof. intros x y H. unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Ltac zdestr Z :=
  destruct Z as [(z & Hz & X1 & X2 & X3 & X4)|[(z & Hz & X1 & X2 & X3 & X4)|[(c & i & st & Hci & Hc & Hst & X1 & X2)
      |[(c & i & st & Hci & Hc & Hst & X1 & X2)|[(c & Hc0 & Hc & X1 & X2)|[(c & Hc0 & Hc & X1 & X2)|[(c & Hc0 & Hc & X1 & X2)
      |[(k & s & Hk0 & Hk & X1 & X2)|[(k & s & Hk0 & Hk & X1 & X2)|(X1 & X2)]]]]]]]]].

Lemma dk_slot_in : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  PRB <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= SB + 2 ^ 37 /\ rb SB c <= p_abeg SB c i
  /\ p_abeg SB c i + ClassSize c <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))) /\ ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= kUserCap
  /\ 0 < ClassSize c.
Proof using HG.
  intros c i st Hc Hn. pose proof (dk_slot c i st Hc Hn) as (S1 & S2 & S3 & S4). pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4).
  unfold fa, kUserCap, kFaCap in *. repeat split; lia.
Qed.

Lemma dk_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ a n -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros a n H1 H2 HZ. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  zdestr Z.
  - pose proof (dsj_in IZ z a n HZ Hz). lia.
  - clear - T3 X1 X2 X3 X4 H1 H2. unfold SEGTOP_A in *. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). clear - G5 S1 X1 H2. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & _). pose proof (dk_shad_mono PRB (p_abeg SB c i) S1). pose proof (dk_shad_rng PRB ltac:(lia)).
    clear - X1 H2 H H0. unfold SHB, SEGTOP_A in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & _). clear - G5 R1 R2 X1 H2 Hc. unfold rinfo, RIS_of, rb in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). clear - G5 R1 R4 X1 H2. unfold kUserCap in *. lia.
  - pose proof (dk_shad_rng (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))))) as Q.
    pose proof (dk_rb c Hc) as (R1 & R2 & _). assert (0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; pose proof (ClassSize_range c Hc); lia).
    assert (Hx : SHB <= shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))))) by (unfold shad; pose proof (Z.div_pos (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) 8 ltac:(lia) ltac:(lia)); lia).
    clear - Hx X1 H2. unfold SHB, SEGTOP_A in *. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & M3 & _). clear - M3 X1 X2 H1 H2. unfold SEGTOP_A in *. lia.
  - pose proof (dk_map k s Hk) as (M1 & _). assert (Hx : SHB <= shad (s_mb s)) by (unfold shad; pose proof (Z.div_pos (s_mb s) 8 ltac:(lia) ltac:(lia)); lia).
    clear - Hx X1 H2. unfold SHB, SEGTOP_A in *. lia.
  - clear - Hzlo G1 X1 H2. unfold SHB, SEGTOP_A in *. lia.
Qed.

Lemma dk_Tz : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros a n H1 H2 HZ. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  zdestr Z.
  - clear - T3 X1 X2 X3 X4 H1 H2. unfold SEGTOP_A in *. lia.
  - pose proof (dsj_in TZ z a n HZ Hz). lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). clear - T5 S1 S2 X1 X2 H1 H2 G7. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) (SB + 2 ^ 37) S2).
    pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)). pose proof (dk_shad_mono PRB (p_abeg SB c i) S1). pose proof (dk_shad_rng PRB ltac:(lia)).
    clear - T4 X1 X2 H1 H2 H H0 H3 H4. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & _). clear - T5 R1 R2 X1 X2 H1 H2 Hc G6 G7. unfold rinfo, RIS_of, rb in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). clear - T5 R1 R2 R3 R4 X1 X2 H1 H2 G7. unfold kUserCap, kFaCap in *. lia.
  - pose proof (dk_auser c Hc) as (U1 & U2). pose proof (dk_rb c Hc) as (R1 & R2 & _).
    pose proof (dk_shad_rng (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) ltac:(unfold kUserCap in *; lia)).
    pose proof (dk_shad_rng (rb SB c + 2 ^ 32) ltac:(lia)).
    clear - T4 X1 X2 H1 H2 H H0. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_map k s Hk) as (_ & _ & _ & _ & _ & M6 & _). clear - M6 X1 X2 H1 H2. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & _).
    pose proof (dk_shad_rng (s_mb s) ltac:(lia)). pose proof (dk_shad_rng (s_mb s + smsz (s_n s)) ltac:(lia)).
    clear - T4 X1 X2 H1 H2 H H0. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - clear - Hzlo T2 X1 H2. lia.
Qed.

Lemma dk_shad_apart : forall x1 y1 x2 y2, x1 <= y1 -> x2 <= y2 -> (y1 <= x2 \/ y2 <= x1) ->
  shad y1 <= shad x2 \/ shad y2 <= shad x1.
Proof. intros x1 y1 x2 y2 H1 H2 [H|H]; [left | right]; apply dk_shad_mono; exact H. Qed.

Lemma dk_regions : forall c c', 1 <= c <= 31 -> 1 <= c' <= 31 -> c <> c' -> rb SB c + 2 ^ 32 <= rb SB c' \/ rb SB c' + 2 ^ 32 <= rb SB c.
Proof. intros c c' Hc Hc' Hne. unfold rb. lia. Qed.

Lemma dk_grant_hw : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros j b gn a n Hj Hjr H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof (dk_grant j b gn Hj Hjr) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  zdestr Z.
  - clear - B3 X1 X2 X3 X4 H1 H2. unfold SEGTOP_A in *. lia.
  - clear - B6 X1 X2 X3 X4 H1 H2. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). clear - B5 S1 S2 X1 X2 H1 H2 G7. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) (SB + 2 ^ 37) S2).
    pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)). pose proof (dk_shad_mono PRB (p_abeg SB c i) S1). pose proof (dk_shad_rng PRB ltac:(lia)).
    clear - B4 X1 X2 H1 H2 H H0 H3 H4. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & _). clear - B5 R1 R2 X1 X2 H1 H2 Hc G6 G7. unfold rinfo, RIS_of, rb in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). clear - B5 R1 R2 R3 R4 X1 X2 H1 H2 G7. unfold kUserCap, kFaCap in *. lia.
  - pose proof (dk_auser c Hc) as (U1 & U2). pose proof (dk_rb c Hc) as (R1 & R2 & _).
    pose proof (dk_shad_rng (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) ltac:(unfold kUserCap in *; lia)).
    pose proof (dk_shad_rng (rb SB c + 2 ^ 32) ltac:(lia)).
    clear - B4 X1 X2 H1 H2 H H0. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_map k s Hk) as (_ & _ & _ & _ & _ & _ & M7 & _). pose proof (M7 j b gn Hj). clear - H X1 X2 H1 H2. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & _).
    pose proof (dk_shad_rng (s_mb s) ltac:(lia)). pose proof (dk_shad_rng (s_mb s + smsz (s_n s)) ltac:(lia)).
    clear - B4 X1 X2 H1 H2 H H0. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - clear - Hzlo B2 X1 H2. lia.
Qed.

Lemma dk_ris_hw : forall c' a n, 1 <= c' <= 31 -> ~ In c' DC -> rinfo (RIS_of SB) c' <= a -> a + n <= rinfo (RIS_of SB) c' + 120 ->
  disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros c' a n Hc' HDc H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  assert (Hr : SB + 2 ^ 37 <= a /\ a + n <= SB + 2 ^ 37 + 4096) by (clear - Hc' H1 H2; unfold rinfo, RIS_of in *; lia). rename H1 into P1. rename H2 into P2. destruct Hr as (H1 & H2).
  zdestr Z.
  - clear - G5 G6 X1 X2 X3 X4 H1 H2. unfold SEGTOP_A in *. lia.
  - clear - T5 G6 G7 X1 X2 X3 X4 H1 H2. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). clear - S2 X1 X2 H1 H2. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) (SB + 2 ^ 37) S2).
    pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)). clear - G6 G8 X2 H1 H H0. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - assert (c <> c') by (intros ->; exact (HDc Hc0)). clear - Hc Hc' H X1 X2 P1 P2. unfold rinfo, RIS_of in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). clear - R2 R3 X1 X2 H1 H2. unfold kFaCap in *. lia.
  - pose proof (dk_auser c Hc) as (U1 & U2). pose proof (dk_rb c Hc) as (R1 & R2 & _).
    pose proof (dk_shad_rng (rb SB c + 2 ^ 32) ltac:(lia)). clear - G6 G8 X2 H1 H. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_map k s Hk) as (_ & _ & _ & _ & M5 & _). clear - M5 G6 G7 X1 X2 H1 H2. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & _).
    pose proof (dk_shad_rng (s_mb s + smsz (s_n s)) ltac:(lia)). clear - G6 G8 X2 H1 H. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - clear - Hzlo G4 G7 X1 H2. lia.
Qed.

Lemma dk_fa_hw : forall c' a n, 1 <= c' <= 31 -> ~ In c' DC -> fa SB c' <= a -> a + n <= fa SB c' + kFaCap -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros c' a n Hc' HDc H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  pose proof (dk_rb c' Hc') as (Q1 & Q2 & Q3 & Q4).
  zdestr Z.
  - clear - G5 Q1 Q4 X1 X2 X3 X4 H1 H2. unfold SEGTOP_A, kUserCap in *. lia.
  - clear - T5 Q1 Q2 Q3 Q4 G7 X1 X2 X3 X4 H1 H2. unfold kUserCap, kFaCap in *. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & S3 & S4 & S5 & _). pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4).
    destruct (Z.eq_dec c c') as [->|Hne].
    + clear - S4 S5 Q4 X1 X2 H1 H2. unfold kUserCap in *. lia.
    + pose proof (dk_regions c c' Hc Hc' Hne). clear - H S3 S4 S5 Q3 Q4 X1 X2 H1 H2. unfold kUserCap, kFaCap in *. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) (SB + 2 ^ 37) S2).
    pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)). clear - G6 G8 Q1 Q4 X2 H1 H H0. unfold K_HIGH_SHADOW_hi, SHB, kUserCap in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & _). clear - Q2 Q3 X1 X2 H1 H2 Hc. unfold rinfo, RIS_of, kFaCap in *. lia.
  - assert (c <> c') by (intros ->; exact (HDc Hc0)). pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). pose proof (dk_regions c c' Hc Hc' H).
    clear - H0 Q3 Q4 R3 R4 X1 X2 H1 H2. unfold kUserCap, kFaCap in *. lia.
  - pose proof (dk_auser c Hc) as (U1 & U2). pose proof (dk_rb c Hc) as (R1 & R2 & _).
    pose proof (dk_shad_rng (rb SB c + 2 ^ 32) ltac:(lia)). clear - G6 G8 Q1 Q4 X2 H1 H. unfold K_HIGH_SHADOW_hi, SHB, kUserCap in *. lia.
  - pose proof (dk_map k s Hk) as (_ & _ & _ & _ & M5 & _). clear - M5 G6 G7 Q1 Q2 Q3 Q4 X1 X2 H1 H2. unfold kUserCap, kFaCap in *. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & _).
    pose proof (dk_shad_rng (s_mb s + smsz (s_n s)) ltac:(lia)). clear - G6 G8 Q1 Q4 X2 H1 H. unfold K_HIGH_SHADOW_hi, SHB, kUserCap in *. lia.
  - clear - Hzlo G4 G7 Q2 Q3 X1 H2. unfold kFaCap in *. lia.
Qed.

Lemma dk_slot_hw : forall c' i' st' a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st' -> ~ In (c', i') D ->
  p_abeg SB c' i' <= a -> a + n <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros c' i' st' a n Hc' Hn' HDc H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  pose proof (dk_slot_in c' i' st' Hc' Hn') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). pose proof (dk_rb c' Hc') as (P1 & P2 & P3 & P4).
  zdestr Z.
  - clear - G5 Q1 X1 X2 X3 X4 H1 H2. unfold SEGTOP_A in *. lia.
  - clear - T5 Q1 Q2 G7 X1 X2 X3 X4 H1 H2. lia.
  - assert (Hne : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [->|X]; [right; intros ->; exact (HDc Hci) | left; exact X]).
    pose proof (g_slot_apart Σ HG c i c' i' st st' Hc Hc' Hst Hn' Hne). clear - H X1 X2 H1 H2. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) (SB + 2 ^ 37) S2).
    pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)). clear - G8 Q1 X2 H1 H H0. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & _). clear - Q2 X1 X2 H1 H2 Hc. unfold rinfo, RIS_of in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). destruct (Z.eq_dec c c') as [->|Hne].
    + clear - Q4 Q5 P4 X1 X2 H1 H2. unfold kUserCap in *. lia.
    + pose proof (dk_regions c c' Hc Hc' Hne). clear - H Q3 Q4 Q5 R3 R4 X1 X2 H1 H2. unfold kUserCap, kFaCap in *. lia.
  - pose proof (dk_auser c Hc) as (U1 & U2). pose proof (dk_rb c Hc) as (R1 & R2 & _).
    pose proof (dk_shad_rng (rb SB c + 2 ^ 32) ltac:(lia)). clear - G8 Q1 X2 H1 H. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_map k s Hk) as (_ & _ & _ & _ & M5 & _). clear - M5 G7 Q1 Q2 X1 X2 H1 H2. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & _).
    pose proof (dk_shad_rng (s_mb s + smsz (s_n s)) ltac:(lia)). clear - G8 Q1 X2 H1 H. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - clear - Hzlo G4 G7 Q2 X1 H2. lia.
Qed.

Lemma dk_shad_slot_hw : forall c' i' st' a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st' -> ~ In (c', i') DSH ->
  shad (p_abeg SB c' i') <= a -> a + n <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros c' i' st' a n Hc' Hn' HDc H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  pose proof (dk_slot_in c' i' st' Hc' Hn') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  pose proof (dk_shad_mono PRB (p_abeg SB c' i') Q1) as M1. pose proof (dk_shad_mono (p_abeg SB c' i' + ClassSize c') (SB + 2 ^ 37) Q2) as M2.
  pose proof (dk_shad_rng PRB ltac:(lia)) as R1. pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)) as R2.
  assert (Hr : SHB <= a /\ a + n <= 2 ^ 44 + SHB) by (clear - M1 M2 R1 R2 H1 H2; lia). clear M1 M2 R1 R2.
  zdestr Z.
  - clear - Hr X1 X2 X3 X4. unfold SHB, SEGTOP_A in *. lia.
  - clear - T4 Hr X1 X2 X3 X4. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & _). clear - G8 S1 Hr X1 X2. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - assert (Hne : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [->|X]; [right; intros ->; exact (HDc Hci) | left; exact X]).
    pose proof (g_slot_apart Σ HG c i c' i' st st' Hc Hc' Hst Hn' Hne) as Ap. pose proof (dk_slot_in c i st Hc Hst) as (_ & _ & _ & _ & _ & S6).
    pose proof (dk_shad_apart (p_abeg SB c i) (p_abeg SB c i + ClassSize c) (p_abeg SB c' i') (p_abeg SB c' i' + ClassSize c') ltac:(lia) ltac:(lia) Ap) as SA.
    clear - SA X1 X2 H1 H2. lia.
  - pose proof (dk_rb c Hc) as (R1 & _). clear - G8 G6 R1 Hr X1 X2 Hc. unfold rinfo, RIS_of, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). clear - G8 R1 R4 Hr X1 X2. unfold kUserCap, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_auser c Hc) as (U1 & U2). destruct (Z.eq_dec c c') as [->|Hne].
    + pose proof (dk_shad_mono (p_abeg SB c' i' + ClassSize c') (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c'))))) as M.
      specialize (M Q4). clear - M X1 X2 H1 H2. lia.
    + pose proof (dk_regions c c' Hc Hc' Hne) as Rg. pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4).
      assert (Ap : rb SB c + 2 ^ 32 <= p_abeg SB c' i' \/ p_abeg SB c' i' + ClassSize c' <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
      { pose proof (dk_rb c' Hc') as (R1' & R2' & R3' & R4'). clear - Rg Q3 Q4 Q5 R3' R4' U1. unfold kUserCap, kFaCap in *. lia. }
      pose proof (dk_shad_apart (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (rb SB c + 2 ^ 32) (p_abeg SB c' i') (p_abeg SB c' i' + ClassSize c')
                    ltac:(unfold kUserCap in *; lia) ltac:(lia) ltac:(destruct Ap as [A|A]; [left; exact A | right]; lia)) as SA.

      destruct Ap as [A|A]; [clear - SA X1 X2 H1 H2; lia|].
      pose proof (dk_shad_mono (p_abeg SB c' i' + ClassSize c') (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) A) as M.
      clear - M X1 X2 H1 H2. lia.
  - pose proof (dk_map k s Hk) as (_ & _ & _ & M4 & _). clear - M4 G8 Q1 Hr X1 X2. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & M5 & _ & _ & M8 & _).
    assert (Ap : s_mb s + smsz (s_n s) <= p_abeg SB c' i' \/ p_abeg SB c' i' + ClassSize c' <= s_mb s) by (clear - M5 Q1 Q2 G7; lia).
    pose proof (dk_shad_apart (s_mb s) (s_mb s + smsz (s_n s)) (p_abeg SB c' i') (p_abeg SB c' i' + ClassSize c') ltac:(lia) ltac:(lia) Ap) as SA.
    clear - SA X1 X2 H1 H2. lia.
  - clear - Hzlo G1 Hr X1. lia.
Qed.

Lemma dk_shad_reg_hw : forall c' a n, 1 <= c' <= 31 -> ~ In c' DC ->
  shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a -> a + n <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros c' a n Hc' HDc H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  pose proof (dk_auser c' Hc') as (U1' & U2'). pose proof (dk_rb c' Hc') as (Q1 & Q2 & Q3 & Q4).
  pose proof (dk_shad_mono PRB (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) ltac:(lia)) as M1.
  pose proof (dk_shad_mono (rb SB c' + 2 ^ 32) (SB + 2 ^ 37) Q2) as M2.
  pose proof (dk_shad_rng PRB ltac:(lia)) as R1. pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)) as R2.
  assert (Hr : SHB <= a /\ a + n <= 2 ^ 44 + SHB) by (clear - M1 M2 R1 R2 H1 H2; lia). clear M1 M2 R1 R2.
  zdestr Z.
  - clear - Hr X1 X2 X3 X4. unfold SHB, SEGTOP_A in *. lia.
  - clear - T4 Hr X1 X2 X3 X4. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & _). clear - G8 S1 Hr X1 X2. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (Z.eq_dec c c') as [->|Hne].
    + pose proof (dk_shad_mono (p_abeg SB c' i + ClassSize c') (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) S4) as M.
      clear - M X2 H1. lia.
    + pose proof (dk_regions c c' Hc Hc' Hne) as Rg. pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4).
      assert (Ap : rb SB c' + 2 ^ 32 <= p_abeg SB c i \/ p_abeg SB c i + ClassSize c <= rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))).
      { clear - Rg S3 S4 S5 R3 R4 U1'. unfold kUserCap, kFaCap in *. lia. }
      destruct Ap as [A|A].
      * pose proof (dk_shad_mono (rb SB c' + 2 ^ 32) (p_abeg SB c i) A) as M. clear - M X1 H2. lia.
      * pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) A) as M. clear - M X2 H1. lia.
  - pose proof (dk_rb c Hc) as (R1 & _). clear - G8 G6 R1 Hr X1 X2 Hc. unfold rinfo, RIS_of, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). clear - G8 R1 R4 Hr X1 X2. unfold kUserCap, K_HIGH_SHADOW_hi, SHB in *. lia.
  - assert (c <> c') by (intros ->; exact (HDc Hc0)). pose proof (dk_regions c c' Hc Hc' H) as Rg. pose proof (dk_auser c Hc) as (U1 & U2).
    destruct Rg as [A|A].
    + pose proof (dk_shad_mono (rb SB c + 2 ^ 32) (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) ltac:(lia)) as M. clear - M X2 H1. lia.
    + pose proof (dk_shad_mono (rb SB c' + 2 ^ 32) (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) ltac:(lia)) as M. clear - M X1 H2. lia.
  - pose proof (dk_map k s Hk) as (_ & _ & _ & M4 & _). clear - M4 G8 Q1 Hr X1 X2. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & M5 & _ & _ & M8 & _).
    assert (Ap : s_mb s + smsz (s_n s) <= rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c'))) \/ rb SB c' + 2 ^ 32 <= s_mb s)
      by (clear - M5 Q1 Q2 G7 U1'; lia).
    destruct Ap as [A|A].
    + pose proof (dk_shad_mono (s_mb s + smsz (s_n s)) (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) A) as M. clear - M X2 H1. lia.
    + pose proof (dk_shad_mono (rb SB c' + 2 ^ 32) (s_mb s) A) as M. clear - M X1 H2. lia.
  - clear - Hzlo G1 Hr X1. lia.
Qed.

Lemma dk_shad_app_hw : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= PRB \/ PRB + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k DS -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros lo hi a n H0 H47 Hoff HDSo H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  assert (Hr : SHB <= a /\ a + n <= 2 ^ 44 + SHB).
  { clear - H0 H47 H1 H2. unfold shad in *. pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)).
    assert (hi / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
  zdestr Z.
  - clear - Hr X1 X2 X3 X4. unfold SHB, SEGTOP_A in *. lia.
  - clear - T4 Hr X1 X2 X3 X4. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & _). clear - G8 S1 Hr X1 X2. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _ & _ & _ & S6).
    assert (Ap : hi <= p_abeg SB c i \/ p_abeg SB c i + ClassSize c <= lo) by (clear - Hoff S1 S2 G7; lia).
    destruct Ap as [A|A].
    + pose proof (dk_shad_mono hi (p_abeg SB c i) A) as M. clear - M X1 H2. lia.
    + pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) lo A) as M. clear - M X2 H1. lia.
  - pose proof (dk_rb c Hc) as (R1' & _). clear - G8 G6 R1' Hr X1 X2 Hc. unfold rinfo, RIS_of, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_rb c Hc) as (R1' & R2' & R3' & R4'). clear - G8 R1' R4' Hr X1 X2. unfold kUserCap, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_auser c Hc) as (U1 & U2). pose proof (dk_rb c Hc) as (R1' & R2' & R3' & R4').
    assert (Ap : hi <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))) \/ rb SB c + 2 ^ 32 <= lo) by (clear - Hoff R1' R2' G7 U1; lia).
    destruct Ap as [A|A].
    + pose proof (dk_shad_mono hi (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) A) as M. clear - M X1 H2. lia.
    + pose proof (dk_shad_mono (rb SB c + 2 ^ 32) lo A) as M. clear - M X2 H1. lia.
  - pose proof (dk_map k s Hk) as (_ & _ & _ & M4 & _). clear - M4 G8 Hr X1 X2. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - destruct (HDSo k s Hk Hk0) as [A|A].
    + pose proof (dk_shad_mono hi (s_mb s) A) as M. clear - M X1 H2. lia.
    + pose proof (dk_shad_mono (s_mb s + smsz (s_n s)) lo A) as M. clear - M X2 H1. lia.
  - clear - Hzlo G1 Hr X1. lia.
Qed.

Lemma dk_secmap_hw : forall k' s' a n, nth_error (sec Σ) k' = Some s' -> ~ In k' DS -> s_mb s' <= a -> a + n <= s_mb s' + smsz (s_n s') ->
  disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo.
  intros k' s' a n Hk' HDk H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  pose proof (dk_map k' s' Hk') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  zdestr Z.
  - clear - Q3 X1 X2 X3 X4 H1 H2. unfold SEGTOP_A in *. lia.
  - clear - Q6 X1 X2 X3 X4 H1 H2. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). clear - Q5 S1 S2 G7 X1 X2 H1 H2. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) (SB + 2 ^ 37) S2).
    pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)). pose proof (dk_shad_mono PRB (p_abeg SB c i) S1). pose proof (dk_shad_rng PRB ltac:(lia)).
    clear - Q4 X1 X2 H1 H2 H H0 H3 H4. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & _). clear - Q5 R1 R2 X1 X2 H1 H2 Hc G6 G7. unfold rinfo, RIS_of, rb in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). clear - Q5 R1 R2 R3 R4 X1 X2 H1 H2 G7. unfold kUserCap, kFaCap in *. lia.
  - pose proof (dk_auser c Hc) as (U1 & U2). pose proof (dk_rb c Hc) as (R1 & R2 & _).
    pose proof (dk_shad_rng (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) ltac:(unfold kUserCap in *; lia)).
    pose proof (dk_shad_rng (rb SB c + 2 ^ 32) ltac:(lia)).
    clear - Q4 X1 X2 H1 H2 H H0. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - assert (k <> k') by (intros ->; exact (HDk Hk0)). pose proof (Q9 k s Hk H) as A. clear - A X1 X2 H1 H2. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & _).
    pose proof (dk_shad_rng (s_mb s) ltac:(lia)). pose proof (dk_shad_rng (s_mb s + smsz (s_n s)) ltac:(lia)).
    clear - Q4 X1 X2 H1 H2 H H0. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - clear - Hzlo Q2 X1 H2. lia.
Qed.

Lemma dk_stack_hw : forall a n, zhi <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.
Proof using HW HG HD HDSH HDC HIZ HTZ Hzlo Hzlh.
  intros a n H1 H2. apply dk_all. intros iv Hz0. pose proof (zone_cases iv Hz0) as Z. clear Hz0.
  pose proof dk_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof dk_T as (T1 & T2 & T3 & T4 & T5).
  assert (HA : l_ACEIL L <= a) by (clear - Hzlo Hzlh H1; lia).
  zdestr Z.
  - clear - HA G1 X1 X2 X3 X4. unfold SEGTOP_A, SHB in *. lia.
  - clear - HA T2 X1 X2 X3 X4. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). clear - HA S2 G4 G7 X2. lia.
  - pose proof (dk_slot_in c i st Hc Hst) as (S1 & S2 & _). pose proof (dk_shad_mono (p_abeg SB c i + ClassSize c) (SB + 2 ^ 37) S2).
    pose proof (dk_shad_rng (SB + 2 ^ 37) ltac:(lia)). clear - HA G1 X2 H H0. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & _). clear - HA G4 G6 G7 X2 Hc. unfold rinfo, RIS_of in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & R3 & R4). clear - HA G4 G7 R2 R3 X2. unfold kFaCap in *. lia.
  - pose proof (dk_rb c Hc) as (R1 & R2 & _). pose proof (dk_shad_rng (rb SB c + 2 ^ 32) ltac:(lia)). clear - HA G1 X2 H. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _). clear - HA M2 X2. lia.
  - pose proof (dk_map k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & _). pose proof (dk_shad_rng (s_mb s + smsz (s_n s)) ltac:(lia)).
    clear - HA G1 X2 H. lia.
  - clear - X2 H1. lia.
Qed.

End W.
End DKit.

End GWIN.
