(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SoftFloat FmtFp FmtFpPre FmtFpProps SoftFloatProps FmtFpDig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_of_u32 f128_of_i32.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

Definition NB : Z := 1000000000.

Definition W9 (b : list Z) : Prop := forall i, 0 <= znth b i < NB.
Definition zeros_below (b : list Z) (a : Z) : Prop := forall k, k < a -> znth b k = 0.
Definition zeros_from (b : list Z) (z : Z) : Prop := forall k, z <= k -> znth b k = 0.

Lemma W9_W32 : forall b, W9 b -> W32L b.
Proof. intros b H i. pose proof (H i). unfold NB in *. lia. Qed.
Lemma W9_zupd : forall b i v, W9 b -> 0 <= v < NB -> W9 (zupd b i v).
Proof.
  intros b i v H Hv j. destruct (Z.eq_dec i j) as [->|].
  - destruct (Z.lt_ge_cases j 0). { rewrite znth_neg by lia. unfold NB; lia. }
    destruct (Z.lt_ge_cases j (zlength b)). { rewrite znth_zupd_eq by lia. lia. }
    rewrite znth_ge by (rewrite zlength_zupd; lia). unfold NB; lia.
  - rewrite znth_zupd_neq by lia. apply H.
Qed.
Lemma W9_zrepeat : forall n, W9 (zrepeat 0 n).
Proof. intros n i. rewrite znth_zrepeat. unfold NB. destruct (_ && _); lia. Qed.

Lemma strip_spec : forall big a z, z - a <= 129 -> a < z -> znth big a <> 0 ->
  exists z', fmt_fp_strip BIG_FUEL big a z = Some z' /\ a < z' <= z /\
    (forall i, z' <= i < z -> znth big i = 0) /\ znth big (z' - 1) <> 0.
Proof.
  intros big a z Hz Haz NZ. rewrite fmt_fp_strip_eq.
  destruct (wloop_total (fun z0 => (a <? z0) && (znth big (z0 - 1) =? 0)) fmt_fp_strip_body
             (fun z' => a < z' <= z /\ forall i, z' <= i < z -> znth big i = 0) (fun z' => Z.max 0 (z' - a)))
    with (fuel := BIG_FUEL) (s := z) as [z' (E & [Q1 Q2] & C)].
  - intros z1 [R1 R2] C1. apply andb_prop in C1. destruct C1 as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2. unfold fmt_fp_strip_body.
    assert (z1 - 1 <> a) by (intros X; rewrite X in C2; exact (NZ C2)).
    split; [|lia]. split; [lia|]. intros i Hi. destruct (Z.eq_dec i (z1 - 1)) as [->|]; [exact C2|]. apply R2. lia.
  - split; [lia|]. intros; lia.
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - exists z'. split; [exact E|]. split; [exact Q1|]. split; [exact Q2|].
    apply Bool.andb_false_iff in C. destruct C as [C|C]. { apply Z.ltb_ge in C. lia. } apply Z.eqb_neq in C. exact C.
Qed.

Lemma up_inner_spec : forall sh a big z, 1 <= sh <= 29 -> a < z -> z - a <= 128 -> W9 big -> zlength big = 128 -> 0 <= a < 128 ->
  exists big' d' c', fmt_fp_up_inner sh BIG_FUEL a (big, z - 1, 0) = Some (big', d', c') /\
    W9 big' /\ 0 <= c' < NB /\ zlength big' = 128 /\ d' = a - 1 /\
    (forall i, (i < a \/ z <= i) -> znth big' i = znth big i) /\
    exists cin, 0 <= cin < NB /\ let x := znth big a * 2 ^ sh + cin in
      c' = x / NB /\ znth big' a = x mod NB.
Proof.
  intros sh a big z Hsh Haz Hza WB LB Ha. rewrite fmt_fp_up_inner_eq.
  assert (P2 : 2 <= 2 ^ sh <= 2^29). { split. { change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. } apply Z.pow_le_mono_r; lia. }
  destruct (wloop_total (fun s : list Z * Z * Z => let '(_, d0, _) := s in a <=? d0) (fmt_fp_up_inner_body sh)
             (fun s => let '(b, d1, c1) := s in W9 b /\ 0 <= c1 < NB /\ zlength b = 128 /\ a - 1 <= d1 <= z - 1 /\
                 (forall i, (i <= d1 \/ z <= i) -> znth b i = znth big i) /\
                 (d1 < a -> exists cin, 0 <= cin < NB /\ let x := znth big a * 2 ^ sh + cin in
                      c1 = x / NB /\ znth b a = x mod NB))
             (fun s => let '(_, d1, _) := s in Z.max 0 (d1 - a + 1)))
    with (fuel := BIG_FUEL) (s := (big, z - 1, 0)) as [[[b' d'] c'] (E & (W' & C' & L' & D' & U' & X') & CND)].
  - intros [[b d1] c1] (W1 & C1 & L1 & D1 & U1 & _) CC. apply Z.leb_le in CC. unfold fmt_fp_up_inner_body.
    pose proof (W1 d1) as Wd. rewrite Z.shiftl_mul_pow2 by lia.
    set (x := znth b d1 * 2 ^ sh + c1).
    assert (XR : 0 <= x <= (NB - 1) * 2^29 + NB) by (subst x; unfold NB in *; nia).
    assert (XD : 0 <= x / NB < NB). { unfold NB in *. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    change 1000000000 with NB.
    split; [| lia]. split. { apply W9_zupd; [exact W1|]. pose proof (Z.mod_pos_bound x NB ltac:(unfold NB; lia)). lia. }
    split; [rewrite u32_id by (unfold NB in *; lia); lia|]. split; [now rewrite zlength_zupd|]. split; [lia|].
    split. { intros i Hi. rewrite znth_zupd_neq by lia. apply U1. lia. }
    intros LT. assert (d1 = a) by lia. subst d1. exists c1. split; [lia|]. cbv zeta.
    rewrite u32_id by (unfold NB in *; lia). subst x. rewrite <- (U1 a ltac:(lia)).
    split; [reflexivity|]. apply znth_zupd_eq. rewrite L1. lia.
  - split; [exact WB|]. split; [unfold NB; lia|]. split; [exact LB|]. split; [lia|]. split; [intros; reflexivity| intros; lia].
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. apply Z.leb_gt in CND. eexists _, _, _. split; [reflexivity|]. split; [exact W'|]. split; [exact C'|]. split; [exact L'|].
    split; [lia|]. split. { intros i Hi. apply U'. lia. } apply X'. lia.
Qed.

Definition upm (e2 : Z) : Z := Z.max 0 ((e2 + 28) / 29).
Lemma upm_pos : forall e2, 0 < e2 -> 1 <= upm e2.
Proof. intros. unfold upm. assert (1 <= (e2 + 28) / 29) by (apply Z.div_le_lower_bound; lia). lia. Qed.
Lemma upm_step : forall e2, 0 < e2 -> upm (e2 - Z.min 29 e2) = upm e2 - 1.
Proof.
  intros e2 H. unfold upm. destruct (Z.le_gt_cases 29 e2).
  - rewrite Z.min_l by lia. replace (e2 - 29 + 28) with ((e2 + 28) + (-1) * 29) by lia. rewrite Z.div_add by lia.
    assert (1 <= (e2 + 28) / 29) by (apply Z.div_le_lower_bound; lia). lia.
  - rewrite Z.min_r by lia. replace (e2 - e2 + 28) with 28 by lia. change (28 / 29) with 0.
    assert ((e2 + 28) / 29 = 1). { symmetry. apply Z.div_unique with (r := e2 - 1); lia. } lia.
Qed.

Definition UPI (z0 : Z) (s : list Z * Z * Z * Z) : Prop :=
  let '(big, a, z, e2) := s in
  W9 big /\ zlength big = 128 /\ 0 <= a < z /\ z <= z0 /\ a <= 122 /\ 122 - a + upm e2 <= 36 /\ 0 <= e2 <= 1024 /\
  znth big a <> 0 /\ zeros_below big a /\ zeros_from big z.

Lemma up_body_spec : forall z0 big a z e2, z0 <= 126 -> UPI z0 (big, a, z, e2) -> 0 < e2 ->
  exists s', fmt_fp_up_body (big, a, z, e2) = Some s' /\ UPI z0 s' /\
    (let '(_, _, _, e2') := s' in e2' = e2 - Z.min 29 e2).
Proof.
  intros z0 big a z e2 HZ0 (WB & LB & AZ & ZZ & AR & RA & E2 & NZ & ZB & ZF) C1.
  pose proof (upm_pos e2 C1) as UP1. pose proof (upm_step e2 C1) as UPS.
  unfold fmt_fp_up_body.
  destruct (up_inner_spec (Z.min 29 e2) a big z ltac:(lia) ltac:(lia) ltac:(lia) WB LB ltac:(lia)) as [b1 [d1 [c1 (E1 & W1 & C1r & L1 & D1 & U1 & [cin (Hcin & X1 & X2)])]]].
  rewrite E1.
  assert (P2 : 2 <= 2 ^ Z.min 29 e2). { change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. }
  pose proof (WB a) as Wa.
  set (ab := if negb (c1 =? 0) then (a - 1, zupd b1 (a - 1) c1) else (a, b1)).
  assert (AB : exists a2 b2, ab = (a2, b2) /\ W9 b2 /\ zlength b2 = 128 /\ a - 1 <= a2 <= a /\ 0 <= a2 /\ znth b2 a2 <> 0 /\
               zeros_below b2 a2 /\ zeros_from b2 z).
  { subst ab. destruct (Z.eqb_spec c1 0) as [C0|C0]; cbn [negb].
    - eexists _, _. split; [reflexivity|]. split; [exact W1|]. split; [exact L1|]. split; [lia|]. split; [lia|].
      split. { rewrite X2. rewrite C0 in X1. symmetry in X1.
        assert (znth big a * 2 ^ Z.min 29 e2 + cin < NB). { apply Z.div_small_iff in X1; unfold NB in *; lia. }
        rewrite Z.mod_small by lia. nia. }
      split. { intros k Hk. rewrite U1 by lia. apply ZB. lia. }
      intros k Hk. rewrite U1 by lia. apply ZF. lia.
    - assert (1 <= a). { destruct (Z.eq_dec a 0) as [A0|]; [|lia]. exfalso.
          lia. }
      eexists _, _. split; [reflexivity|]. split; [apply W9_zupd; [exact W1| lia]|]. split; [now rewrite zlength_zupd|]. split; [lia|]. split; [lia|].
      split. { rewrite znth_zupd_eq by (rewrite L1; lia). exact C0. }
      split. { intros k Hk. rewrite znth_zupd_neq by lia. rewrite U1 by lia. apply ZB. lia. }
      intros k Hk. rewrite znth_zupd_neq by lia. rewrite U1 by lia. apply ZF. lia. }
  destruct AB as [a2 [b2 (-> & W2 & L2 & A2 & A2p & N2 & ZB2 & ZF2)]].
  destruct (strip_spec b2 a2 z ltac:(lia) ltac:(lia) N2) as [z2 (Es & Z2 & Z2z & _)]. rewrite Es.
  eexists. split; [reflexivity|]. split.
  + unfold UPI. split; [exact W2|]. split; [exact L2|]. split; [lia|]. split; [lia|]. split; [lia|]. rewrite UPS. split; [lia|]. split; [lia|].
    split; [exact N2|]. split; [exact ZB2|].
    intros k Hk. destruct (Z.lt_ge_cases k z); [apply Z2z; lia| apply ZF2; lia].
  + reflexivity.
Qed.

Lemma up_spec : forall z0 s, z0 <= 126 -> UPI z0 s ->
  exists s', fmt_fp_up UP_FUEL s = Some s' /\ UPI z0 s' /\ (let '(_, _, _, e2) := s' in e2 = 0).
Proof.
  intros z0 s HZ0 HI. rewrite fmt_fp_up_eq.
  destruct (owloop_total (fun s : list Z * Z * Z * Z => let '(_, _, _, e2) := s in 0 <? e2) fmt_fp_up_body (UPI z0)
             (fun s => let '(_, _, _, e2) := s in upm e2)) with (fuel := UP_FUEL) (s := s) as [s' (E & HI' & C)].
  - intros [[[big a] z] e2] HI1 C1. apply Z.ltb_lt in C1.
    destruct (up_body_spec z0 big a z e2 HZ0 HI1 C1) as [s' (E & HI2 & He)].
    exists s'. split; [exact E|]. split; [exact HI2|]. destruct s' as [[[? ?] ?] e2']. rewrite He, upm_step by lia.
    destruct HI1 as (_ & _ & _ & _ & _ & RA & _). pose proof (upm_pos e2 C1). lia.
  - exact HI.
  - destruct s as [[[big a] z] e2]. destruct HI as (_ & _ & _ & _ & _ & RA & E2 & _). unfold upm in *. unfold UP_FUEL. change (Z.of_nat 40) with 40.
    assert ((e2 + 28) / 29 <= 37) by (apply Z.div_le_upper_bound; lia). lia.
  - exists s'. split; [exact E|]. split; [exact HI'|]. destruct s' as [[[? ?] ?] e2']. apply Z.ltb_ge in C.
    destruct HI' as (_ & _ & _ & _ & _ & _ & E2 & _). lia.
Qed.

Lemma dn_word_bound : forall sh w rm, 1 <= sh <= 9 -> 0 <= w < NB -> 0 <= rm < 2^sh ->
  0 <= Z.shiftr w sh + Z.shiftr NB sh * rm < NB.
Proof.
  intros sh w rm Hsh Hw Hrm. rewrite !Z.shiftr_div_pow2 by lia. unfold NB in *.
  assert (C : sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7 \/ sh = 8 \/ sh = 9) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]; cbn -[Z.add Z.mul Z.div Z.le Z.lt] in *; dnia.
Qed.

Lemma sh_ones : forall sh, 0 <= sh -> Z.shiftl 1 sh - 1 = Z.ones sh.
Proof. intros. unfold Z.ones. rewrite Z.shiftl_1_l. lia. Qed.

Section DnInner.
  Variables (sh a z : Z) (big : list Z).
  Let v := znth big a.
  Hypothesis Hsh : 1 <= sh <= 9.
  Hypothesis Haz : 0 <= a < z.
  Hypothesis Hz : z <= 128.
  Hypothesis WB : W9 big.
  Hypothesis HL : zlength big = 128.
  Hypothesis Hv : v <> 0.

  Definition DNK (s : list Z * Z * Z) : Prop :=
    let '(b, d, c) := s in
    W9 b /\ zlength b = 128 /\ (exists rm, 0 <= rm < 2^sh /\ c = Z.shiftr NB sh * rm) /\ a <= d /\
    (forall i, (i < a \/ d <= i) -> znth b i = znth big i) /\
    (d = a -> c = 0) /\
    (a < d -> znth b a = Z.shiftr v sh /\
              (Z.shiftr v sh = 0 -> (d = a + 1 -> 1 <= c) /\ (a + 1 < d -> 1 <= znth b (a + 1)))).

  Lemma dn_inner_spec :
    exists b c, fmt_fp_dn_inner sh BIG_FUEL z (big, a, 0) = Some (b, z, c) /\ DNK (b, z, c).
  Proof.
    assert (P2 : 2 <= 2 ^ sh <= 512). { split. { change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. } change 512 with (2^9). apply Z.pow_le_mono_r; lia. }
    assert (Q1 : 1 <= Z.shiftr NB sh). { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_le_lower_bound; unfold NB; lia. }
    rewrite fmt_fp_dn_inner_eq.
    destruct (wloop_total (fun s : list Z * Z * Z => let '(_, d, _) := s in d <? z) (fmt_fp_dn_inner_body sh)
               (fun s => DNK s /\ (let '(_, d, _) := s in d <= z))
               (fun s => let '(_, d, _) := s in z - d)) with (fuel := BIG_FUEL) (s := (big, a, 0)) as [[[b d] c] (E & [HI Dz] & C)].
    - intros [[b d] c] [(W1 & L1 & [rm0 [Hrm0 Hc]] & AD & U1 & D0 & D1) Dz] CC. apply Z.ltb_lt in CC.
      unfold fmt_fp_dn_inner_body.
      pose proof (W1 d) as Wd.
      rewrite sh_ones, Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (znth b d) (2^sh) ltac:(lia)) as RR.
      pose proof (dn_word_bound sh (znth b d) rm0 Hsh Wd Hrm0) as NB1. rewrite <- Hc in NB1.
      rewrite (u32_id (Z.shiftr (znth b d) sh + c)) by (unfold NB in *; lia).
      pose proof (dn_word_bound sh 0 (znth b d mod 2^sh) Hsh ltac:(unfold NB; lia) RR) as NB2.
      rewrite Z.shiftr_0_l, Z.add_0_l in NB2.
      change 1000000000 with NB. rewrite (u32_id _) by (unfold NB in *; lia).
      split; [| lia]. split; [| lia].
      unfold DNK. split; [apply W9_zupd; [exact W1| lia]|]. split; [now rewrite zlength_zupd|].
      split; [exists (znth b d mod 2^sh); split; [lia| reflexivity]|]. split; [lia|].
      split. { intros i Hi. rewrite znth_zupd_neq by lia. apply U1. lia. }
      split; [intros; lia|]. intros _.
      assert (SR : 0 <= Z.shiftr (znth b d) sh <= znth b d). { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
      destruct (Z.eq_dec d a) as [->|NE].
      + rewrite (D0 eq_refl). rewrite Z.add_0_r.
        split. { rewrite znth_zupd_eq by (rewrite L1; lia). subst v. rewrite (U1 a) by lia. reflexivity. }
        intros VS. split; [| intros; lia]. intros _.
        subst v. rewrite <- (U1 a) in VS, Hv by lia.
        rewrite Z.shiftr_div_pow2 in VS by lia. apply Z.div_small_iff in VS; [| lia].
        rewrite Z.mod_small by lia. nia.
      + destruct (D1 ltac:(lia)) as [BA BS]. split. { rewrite znth_zupd_neq by lia. exact BA. }
        intros VS. destruct (BS VS) as [B1 B2]. split; [intros; lia|]. intros LT.
        destruct (Z.eq_dec d (a + 1)) as [->|NE2].
        * rewrite znth_zupd_eq by (rewrite L1; lia). specialize (B1 eq_refl). lia.
        * rewrite znth_zupd_neq by lia. apply B2. lia.
    - split; [| lia]. unfold DNK. split; [exact WB|]. split; [exact HL|]. split; [exists 0; split; [lia|lia]|]. split; [lia|].
      split; [intros; reflexivity|]. split; [auto| intros; lia].
    - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
    - exists b, c. apply Z.ltb_ge in C. assert (d = z) by lia. subst d. split; [exact E| exact HI].
  Qed.
End DnInner.

Definition dnm (e2 : Z) : Z := Z.max 0 ((- e2 + 8) / 9).
Lemma dnm_pos : forall e2, e2 < 0 -> 1 <= dnm e2.
Proof. intros. unfold dnm. assert (1 <= (- e2 + 8) / 9) by (apply Z.div_le_lower_bound; lia). lia. Qed.
Lemma dnm_step : forall e2, e2 < 0 -> dnm (e2 + Z.min 9 (- e2)) = dnm e2 - 1.
Proof.
  intros e2 H. unfold dnm. destruct (Z.le_gt_cases 9 (- e2)).
  - rewrite Z.min_l by lia. replace (- (e2 + 9) + 8) with ((- e2 + 8) + (-1) * 9) by lia. rewrite Z.div_add by lia.
    assert (1 <= (- e2 + 8) / 9) by (apply Z.div_le_lower_bound; lia). lia.
  - rewrite Z.min_r by lia. replace (- (e2 + - e2) + 8) with 8 by lia. change (8 / 9) with 0.
    assert ((- e2 + 8) / 9 = 1). { symmetry. apply Z.div_unique with (r := - e2 - 1); lia. } lia.
Qed.

Definition DNI (s : list Z * Z * Z * Z) : Prop :=
  let '(big, a, z, e2) := s in
  W9 big /\ zlength big = 128 /\ 0 <= a < z /\ znth big a <> 0 /\ zeros_below big a /\
  z + dnm e2 <= 127 /\ -1102 <= e2 <= 0 /\ znth big 0 < 2^29.

Lemma dn_body_spec : forall p t big a z e2, 0 <= p -> Z.lor t 32 <> CHR_f -> DNI (big, a, z, e2) -> e2 < 0 ->
  exists s', fmt_fp_dn_body p t 0 (big, a, z, e2) = Some s' /\ DNI s' /\
    (let '(_, _, _, e2') := s' in e2' = e2 + Z.min 9 (- e2)).
Proof.
  intros p t big a z e2 Hp Ht (WB & LB & AZ & NZ & ZB & ZM & E2 & B0) C1.
  pose proof (dnm_pos e2 C1) as DP. pose proof (dnm_step e2 C1) as DS.
  unfold fmt_fp_dn_body.
  set (sh := Z.min 9 (- e2)). assert (Hsh : 1 <= sh <= 9) by (subst sh; lia).
  change LDBL_MANT_DIG with 113. change (113 / 3) with 37.
  pose proof (u32_range (p + 37 + 8)) as UR.
  set (need := 1 + u32 (p + 37 + 8) / 9).
  assert (Hneed : 1 <= need) by (subst need; pose proof (Z.div_pos (u32 (p + 37 + 8)) 9); lia).
  destruct (dn_inner_spec sh a z big Hsh AZ ltac:(lia) WB LB NZ) as [b [c (E1 & (W1 & L1 & [rm [Hrm Hc]] & AD & U1 & D0 & D1))]].
  rewrite E1.
  destruct (D1 ltac:(lia)) as [BA BS].
  replace (Z.lor t 32 =? CHR_f) with false by (symmetry; apply Z.eqb_neq; exact Ht).
  assert (P2 : 2 <= 2 ^ sh). { change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. }
  assert (Hc2 : 0 <= c < NB). { pose proof (dn_word_bound sh 0 rm Hsh ltac:(unfold NB; lia) Hrm) as X. rewrite Z.shiftr_0_l in X. lia. }
  assert (B0' : znth b 0 < 2^29).
  { destruct (Z.eq_dec a 0) as [A0|A0].
    - rewrite A0 in BA. rewrite BA. rewrite Z.shiftr_div_pow2 by lia.
      pose proof (WB 0). apply Z.div_lt_upper_bound; [lia|]. nia.
    - rewrite U1 by lia. exact B0. }
  set (a' := if znth b a =? 0 then a + 1 else a).
  assert (A' : (znth b a <> 0 /\ a' = a) \/ (znth b a = 0 /\ a' = a + 1)).
  { subst a'. destruct (Z.eqb_spec (znth b a) 0); [right| left]; auto. }
  clearbody a'.
  assert (ZB' : zeros_below b a').
  { intros k Hk. destruct A' as [[N ->]|[Zr ->]].
    - rewrite U1 by lia. apply ZB. lia.
    - destruct (Z.eq_dec k a) as [->|]; [exact Zr|]. rewrite U1 by lia. apply ZB. lia. }
  set (bz := if negb (c =? 0) then (zupd b z c, z + 1) else (b, z)).
  assert (BZ : exists b1 z1, bz = (b1, z1) /\ W9 b1 /\ zlength b1 = 128 /\ z <= z1 <= z + 1 /\
               a' < z1 /\ znth b1 a' <> 0 /\ a <= a' <= a + 1 /\ zeros_below b1 a' /\ znth b1 0 < 2^29).
  { subst bz. destruct (Z.eqb_spec c 0) as [C0|C0]; cbn [negb].
    - eexists _, _. split; [reflexivity|]. split; [exact W1|]. split; [exact L1|]. split; [lia|].
      destruct A' as [[N ->]|[Zr ->]]. { split; [lia|]. split; [exact N|]. split; [lia|]. split; [exact ZB'| exact B0']. }
      rewrite BA in Zr. destruct (BS Zr) as [B1 B2].
      destruct (Z.eq_dec z (a + 1)) as [E|NE]. { exfalso. specialize (B1 E). lia. }
      split; [lia|]. split; [specialize (B2 ltac:(lia)); lia|]. split; [lia|]. split; [exact ZB'| exact B0'].
    - eexists _, _. split; [reflexivity|]. split; [apply W9_zupd; [exact W1| lia]|]. split; [rewrite zlength_zupd; exact L1|]. split; [lia|].
      destruct A' as [[N ->]|[Zr ->]].
      { split; [lia|]. split; [rewrite znth_zupd_neq by lia; exact N|]. split; [lia|].
        split; [intros k Hk; rewrite znth_zupd_neq by lia; apply ZB'; lia|]. rewrite znth_zupd_neq by lia. exact B0'. }
      rewrite BA in Zr. destruct (BS Zr) as [B1 B2].
      split; [lia|]. split.
      { destruct (Z.eq_dec z (a + 1)) as [->|NE].
        - rewrite znth_zupd_eq by (rewrite L1; lia). exact C0.
        - rewrite znth_zupd_neq by lia. specialize (B2 ltac:(lia)). lia. }
      split; [lia|]. split; [intros k Hk; rewrite znth_zupd_neq by lia; apply ZB'; lia|]. rewrite znth_zupd_neq by lia. exact B0'. }
  destruct BZ as [b1 [z1 (-> & W2 & L2 & Z1 & AZ1 & N1 & AA & ZB1 & B01)]].
  eexists. split; [reflexivity|]. split; [| reflexivity].
  unfold DNI. split; [exact W2|]. split; [exact L2|]. split.
  { destruct (need <? z1 - a'); lia. }
  split; [exact N1|]. split; [exact ZB1|]. split.
  { replace (e2 + sh) with (e2 + Z.min 9 (- e2)) by reflexivity. rewrite DS. destruct (need <? z1 - a') eqn:CN; [apply Z.ltb_lt in CN|]; lia. }
  split; [lia| exact B01].
Qed.

Fixpoint dn_iter (n : nat) (p t r : Z) (s : list Z * Z * Z * Z) {struct n} : option (list Z * Z * Z * Z) :=
  match n with
  | O => Some s
  | S n' => let '(big, a, z, e2) := s in
            if e2 <? 0 then match fmt_fp_dn_body p t r s with Some s' => dn_iter n' p t r s' | None => None end
            else None
  end.

Lemma dn_iter_DNI : forall p t n s s', 0 <= p -> Z.lor t 32 <> CHR_f -> DNI s -> dn_iter n p t 0 s = Some s' -> DNI s'.
Proof.
  intros p t n. induction n as [|n IH]; intros s s' Hp Ht HI E.
  - cbn in E. inversion E. subst. exact HI.
  - cbn [dn_iter] in E. destruct s as [[[big a] z] e2]. destruct (Z.ltb_spec e2 0); [|discriminate E].
    destruct (dn_body_spec p t big a z e2 Hp Ht HI ltac:(lia)) as [s1 (E1 & HI1 & _)]. rewrite E1 in E.
    eapply IH; eauto.
Qed.

Lemma dn_spec : forall p t s, 0 <= p -> Z.lor t 32 <> CHR_f -> DNI s ->
  exists s', fmt_fp_dn DN_FUEL p t 0 s = Some s' /\ DNI s' /\ (let '(_, _, _, e2) := s' in e2 = 0).
Proof.
  intros p t s Hp Ht HI. rewrite fmt_fp_dn_eq.
  destruct (owloop_total (fun s : list Z * Z * Z * Z => let '(_, _, _, e2) := s in e2 <? 0) (fmt_fp_dn_body p t 0) DNI
             (fun s => let '(_, _, _, e2) := s in dnm e2)) with (fuel := DN_FUEL) (s := s) as [s' (E & HI' & C)].
  - intros [[[big a] z] e2] HI1 C1. apply Z.ltb_lt in C1.
    destruct (dn_body_spec p t big a z e2 Hp Ht HI1 C1) as [s1 (E1 & HI2 & He)].
    exists s1. split; [exact E1|]. split; [exact HI2|]. destruct s1 as [[[? ?] ?] e2']. rewrite He, dnm_step by lia.
    pose proof (dnm_pos e2 C1). unfold dnm in *. lia.
  - exact HI.
  - destruct s as [[[big a] z] e2]. destruct HI as (_ & _ & AZ & _ & _ & ZM & E2 & _). unfold dnm in *. unfold DN_FUEL. change (Z.of_nat 130) with 130.
    assert ((- e2 + 8) / 9 <= 124) by (apply Z.div_le_upper_bound; lia). lia.
  - exists s'. split; [exact E|]. split; [exact HI'|]. destruct s' as [[[? ?] ?] e2']. apply Z.ltb_ge in C.
    destruct HI' as (_ & _ & _ & _ & _ & _ & E2 & _). lia.
Qed.

Lemma upd_nat_same : forall l i, upd_nat l i (nth i l 0) = l.
Proof. induction l as [|h l IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma zupd_same : forall l i, zupd l i (znth l i) = l.
Proof.
  intros l i. unfold zupd, znth. destruct (Z.ltb_spec i 0); [reflexivity|]. apply upd_nat_same.
Qed.

Definition POST (r0 : Z) (big : list Z) (a z : Z) : Prop :=
  W9 big /\ zlength big = 128 /\ 0 <= a < z /\ z <= 127 /\ znth big a <> 0 /\ zeros_below big a /\
  ((r0 = 0 /\ znth big 0 < 2^29) \/ (r0 = 122 /\ 86 <= a <= 122 /\ zeros_from big z)).

Theorem fmt_loops : forall d p t, dfin d -> 0 <= p -> Z.lor t 32 <> CHR_f ->
  let y1 := strip_sign (f128_of_d d) in
  exists (nz : bool) fr e0 y2,
    1 < fpclassifyl y1 /\ frexpl FREXPL_FUEL y1 0 = Some (fr, e0) /\ f128_mul fr (f128_of_i32 2) = y2 /\
    negb (f128_le y2 F128_ZERO =? 0) = nz /\
    let e1 := if nz then e0 - 1 else e0 in
    let y := if nz then f128_mul y2 (f128_of_d D_0x1p28) else y2 in
    let e2 := if nz then e1 - 28 else e1 in
    let r0 := if e2 <? 0 then 0 else 122 in
    -1102 <= e2 <= 995 /\
    exists big z, fmt_fp_dig DIG_FUEL (zrepeat 0 128, r0, y) = Some (big, z, f128_pack 0 0 0) /\ r0 + 1 <= z <= r0 + 4 /\
      W9 big /\ zlength big = 128 /\ (forall i, ~ (r0 <= i < z) -> znth big i = 0) /\
      (nz = true -> 2^28 <= znth big r0 < 2^29) /\
      (nz = false -> e2 = 0 /\ z = 123 /\ big = zrepeat 0 128) /\
      exists s1, fmt_fp_up UP_FUEL (big, r0, z, e2) = Some s1 /\
        (e2 <= 0 -> s1 = (big, r0, z, e2)) /\ (nz = true -> e2 < 0 -> DNI s1) /\
        (0 <= e2 -> exists b1 a1 z1, s1 = (b1, a1, z1, 0)) /\
        exists big2 a2 z2, fmt_fp_dn DN_FUEL p t r0 s1 = Some (big2, a2, z2, 0) /\
          (nz = true -> POST r0 big2 a2 z2) /\ (nz = false -> big2 = zrepeat 0 128 /\ a2 = 122 /\ z2 = 123).
Proof.
  intros d p t Hfin Hp Ht.
  destruct (prologue_ok_finite d Hfin) as [nz [fr [e0 [N0 (C1 & C2 & C3 & C4 & C5 & DIG)]]]].
  cbv zeta in C3, C4, C5. cbv zeta.
  exists nz, fr, e0, (f128_mul fr (f128_of_i32 2)).
  split; [exact C1|]. split; [exact C2|]. split; [reflexivity|]. split; [exact C3|].
  destruct nz.
  -
    destruct (C5 eq_refl) as (He0 & HN0 & EY). rewrite EY.
    set (e2 := e0 - 1 - 28).
    assert (He2 : -1102 <= e2 <= 995) by (subst e2; lia).
    split; [exact He2|].
    set (r0 := if e2 <? 0 then 0 else 122).
    assert (Hr0 : (e2 < 0 /\ r0 = 0) \/ (0 <= e2 /\ r0 = 122)). { subst r0. destruct (Z.ltb_spec e2 0); lia. }
    destruct (DIG DIG_FUEL r0 (zrepeat 0 128)) as [big [z (E & HL & Hz & _ & W0 & Ws & Oth)]].
    { unfold DIG_FUEL. lia. } { lia. } { rewrite zlength_zrepeat; lia. }
    rewrite E. exists big, z. split; [reflexivity|]. split; [exact Hz|].
    assert (WB : W9 big). { intros i. destruct (Z.lt_ge_cases i r0); [|destruct (Z.lt_ge_cases i z)].
      - rewrite Oth by lia. rewrite znth_zrepeat. unfold NB. destruct (_ && _); lia.
      - unfold NB. apply Ws. lia.
      - rewrite Oth by lia. rewrite znth_zrepeat. unfold NB. destruct (_ && _); lia. }
    assert (LB : zlength big = 128). { unfold zlength. rewrite HL. pose proof (zlength_zrepeat 0 128). unfold zlength in H. lia. }
    assert (ZO : forall i, ~ (r0 <= i < z) -> znth big i = 0). { intros i Hi. rewrite Oth by lia. rewrite znth_zrepeat. destruct (_ && _); reflexivity. }
    destruct (W0 eq_refl) as [W0a W0b].
    split; [exact WB|]. split; [exact LB|]. split; [exact ZO|]. split; [intros _; exact W0b|]. split; [intros X; discriminate X|].
    destruct Hr0 as [[Hneg ->]|[Hnn ->]].
    +
      exists (big, 0, z, e2). rewrite fmt_fp_up_eq. unfold UP_FUEL. cbn [owloop].
      replace (0 <? e2) with false by (symmetry; apply Z.ltb_ge; lia).
      split; [reflexivity|]. split; [intros _; reflexivity|].
      assert (HD : DNI (big, 0, z, e2)).
      { unfold DNI. split; [exact WB|]. split; [exact LB|]. split; [lia|]. split; [lia|].
        split; [intros k Hk; apply ZO; lia|]. split; [| lia].
        unfold dnm. assert ((- e2 + 8) / 9 <= 123) by dlia. lia. }
      split; [intros _ _; exact HD|]. split; [intros X; lia|].
      destruct (dn_spec p t (big, 0, z, e2) Hp Ht HD) as [[[[big2 a2] z2] e2'] (E2 & HI2 & He2')]. subst e2'.
      rewrite E2. exists big2, a2, z2. split; [reflexivity|]. split; [| intros X; discriminate X]. intros _.
      destruct HI2 as (W2 & L2 & AZ2 & NZ2 & ZB2 & ZM2 & _ & B02). unfold POST.
      split; [exact W2|]. split; [exact L2|]. split; [exact AZ2|]. split; [unfold dnm in ZM2; change ((- 0 + 8) / 9) with 0 in ZM2; lia|].
      split; [exact NZ2|]. split; [exact ZB2|]. left. split; [reflexivity| exact B02].
    +
      assert (HU : UPI z (big, 122, z, e2)).
      { unfold UPI. split; [exact WB|]. split; [exact LB|]. split; [lia|]. split; [lia|]. split; [lia|].
        split. { unfold upm. assert ((e2 + 28) / 29 <= 35) by dlia. lia. }
        split; [lia|]. split; [lia|]. split; [intros k Hk; apply ZO; lia| intros k Hk; apply ZO; lia]. }
      destruct (up_spec z (big, 122, z, e2) ltac:(lia) HU) as [[[[big1 a1] z1] e21] (E1 & HI1 & He21)]. subst e21.
      rewrite E1. exists (big1, a1, z1, 0). split; [reflexivity|]. split.
      { intros Hle. assert (e2 = 0) by lia. rewrite fmt_fp_up_eq in E1. unfold UP_FUEL in E1. cbn [owloop] in E1.
        replace (0 <? e2) with false in E1 by (symmetry; apply Z.ltb_ge; lia). inversion E1; subst. reflexivity. }
      split; [intros _ X; lia|]. split; [intros _; eexists _, _, _; reflexivity|].
      rewrite fmt_fp_dn_eq. unfold DN_FUEL. cbn [owloop]. change (0 <? 0) with false. cbv iota.
      exists big1, a1, z1. split; [reflexivity|]. split; [| intros X; discriminate X]. intros _.
      destruct HI1 as (W1 & L1 & AZ1 & ZZ1 & AR1 & RA1 & _ & NZ1 & ZB1 & ZF1). unfold POST.
      split; [exact W1|]. split; [exact L1|]. split; [exact AZ1|]. split; [lia|]. split; [exact NZ1|]. split; [exact ZB1|].
      right. split; [reflexivity|]. split; [unfold upm in RA1; change ((0 + 28) / 29) with 0 in RA1; lia| exact ZF1].
  -
    destruct (C4 eq_refl) as [-> EY2]. rewrite EY2.
    change (0 <? 0) with false. cbv iota. change (0 - 28 <? 0) with true. cbv iota.
    split; [lia|].
    rewrite (dig_zero DIG_FUEL (zrepeat 0 128) 122) by (try rewrite zlength_zrepeat; unfold DIG_FUEL; lia).
    replace (zupd (zrepeat 0 128) 122 0) with (zrepeat 0 128).
    2:{ symmetry. etransitivity; [| apply (zupd_same (zrepeat 0 128) 122)]. rewrite znth_zrepeat. reflexivity. }
    exists (zrepeat 0 128), 123. split; [reflexivity|]. split; [lia|]. split; [apply W9_zrepeat|]. split; [apply zlength_zrepeat; lia|].
    split; [intros i _; rewrite znth_zrepeat; destruct (_ && _); reflexivity|]. split; [intros X; discriminate X|]. split; [intros _; repeat split; reflexivity|].
    exists (zrepeat 0 128, 122, 123, 0). rewrite fmt_fp_up_eq. unfold UP_FUEL. cbn [owloop]. change (0 <? 0) with false. cbv iota.
    split; [reflexivity|]. split; [intros _; reflexivity|]. split; [intros X; discriminate X|].
    split; [intros _; eexists _, _, _; reflexivity|].
    rewrite fmt_fp_dn_eq. unfold DN_FUEL. cbn [owloop]. change (0 <? 0) with false. cbv iota.
    exists (zrepeat 0 128), 122, 123. split; [reflexivity|]. split; [intros X; discriminate X|]. intros _. repeat split; reflexivity.
Qed.
