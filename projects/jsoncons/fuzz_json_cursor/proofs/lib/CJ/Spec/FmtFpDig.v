(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool Lia List.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloatProps.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloatProps2.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloatProps3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

Lemma K2_eq : f128_of_i32 2 = f128_pack 0 16384 0.
Proof. vmc_refl. Qed.
Lemma K28_eq : f128_of_d D_0x1p28 = f128_pack 0 16411 0.
Proof. vmc_refl. Qed.
Definition T9 : Z := 1000000000 * 2^83 - 2^112.
Lemma K1E9_eq : f128_of_i32 1000000000 = f128_pack 0 16412 T9.
Proof. vmc_refl. Qed.

Definition nrepr (L N s : Z) : Z := f128_pack 0 (16383 + L - s) (N * 2^(112 - L) - 2^112).

Section Pow.
  Lemma pow2_pos' : forall a, 0 <= a -> 0 < 2^a. Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
  Lemma pow2_mul : forall a b, 0 <= a -> 0 <= b -> 2^a * 2^b = 2^(a+b). Proof. intros. symmetry. apply Z.pow_add_r; lia. Qed.
End Pow.

Lemma nrepr_T : forall L N, 0 <= L <= 112 -> 2^L <= N < 2^(L+1) ->
  0 <= N * 2^(112 - L) - 2^112 < 2^112 /\ 2^112 <= N * 2^(112-L) < 2^113.
Proof.
  intros L N HL HN.
  pose proof (pow2_pos' (112 - L) ltac:(lia)).
  assert (E1 : 2^L * 2^(112 - L) = 2^112) by (rewrite pow2_mul by lia; f_equal; lia).
  assert (E2 : 2^(L+1) * 2^(112 - L) = 2^113) by (rewrite pow2_mul by lia; f_equal; lia).
  nia.
Qed.

Lemma nrepr_packed : forall L N s, 0 <= L <= 112 -> 2^L <= N < 2^(L+1) -> L - 16382 <= s <= L + 16383 ->
  packed 0 (16383 + L - s) (N * 2^(112 - L) - 2^112).
Proof. intros. pose proof (nrepr_T L N H H0). constructor; lia. Qed.

Lemma f128_le_nrepr : forall L N s, 0 <= L <= 112 -> 2^L <= N < 2^(L+1) -> L - 16382 <= s <= L + 16382 ->
  f128_le (nrepr L N s) 0 = 1.
Proof.
  intros. unfold nrepr. pose proof (nrepr_T L N H H0). apply f128_le_pos_zero; [constructor; lia| lia| lia].
Qed.

Lemma f128_le_zero : f128_le (f128_pack 0 0 0) 0 = 0.
Proof. reflexivity. Qed.

Lemma to_u32_nrepr : forall L N s, 0 <= s <= 60 -> 0 <= L <= 31 + s -> 2^L <= N < 2^(L+1) ->
  f128_to_u32 (nrepr L N s) = N / 2^s.
Proof.
  intros L N s Hs HL HN. unfold nrepr.
  pose proof (nrepr_T L N ltac:(lia) HN) as [HT HM].
  destruct (Z.lt_ge_cases L s).
  - rewrite f128_to_u32_small; [| constructor; lia | lia].
    symmetry. apply Z.div_small. split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 HN)|]. apply Z.pow_le_mono_r; lia.
  - rewrite f128_to_u32_val; [| constructor; lia | lia].
    replace (2 ^ 112 + (N * 2 ^ (112 - L) - 2 ^ 112)) with (N * 2^(112 - L)) by lia.
    replace (16495 - (16383 + L - s)) with ((112 - L) + s) by lia.
    rewrite <- pow2_mul by lia. rewrite <- Z.div_div by (try apply pow2_pos'; lia).
    rewrite Z.div_mul by (pose proof (pow2_pos' (112 - L)); lia). reflexivity.
Qed.

Lemma sub_trunc_nrepr : forall L N s, 0 <= s <= 60 -> 0 <= L <= 31 + s -> 2^L <= N < 2^(L+1) ->
  let R := N mod 2^s in
  (R = 0 -> f128_sub (nrepr L N s) (f128_of_u32 (N / 2^s)) = f128_pack 0 0 0) /\
  (R <> 0 -> f128_sub (nrepr L N s) (f128_of_u32 (N / 2^s)) = nrepr (Z.log2 R) R s /\ 2^(Z.log2 R) <= R < 2^(Z.log2 R + 1) /\ 0 <= Z.log2 R < s).
Proof.
  intros L N s Hs HL HN. cbv zeta.
  pose proof (pow2_pos' s ltac:(lia)) as Ps.
  pose proof (Z.div_mod N (2^s) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound N (2^s) ltac:(lia)) as MB.
  pose proof (nrepr_T L N ltac:(lia) HN) as [HT HM].
  pose proof (pow2_pos' (112 - L) ltac:(lia)) as P1.
  destruct (Z.lt_ge_cases L s) as [SM|BG].
  -
    assert (N < 2^s). { eapply Z.lt_le_trans; [apply (proj2 HN)|]. apply Z.pow_le_mono_r; lia. }
    rewrite (Z.div_small N (2^s)) by lia. rewrite f128_of_u32_zero.
    rewrite (Z.mod_small N (2^s)) by lia.
    split; [intros; lia|]. intros _.
    assert (HLg : Z.log2 N = L) by (apply Z.log2_unique; lia).
    rewrite HLg. split; [|split; [exact HN| lia]].
    unfold nrepr. apply f128_sub_zero_r; [constructor; lia| lia].
  - set (q := N / 2^s) in *. set (R := N mod 2^s) in *.
    assert (Hq : 2^(L - s) <= q < 2^(L - s + 1)).
    { assert (E1 : 2^L = 2^(L-s) * 2^s) by (rewrite pow2_mul by lia; f_equal; lia).
      assert (E2 : 2^(L+1) = 2^(L-s+1) * 2^s) by (rewrite pow2_mul by lia; f_equal; lia).
      pose proof (pow2_pos' (L - s) ltac:(lia)). nia. }
    rewrite (f128_of_u32_val q (L - s)) by lia.
    unfold nrepr.
    replace (16383 + (L - s)) with (16383 + L - s) by lia.
    assert (EQT : q * 2 ^ (112 - (L - s)) = (N - R) * 2^(112 - L)).
    { replace (112 - (L - s)) with (s + (112 - L)) by lia. rewrite <- pow2_mul by lia. nia. }
    rewrite EQT.
    split.
    + intros HR0. rewrite HR0, Z.sub_0_r. apply f128_sub_same; [constructor; lia| lia].
    + intros HR.
      destruct (Z.log2_spec R ltac:(lia)) as [LR1 LR2]. rewrite <- Z.add_1_r in LR2.
      set (LR := Z.log2 R) in *.
      assert (HLR : 0 <= LR < s).
      { split; [apply Z.log2_nonneg|]. apply Z.log2_lt_pow2; lia. }
      split; [| split; [lia| lia]].
      rewrite (f128_sub_exact (16383 + L - s) (N * 2^(112-L) - 2^112) ((N - R) * 2^(112-L) - 2^112) (LR + (112 - L))).
      * f_equal; [lia|].
        replace (N * 2 ^ (112 - L) - 2 ^ 112 - ((N - R) * 2 ^ (112 - L) - 2 ^ 112)) with (R * 2^(112 - L)) by lia.
        replace (112 - (LR + (112 - L))) with (L - LR) by lia.
        replace (112 - LR) with ((112 - L) + (L - LR)) by lia. rewrite <- (pow2_mul (112 - L) (L - LR)) by lia. lia.
      * constructor; lia.
      * assert (E1 : 2^(L - s) * 2^s = 2^L) by (rewrite pow2_mul by lia; f_equal; lia).
        assert (E2 : 2^L * 2^(112 - L) = 2^112) by (rewrite pow2_mul by lia; f_equal; lia).
        assert (G : 2^L <= N - R) by nia.
        nia.
      * lia.
      * lia.
      * replace (N * 2 ^ (112 - L) - 2 ^ 112 - ((N - R) * 2 ^ (112 - L) - 2 ^ 112)) with (R * 2^(112 - L)) by lia.
        rewrite <- !pow2_mul by lia. replace (LR + (112 - L) + 1) with ((LR + 1) + (112 - L)) by lia.
        change (2^1) with 2. rewrite Z.pow_add_r in LR2 by lia. change (2^1) with 2 in LR2. nia.
Qed.

Lemma T9_range : 0 <= T9 < 2^112. Proof. unfold T9. split; [vm_compute; discriminate| reflexivity]. Qed.

Lemma mul_1e9_nrepr : forall LR R s, 0 <= LR -> 2^LR <= R < 2^(LR+1) -> LR <= s <= 60 ->
  let P := 1000000000 * R in let LP := Z.log2 P in
  f128_mul (f128_pack 0 16412 T9) (nrepr LR R s) = nrepr LP P s /\ 2^LP <= P < 2^(LP+1) /\ (LP = LR + 29 \/ LP = LR + 30).
Proof.
  intros LR R s HLR HR Hs. cbv zeta.
  set (P := 1000000000 * R).
  assert (HP : 2^(LR+29) <= P < 2^(LR+31)).
  { subst P. rewrite <- !pow2_mul by lia. change (2^29) with 536870912. change (2^31) with 2147483648.
    pose proof HR as HR'. rewrite Z.pow_add_r in HR' by lia. change (2^1) with 2 in HR'. nia. }
  destruct (Z.log2_spec P ltac:(lia)) as [LP1 LP2]. rewrite <- Z.add_1_r in LP2. set (LP := Z.log2 P) in *.
  assert (HLP : LP = LR + 29 \/ LP = LR + 30).
  { assert (LR + 29 <= LP). { subst LP. apply Z.log2_le_pow2; lia. }
    assert (LP < LR + 31). { subst LP. apply Z.log2_lt_pow2; lia. } lia. }
  split; [| split; [lia| exact HLP]].
  unfold nrepr.
  pose proof (nrepr_T LR R ltac:(lia) HR) as [HT HM].
  pose proof (nrepr_T LP P ltac:(lia) ltac:(lia)) as [HTP HMP].
  rewrite (f128_mul_exact 0 16412 T9 0 (16383 + LR - s) (R * 2^(112 - LR) - 2^112) (P * 2^(112 - LP)) (LP - LR - 29)).
  - f_equal; lia.
  - pose proof T9_range. constructor; lia.
  - constructor; lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold T9. replace (2 ^ 112 + (1000000000 * 2 ^ 83 - 2 ^ 112)) with (1000000000 * 2^83) by lia.
    replace (2 ^ 112 + (R * 2 ^ (112 - LR) - 2 ^ 112)) with (R * 2^(112 - LR)) by lia.
    subst P.
    transitivity (1000000000 * R * (2^83 * 2^(112 - LR))); [lia|].
    rewrite <- !Z.mul_assoc. f_equal. rewrite !pow2_mul by lia. f_equal. f_equal. lia.
  - lia.
Qed.

Lemma mul_1e9_zero : f128_mul (f128_pack 0 16412 T9) (f128_pack 0 0 0) = f128_pack 0 0 0.
Proof. vmc_refl. Qed.

Lemma fmt_fp_dig_unfold : forall k big z y,
  fmt_fp_dig (S k) (big, z, y) =
   (let zv := f128_to_u32 y in
    let y' := f128_mul (f128_of_i32 1000000000) (f128_sub y (f128_of_u32 zv)) in
    if negb (f128_le y' F128_ZERO =? 0) then fmt_fp_dig k (zupd big z zv, z + 1, y') else Some (zupd big z zv, z + 1, y')).
Proof. reflexivity. Qed.

Definition ZERO128 : Z := f128_pack 0 0 0.
Lemma zero128_eq : ZERO128 = 0. Proof. reflexivity. Qed.

Lemma dig_iter : forall (m : nat) fuel big z L N,
  (m <= 3)%nat -> (S m <= fuel)%nat -> 0 <= L <= 55 -> 2^L <= N < 2^(L+1) -> N < 1000000000 * 2^24 ->
  N mod 2^(27 - 9 * Z.of_nat m) = 0 -> 0 <= z -> z + Z.of_nat m + 1 <= zlength big ->
  exists big' n,
    fmt_fp_dig fuel (big, z, nrepr L N 24) = Some (big', z + n, ZERO128) /\
    1 <= n <= Z.of_nat m + 1 /\ length big' = length big /\
    znth big' z = N / 2^24 /\
    (forall i, z <= i < z + n -> 0 <= znth big' i < 1000000000) /\
    (forall i, ~ (z <= i < z + n) -> znth big' i = znth big i).
Proof.
  induction m as [|m IH]; intros fuel big z L N Hm Hf HL HN HNB HD Hz Hlen.
  -
    destruct fuel as [|k]; [lia|]. rewrite fmt_fp_dig_unfold. cbv zeta.
    rewrite (to_u32_nrepr L N 24) by lia.
    destruct (sub_trunc_nrepr L N 24) as [Z0 _]; [lia|lia|lia|].
    change (27 - 9 * Z.of_nat 0) with 27 in HD.
    assert (R0 : N mod 2^24 = 0).
    { apply Z.mod_divide in HD; [|lia]. apply Z.mod_divide; [lia|]. destruct HD as [q Hq]. exists (q * 2^3). rewrite Hq. rewrite <- Z.mul_assoc. f_equal. }
    rewrite (Z0 R0). rewrite K1E9_eq, mul_1e9_zero. unfold F128_ZERO. rewrite f128_le_zero. cbn [Z.eqb negb].
    exists (zupd big z (N / 2^24)), 1. split; [reflexivity|]. split; [lia|]. split; [apply zupd_length|].
    split; [apply znth_zupd_eq; lia|]. split.
    + intros i Hi. replace i with z by lia. rewrite znth_zupd_eq by lia.
      split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
    + intros i Hi. apply znth_zupd_neq. lia.
  - destruct fuel as [|k]; [lia|]. rewrite fmt_fp_dig_unfold. cbv zeta.
    rewrite (to_u32_nrepr L N 24) by lia.
    destruct (sub_trunc_nrepr L N 24) as [Z0 NZ]; [lia|lia|lia|].
    destruct (Z.eq_dec (N mod 2^24) 0) as [R0|RNZ].
    + rewrite (Z0 R0). rewrite K1E9_eq, mul_1e9_zero. unfold F128_ZERO. rewrite f128_le_zero. cbn [Z.eqb negb].
      exists (zupd big z (N / 2^24)), 1. split; [reflexivity|]. split; [lia|]. split; [apply zupd_length|].
      split; [apply znth_zupd_eq; lia|]. split.
      * intros i Hi. replace i with z by lia. rewrite znth_zupd_eq by lia.
        split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
      * intros i Hi. apply znth_zupd_neq. lia.
    + destruct (NZ RNZ) as (ES & HR & HLR). rewrite ES. set (R := N mod 2^24) in *. set (LR := Z.log2 R) in *.
      rewrite K1E9_eq.
      destruct (mul_1e9_nrepr LR R 24) as (EM & HP & HLP); [lia|exact HR|lia|]. cbv zeta in EM. rewrite EM.
      set (P := 1000000000 * R) in *. set (LP := Z.log2 P) in *.
      unfold F128_ZERO. rewrite (f128_le_nrepr LP P 24) by lia. cbn [Z.eqb negb].
      destruct (IH k (zupd big z (N / 2^24)) (z + 1) LP P) as [big' [n (E & Hn & Hlen' & Hw0 & Hws & Hother)]]; try lia.
      { pose proof (Z.mod_pos_bound N (2^24) ltac:(lia)). subst P. lia. }
      {
        rewrite Nat2Z.inj_succ in HD.
        replace (27 - 9 * Z.of_nat m) with (9 + (27 - 9 * Z.succ (Z.of_nat m))) by lia.
        set (e := 27 - 9 * Z.succ (Z.of_nat m)) in *.
        assert (He : 0 <= e <= 18) by lia.
        rewrite <- pow2_mul by lia. subst P.
        assert (HRd : R mod 2^e = 0).
        { subst R. rewrite <- Znumtheory.Zmod_div_mod; try (apply pow2_pos'; lia).
          - exact HD.
          - replace 24 with (e + (24 - e)) by lia. rewrite <- pow2_mul by lia. apply Z.divide_factor_l. }
        apply Z.mod_divide in HRd; [|pose proof (pow2_pos' e); lia]. destruct HRd as [q Hq].
        apply Z.mod_divide; [pose proof (pow2_pos' e); lia|]. exists (1953125 * q).
        rewrite Hq. change (2^9) with 512. lia. }
      { rewrite zlength_zupd. lia. }
      rewrite E. exists big', (n + 1). split; [f_equal; f_equal; f_equal; lia|]. split; [lia|]. split; [rewrite Hlen'; apply zupd_length|].
      split. { rewrite Hother by lia. apply znth_zupd_eq. lia. }
      split.
      * intros i Hi. destruct (Z.eq_dec i z) as [->|].
        -- rewrite Hother by lia. rewrite znth_zupd_eq by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
        -- apply Hws. lia.
      * intros i Hi. rewrite Hother by lia. apply znth_zupd_neq. lia.
Qed.

Lemma f128_of_d_mod : forall d, f128_of_d d = f128_of_d (d mod 2^64).
Proof.
  intros d. unfold f128_of_d, lo64. rewrite !wrap64_mod. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Definition d_sign (d : Z) : Z := (d mod 2^64) / 2^63.
Definition d_exp (d : Z) : Z := ((d mod 2^64) / 2^52) mod 2^11.
Definition d_frac (d : Z) : Z := (d mod 2^64) mod 2^52.

Definition dfin (d : Z) : Prop := d_exp d <> 2047.

Lemma d_fields : forall d,
  0 <= d_sign d <= 1 /\ 0 <= d_exp d <= 2047 /\ 0 <= d_frac d < 2^52 /\
  d mod 2^64 = d_sign d * 2^63 + d_exp d * 2^52 + d_frac d.
Proof.
  intros d. unfold d_sign, d_exp, d_frac.
  pose proof (Z.mod_pos_bound d (2^64) ltac:(lia)). set (dm := d mod 2^64) in *. clearbody dm. dlia.
Qed.

Lemma f128_of_d_shape : forall d,
  (d_exp d = 2047 -> f128_of_d d = f128_pack (d_sign d) 32767 (d_frac d * 2^60)) /\
  (d_exp d = 0 -> d_frac d = 0 -> f128_of_d d = f128_pack (d_sign d) 0 0) /\
  (d_exp d <> 2047 -> ~ (d_exp d = 0 /\ d_frac d = 0) ->
     exists E0 K0, f128_of_d d = f128_pack (d_sign d) E0 (K0 * 2^60) /\ 15309 <= E0 <= 17406 /\ 0 <= K0 < 2^52).
Proof.
  intros d. pose proof (d_fields d) as (Hs & He & Hf & Hd).
  rewrite f128_of_d_mod. rewrite Hd.
  set (sd := d_sign d) in *. set (Ed := d_exp d) in *. set (Td := d_frac d) in *. clearbody sd Ed Td.
  split; [|split].
  - intros ->. apply f128_of_d_infnan; lia.
  - intros -> ->. replace (sd * 2 ^ 63 + 0 * 2 ^ 52 + 0) with (sd * 2^63) by lia. apply f128_of_d_zero; lia.
  - intros HE HNZ. destruct (Z.eq_dec Ed 0) as [E0|E0].
    + subst Ed. assert (Tpos : 0 < Td) by lia.
      destruct (Z.log2_spec Td Tpos) as [L1 L2]. rewrite <- Z.add_1_r in L2. set (L := Z.log2 Td) in *.
      assert (HL : 0 <= L <= 51). { split; [apply Z.log2_nonneg|]. enough (L < 52) by lia. apply Z.log2_lt_pow2; lia. }
      exists (15309 + L), (Td * 2^(52 - L) - 2^52).
      replace (sd * 2 ^ 63 + 0 * 2 ^ 52 + Td) with (sd * 2^63 + Td) by lia.
      rewrite (f128_of_d_subnormal sd Td L) by lia.
      assert (E1 : 2^(112 - L) = 2^(52 - L) * 2^60) by (rewrite pow2_mul by lia; f_equal; lia).
      assert (E2 : 2^L * 2^(52 - L) = 2^52) by (rewrite pow2_mul by lia; f_equal; lia).
      assert (E3 : 2^(L+1) * 2^(52 - L) = 2^53) by (rewrite pow2_mul by lia; f_equal; lia).
      pose proof (pow2_pos' (52 - L) ltac:(lia)).
      split; [f_equal; rewrite E1; lia|]. split; [lia|]. nia.
    + exists (Ed + 15360), Td. rewrite f128_of_d_normal by lia. split; [reflexivity|]. lia.
Qed.

Lemma signbitl_pack : forall s E T, packed s E T -> signbitl (f128_pack s E T) = s.
Proof.
  intros s E T PK. destruct PK as [Hs HE HT]. pose proof (T_split T HT) as (A & B & C).
  unfold signbitl. rewrite f128_pack_hi by (constructor; lia). apply hiword_sign; lia.
Qed.

Lemma strip_sign_pack : forall s E T, packed s E T ->
  (if negb (signbitl (f128_pack s E T) =? 0) then Z.lxor (f128_pack s E T) F128_SIGNBIT else f128_pack s E T) = f128_pack 0 E T.
Proof.
  intros s E T PK. rewrite signbitl_pack by exact PK. destruct PK as [Hs HE HT].
  assert (D : s = 0 \/ s = 1) by lia. destruct D as [-> | ->]; cbn [Z.eqb negb].
  - reflexivity.
  - unfold F128_SIGNBIT. change 0x80000000000000000000000000000000 with (2^127).
    unfold f128_pack. rewrite lxor_bit_set; [lia|lia|lia|].
    replace ((1 * 2 ^ 127 + E * 2 ^ 112 + T) / 2 ^ 127) with 1; [reflexivity|].
    apply Z.div_unique with (r := E * 2^112 + T); lia.
Qed.

Lemma fpclassifyl_pack : forall E T, packed 0 E T -> E <= 32766 ->
  fpclassifyl (f128_pack 0 E T) = (if (E =? 0) then (if (T =? 0) then 2 else 3) else 4).
Proof.
  intros E T PK HE. destruct PK as [_ HE' HT]. pose proof (T_split T HT) as (A & B & C).
  unfold fpclassifyl. rewrite f128_pack_hi, f128_pack_lo by (constructor; lia).
  rewrite hiword_expfield by lia. change 0x0000ffffffffffff with MASK48. rewrite hiword_frac by lia.
  destruct (Z.eqb_spec E 0) as [->|NE].
  - rewrite lor_eqb0 by lia.
    destruct (Z.eqb_spec T 0) as [->|NT].
    + change (0 mod 2^64 =? 0) with true. change (0 / 2^64 =? 0) with true. reflexivity.
    + replace ((T mod 2 ^ 64 =? 0) && (T / 2 ^ 64 =? 0)) with false; [reflexivity|].
      symmetry. apply Bool.andb_false_iff. destruct (Z.eq_dec (T mod 2^64) 0); [right|left]; apply Z.eqb_neq; lia.
  - replace (E =? 32767) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma frexpl_pack_zero : frexpl FREXPL_FUEL (f128_pack 0 0 0) 0 = Some (f128_pack 0 0 0, 0).
Proof. reflexivity. Qed.

Lemma frexpl_pack : forall E T, packed 0 E T -> 1 <= E <= 32766 ->
  frexpl FREXPL_FUEL (f128_pack 0 E T) 0 = Some (f128_pack 0 16382 T, E - 16382).
Proof.
  intros E T PK HE. destruct PK as [_ HE' HT]. pose proof (T_split T HT) as (A & B & C).
  change FREXPL_FUEL with 2%nat. cbn [frexpl].
  rewrite f128_pack_hi, f128_pack_lo by (constructor; lia).
  rewrite hiword_expfield by lia.
  replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (E =? 32767) with false by (symmetry; apply Z.eqb_neq; lia).
  f_equal. f_equal.
  change 9223372036854775808 with (2^63). change 281474976710655 with MASK48. change 4611123068473966592 with (16382 * 2^48). change 0x0000ffffffffffff with MASK48. change 0x3ffe000000000000 with (16382 * 2^48).
  rewrite hiword_frac by lia.
  replace (Z.land (0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) (2 ^ 63)) with 0.
  2:{ symmetry. rewrite Z.land_comm. apply (land_high_low 1 _ 63); lia. }
  rewrite Z.lor_0_l. rewrite lor_low_high by lia. rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

Record prologue_vals := { pv_ynz : bool; pv_e0 : Z; pv_fr : Z; pv_y2 : Z; pv_y3 : Z; pv_e2 : Z }.

Lemma prologue_nonzero : forall E0 K0, 15309 <= E0 <= 17406 -> 0 <= K0 < 2^52 ->
  let y1 := f128_pack 0 E0 (K0 * 2^60) in
  fpclassifyl y1 = 4 /\
  frexpl FREXPL_FUEL y1 0 = Some (f128_pack 0 16382 (K0 * 2^60), E0 - 16382) /\
  f128_mul (f128_pack 0 16382 (K0 * 2^60)) (f128_of_i32 2) = f128_pack 0 16383 (K0 * 2^60) /\
  f128_le (f128_pack 0 16383 (K0 * 2^60)) F128_ZERO = 1 /\
  f128_mul (f128_pack 0 16383 (K0 * 2^60)) (f128_of_d D_0x1p28) = nrepr 52 (2^52 + K0) 24.
Proof.
  intros E0 K0 HE HK. cbv zeta.
  assert (PK : forall E, 0 <= E <= 32767 -> packed 0 E (K0 * 2^60)) by (intros; constructor; lia).
  split. { rewrite fpclassifyl_pack; [|apply PK; lia|lia]. replace (E0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  split. { apply frexpl_pack; [apply PK; lia| lia]. }
  split. { rewrite K2_eq. rewrite (f128_mul_exact 0 16382 (K0 * 2^60) 0 16384 0 (2^112 + K0 * 2^60) 0); try lia.
           all: try (apply PK; lia). all: try (constructor; lia).
           change (Z.lxor 0 0) with 0. f_equal; lia. }
  split. { unfold F128_ZERO. apply f128_le_pos_zero; [apply PK; lia| lia| lia]. }
  rewrite K28_eq. rewrite (f128_mul_exact 0 16383 (K0 * 2^60) 0 16411 0 (2^112 + K0 * 2^60) 0); try lia.
  all: try (apply PK; lia). all: try (constructor; lia).
  unfold nrepr. change (Z.lxor 0 0) with 0. change (2^(112-52)) with (2^60). f_equal; lia.
Qed.

Lemma prologue_zero :
  fpclassifyl (f128_pack 0 0 0) = 2 /\
  frexpl FREXPL_FUEL (f128_pack 0 0 0) 0 = Some (f128_pack 0 0 0, 0) /\
  f128_mul (f128_pack 0 0 0) (f128_of_i32 2) = f128_pack 0 0 0 /\
  f128_le (f128_pack 0 0 0) F128_ZERO = 0.
Proof. repeat split; reflexivity. Qed.

Lemma dig_zero : forall fuel big z, (1 <= fuel)%nat -> 0 <= z < zlength big ->
  fmt_fp_dig fuel (big, z, f128_pack 0 0 0) = Some (zupd big z 0, z + 1, f128_pack 0 0 0).
Proof.
  intros fuel big z Hf Hz. destruct fuel as [|k]; [lia|]. rewrite fmt_fp_dig_unfold. cbv zeta.
  rewrite f128_to_u32_small by (try constructor; lia).
  rewrite f128_of_u32_zero. rewrite f128_sub_zero_r by (try constructor; lia).
  rewrite K1E9_eq, mul_1e9_zero. reflexivity.
Qed.

Definition strip_sign (y0 : Z) : Z :=
  if negb (signbitl y0 =? 0) then Z.lxor y0 F128_SIGNBIT else y0.

Definition prologue_ok (d : Z) : Prop :=
  let y1 := strip_sign (f128_of_d d) in
  exists (nz : bool) (fr : Z) (e0 : Z) (N0 : Z),
    1 < fpclassifyl y1 /\
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) /\
    let y2 := f128_mul fr (f128_of_i32 2) in
    negb (f128_le y2 F128_ZERO =? 0) = nz /\
    (nz = false -> e0 = 0 /\ y2 = f128_pack 0 0 0) /\
    (nz = true -> -1073 <= e0 <= 1024 /\ 2^52 <= N0 < 2^53 /\
                  f128_mul y2 (f128_of_d D_0x1p28) = nrepr 52 N0 24) /\

    (forall (fuel : nat) (r0 : Z) (big0 : list Z), (4 <= fuel)%nat -> 0 <= r0 -> r0 + 4 <= zlength big0 ->
       exists big z,
         fmt_fp_dig fuel (big0, r0, if nz then nrepr 52 N0 24 else f128_pack 0 0 0) = Some (big, z, f128_pack 0 0 0) /\
         length big = length big0 /\
         r0 + 1 <= z <= r0 + 4 /\
         (nz = false -> z = r0 + 1 /\ znth big r0 = 0) /\
         (nz = true -> znth big r0 = N0 / 2^24 /\ 2^28 <= znth big r0 < 2^29) /\
         (forall i, r0 <= i < z -> 0 <= znth big i < 1000000000) /\
         (forall i, ~ (r0 <= i < z) -> znth big i = znth big0 i)).

Theorem prologue_ok_finite : forall d, dfin d -> prologue_ok d.
Proof.
  intros d Hfin. unfold prologue_ok, strip_sign.
  pose proof (d_fields d) as (Hs & He & Hf & Hd).
  destruct (f128_of_d_shape d) as (_ & SHZ & SHN).
  destruct (Z.eq_dec (d_exp d) 0) as [E0|E0]; [destruct (Z.eq_dec (d_frac d) 0) as [F0|F0]|].
  -
    rewrite (SHZ E0 F0). rewrite strip_sign_pack by (constructor; lia).
    destruct prologue_zero as (C1 & C2 & C3 & C4).
    exists false, (f128_pack 0 0 0), 0, 0.
    split; [rewrite C1; lia|]. split; [exact C2|]. cbv zeta. rewrite C3, C4.
    split; [reflexivity|]. split; [intros _; split; reflexivity|]. split; [intros X; discriminate X|].
    intros fuel r0 big0 Hfu Hr0 Hlen. rewrite dig_zero by lia.
    eexists _, _. split; [reflexivity|]. split; [apply zupd_length|]. split; [lia|].
    split; [intros _; split; [reflexivity| apply znth_zupd_eq; lia]|]. split; [intros X; discriminate X|].
    split.
    + intros i Hi. replace i with r0 by lia. rewrite znth_zupd_eq by lia. lia.
    + intros i Hi. apply znth_zupd_neq. lia.
  - destruct (SHN Hfin ltac:(lia)) as [E1 [K0 (EQ & HE1 & HK0)]].
    rewrite EQ. rewrite strip_sign_pack by (constructor; lia).
    destruct (prologue_nonzero E1 K0 HE1 HK0) as (C1 & C2 & C3 & C4 & C5).
    exists true, (f128_pack 0 16382 (K0 * 2^60)), (E1 - 16382), (2^52 + K0).
    split; [rewrite C1; lia|]. split; [exact C2|]. cbv zeta. rewrite C3, C4.
    split; [reflexivity|]. split; [intros X; discriminate X|]. split; [intros _; split; [lia|]; split; [lia| exact C5]|].
    intros fuel r0 big0 Hfu Hr0 Hlen.
    destruct (dig_iter 3 fuel big0 r0 52 (2^52 + K0)) as [big [n (E & Hn & HL & Hw0 & Hws & Hoth)]]; try lia.
    all: try (change (2^(52+1)) with (2^53); lia).
    1: { change (27 - 9 * Z.of_nat 3) with 0. apply Z.mod_1_r. }
    unfold ZERO128 in E. rewrite E. exists big, (r0 + n). split; [reflexivity|]. split; [exact HL|]. split; [lia|].
    split; [intros X; discriminate X|]. split.
    + intros _. split; [exact Hw0|]. rewrite Hw0. dlia.
    + split; [intros i Hi; apply Hws; lia| intros i Hi; apply Hoth; lia].
  - destruct (SHN Hfin ltac:(lia)) as [E1 [K0 (EQ & HE1 & HK0)]].
    rewrite EQ. rewrite strip_sign_pack by (constructor; lia).
    destruct (prologue_nonzero E1 K0 HE1 HK0) as (C1 & C2 & C3 & C4 & C5).
    exists true, (f128_pack 0 16382 (K0 * 2^60)), (E1 - 16382), (2^52 + K0).
    split; [rewrite C1; lia|]. split; [exact C2|]. cbv zeta. rewrite C3, C4.
    split; [reflexivity|]. split; [intros X; discriminate X|]. split; [intros _; split; [lia|]; split; [lia| exact C5]|].
    intros fuel r0 big0 Hfu Hr0 Hlen.
    destruct (dig_iter 3 fuel big0 r0 52 (2^52 + K0)) as [big [n (E & Hn & HL & Hw0 & Hws & Hoth)]]; try lia.
    all: try (change (2^(52+1)) with (2^53); lia).
    1: { change (27 - 9 * Z.of_nat 3) with 0. apply Z.mod_1_r. }
    unfold ZERO128 in E. rewrite E. exists big, (r0 + n). split; [reflexivity|]. split; [exact HL|]. split; [lia|].
    split; [intros X; discriminate X|]. split.
    + intros _. split; [exact Hw0|]. rewrite Hw0. dlia.
    + split; [intros i Hi; apply Hws; lia| intros i Hi; apply Hoth; lia].
Qed.

Lemma fpclassifyl_infnan : forall d, d_exp d = 2047 -> fpclassifyl (strip_sign (f128_of_d d)) <= 1.
Proof.
  intros d HE. pose proof (d_fields d) as (Hs & He & Hf & Hd).
  destruct (f128_of_d_shape d) as (SHI & _ & _). rewrite (SHI HE).
  unfold strip_sign. rewrite strip_sign_pack by (constructor; dlia).
  unfold fpclassifyl.
  assert (PK : packed 0 32767 (d_frac d * 2^60)) by (constructor; dlia).
  pose proof (T_split (d_frac d * 2^60) ltac:(dlia)) as (A & B & C).
  rewrite f128_pack_hi, f128_pack_lo by exact PK.
  rewrite hiword_expfield by lia. change (32767 =? 0) with false. change (32767 =? 32767) with true. cbv iota.
  destruct (negb _); lia.
Qed.

Lemma yn_widened : forall d, dfin d ->
  let y := f128_of_d d in
  (Z.land (Z.shiftr (hi64 y) 48) 0x7fff <> 0 \/ f128_le y F128_ZERO = 0) /\
  (Z.land (Z.shiftr (hi64 (Z.lxor y F128_SIGNBIT)) 48) 0x7fff <> 0 \/ f128_le (Z.lxor y F128_SIGNBIT) F128_ZERO = 0).
Proof.
  intros d Hfin. cbv zeta. pose proof (d_fields d) as (Hs & He & Hf & Hd).
  destruct (f128_of_d_shape d) as (_ & SHZ & SHN).
  assert (XS : forall s E T, packed s E T -> Z.lxor (f128_pack s E T) F128_SIGNBIT = f128_pack (1 - s) E T).
  { intros s E T [A B C]. unfold F128_SIGNBIT, f128_pack. change 0x80000000000000000000000000000000 with (2^127).
    assert (D : s = 0 \/ s = 1) by lia. destruct D as [-> | ->].
    - rewrite lxor_bit_clear; [lia|lia|lia|]. rewrite Z.div_small; [reflexivity| lia].
    - rewrite lxor_bit_set; [lia|lia|lia|]. replace ((1 * 2 ^ 127 + E * 2 ^ 112 + T) / 2 ^ 127) with 1; [reflexivity|].
      apply Z.div_unique with (r := E * 2^112 + T); lia. }
  destruct (Z.eq_dec (d_exp d) 0) as [E0|E0]; [destruct (Z.eq_dec (d_frac d) 0) as [F0|F0]|].
  - rewrite (SHZ E0 F0). rewrite XS by (constructor; lia). split; right; unfold F128_ZERO; apply f128_le_zero_zero; lia.
  - destruct (SHN Hfin ltac:(lia)) as [E1 [K0 (EQ & HE1 & HK0)]]. rewrite EQ. rewrite XS by (constructor; lia).
    pose proof (T_split (K0 * 2^60) ltac:(lia)) as (A & B & C).
    split; left; rewrite f128_pack_hi by (constructor; lia); rewrite hiword_expfield by lia; lia.
  - destruct (SHN Hfin ltac:(lia)) as [E1 [K0 (EQ & HE1 & HK0)]]. rewrite EQ. rewrite XS by (constructor; lia).
    pose proof (T_split (K0 * 2^60) ltac:(lia)) as (A & B & C).
    split; left; rewrite f128_pack_hi by (constructor; lia); rewrite hiword_expfield by lia; lia.
Qed.
