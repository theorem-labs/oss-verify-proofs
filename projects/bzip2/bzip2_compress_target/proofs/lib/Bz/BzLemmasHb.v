(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section Hb.
  Variables (len : Z -> Z) (alpha minLen maxLen : Z).
  Hypothesis Halpha : 1 <= alpha <= 258.
  Hypothesis Hmm : 1 <= minLen /\ minLen <= maxLen <= 20.
  Hypothesis Hlen : forall j, 0 <= j < alpha -> minLen <= len j <= maxLen.

  (* [comment removed for export] *)
  Definition cnt_eq (i : Z) : Z := zcount (fun j => len j =? i) 0 (Z.to_nat alpha).
  Definition cnt_lt (i : Z) : Z := zcount (fun j => len j <? i) 0 (Z.to_nat alpha).

  Lemma cnt_eq_range : forall i, 0 <= cnt_eq i <= alpha.
  Proof. intros. unfold cnt_eq. pose proof (zcount_bounds (fun j => len j =? i) 0 (Z.to_nat alpha)). lia. Qed.
  Lemma cnt_lt_range : forall i, 0 <= cnt_lt i <= alpha.
  Proof. intros. unfold cnt_lt. pose proof (zcount_bounds (fun j => len j <? i) 0 (Z.to_nat alpha)). lia. Qed.

  Lemma cnt_lt_succ : forall i, cnt_lt (i + 1) = cnt_lt i + cnt_eq i.
  Proof.
    intros. unfold cnt_lt, cnt_eq.
    rewrite <- zcount_or_disj by (intros k Hk A B; apply Z.ltb_lt in A; apply Z.eqb_eq in B; lia).
    apply zcount_ext. intros k Hk.
    destruct (Z.ltb_spec (len k) (i + 1)), (Z.ltb_spec (len k) i), (Z.eqb_spec (len k) i); cbn; auto; lia.
  Qed.

  Lemma cnt_lt_low : forall i, i <= minLen -> cnt_lt i = 0.
  Proof.
    intros. unfold cnt_lt. apply zcount_false. intros k Hk.
    specialize (Hlen k ltac:(lia)). destruct (Z.ltb_spec (len k) i); auto; lia.
  Qed.

  Lemma cnt_lt_high : forall i, maxLen < i -> cnt_lt i = alpha.
  Proof.
    intros. unfold cnt_lt. rewrite zcount_all; [lia|]. intros k Hk.
    specialize (Hlen k ltac:(lia)). destruct (Z.ltb_spec (len k) i); auto; lia.
  Qed.

  Lemma cnt_eq_out : forall i, i < minLen \/ maxLen < i -> cnt_eq i = 0.
  Proof.
    intros. unfold cnt_eq. apply zcount_false. intros k Hk.
    specialize (Hlen k ltac:(lia)). destruct (Z.eqb_spec (len k) i); auto; lia.
  Qed.

  (* [comment removed for export] *)

  Lemma cnt_lt_succ_le : forall i, cnt_lt i + cnt_eq i <= alpha.
  Proof. intros. rewrite <- cnt_lt_succ. apply cnt_lt_range. Qed.

  (* [comment removed for export] *)
  Fixpoint firstn (d : nat) : Z :=
    match d with
    | O => 0
    | S d' => 2 * (firstn d' + cnt_eq (minLen + Z.of_nat d'))
    end.
  Definition first (i : Z) : Z := firstn (Z.to_nat (i - minLen)).

  Lemma first_minLen : first minLen = 0.
  Proof. unfold first. now rewrite Z.sub_diag. Qed.

  Lemma first_succ : forall i, minLen <= i -> first (i + 1) = 2 * (first i + cnt_eq i).
  Proof.
    intros. unfold first. replace (Z.to_nat (i + 1 - minLen)) with (S (Z.to_nat (i - minLen))) by lia.
    cbn [firstn]. do 2 f_equal. f_equal. lia.
  Qed.

  Lemma firstn_nonneg : forall d, 0 <= firstn d.
  Proof. induction d; cbn [firstn]; [lia|]. pose proof (cnt_eq_range (minLen + Z.of_nat d)). lia. Qed.

  Lemma first_nonneg : forall i, 0 <= first i.
  Proof. intros. apply firstn_nonneg. Qed.

  Lemma first_ge_cnt_lt : forall i, minLen <= i -> cnt_lt i <= first i.
  Proof.
    intros i Hi. replace i with (minLen + Z.of_nat (Z.to_nat (i - minLen))) by lia.
    generalize (Z.to_nat (i - minLen)) as d. clear i Hi. intros d. induction d.
    - rewrite Z.add_0_r, cnt_lt_low, first_minLen; lia.
    - replace (minLen + Z.of_nat (S d)) with (minLen + Z.of_nat d + 1) by lia.
      rewrite first_succ, cnt_lt_succ by lia. pose proof (cnt_eq_range (minLen + Z.of_nat d)).
      pose proof (first_nonneg (minLen + Z.of_nat d)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma first_bound : forall i, minLen <= i -> first i + (alpha - cnt_lt i) <= 2 ^ (i - minLen) * alpha.
  Proof.
    intros i Hi. replace i with (minLen + Z.of_nat (Z.to_nat (i - minLen))) by lia.
    generalize (Z.to_nat (i - minLen)) as d. clear i Hi. intros d. induction d.
    - rewrite Z.add_0_r, first_minLen, cnt_lt_low, Z.sub_diag, Z.pow_0_r by lia. lia.
    - replace (minLen + Z.of_nat (S d)) with (minLen + Z.of_nat d + 1) by lia.
      rewrite first_succ, cnt_lt_succ by lia.
      replace (minLen + Z.of_nat d + 1 - minLen) with (Z.of_nat d + 1) by lia.
      replace (minLen + Z.of_nat d - minLen) with (Z.of_nat d) in IHd by lia.
      rewrite Z.pow_add_r by lia. pose proof (cnt_lt_succ_le (minLen + Z.of_nat d)).
      pose proof (cnt_eq_range (minLen + Z.of_nat d)). lia.
  Qed.

  Lemma first_le : forall i, minLen <= i -> first i <= 2 ^ (i - minLen) * alpha.
  Proof. intros. pose proof (first_bound i H). pose proof (cnt_lt_range i). lia. Qed.

  Lemma first_plus_le : forall i, minLen <= i -> first i + cnt_eq i <= 2 ^ (i - minLen) * alpha.
  Proof. intros. pose proof (first_bound i H). pose proof (cnt_lt_succ_le i). pose proof (cnt_lt_range i). lia. Qed.

  (* [comment removed for export] *)
  Lemma first_lt_2p29 : forall i, minLen <= i <= 21 -> 0 <= first i < 2 ^ 29.
  Proof.
    intros i Hi. split; [apply first_nonneg|].
    pose proof (first_le i ltac:(lia)).
    assert (2 ^ (i - minLen) <= 2 ^ 20) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ (i - minLen)) by (apply Z.pow_pos_nonneg; lia). nia.
  Qed.

  Lemma first_plus_lt_2p28 : forall i, minLen <= i <= 20 -> 0 <= first i + cnt_eq i < 2 ^ 28.
  Proof.
    intros i Hi. pose proof (first_nonneg i). pose proof (cnt_eq_range i). split; [lia|].
    pose proof (first_plus_le i ltac:(lia)).
    assert (2 ^ (i - minLen) <= 2 ^ 19) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ (i - minLen)) by (apply Z.pow_pos_nonneg; lia). nia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma hb_permJ_spec : forall n i j perm pp,
    let r := hb_permJ len i j n perm pp in
    snd r = pp + zcount (fun k => len k =? i) j n /\
    (forall q, q < pp \/ snd r <= q -> fst r q = perm q) /\
    (forall q, pp <= q < snd r -> j <= fst r q < j + Z.of_nat n /\ len (fst r q) = i).
  Proof.
    induction n as [|n IH]; intros i j perm pp; cbn zeta.
    - cbn. split; [lia|]. split; [intros; reflexivity | intros; lia].
    - rewrite hb_permJ_S, zcount_cons. pose proof (zcount_bounds (fun k => len k =? i) (j + 1) n) as B.
      destruct (Z.eqb_spec (len j) i) as [E|NE].
      + cps_destruct (IH i (j + 1) (zfupd perm pp j) (pp + 1)) as (A1 & A2 & A3). split; [lia|]. split.
        * intros q Hq. rewrite A2 by lia. apply zfupd_other. lia.
        * intros q Hq. destruct (Z.eq_dec q pp) as [->|NE'].
          -- rewrite A2 by lia. rewrite zfupd_same. lia.
          -- destruct (A3 q ltac:(lia)). lia.
      + cps_destruct (IH i (j + 1) perm pp) as (A1 & A2 & A3). split; [lia|]. split.
        * intros q Hq. apply A2. lia.
        * intros q Hq. destruct (A3 q ltac:(lia)). lia.
  Qed.

  Lemma hb_permI_spec : forall n i perm pp, 0 <= alpha ->
    let r := hb_permI len alpha i n perm pp in
    snd r = pp + zcount (fun k => (i <=? len k) && (len k <? i + Z.of_nat n)) 0 (Z.to_nat alpha) /\
    (forall q, q < pp \/ snd r <= q -> fst r q = perm q) /\
    (forall q, pp <= q < snd r -> 0 <= fst r q < alpha).
  Proof.
    induction n as [|n IH]; intros i perm pp Ha; cbn zeta.
    - cbn [hb_permI fst snd]. rewrite zcount_false; [|intros k Hk; destruct (Z.leb_spec i (len k)), (Z.ltb_spec (len k) (i + Z.of_nat 0)); cbn; auto; lia].
      split; [lia|]. split; [intros; reflexivity| intros; lia].
    - rewrite hb_permI_S. cbn zeta.
      pose proof (hb_permJ_spec (Z.to_nat alpha) i 0 perm pp) as PJ. cbn zeta in PJ. cps_destruct PJ as (J1 & J2 & J3).
      set (r1 := hb_permJ len i 0 (Z.to_nat alpha) perm pp) in *.
      cps_destruct (IH (i + 1) (fst r1) (snd r1) Ha) as (A1 & A2 & A3).
      pose proof (zcount_bounds (fun k => len k =? i) 0 (Z.to_nat alpha)).
      pose proof (zcount_bounds (fun k : Z => (i + 1 <=? len k) && (len k <? i + 1 + Z.of_nat n)) 0 (Z.to_nat alpha)).
      split.
      + rewrite A1, J1.
        enough (E : zcount (fun k => len k =? i) 0 (Z.to_nat alpha)
                    + zcount (fun k => (i + 1 <=? len k) && (len k <? i + 1 + Z.of_nat n)) 0 (Z.to_nat alpha)
                    = zcount (fun k => (i <=? len k) && (len k <? i + Z.of_nat (S n))) 0 (Z.to_nat alpha)) by lia.
        rewrite <- (zcount_or_disj (fun k => len k =? i)) by
          (intros k Hk A B%andb_prop; apply Z.eqb_eq in A; destruct B as [B _]; apply Z.leb_le in B; lia).
        apply zcount_ext.
        intros k Hk. destruct (Z.eqb_spec (len k) i), (Z.leb_spec (i+1) (len k)), (Z.ltb_spec (len k) (i + 1 + Z.of_nat n)),
          (Z.leb_spec i (len k)), (Z.ltb_spec (len k) (i + Z.of_nat (S n))); cbn; auto; lia.
      + split.
        * intros q Hq. rewrite A2 by lia. apply J2. lia.
        * intros q Hq. destruct (Z_lt_le_dec q (snd r1)).
          -- rewrite A2 by lia. destruct (J3 q ltac:(lia)). lia.
          -- apply A3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hb_perm_final : forall perm0,
    let r := hb_permI len alpha minLen (span minLen maxLen) perm0 0 in
    snd r = alpha /\
    (forall q, 0 <= q < alpha -> 0 <= fst r q < alpha) /\
    (forall q, q < 0 \/ alpha <= q -> fst r q = perm0 q).
  Proof.
    intros perm0. cbn zeta.
    cps_destruct (hb_permI_spec (span minLen maxLen) minLen perm0 0 ltac:(lia)) as (A1 & A2 & A3).
    assert (E : snd (hb_permI len alpha minLen (span minLen maxLen) perm0 0) = alpha).
    { rewrite A1, zcount_all; [lia|]. intros k Hk. unfold span.
      specialize (Hlen k ltac:(lia)). destruct (Z.leb_spec minLen (len k)), (Z.ltb_spec (len k) (minLen + Z.of_nat (Z.to_nat (maxLen - minLen + 1)))); cbn; auto; lia. }
    split; [exact E|]. split.
    - intros q Hq. apply A3. lia.
    - intros q Hq. apply A2. lia.
  Qed.

  (* [comment removed for export] *)
  Definition hb_perm_state (perm0 : Z -> Z) (i j : Z) : (Z -> Z) * Z :=
    let r := hb_permI len alpha minLen (Z.to_nat (i - minLen)) perm0 0 in
    hb_permJ len i 0 (Z.to_nat j) (fst r) (snd r).

  Lemma hb_perm_state_pp : forall perm0 i j, minLen <= i -> 0 <= j <= alpha ->
    snd (hb_perm_state perm0 i j) =
      zcount (fun k => (minLen <=? len k) && (len k <? i)) 0 (Z.to_nat alpha) + zcount (fun k => len k =? i) 0 (Z.to_nat j).
  Proof.
    intros. unfold hb_perm_state. cbn zeta.
    pose proof (hb_permJ_spec (Z.to_nat j) i 0) as PJ. cbn zeta in PJ.
    cps_destruct (PJ (fst (hb_permI len alpha minLen (Z.to_nat (i - minLen)) perm0 0)) (snd (hb_permI len alpha minLen (Z.to_nat (i - minLen)) perm0 0))) as (J1 & _ & _).
    rewrite J1. cps_destruct (hb_permI_spec (Z.to_nat (i - minLen)) minLen perm0 0 ltac:(lia)) as (A1 & _ & _).
    rewrite A1. replace (minLen + Z.of_nat (Z.to_nat (i - minLen))) with i by lia. lia.
  Qed.

  Lemma hb_perm_pp_bound : forall perm0 i j, minLen <= i <= maxLen -> 0 <= j <= alpha ->
    0 <= snd (hb_perm_state perm0 i j) <= alpha - (if (j <? alpha) && (len j =? i) then 1 else 0).
  Proof.
    intros perm0 i j Hi Hj. rewrite hb_perm_state_pp by lia.
    pose proof (zcount_bounds (fun k => (minLen <=? len k) && (len k <? i)) 0 (Z.to_nat alpha)).
    pose proof (zcount_bounds (fun k => len k =? i) 0 (Z.to_nat j)).
    split; [lia|].
    assert (M : zcount (fun k => (minLen <=? len k) && (len k <? i)) 0 (Z.to_nat alpha) <= cnt_lt i).
    { unfold cnt_lt. apply zcount_mono. intros k Hk A%andb_prop. tauto. }
    assert (T : zcount (fun k => len k =? i) 0 (Z.to_nat j) + (if (j <? alpha) && (len j =? i) then 1 else 0) <= cnt_eq i).
    { unfold cnt_eq. replace (Z.to_nat alpha) with (Z.to_nat j + Z.to_nat (alpha - j))%nat by lia.
      rewrite zcount_app. destruct (Z.ltb_spec j alpha); cbn [andb].
      - destruct (Z.eqb_spec (len j) i).
        + pose proof (zcount_true1 (fun k => len k =? i) (0 + Z.of_nat (Z.to_nat j)) (Z.to_nat (alpha - j)) j ltac:(lia) ltac:(now apply Z.eqb_eq)). lia.
        + pose proof (zcount_bounds (fun k => len k =? i) (0 + Z.of_nat (Z.to_nat j)) (Z.to_nat (alpha - j))). lia.
      - pose proof (zcount_bounds (fun k => len k =? i) (0 + Z.of_nat (Z.to_nat j)) (Z.to_nat (alpha - j))). lia. }
    pose proof (cnt_lt_succ_le i). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fill0_spec : forall n f i k,
    fill0 f i n k = if (i <=? k) && (k <? i + Z.of_nat n) then 0 else f k.
  Proof.
    induction n as [|n IH]; intros.
    - cbn [fill0]. destruct (Z.leb_spec i k), (Z.ltb_spec k (i + Z.of_nat 0)); cbn; auto; lia.
    - rewrite fill0_S, IH, zfupd_eq.
      destruct (Z.leb_spec (i + 1) k), (Z.ltb_spec k (i + 1 + Z.of_nat n)), (Z.leb_spec i k),
        (Z.ltb_spec k (i + Z.of_nat (S n))), (Z.eqb_spec k i); cbn; auto; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hb_count_spec : forall n i base k,
    hb_count len i n base k = base k + zcount (fun q => len q + 1 =? k) i n.
  Proof.
    induction n as [|n IH]; intros.
    - cbn. lia.
    - rewrite hb_count_S, IH, zcount_cons, zfupd_eq.
      destruct (Z.eqb_spec k (len i + 1)), (Z.eqb_spec (len i + 1) k); subst; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hb_accum_spec : forall n base k,
    hb_accum 1 n base k = if (0 <=? k) && (k <=? Z.of_nat n) then zsum base 0 (Z.to_nat (k + 1)) else base k.
  Proof.
    induction n as [|n IH]; intros.
    - cbn [hb_accum]. destruct (Z.leb_spec 0 k), (Z.leb_spec k (Z.of_nat 0)); cbn [andb]; auto.
      replace k with 0 by lia. reflexivity.
    - rewrite hb_accum_snoc. cbn zeta. rewrite zfupd_eq, !IH.
      destruct (Z.eqb_spec k (1 + Z.of_nat n)).
      + subst k. destruct (Z.leb_spec 0 (1 + Z.of_nat n)), (Z.leb_spec (1 + Z.of_nat n) (Z.of_nat (S n))),
          (Z.leb_spec (1 + Z.of_nat n) (Z.of_nat n)), (Z.leb_spec 0 (1 + Z.of_nat n - 1)), (Z.leb_spec (1 + Z.of_nat n - 1) (Z.of_nat n)); cbn [andb]; try lia.
        replace (Z.to_nat (1 + Z.of_nat n + 1)) with (S (S n)) by lia.
        replace (Z.to_nat (1 + Z.of_nat n - 1 + 1)) with (S n) by lia.
        rewrite (zsum_S base 0 (S n)). rewrite Z.add_comm. f_equal. f_equal. lia.
      + destruct (Z.leb_spec 0 k), (Z.leb_spec k (Z.of_nat (S n))), (Z.leb_spec k (Z.of_nat n)); cbn [andb]; auto; lia.
  Qed.

  (* [comment removed for export] *)
  Definition base3 (base0 : Z -> Z) : Z -> Z :=
    hb_accum 1 (Z.to_nat (BZ_MAX_CODE_LEN - 1))
      (hb_count len 0 (Z.to_nat alpha) (fill0 base0 0 (Z.to_nat BZ_MAX_CODE_LEN))).

  Lemma base3_fold : forall base0,
    hb_accum 1 (Z.to_nat (BZ_MAX_CODE_LEN - 1))
      (hb_count len 0 (Z.to_nat alpha) (fill0 base0 0 (Z.to_nat BZ_MAX_CODE_LEN))) = base3 base0.
  Proof. reflexivity. Qed.

  Lemma count_shift : forall q, zcount (fun j => len j + 1 =? q) 0 (Z.to_nat alpha) = cnt_eq (q - 1).
  Proof.
    intros. unfold cnt_eq. apply zcount_ext. intros k Hk.
    destruct (Z.eqb_spec (len k + 1) q), (Z.eqb_spec (len k) (q - 1)); auto; lia.
  Qed.

  Lemma zsum_cnt_eq : forall m, zsum (fun q => cnt_eq (q - 1)) 0 m = cnt_lt (Z.of_nat m - 1) - cnt_lt (-1).
  Proof.
    induction m as [|m IH].
    - cbn [zsum Z.of_nat]. replace (0 - 1) with (-1) by lia. lia.
    - rewrite zsum_S, IH. cbn beta. replace (Z.of_nat (S m) - 1) with ((Z.of_nat m - 1) + 1) by lia.
      rewrite (cnt_lt_succ (Z.of_nat m - 1)). replace (0 + Z.of_nat m - 1) with (Z.of_nat m - 1) by lia. lia.
  Qed.

  Lemma base3_spec : forall base0 k,
    base3 base0 k = if (0 <=? k) && (k <? BZ_MAX_CODE_LEN) then cnt_lt k else base0 k.
  Proof.
    intros. unfold base3. rewrite hb_accum_spec. pose proof BZ_MAX_CODE_LEN_eq.
    destruct (Z.leb_spec 0 k), (Z.leb_spec k (Z.of_nat (Z.to_nat (BZ_MAX_CODE_LEN - 1)))), (Z.ltb_spec k BZ_MAX_CODE_LEN); cbn [andb]; try lia.
    - rewrite (zsum_ext _ (fun q => cnt_eq (q - 1))).
      + rewrite zsum_cnt_eq, (cnt_lt_low (-1)) by lia. replace (Z.of_nat (Z.to_nat (k + 1)) - 1) with k by lia. lia.
      + intros q Hq. rewrite hb_count_spec, fill0_spec, count_shift.
        destruct (Z.leb_spec 0 q), (Z.ltb_spec q (0 + Z.of_nat (Z.to_nat BZ_MAX_CODE_LEN))); cbn [andb]; lia.
    - rewrite hb_count_spec, fill0_spec, zcount_false.
      + destruct (Z.leb_spec 0 k), (Z.ltb_spec k (0 + Z.of_nat (Z.to_nat BZ_MAX_CODE_LEN))); cbn [andb]; lia.
      + intros q Hq. specialize (Hlen q ltac:(lia)). destruct (Z.eqb_spec (len q + 1) k); auto; lia.
    - rewrite hb_count_spec, fill0_spec, zcount_false.
      + destruct (Z.leb_spec 0 k); cbn [andb]; lia.
      + intros q Hq. specialize (Hlen q ltac:(lia)). destruct (Z.eqb_spec (len q + 1) k); auto; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hb_count_step_facts : forall base0 n, (n <= Z.to_nat alpha)%nat ->
    let b := hb_count len 0 n (fill0 base0 0 (Z.to_nat BZ_MAX_CODE_LEN)) in
    (n < Z.to_nat alpha)%nat ->
    2 <= len (Z.of_nat n) + 1 <= 21 /\ 0 <= b (len (Z.of_nat n) + 1) <= Z.of_nat n.
  Proof.
    intros base0 n Hn. cbn zeta. intros Hlt.
    pose proof (Hlen (Z.of_nat n) ltac:(lia)).
    split; [lia|]. rewrite hb_count_spec, fill0_spec. pose proof BZ_MAX_CODE_LEN_eq.
    pose proof (zcount_bounds (fun q => len q + 1 =? len (Z.of_nat n) + 1) 0 n).
    destruct (Z.leb_spec 0 (len (Z.of_nat n) + 1)), (Z.ltb_spec (len (Z.of_nat n) + 1) (0 + Z.of_nat (Z.to_nat BZ_MAX_CODE_LEN))); cbn [andb]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hb_accum_step_facts : forall base0 m, (m < Z.to_nat (BZ_MAX_CODE_LEN - 1))%nat ->
    let b2 := hb_count len 0 (Z.to_nat alpha) (fill0 base0 0 (Z.to_nat BZ_MAX_CODE_LEN)) in
    let b := hb_accum 1 m b2 in
    0 <= b (1 + Z.of_nat m) <= alpha /\ 0 <= b (1 + Z.of_nat m - 1) <= alpha /\
    0 <= b (1 + Z.of_nat m) + b (1 + Z.of_nat m - 1) <= alpha.
  Proof.
    intros base0 m Hm. cbn zeta. pose proof BZ_MAX_CODE_LEN_eq. rewrite !hb_accum_spec.
    assert (B2 : forall q, 0 <= q < 23 -> hb_count len 0 (Z.to_nat alpha) (fill0 base0 0 (Z.to_nat BZ_MAX_CODE_LEN)) q = cnt_eq (q - 1)).
    { intros q Hq. rewrite hb_count_spec, fill0_spec, count_shift.
      destruct (Z.leb_spec 0 q), (Z.ltb_spec q (0 + Z.of_nat (Z.to_nat BZ_MAX_CODE_LEN))); cbn [andb]; lia. }
    assert (SUM : forall j, 0 <= j < 23 -> zsum (hb_count len 0 (Z.to_nat alpha) (fill0 base0 0 (Z.to_nat BZ_MAX_CODE_LEN))) 0 (Z.to_nat (j + 1)) = cnt_lt j).
    { intros j Hj. rewrite (zsum_ext _ (fun q => cnt_eq (q - 1))) by (intros; apply B2; lia).
      rewrite zsum_cnt_eq, (cnt_lt_low (-1)) by lia. replace (Z.of_nat (Z.to_nat (j + 1)) - 1) with j by lia. lia. }
    destruct (Z.leb_spec 0 (1 + Z.of_nat m)), (Z.leb_spec (1 + Z.of_nat m) (Z.of_nat m)),
      (Z.leb_spec 0 (1 + Z.of_nat m - 1)), (Z.leb_spec (1 + Z.of_nat m - 1) (Z.of_nat m)); cbn [andb]; try lia.
    rewrite B2, SUM by lia.
    replace (1 + Z.of_nat m - 1 - 1 + 1) with (Z.of_nat m) by lia. replace (1 + Z.of_nat m - 1) with (Z.of_nat m) by lia.
    pose proof (cnt_eq_range (Z.of_nat m)). pose proof (cnt_lt_range (Z.of_nat m)).
    pose proof (cnt_lt_succ_le (Z.of_nat m)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma hb_limit_spec : forall base0 limit1 d, Z.of_nat d <= maxLen - minLen + 1 ->
    let r := hb_limit (base3 base0) minLen d limit1 0 in
    snd r = first (minLen + Z.of_nat d) /\
    (forall k, minLen <= k < minLen + Z.of_nat d -> fst r k = first k + cnt_eq k - 1) /\
    (forall k, k < minLen \/ minLen + Z.of_nat d <= k -> fst r k = limit1 k).
  Proof.
    intros base0 limit1 d. induction d as [|d IH]; intros Hd; cbn zeta.
    - cbn [hb_limit fst snd]. rewrite Z.add_0_r, first_minLen. split; [reflexivity|]. split; [intros; lia| intros; reflexivity].
    - rewrite hb_limit_snoc. cbn zeta. cps_destruct (IH ltac:(lia)) as (A1 & A2 & A3).
      rewrite A1. rewrite !base3_spec. pose proof BZ_MAX_CODE_LEN_eq.
      destruct (Z.leb_spec 0 (minLen + Z.of_nat d + 1)), (Z.ltb_spec (minLen + Z.of_nat d + 1) BZ_MAX_CODE_LEN),
        (Z.leb_spec 0 (minLen + Z.of_nat d)), (Z.ltb_spec (minLen + Z.of_nat d) BZ_MAX_CODE_LEN); cbn [andb fst snd]; try lia.
      rewrite cnt_lt_succ. split.
      + rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
        replace (minLen + Z.of_nat (S d)) with (minLen + Z.of_nat d + 1) by lia. rewrite first_succ by lia. lia.
      + split.
        * intros k Hk. rewrite zfupd_eq. destruct (Z.eqb_spec k (minLen + Z.of_nat d)).
          -- subst k. lia.
          -- apply A2. lia.
        * intros k Hk. rewrite zfupd_other by lia. apply A3. lia.
  Qed.

  Lemma hb_base_spec : forall base0 limit d, Z.of_nat d <= maxLen - minLen ->
    (forall k, minLen <= k <= maxLen -> limit k = first k + cnt_eq k - 1) ->
    let b := hb_base limit (minLen + 1) d (base3 base0) in
    (forall k, minLen + 1 <= k < minLen + 1 + Z.of_nat d -> b k = first k - cnt_lt k) /\
    (forall k, k < minLen + 1 \/ minLen + 1 + Z.of_nat d <= k -> b k = base3 base0 k).
  Proof.
    intros base0 limit d. induction d as [|d IH]; intros Hd HL; cbn zeta.
    - cbn [hb_base]. split; [intros; lia| intros; reflexivity].
    - rewrite hb_base_snoc. cbn zeta. destruct (IH ltac:(lia) HL) as (A1 & A2). split.
      + intros k Hk. rewrite zfupd_eq. destruct (Z.eqb_spec k (minLen + 1 + Z.of_nat d)).
        * subst k. rewrite A2 by lia. rewrite HL by lia. rewrite base3_spec. pose proof BZ_MAX_CODE_LEN_eq.
          destruct (Z.leb_spec 0 (minLen + 1 + Z.of_nat d)), (Z.ltb_spec (minLen + 1 + Z.of_nat d) BZ_MAX_CODE_LEN); cbn [andb]; try lia.
          rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
          replace (minLen + 1 + Z.of_nat d) with (minLen + Z.of_nat d + 1) by lia.
          rewrite first_succ by lia. replace (minLen + Z.of_nat d + 1 - 1) with (minLen + Z.of_nat d) by lia. lia.
        * apply A1. lia.
      + intros k Hk. rewrite zfupd_other by lia. apply A2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition hb_limitv (k : Z) : Z := first k + cnt_eq k - 1.     (* [comment removed for export] *)
  Definition hb_basev  (k : Z) : Z := first k - cnt_lt k.         (* [comment removed for export] *)

  Theorem hb_create_spec : forall limit0 base0 perm0,
    let '(limit, base, perm) := hb_create limit0 base0 perm0 len minLen maxLen alpha in
    (forall k, minLen <= k <= maxLen -> limit k = hb_limitv k /\ base k = hb_basev k) /\
    (forall k, 0 <= k < BZ_MAX_CODE_LEN -> ~ (minLen <= k <= maxLen) -> limit k = 0 /\ base k = cnt_lt k) /\
    (forall k, ~ (0 <= k < BZ_MAX_CODE_LEN) -> limit k = limit0 k /\ base k = base0 k) /\
    (forall q, 0 <= q < alpha -> 0 <= perm q < alpha) /\
    (forall q, ~ (0 <= q < alpha) -> perm q = perm0 q).
  Proof.
    intros limit0 base0 perm0. unfold hb_create.
    cps_destruct (hb_perm_final perm0) as (P1 & P2 & P3).
    rewrite (base3_fold base0).
    cps_destruct (hb_limit_spec base0 (fill0 limit0 0 (Z.to_nat BZ_MAX_CODE_LEN)) (span minLen maxLen) ltac:(unfold span; lia)) as (L1 & L2 & L3).
    set (lv := hb_limit (base3 base0) minLen (span minLen maxLen) (fill0 limit0 0 (Z.to_nat BZ_MAX_CODE_LEN)) 0) in *.
    assert (HL : forall k, minLen <= k <= maxLen -> fst lv k = first k + cnt_eq k - 1)
      by (intros; apply L2; unfold span; lia).
    destruct (hb_base_spec base0 (fst lv) (span (minLen + 1) maxLen) ltac:(unfold span; lia) HL) as (B1 & B2).
    cbn zeta in *. unfold span in *.
    split; [|split; [|split; [|split]]].
    - intros k Hk. split. { apply HL. lia. }
      unfold hb_basev. destruct (Z.eq_dec k minLen).
      + subst k. rewrite B2 by lia. rewrite base3_spec. pose proof BZ_MAX_CODE_LEN_eq.
        destruct (Z.leb_spec 0 minLen), (Z.ltb_spec minLen BZ_MAX_CODE_LEN); cbn [andb]; try lia.
        rewrite first_minLen, cnt_lt_low; lia.
      + apply B1. lia.
    - intros k Hk Hn. split.
      + rewrite L3 by lia. rewrite fill0_spec. pose proof BZ_MAX_CODE_LEN_eq.
        destruct (Z.leb_spec 0 k), (Z.ltb_spec k (0 + Z.of_nat (Z.to_nat BZ_MAX_CODE_LEN))); cbn [andb]; lia.
      + rewrite B2 by lia. rewrite base3_spec. pose proof BZ_MAX_CODE_LEN_eq.
        destruct (Z.leb_spec 0 k), (Z.ltb_spec k BZ_MAX_CODE_LEN); cbn [andb]; lia.
    - intros k Hk. pose proof BZ_MAX_CODE_LEN_eq. split.
      + rewrite L3 by lia. rewrite fill0_spec. destruct (Z.leb_spec 0 k), (Z.ltb_spec k (0 + Z.of_nat (Z.to_nat BZ_MAX_CODE_LEN))); cbn [andb]; lia.
      + rewrite B2 by lia. rewrite base3_spec. destruct (Z.leb_spec 0 k), (Z.ltb_spec k BZ_MAX_CODE_LEN); cbn [andb]; lia.
    - exact P2.
    - intros q Hq. apply P3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hb_limitv_range : forall k, minLen <= k <= maxLen -> -1 <= hb_limitv k < 2 ^ 28.
  Proof. intros. unfold hb_limitv. pose proof (first_plus_lt_2p28 k ltac:(lia)). lia. Qed.
  Lemma hb_basev_range : forall k, minLen <= k <= maxLen -> - 258 <= hb_basev k < 2 ^ 29.
  Proof. intros. unfold hb_basev. pose proof (first_lt_2p29 k ltac:(lia)). pose proof (cnt_lt_range k). lia. Qed.

  (* [comment removed for export] *)
  Definition decJ (zn zvec : Z) : Prop := minLen <= zn <= 21 /\ first zn <= zvec < 2 ^ zn.

  Lemma decJ_init : forall zvec, 0 <= zvec < 2 ^ minLen -> decJ minLen zvec.
  Proof. intros. unfold decJ. rewrite first_minLen. lia. Qed.

  Lemma decJ_zvec_range : forall zn zvec, decJ zn zvec -> 0 <= zvec < 2 ^ 21.
  Proof.
    intros zn zvec [A B]. pose proof (first_nonneg zn).
    assert (2 ^ zn <= 2 ^ 21) by (apply Z.pow_le_mono_r; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma decJ_step : forall limit0 base0 perm0 zn zvec b,
    let '(limit, base, perm) := hb_create limit0 base0 perm0 len minLen maxLen alpha in
    decJ zn zvec -> zn <= 20 -> limit zn < zvec -> 0 <= b <= 1 ->
    decJ (zn + 1) (Z.lor (Z.shiftl zvec 1) b) /\ Z.lor (Z.shiftl zvec 1) b = 2 * zvec + b.
  Proof.
    intros limit0 base0 perm0 zn zvec b.
    pose proof (hb_create_spec limit0 base0 perm0) as SP.
    destruct (hb_create limit0 base0 perm0 len minLen maxLen alpha) as [[limit base] perm].
    cps_destruct SP as (S1 & S2 & S3 & S4 & S5).
    intros [J1 J2] Hzn Hgt Hb.
    assert (E : Z.lor (Z.shiftl zvec 1) b = 2 * zvec + b) by (apply lor_shiftl1_bit; pose proof (first_nonneg zn); lia).
    split; [|exact E]. rewrite E. unfold decJ. split; [lia|].
    rewrite first_succ by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia.
    destruct (Z_le_gt_dec zn maxLen).
    - destruct (S1 zn ltac:(lia)) as [L _]. rewrite L in Hgt. unfold hb_limitv in Hgt. lia.
    - destruct (S2 zn ltac:(pose proof BZ_MAX_CODE_LEN_eq; lia) ltac:(lia)) as [L _]. rewrite L in Hgt.
      rewrite cnt_eq_out by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem decJ_break : forall limit0 base0 perm0 zn zvec,
    let '(limit, base, perm) := hb_create limit0 base0 perm0 len minLen maxLen alpha in
    decJ zn zvec -> zn <= 20 -> zvec <= limit zn ->
    minLen <= zn <= maxLen /\
    0 <= zvec - base zn < alpha /\
    0 <= perm (zvec - base zn) < alpha /\
    - 2 ^ 30 < base zn < 2 ^ 30.
  Proof.
    intros limit0 base0 perm0 zn zvec.
    pose proof (hb_create_spec limit0 base0 perm0) as SP.
    destruct (hb_create limit0 base0 perm0 len minLen maxLen alpha) as [[limit base] perm].
    cps_destruct SP as (S1 & S2 & S3 & S4 & S5).
    intros [J1 J2] Hzn Hle.
    destruct (Z_le_gt_dec zn maxLen).
    - destruct (S1 zn ltac:(lia)) as [L B]. rewrite L in Hle. rewrite B. unfold hb_limitv, hb_basev in *.
      pose proof (cnt_lt_succ_le zn). pose proof (cnt_lt_range zn). pose proof (hb_basev_range zn ltac:(lia)).
      unfold hb_basev in *.
      assert (R : 0 <= zvec - (first zn - cnt_lt zn) < alpha) by lia.
      split; [lia|]. split; [exact R|]. split; [apply S4; exact R| lia].
    - exfalso. destruct (S2 zn ltac:(pose proof BZ_MAX_CODE_LEN_eq; lia) ltac:(lia)) as [L _]. rewrite L in Hle.
      pose proof (first_ge_cnt_lt zn ltac:(lia)). rewrite cnt_lt_high in * by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dec_limit_range : forall limit0 base0 perm0 zn,
    let '(limit, base, perm) := hb_create limit0 base0 perm0 len minLen maxLen alpha in
    minLen <= zn <= 20 -> -1 <= limit zn < 2 ^ 28.
  Proof.
    intros limit0 base0 perm0 zn.
    pose proof (hb_create_spec limit0 base0 perm0) as SP.
    destruct (hb_create limit0 base0 perm0 len minLen maxLen alpha) as [[limit base] perm].
    cps_destruct SP as (S1 & S2 & S3 & S4 & S5). intros Hzn.
    destruct (Z_le_gt_dec zn maxLen).
    - destruct (S1 zn ltac:(lia)) as [L _]. rewrite L. apply hb_limitv_range. lia.
    - destruct (S2 zn ltac:(pose proof BZ_MAX_CODE_LEN_eq; lia) ltac:(lia)) as [L _]. rewrite L. lia.
  Qed.

End Hb.
