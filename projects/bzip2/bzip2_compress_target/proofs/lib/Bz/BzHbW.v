(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section HbW.
  Variables (len : Z -> Z) (alpha minLen maxLen : Z).
  Hypothesis Halpha : 1 <= alpha <= 258.
  Hypothesis Hmm : 1 <= minLen /\ minLen <= maxLen <= 20.
  Hypothesis Hlen : forall j, 0 <= j < alpha -> minLen <= len j <= maxLen.

  (* [comment removed for export] *)
  Local Ltac feed F := repeat first [ specialize (F Halpha) | specialize (F Hmm) | specialize (F Hlen) ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hbm_perm (perm0 : Z -> Z) : Z -> Z := fst (hb_permI len alpha minLen (span minLen maxLen) perm0 0).
  Definition hbm_base1 (base0 : Z -> Z) : Z -> Z := fill0 base0 0 23.
  Definition hbm_base2 (base0 : Z -> Z) : Z -> Z := hb_count len 0 (Z.to_nat alpha) (hbm_base1 base0).
  Definition hbm_base3 (base0 : Z -> Z) : Z -> Z := hb_accum 1 22 (hbm_base2 base0).
  Definition hbm_limit1 (limit0 : Z -> Z) : Z -> Z := fill0 limit0 0 23.
  Definition hbm_lv (limit0 base0 : Z -> Z) : (Z -> Z) * Z :=
    hb_limit (hbm_base3 base0) minLen (span minLen maxLen) (hbm_limit1 limit0) 0.
  Definition hbm_limit (limit0 base0 : Z -> Z) : Z -> Z := fst (hbm_lv limit0 base0).
  Definition hbm_base (limit0 base0 : Z -> Z) : Z -> Z :=
    hb_base (hbm_limit limit0 base0) (minLen + 1) (span (minLen + 1) maxLen) (hbm_base3 base0).

  Lemma hbm_base3_eq : forall base0, hbm_base3 base0 = base3 len alpha base0.
  Proof.
    intros. unfold hbm_base3, hbm_base2, hbm_base1, base3.
    rewrite BZ_MAX_CODE_LEN_eq. reflexivity.
  Qed.

  Lemma hb_create_pieces : forall limit0 base0 perm0,
    hb_create limit0 base0 perm0 len minLen maxLen alpha =
    (hbm_limit limit0 base0, hbm_base limit0 base0, hbm_perm perm0).
  Proof.
    intros. unfold hb_create, hbm_base, hbm_limit, hbm_lv, hbm_limit1, hbm_base3, hbm_base2, hbm_base1, hbm_perm.
    rewrite BZ_MAX_CODE_LEN_eq. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma hbm_base3_val : forall base0 k, 0 <= k < 23 -> hbm_base3 base0 k = cnt_lt len alpha k.
  Proof.
    intros. rewrite hbm_base3_eq. pose proof (base3_spec len alpha minLen maxLen) as F. feed F.
    rewrite F, BZ_MAX_CODE_LEN_eq. destruct (Z.leb_spec 0 k), (Z.ltb_spec k 23); cbn; lia.
  Qed.

  (* [comment removed for export] *)

  Lemma cnt_lt_range' : forall k, 0 <= cnt_lt len alpha k <= alpha.
  Proof. intros. pose proof (cnt_lt_range len alpha) as F. feed F. apply F. Qed.
  Lemma cnt_eq_range' : forall k, 0 <= cnt_eq len alpha k <= alpha.
  Proof. intros. pose proof (cnt_eq_range len alpha) as F. feed F. apply F. Qed.
  Lemma cnt_lt_succ' : forall k, cnt_lt len alpha (k + 1) = cnt_lt len alpha k + cnt_eq len alpha k.
  Proof. intros. pose proof (cnt_lt_succ len alpha) as F. feed F. apply F. Qed.
  Lemma first_succ' : forall i, minLen <= i -> first len alpha minLen (i + 1) = 2 * (first len alpha minLen i + cnt_eq len alpha i).
  Proof. intros. pose proof (first_succ len alpha minLen) as F. feed F. apply F. lia. Qed.
  Lemma first_lt_2p29' : forall i, minLen <= i <= 21 -> 0 <= first len alpha minLen i < 2 ^ 29.
  Proof. intros. pose proof (first_lt_2p29 len alpha minLen maxLen) as F. feed F. apply F. lia. Qed.
  Lemma first_plus_lt_2p28' : forall i, minLen <= i <= 20 -> 0 <= first len alpha minLen i + cnt_eq len alpha i < 2 ^ 28.
  Proof. intros. pose proof (first_plus_lt_2p28 len alpha minLen maxLen) as F. feed F. apply F. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma hbw_perm_store : forall perm0 i j,
    minLen <= i <= maxLen -> 0 <= j < alpha -> len j = i ->
    0 <= snd (hb_perm_state len alpha minLen perm0 i j) <= alpha - 1.
  Proof.
    intros perm0 i j Hi Hj Hl.
    pose proof (hb_perm_pp_bound len alpha minLen maxLen) as B. feed B. specialize (B perm0 i j ltac:(lia) ltac:(lia)).
    replace (j <? alpha) with true in B by (symmetry; apply Z.ltb_lt; lia).
    replace (len j =? i) with true in B by (symmetry; apply Z.eqb_eq; lia). cbn in B. lia.
  Qed.

  Lemma hbw_perm_pp_range : forall perm0 i j,
    minLen <= i <= maxLen -> 0 <= j <= alpha ->
    0 <= snd (hb_perm_state len alpha minLen perm0 i j) <= alpha.
  Proof.
    intros perm0 i j Hi Hj.
    pose proof (hb_perm_pp_bound len alpha minLen maxLen) as B. feed B. specialize (B perm0 i j ltac:(lia) ltac:(lia)).
    destruct ((j <? alpha) && (len j =? i)); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hbw_count_step : forall base0 k, 0 <= k < alpha ->
    let b := hb_count len 0 (Z.to_nat k) (hbm_base1 base0) in
    2 <= len k + 1 <= 21 /\ 0 <= b (len k + 1) <= k.
  Proof.
    intros base0 k Hk. cbn zeta.
    pose proof (hb_count_step_facts len alpha minLen maxLen) as F. feed F. specialize (F base0 (Z.to_nat k) ltac:(lia)).
    cbn zeta in F. unfold hbm_base1. rewrite BZ_MAX_CODE_LEN_nat in F. rewrite Z2Nat.id in F by lia.
    apply F. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hbw_accum_step : forall base0 m, 0 <= m < 22 ->
    let b := hb_accum 1 (Z.to_nat m) (hbm_base2 base0) in
    0 <= b (1 + m) <= alpha /\ 0 <= b (1 + m - 1) <= alpha /\ 0 <= b (1 + m) + b (1 + m - 1) <= alpha.
  Proof.
    intros base0 m Hm. cbn zeta.
    pose proof (hb_accum_step_facts len alpha minLen maxLen) as F. feed F. specialize (F base0 (Z.to_nat m)).
    cbn zeta in F. rewrite BZ_MAX_CODE_LEN_eq, !Z2Nat.id in F by lia. unfold hbm_base2, hbm_base1.
    change (Z.to_nat 23) with 23%nat in F. apply F. change (Z.to_nat (23 - 1)) with 22%nat. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hbw_limit_step : forall limit0 base0 d, minLen + Z.of_nat d <= maxLen ->
    let r := hb_limit (hbm_base3 base0) minLen d (hbm_limit1 limit0) 0 in
    let i := minLen + Z.of_nat d in
    snd r = first len alpha minLen i /\
    0 <= first len alpha minLen i < 2 ^ 29 /\
    hbm_base3 base0 i = cnt_lt len alpha i /\ hbm_base3 base0 (i + 1) = cnt_lt len alpha (i + 1) /\
    cnt_lt len alpha (i + 1) = cnt_lt len alpha i + cnt_eq len alpha i /\
    0 <= cnt_lt len alpha i <= alpha /\ 0 <= cnt_eq len alpha i <= alpha /\
    0 <= first len alpha minLen i + cnt_eq len alpha i < 2 ^ 28 /\
    Z.shiftl (first len alpha minLen i + cnt_eq len alpha i) 1 = first len alpha minLen (i + 1).
  Proof.
    intros limit0 base0 d Hd. cbn zeta.
    pose proof (hb_limit_spec len alpha minLen maxLen) as F. feed F.
    cps_destruct (F base0 (hbm_limit1 limit0) d ltac:(lia)) as (A1 & A2 & A3). clear F.
    rewrite <- hbm_base3_eq in A1. split; [exact A1|].
    split; [apply first_lt_2p29'; lia|].
    rewrite !hbm_base3_val by lia.
    split; [reflexivity|]. split; [reflexivity|].
    split; [apply cnt_lt_succ'|].
    split; [apply cnt_lt_range'|]. split; [apply cnt_eq_range'|].
    split; [apply first_plus_lt_2p28'; lia|].
    rewrite Z.shiftl_mul_pow2, Z.pow_1_r, first_succ' by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hbm_limit_val_in : forall limit0 base0 k, minLen <= k <= maxLen ->
    hbm_limit limit0 base0 k = first len alpha minLen k + cnt_eq len alpha k - 1.
  Proof.
    intros. unfold hbm_limit, hbm_lv.
    pose proof (hb_limit_spec len alpha minLen maxLen) as F. feed F.
    cps_destruct (F base0 (hbm_limit1 limit0) (span minLen maxLen) ltac:(unfold span; lia)) as (A1 & A2 & A3). clear F.
    rewrite <- hbm_base3_eq in A2. apply A2. unfold span. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hbw_base_step : forall limit0 base0 d, minLen + 1 + Z.of_nat d <= maxLen ->
    let b := hb_base (hbm_limit limit0 base0) (minLen + 1) d (hbm_base3 base0) in
    let i := minLen + 1 + Z.of_nat d in
    hbm_limit limit0 base0 (i - 1) = first len alpha minLen (i - 1) + cnt_eq len alpha (i - 1) - 1 /\
    0 <= first len alpha minLen (i - 1) + cnt_eq len alpha (i - 1) < 2 ^ 28 /\
    b i = cnt_lt len alpha i /\ 0 <= cnt_lt len alpha i <= alpha.
  Proof.
    intros limit0 base0 d Hd. cbn zeta.
    split; [apply hbm_limit_val_in; lia|].
    split; [apply first_plus_lt_2p28'; lia|].
    pose proof (hb_base_spec len alpha minLen maxLen) as F. feed F.
    destruct (F base0 (hbm_limit limit0 base0) d ltac:(lia) ltac:(intros; apply hbm_limit_val_in; lia)) as (B1 & B2). clear F.
    rewrite <- hbm_base3_eq in B2. rewrite B2 by lia. rewrite hbm_base3_val by lia.
    split; [reflexivity| apply cnt_lt_range'].
  Qed.
End HbW.
