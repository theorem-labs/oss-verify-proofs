(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia Bool List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition two64 : Z := 2 ^ 64.

(* [comment removed for export] *)
Definition smear_step (a : Z) (n : Z) : Z := Z.lor a (Z.shiftr a n).
Definition smear (x : Z) : Z :=
  smear_step (smear_step (smear_step (smear_step (smear_step (smear_step x 1) 2) 4) 8) 16) 32.

(* [comment removed for export] *)
Definition covers (x a : Z) (w : Z) : Prop :=
  forall j, 0 <= j -> Z.testbit a j = true <-> exists d, 0 <= d < w /\ Z.testbit x (j + d) = true.

Lemma covers_0 x : 0 <= x -> covers x x 1.
Proof.
  intros Hx j Hj. split.
  - intros H. exists 0. split; [lia|]. rewrite Z.add_0_r. exact H.
  - intros (d & Hd & H). replace (j + d) with j in H by lia. exact H.
Qed.

Lemma covers_step x a w : 0 < w -> covers x a w -> covers x (smear_step a w) (2 * w).
Proof.
  intros Hw HC j Hj. unfold smear_step. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite orb_true_iff. split.
  - intros [H|H].
    + apply HC in H as (d & Hd & H); [|lia]. exists d. split; [lia|exact H].
    + apply HC in H as (d & Hd & H); [|lia]. exists (w + d). split; [lia|]. replace (j + (w + d)) with (j + w + d) by lia. exact H.
  - intros (d & Hd & H). destruct (Z_lt_le_dec d w).
    + left. apply HC; [lia|]. exists d. split; [lia|exact H].
    + right. apply HC; [lia|]. exists (d - w). split; [lia|]. replace (j + w + (d - w)) with (j + d) by lia. exact H.
Qed.

Lemma covers_smear x : 0 <= x -> covers x (smear x) 64.
Proof.
  intros Hx. unfold smear.
  change 64 with (2 * (2 * (2 * (2 * (2 * (2 * 1)))))).
  apply covers_step; [lia|]. apply covers_step; [lia|]. apply covers_step; [lia|].
  apply covers_step; [lia|]. apply covers_step; [lia|]. apply covers_step; [lia|].
  apply covers_0. exact Hx.
Qed.

Lemma smear_step_nonneg a n : 0 <= a -> 0 <= smear_step a n.
Proof. intros. unfold smear_step. apply Z.lor_nonneg. split; [lia|]. apply Z.shiftr_nonneg. lia. Qed.

Lemma smear_nonneg x : 0 <= x -> 0 <= smear x.
Proof. intros. unfold smear. repeat apply smear_step_nonneg. lia. Qed.

(* [comment removed for export] *)
Lemma smear_eq x K : 0 <= K < 64 -> 2 ^ K <= x < 2 ^ (K + 1) -> smear x = Z.ones (K + 1).
Proof.
  intros HK Hx.
  assert (Hx0 : 0 < x) by (pose proof (Z.pow_pos_nonneg 2 K); lia).
  assert (HL : Z.log2 x = K) by (apply Z.log2_unique; [lia|]; rewrite <- Z.add_1_r; lia).
  pose proof (covers_smear x ltac:(lia)) as HC.
  apply Z.bits_inj'. intros j Hj. rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec j (K + 1)).
  - apply HC; [lia|]. exists (K - j). split; [lia|]. replace (j + (K - j)) with K by lia. rewrite <- HL. apply Z.bit_log2. lia.
  - destruct (Z.testbit (smear x) j) eqn:T; [|reflexivity]. exfalso.
    apply HC in T as (d & Hd & T); [|lia]. rewrite Z.bits_above_log2 in T; [discriminate|lia|]. rewrite HL. lia.
Qed.

(* [comment removed for export] *)
Definition rd (t : Z) : Z := t mod two64.

Definition M55 : Z := 0x5555555555555555.
Definition M33 : Z := 0x3333333333333333.
Definition M0F : Z := 0x0f0f0f0f0f0f0f0f.
Definition M01 : Z := 0x0101010101010101.
Definition MFF : Z := 0xffffffffffffffff.    (* [comment removed for export] *)

Definition stepw (a : Z) (n : Z) : Z := Z.lor (rd a) (rd (Z.shiftr (rd a) n)).
Definition smearw (x : Z) : Z := stepw (stepw (stepw (stepw (stepw (stepw x 1) 2) 4) 8) 16) 32.

(* [comment removed for export] *)
Definition tailw (s : Z) : Z :=
  let n  := Z.lxor (rd s) MFF in                                   (* [comment removed for export] *)
  let a6 := Z.shiftr (rd n) 1 in                                   (* [comment removed for export] *)
  let a2 := Z.land (rd a6) (rd M55) in                             (* [comment removed for export] *)
  let d  := rd n - rd a2 in                                        (* [comment removed for export] *)
  let a2 := Z.shiftr (rd d) 2 in                                   (* [comment removed for export] *)
  let e1 := Z.land (rd d) (rd M33) in                              (* [comment removed for export] *)
  let e2 := Z.land (rd a2) (rd M33) in                             (* [comment removed for export] *)
  let f  := rd e1 + rd e2 in                                       (* [comment removed for export] *)
  let a2 := Z.shiftr (rd f) 4 in                                   (* [comment removed for export] *)
  let g  := rd f + rd a2 in                                        (* [comment removed for export] *)
  let h  := Z.land (rd g) (rd M0F) in                              (* [comment removed for export] *)
  let p  := rd h * rd M01 in                                       (* [comment removed for export] *)
  Z.shiftr (rd p) 56.                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition prodw (s : Z) : Z :=
  let n  := Z.lxor (rd s) MFF in let a6 := Z.shiftr (rd n) 1 in let a2 := Z.land (rd a6) (rd M55) in
  let d  := rd n - rd a2 in let a2 := Z.shiftr (rd d) 2 in let e1 := Z.land (rd d) (rd M33) in
  let e2 := Z.land (rd a2) (rd M33) in let f := rd e1 + rd e2 in let a2 := Z.shiftr (rd f) 4 in
  let g  := rd f + rd a2 in let h := Z.land (rd g) (rd M0F) in rd h * rd M01.

Definition clz (x : Z) : Z := tailw (smearw x).

(* [comment removed for export] *)
Definition clz_tab_ok : bool :=
  forallb (fun K => Z.eqb (tailw (Z.ones (K + 1))) (63 - K)) (map Z.of_nat (seq 0 64)).

Lemma clz_tab_ok_true : clz_tab_ok = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lor_lt_pow2 a b n : 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
  assert (HP : 0 < Z.lor a b) by (pose proof (Z.lor_nonneg a b); pose proof (proj1 (Z.lor_eq_0_iff a b)); lia).
  apply Z.log2_lt_pow2; [exact HP|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_lt_pow2 a b n : 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b -> 0 <= Z.land a b < 2 ^ n.
Proof.
  intros Hn Ha Hb. split; [apply Z.land_nonneg; lia|].
  destruct (Z.eq_dec (Z.land a b) 0) as [E|NE]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  assert (HP : 0 < Z.land a b) by (pose proof (Z.land_nonneg a b); lia).
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.land_0_l in NE; lia|].
  apply Z.log2_lt_pow2; [exact HP|]. pose proof (Z.log2_land a b ltac:(lia) ltac:(lia)).
  pose proof (Z.log2_lt_pow2 a n ltac:(lia)). lia.
Qed.

Lemma shiftr_lt_pow2 a k n : 0 <= k -> 0 <= a < 2 ^ n -> 0 <= Z.shiftr a k < 2 ^ n.
Proof.
  intros Hk Ha. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma mod_lt_two64 a : 0 <= a mod two64 < two64.
Proof. unfold two64. apply Z.mod_pos_bound. lia. Qed.

Lemma smear_step_lt a n : 0 <= n -> 0 <= a < two64 -> 0 <= smear_step a n < two64.
Proof. intros. unfold smear_step, two64 in *. apply lor_lt_pow2; [lia|assumption|]. apply shiftr_lt_pow2; [lia|assumption]. Qed.

Lemma smear_lt x : 0 <= x < two64 -> 0 <= smear x < two64.
Proof. intros Hx. unfold smear. repeat (apply smear_step_lt; [lia|]). exact Hx. Qed.

(* [comment removed for export] *)
Lemma rd_small t : 0 <= t < two64 -> rd t = t.
Proof. intros. unfold rd. apply Z.mod_small. lia. Qed.

Lemma stepw_eq a n : 0 <= n -> 0 <= a < two64 -> stepw a n = smear_step a n.
Proof.
  intros Hn Ha. unfold stepw, smear_step. rewrite (rd_small a) by lia.
  rewrite rd_small; [reflexivity|]. unfold two64 in *. apply shiftr_lt_pow2; [lia|exact Ha].
Qed.

Lemma smearw_eq x : 0 <= x < two64 -> smearw x = smear x.
Proof.
  intros Hx. unfold smearw, smear.
  pose proof (smear_step_lt x 1 ltac:(lia) Hx) as H1.
  pose proof (smear_step_lt _ 2 ltac:(lia) H1) as H2.
  pose proof (smear_step_lt _ 4 ltac:(lia) H2) as H3.
  pose proof (smear_step_lt _ 8 ltac:(lia) H3) as H4.
  pose proof (smear_step_lt _ 16 ltac:(lia) H4) as H5.
  rewrite (stepw_eq x 1) by lia. rewrite (stepw_eq _ 2) by (try lia; exact H1).
  rewrite (stepw_eq _ 4) by (try lia; exact H2). rewrite (stepw_eq _ 8) by (try lia; exact H3).
  rewrite (stepw_eq _ 16) by (try lia; exact H4). rewrite (stepw_eq _ 32) by (try lia; exact H5). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma clz_tab_all : forallb (fun K => Z.eqb (tailw (Z.ones (K + 1))) (63 - K)) (map Z.of_nat (seq 0 64)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma clz_tab_prop : forall K, In K (map Z.of_nat (seq 0 64)) -> tailw (Z.ones (K + 1)) = 63 - K.
Proof. intros K HK. apply Z.eqb_eq. exact (proj1 (forallb_forall _ _) clz_tab_all K HK). Qed.

Theorem clz_val x K : 0 <= K < 64 -> 2 ^ K <= x < 2 ^ (K + 1) -> clz x = 63 - K.
Proof.
  intros HK Hx. unfold clz.
  assert (Hx64 : 0 <= x < two64).
  { unfold two64. pose proof (Z.pow_le_mono_r 2 (K + 1) 64 ltac:(lia) ltac:(lia)). pose proof (Z.pow_nonneg 2 K). lia. }
  rewrite (smearw_eq x Hx64), (smear_eq x K HK Hx).
  apply clz_tab_prop. apply in_map_iff. exists (Z.to_nat K). split; [lia|]. apply in_seq. lia.
Qed.

Theorem clz_log2 x : 0 < x < two64 -> clz x = 63 - Z.log2 x.
Proof.
  intros Hx. pose proof (Z.log2_spec x ltac:(lia)) as HS. rewrite <- Z.add_1_r in HS. pose proof (Z.log2_nonneg x).
  assert (Z.log2 x < 64).
  { destruct (Z_lt_le_dec (Z.log2 x) 64); [lia|]. exfalso. unfold two64 in Hx.
    pose proof (Z.pow_le_mono_r 2 64 (Z.log2 x) ltac:(lia) ltac:(lia)). lia. }
  apply clz_val; lia.
Qed.

(* [comment removed for export] *)
Theorem clz_range x lo hi : 1 <= lo -> lo <= x <= hi -> hi < two64 ->
  63 - Z.log2 hi <= clz x <= 63 - Z.log2 lo.
Proof.
  intros Hlo Hx Hhi. rewrite clz_log2 by lia.
  pose proof (Z.log2_le_mono lo x ltac:(lia)). pose proof (Z.log2_le_mono x hi ltac:(lia)). lia.
Qed.

Lemma clz_lt64 x : 0 < x < two64 -> 0 <= clz x <= 63.
Proof.
  intros Hx. rewrite clz_log2 by lia. pose proof (Z.log2_nonneg x).
  assert (Z.log2 x < 64).
  { destruct (Z_lt_le_dec (Z.log2 x) 64); [lia|]. exfalso. unfold two64 in Hx.
    pose proof (Z.log2_spec x ltac:(lia)). pose proof (Z.pow_le_mono_r 2 64 (Z.log2 x) ltac:(lia) ltac:(lia)). lia. }
  lia.
Qed.
