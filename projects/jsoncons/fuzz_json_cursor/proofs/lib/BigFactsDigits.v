(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import BigModel BigFactsBase BigFactsOps BigFactsRun.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition nwords (v : Z) : nat := if v <=? 0 then 0%nat else Z.to_nat (Z.log2 v / 64 + 1).

Lemma Mpow_nat (k : nat) : W.M ^ Z.of_nat k = 2 ^ (64 * Z.of_nat k).
Proof. rewrite M_val. change 18446744073709551616 with (2^64). rewrite <- Z.pow_mul_r by lia. reflexivity. Qed.

Lemma Mpow_pos (k : nat) : 0 < W.M ^ Z.of_nat k.
Proof. apply Z.pow_pos_nonneg. rewrite M_val; lia. lia. Qed.

Lemma Mpow_S (k : nat) : W.M ^ Z.of_nat (S k) = W.M * W.M ^ Z.of_nat k.
Proof. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.

Lemma Mpow_le_mono (a b : nat) : (a <= b)%nat -> W.M ^ Z.of_nat a <= W.M ^ Z.of_nat b.
Proof. intros. apply Z.pow_le_mono_r. rewrite M_val; lia. lia. Qed.

Lemma Mpow_lt_mono (a b : nat) : (a < b)%nat -> W.M ^ Z.of_nat a < W.M ^ Z.of_nat b.
Proof. intros. apply Z.pow_lt_mono_r. rewrite M_val; lia. lia. lia. Qed.

Lemma nwords_0 : nwords 0 = 0%nat. Proof. reflexivity. Qed.
Lemma nwords_nonpos v : v <= 0 -> nwords v = 0%nat.
Proof. intros. unfold nwords. destruct (Z.leb_spec v 0); auto. lia. Qed.

Lemma nwords_spec v : 0 < v ->
  W.M ^ Z.of_nat (nwords v - 1) <= v < W.M ^ Z.of_nat (nwords v).
Proof.
  intros Hv. unfold nwords. destruct (Z.leb_spec v 0). lia.
  destruct (Z.log2_spec v Hv) as [L1 L2]. pose proof (Z.log2_nonneg v) as L0.
  set (l := Z.log2 v) in *.
  assert (Hq: 0 <= l / 64) by (apply Z.div_pos; lia).
  replace (Z.of_nat (Z.to_nat (l / 64 + 1) - 1)) with (l / 64) by lia.
  replace (Z.of_nat (Z.to_nat (l / 64 + 1))) with (l / 64 + 1) by lia.
  rewrite M_val. change 18446744073709551616 with (2^64). rewrite <- !Z.pow_mul_r by lia.
  pose proof (Z.div_mod l 64 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound l 64 ltac:(lia)) as MB.
  split.
  - eapply Z.le_trans; [|exact L1]. apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans; [exact L2|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma nwords_pos v : 0 < v -> (1 <= nwords v)%nat.
Proof. intros. unfold nwords. destruct (Z.leb_spec v 0). lia. pose proof (Z.log2_nonneg v). assert (0 <= Z.log2 v / 64) by (apply Z.div_pos; lia). lia. Qed.

Lemma nwords_unique v k : (1 <= k)%nat -> W.M ^ Z.of_nat (k - 1) <= v < W.M ^ Z.of_nat k -> nwords v = k.
Proof.
  intros Hk [H1 H2]. pose proof (Mpow_pos (k - 1)).
  destruct (nwords_spec v ltac:(lia)) as [A B]. pose proof (nwords_pos v ltac:(lia)) as P.
  destruct (Nat.lt_trichotomy (nwords v) k) as [C|[C|C]]; auto; exfalso.
  - pose proof (Mpow_le_mono (nwords v) (k - 1) ltac:(lia)). lia.
  - pose proof (Mpow_le_mono k (nwords v - 1) ltac:(lia)). lia.
Qed.

Lemma nwords_le_iff v k : 0 <= v -> ((nwords v <= k)%nat <-> v < W.M ^ Z.of_nat k).
Proof.
  intros Hv. destruct (Z.eq_dec v 0) as [->|].
  { rewrite nwords_0. split; intros. apply Mpow_pos. lia. }
  destruct (nwords_spec v ltac:(lia)) as [A B]. split; intros C.
  - eapply Z.lt_le_trans; [exact B|]. apply Mpow_le_mono; auto.
  - destruct (Nat.le_gt_cases (nwords v) k); auto. exfalso.
    pose proof (Mpow_le_mono k (nwords v - 1) ltac:(lia)). lia.
Qed.

Lemma nwords_lt_pow v : 0 <= v -> v < W.M ^ Z.of_nat (nwords v).
Proof. intros. apply (proj1 (nwords_le_iff v (nwords v) H)). lia. Qed.

Lemma nwords_ge_iff v k : 0 <= v -> ((k <= nwords v)%nat <-> (k = 0%nat \/ W.M ^ Z.of_nat (k - 1) <= v)).
Proof.
  intros Hv. split; intros C.
  - destruct k. auto. right. destruct (Z_lt_le_dec v (W.M ^ Z.of_nat (S k - 1))); auto. exfalso.
    pose proof (proj2 (nwords_le_iff v (S k - 1) Hv) l). lia.
  - destruct C as [->|C]. lia. destruct (Nat.le_gt_cases k (nwords v)); auto. exfalso.
    pose proof (proj1 (nwords_le_iff v (nwords v) Hv) ltac:(lia)).
    pose proof (Mpow_le_mono (nwords v) (k - 1) ltac:(lia)). lia.
Qed.

Lemma nwords_mono a b : 0 <= a <= b -> (nwords a <= nwords b)%nat.
Proof. intros. apply (proj2 (nwords_le_iff a (nwords b) ltac:(lia))). eapply Z.le_lt_trans. apply (proj2 H). apply nwords_lt_pow. lia. Qed.

Lemma nwords_1 v : 0 < v < W.M -> nwords v = 1%nat.
Proof. intros. apply nwords_unique. lia. change (Z.of_nat (1 - 1)) with 0. change (Z.of_nat 1) with 1. rewrite Z.pow_0_r, Z.pow_1_r. lia. Qed.

Definition wordi (v : Z) (i : nat) : Z := (v / W.M ^ Z.of_nat i) mod W.M.
Definition wlist (v : Z) (n : nat) : words := map (fun i => wordi v i) (seq 0 n).

Lemma wordi_range v i : wordZ (wordi v i).
Proof. unfold wordi, wordZ. apply Z.mod_pos_bound. rewrite M_val; lia. Qed.

Lemma wlist_length v n : length (wlist v n) = n.
Proof. unfold wlist. rewrite length_map, length_seq. reflexivity. Qed.

Lemma wlist_words_ok v n : words_ok (wlist v n).
Proof. unfold wlist, words_ok. apply Forall_map. apply Forall_forall. intros; apply wordi_range. Qed.

Lemma wlist_nth v n i : (i < n)%nat -> nth_w (wlist v n) i = wordi v i.
Proof.
  intros. unfold wlist, nth_w. rewrite (nth_indep _ 0 (wordi v 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun i => wordi v i)), seq_nth; auto.
Qed.

Lemma wordi_0 v : wordi v 0 = v mod W.M.
Proof. unfold wordi. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r. reflexivity. Qed.

Lemma wordi_S v i : 0 <= v -> wordi v (S i) = wordi (v / W.M) i.
Proof.
  intros. unfold wordi. rewrite Mpow_S. rewrite <- Z.div_div. reflexivity. rewrite M_val; lia. apply Mpow_pos.
Qed.

Lemma wlist_S v n : 0 <= v -> wlist v (S n) = (v mod W.M) :: wlist (v / W.M) n.
Proof.
  intros Hv. unfold wlist. rewrite <- cons_seq. simpl map. rewrite wordi_0. f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intros; apply wordi_S; auto.
Qed.

Lemma val_wlist v n : 0 <= v -> val (wlist v n) = v mod W.M ^ Z.of_nat n.
Proof.
  revert v. induction n as [|n IH]; intros v Hv.
  - change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
  - rewrite wlist_S by auto. rewrite val_cons, IH. 2: apply Z.div_pos; [lia|rewrite M_val; lia].
    rewrite Mpow_S. rewrite Z.rem_mul_r. lia. rewrite M_val; lia. apply Mpow_pos.
Qed.

Lemma val_wlist_small v n : 0 <= v < W.M ^ Z.of_nat n -> val (wlist v n) = v.
Proof. intros. rewrite val_wlist by lia. apply Z.mod_small. lia. Qed.

Lemma wordi_zero i : wordi 0 i = 0.
Proof. unfold wordi. rewrite Z.div_0_l. reflexivity. pose proof (Mpow_pos i). lia. Qed.

Lemma wordi_val ws i : words_ok ws -> wordi (val ws) i = nth_w ws i.
Proof.
  revert ws. induction i as [|i IH]; intros ws Hw.
  - rewrite wordi_0. destruct ws as [|w t]. reflexivity. rewrite val_cons. inversion Hw; subst.
    unfold nth_w; simpl. unfold wordZ in *. rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small; auto.
  - destruct ws as [|w t]. { rewrite val_nil, wordi_zero. reflexivity. }
    inversion Hw; subst. rewrite wordi_S. 2: apply val_nonneg; auto.
    rewrite val_cons. replace ((w + W.M * val t) / W.M) with (val t). apply IH; auto.
    unfold wordZ in *. rewrite Z.mul_comm, Z_div_plus_full, Z.div_small; lia.
Qed.

Lemma wlist_val ws : words_ok ws -> wlist (val ws) (length ws) = ws.
Proof.
  intros Hw. apply (nth_ext _ _ 0 0). rewrite wlist_length; auto.
  intros n Hn. rewrite wlist_length in Hn. pose proof (wlist_nth (val ws) (length ws) n Hn). unfold nth_w in H. rewrite H.
  apply wordi_val; auto.
Qed.

Lemma reduced_length_nwords ws : words_ok ws -> reduced_ws ws -> length ws = nwords (val ws).
Proof.
  intros Hw Hr. destruct ws as [|w t] eqn:E. reflexivity.
  assert (NE: ws <> []) by (subst; discriminate). rewrite <- E in *.
  pose proof (reduced_val_lower ws Hw Hr NE) as L. pose proof (val_bound ws Hw) as [_ U].
  symmetry. apply nwords_unique. subst; simpl; lia.
  replace (Z.of_nat (length ws - 1)) with (Z.of_nat (length ws) - 1). lia. subst ws; simpl length. lia.
Qed.

Lemma reduced_is_wlist ws : words_ok ws -> reduced_ws ws -> ws = wlist (val ws) (nwords (val ws)).
Proof. intros. rewrite <- reduced_length_nwords by auto. symmetry. apply wlist_val; auto. Qed.

Lemma wlist_reduced v : 0 <= v -> reduced_ws (wlist v (nwords v)).
Proof.
  intros Hv. destruct (Z.eq_dec v 0) as [->|]. { rewrite nwords_0. left. reflexivity. }
  apply reduced_ws_intro. intros NE. rewrite wlist_length. rewrite wlist_nth. 2: pose proof (nwords_pos v ltac:(lia)); lia.
  destruct (nwords_spec v ltac:(lia)) as [A B].
  pose proof (nwords_pos v ltac:(lia)) as P. pose proof (Mpow_pos (nwords v - 1)) as Q.
  assert (U: v / W.M ^ Z.of_nat (nwords v - 1) < W.M).
  { apply Z.div_lt_upper_bound. lia. rewrite Z.mul_comm, <- Mpow_S. replace (S (nwords v - 1)) with (nwords v) by lia. auto. }
  assert (L: 1 <= v / W.M ^ Z.of_nat (nwords v - 1)).
  { apply Z.div_le_lower_bound. lia. lia. }
  unfold wordi. rewrite Z.mod_small by lia. lia.
Qed.

Lemma wordi_high v i : 0 <= v -> (nwords v <= i)%nat -> wordi v i = 0.
Proof.
  intros Hv Hi. unfold wordi. rewrite Z.div_small. reflexivity. split; auto.
  eapply Z.lt_le_trans. apply nwords_lt_pow; auto. apply Mpow_le_mono; auto.
Qed.

Lemma wordi_top_nonzero v : 0 < v -> wordi v (nwords v - 1) <> 0.
Proof.
  intros Hv. pose proof (wlist_reduced v ltac:(lia)) as R. pose proof (nwords_pos v Hv).
  apply reduced_ws_top in R. rewrite wlist_length, wlist_nth in R by lia. exact R.
  intros E. apply (f_equal (@length Z)) in E. rewrite wlist_length in E. simpl in E. lia.
Qed.

Lemma nwords_mul10_add v d : 0 <= v -> 0 <= d < W.M -> (nwords (10 * v + d) <= nwords v + 1)%nat.
Proof.
  intros Hv Hd. apply (proj2 (nwords_le_iff (10 * v + d) (nwords v + 1) ltac:(lia))).
  pose proof (nwords_lt_pow v Hv) as B. replace (nwords v + 1)%nat with (S (nwords v)) by lia. rewrite Mpow_S.
  pose proof (Mpow_pos (nwords v)). rewrite M_val in *. nia.
Qed.

Lemma nwords_mul10_add_ge v d : 0 <= v -> 0 <= d -> (nwords v <= nwords (10 * v + d))%nat.
Proof. intros. apply nwords_mono. lia. Qed.

Definition e3402 (m : Z) : Z := (m * 3402) / 1024.

Fixpoint pow10_check (k : nat) (p : Z) (m : Z) : bool :=
  match k with
  | O => true
  | S k' => (p <? 2 ^ (e3402 m + 1)) && pow10_check k' (10 * p) (m + 1)
  end.

Lemma pow10_check_sound k : forall p m, 0 <= m -> p = 10 ^ m -> pow10_check k p m = true ->
  forall j, m <= j < m + Z.of_nat k -> 10 ^ j < 2 ^ (e3402 j + 1).
Proof.
  induction k as [|k IH]; intros p m Hm Hp Hc j Hj. lia.
  cbn [pow10_check] in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2]. apply Z.ltb_lt in H1.
  destruct (Z.eq_dec j m). { subst j p. exact H1. }
  apply (IH (10 * p) (m + 1)); [lia| |exact H2|lia]. subst p. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia.
Qed.

Lemma pow10_base : pow10_check 1024 1 0 = true.
Proof. vmc_refl. Qed.

Lemma pow10_1024 : 10 ^ 1024 < 2 ^ 3402.
Proof. vmc_refl. Qed.

Lemma e3402_shift m : e3402 (m + 1024) = e3402 m + 3402.
Proof. unfold e3402. rewrite Z.mul_add_distr_r. replace (1024 * 3402) with (3402 * 1024) by lia. rewrite Z_div_plus_full by lia. reflexivity. Qed.

Lemma pow10_lt_e3402 m : 0 <= m -> 10 ^ m < 2 ^ (e3402 m + 1).
Proof.
  intros Hm. remember (Z.to_nat (m / 1024)) as q eqn:Eq. revert m Hm Eq.
  induction q as [|q IH]; intros m Hm Eq.
  - apply (pow10_check_sound 1024 1 0 ltac:(lia) eq_refl pow10_base).
    pose proof (Z.div_mod m 1024 ltac:(lia)). pose proof (Z.mod_pos_bound m 1024 ltac:(lia)).
    assert (m / 1024 = 0) by lia. simpl. lia.
  - pose proof (Z.div_mod m 1024 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound m 1024 ltac:(lia)) as MB.
    assert (Hm': 1024 <= m) by lia.
    specialize (IH (m - 1024)). replace m with ((m - 1024) + 1024) by lia.
    rewrite e3402_shift. rewrite Z.pow_add_r by lia.
    assert (He: 0 <= e3402 (m - 1024)) by (unfold e3402; apply Z.div_pos; lia).
    replace (e3402 (m - 1024) + 3402 + 1) with ((e3402 (m - 1024) + 1) + 3402) by lia. rewrite (Z.pow_add_r 2) by lia.
    assert (IH': 10 ^ (m - 1024) < 2 ^ (e3402 (m - 1024) + 1)).
    { apply IH. lia. replace (m - 1024) with (m + (-1) * 1024) by lia. rewrite Z_div_plus_full by lia. lia. }
    pose proof pow10_1024. pose proof (Z.pow_pos_nonneg 10 (m - 1024) ltac:(lia) ltac:(lia)).
    apply Z.mul_lt_mono_nonneg; lia.
Qed.

Theorem pow10_lt_num_words_est (m : nat) : 10 ^ Z.of_nat m < W.M ^ Z.of_nat (num_words_est m).
Proof.
  rewrite Mpow_nat. unfold num_words_est.
  destruct (Nat.ltb_spec m 10).
  - change (Z.of_nat 1%nat) with 1. eapply Z.le_lt_trans. apply Z.pow_le_mono_r. lia. apply (proj1 (Nat2Z.inj_le m 9)). lia.
    vm_compute. reflexivity.
  - pose proof (pow10_lt_e3402 (Z.of_nat m) ltac:(lia)) as P. unfold e3402 in P.
    set (e := Z.of_nat m * 3402 / 1024) in *.
    assert (He: 0 <= e) by (subst e; apply Z.div_pos; lia).
    assert (Hq: e + 1 <= 64 * ((e + 1 + 63) / 64)).
    { pose proof (Z.div_mod (e + 1 + 63) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (e + 1 + 63) 64 ltac:(lia)). lia. }
    rewrite Z2Nat.id. 2: apply Z.div_pos; lia.
    eapply Z.lt_le_trans. exact P. apply Z.pow_le_mono_r. lia. exact Hq.
Qed.

Theorem nwords_bound v J : 0 <= v < 10 ^ Z.of_nat J -> (nwords v <= num_words_est J)%nat.
Proof.
  intros Hv. apply (proj2 (nwords_le_iff v (num_words_est J) ltac:(lia))). eapply Z.lt_trans. apply (proj2 Hv). apply pow10_lt_num_words_est.
Qed.

Corollary nwords_bound_le v J m : 0 <= v < 10 ^ Z.of_nat J -> (J <= m)%nat -> (nwords v <= num_words_est m)%nat.
Proof. intros. eapply Nat.le_trans. apply nwords_bound; eauto. apply num_words_est_mono; auto. Qed.

Lemma round_up_ge_S n : (n + 1 <= round_up n)%nat.
Proof. pose proof (round_up_gt n). lia. Qed.

Theorem digit_step_no_realloc v d J m :
  0 <= v < 10 ^ Z.of_nat J -> 0 <= d <= 9 -> (J < m)%nat ->
  (nwords v + 1 <= round_up (num_words_est m))%nat /\
  (nwords (10 * v) + 1 <= round_up (num_words_est m))%nat /\
  (nwords (10 * v + d) + 1 <= round_up (num_words_est m))%nat /\
  0 <= 10 * v + d < 10 ^ Z.of_nat (S J).
Proof.
  intros Hv Hd HJ. pose proof (round_up_ge_S (num_words_est m)) as R.
  assert (B: 0 <= 10 * v + d < 10 ^ Z.of_nat (S J)). { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
  pose proof (nwords_bound_le v J m Hv ltac:(lia)).
  pose proof (nwords_bound_le (10 * v + d) (S J) m B ltac:(lia)).
  pose proof (nwords_bound_le (10 * v) (S J) m ltac:(rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia) ltac:(lia)).
  repeat split; try lia.
Qed.

Lemma nwords_after_growth v k t w :
  (1 <= k)%nat -> 0 <= v < 10 * W.M ^ Z.of_nat (k - 1) -> 0 <= t <= 18 ->
  0 <= w < 10 ^ t * (v + 1) -> (nwords w <= k)%nat.
Proof.
  intros Hk Hv Ht Hw. apply (proj2 (nwords_le_iff w k ltac:(lia))).
  replace (W.M ^ Z.of_nat k) with (W.M ^ Z.of_nat (S (k - 1))) by (f_equal; lia). rewrite Mpow_S.
  assert (P: 10 ^ t * 10 <= 10 ^ 19). { replace (10 ^ 19) with (10 ^ 18 * 10) by reflexivity. apply Z.mul_le_mono_nonneg_r. lia. apply Z.pow_le_mono_r; lia. }
  assert (Q: 10 ^ 19 < W.M) by (rewrite M_val; reflexivity).
  pose proof (Mpow_pos (k - 1)). pose proof (Z.pow_pos_nonneg 10 t ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma mod_Mpow_S v i : 0 <= v ->
  v mod W.M ^ Z.of_nat (S i) = wordi v i * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i.
Proof.
  intros Hv. rewrite Mpow_S, (Z.mul_comm W.M), Z.rem_mul_r. unfold wordi. lia. pose proof (Mpow_pos i); lia. rewrite M_val; lia.
Qed.

Lemma div_Mpow_S a b i : 0 <= b ->
  (a * W.M ^ Z.of_nat i + b) / W.M ^ Z.of_nat (S i) = (a + b / W.M ^ Z.of_nat i) / W.M.
Proof.
  intros Hb. pose proof (Mpow_pos i). rewrite Mpow_S, (Z.mul_comm W.M). rewrite <- Z.div_div. 2: lia. 2: rewrite M_val; lia.
  rewrite Z_div_plus_full_l. reflexivity. lia.
Qed.

Lemma split_Mpow_S v i : 0 <= v ->
  v = (v / W.M ^ Z.of_nat (S i)) * W.M ^ Z.of_nat (S i) + wordi v i * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i.
Proof. intros Hv. pose proof (mod_Mpow_S v i Hv). pose proof (Z.div_mod v (W.M ^ Z.of_nat (S i)) ltac:(pose proof (Mpow_pos (S i)); lia)). lia. Qed.

Definition mcarry (y v : Z) (i : nat) : Z := (y * (v mod W.M ^ Z.of_nat i)) / W.M ^ Z.of_nat i.

Lemma mcarry_0 y v : mcarry y v 0 = 0.
Proof. unfold mcarry. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mod_1_r, Z.mul_0_r. reflexivity. Qed.

Lemma mcarry_bound y v i : 0 <= y -> 0 <= mcarry y v i <= Z.max 0 (y - 1).
Proof.
  intros Hy. unfold mcarry. pose proof (Mpow_pos i) as P. pose proof (Z.mod_pos_bound v _ P) as [A B].
  split. apply Z.div_pos; nia.
  destruct (Z.eq_dec y 0). subst. rewrite Z.mul_0_l, Z.div_0_l; lia.
  assert (y * (v mod W.M ^ Z.of_nat i) / W.M ^ Z.of_nat i < y). { apply Z.div_lt_upper_bound. lia. nia. } lia.
Qed.

Lemma mcarry_wordZ y v i : wordZ y -> wordZ (mcarry y v i).
Proof. intros Hy. pose proof (mcarry_bound y v i ltac:(unfold wordZ in Hy; lia)). unfold wordZ in *. lia. Qed.

Theorem mul_limb_step y v i : wordZ y -> 0 <= v ->
  let x := wordi v i in
  let c := mcarry y v i in
  let hl := DDproduct x y in
  let w := W.add (snd hl) c in
  w = wordi (y * v) i /\
  W.add (fst hl) (W.b2z (W.ltu w (snd hl))) = mcarry y v (S i).
Proof.
  intros Hy Hv. cbn zeta.
  pose proof (wordi_range v i) as Hx. pose proof (DDproduct_correct (wordi v i) y Hx Hy) as DC.
  pose proof (DDproduct_hi_bound (wordi v i) y Hx Hy) as HB.
  destruct (DDproduct (wordi v i) y) as [hi lo]. cbn [fst snd] in *. destruct DC as (Whi & Wlo & E).
  pose proof (mcarry_wordZ y v i Hy) as Wc. set (c := mcarry y v i) in *.
  pose proof (add_carry lo c Wlo Wc) as AC. set (b := W.b2z (W.ltu (W.add lo c) lo)) in *.
  pose proof (b2z_range (W.ltu (W.add lo c) lo)) as Rb. fold b in Rb.
  pose proof (add_range lo c) as Ww. set (w := W.add lo c) in *.
  pose proof (Mpow_pos i) as P. pose proof (Z.mod_pos_bound v _ P) as [MA MB].

  assert (K1: (y * (v mod W.M ^ Z.of_nat (S i))) / W.M ^ Z.of_nat i = y * wordi v i + c).
  { rewrite mod_Mpow_S by auto.
    replace (y * (wordi v i * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i)) with ((y * wordi v i) * W.M ^ Z.of_nat i + y * (v mod W.M ^ Z.of_nat i)) by lia.
    rewrite Z_div_plus_full_l by lia. unfold c, mcarry. lia. }
  split.
  -
    unfold wordi.
    assert (Hyv: y * v = (y * (v / W.M ^ Z.of_nat (S i))) * W.M ^ Z.of_nat (S i) + y * (v mod W.M ^ Z.of_nat (S i))).
    { pose proof (Z.div_mod v (W.M ^ Z.of_nat (S i)) ltac:(pose proof (Mpow_pos (S i)); lia)). nia. }
    set (q := v / W.M ^ Z.of_nat (S i)) in *. set (r := v mod W.M ^ Z.of_nat (S i)) in *.
    rewrite Hyv. rewrite Mpow_S.
    replace (y * q * (W.M * W.M ^ Z.of_nat i) + y * r) with (y * r + (y * q * W.M) * W.M ^ Z.of_nat i) by lia.
    rewrite Z_div_plus_full by lia. rewrite K1.
    replace (y * wordi v i + c + y * q * W.M) with ((lo + c) + (hi + y * q) * W.M) by lia.
    rewrite Z_mod_plus_full. unfold w, W.add, W.wrap. reflexivity.
  -
    assert (K2: mcarry y v (S i) = (y * wordi v i + c) / W.M).
    { unfold mcarry at 1. rewrite (mod_Mpow_S v i) at 1 by auto. rewrite Z.mul_add_distr_l, Z.mul_assoc.
      rewrite div_Mpow_S. 2: unfold wordZ in Hy; nia. unfold c, mcarry. reflexivity. }
    rewrite K2. replace (y * wordi v i + c) with (w + (b + hi) * W.M) by lia. rewrite Z_div_plus_full by (rewrite M_val; lia).
    unfold wordZ in Ww. rewrite Z.div_small by lia. rewrite add_small; auto. lia. unfold wordZ; rewrite M_val in *; lia. unfold wordZ in *; lia.
Qed.

Lemma mcarry_top y v n : 0 <= y -> 0 <= v < W.M ^ Z.of_nat n -> mcarry y v n = (y * v) / W.M ^ Z.of_nat n.
Proof. intros. unfold mcarry. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma mul_top_word y v n : wordZ y -> 0 <= v < W.M ^ Z.of_nat n -> mcarry y v n = wordi (y * v) n.
Proof.
  intros Hy Hv. rewrite mcarry_top by (unfold wordZ in Hy; lia). unfold wordi. symmetry. apply Z.mod_small. split.
  apply Z.div_pos. unfold wordZ in Hy; nia. apply Mpow_pos.
  apply Z.div_lt_upper_bound. apply Mpow_pos. unfold wordZ in Hy. pose proof (Mpow_pos n). nia.
Qed.

Lemma mul_value_bound y v n : wordZ y -> 0 <= v < W.M ^ Z.of_nat n -> 0 <= y * v < W.M ^ Z.of_nat (S n).
Proof. intros Hy Hv. rewrite Mpow_S. unfold wordZ in Hy. pose proof (Mpow_pos n). nia. Qed.

Definition acarry (y v : Z) (i : nat) : Z := if W.M ^ Z.of_nat i <=? v mod W.M ^ Z.of_nat i + y then 1 else 0.

Lemma acarry_range y v i : 0 <= acarry y v i <= 1.
Proof. unfold acarry. destruct (Z.leb _ _); lia. Qed.

Lemma acarry_div y v i : (1 <= i)%nat -> wordZ y -> acarry y v i = (v mod W.M ^ Z.of_nat i + y) / W.M ^ Z.of_nat i.
Proof.
  intros Hi Hy. pose proof (Mpow_pos i) as P. pose proof (Z.mod_pos_bound v _ P) as [A B].
  assert (yM: y < W.M ^ Z.of_nat i). { unfold wordZ in Hy. eapply Z.lt_le_trans. apply (proj2 Hy). replace W.M with (W.M ^ Z.of_nat 1) at 1. apply Mpow_le_mono; lia. change (Z.of_nat 1) with 1. rewrite Z.pow_1_r. reflexivity. }
  unfold acarry. destruct (Z.leb_spec (W.M ^ Z.of_nat i) (v mod W.M ^ Z.of_nat i + y)).
  - apply Z.div_unique with (v mod W.M ^ Z.of_nat i + y - W.M ^ Z.of_nat i); unfold wordZ in Hy; lia.
  - symmetry. apply Z.div_small. unfold wordZ in Hy; lia.
Qed.

Theorem add_limb0 y v : wordZ y -> 0 <= v ->
  let x := wordi v 0 in
  let w := W.add x y in
  w = wordi (v + y) 0 /\ W.b2z (W.ltu w x) = acarry y v 1.
Proof.
  intros Hy Hv. cbn zeta. pose proof (wordi_range v 0) as Hx.
  rewrite acarry_div by (auto; lia). change (Z.of_nat 1) with 1. rewrite Z.pow_1_r.
  rewrite !wordi_0. split.
  - unfold W.add, W.wrap. rewrite Z.add_mod_idemp_l. reflexivity. rewrite M_val; lia.
  - pose proof (add_carry (v mod W.M) y ltac:(rewrite <- wordi_0; apply wordi_range) Hy) as AC.
    pose proof (add_range (v mod W.M) y) as R. unfold wordZ in R.
    pose proof (b2z_range (W.ltu (W.add (v mod W.M) y) (v mod W.M))) as B.
    apply Z.div_unique with (W.add (v mod W.M) y); lia.
Qed.

Theorem add_limbS y v i : wordZ y -> 0 <= v -> (1 <= i)%nat ->
  let x := wordi v i in
  let c := acarry y v i in
  let d := W.add x c in
  d = wordi (v + y) i /\
  acarry y v (S i) = (if c =? 1 then W.b2z (W.ltu d c) else 0).
Proof.
  intros Hy Hv Hi. cbn zeta. pose proof (wordi_range v i) as Hx.
  pose proof (Mpow_pos i) as P. pose proof (Z.mod_pos_bound v _ P) as [A B].
  assert (yM: y < W.M ^ Z.of_nat i). { unfold wordZ in Hy. eapply Z.lt_le_trans. apply (proj2 Hy). replace W.M with (W.M ^ Z.of_nat 1) at 1. apply Mpow_le_mono; lia. change (Z.of_nat 1) with 1. rewrite Z.pow_1_r. reflexivity. }
  pose proof (acarry_div y v i Hi Hy) as CD. pose proof (acarry_range y v i) as CR.
  set (c := acarry y v i) in *.
  split.
  - unfold wordi at 2.
    assert (Hs: v + y = (v mod W.M ^ Z.of_nat i + y) + (wordi v i + v / W.M ^ Z.of_nat (S i) * W.M) * W.M ^ Z.of_nat i).
    { pose proof (split_Mpow_S v i Hv) as Sp. rewrite Mpow_S in Sp at 2. lia. }
    rewrite Hs. rewrite Z_div_plus_full by lia. rewrite <- CD.
    replace (c + (wordi v i + v / W.M ^ Z.of_nat (S i) * W.M)) with ((wordi v i + c) + (v / W.M ^ Z.of_nat (S i)) * W.M) by lia.
    rewrite Z_mod_plus_full. unfold W.add, W.wrap. reflexivity.
  - unfold acarry at 1. rewrite mod_Mpow_S by auto.
    destruct (Z.eqb_spec c 1) as [C1|C0].
    +
      assert (R: W.M ^ Z.of_nat i <= v mod W.M ^ Z.of_nat i + y). { unfold c, acarry in C1. destruct (Z.leb_spec (W.M ^ Z.of_nat i) (v mod W.M ^ Z.of_nat i + y)); auto; lia. }
      rewrite C1. unfold W.ltu, W.b2z, W.add, W.wrap. unfold wordZ in *.
      destruct (Z.eq_dec (wordi v i) (W.M - 1)) as [T|T].
      * rewrite T. replace (W.M - 1 + 1) with W.M by lia. rewrite Z.mod_same by lia. cbn [Z.ltb].
        destruct (Z.leb_spec (W.M ^ Z.of_nat (S i)) ((W.M - 1) * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i + y)); auto.
        exfalso. rewrite Mpow_S in *. nia.
      * assert (Hw1: 0 <= wordi v i + 1 < W.M) by (clear -Hx T; lia). rewrite (Z.mod_small (wordi v i + 1) W.M Hw1).
        clearbody c. destruct (Z.ltb_spec (wordi v i + 1) 1); try lia.
        destruct (Z.leb_spec (W.M ^ Z.of_nat (S i)) (wordi v i * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i + y)); auto.
        exfalso. rewrite Mpow_S in *. nia.
    + clearbody c. assert (c = 0) by lia. assert (R: v mod W.M ^ Z.of_nat i + y < W.M ^ Z.of_nat i).
      { destruct (Z_lt_le_dec (v mod W.M ^ Z.of_nat i + y) (W.M ^ Z.of_nat i)); auto. exfalso.
        assert (1 <= (v mod W.M ^ Z.of_nat i + y) / W.M ^ Z.of_nat i) by (apply Z.div_le_lower_bound; lia). lia. }
      destruct (Z.leb_spec (W.M ^ Z.of_nat (S i)) (wordi v i * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i + y)); auto.
      exfalso. rewrite Mpow_S in *. unfold wordZ in Hx. nia.
Qed.

Lemma acarry_stays_0 y v i : wordZ y -> 0 <= v -> (1 <= i)%nat -> acarry y v i = 0 -> acarry y v (S i) = 0.
Proof. intros. pose proof (add_limbS y v i H H0 H1) as [_ E]. rewrite H2 in E. simpl in E. exact E. Qed.

Lemma add_above_carry y v i j : wordZ y -> 0 <= v -> (1 <= i)%nat -> acarry y v i = 0 -> (i <= j)%nat ->
  wordi (v + y) j = wordi v j /\ acarry y v j = 0.
Proof.
  intros Hy Hv Hi Hc Hij. induction Hij.
  - split; auto. pose proof (add_limbS y v i Hy Hv Hi) as [E _]. rewrite Hc in E. rewrite <- E. unfold W.add, W.wrap. rewrite Z.add_0_r. apply Z.mod_small. apply wordi_range.
  - destruct IHHij as [E C]. pose proof (acarry_stays_0 y v m Hy Hv ltac:(lia) C) as C'. split; auto.
    pose proof (add_limbS y v (S m) Hy Hv ltac:(lia)) as [E' _]. rewrite C' in E'. rewrite <- E'. unfold W.add, W.wrap. rewrite Z.add_0_r. apply Z.mod_small. apply wordi_range.
Qed.

Lemma add_top_word y v n : wordZ y -> 0 <= v < W.M ^ Z.of_nat n -> (1 <= n)%nat -> acarry y v n = wordi (v + y) n.
Proof.
  intros Hy Hv Hn. pose proof (add_limbS y v n Hy ltac:(lia) Hn) as [E _]. rewrite <- E.
  rewrite (wordi_high v n) by (try lia; apply (proj2 (nwords_le_iff v n ltac:(lia))); lia).
  unfold W.add, W.wrap. rewrite Z.add_0_l. symmetry; apply Z.mod_small. pose proof (acarry_range y v n). rewrite M_val; lia.
Qed.

Lemma add_value_bound y v n : wordZ y -> 0 <= v < W.M ^ Z.of_nat n -> (1 <= n)%nat -> 0 <= v + y < W.M ^ Z.of_nat (S n).
Proof.
  intros Hy Hv Hn. rewrite Mpow_S. unfold wordZ in Hy. pose proof (Mpow_pos n).
  assert (W.M <= W.M ^ Z.of_nat n). { replace W.M with (W.M ^ Z.of_nat 1) at 1. apply Mpow_le_mono; lia. change (Z.of_nat 1) with 1. rewrite Z.pow_1_r; auto. }
  rewrite M_val in *. nia.
Qed.

Lemma nwords_by_top p n : (1 <= n)%nat -> W.M ^ Z.of_nat (n - 1) <= p < W.M ^ Z.of_nat (S n) ->
  (wordi p n = 0 -> nwords p = n /\ wordi p (n - 1) <> 0) /\
  (wordi p n <> 0 -> nwords p = S n).
Proof.
  intros Hn [L U]. pose proof (Mpow_pos n) as P.
  assert (Hp: 0 < p) by (pose proof (Mpow_pos (n - 1)); lia).
  assert (T: wordi p n = p / W.M ^ Z.of_nat n).
  { unfold wordi. apply Z.mod_small. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound. lia. rewrite Z.mul_comm, <- Mpow_S. auto. }
  split; intros W0.
  - rewrite T in W0. apply Z.div_small_iff in W0; try lia. assert (E: nwords p = n) by (apply nwords_unique; lia). split; auto.
    rewrite <- E at 1. apply wordi_top_nonzero. lia.
  - apply nwords_unique. lia. replace (S n - 1)%nat with n by lia. split; try lia. rewrite T in W0.
    destruct (Z_lt_le_dec p (W.M ^ Z.of_nat n)); auto. exfalso. apply W0. apply Z.div_small. lia.
Qed.

Theorem mul_reduce_facts y v : wordZ y -> 1 <= y -> 0 < v ->
  let n := nwords v in let p := y * v in
  0 <= p < W.M ^ Z.of_nat (S n) /\
  (wordi p n = 0 -> nwords p = n /\ wordi p (n - 1) <> 0) /\
  (wordi p n <> 0 -> nwords p = S n).
Proof.
  intros Hy Hy1 Hv. cbn zeta. destruct (nwords_spec v Hv) as [L U]. pose proof (nwords_pos v Hv) as Hn.
  pose proof (mul_value_bound y v (nwords v) Hy ltac:(lia)) as B. split. auto.
  apply nwords_by_top. auto. split. 2: lia. pose proof (Mpow_pos (nwords v - 1)). nia.
Qed.

Theorem add_reduce_facts y v : wordZ y -> 0 < v ->
  let n := nwords v in let p := v + y in
  0 <= p < W.M ^ Z.of_nat (S n) /\
  (wordi p n = 0 -> nwords p = n /\ wordi p (n - 1) <> 0) /\
  (wordi p n <> 0 -> nwords p = S n).
Proof.
  intros Hy Hv. cbn zeta. destruct (nwords_spec v Hv) as [L U]. pose proof (nwords_pos v Hv) as Hn.
  pose proof (add_value_bound y v (nwords v) Hy ltac:(lia) Hn) as B. split. auto.
  apply nwords_by_top. auto. unfold wordZ in Hy. lia.
Qed.

Lemma nwords_small y : wordZ y -> nwords y = (if (y =? 0)%Z then 0%nat else 1%nat).
Proof. intros Hy. unfold wordZ in Hy. destruct (Z.eqb_spec y 0). subst; apply nwords_0. apply nwords_1. lia. Qed.

Theorem mul_word_is_wlist N s y s0 : okN N s -> reduced s -> wordZ y -> (S (size s) <= N)%nat ->
  let s' := fst (mul_word s y s0) in
  s_words s' = wlist (val (s_words s) * y) (nwords (val (s_words s) * y)) /\
  size s' = nwords (val (s_words s) * y).
Proof.
  intros Hok Hr Hy Hn. destruct (mul_word_mspec N s y Hok Hy Hn s0) as [(Hok' & Hr' & Hv' & _) _].
  cbn zeta. rewrite <- Hv'. split.
  apply reduced_is_wlist. apply (okN_words N); auto. exact Hr'.
  unfold size. apply reduced_length_nwords. apply (okN_words N); auto. exact Hr'.
Qed.

Theorem add_word_is_wlist N s y s0 : okN N s -> reduced s -> wordZ y -> (S (size s) <= N)%nat ->
  let s' := fst (add_word s y s0) in
  s_words s' = wlist (val (s_words s) + y) (nwords (val (s_words s) + y)) /\
  size s' = nwords (val (s_words s) + y).
Proof.
  intros Hok Hr Hy Hn. destruct (add_word_mspec N s y Hok Hy Hn s0) as [(Hok' & Hr' & Hv' & _) _].
  cbn zeta. rewrite <- Hv'. split.
  apply reduced_is_wlist. apply (okN_words N); auto. exact Hr'.
  unfold size. apply reduced_length_nwords. apply (okN_words N); auto. exact Hr'.
Qed.

Lemma reduced_sto_shape s : wf s -> reduced s ->
  s_words s = wlist (val (s_words s)) (nwords (val (s_words s))) /\ size s = nwords (val (s_words s)).
Proof.
  intros [Hw _] Hr. split. apply reduced_is_wlist; auto. unfold size. apply reduced_length_nwords; auto.
Qed.

Lemma dec_acc_app' acc a b : dec_acc acc (a ++ b) = dec_acc (dec_acc acc a) b.
Proof. revert acc; induction a; intros; simpl; auto. Qed.

Lemma dec_firstn_S (ds : list Z) (J : nat) : (J < length ds)%nat ->
  dec (firstn (S J) ds) = 10 * dec (firstn J ds) + (nth J ds 0 - 48).
Proof.
  intros HJ. unfold dec. rewrite (firstn_S_nth ds J HJ). rewrite dec_acc_app'. unfold nth_w. cbn [dec_acc]. lia.
Qed.

Lemma all_digits_firstn ds J : all_digits ds = true -> all_digits (firstn J ds) = true.
Proof.
  unfold all_digits. rewrite !forallb_forall. intros H x Hx. apply H. rewrite <- (firstn_skipn J ds). apply in_app_iff. auto.
Qed.

Lemma all_digits_Forall ds : Forall (fun c => 48 <= c <= 57) ds -> all_digits ds = true.
Proof.
  unfold all_digits. rewrite forallb_forall, Forall_forall. intros H x Hx. unfold is_digit. specialize (H x Hx).
  rewrite andb_true_iff, !Z.leb_le. exact H.
Qed.

Lemma dec_firstn_bound ds J : all_digits ds = true -> (J <= length ds)%nat -> 0 <= dec (firstn J ds) < 10 ^ Z.of_nat J.
Proof.
  intros Hd HJ. pose proof (dec_bound (firstn J ds) (all_digits_firstn ds J Hd)) as B.
  rewrite length_firstn, Nat.min_l in B by auto. exact B.
Qed.

Lemma dec_firstn_all ds : dec (firstn (length ds) ds) = dec ds.
Proof. rewrite firstn_all. reflexivity. Qed.

Lemma digit_val ds J : Forall (fun c => 48 <= c <= 57) ds -> (J < length ds)%nat -> 0 <= nth J ds 0 - 48 <= 9.
Proof. intros H HJ. rewrite Forall_forall in H. specialize (H (nth J ds 0) (nth_In ds 0 HJ)). lia. Qed.

Theorem digit_step_facts ds J m :
  Forall (fun c => 48 <= c <= 57) ds -> (J < length ds)%nat -> (length ds <= m)%nat ->
  let V := dec (firstn J ds) in let d := nth J ds 0 - 48 in let V' := dec (firstn (S J) ds) in
  V' = 10 * V + d /\ 0 <= d <= 9 /\ 0 <= V < 10 ^ Z.of_nat J /\ 0 <= V' < 10 ^ Z.of_nat (S J) /\
  (nwords V <= num_words_est m)%nat /\ (nwords (10 * V) <= num_words_est m)%nat /\ (nwords V' <= num_words_est m)%nat /\
  (nwords V + 1 <= round_up (num_words_est m))%nat /\ (nwords (10 * V) + 1 <= round_up (num_words_est m))%nat /\
  (nwords V' + 1 <= round_up (num_words_est m))%nat.
Proof.
  intros Hds HJ Hm. cbn zeta. pose proof (all_digits_Forall ds Hds) as AD.
  pose proof (dec_firstn_S ds J HJ) as E. pose proof (digit_val ds J Hds HJ) as Dd.
  pose proof (dec_firstn_bound ds J AD ltac:(lia)) as B. pose proof (dec_firstn_bound ds (S J) AD ltac:(lia)) as B'.
  destruct (digit_step_no_realloc (dec (firstn J ds)) (nth J ds 0 - 48) J m B Dd ltac:(lia)) as (R1 & R2 & R3 & R4).
  rewrite <- E in R3.
  pose proof (nwords_bound_le (dec (firstn J ds)) J m B ltac:(lia)).
  pose proof (nwords_bound_le (dec (firstn (S J) ds)) (S J) m B' ltac:(lia)).
  assert (nwords (10 * dec (firstn J ds)) <= num_words_est m)%nat.
  { eapply Nat.le_trans. 2: exact H0. apply nwords_mono. rewrite E. lia. }
  repeat split; auto; lia.
Qed.
