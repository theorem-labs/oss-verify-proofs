(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ItCovBits ItCovPre.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_le : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow2_split : forall a b, 0 <= a -> 0 <= b -> 2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. intros. apply Z.pow_add_r; lia. Qed.

Lemma brv_brv : forall (w : nat) v, 0 <= v < 2 ^ Z.of_nat w -> brv w (brv w v) = v.
Proof.
  intros w v Hv. apply Z.bits_inj'. intros j Hj.
  destruct (Z_lt_le_dec j (Z.of_nat w)).
  - rewrite brv_testbit by lia. rewrite brv_testbit by lia. f_equal. lia.
  - rewrite brv_testbit_high by lia. symmetry. apply (testbit_lt_pow2 v (Z.of_nat w)); lia.
Qed.


Lemma brv_shiftr : forall (w u : nat) C, (u <= w)%nat -> 0 <= C ->
  brv w C / 2 ^ Z.of_nat u = brv (w - u) (C mod 2 ^ Z.of_nat (w - u)).
Proof.
  intros w u C Hu HC. apply Z.bits_inj'. intros j Hj.
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_spec by lia.
  destruct (Z_lt_le_dec j (Z.of_nat (w - u))).
  - rewrite brv_testbit by lia. rewrite brv_testbit by lia.
    rewrite Z.mod_pow2_bits_low by lia. f_equal. lia.
  - rewrite brv_testbit_high by lia. rewrite brv_testbit_high by lia. reflexivity.
Qed.

Lemma low_bits_brv_iff : forall (w u : nat) x c,
  (u <= w)%nat -> 0 <= x < 2 ^ Z.of_nat w -> 0 <= c < 2 ^ Z.of_nat u ->
  (x mod 2 ^ Z.of_nat u = brv u c <-> brv w x / 2 ^ Z.of_nat (w - u) = c).
Proof.
  intros w u x c Hu Hx Hc.
  rewrite <- (brv_brv w x Hx) at 1.
  rewrite brv_mod_pow2 by (try lia; apply brv_nonneg).
  split.
  - intros H. apply (brv_inj u); [| exact Hc | exact H].
    pose proof (brv_range w x). split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|].
    apply Z.div_lt_upper_bound; [apply pow2_pos; lia|].
    rewrite <- pow2_split by lia. replace (Z.of_nat (w - u) + Z.of_nat u) with (Z.of_nat w) by lia. lia.
  - intros ->. reflexivity.
Qed.

Lemma low_bits_brv_iffZ : forall (W U : Z) x c,
  0 <= U <= W -> 0 <= x < 2 ^ W -> 0 <= c < 2 ^ U ->
  (x mod 2 ^ U = brv (Z.to_nat U) c <-> brv (Z.to_nat W) x / 2 ^ (W - U) = c).
Proof.
  intros W U x c HU.
  assert (HUW : (Z.to_nat U <= Z.to_nat W)%nat) by lia.
  assert (E1 : Z.of_nat (Z.to_nat U) = U) by lia.
  assert (E2 : Z.of_nat (Z.to_nat W) = W) by lia.
  assert (E3 : Z.of_nat (Z.to_nat W - Z.to_nat U) = W - U) by lia.
  intros Hx Hc.
  pose proof (low_bits_brv_iff (Z.to_nat W) (Z.to_nat U) x c HUW) as I.
  rewrite E1, E2, E3 in I. exact (I Hx Hc).
Qed.


Lemma step_over : forall (f : Z -> Z) a e y,
  a < e -> f a <= y < f e ->
  exists k, a <= k < e /\ f k <= y < f (k + 1).
Proof.
  intros f a e y Hae Hy.
  remember (Z.to_nat (e - a)) as n eqn:Hn.
  assert (He : e = a + Z.of_nat n) by lia. subst e. clear Hn Hae.
  revert Hy. induction n as [|n IH]; intros Hy.
  - rewrite Z.add_0_r in Hy. lia.
  - destruct (Z_lt_le_dec y (f (a + Z.of_nat n))).
    + destruct (IH (conj (proj1 Hy) l)) as (k & Hk & Hk'). exists k. split; [lia|exact Hk'].
    + exists (a + Z.of_nat n). split; [lia|]. replace (a + Z.of_nat n + 1) with (a + Z.of_nat (S n)) by lia. lia.
Qed.


Section Tiling.
  Variables (d : Z -> Z) (a e w : Z).
  Hypothesis Hw : 0 <= w <= 16.
  Hypothesis Hae : a <= e.
  Hypothesis Hd : forall k, a <= k < e -> 0 <= d k <= w.
  Hypothesis Hmono : forall k k', a <= k <= k' -> k' < e -> d k <= d k'.

  Definition T (k : Z) : Z := sumZ (fun k => 2 ^ (w - d k)) a k.

  Hypothesis Hbound : T e <= 2 ^ w.

  Lemma T_a : T a = 0.
  Proof. unfold T. apply sumZ_nil. lia. Qed.
  Lemma T_step : forall k, a <= k -> T (k + 1) = T k + 2 ^ (w - d k).
  Proof. intros k Hk. unfold T. apply (sumZ_snoc (fun k0 => 2 ^ (w - d k0)) a k). lia. Qed.
  Lemma T_mono : forall k k', a <= k <= k' -> T k <= T k'.
  Proof.
    intros k k' H. unfold T. rewrite (sumZ_split _ a k k') by lia.
    pose proof (sumZ_nonneg (fun k0 => 2 ^ (w - d k0)) k k' ltac:(intros; apply Z.pow_nonneg; lia)). lia.
  Qed.
  Lemma T_nonneg : forall k, a <= k -> 0 <= T k.
  Proof. intros k Hk. rewrite <- T_a. apply T_mono. lia. Qed.

  Lemma T_div : forall k, a <= k < e -> T k mod 2 ^ (w - d k) = 0.
  Proof.
    intros k Hk. pose proof (Hd k Hk) as Hdk.
    assert (G : forall n, Z.of_nat n <= k - a -> T (a + Z.of_nat n) mod 2 ^ (w - d k) = 0).
    { induction n as [|n IH]; intros Hn.
      - rewrite Z.add_0_r, T_a. reflexivity.
      - replace (a + Z.of_nat (S n)) with (a + Z.of_nat n + 1) by lia. rewrite T_step by lia.
        rewrite Z.add_mod by (apply Z.pow_nonzero; lia). rewrite IH by lia.
        pose proof (Hmono (a + Z.of_nat n) k ltac:(lia) ltac:(lia)).
        pose proof (Hd (a + Z.of_nat n) ltac:(lia)).
        replace (2 ^ (w - d (a + Z.of_nat n))) with (2 ^ (d k - d (a + Z.of_nat n)) * 2 ^ (w - d k))
          by (rewrite <- pow2_split by lia; f_equal; lia).
        rewrite Z.mod_mul by (apply Z.pow_nonzero; lia). reflexivity. }
    replace k with (a + Z.of_nat (Z.to_nat (k - a))) at 1 by lia. apply G. lia.
  Qed.

  Definition cw (k : Z) : Z := T k / 2 ^ (w - d k).

  Lemma cw_range : forall k, a <= k < e -> 0 <= cw k < 2 ^ d k.
  Proof.
    intros k Hk. unfold cw. pose proof (Hd k Hk).
    pose proof (T_nonneg k ltac:(lia)). pose proof (T_mono (k + 1) e ltac:(lia)).
    rewrite T_step in * by lia.
    split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|].
    apply Z.div_lt_upper_bound; [apply pow2_pos; lia|].
    rewrite <- pow2_split by lia. replace (w - d k + d k) with w by lia. lia.
  Qed.

  Lemma cw_T : forall k, a <= k < e -> T k = cw k * 2 ^ (w - d k).
  Proof.
    intros k Hk. unfold cw. pose proof (T_div k Hk). pose proof (pow2_pos (w - d k) ltac:(pose proof (Hd k Hk); lia)).
    rewrite (Z.div_mod (T k) (2 ^ (w - d k))) at 1 by lia. lia.
  Qed.

  Lemma tile_cover : forall x, 0 <= x < 2 ^ w -> brv (Z.to_nat w) x < T e ->
    exists k, a <= k < e /\ x mod 2 ^ d k = brv (Z.to_nat (d k)) (cw k).
  Proof.
    intros x Hx Hxe.
    set (y := brv (Z.to_nat w) x) in *.
    assert (Hy : 0 <= y < 2 ^ w).
    { pose proof (brv_range (Z.to_nat w) x). rewrite Z2Nat.id in * by lia. unfold y. lia. }
    assert (Hae' : a < e).
    { destruct (Z.eq_dec a e); [|lia]. exfalso. subst e. rewrite T_a in Hxe. lia. }
    destruct (step_over T a e y Hae') as (k & Hk & Hk2). { rewrite T_a. lia. }
    exists k. split; [exact Hk|].
    pose proof (Hd k Hk) as Hdk.
    rewrite T_step in Hk2 by lia. rewrite (cw_T k Hk) in Hk2.
    assert (E : y / 2 ^ (w - d k) = cw k).
    { pose proof (pow2_pos (w - d k) ltac:(lia)).
      symmetry. apply Z.div_unique with (r := y - cw k * 2 ^ (w - d k)); [left; lia| nia]. }
    apply (proj2 (low_bits_brv_iffZ w (d k) x (cw k) ltac:(lia) Hx (cw_range k Hk))).
    unfold y in E. exact E.
  Qed.
End Tiling.


Fixpoint findN (P : Z -> bool) (lo : Z) (n : nat) : Z :=
  match n with
  | O => lo
  | S k => if P lo then lo else findN P (lo + 1) k
  end.
Definition findZ (P : Z -> bool) (lo hi : Z) : Z := findN P lo (Z.to_nat (hi - lo)).

Lemma findZ_spec : forall P lo hi, lo <= hi ->
  lo <= findZ P lo hi <= hi
  /\ (findZ P lo hi < hi -> P (findZ P lo hi) = true)
  /\ (forall k, lo <= k < findZ P lo hi -> P k = false).
Proof.
  intros P lo hi Hlh. unfold findZ.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  assert (Hhi : hi = lo + Z.of_nat n) by lia. rewrite Hhi. clear Hhi Hn Hlh.
  revert lo. induction n as [|n IH]; intros lo.
  - cbn [findN]. rewrite Z.add_0_r. split; [lia|]. split; [lia|]. intros; lia.
  - cbn [findN]. destruct (P lo) eqn:E.
    + split; [lia|]. split; [intros; exact E|]. intros; lia.
    + destruct (IH (lo + 1)) as (A & B & C). replace (lo + Z.of_nat (S n)) with (lo + 1 + Z.of_nat n) by lia.
      split; [lia|]. split; [exact B|]. intros k Hk.
      destruct (Z.eq_dec k lo) as [->|]; [exact E|]. apply C. lia.
Qed.


Section Canon.
  Variables (N : Z) (Lf : Z -> Z) (root : Z).
  Hypothesis HN : 1 <= N.
  Hypothesis HL : forall i, 0 <= i < N -> 1 <= Lf i <= 15.
  Hypothesis Hsorted : forall i j, 0 <= i <= j -> j < N -> Lf i <= Lf j.
  Hypothesis Hroot : 1 <= root <= 15.
  Hypothesis Hrootmin : Lf 0 <= root.

  Definition SK (i : Z) : Z := T Lf 0 15 i.
  Hypothesis Hcomplete : SK N = 2 ^ 15.

  Lemma S_0 : SK 0 = 0.
  Proof. unfold SK. apply T_a. Qed.
  Lemma S_step : forall i, 0 <= i -> SK (i + 1) = SK i + 2 ^ (15 - Lf i).
  Proof. intros. unfold SK. apply T_step. lia. Qed.
  Lemma S_mono : forall i j, 0 <= i <= j -> SK i <= SK j.
  Proof. intros. unfold SK. apply T_mono. lia. Qed.
  Lemma S_lt : forall i j, 0 <= i < j -> j <= N -> SK i < SK j.
  Proof.
    intros i j Hij Hj. pose proof (S_step i ltac:(lia)). pose proof (S_mono (i + 1) j ltac:(lia)).
    pose proof (pow2_pos (15 - Lf i) ltac:(pose proof (HL i); lia)). lia.
  Qed.
  Lemma S_nonneg : forall i, 0 <= i -> 0 <= SK i.
  Proof. intros. rewrite <- S_0. apply S_mono. lia. Qed.
  Lemma S_le : forall i, 0 <= i <= N -> SK i <= 2 ^ 15.
  Proof. intros. rewrite <- Hcomplete. apply S_mono. lia. Qed.
  Lemma HdL : forall k, 0 <= k < N -> 0 <= Lf k <= 15.
  Proof. intros k Hk. pose proof (HL k Hk). lia. Qed.
  Lemma HmL : forall k k', 0 <= k <= k' -> k' < N -> Lf k <= Lf k'.
  Proof. intros. apply Hsorted; lia. Qed.

  Definition cc (i : Z) : Z := cw Lf 0 15 i.

  Lemma HbL : T Lf 0 15 N <= 2 ^ 15.
  Proof. unfold SK in Hcomplete. rewrite Hcomplete. lia. Qed.
  Lemma cc_range : forall i, 0 <= i < N -> 0 <= cc i < 2 ^ Lf i.
  Proof. intros. unfold cc. apply (cw_range Lf 0 N 15 ltac:(lia) HdL HbL). lia. Qed.
  Lemma cc_S : forall i, 0 <= i < N -> SK i = cc i * 2 ^ (15 - Lf i).
  Proof. intros. unfold SK, cc. apply (cw_T Lf 0 N 15 ltac:(lia) HdL HmL). lia. Qed.

  Lemma cc_succ : forall i, 0 <= i -> i + 1 < N ->
    cc i + 1 < 2 ^ Lf i /\ cc (i + 1) = (cc i + 1) * 2 ^ (Lf (i + 1) - Lf i).
  Proof.
    intros i Hi HiN.
    pose proof (HL i ltac:(lia)) as HLi. pose proof (HL (i + 1) ltac:(lia)) as HLi1.
    pose proof (Hsorted i (i + 1) ltac:(lia) ltac:(lia)) as Hs.
    pose proof (cc_S i ltac:(lia)) as E0. pose proof (cc_S (i + 1) ltac:(lia)) as E1.
    pose proof (S_step i ltac:(lia)) as St.
    pose proof (S_lt (i + 1) N ltac:(lia) ltac:(lia)) as Lt. rewrite Hcomplete in Lt.
    pose proof (cc_range (i + 1) ltac:(lia)) as R1. pose proof (cc_range i ltac:(lia)) as R0.
    assert (P : 2 ^ (15 - Lf i) = 2 ^ (Lf (i + 1) - Lf i) * 2 ^ (15 - Lf (i + 1))).
    { rewrite <- pow2_split by lia. f_equal. lia. }
    assert (P2 : 2 ^ 15 = 2 ^ Lf i * 2 ^ (15 - Lf i)).
    { rewrite <- pow2_split by lia. f_equal. lia. }
    pose proof (pow2_pos (15 - Lf (i + 1)) ltac:(lia)) as Q1. pose proof (pow2_pos (Lf (i + 1) - Lf i) ltac:(lia)) as Q2.
    set (g1 := 2 ^ (15 - Lf (i + 1))) in *. set (q := 2 ^ (Lf (i + 1) - Lf i)) in *.
    set (g0 := 2 ^ (15 - Lf i)) in *. set (P15 := 2 ^ 15) in *. set (PL := 2 ^ Lf i) in *.
    assert (A : cc i + 1 < PL).
    { nia. }
    split; [exact A|].
    apply Z.mul_reg_r with (p := g1); [lia|]. nia.
  Qed.

  Lemma cc_last : cc (N - 1) + 1 = 2 ^ Lf (N - 1).
  Proof.
    pose proof (HL (N - 1) ltac:(lia)) as HLi.
    pose proof (cc_S (N - 1) ltac:(lia)) as E0. pose proof (S_step (N - 1) ltac:(lia)) as St.
    replace (N - 1 + 1) with N in St by lia. rewrite Hcomplete in St.
    assert (P2 : 2 ^ 15 = 2 ^ Lf (N - 1) * 2 ^ (15 - Lf (N - 1))).
    { rewrite <- pow2_split by lia. f_equal. lia. }
    pose proof (pow2_pos (15 - Lf (N - 1)) ltac:(lia)).
    set (g := 2 ^ (15 - Lf (N - 1))) in *.
    apply Z.mul_reg_r with (p := g); [lia|]. nia.
  Qed.

  Definition hf (i : Z) : Z := brv (Z.to_nat (Lf i)) (cc i).

  Lemma hf_range : forall i, 0 <= i < N -> 0 <= hf i < 2 ^ Lf i.
  Proof. intros i Hi. unfold hf. pose proof (brv_range (Z.to_nat (Lf i)) (cc i)). pose proof (HL i Hi). rewrite Z2Nat.id in * by lia. lia. Qed.

  Lemma hf_succ : forall i, 0 <= i -> i + 1 < N -> it_rev_incr (hf i) (Lf i) = hf (i + 1).
  Proof.
    intros i Hi HiN. destruct (cc_succ i Hi HiN) as [A B].
    pose proof (HL i ltac:(lia)). pose proof (HL (i + 1) ltac:(lia)). pose proof (Hsorted i (i + 1) ltac:(lia) ltac:(lia)).
    pose proof (cc_range i ltac:(lia)).
    unfold hf. rewrite it_rev_incr_succZ by lia. rewrite B.
    replace (Z.to_nat (Lf (i + 1))) with (Z.to_nat (Lf (i + 1) - Lf i) + Z.to_nat (Lf i))%nat by lia.
    rewrite Z.mul_comm. replace (2 ^ (Lf (i + 1) - Lf i)) with (2 ^ Z.of_nat (Z.to_nat (Lf (i + 1) - Lf i))) by (f_equal; lia).
    symmetry. apply brv_shift.
  Qed.

  Lemma hf_last : it_rev_incr (hf (N - 1)) (Lf (N - 1)) = 0.
  Proof.
    pose proof (HL (N - 1) ltac:(lia)). unfold hf.
    replace (cc (N - 1)) with (2 ^ Lf (N - 1) - 1) by (pose proof cc_last; lia).
    apply it_rev_incr_lastZ. lia.
  Qed.


  Definition m : Z := findZ (fun i => root <? Lf i) 0 N.

  Lemma m_spec : 1 <= m <= N /\ (forall i, 0 <= i < m -> Lf i <= root) /\ (forall i, m <= i < N -> root < Lf i).
  Proof.
    unfold m. destruct (findZ_spec (fun i => root <? Lf i) 0 N ltac:(lia)) as (A & B & C).
    assert (D : forall i, 0 <= i < findZ (fun i0 : Z => root <? Lf i0) 0 N -> Lf i <= root).
    { intros i Hi. pose proof (C i Hi) as E. apply Z.ltb_ge in E. exact E. }
    split; [|split; [exact D|]].
    - split; [|lia]. destruct (Z.eq_dec (findZ (fun i : Z => root <? Lf i) 0 N) 0); [|lia].
      exfalso. pose proof (B ltac:(lia)) as E. rewrite e in E. apply Z.ltb_lt in E. lia.
    - intros i Hi. pose proof (B ltac:(lia)) as E. apply Z.ltb_lt in E.
      pose proof (Hsorted (findZ (fun i0 : Z => root <? Lf i0) 0 N) i ltac:(lia) ltac:(lia)). lia.
  Qed.

  Definition B : Z := 2 ^ (15 - root).
  Lemma B_pos : 0 < B.
  Proof. unfold B. apply pow2_pos. lia. Qed.

  Lemma S_short : forall k, 0 <= k <= m -> SK k = T Lf 0 root k * B.
  Proof.
    intros k Hk. destruct m_spec as (A & D & _). unfold SK, T, B. rewrite (Z.mul_comm _ (2 ^ (15 - root))), <- sumZ_scale.
    apply sumZ_ext. intros j Hj. pose proof (D j ltac:(lia)). pose proof (HL j ltac:(lia)).
    rewrite <- pow2_split by lia. f_equal. lia.
  Qed.

  Lemma T_root_bound : T Lf 0 root m <= 2 ^ root.
  Proof.
    destruct m_spec as (A & _ & _). pose proof (S_le m ltac:(lia)) as H. rewrite S_short in H by lia.
    unfold B in H. replace (2 ^ 15) with (2 ^ root * 2 ^ (15 - root)) in H by (rewrite <- pow2_split by lia; f_equal; lia).
    pose proof (pow2_pos (15 - root) ltac:(lia)). nia.
  Qed.

  Lemma cc_short : forall k, 0 <= k < m -> cw Lf 0 root k = cc k.
  Proof.
    intros k Hk. destruct m_spec as (A & D & _). pose proof (D k Hk). pose proof (HL k ltac:(lia)).
    unfold cc, cw. fold (SK k). rewrite S_short by lia. unfold B.
    replace (2 ^ (15 - Lf k)) with (2 ^ (root - Lf k) * 2 ^ (15 - root)) by (rewrite <- pow2_split by lia; f_equal; lia).
    rewrite Z.div_mul_cancel_r; [reflexivity | apply Z.pow_nonzero; lia | apply Z.pow_nonzero; lia].
  Qed.

  Lemma root_fill_cover : forall x, 0 <= x < 2 ^ root -> brv (Z.to_nat root) x < T Lf 0 root m ->
    exists k, 0 <= k < m /\ x mod 2 ^ Lf k = hf k.
  Proof.
    intros x Hx Hlt. destruct m_spec as (A & D & _).
    destruct (tile_cover Lf 0 m root ltac:(lia) ltac:(lia)
                ltac:(intros k Hk; pose proof (D k Hk); pose proof (HL k ltac:(lia)); lia)
                ltac:(intros k k' H1 H2; apply Hsorted; lia) T_root_bound x Hx Hlt) as (k & Hk & E).
    exists k. split; [exact Hk|]. unfold hf. rewrite <- cc_short by lia. exact E.
  Qed.


  Definition pp (j : Z) : Z := SK j / B.

  Lemma pp_m : SK m = pp m * B.
  Proof. destruct m_spec as (A & _ & _). unfold pp. rewrite (S_short m) by lia. rewrite Z.div_mul by (pose proof B_pos; lia). reflexivity. Qed.

  Lemma pp_mono : forall i j, 0 <= i <= j -> pp i <= pp j.
  Proof. intros. unfold pp. apply Z.div_le_mono; [apply B_pos | apply S_mono; lia]. Qed.

  Lemma pp_range : forall j, m <= j < N -> pp m <= pp j < 2 ^ root.
  Proof.
    intros j Hj. destruct m_spec as (A & _ & _). split; [apply pp_mono; lia|].
    unfold pp. apply Z.div_lt_upper_bound; [apply B_pos|]. unfold B.
    rewrite <- pow2_split by lia. replace (15 - root + root) with 15 by lia. rewrite <- Hcomplete. apply S_lt; lia.
  Qed.

  Lemma pp_cc : forall j, m <= j < N -> pp j = cc j / 2 ^ (Lf j - root).
  Proof.
    intros j Hj. destruct m_spec as (A & _ & D). pose proof (D j Hj). pose proof (HL j ltac:(lia)).
    unfold pp. rewrite (cc_S j) by lia. unfold B.
    replace (2 ^ (15 - root)) with (2 ^ (Lf j - root) * 2 ^ (15 - Lf j)) by (rewrite <- pow2_split by lia; f_equal; lia).
    rewrite Z.div_mul_cancel_r; [reflexivity | apply Z.pow_nonzero; lia | apply Z.pow_nonzero; lia].
  Qed.

  Lemma hf_low : forall j, m <= j < N -> hf j mod 2 ^ root = brv (Z.to_nat root) (pp j).
  Proof.
    intros j Hj. destruct m_spec as (A & _ & D). pose proof (D j Hj). pose proof (HL j ltac:(lia)).
    pose proof (cc_range j ltac:(lia)).
    unfold hf. rewrite pp_cc by exact Hj.
    replace (2 ^ root) with (2 ^ Z.of_nat (Z.to_nat root)) by (f_equal; lia).
    rewrite brv_mod_pow2 by lia. f_equal. f_equal. f_equal. lia.
  Qed.


  Lemma pp_step : forall j, m <= j -> j + 1 < N ->
    (pp (j + 1) = pp j /\ SK (j + 1) < (pp j + 1) * B) \/ (pp (j + 1) = pp j + 1 /\ SK (j + 1) = (pp j + 1) * B).
  Proof.
    intros j Hj HjN. destruct m_spec as (A & _ & D). pose proof (D j ltac:(lia)) as Dj. pose proof (HL j ltac:(lia)) as HLj.
    pose proof (cc_range j ltac:(lia)) as Rc.
    set (g := 2 ^ (15 - Lf j)). set (q := 2 ^ (Lf j - root)).
    assert (Hg : 0 < g) by (unfold g; apply pow2_pos; lia).
    assert (Hq : 0 < q) by (unfold q; apply pow2_pos; lia).
    assert (HB : B = q * g) by (unfold B, q, g; rewrite <- pow2_split by lia; f_equal; lia).
    pose proof (cc_S j ltac:(lia)) as E0. fold g in E0.
    pose proof (S_step j ltac:(lia)) as St. fold g in St.
    assert (P0 : pp j = cc j / q).
    { unfold pp. rewrite E0, HB. rewrite Z.div_mul_cancel_r by lia. reflexivity. }
    assert (P1 : pp (j + 1) = (cc j + 1) / q).
    { unfold pp. rewrite St, E0, HB. replace (cc j * g + g) with ((cc j + 1) * g) by lia.
      rewrite Z.div_mul_cancel_r by lia. reflexivity. }
    pose proof (Z.div_mod (cc j) q ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (cc j) q Hq) as MB.
    set (u := cc j / q) in *. set (v := cc j mod q) in *.
    destruct (Z_lt_le_dec (v + 1) q).
    - left. assert (E : (cc j + 1) / q = u).
      { symmetry. apply Z.div_unique with (r := v + 1); [left; lia | lia]. }
      rewrite P1, P0, E. split; [reflexivity|]. rewrite St, E0, HB. nia.
    - right. assert (E : (cc j + 1) / q = u + 1).
      { symmetry. apply Z.div_unique with (r := 0); [left; lia | lia]. }
      rewrite P1, P0, E. split; [reflexivity|]. rewrite St, E0, HB. nia.
  Qed.

  Lemma pp_last : m < N -> pp (N - 1) = 2 ^ root - 1.
  Proof.
    intros HmN. destruct m_spec as (A & _ & D). pose proof (D (N - 1) ltac:(lia)) as Dj. pose proof (HL (N - 1) ltac:(lia)) as HLj.
    pose proof (S_step (N - 1) ltac:(lia)) as St. replace (N - 1 + 1) with N in St by lia. rewrite Hcomplete in St.
    set (g := 2 ^ (15 - Lf (N - 1))) in *.
    assert (Hg : 0 < g) by (unfold g; apply pow2_pos; lia).
    assert (HgB : g <= B) by (unfold g, B; apply pow2_le; lia).
    assert (P : 2 ^ 15 = 2 ^ root * B) by (unfold B; rewrite <- pow2_split by lia; f_equal; lia).
    pose proof B_pos.
    unfold pp. symmetry. apply Z.div_unique with (r := B - g); [left; lia | nia].
  Qed.

  Definition is_block (a e : Z) : Prop :=
    m <= a < e /\ e <= N /\ SK a = pp a * B /\ (forall k, a <= k < e -> pp k = pp a) /\ SK e = (pp a + 1) * B.

  Definition be (a : Z) : Z := findZ (fun k => negb (pp k =? pp a)) (a + 1) N.






  Section Block.
    Variables a e : Z.
    Hypothesis HB : is_block a e.

    Definition D : Z := Lf (e - 1) - root.
    Definition dsub (k : Z) : Z := Lf k - root.

    Lemma D_range : 1 <= D <= 15 - root.
    Proof. destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. destruct m_spec as (A & _ & Dm). pose proof (Dm (e - 1) ltac:(lia)). pose proof (HL (e - 1) ltac:(lia)). unfold D. lia. Qed.
    Lemma dsub_range : forall k, a <= k < e -> 1 <= dsub k <= D.
    Proof.
      intros k Hk. destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. destruct m_spec as (A & _ & Dm). pose proof (Dm k ltac:(lia)).
      pose proof (Hsorted k (e - 1) ltac:(lia) ltac:(lia)). unfold dsub, D. lia.
    Qed.
    Lemma dsub_mono : forall k k', a <= k <= k' -> k' < e -> dsub k <= dsub k'.
    Proof. intros. unfold dsub. destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. pose proof (Hsorted k k' ltac:(lia) ltac:(lia)). lia. Qed.

    Lemma T_sub : forall k, a <= k <= e -> SK k - SK a = T dsub a D k * 2 ^ (15 - root - D).
    Proof.
      intros k Hk. destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. pose proof D_range as DR.
      unfold SK, T. rewrite (sumZ_split _ 0 a k) by lia.
      replace (sumZ (fun k0 : Z => 2 ^ (15 - Lf k0)) 0 a + sumZ (fun k0 : Z => 2 ^ (15 - Lf k0)) a k - sumZ (fun k0 : Z => 2 ^ (15 - Lf k0)) 0 a)
        with (sumZ (fun k0 : Z => 2 ^ (15 - Lf k0)) a k) by lia.
      rewrite (Z.mul_comm _ (2 ^ (15 - root - D))), <- sumZ_scale. apply sumZ_ext. intros j Hj.
      pose proof (dsub_range j ltac:(lia)). unfold dsub in *.
      rewrite <- pow2_split by lia. f_equal. lia.
    Qed.

    Lemma T_sub_full : T dsub a D e = 2 ^ D.
    Proof.
      destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. pose proof D_range as DR.
      pose proof (T_sub e ltac:(lia)) as E. rewrite H5, H3 in E.
      replace ((pp a + 1) * B - pp a * B) with B in E by lia. unfold B in E.
      replace (2 ^ (15 - root)) with (2 ^ D * 2 ^ (15 - root - D)) in E by (rewrite <- pow2_split by lia; f_equal; lia).
      pose proof (pow2_pos (15 - root - D) ltac:(lia)). nia.
    Qed.
    Lemma T_sub_bound : forall j, a <= j <= e -> T dsub a D j <= 2 ^ D.
    Proof. intros j Hj. rewrite <- T_sub_full. apply T_mono. lia. Qed.

    Lemma cw_sub : forall k, a <= k < e -> cw dsub a D k = cc k mod 2 ^ (Lf k - root).
    Proof.
      intros k Hk. destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. pose proof D_range as DR. pose proof (dsub_range k Hk) as dR.
      destruct m_spec as (A & _ & Dm). pose proof (HL k ltac:(lia)) as HLk. pose proof (Dm k ltac:(lia)) as Dk.
      assert (dR' : 1 <= Lf k - root <= D) by exact dR.
      unfold cw. pose proof (T_sub k ltac:(lia)) as E.
      rewrite (cc_S k) in E by lia. rewrite H3 in E. rewrite <- (H4 k Hk) in E. rewrite (pp_cc k) in E by lia.
      set (q := 2 ^ (Lf k - root)) in *. set (g := 2 ^ (15 - Lf k)) in *.
      assert (Hq : 0 < q) by (unfold q; apply pow2_pos; lia). assert (Hg : 0 < g) by (unfold g; apply pow2_pos; lia).
      assert (HBq : B = q * g) by (unfold B, q, g; rewrite <- pow2_split by lia; f_equal; lia). rewrite HBq in E.
      assert (Hgs : g = 2 ^ (D - dsub k) * 2 ^ (15 - root - D)) by (unfold g, dsub; rewrite <- pow2_split by lia; f_equal; lia).
      pose proof (pow2_pos (15 - root - D) ltac:(lia)) as P1. pose proof (pow2_pos (D - dsub k) ltac:(lia)) as P2.
      pose proof (Z.div_mod (cc k) q ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (cc k) q Hq) as MBd.
      assert (E2 : T dsub a D k = (cc k mod q) * 2 ^ (D - dsub k)) by nia.
      rewrite E2. apply Z.div_mul. lia.
    Qed.

    Lemma hf_high : forall k, a <= k < e -> hf k / 2 ^ root = brv (Z.to_nat (dsub k)) (cw dsub a D k).
    Proof.
      intros k Hk. destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. destruct m_spec as (A & _ & Dm).
      pose proof (Dm k ltac:(lia)). pose proof (HL k ltac:(lia)). pose proof (cc_range k ltac:(lia)).
      rewrite cw_sub by exact Hk. unfold hf, dsub.
      replace (2 ^ root) with (2 ^ Z.of_nat (Z.to_nat root)) by (f_equal; lia).
      rewrite (brv_shiftr (Z.to_nat (Lf k)) (Z.to_nat root)) by lia.
      replace (Z.to_nat (Lf k) - Z.to_nat root)%nat with (Z.to_nat (Lf k - root)) by lia.
      f_equal. f_equal. f_equal. lia.
    Qed.

    Lemma sub_fill_cover : forall j x, a <= j <= e -> 0 <= x < 2 ^ D -> brv (Z.to_nat D) x < T dsub a D j ->
      exists k, a <= k < j /\ x mod 2 ^ dsub k = hf k / 2 ^ root.
    Proof.
      intros j x Hj Hx Hlt. pose proof D_range.
      destruct (tile_cover dsub a j D ltac:(lia) ltac:(lia)
                  ltac:(intros k Hk; pose proof (dsub_range k ltac:(lia)); lia)
                  ltac:(intros k k' Q1 Q2; apply dsub_mono; lia) (T_sub_bound j Hj) x Hx Hlt) as (k & Hk & E).
      exists k. split; [exact Hk|]. rewrite hf_high by lia. exact E.
    Qed.
  End Block.


  Definition remf (a l : Z) : Z := sumZ (fun k => if Lf k =? l then 1 else 0) a N.
  Definition k1 (a v : Z) : Z := findZ (fun k => v <=? Lf k) a N.

  Lemma k1_spec : forall a v, 0 <= a <= N ->
    a <= k1 a v <= N /\ (forall k, a <= k < k1 a v -> Lf k < v) /\ (forall k, k1 a v <= k < N -> v <= Lf k).
  Proof.
    intros a v Ha. unfold k1. destruct (findZ_spec (fun k => v <=? Lf k) a N ltac:(lia)) as (A & B2 & C).
    split; [exact A|]. split.
    - intros k Hk. pose proof (C k Hk) as E. apply Z.leb_gt in E. exact E.
    - intros k Hk. destruct (Z_lt_le_dec (findZ (fun k0 : Z => v <=? Lf k0) a N) N).
      + pose proof (B2 l) as E. apply Z.leb_le in E. pose proof (Hsorted (findZ (fun k0 : Z => v <=? Lf k0) a N) k ltac:(lia) ltac:(lia)). lia.
      + lia.
  Qed.

  Lemma k1_mono : forall a v v', 0 <= a <= N -> v <= v' -> k1 a v <= k1 a v'.
  Proof.
    intros a v v' Ha Hv. destruct (k1_spec a v Ha) as (A & B2 & C). destruct (k1_spec a v' Ha) as (A' & B' & C').
    destruct (Z_lt_le_dec (k1 a v') (k1 a v)); [|lia].
    exfalso. pose proof (B2 (k1 a v') ltac:(lia)). destruct (Z_lt_le_dec (k1 a v') N).
    - pose proof (C' (k1 a v') ltac:(lia)). lia.
    - lia.
  Qed.

  Lemma remf_k1 : forall a v, 0 <= a <= N -> remf a v = k1 a (v + 1) - k1 a v.
  Proof.
    intros a v Ha. destruct (k1_spec a v Ha) as (A & B2 & C). destruct (k1_spec a (v + 1) Ha) as (A' & B' & C').
    pose proof (k1_mono a v (v + 1) Ha ltac:(lia)) as M.
    unfold remf. rewrite (sumZ_split _ a (k1 a v) N) by lia. rewrite (sumZ_split _ (k1 a v) (k1 a (v + 1)) N) by lia.
    rewrite (sumZ_ext _ (fun _ => 0) a (k1 a v)) by (intros j Hj; pose proof (B2 j Hj); destruct (Z.eqb_spec (Lf j) v); lia).
    rewrite (sumZ_ext _ (fun _ => 1) (k1 a v) (k1 a (v + 1))) by (intros j Hj; pose proof (C j ltac:(lia)); pose proof (B' j ltac:(lia)); destruct (Z.eqb_spec (Lf j) v); lia).
    rewrite (sumZ_ext _ (fun _ => 0) (k1 a (v + 1)) N) by (intros j Hj; pose proof (C' j Hj); destruct (Z.eqb_spec (Lf j) v); lia).
    rewrite !sumZ_zero.
    assert (ONE : forall lo hi, lo <= hi -> sumZ (fun _ => 1) lo hi = hi - lo).
    { intros lo hi Hlh. unfold sumZ. remember (Z.to_nat (hi - lo)) as n eqn:Hn. assert (hi - lo = Z.of_nat n) as -> by lia.
      clear. induction n; cbn [sumN]; lia. }
    rewrite ONE by lia. lia.
  Qed.

  Lemma SK_k1_diff : forall a v, 0 <= a <= N -> SK (k1 a (v + 1)) - SK (k1 a v) = (k1 a (v + 1) - k1 a v) * 2 ^ (15 - v).
  Proof.
    intros a v Ha. destruct (k1_spec a v Ha) as (A & B2 & C). destruct (k1_spec a (v + 1) Ha) as (A' & B' & C').
    pose proof (k1_mono a v (v + 1) Ha ltac:(lia)) as M.
    unfold SK, T. rewrite (sumZ_split _ 0 (k1 a v) (k1 a (v + 1))) by lia.
    rewrite (sumZ_ext _ (fun _ => 2 ^ (15 - v)) (k1 a v) (k1 a (v + 1))) by (intros j Hj; pose proof (C j ltac:(lia)); pose proof (B' j ltac:(lia)); f_equal; lia).
    assert (CST : forall c lo hi, lo <= hi -> sumZ (fun _ => c) lo hi = (hi - lo) * c).
    { intros c lo hi Hlh. unfold sumZ. remember (Z.to_nat (hi - lo)) as n eqn:Hn. assert (hi - lo = Z.of_nat n) as -> by lia.
      clear. induction n; cbn [sumN]; lia. }
    rewrite CST by lia. lia.
  Qed.

  Lemma remf_pos_self : forall a, 0 <= a < N -> 1 <= remf a (Lf a).
  Proof.
    intros a Ha. unfold remf. rewrite (sumZ_split _ a (a + 1) N) by lia.
    rewrite (sumZ_snoc _ a a), (sumZ_nil _ a a) by lia. cbv beta. rewrite Z.eqb_refl.
    pose proof (sumZ_nonneg (fun k : Z => if Lf k =? Lf a then 1 else 0) (a + 1) N ltac:(intros j Hj; cbv beta; destruct (Lf j =? Lf a); lia)). lia.
  Qed.
  Lemma remf_step : forall a l, 0 <= a < N -> remf (a + 1) l = remf a l - (if Lf a =? l then 1 else 0).
  Proof.
    intros a l Ha. unfold remf. rewrite (sumZ_split _ a (a + 1) N) by lia. rewrite (sumZ_snoc _ a a), (sumZ_nil _ a a) by lia. cbv beta. lia.
  Qed.
  Lemma remf_nonneg : forall a l, 0 <= remf a l.
  Proof. intros a l. unfold remf. apply sumZ_nonneg. intros j Hj; cbv beta; destruct (Lf j =? l); lia. Qed.
  Lemma remf_N : forall l, remf N l = 0.
  Proof. intros. unfold remf. apply sumZ_nil. lia. Qed.
  Lemma remf_le : forall a l, 0 <= a <= N -> remf a l <= N - a.
  Proof.
    intros a l Ha. unfold remf.
    pose proof (sumZ_mono (fun k : Z => if Lf k =? l then 1 else 0) (fun _ => 1) a N ltac:(intros j Hj; cbv beta; destruct (Lf j =? l); lia)).
    assert (CST : forall lo hi, lo <= hi -> sumZ (fun _ => 1) lo hi = (hi - lo)).
    { intros lo hi Hlh. unfold sumZ. remember (Z.to_nat (hi - lo)) as n eqn:Hn. assert (hi - lo = Z.of_nat n) as -> by lia.
      clear. induction n; cbn [sumN]; lia. }
    rewrite CST in H by lia. lia.
  Qed.
  Lemma remf_zero_next : forall a, 0 <= a -> a + 1 < N -> remf (a + 1) (Lf a) = 0 -> Lf a < Lf (a + 1).
  Proof.
    intros a Ha HaN Hz. pose proof (Hsorted a (a + 1) ltac:(lia) ltac:(lia)).
    destruct (Z.eq_dec (Lf a) (Lf (a + 1))); [|lia]. exfalso.
    pose proof (remf_pos_self (a + 1) ltac:(lia)). rewrite <- e in *. lia.
  Qed.
  Lemma remf_pos_next : forall a, 0 <= a -> a + 1 < N -> remf (a + 1) (Lf a) <> 0 -> Lf (a + 1) = Lf a.
  Proof.
    intros a Ha HaN Hz. pose proof (Hsorted a (a + 1) ltac:(lia) ltac:(lia)).
    destruct (Z.eq_dec (Lf (a + 1)) (Lf a)); [lia|]. exfalso. apply Hz.
    unfold remf. rewrite (sumZ_ext _ (fun _ => 0)); [apply sumZ_zero|].
    intros j Hj. pose proof (Hsorted (a + 1) j ltac:(lia) ltac:(lia)). destruct (Z.eqb_spec (Lf j) (Lf a)); lia.
  Qed.

  Section Subsz.
    Variables a e : Z.
    Hypothesis HB : is_block a e.
    Variable count : arr.
    Hypothesis Hcount : forall l, 1 <= l <= 15 -> arr_get count l = remf a l.
    Variable max : Z.
    Hypothesis Hmax : max = Lf (N - 1).

    Let Dd := D e.

    Definition subsz_body (cl : Z * Z) : bool * (Z * Z) :=
      let '(curr, lft) := cl in
      if wrap32 (curr + root) <? max then
        let lft := lft - arr_get count (wrap32 (curr + root)) in
        if lft <=? 0 then (false, (curr, lft)) else (true, (wrap32 (curr + 1), Z.shiftl lft 1))
      else (false, (curr, lft)).

    Lemma subsz_eq : it_subtable_curr count (Lf a) root max =
      fst (loopZ 16 subsz_body (wrap32 (Lf a - root), swrap32 (Z.shiftl 1 (wrap32 (Lf a - root))))).
    Proof. reflexivity. Qed.

    Lemma subsz_loop : forall (n : nat) c lft,
      Lf a - root <= c <= Dd -> Z.of_nat n >= Dd - c + 1 ->
      lft * 2 ^ (15 - root - c) = SK e - SK (k1 a (root + c)) ->
      fst (loopZ (Z.of_nat n) subsz_body (c, lft)) = Dd.
    Proof.
      induction n as [|n IH]; intros c lft Hc Hn Hl; [lia|].
      destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. destruct m_spec as (_ & _ & Dm).
      pose proof (D_range a e HB) as DR. unfold Dd in *.
      pose proof (Dm a ltac:(lia)) as Da. pose proof (HL (e - 1) ltac:(lia)) as HLe.
      assert (HDe : D e = Lf (e - 1) - root) by reflexivity.
      rewrite loopZ_step by lia. unfold subsz_body at 1.
      rewrite (wrap32_id (c + root)) by lia.
      destruct (Z.ltb_spec (c + root) max).
      - rewrite Hcount by lia.
        destruct (k1_spec a (root + c) ltac:(lia)) as (K1 & K2 & K3).
        destruct (k1_spec a (root + c + 1) ltac:(lia)) as (K1' & K2' & K3').
        pose proof (remf_k1 a (root + c) ltac:(lia)) as RK. replace (c + root) with (root + c) by lia. rewrite RK.
        pose proof (SK_k1_diff a (root + c) ltac:(lia)) as SD.
        pose proof (pow2_pos (15 - root - c) ltac:(lia)) as Pu.
        replace (2 ^ (15 - (root + c))) with (2 ^ (15 - root - c)) in SD by (f_equal; lia).
        set (u := 2 ^ (15 - root - c)) in *.
        set (lft' := lft - (k1 a (root + c + 1) - k1 a (root + c))).
        assert (Hl' : lft' * u = SK e - SK (k1 a (root + c + 1))) by (unfold lft'; nia).
        destruct (Z.leb_spec lft' 0).
        +
          cbn [fst].
          destruct (Z_lt_le_dec c (Lf (e - 1) - root)); [|lia]. exfalso.
          assert (k1 a (root + c + 1) <= e - 1).
          { destruct (Z_lt_le_dec (e - 1) (k1 a (root + c + 1))); [|lia]. pose proof (K2' (e - 1) ltac:(lia)). lia. }
          pose proof (S_lt (k1 a (root + c + 1)) e ltac:(lia) ltac:(lia)). nia.
        +
          replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
          assert (Hc1 : c + 1 <= Lf (e - 1) - root).
          { destruct (Z_lt_le_dec c (Lf (e - 1) - root)); [lia|]. exfalso.
            assert (e <= k1 a (root + c + 1)).
            { destruct (Z_lt_le_dec (k1 a (root + c + 1)) e); [|lia].
              pose proof (K3' (k1 a (root + c + 1)) ltac:(lia)). pose proof (Hsorted (k1 a (root + c + 1)) (e - 1) ltac:(lia) ltac:(lia)). lia. }
            pose proof (S_mono e (k1 a (root + c + 1)) ltac:(lia)). nia. }
          rewrite (wrap32_id (c + 1)) by lia.
          apply IH; [lia|lia|].
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
          replace (root + (c + 1)) with (root + c + 1) by lia. rewrite <- Hl'.
          unfold u. replace (15 - root - c) with (Z.succ (15 - root - (c + 1))) by lia. rewrite Z.pow_succ_r by lia. lia.
      - cbn [fst]. pose proof (Hsorted (e - 1) (N - 1) ltac:(lia) ltac:(lia)). lia.
    Qed.

    Lemma subsz_spec : it_subtable_curr count (Lf a) root max = D e.
    Proof.
      rewrite subsz_eq. destruct HB as (H1 & H2 & H3 & H4 & H5). pose proof (proj1 m_spec) as Am. destruct m_spec as (_ & _ & Dm).
      pose proof (Dm a ltac:(lia)) as Da. pose proof (HL a ltac:(lia)) as HLa. pose proof (D_range a e HB) as DR.
      pose proof (dsub_range a e HB a ltac:(lia)) as Ra. unfold dsub in Ra.
      rewrite (wrap32_id (Lf a - root)) by lia.
      assert (P : Z.shiftl 1 (Lf a - root) = 2 ^ (Lf a - root)) by (apply Z.shiftl_1_l).
      rewrite P. rewrite swrap32_id.
      2: { split; [pose proof (pow2_pos (Lf a - root)); lia|]. apply Z.lt_le_trans with (m := 2 ^ 15); [apply Z.pow_lt_mono_r; lia|]. apply Z.pow_le_mono_r; lia. }
      apply (subsz_loop 16); [lia| change (Z.of_nat 16) with 16; lia |].
      destruct (k1_spec a (root + (Lf a - root)) ltac:(lia)) as (K1 & K2 & K3).
      assert (E : k1 a (root + (Lf a - root)) = a).
      { destruct (Z_lt_le_dec a (k1 a (root + (Lf a - root)))); [|lia]. pose proof (K2 a ltac:(lia)). lia. }
      rewrite E, H5, H3. replace ((pp a + 1) * B - pp a * B) with B by lia. unfold B.
      rewrite <- pow2_split by lia. f_equal. lia.
    Qed.
  End Subsz.


  Lemma findZ_unique : forall P lo hi r, lo <= r <= hi ->
    (r < hi -> P r = true) -> (forall k, lo <= k < r -> P k = false) -> findZ P lo hi = r.
  Proof.
    intros P lo hi r Hr HP HQ. destruct (findZ_spec P lo hi ltac:(lia)) as (A & B2 & C).
    destruct (Z.lt_total (findZ P lo hi) r) as [L|[E|G]]; [| exact E |].
    - exfalso. pose proof (HQ (findZ P lo hi) ltac:(lia)) as X. rewrite (B2 ltac:(lia)) in X. discriminate.
    - exfalso. pose proof (C r ltac:(lia)) as X. rewrite (HP ltac:(lia)) in X. discriminate.
  Qed.

  Definition kp (p : Z) : Z := findZ (fun k => p <=? pp k) m N.

  Lemma kp_spec : forall p,
    m <= kp p <= N /\ (forall k, m <= k < kp p -> pp k < p) /\ (forall k, kp p <= k < N -> p <= pp k).
  Proof.
    intros p. destruct m_spec as (A & _ & _). unfold kp.
    destruct (findZ_spec (fun k => p <=? pp k) m N ltac:(lia)) as (R & P & Q).
    split; [exact R|]. split.
    - intros k Hk. pose proof (Q k Hk) as E. apply Z.leb_gt in E. exact E.
    - intros k Hk. destruct (Z_lt_le_dec (findZ (fun k0 => p <=? pp k0) m N) N); [|lia].
      pose proof (P l) as E. apply Z.leb_le in E. pose proof (pp_mono (findZ (fun k0 => p <=? pp k0) m N) k ltac:(lia)). lia.
  Qed.


  Lemma kp_lt_N : forall p, m < N -> p < 2 ^ root -> kp p < N.
  Proof.
    intros p HmN Hp. destruct (kp_spec p) as (R & P & Q).
    destruct (Z_lt_le_dec (kp p) N); [assumption|]. exfalso.
    pose proof (P (N - 1) ltac:(lia)). rewrite pp_last in H by exact HmN. lia.
  Qed.


  Lemma kp_mono : forall p p', p <= p' -> kp p <= kp p'.
  Proof.
    intros p p' Hp. destruct (kp_spec p) as (R & P & Q). destruct (kp_spec p') as (R' & P' & Q').
    destruct (Z_lt_le_dec (kp p') (kp p)); [|lia]. exfalso.
    pose proof (P (kp p') ltac:(lia)). destruct (Z_lt_le_dec (kp p') N).
    - pose proof (Q' (kp p') ltac:(lia)). lia.
    - lia.
  Qed.

  Lemma kp_start : forall p, pp m <= p -> kp p < N -> pp (kp p) = p /\ SK (kp p) = p * B.
  Proof.
    intros p Hp HkN. destruct m_spec as (A & _ & _). destruct (kp_spec p) as (R & P & Q).
    pose proof (Q (kp p) ltac:(lia)) as GE.
    destruct (Z.eq_dec (kp p) m) as [E|E].
    - rewrite E in *. assert (pp m = p) as <- by lia. split; [reflexivity | apply pp_m].
    - pose proof (P (kp p - 1) ltac:(lia)) as LT.
      destruct (pp_step (kp p - 1) ltac:(lia) ltac:(lia)) as [[X _]|[X Y]];
        replace (kp p - 1 + 1) with (kp p) in * by lia.
      + exfalso. lia.
      + assert (pp (kp p) = p) as EQ by lia. split; [exact EQ|]. rewrite Y. f_equal. lia.
  Qed.

  Lemma kp_block : forall p, pp m <= p < 2 ^ root -> m < N -> is_block (kp p) (kp (p + 1)).
  Proof.
    intros p Hp HmN. destruct m_spec as (A & _ & _).
    pose proof (kp_lt_N p HmN ltac:(lia)) as K1.
    destruct (kp_start p ltac:(lia) K1) as [PP SS].
    destruct (kp_spec p) as (R & P & Q). destruct (kp_spec (p + 1)) as (R' & P' & Q').
    pose proof (kp_mono p (p + 1) ltac:(lia)) as M.
    assert (SAME : forall k, kp p <= k < kp (p + 1) -> pp k = p).
    { intros k Hk. pose proof (Q k ltac:(lia)). pose proof (P' k ltac:(lia)). lia. }
    assert (LT : kp p < kp (p + 1)).
    { destruct (Z_lt_le_dec (kp p) (kp (p + 1))); [assumption|]. exfalso.
      destruct (Z_lt_le_dec (kp (p + 1)) N).
      - pose proof (Q' (kp p) ltac:(lia)). lia.
      - lia. }
    unfold is_block. rewrite PP. split; [lia|]. split; [lia|]. split; [exact SS|]. split; [exact SAME|].
    destruct (Z_lt_le_dec (kp (p + 1)) N) as [L2|G2].
    - destruct (kp_start (p + 1) ltac:(lia) L2) as [_ S2]. exact S2.
    - assert (kp (p + 1) = N) as -> by lia. rewrite Hcomplete.
      pose proof (P' (N - 1) ltac:(lia)) as X. rewrite pp_last in X by exact HmN.
      assert (p = 2 ^ root - 1) as -> by lia. replace (2 ^ root - 1 + 1) with (2 ^ root) by lia.
      unfold B. rewrite <- pow2_split by lia. f_equal. lia.
  Qed.

  Lemma kp_of_pp : forall j, m <= j < N -> kp (pp j) <= j < kp (pp j + 1).
  Proof.
    intros j Hj. destruct (kp_spec (pp j)) as (R & P & Q). destruct (kp_spec (pp j + 1)) as (R' & P' & Q').
    split.
    - destruct (Z_lt_le_dec j (kp (pp j))); [|lia]. exfalso. pose proof (P j ltac:(lia)). lia.
    - destruct (Z_lt_le_dec j (kp (pp j + 1))); [assumption|]. exfalso. pose proof (Q' j ltac:(lia)). lia.
  Qed.

  Definition Dp (p : Z) : Z := D (kp (p + 1)).

  Lemma Dp_range : forall p, pp m <= p < 2 ^ root -> m < N -> 1 <= Dp p <= 15 - root.
  Proof. intros p Hp HmN. unfold Dp. apply (D_range (kp p)). apply kp_block; assumption. Qed.

  Definition SB (p : Z) : Z := sumZ (fun q => 2 ^ Dp q) (pp m) p.

  Lemma SB_first : SB (pp m) = 0.
  Proof. unfold SB. apply sumZ_nil. lia. Qed.
  Lemma SB_step : forall p, pp m <= p -> SB (p + 1) = SB p + 2 ^ Dp p.
  Proof. intros p Hp. unfold SB. rewrite (sumZ_snoc (fun q => 2 ^ Dp q) (pp m) p) by lia. reflexivity. Qed.
  Lemma SB_nonneg : forall p, 0 <= SB p.
  Proof. intros p. unfold SB. apply sumZ_nonneg. intros q Hq. cbv beta. apply Z.pow_nonneg. lia. Qed.
  Lemma SB_mono : forall p p', pp m <= p <= p' -> SB p <= SB p'.
  Proof.
    intros p p' Hp. unfold SB. rewrite (sumZ_split (fun q => 2 ^ Dp q) (pp m) p p') by lia.
    pose proof (sumZ_nonneg (fun q => 2 ^ Dp q) p p' ltac:(intros q Hq; cbv beta; apply Z.pow_nonneg; lia)). lia.
  Qed.
  Lemma SB_bound : forall p, pp m <= p <= 2 ^ root -> m < N -> SB p <= (p - pp m) * B.
  Proof.
    intros p Hp HmN. unfold SB.
    pose proof (sumZ_mono (fun q => 2 ^ Dp q) (fun _ => B) (pp m) p
                  ltac:(intros q Hq; cbv beta; pose proof (Dp_range q ltac:(lia) HmN); unfold B; apply pow2_le; lia)) as M.
    assert (CST : forall c lo hi, lo <= hi -> sumZ (fun _ => c) lo hi = (hi - lo) * c).
    { intros c lo hi Hlh. unfold sumZ. remember (Z.to_nat (hi - lo)) as n eqn:Hn. assert (hi - lo = Z.of_nat n) as -> by lia.
      clear. induction n; cbn [sumN]; lia. }
    rewrite CST in M by lia. lia.
  Qed.
End Canon.
