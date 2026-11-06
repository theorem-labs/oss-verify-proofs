(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition kb_val (m v u : Z) : Prop := Z.land u m = v.

Ltac bits := repeat first [rewrite Z.land_spec | rewrite Z.lor_spec | rewrite Z.lxor_spec | rewrite Z.ldiff_spec].

(* [comment removed for export] *)
Lemma kb_bit (m v u : Z) (i : Z) : kb_val m v u -> 0 <= i -> Z.testbit m i = true -> Z.testbit u i = Z.testbit v i.
Proof. intros H Hi Hm. rewrite <- H. rewrite Z.land_spec, Hm. rewrite andb_true_r. reflexivity. Qed.

Lemma kb_bit_out (m v u : Z) (i : Z) : kb_val m v u -> 0 <= i -> Z.testbit m i = false -> Z.testbit v i = false.
Proof. intros H Hi Hm. rewrite <- H. rewrite Z.land_spec, Hm. rewrite andb_false_r. reflexivity. Qed.

Lemma kb_intro (m v u : Z) : (forall i, 0 <= i -> Z.testbit (Z.land u m) i = Z.testbit v i) -> kb_val m v u.
Proof. intros H. unfold kb_val. apply Z.bits_inj'. exact H. Qed.

(* [comment removed for export] *)
Definition kbz_or (m1 v1 m2 v2 : Z) : Z * Z :=
  let ones := Z.lor v1 v2 in
  let zeros := Z.land (Z.ldiff m1 v1) (Z.ldiff m2 v2) in
  (Z.lor ones zeros, ones).

Lemma kbz_or_sound (m1 v1 m2 v2 u1 u2 : Z) :
  kb_val m1 v1 u1 -> kb_val m2 v2 u2 -> kb_val (fst (kbz_or m1 v1 m2 v2)) (snd (kbz_or m1 v1 m2 v2)) (Z.lor u1 u2).
Proof.
  intros H1 H2. apply kb_intro. intros i Hi. unfold kbz_or; cbn [fst snd].
  bits. unfold kb_val in *. rewrite <- H1, <- H2. bits.
  destruct (Z.testbit u1 i), (Z.testbit u2 i), (Z.testbit m1 i), (Z.testbit m2 i); reflexivity.
Qed.

Definition kbz_and (m1 v1 m2 v2 : Z) : Z * Z :=
  let ones := Z.land v1 v2 in
  let zeros := Z.lor (Z.ldiff m1 v1) (Z.ldiff m2 v2) in
  (Z.lor ones zeros, ones).

Lemma kbz_and_sound (m1 v1 m2 v2 u1 u2 : Z) :
  kb_val m1 v1 u1 -> kb_val m2 v2 u2 -> kb_val (fst (kbz_and m1 v1 m2 v2)) (snd (kbz_and m1 v1 m2 v2)) (Z.land u1 u2).
Proof.
  intros H1 H2. apply kb_intro. intros i Hi. unfold kbz_and; cbn [fst snd].
  bits. unfold kb_val in *. rewrite <- H1, <- H2. bits.
  destruct (Z.testbit u1 i), (Z.testbit u2 i), (Z.testbit m1 i), (Z.testbit m2 i); reflexivity.
Qed.

Definition kbz_xor (m1 v1 m2 v2 : Z) : Z * Z :=
  let m := Z.land m1 m2 in (m, Z.land (Z.lxor v1 v2) m).

Lemma kbz_xor_sound (m1 v1 m2 v2 u1 u2 : Z) :
  kb_val m1 v1 u1 -> kb_val m2 v2 u2 -> kb_val (fst (kbz_xor m1 v1 m2 v2)) (snd (kbz_xor m1 v1 m2 v2)) (Z.lxor u1 u2).
Proof.
  intros H1 H2. apply kb_intro. intros i Hi. unfold kbz_xor; cbn [fst snd].
  bits. unfold kb_val in *. rewrite <- H1, <- H2. bits.
  destruct (Z.testbit u1 i), (Z.testbit u2 i), (Z.testbit m1 i), (Z.testbit m2 i); reflexivity.
Qed.

(* [comment removed for export] *)
Definition kbz_srl (m v k : Z) : Z * Z :=
  (Z.lor (Z.shiftr m k) (Z.ldiff (Z.ones 64) (Z.ones (64 - k))), Z.shiftr v k).

Lemma kbz_srl_sound (m v u k : Z) : 0 <= k < 64 -> 0 <= u < 2 ^ 64 ->
  kb_val m v u -> kb_val (fst (kbz_srl m v k)) (snd (kbz_srl m v k)) (Z.shiftr u k).
Proof.
  intros Hk Hu H. apply kb_intro. intros i Hi. unfold kbz_srl; cbn [fst snd].
  unfold kb_val in H. rewrite <- H.
  rewrite Z.land_spec, Z.lor_spec, Z.ldiff_spec.
  rewrite !Z.shiftr_spec by lia. rewrite Z.land_spec.
  rewrite (Z.testbit_ones_nonneg 64 i) by lia. rewrite (Z.testbit_ones_nonneg (64 - k) i) by lia.
  destruct (Z_lt_le_dec i (64 - k)) as [Hlt|Hge].
  - rewrite (proj2 (Z.ltb_lt i 64)) by lia. rewrite (proj2 (Z.ltb_lt i (64 - k))) by lia. cbn [negb andb].
    rewrite orb_false_r. reflexivity.
  - assert (Hb : Z.testbit u (i + k) = false).
    { apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec u 0) as [->|Hn]; [cbn; lia|].
      apply Z.log2_lt_pow2; [lia|]. pose proof (Z.pow_le_mono_r 2 64 (i + k) ltac:(lia) ltac:(lia)). lia. }
    rewrite Hb. cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition kbz_sll (m v k : Z) : Z * Z :=
  (Z.lor (Z.land (Z.shiftl m k) (Z.ones 64)) (Z.ones k), Z.land (Z.shiftl v k) (Z.ones 64)).

Lemma kbz_sll_sound (m v u k : Z) : 0 <= k < 64 ->
  kb_val m v u -> kb_val (fst (kbz_sll m v k)) (snd (kbz_sll m v k)) (Z.land (Z.shiftl u k) (Z.ones 64)).
Proof.
  intros Hk H. apply kb_intro. intros i Hi. unfold kbz_sll; cbn [fst snd].
  unfold kb_val in H.
  rewrite !Z.land_spec, Z.lor_spec, !Z.land_spec.
  rewrite !Z.shiftl_spec by lia.
  rewrite (Z.testbit_ones_nonneg k i) by lia.
  destruct (Z_lt_le_dec i k) as [Hlt|Hge].
  - rewrite (Z.testbit_neg_r u (i - k)) by lia. rewrite (Z.testbit_neg_r v (i - k)) by lia. cbn. reflexivity.
  - rewrite <- H. rewrite Z.land_spec. rewrite (proj2 (Z.ltb_ge i k)) by lia. rewrite orb_false_r.
    destruct (Z.testbit u (i - k)), (Z.testbit m (i - k)), (Z.testbit (Z.ones 64) i); reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint lowrun_aux (n : nat) (m : Z) (k : Z) : Z :=
  match n with
  | O => k
  | S n' => if Z.testbit m k then lowrun_aux n' m (k + 1) else k
  end.
Definition lowrun (m : Z) : Z := lowrun_aux 64 m 0.

Lemma lowrun_aux_spec (n : nat) (m k : Z) : 0 <= k ->
  k <= lowrun_aux n m k <= k + Z.of_nat n /\ forall i, k <= i < lowrun_aux n m k -> Z.testbit m i = true.
Proof.
  revert k. induction n as [|n IH]; intros k Hk; cbn [lowrun_aux].
  - split; [lia|]. intros i Hi. lia.
  - destruct (Z.testbit m k) eqn:E.
    + destruct (IH (k + 1) ltac:(lia)) as [H1 H2]. split; [lia|].
      intros i Hi. destruct (Z.eq_dec i k) as [->|Hne]; [exact E|]. apply H2. lia.
    + split; [lia|]. intros i Hi. lia.
Qed.

Lemma lowrun_spec (m : Z) : 0 <= lowrun m <= 64 /\ forall i, 0 <= i < lowrun m -> Z.testbit m i = true.
Proof. unfold lowrun. destruct (lowrun_aux_spec 64 m 0 ltac:(lia)) as [H1 H2]. split; [lia | exact H2]. Qed.

Lemma kb_mod (m v u k : Z) : 0 <= k -> (forall i, 0 <= i < k -> Z.testbit m i = true) ->
  kb_val m v u -> u mod 2 ^ k = v mod 2 ^ k.
Proof.
  intros Hk Hm H. rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec. rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z_lt_le_dec i k) as [Hlt|Hge].
  - rewrite (proj2 (Z.ltb_lt i k)) by lia. rewrite !andb_true_r. apply (kb_bit m v u i H Hi). apply Hm. lia.
  - rewrite (proj2 (Z.ltb_ge i k)) by lia. rewrite !andb_false_r. reflexivity.
Qed.

Definition kbz_add (m1 v1 m2 v2 : Z) (sub : bool) : Z * Z :=
  let k := Z.min (lowrun m1) (lowrun m2) in
  (Z.ones k, Z.land (if sub then v1 - v2 else v1 + v2) (Z.ones k)).

Lemma kbz_add_sound (m1 v1 m2 v2 u1 u2 : Z) (sub : bool) :
  kb_val m1 v1 u1 -> kb_val m2 v2 u2 ->
  kb_val (fst (kbz_add m1 v1 m2 v2 sub)) (snd (kbz_add m1 v1 m2 v2 sub)) ((if sub then u1 - u2 else u1 + u2) mod 2 ^ 64).
Proof.
  intros H1 H2. unfold kbz_add; cbn [fst snd].
  destruct (lowrun_spec m1) as [Hr1 Hb1]. destruct (lowrun_spec m2) as [Hr2 Hb2].
  set (k := Z.min (lowrun m1) (lowrun m2)).
  assert (Hk : 0 <= k <= 64) by (unfold k; lia).
  unfold kb_val. rewrite !Z.land_ones by lia.
  assert (Hdiv : (2 ^ k | 2 ^ 64)).
  { exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite Z.mod_mod_divide by exact Hdiv.
  assert (E1 : u1 mod 2 ^ k = v1 mod 2 ^ k) by (apply (kb_mod m1 v1 u1 k); [lia | intros i Hi; apply Hb1; lia | exact H1]).
  assert (E2 : u2 mod 2 ^ k = v2 mod 2 ^ k) by (apply (kb_mod m2 v2 u2 k); [lia | intros i Hi; apply Hb2; lia | exact H2]).
  destruct sub.
  - rewrite Zminus_mod, E1, E2, <- Zminus_mod. reflexivity.
  - rewrite Zplus_mod, E1, E2, <- Zplus_mod. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_add_ldiff (u m : Z) : Z.land u m + Z.ldiff u m = u.
Proof.
  rewrite Z.add_nocarry_lxor.
  - rewrite <- (Z.lor_ldiff_and u m) at 3. apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.lor_spec, Z.land_spec, Z.ldiff_spec.
    destruct (Z.testbit u i), (Z.testbit m i); reflexivity.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit u i), (Z.testbit m i); reflexivity.
Qed.

Lemma ldiff_nonneg (u m : Z) : 0 <= u -> 0 <= Z.ldiff u m.
Proof. intros Hu. apply Z.ldiff_nonneg. left. exact Hu. Qed.

Lemma land_nonneg_l (u m : Z) : 0 <= u -> 0 <= Z.land u m.
Proof. intros Hu. apply Z.land_nonneg. left. exact Hu. Qed.

Lemma kb_lower (m v u : Z) : 0 <= u -> kb_val m v u -> v <= u.
Proof. intros Hu H. unfold kb_val in H. pose proof (land_add_ldiff u m). pose proof (ldiff_nonneg u m Hu). lia. Qed.

Lemma ldiff_ones_le (u m : Z) : 0 <= u < 2 ^ 64 -> 0 <= m < 2 ^ 64 -> Z.ldiff u m <= 2 ^ 64 - 1 - m.
Proof.
  intros Hu Hm.
  assert (Hsub : Z.ldiff u m = Z.land (Z.ldiff u m) (Z.ldiff (Z.ones 64) m)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec, Z.testbit_ones_nonneg by lia.
    destruct (Z_lt_le_dec i 64) as [Hl|Hg].
    - rewrite (proj2 (Z.ltb_lt i 64)) by lia. destruct (Z.testbit u i), (Z.testbit m i); reflexivity.
    - rewrite (proj2 (Z.ltb_ge i 64)) by lia.
      assert (Z.testbit u i = false) as ->.
      { apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec u 0) as [->|Hn]; [cbn; lia|].
        apply Z.log2_lt_pow2; [lia|]. pose proof (Z.pow_le_mono_r 2 64 i ltac:(lia) ltac:(lia)). lia. }
      reflexivity. }
  pose proof (land_add_ldiff (Z.ones 64) m) as E0.
  rewrite (Z.land_comm (Z.ones 64) m), Z.land_ones in E0 by lia. rewrite Z.mod_small in E0 by lia.
  rewrite Hsub. pose proof (land_add_ldiff (Z.ldiff (Z.ones 64) m) (Z.ldiff u m)) as E2.
  rewrite Z.land_comm in E2. pose proof (ldiff_nonneg (Z.ldiff (Z.ones 64) m) (Z.ldiff u m)).
  assert (HO : Z.ones 64 = 2 ^ 64 - 1) by (rewrite Z.ones_equiv, <- Z.sub_1_r; reflexivity).
  assert (Hp : 0 <= Z.ones 64) by (rewrite HO; lia).
  pose proof (ldiff_nonneg (Z.ones 64) m Hp).
  set (X := Z.ldiff (Z.ones 64) m) in *. rewrite HO in E0. lia.
Qed.

Lemma kb_upper (m v u : Z) : 0 <= u < 2 ^ 64 -> 0 <= m < 2 ^ 64 -> kb_val m v u -> u <= v + (2 ^ 64 - 1 - m).
Proof.
  intros Hu Hm H. unfold kb_val in H. pose proof (land_add_ldiff u m). pose proof (ldiff_ones_le u m Hu Hm). lia.
Qed.
