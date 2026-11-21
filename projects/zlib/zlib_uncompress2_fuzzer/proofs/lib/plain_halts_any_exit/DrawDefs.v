(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec StepTac MemSplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition rndb (d : EntryDraw) (k : nat) : byte :=
  nth k (at_random_bytes (ed_random d)) (Z_to_bv 8 0).

Lemma at_random_bytes_rndb : forall d,
  at_random_bytes (ed_random d)
  = [rndb d 0; rndb d 1; rndb d 2; rndb d 3; rndb d 4; rndb d 5; rndb d 6; rndb d 7;
     rndb d 8; rndb d 9; rndb d 10; rndb d 11; rndb d 12; rndb d 13; rndb d 14; rndb d 15].
Proof. intros d. reflexivity. Qed.

Lemma rnd_sub : forall d j n, (j + n <= 16)%nat ->
  firstn n (skipn j (at_random_bytes (ed_random d))) = map (rndb d) (seq j n).
Proof.
  intros d j n H. rewrite at_random_bytes_rndb.
  do 17 (destruct j as [|j]; [do 17 (destruct n as [|n]; [first [reflexivity | exfalso; lia]|]); exfalso; lia|]).
  exfalso; lia.
Qed.

Definition canary_bytes (d : EntryDraw) : list byte :=
  [rndb d 0; Z_to_bv 8 0; rndb d 2; rndb d 3; rndb d 4; rndb d 5; rndb d 6; rndb d 7].
Definition secret_bytes (d : EntryDraw) : list byte :=
  [rndb d 8; rndb d 9; rndb d 10; rndb d 11; rndb d 12; rndb d 13; rndb d 14; rndb d 15].

Definition canary_w (d : EntryDraw) : word := le_bytes_to_word (canary_bytes d).
Definition secret_w (d : EntryDraw) : word := le_bytes_to_word (secret_bytes d).

Lemma length_canary_bytes : forall d, length (canary_bytes d) = 8%nat.
Proof. reflexivity. Qed.


Lemma lez_word_range : forall bs, (length bs <= 8)%nat ->
  (0 <= bytes_le_to_Z bs < 2 ^ 64)%Z.
Proof.
  intros bs Hl. pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs).
  assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma u_le_bytes_to_word : forall bs, (length bs <= 8)%nat ->
  bv_unsigned (le_bytes_to_word bs) = bytes_le_to_Z bs.
Proof.
  intros bs Hl. pose proof (lez_word_range bs Hl). unfold le_bytes_to_word.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hn.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8)%Z.
    rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.lor_spec.
    destruct (Z.lt_ge_cases i 8).
    + rewrite Z.ones_spec_low, Z.shiftl_spec_low by lia. now rewrite Bool.orb_false_r, Bool.andb_true_r.
    + rewrite Z.ones_spec_high, Bool.andb_false_r by lia. symmetry. apply (Z_testbit_high 8); lia.
  - transitivity (Z_to_le_bytes (length bs) (bytes_le_to_Z bs)); [|exact IH]. f_equal.
    apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
    replace (i + 8 - 8)%Z with i by lia.
    rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.

Lemma le8_roundtrip : forall bs, length bs = 8%nat ->
  word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold word_to_le_bytes. rewrite u_le_bytes_to_word by lia.
  rewrite <- Hl. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma w8_canary : forall d, word_to_le_bytes 8 (canary_w d) = canary_bytes d.
Proof. intros d. apply le8_roundtrip. reflexivity. Qed.
Lemma w8_secret : forall d, word_to_le_bytes 8 (secret_w d) = secret_bytes d.
Proof. intros d. apply le8_roundtrip. reflexivity. Qed.

Lemma u_canary_w : forall d, bv_unsigned (canary_w d) = bytes_le_to_Z (canary_bytes d).
Proof. intros d. apply u_le_bytes_to_word. rewrite length_canary_bytes. lia. Qed.

Lemma ld_canary : forall d, bytes_le_to_Z (canary_bytes d) = bv_unsigned (canary_w d).
Proof. intros d. symmetry. apply u_canary_w. Qed.


Definition lw_val (l : list byte) : word := v_lw (le_bytes_to_word l).

Lemma lw_bridge : forall l, (length l <= 8)%nat ->
  bytes_le_to_Z l = bv_unsigned (le_bytes_to_word l).
Proof. intros l Hl. symmetry. apply u_le_bytes_to_word. exact Hl. Qed.

Lemma sw_lw_val : forall l, length l = 4%nat -> word_to_le_bytes 4 (lw_val l) = l.
Proof.
  intros l Hl. unfold lw_val, v_lw, word_to_le_bytes.
  pose proof (lez_word_range l ltac:(lia)) as Hr.
  pose proof (bytes_le_to_Z_bound l) as Hb. rewrite Hl in Hb. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in Hb.
  rewrite u_le_bytes_to_word by lia.
  rewrite Z_to_bv_unsigned.
  transitivity (Z_to_le_bytes 4 (bytes_le_to_Z l)); [|rewrite <- Hl; apply Z_to_le_bytes_of_bytes].
  assert (E : forall n (x y : Z), (forall i, (0 <= i < 8 * Z.of_nat n)%Z -> Z.testbit x i = Z.testbit y i) ->
                               Z_to_le_bytes n x = Z_to_le_bytes n y).
  { induction n as [|n IH]; intros x y Hxy; [reflexivity|]. cbn [Z_to_le_bytes]. f_equal.
    - apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
      rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
      destruct (Z.lt_ge_cases i 8); [rewrite Hxy by lia; reflexivity | rewrite Z.ones_spec_high, !Bool.andb_false_r by lia; reflexivity].
    - apply IH. intros i Hi. rewrite !Z.shiftr_spec by lia. apply Hxy. lia. }
  apply E. intros i Hi. change (8 * Z.of_nat 4)%Z with 32%Z in Hi.
  rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
  case_bool_decide; [reflexivity|]. replace i with 31%Z by lia. reflexivity.
Qed.


Definition rnd4 (d : EntryDraw) (j : nat) : list byte :=
  [rndb d j; rndb d (S j); rndb d (S (S j)); rndb d (S (S (S j)))].

Lemma length_rnd4 : forall d j, length (rnd4 d j) = 4%nat.
Proof. reflexivity. Qed.

Lemma rnd_sub4 : forall d j, (j + 4 <= 16)%nat ->
  firstn 4 (skipn j (at_random_bytes (ed_random d))) = rnd4 d j.
Proof. intros d j H. rewrite rnd_sub by lia. reflexivity. Qed.


Lemma rdn_pointwise : forall segs bs m (a : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (forall i, (i < length bs)%nat ->
     m (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0))) ->
  rdn segs m a (length bs) = Some bs.
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros m a Hnw Hpt; [reflexivity|].
  cbn [length] in Hnw. cbn [rdn length].
  pose proof (Hpt 0%nat ltac:(cbn; lia)) as H0. cbn [nth Z.of_nat] in H0.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  destruct bs as [|b' bs']; [reflexivity|]. cbn [length] in Hnw.
  rewrite (IH _ (a + 1)%bv); [reflexivity| cbn [length]; rewrite u_add1 by lia; lia |].
  intros i Hi. rewrite u_add1 by lia.
  replace (bv_unsigned a + 1 + Z.of_nat i)%Z with (bv_unsigned a + Z.of_nat (S i))%Z by lia.
  exact (Hpt (S i) ltac:(cbn [length] in *; lia)).
Qed.

Local Ltac wb1 :=
  first [ rewrite wbytes_inside by (rewrite ?length_rnd4; cbn [length]; rewrite !u_Z2bv by lia; lia)
        | rewrite wbytes_outside by (rewrite ?length_rnd4; cbn [length]; rewrite !u_Z2bv by lia; lia) ].

Lemma rdn_guard : forall segs m (g g4 g1 : Z) d,
  g4 = (g + 4)%Z -> g1 = (g + 1)%Z ->
  (0 <= g)%Z -> (g + 8 <= 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes m (Z_to_bv 64 g) (word_to_le_bytes 4 (lw_val (rnd4 d 0))))
                          (Z_to_bv 64 g4) (word_to_le_bytes 4 (lw_val (rnd4 d 4))))
                  (Z_to_bv 64 g1) [Z_to_bv 8 0])
      (Z_to_bv 64 g) 8 = Some (canary_bytes d).
Proof.
  intros segs m g g4 g1 d -> -> Hg0 Hg8.
  rewrite !sw_lw_val by reflexivity.
  change 8%nat with (length (canary_bytes d)).
  apply rdn_pointwise; [rewrite length_canary_bytes, u_Z2bv by lia; lia|].
  intros i Hi. rewrite length_canary_bytes in Hi. rewrite u_Z2bv by lia.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [ .. | exfalso; lia];
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ nth canary_bytes];
    repeat wb1; rewrite ?u_Z2bv by lia;
    match goal with |- Some (nth (Z.to_nat ?k) _ _) = _ => ring_simplify k; reflexivity end.
Qed.
