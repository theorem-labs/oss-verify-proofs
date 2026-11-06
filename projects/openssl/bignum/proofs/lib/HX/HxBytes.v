(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import AxFetchFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition byteZ (z j : Z) : Z := (z / 2 ^ (8 * j)) mod 256.

Definition fieldZ (z j n : Z) : Z := (z / 2 ^ (8 * j)) mod 2 ^ (8 * n).

Definition insZ (z j n x : Z) : Z := z - fieldZ z j n * 2 ^ (8 * j) + (x mod 2 ^ (8 * n)) * 2 ^ (8 * j).

Lemma pow8_pos (k : Z) : 0 <= k -> 0 < 2 ^ (8 * k).
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Ltac pw := first [ apply pow8_pos; lia | apply Z.neq_sym, Z.lt_neq, pow8_pos; lia | apply Z.lt_neq, pow8_pos; lia | lia ].

Lemma byteZ_range (z j : Z) : 0 <= byteZ z j < 256.
Proof. unfold byteZ. apply Z.mod_pos_bound. lia. Qed.

Lemma fieldZ_range (z j n : Z) : 0 <= n -> 0 <= fieldZ z j n < 2 ^ (8 * n).
Proof. intros. unfold fieldZ. apply Z.mod_pos_bound. apply pow8_pos. lia. Qed.

Lemma byteZ_low (a b k i : Z) : 0 <= k -> 0 <= a < 2 ^ (8 * k) -> 0 <= i < k -> byteZ (a + b * 2 ^ (8 * k)) i = byteZ a i.
Proof.
  intros Hk Ha Hi. unfold byteZ.
  replace (2 ^ (8 * k)) with (2 ^ (8 * i) * (256 * 2 ^ (8 * (k - i - 1))))
    by (change 256 with (2 ^ 8); rewrite <- !Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc, (Z.mul_comm b), <- Z.mul_assoc, (Z.mul_comm (2 ^ (8 * i))).
  rewrite Z.div_add by pw.
  rewrite (Z.mul_comm b), <- Z.mul_assoc, (Z.mul_comm 256), Z.mod_add by lia. reflexivity.
Qed.

Lemma byteZ_high (a b k i : Z) : 0 <= k -> 0 <= a < 2 ^ (8 * k) -> k <= i -> byteZ (a + b * 2 ^ (8 * k)) i = byteZ b (i - k).
Proof.
  intros Hk Ha Hi. unfold byteZ.
  replace (8 * i) with (8 * k + 8 * (i - k)) by ring. rewrite Z.pow_add_r by lia.
  rewrite <- Z.div_div by pw.
  rewrite Z.div_add by pw.
  rewrite (Z.div_small a) by lia. reflexivity.
Qed.

Lemma field_decomp (z j n : Z) : 0 <= z -> 0 <= j -> 0 <= n ->
  z = z mod 2 ^ (8 * j) + (fieldZ z j n + (z / 2 ^ (8 * (j + n))) * 2 ^ (8 * n)) * 2 ^ (8 * j).
Proof.
  intros Hz Hj Hn. unfold fieldZ. set (y := z / 2 ^ (8 * j)).
  assert (Ey : z / 2 ^ (8 * (j + n)) = y / 2 ^ (8 * n)).
  { unfold y. replace (8 * (j + n)) with (8 * j + 8 * n) by ring. rewrite Z.pow_add_r by lia.
    rewrite Z.div_div by pw. reflexivity. }
  rewrite Ey. pose proof (Z.div_mod y (2 ^ (8 * n)) ltac:(apply Z.neq_sym, Z.lt_neq, pow8_pos; lia)) as E1.
  pose proof (Z.div_mod z (2 ^ (8 * j)) ltac:(apply Z.neq_sym, Z.lt_neq, pow8_pos; lia)) as E2. fold y in E2.
  replace (y mod 2 ^ (8 * n) + y / 2 ^ (8 * n) * 2 ^ (8 * n)) with y by lia. lia.
Qed.

Lemma insZ_decomp (z j n x : Z) : 0 <= z -> 0 <= j -> 0 <= n ->
  insZ z j n x = z mod 2 ^ (8 * j) + (x mod 2 ^ (8 * n) + (z / 2 ^ (8 * (j + n))) * 2 ^ (8 * n)) * 2 ^ (8 * j).
Proof. intros Hz Hj Hn. unfold insZ. rewrite (field_decomp z j n Hz Hj Hn) at 1. ring. Qed.

Lemma insZ_range (z j n x : Z) : 0 <= z < 2 ^ 64 -> 0 <= j -> 0 <= n -> j + n <= 8 -> 0 <= insZ z j n x < 2 ^ 64.
Proof.
  intros Hz Hj Hn Hjn. rewrite insZ_decomp by lia.
  pose proof (Z.mod_pos_bound z (2 ^ (8 * j)) (pow8_pos j Hj)) as H1.
  pose proof (Z.mod_pos_bound x (2 ^ (8 * n)) (pow8_pos n Hn)) as H2.
  set (hi := z / 2 ^ (8 * (j + n))).
  assert (Hhi : 0 <= hi < 2 ^ (64 - 8 * (j + n))).
  { unfold hi. split; [apply Z.div_pos; [lia | apply pow8_pos; lia]|].
    apply Z.div_lt_upper_bound; [apply pow8_pos; lia|]. rewrite <- Z.pow_add_r by lia.
    replace (8 * (j + n) + (64 - 8 * (j + n))) with 64 by ring. lia. }
  assert (P1 := pow8_pos j Hj). assert (P2 := pow8_pos n Hn).
  assert (E64 : 2 ^ 64 = 2 ^ (64 - 8 * (j + n)) * 2 ^ (8 * n) * 2 ^ (8 * j)).
  { rewrite <- !Z.pow_add_r by lia. f_equal. lia. }
  split; [nia|]. rewrite E64.
  assert (x mod 2 ^ (8 * n) + hi * 2 ^ (8 * n) <= 2 ^ (64 - 8 * (j + n)) * 2 ^ (8 * n) - 1) by nia. nia.
Qed.

Lemma byteZ_insZ (z j n x i : Z) : 0 <= z -> 0 <= j -> 0 <= n -> 0 <= i ->
  byteZ (insZ z j n x) i = if (j <=? i) && (i <? j + n) then byteZ x (i - j) else byteZ z i.
Proof.
  intros Hz Hj Hn Hi. rewrite insZ_decomp by lia.
  pose proof (Z.mod_pos_bound z (2 ^ (8 * j)) (pow8_pos j Hj)) as H1.
  pose proof (Z.mod_pos_bound x (2 ^ (8 * n)) (pow8_pos n Hn)) as H2.
  destruct (Z.leb_spec j i) as [Hji|Hji]; cbn [andb].
  - rewrite byteZ_high by lia. destruct (Z.ltb_spec i (j + n)) as [Hin|Hin].
    + rewrite byteZ_low by lia. unfold byteZ.
      replace (2 ^ (8 * n)) with (2 ^ (8 * (i - j)) * (256 * 2 ^ (8 * (n - (i - j) - 1))))
        by (change 256 with (2 ^ 8); rewrite <- !Z.pow_add_r by lia; f_equal; lia).
      rewrite Z.rem_mul_r by (try (apply Z.neq_sym, Z.lt_neq, pow8_pos; lia); assert (0 < 2 ^ (8 * (n - (i - j) - 1))) by (apply pow8_pos; lia); lia).
      rewrite (Z.mul_comm (2 ^ (8 * (i - j)))), Z.div_add by pw.
      rewrite (Z.div_small (x mod 2 ^ (8 * (i - j)))) by (apply Z.mod_pos_bound, pow8_pos; lia). rewrite Z.add_0_l.
      rewrite Z.rem_mul_r by pw.
      rewrite (Z.mul_comm 256), Z.mod_add by lia. apply Z.mod_mod. lia.
    + rewrite byteZ_high by lia. rewrite (field_decomp z j n Hz Hj Hn) at 2.
      rewrite byteZ_high by lia. pose proof (fieldZ_range z j n Hn). rewrite byteZ_high by lia. reflexivity.
  - rewrite byteZ_low by lia. rewrite (field_decomp z j n Hz Hj Hn) at 2. rewrite byteZ_low by lia. reflexivity.
Qed.

Definition byte_of (z j : Z) : byte := Z_to_bv 8 (byteZ z j).

Lemma byte_of_unsigned (z j : Z) : bv_unsigned (byte_of z j) = byteZ z j.
Proof.
  unfold byte_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (byteZ_range z j). change (bv_modulus 8) with 256. lia.
Qed.

Lemma Z_to_bv8_byteZ (z : Z) : Z_to_bv 8 z = byte_of z 0.
Proof.
  unfold byte_of, byteZ. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. symmetry. apply Z.mod_mod. lia.
Qed.

Lemma nth_Z_to_le_bytes (n : nat) : forall (z : Z) (i : nat), 0 <= z -> (i < n)%nat ->
  nth_error (Z_to_le_bytes n z) i = Some (byte_of z (Z.of_nat i)).
Proof.
  induction n as [|n IH]; intros z i Hz Hi; [lia|]. cbn [Z_to_le_bytes]. destruct i as [|i].
  - cbn [nth_error]. rewrite Z_to_bv8_byteZ. reflexivity.
  - cbn [nth_error]. rewrite IH by (try apply Z.shiftr_nonneg; lia). f_equal. unfold byte_of, byteZ. f_equal.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by pw.
    f_equal. f_equal. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma bytes_le_to_Z_field (n : nat) : forall (bs : list byte) (z j : Z), 0 <= j -> length bs = n ->
  (forall i, (i < n)%nat -> nth_error bs i = Some (byte_of z (j + Z.of_nat i))) ->
  bytes_le_to_Z bs = fieldZ z j (Z.of_nat n).
Proof.
  induction n as [|n IH]; intros bs z j Hj Hl Hb.
  - destruct bs; [|discriminate]. cbn. unfold fieldZ. change (2 ^ (8 * 0)) with 1. rewrite Z.mod_1_r. reflexivity.
  - destruct bs as [|b bs]; [discriminate|]. cbn [bytes_le_to_Z].
    assert (Eb : b = byte_of z j).
    { specialize (Hb 0%nat ltac:(lia)). cbn [nth_error] in Hb. injection Hb as ->. f_equal. lia. }
    assert (Hl' : length bs = n) by (cbn in Hl; lia).
    assert (Hb' : forall i, (i < n)%nat -> nth_error bs i = Some (byte_of z (j + 1 + Z.of_nat i))).
    { intros i Hi. specialize (Hb (S i) ltac:(lia)). cbn [nth_error] in Hb. rewrite Hb. f_equal. f_equal. lia. }
    rewrite (IH bs z (j + 1) ltac:(lia) Hl' Hb').
    subst b. rewrite byte_of_unsigned. unfold byteZ, fieldZ.
    replace (8 * (j + 1)) with (8 * j + 8) by ring. rewrite Z.pow_add_r by lia.
    rewrite <- Z.div_div by pw. set (y := z / 2 ^ (8 * j)).
    change (2 ^ 8) with 256.
    replace (2 ^ (8 * Z.of_nat (S n))) with (256 * 2 ^ (8 * Z.of_nat n))
      by (change 256 with (2 ^ 8); rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Z.rem_mul_r by pw.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    assert (H0 : 0 <= y mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    assert (H1 : 0 <= (y / 256) mod 2 ^ (8 * Z.of_nat n)) by (apply Z.mod_pos_bound, pow8_pos; lia).
    pose proof (lor_shift_add (y mod 256) ((y / 256) mod 2 ^ (8 * Z.of_nat n)) 8 ltac:(change (2 ^ 8) with 256; lia) H1 ltac:(lia)) as E.
    change (2 ^ 8) with 256 in E. rewrite Z.lor_comm, E. ring.
Qed.

Definition w_mask (n : int) : w64 :=
  if (n =? 8)%uint63 then w_ones else W false ((1 << (8 * n)) - 1)%uint63.

Lemma wZ_mask (n : int) : 1 <= to_Z n <= 8 -> wZ (w_mask n) = 2 ^ (8 * to_Z n) - 1.
Proof.
  intros Hn. unfold w_mask. destruct (eqbP n 8) as [E|E]; change (to_Z 8%uint63) with 8 in E.
  - rewrite E. reflexivity.
  - unfold wZ; cbn [wh wl]. rewrite sub_spec, lsl_spec, mul_spec. change (to_Z 1%uint63) with 1. change (to_Z 8%uint63) with 8.
    change wB with (2 ^ 63). rewrite (Z.mod_small (8 * to_Z n)) by lia.
    assert (P : 0 < 2 ^ (8 * to_Z n) <= 2 ^ 56) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    rewrite Z.mul_1_l, (Z.mod_small (2 ^ (8 * to_Z n))) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition w_ext (w : w64) (j n : int) : w64 := w_and (w_srl w (8 * j)%uint63) (w_mask n).

Lemma wZ_ext (w : w64) (j n : int) : to_Z j < 8 -> 1 <= to_Z n <= 8 -> wZ (w_ext w j n) = fieldZ (wZ w) (to_Z j) (to_Z n).
Proof.
  intros Hj Hn. unfold w_ext. pose proof (to_Z_bounded j) as Bj.
  assert (E8 : to_Z (8 * j)%uint63 = 8 * to_Z j).
  { rewrite mul_spec. change (to_Z 8%uint63) with 8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  rewrite wZ_and, wZ_srl by lia. rewrite wZ_mask by lia. rewrite E8.
  change (2 ^ (8 * to_Z n) - 1) with (Z.pred (2 ^ (8 * to_Z n))). rewrite <- Z.ones_equiv. rewrite Z.land_ones by lia. reflexivity.
Qed.

Definition w_ins (w : w64) (j n : int) (x : w64) : w64 :=
  let s := (8 * j)%uint63 in
  w_add (w_sub w (w_sll (w_ext w j n) s)) (w_sll (w_and x (w_mask n)) s).

Lemma wZ_ins (w : w64) (j n : int) (x : w64) : to_Z j + to_Z n <= 8 -> 1 <= to_Z n ->
  wZ (w_ins w j n x) = insZ (wZ w) (to_Z j) (to_Z n) (wZ x).
Proof.
  intros Hjn Hn. pose proof (to_Z_bounded j) as Bj. pose proof (to_Z_bounded n) as Bn.
  assert (E8 : to_Z (8 * j)%uint63 = 8 * to_Z j).
  { rewrite mul_spec. change (to_Z 8%uint63) with 8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  pose proof (wZ_range w) as Hw. unfold two64 in Hw. change 18446744073709551616 with (2 ^ 64) in Hw.
  pose proof (insZ_range (wZ w) (to_Z j) (to_Z n) (wZ x) Hw ltac:(lia) ltac:(lia) Hjn) as Hr.
  unfold w_ins. rewrite wZ_add, wZ_sub, !wZ_sll by lia. rewrite wZ_ext by lia. rewrite wZ_and, wZ_mask by lia. rewrite E8.
  change (2 ^ (8 * to_Z n) - 1) with (Z.pred (2 ^ (8 * to_Z n))). rewrite <- Z.ones_equiv. rewrite Z.land_ones by lia.
  unfold two64. change 18446744073709551616 with (2 ^ 64).
  rewrite Zminus_mod_idemp_r. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  unfold insZ in *. apply Z.mod_small. exact Hr.
Qed.

Definition w_byte (w : w64) (j : int) : int := wl (w_ext w j 1).

Definition w_sextn (n : int) (x : w64) : w64 :=
  let sb := ((8 * n) - 1)%uint63 in
  if is_odd (wl x >> sb)%uint63 then w_sub x (w_sll w_one (8 * n)%uint63) else x.

Lemma wZ_sextn (n : int) (x : w64) : 1 <= to_Z n <= 4 -> 0 <= wZ x < 2 ^ (8 * to_Z n) ->
  wZ (w_sextn n x) = if wZ x <? 2 ^ (8 * to_Z n - 1) then wZ x else wZ x + two64 - 2 ^ (8 * to_Z n).
Proof.
  intros Hn Hx. unfold w_sextn.
  assert (E8 : to_Z (8 * n)%uint63 = 8 * to_Z n).
  { rewrite mul_spec. change (to_Z 8%uint63) with 8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  assert (Esb : to_Z (8 * n - 1)%uint63 = 8 * to_Z n - 1).
  { rewrite sub_spec, E8. change (to_Z 1%uint63) with 1. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  assert (P32 : 2 ^ (8 * to_Z n) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (Hh : wh x = false).
  { destruct (wh x) eqn:E; [|reflexivity]. exfalso. rewrite wZ_split, E in Hx. cbn [Z.b2z] in Hx.
    pose proof (phi_range (wl x)). unfold two63 in *. lia. }
  assert (El : to_Z (wl x) = wZ x) by (rewrite wZ_split, Hh; cbn [Z.b2z]; lia).
  assert (Hodd : Z.b2z (is_odd (wl x >> (8 * n - 1))%uint63) = if wZ x <? 2 ^ (8 * to_Z n - 1) then 0 else 1).
  { rewrite is_odd_spec, lsr_spec, Esb, El.
    assert (Ep : 2 ^ (8 * to_Z n) = 2 * 2 ^ (8 * to_Z n - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Pp : 0 < 2 ^ (8 * to_Z n - 1)) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.ltb_spec (wZ x) (2 ^ (8 * to_Z n - 1))).
    - rewrite Z.div_small by lia. reflexivity.
    - assert (wZ x / 2 ^ (8 * to_Z n - 1) = 1) as -> by (symmetry; apply Z.div_unique with (r := wZ x - 2 ^ (8 * to_Z n - 1)); lia).
      reflexivity. }
  destruct (is_odd (wl x >> (8 * n - 1))%uint63); cbn [Z.b2z] in Hodd;
    destruct (Z.ltb_spec (wZ x) (2 ^ (8 * to_Z n - 1))); try discriminate; [|reflexivity].
  rewrite wZ_sub, wZ_sll by lia. rewrite wZ_one, E8, Z.mul_1_l.
  assert (Pp : 0 < 2 ^ (8 * to_Z n - 1)) by (apply Z.pow_pos_nonneg; lia).
  rewrite (Z.mod_small (2 ^ (8 * to_Z n))) by (unfold two64; lia).
  replace (wZ x - 2 ^ (8 * to_Z n)) with ((wZ x + two64 - 2 ^ (8 * to_Z n)) + (-1) * two64) by ring.
  rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. unfold two64 in *. lia.
Qed.
