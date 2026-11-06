(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia FinFun.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma first_free : forall (P : Z -> Prop), (forall i, {P i} + {~ P i}) -> forall n, 0 <= n ->
  (exists j, 0 <= j < n /\ P j /\ forall k, 0 <= k < j -> ~ P k) \/ (forall k, 0 <= k < n -> ~ P k).
Proof.
  intros P dec n Hn. pattern n. apply natlike_ind; [| | exact Hn].
  - right. intros k Hk. lia.
  - intros x Hx [(j & Hj & Pj & Lj)|NO].
    + left. exists j. split; [lia|]. split; assumption.
    + destruct (dec x) as [Px|NPx].
      * left. exists x. split; [lia|]. split; [exact Px|]. intros k Hk. apply NO. lia.
      * right. intros k Hk. destruct (Z.eq_dec k x) as [->|NE]; [exact NPx| apply NO; lia].
Qed.

Lemma probe_pos_inj : forall N h k1 k2, 0 < N -> 0 <= k1 < N -> 0 <= k2 < N ->
  (h + k1) mod N = (h + k2) mod N -> k1 = k2.
Proof.
  intros N h k1 k2 HN H1 H2 E.
  assert (D : (k1 - k2) mod N = 0).
  { replace (k1 - k2) with ((h + k1) - (h + k2)) by lia. rewrite Zminus_mod, E, Z.sub_diag. apply Z.mod_0_l. lia. }
  apply Z.mod_divide in D; [|lia]. destruct D as [q Hq].
  assert (q = 0) by nia. lia.
Qed.

Lemma land_ones_mod : forall x k, 0 <= k -> Z.land x (2^k - 1) = x mod 2^k.
Proof. intros x k Hk. replace (2^k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. exact Hk. Qed.

Lemma pigeon_nat : forall (A : Type) (f : nat -> A) (n : nat) (l : list A),
  (forall k, (k < n)%nat -> In (f k) l) -> (forall k1 k2, (k1 < n)%nat -> (k2 < n)%nat -> f k1 = f k2 -> k1 = k2) ->
  (n <= length l)%nat.
Proof.
  intros A f n l HIN INJ.
  assert (ND : List.NoDup (map f (seq 0 n))).
  { apply Injective_map_NoDup_in; [| apply seq_NoDup].
    intros x y Hx Hy E. apply in_seq in Hx, Hy. apply INJ; [lia| lia| exact E]. }
  assert (INC : incl (map f (seq 0 n)) l).
  { intros a Ha. apply in_map_iff in Ha as (k & <- & Hk). apply in_seq in Hk. apply HIN. lia. }
  pose proof (NoDup_incl_length ND INC) as LE. rewrite length_map, length_seq in LE. exact LE.
Qed.

Lemma pigeon_Z : forall (A : Type) (f : Z -> A) (n : Z) (l : list A), 0 <= n ->
  (forall k, 0 <= k < n -> In (f k) l) -> (forall k1 k2, 0 <= k1 < n -> 0 <= k2 < n -> f k1 = f k2 -> k1 = k2) ->
  n <= Z.of_nat (length l).
Proof.
  intros A f n l Hn HIN INJ.
  pose proof (pigeon_nat A (fun k => f (Z.of_nat k)) (Z.to_nat n) l) as P.
  assert (LE : (Z.to_nat n <= length l)%nat).
  { apply P.
    - intros k Hk. apply HIN. lia.
    - intros k1 k2 H1 H2 E. apply INJ in E; lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma land_mod64 : forall x msk, 0 <= msk < 2^64 -> Z.land (x mod 18446744073709551616) msk = Z.land x msk.
Proof.
  intros x msk Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.ltb_spec i 64) as [L|L].
  - change 18446744073709551616 with (2^64). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - assert (E : Z.testbit msk i = false).
    { destruct (Z.eq_dec msk 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia. }
    rewrite E, !andb_false_r. reflexivity.
Qed.

Lemma swrap32_smallF : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 `div` 2) with (2^31).
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Vectors.FinFun.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma first_free : forall (P : Z -> Prop), (forall i, {P i} + {~ P i}) -> forall n, 0 <= n ->
  (exists j, 0 <= j < n /\ P j /\ forall k, 0 <= k < j -> ~ P k) \/ (forall k, 0 <= k < n -> ~ P k).
Proof.
  intros P dec n Hn. pattern n. apply natlike_ind; [| | exact Hn].
  - right. intros k Hk. lia.
  - intros x Hx [(j & Hj & Pj & Lj)|NO].
    + left. exists j. split; [lia|]. split; assumption.
    + destruct (dec x) as [Px|NPx].
      * left. exists x. split; [lia|]. split; [exact Px|]. intros k Hk. apply NO. lia.
      * right. intros k Hk. destruct (Z.eq_dec k x) as [->|NE]; [exact NPx| apply NO; lia].
Qed.

Lemma probe_pos_inj : forall N h k1 k2, 0 < N -> 0 <= k1 < N -> 0 <= k2 < N ->
  (h + k1) mod N = (h + k2) mod N -> k1 = k2.
Proof.
  intros N h k1 k2 HN H1 H2 E.
  assert (D : (k1 - k2) mod N = 0).
  { replace (k1 - k2) with ((h + k1) - (h + k2)) by lia. rewrite Zminus_mod, E, Z.sub_diag. apply Z.mod_0_l. lia. }
  apply Z.mod_divide in D; [|lia]. destruct D as [q Hq].
  assert (q = 0) by nia. lia.
Qed.

Lemma land_ones_mod : forall x k, 0 <= k -> Z.land x (2^k - 1) = x mod 2^k.
Proof. intros x k Hk. replace (2^k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. exact Hk. Qed.

Lemma pigeon_nat : forall (A : Type) (f : nat -> A) (n : nat) (l : list A),
  (forall k, (k < n)%nat -> In (f k) l) -> (forall k1 k2, (k1 < n)%nat -> (k2 < n)%nat -> f k1 = f k2 -> k1 = k2) ->
  (n <= length l)%nat.
Proof.
  intros A f n l HIN INJ.
  assert (ND : List.NoDup (map f (seq 0 n))).
  { apply Injective_map_NoDup_in; [| apply seq_NoDup].
    intros x y Hx Hy E. apply in_seq in Hx, Hy. apply INJ; [lia| lia| exact E]. }
  assert (INC : incl (map f (seq 0 n)) l).
  { intros a Ha. apply in_map_iff in Ha as (k & <- & Hk). apply in_seq in Hk. apply HIN. lia. }
  pose proof (NoDup_incl_length ND INC) as LE. rewrite length_map, length_seq in LE. exact LE.
Qed.

Lemma pigeon_Z : forall (A : Type) (f : Z -> A) (n : Z) (l : list A), 0 <= n ->
  (forall k, 0 <= k < n -> In (f k) l) -> (forall k1 k2, 0 <= k1 < n -> 0 <= k2 < n -> f k1 = f k2 -> k1 = k2) ->
  n <= Z.of_nat (length l).
Proof.
  intros A f n l Hn HIN INJ.
  pose proof (pigeon_nat A (fun k => f (Z.of_nat k)) (Z.to_nat n) l) as P.
  assert (LE : (Z.to_nat n <= length l)%nat).
  { apply P.
    - intros k Hk. apply HIN. lia.
    - intros k1 k2 H1 H2 E. apply INJ in E; lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma land_mod64 : forall x msk, 0 <= msk < 2^64 -> Z.land (x mod 18446744073709551616) msk = Z.land x msk.
Proof.
  intros x msk Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.ltb_spec i 64) as [L|L].
  - change 18446744073709551616 with (2^64). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - assert (E : Z.testbit msk i = false).
    { destruct (Z.eq_dec msk 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia. }
    rewrite E, !andb_false_r. reflexivity.
Qed.

Lemma swrap32_smallF : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 `div` 2) with (2^31).
  rewrite Z.mod_small by lia. lia.
Qed.
End TwB.
