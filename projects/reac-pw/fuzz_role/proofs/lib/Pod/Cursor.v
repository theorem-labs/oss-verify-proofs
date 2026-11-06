(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v; 110 of its 150 lines of code are new or changed and 447 lines of the source are left out. *)
(** The input cursor of fuzz/fuzz.h (fuzz.h:26-66) and the byte-list words of the fuzz/pod.h model. fuzz.h and
    pod.h are the same file in the reac-pw harnesses fuzz_role, fuzz_rate and fuzz_headamp, so the Pod/ files are
    shared by the three. Statement text and computation only: no function of a binary is proved here.

    The cursor is total: past the end of the input, fuzz_u8 gives 0 and does not move, and fuzz_take gives the bytes
    that are left. A cursor result is the value and the input that remains. *)
From Stdlib Require Import String Ascii ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

(** ** Byte lists *)
Definition sbytes (s : string) : list byte :=
  map (fun a => Z_to_bv 8 (Z.of_N (N_of_ascii a))) (list_ascii_of_string s).
Definition NUL : byte := Z_to_bv 8 0.
Definition zeros (n : nat) : list byte := repeat NUL n.
(** The 4 (8) little-endian bytes of v mod 2^32 (2^64); a negative v gives its two's complement. *)
Definition le32 (v : Z) : list byte := Z_to_le_bytes 4 v.
Definition le64 (v : Z) : list byte := Z_to_le_bytes 8 v.
(** The little-endian value of the first 4 bytes of l. *)
Definition rd32 (l : list byte) : Z := bytes_le_to_Z (firstn 4 l).
(** The index of the first NUL of l, or its length. *)
Fixpoint nul_idx (l : list byte) : nat :=
  match l with
  | [] => O
  | x :: l' => if bv_unsigned x =? 0 then O else S (nul_idx l')
  end.
(** The C string at the head of l: its bytes up to the first NUL. *)
Definition cstr (l : list byte) : list byte := firstn (nul_idx l) l.
Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (bv_unsigned x =? bv_unsigned y) && bytes_eqb a' b'
  | _, _ => false
  end.

(** ** The cursor (fuzz.h:37-66) *)
(** fuzz_u8: the next byte, or 0 at the end. *)
Definition fuzz_u8 (inp : list byte) : Z * list byte :=
  match inp with [] => (0, []) | b :: r => (bv_unsigned b, r) end.
(** fuzz_u16 / fuzz_u32: little-endian, the low part read first. *)
Definition fuzz_u16 (inp : list byte) : Z * list byte :=
  let '(lo, r) := fuzz_u8 inp in let '(hi, r') := fuzz_u8 r in (lo + 256 * hi, r').
Definition fuzz_u32 (inp : list byte) : Z * list byte :=
  let '(lo, r) := fuzz_u16 inp in let '(hi, r') := fuzz_u16 r in (lo + 65536 * hi, r').
(** fuzz_take(in, n, &p): the next min(n, left) bytes. *)
Definition fuzz_take (n : nat) (inp : list byte) : list byte * list byte := (firstn n inp, skipn n inp).
(** n successive fuzz_u8 reads, each kept as a byte. *)
Fixpoint fuzz_u8s (n : nat) (inp : list byte) : list byte * list byte :=
  match n with
  | O => ([], inp)
  | S n' => let '(b, r) := fuzz_u8 inp in let '(bs, r') := fuzz_u8s n' r in (Z_to_bv 8 b :: bs, r')
  end.

(** ** Facts *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma length_le32 : forall v, length (le32 v) = 4%nat.
Proof. intros v. reflexivity. Qed.
Lemma length_le64 : forall v, length (le64 v) = 8%nat.
Proof. intros v. reflexivity. Qed.
Lemma length_zeros : forall n, length (zeros n) = n.
Proof. intros n. apply repeat_length. Qed.

Lemma bytes_le_to_Z_Z_to_le_bytes : forall n z,
  bytes_le_to_Z (Z_to_le_bytes n z) = z mod 2 ^ (8 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intros z.
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - cbn [Z_to_le_bytes bytes_le_to_Z]. rewrite IH.
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 2^8).
    set (w := 8 * Z.of_nat (S n)). set (w' := 8 * Z.of_nat n).
    assert (Hw : w = w' + 8) by lia. assert (Hw' : 0 <= w') by lia.
    apply Z.bits_inj'. intros k Hk.
    rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite <- !Z.land_ones by lia. rewrite !Z.land_spec.
    destruct (Z.ltb_spec0 k 8).
    + rewrite (Z.testbit_neg_r _ (k - 8)) by lia. rewrite (Z.ones_spec_low 8) by lia.
      rewrite (Z.ones_spec_low w) by lia. rewrite orb_false_r. reflexivity.
    + rewrite (Z.ones_spec_high 8) by lia. rewrite andb_false_r. rewrite orb_false_l.
      rewrite Z.shiftr_spec by lia. replace (k - 8 + 8) with k by lia.
      destruct (Z.ltb_spec0 k w).
      * rewrite !Z.ones_spec_low by lia. reflexivity.
      * rewrite !Z.ones_spec_high by lia. reflexivity.
Qed.

Lemma le_bytes_nonneg : forall l, 0 <= bytes_le_to_Z l.
Proof.
  induction l as [|b l IH]; cbn [bytes_le_to_Z]; [lia|]. apply Z.lor_nonneg.
  split; [apply (proj1 (byte_range b)) | apply Z.shiftl_nonneg; exact IH].
Qed.
Lemma rd32_nonneg : forall l, 0 <= rd32 l.
Proof. intros l. apply le_bytes_nonneg. Qed.

Lemma lor_low_shiftl : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + y * 256.
Proof.
  intros x y Hx Hy. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 8) as [Hl|Hg].
  - rewrite (Z.testbit_neg_r y (i - 8)) by lia. rewrite orb_false_r.
    rewrite <- (Z.mod_pow2_bits_low (x + y * 256) 8 i) by lia. change (2^8) with 256.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
  - assert (Ex : Z.testbit x i = false).
    { destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; cbn; lia | lia]. }
    rewrite Ex, orb_false_l. replace i with ((i - 8) + 8) at 2 by lia. rewrite <- Z.div_pow2_bits by lia.
    change (2^8) with 256. rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma le_bytes_bound : forall l, bytes_le_to_Z l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction l as [|b l IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (byte_range b). pose proof (le_bytes_nonneg l).
  rewrite lor_low_shiftl by lia. rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat (length l)))
    with (8 * Z.of_nat (length l) + 8) by lia. rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.

Lemma rd32_range : forall l, 0 <= rd32 l < 2^32.
Proof.
  intros l. split; [apply rd32_nonneg|]. unfold rd32. pose proof (le_bytes_bound (firstn 4 l)) as H.
  rewrite length_firstn in H. eapply Z.lt_le_trans; [exact H|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma rd32_le32 : forall v l, rd32 (le32 v ++ l) = v mod 2^32.
Proof.
  intros v l. unfold rd32. rewrite firstn_app, length_le32. cbn [Nat.sub firstn]. rewrite app_nil_r.
  rewrite firstn_all2 by (rewrite length_le32; lia). unfold le32.
  rewrite bytes_le_to_Z_Z_to_le_bytes. reflexivity.
Qed.

Lemma rd32_le32_nil : forall v, rd32 (le32 v) = v mod 2^32.
Proof. intros v. rewrite <- (app_nil_r (le32 v)). apply rd32_le32. Qed.

Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; split; intros H; try discriminate; try reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst b. f_equal. apply bv_eq. exact H1.
  - injection H as -> ->. apply andb_true_intro. split; [apply Z.eqb_refl | apply IH; reflexivity].
Qed.

Lemma nul_idx_le : forall l, (nul_idx l <= length l)%nat.
Proof.
  induction l as [|x l IH]; cbn [nul_idx length]; [lia|]. destruct (bv_unsigned x =? 0); lia.
Qed.

Lemma fuzz_u8_spec : forall inp,
  fuzz_u8 inp = (match inp with [] => 0 | b :: _ => bv_unsigned b end, skipn 1 inp).
Proof. intros [|b r]; reflexivity. Qed.

Lemma fuzz_u8_range : forall inp, 0 <= fst (fuzz_u8 inp) < 256.
Proof. intros [|b r]; cbn; [lia | apply byte_range]. Qed.

Lemma fuzz_u16_rest : forall inp, snd (fuzz_u16 inp) = skipn 2 inp.
Proof. intros [|b [|c r]]; reflexivity. Qed.

Lemma fuzz_u16_range : forall inp, 0 <= fst (fuzz_u16 inp) < 65536.
Proof.
  intros inp. unfold fuzz_u16. destruct (fuzz_u8 inp) as [lo r] eqn:E1. destruct (fuzz_u8 r) as [hi r'] eqn:E2.
  cbn. pose proof (fuzz_u8_range inp) as H1. pose proof (fuzz_u8_range r) as H2. rewrite E1 in H1. rewrite E2 in H2.
  cbn in H1, H2. lia.
Qed.

Lemma fuzz_u32_rest : forall inp, snd (fuzz_u32 inp) = skipn 4 inp.
Proof. intros [|b [|c [|d [|e r]]]]; reflexivity. Qed.

Lemma fuzz_u32_range : forall inp, 0 <= fst (fuzz_u32 inp) < 2^32.
Proof.
  intros inp. unfold fuzz_u32. destruct (fuzz_u16 inp) as [lo r] eqn:E1. destruct (fuzz_u16 r) as [hi r'] eqn:E2.
  cbn. pose proof (fuzz_u16_range inp) as H1. pose proof (fuzz_u16_range r) as H2. rewrite E1 in H1. rewrite E2 in H2.
  cbn in H1, H2. lia.
Qed.

Lemma fuzz_u8s_rest : forall n inp, snd (fuzz_u8s n inp) = skipn n inp.
Proof.
  induction n as [|n IH]; intros inp; [reflexivity|]. cbn [fuzz_u8s].
  destruct inp as [|b r]; cbn [fuzz_u8].
  - specialize (IH []). destruct (fuzz_u8s n []) as [bs r'] eqn:E. cbn in IH |- *. rewrite IH. destruct n; reflexivity.
  - specialize (IH r). destruct (fuzz_u8s n r) as [bs r'] eqn:E. cbn in IH |- *. exact IH.
Qed.

Lemma fuzz_u8s_length : forall n inp, length (fst (fuzz_u8s n inp)) = n.
Proof.
  induction n as [|n IH]; intros inp; [reflexivity|]. cbn [fuzz_u8s].
  destruct (fuzz_u8 inp) as [b r]. specialize (IH r). destruct (fuzz_u8s n r) as [bs r']. cbn in *. lia.
Qed.
