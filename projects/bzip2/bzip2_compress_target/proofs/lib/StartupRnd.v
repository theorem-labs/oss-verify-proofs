(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec StepTac CatExec SeqExec MemSplit.
Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = (bv_unsigned b + bytes_le_to_Z bs * 256)%Z.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256%Z with (2 ^ 8)%Z. rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256%Z with (2 ^ 8)%Z. rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256)%Z with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_congr : forall n z z', (0 <= z)%Z -> (0 <= z')%Z ->
  (z mod 2 ^ (8 * Z.of_nat n) = z' mod 2 ^ (8 * Z.of_nat n))%Z ->
  Z_to_le_bytes n z = Z_to_le_bytes n z'.
Proof.
  intros n z z' Hz Hz' Hm.
  transitivity (Z_to_le_bytes (length (Z_to_le_bytes n z)) (bytes_le_to_Z (Z_to_le_bytes n z)));
    [symmetry; apply Z_to_le_bytes_to_Z|].
  rewrite length_Z_to_le_bytes, bytes_le_to_Z_of_le_bytes, Hm, <- bytes_le_to_Z_of_le_bytes by assumption.
  rewrite <- (length_Z_to_le_bytes n z') at 1. apply Z_to_le_bytes_to_Z.
Qed.

Lemma bytes_le_to_Z_range : forall bs, (length bs <= 8)%nat ->
  (0 <= bytes_le_to_Z bs < 2 ^ 64)%Z.
Proof.
  intros bs Hn. pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs).
  assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rnd_bytes (rnd : EntryDraw) (j n : nat) : list byte :=
  firstn n (skipn j (at_random_bytes (ed_random rnd))).

Lemma length_rnd_bytes : forall rnd j n, (j + n <= 16)%nat -> length (rnd_bytes rnd j n) = n.
Proof.
  intros rnd j n H. unfold rnd_bytes. rewrite firstn_length_le; [reflexivity|].
  rewrite length_skipn, length_at_random_bytes. lia.
Qed.

(* [comment removed for export] *)
Definition lew (bs : list byte) : word := Z_to_bv 64 (bytes_le_to_Z bs).

Lemma lew_ok : forall bs, (length bs <= 8)%nat -> bytes_le_to_Z bs = bv_unsigned (lew bs).
Proof.
  intros bs Hn. unfold lew. pose proof (bytes_le_to_Z_range bs Hn). rewrite u_Z2bv by lia. reflexivity.
Qed.

Lemma word_to_le_bytes_lew : forall bs, (length bs <= 8)%nat ->
  word_to_le_bytes (length bs) (lew bs) = bs.
Proof.
  intros bs Hn. unfold word_to_le_bytes. rewrite <- lew_ok by exact Hn. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma word_to_le_bytes_4_vlw : forall bs, length bs = 4%nat ->
  word_to_le_bytes 4 (v_lw (lew bs)) = bs.
Proof.
  intros bs Hn.
  rewrite <- (word_to_le_bytes_lew bs) at 2 by lia. rewrite Hn.
  unfold word_to_le_bytes, v_lw. apply Z_to_le_bytes_congr.
  - apply (u64_range (Z_to_bv 64 _)).
  - apply u64_range.
  - rewrite Z_to_bv_unsigned. change (8 * Z.of_nat 4)%Z with 32%Z.
    change (bv_wrap 64 (bv_swrap 32 (bv_unsigned (lew bs))) mod 2 ^ 32)%Z
      with (bv_wrap 32 (bv_wrap 64 (bv_swrap 32 (bv_unsigned (lew bs))))).
    rewrite bv_wrap_bv_wrap by (cbv; discriminate).
    unfold bv_swrap. rewrite bv_wrap_sub_idemp_l.
    replace (bv_unsigned (lew bs) + bv_half_modulus 32 - bv_half_modulus 32)%Z with (bv_unsigned (lew bs)) by lia.
    reflexivity.
Qed.

(* [comment removed for export] *)
Definition canary_bytes (rnd : EntryDraw) : list byte :=
  rnd_bytes rnd 0 1 ++ [Z_to_bv 8 0] ++ rnd_bytes rnd 2 6.

Lemma length_canary_bytes : forall rnd, length (canary_bytes rnd) = 8%nat.
Proof. intros rnd. reflexivity. Qed.

Definition canary_w (rnd : EntryDraw) : word := lew (canary_bytes rnd).

Lemma canary_ok : forall rnd, bytes_le_to_Z (canary_bytes rnd) = bv_unsigned (canary_w rnd).
Proof. intros rnd. apply lew_ok. rewrite length_canary_bytes. lia. Qed.

Lemma word_to_le_bytes_canary : forall rnd, word_to_le_bytes 8 (canary_w rnd) = canary_bytes rnd.
Proof.
  intros rnd. rewrite <- (length_canary_bytes rnd) at 1. apply word_to_le_bytes_lew.
  rewrite length_canary_bytes. lia.
Qed.

(* [comment removed for export] *)
Definition secret_w (rnd : EntryDraw) : Z := bytes_le_to_Z (rnd_bytes rnd 8 8).

Lemma secret_w_range : forall rnd, (0 <= secret_w rnd < 2 ^ 64)%Z.
Proof. intros rnd. apply bytes_le_to_Z_range. rewrite length_rnd_bytes; lia. Qed.

(* [comment removed for export] *)
Definition secret_word (rnd : EntryDraw) : word := lew (rnd_bytes rnd 8 8).

Lemma secret_word_unsigned : forall rnd, bv_unsigned (secret_word rnd) = secret_w rnd.
Proof. intros rnd. unfold secret_word, secret_w. symmetry. apply lew_ok. rewrite length_rnd_bytes; lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma secret_word_of_Z : forall rnd, Z_to_bv 64 (secret_w rnd) = secret_word rnd.
Proof. intros rnd. apply bv_eq. rewrite u_Z2bv by (apply secret_w_range). symmetry. apply secret_word_unsigned. Qed.

(* [comment removed for export] *)
Lemma rnd_bytes_eq : forall rnd j n, rnd_bytes rnd j n = firstn n (skipn j (at_random_bytes (ed_random rnd))).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rnd_bytes_split : forall rnd j a b, (j + a + b <= 16)%nat ->
  rnd_bytes rnd j (a + b) = rnd_bytes rnd j a ++ rnd_bytes rnd (j + a) b.
Proof.
  intros rnd j a b H. unfold rnd_bytes.
  rewrite <- (firstn_skipn a (firstn (a + b) (skipn j (at_random_bytes (ed_random rnd))))) at 1.
  rewrite firstn_firstn, Nat.min_l by lia.
  rewrite skipn_firstn_comm. replace (a + b - a)%nat with b by lia.
  rewrite skipn_skipn, Nat.add_comm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_canary : forall segs D (g : Z) rnd, (0 <= g)%Z -> (g + 8 <= 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) (word_to_le_bytes 4 (v_lw (lew (rnd_bytes rnd 0 4)))))
                          (Z_to_bv 64 (g + 4)) (word_to_le_bytes 4 (v_lw (lew (rnd_bytes rnd 4 4)))))
                  (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0])
      (Z_to_bv 64 g) 8%nat = Some (canary_bytes rnd).
Proof.
  intros segs D g rnd Hg0 Hg8.
  rewrite !word_to_le_bytes_4_vlw by (apply length_rnd_bytes; lia).
  transitivity (rdn segs (wbytes D (Z_to_bv 64 g) (canary_bytes rnd)) (Z_to_bv 64 g) 8%nat).
  2:{ rewrite <- (length_canary_bytes rnd) at 1. apply rdn_wbytes_hit. rewrite length_canary_bytes, u_Z2bv by lia. lia. }
  apply rdn_ext; [rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  pose proof (length_rnd_bytes rnd 0 4 ltac:(lia)) as L0. pose proof (length_rnd_bytes rnd 4 4 ltac:(lia)) as L4.
  assert (E8 : rnd_bytes rnd 0 8 = rnd_bytes rnd 0 4 ++ rnd_bytes rnd 4 4) by (apply (rnd_bytes_split rnd 0 4 4); lia).
  assert (E26 : rnd_bytes rnd 0 8 = rnd_bytes rnd 0 2 ++ rnd_bytes rnd 2 6) by (apply (rnd_bytes_split rnd 0 2 6); lia).
  assert (E11 : rnd_bytes rnd 0 2 = rnd_bytes rnd 0 1 ++ rnd_bytes rnd 1 1) by (apply (rnd_bytes_split rnd 0 1 1); lia).
  pose proof (length_rnd_bytes rnd 0 1 ltac:(lia)) as L01. pose proof (length_rnd_bytes rnd 1 1 ltac:(lia)) as L11.
  pose proof (length_rnd_bytes rnd 2 6 ltac:(lia)) as L26.
  (* [comment removed for export] *)
  assert (NTH8 : forall k, (k < 8)%nat -> k <> 1%nat ->
            nth k (rnd_bytes rnd 0 8) (Z_to_bv 8 0) = nth k (canary_bytes rnd) (Z_to_bv 8 0)).
  { intros k Hk Hk1. unfold canary_bytes. rewrite E26, E11, <- app_assoc.
    destruct k as [|[|k]]; [| lia |].
    - rewrite !app_nth1 by (rewrite ?length_app; lia). reflexivity.
    - rewrite (app_nth2 (rnd_bytes rnd 0 1)) by lia. rewrite (app_nth2 (rnd_bytes rnd 0 1)) by lia. rewrite L01.
      rewrite (app_nth2 (rnd_bytes rnd 1 1)) by lia. rewrite L11.
      replace (S (S k) - 1 - 1)%nat with k by lia. replace (S (S k) - 1)%nat with (S k) by lia. reflexivity. }
  rewrite (wbytes_inside (canary_bytes rnd)) by (rewrite length_canary_bytes, u_Z2bv by lia; lia).
  rewrite u_Z2bv by lia.
  destruct (Z.eq_dec (bv_unsigned x) (g + 1)) as [E1|NE1].
  - rewrite wbytes_inside by (cbn [length]; rewrite u_Z2bv by lia; lia).
    rewrite u_Z2bv, E1 by lia. replace (g + 1 - (g + 1))%Z with 0%Z by lia. replace (g + 1 - g)%Z with 1%Z by lia. reflexivity.
  - rewrite (wbytes_outside [Z_to_bv 8 0]) by (cbn [length]; rewrite u_Z2bv by lia; lia).
    destruct (Z_lt_le_dec (bv_unsigned x) (g + 4)) as [LO|HI].
    + rewrite (wbytes_outside (rnd_bytes rnd 4 4)) by (rewrite L4, u_Z2bv by lia; lia).
      rewrite wbytes_inside by (rewrite L0, u_Z2bv by lia; lia). rewrite u_Z2bv by lia.
      f_equal. rewrite <- NTH8 by lia. rewrite E8, app_nth1 by lia. reflexivity.
    + rewrite wbytes_inside by (rewrite L4, u_Z2bv by lia; lia). rewrite u_Z2bv by lia.
      f_equal. rewrite <- NTH8 by lia. rewrite E8, app_nth2 by lia. rewrite L0. f_equal. lia.
Qed.
