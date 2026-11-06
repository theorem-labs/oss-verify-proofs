(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Exec Cells Step ZBridge Bytes Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).

(* [comment removed for export] *)
Lemma hk_mod_pow2_mod_pow2 : forall z a b, 0 <= a <= b -> (z mod 2^b) mod 2^a = z mod 2^a.
Proof.
  intros z a b H. replace (2^b) with (2^a * 2^(b-a)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; lia).
  rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. apply Z.pow_nonzero; lia.
Qed.

Lemma hk_b8_unsigned : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma hk_Z_to_le_bytes_eqm : forall n x y, x mod 2^(8 * Z.of_nat n) = y mod 2^(8 * Z.of_nat n) ->
  Z_to_le_bytes n x = Z_to_le_bytes n y.
Proof.
  intros n x y E. rewrite <- (Z_to_le_bytes_mod n x (8 * Z.of_nat n)), <- (Z_to_le_bytes_mod n y (8 * Z.of_nat n)) by lia.
  rewrite E. reflexivity.
Qed.

Lemma hk_le8_lit : forall z, le8 (Z_to_bv 64 z) = Z_to_le_bytes 8 z.
Proof.
  intros z. unfold le8, word_to_le_bytes. rewrite unsigned_lit_wrap. apply hk_Z_to_le_bytes_eqm.
  apply (hk_mod_pow2_mod_pow2 z (8 * Z.of_nat 8) 64). cbn; lia.
Qed.

Lemma hk_pair8_lo : forall a b, (a mod 256 + 256 * b) mod 256 = a mod 256.
Proof. intros. rewrite (Z.mul_comm 256 b), Z_mod_plus_full. apply Z.mod_mod. lia. Qed.
Lemma hk_pair8_hi : forall a b, (a mod 256 + 256 * b) / 256 = b.
Proof.
  intros. rewrite (Z.mul_comm 256 b), Z_div_plus_full by lia.
  rewrite Z.div_small; [lia|]. apply Z.mod_pos_bound. lia.
Qed.

Lemma hk_bytes_le_to_Z_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply (bv_unsigned_in_range 8 b)| apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma hk_Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  rewrite lor_shiftl8_add by (first [lia | apply hk_bytes_le_to_Z_nonneg]).
  rewrite <- (Z.mod_small (bv_unsigned b) 256) at 1 2 by lia.
  f_equal.
  - apply bv_eq. rewrite hk_b8_unsigned, hk_pair8_lo. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite hk_pair8_hi. exact IH.
Qed.

Lemma hk_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros bs H. rewrite hk_le8_lit, <- H. apply hk_Z_to_le_bytes_of_bytes. Qed.

(* [comment removed for export] *)
Fixpoint words8 (n : nat) (bs : list byte) : list word :=
  match n with
  | O => []
  | S n' => Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs)) :: words8 n' (skipn 8 bs)
  end.
Lemma words8_length n bs : length (words8 n bs) = n.
Proof. revert bs. induction n; intros; cbn; auto. Qed.
Lemma u64s_words8 n bs : length bs = (8 * n)%nat -> u64s (words8 n bs) = bs.
Proof.
  revert bs. induction n as [|n IH]; intros bs Hl.
  - destruct bs; [reflexivity| cbn in Hl; lia].
  - cbn [words8 u64s]. rewrite hk_le8_of_bytes by (rewrite length_firstn; lia).
    rewrite IH by (rewrite length_skipn; lia). apply firstn_skipn.
Qed.

Lemma u64arr_of_CB : forall segs (m : mem) A (k : nat) n bs, rw_cells segs m A [CB n bs] -> n = (8 * k)%nat ->
  exists ws, length ws = k /\ u64arr segs m A ws.
Proof.
  intros segs m A k n bs RC ->. pose proof RC as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
  pose proof (u8arr_of_rw_cells segs m A _ _ RC) as [HB HW].
  exists (words8 k bs). split; [apply words8_length|]. split.
  - rewrite u64s_words8 by exact LEN. exact HB.
  - rewrite words8_length. rewrite LEN in HW. replace (8 * Z.of_nat k) with (Z.of_nat (8 * k)) by lia. exact HW.
Qed.

Lemma u64arr_as_CB : forall segs (m : mem) A ws, u64arr segs m A ws -> rw_cells segs m A [CB (length (u64s ws)) (u64s ws)].
Proof.
  intros segs m A ws [HB HW]. apply rw_cells_of_u8arr. split; [exact HB|].
  rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact HW.
Qed.

Lemma u64s_repeat : forall (v : word) k, u64s (repeat v k) = concat (repeat (le8 v) k).
Proof. induction k as [|k IH]; [reflexivity|]. cbn [repeat u64s concat]. rewrite IH. reflexivity. Qed.

Lemma u64s_repeat0 : forall k, u64s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof.
  induction k as [|k IH]; [reflexivity|]. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
  cbn [repeat u64s]. rewrite IH. rewrite repeat_app. f_equal.
Qed.

Lemma upd_app_len {X} : forall (l1 : list X) x y l2, upd (l1 ++ x :: l2) (length l1) y = l1 ++ y :: l2.
Proof. induction l1 as [|a l1 IH]; intros x y l2; cbn [app length upd]; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma repeat_snoc_app {X} : forall (v : X) k tl, repeat v k ++ v :: tl = repeat v (S k) ++ tl.
Proof. intros v k tl. change (v :: tl) with ([v] ++ tl). rewrite app_assoc, <- repeat_cons. reflexivity. Qed.
