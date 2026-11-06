(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma land_mulpow2_small : forall q b r, 0 <= r -> 0 <= b < 2 ^ r -> Z.land (q * 2 ^ r) b = 0.
Proof.
  intros q b r Hr Hb. destruct (Z.eq_dec b 0) as [->|Hb0]. { apply Z.land_0_r. }
  apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n r) as [Hn|Hn].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 b n); [apply Bool.andb_false_r| lia |].
    apply (Z.lt_le_trans _ r); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_mulpow2_small : forall q b r, 0 <= r -> 0 <= q -> 0 <= b < 2 ^ r -> Z.lor (q * 2 ^ r) b = q * 2 ^ r + b.
Proof.
  intros q b r Hr Hq Hb. rewrite <- Z.lxor_lor by (apply land_mulpow2_small; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_mulpow2_small; lia.
Qed.

(* [comment removed for export] *)
Definition shlb_limb (x p r : Z) : Z := (x * 2 ^ r) mod 2 ^ 64 + p / 2 ^ (64 - r).

Lemma shr_small : forall p r, 0 <= p < 2 ^ 64 -> 1 <= r <= 63 -> 0 <= p / 2 ^ (64 - r) < 2 ^ r.
Proof.
  intros p r Hp Hr. split. { apply Z.div_pos; [lia|]. apply Z.pow_pos_nonneg; lia. }
  apply Z.div_lt_upper_bound. { apply Z.pow_pos_nonneg; lia. }
  rewrite <- Z.pow_add_r by lia. replace (64 - r + r) with 64 by lia. lia.
Qed.

Lemma mod64_mulpow2 : forall x r, 0 <= x -> 0 <= r <= 64 -> (x * 2 ^ r) mod 2 ^ 64 = (x mod 2 ^ (64 - r)) * 2 ^ r.
Proof.
  intros x r Hx Hr.
  replace (2 ^ 64) with (2 ^ (64 - r) * 2 ^ r) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r. reflexivity. all: try (apply Z.pow_nonzero; lia).
Qed.

Lemma shlb_limb_range : forall x p r, 0 <= x < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 1 <= r <= 63 ->
  0 <= shlb_limb x p r < 2 ^ 64.
Proof.
  intros x p r Hx Hp Hr. unfold shlb_limb.
  pose proof (shr_small p r Hp Hr) as Hs.
  rewrite mod64_mulpow2 by lia.
  pose proof (Z.mod_pos_bound x (2 ^ (64 - r)) ltac:(apply Z.pow_pos_nonneg; lia)) as Hm.
  assert (2 ^ (64 - r) * 2 ^ r = 2 ^ 64) as E by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (0 < 2 ^ r) by (apply Z.pow_pos_nonneg; lia).
  split; [nia|].
  assert ((x mod 2 ^ (64 - r)) * 2 ^ r <= (2 ^ (64 - r) - 1) * 2 ^ r) by nia. nia.
Qed.

(* [comment removed for export] *)
Lemma shlb_limb_word : forall x p r, 0 <= x < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 1 <= r <= 63 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl x r))) (bv_unsigned (Z_to_bv 64 (Z.shiftr p (64 - r))))
  = shlb_limb x p r.
Proof.
  intros x p r Hx Hp Hr. unfold shlb_limb.
  pose proof (shr_small p r Hp Hr) as Hs.
  assert (0 < 2 ^ r /\ 2 ^ r <= 2 ^ 63) as Hr2. { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]. }
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite unsigned_lit_wrap. rewrite (unsigned_lit (p / _)) by lia.
  rewrite mod64_mulpow2 by lia. apply lor_mulpow2_small; try lia.
  all: pose proof (Z.mod_pos_bound x (2 ^ (64 - r)) ltac:(apply Z.pow_pos_nonneg; lia)); nia.
Qed.

(* [comment removed for export] *)
Definition shl_inv (ws0 cur : list word) (r : Z) (i : nat) (p : Z) : Prop :=
  bval cur i + (p / 2 ^ (64 - r)) * 2 ^ (64 * Z.of_nat i) = bval ws0 i * 2 ^ r
  /\ (forall j, (i <= j)%nat -> nth j cur w0 = nth j ws0 w0)
  /\ 0 <= p < 2 ^ 64
  /\ length cur = length ws0.

Lemma shl_inv_init : forall ws0 r, 1 <= r <= 63 -> shl_inv ws0 ws0 r 0 0.
Proof.
  intros ws0 r Hr. split; [| split; [intros; reflexivity| split; [lia| reflexivity]]].
  cbn [bval Z.of_nat Z.mul]. rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). lia.
Qed.

Lemma shl_inv_step : forall ws0 cur r i p (z : word),
  shl_inv ws0 cur r i p -> (i < length ws0)%nat -> 1 <= r <= 63 ->
  bv_unsigned z = shlb_limb (limbZ ws0 i) p r ->
  shl_inv ws0 (upd cur i z) r (S i) (limbZ ws0 i).
Proof.
  intros ws0 cur r i p z (Hv & Hag & Hp & Hlen) Hi Hr Hz.
  pose proof (limbZ_range ws0 i) as Hx.
  split; [| split; [| split; [exact Hx| rewrite upd_length; exact Hlen]]].
  - rewrite bval_push by (rewrite Hlen; exact Hi). rewrite Hz. unfold shlb_limb.
    rewrite bval_S, pow64_S.
    set (x := limbZ ws0 i) in *. set (c := p / 2 ^ (64 - r)) in *.
    assert (E : (x * 2 ^ r) mod 2 ^ 64 + (x / 2 ^ (64 - r)) * 2 ^ 64 = x * 2 ^ r).
    { replace (x / 2 ^ (64 - r)) with (x * 2 ^ r / 2 ^ 64).
      2:{ replace (2 ^ 64) with (2 ^ (64 - r) * 2 ^ r) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
          rewrite Z.div_mul_cancel_r; [reflexivity| apply Z.pow_nonzero; lia | apply Z.pow_nonzero; lia]. }
      pose proof (Z.div_mod (x * 2 ^ r) (2 ^ 64) ltac:(lia)). lia. }
    assert (bval cur i = bval ws0 i * 2 ^ r - c * 2 ^ (64 * Z.of_nat i)) as -> by lia.
    nia.
  - intros j Hj. rewrite nth_upd_other by lia. apply Hag. lia.
Qed.

Lemma shl_inv_finish_nocarry : forall ws0 cur r n p,
  shl_inv ws0 cur r n p -> p / 2 ^ (64 - r) = 0 -> bval cur n = bval ws0 n * 2 ^ r.
Proof. intros ws0 cur r n p (Hv & _) H0. rewrite H0 in Hv. lia. Qed.

Lemma shl_inv_finish_carry : forall ws0 cur r n p,
  shl_inv ws0 cur r n p -> (n < length ws0)%nat -> 1 <= r <= 63 ->
  bval (upd cur n (Z_to_bv 64 (p / 2 ^ (64 - r)))) (S n) = bval ws0 n * 2 ^ r.
Proof.
  intros ws0 cur r n p (Hv & Hag & Hp & Hlen) Hn Hr.
  pose proof (shr_small p r Hp Hr). assert (2 ^ r <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  rewrite bval_push by (rewrite Hlen; exact Hn). rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma shl_carry_room : forall ws0 cur r n p,
  shl_inv ws0 cur r n p -> 1 <= r <= 63 -> p / 2 ^ (64 - r) <> 0 ->
  bval ws0 n * 2 ^ r < BIG_CAP -> (n < 62)%nat.
Proof.
  intros ws0 cur r n p (Hv & _ & Hp & _) Hr Hc Hcap. unfold BIG_CAP in Hcap.
  pose proof (shr_small p r Hp Hr). pose proof (bval_nonneg cur n). pose proof (pow64_pos n).
  assert (2 ^ (64 * Z.of_nat n) <= bval ws0 n * 2 ^ r) by nia.
  destruct (Nat.lt_ge_cases n 62) as [|Hge]; [assumption|]. exfalso.
  assert (2 ^ (64 * 62) <= 2 ^ (64 * Z.of_nat n)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma shlb_top_nonzero : forall x p r,
  0 < x < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 1 <= r <= 63 -> x / 2 ^ (64 - r) = 0 -> shlb_limb x p r <> 0.
Proof.
  intros x p r Hx Hp Hr H0. unfold shlb_limb.
  pose proof (shr_small p r Hp Hr).
  assert (0 < 2 ^ (64 - r)) by (apply Z.pow_pos_nonneg; lia).
  assert (x < 2 ^ (64 - r)). { apply (Z.div_small_iff x (2 ^ (64 - r))) in H0; lia. }
  rewrite mod64_mulpow2 by lia. rewrite Z.mod_small by lia.
  assert (0 < 2 ^ r) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

(* [comment removed for export] *)
Lemma shr_word : forall x r, 0 <= x < 2 ^ 64 -> 1 <= r <= 63 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr x (64 - r))) = x / 2 ^ (64 - r).
Proof.
  intros x r Hx Hr. pose proof (shr_small x r Hx Hr). assert (2 ^ r <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.shiftr_div_pow2 by lia. apply unsigned_lit. lia.
Qed.

(* [comment removed for export] *)
Lemma bval_shift_limbs : forall (ws ws' : list word) (n d : nat),
  (forall j, (j < d)%nat -> limbZ ws' j = 0) ->
  (forall j, (j < n)%nat -> nth (d + j) ws' w0 = nth j ws w0) ->
  bval ws' (d + n) = bval ws n * 2 ^ (64 * Z.of_nat d).
Proof.
  intros ws ws' n d Hz Hs. induction n as [|n IH].
  - rewrite Nat.add_0_r, Z.mul_0_l. induction d as [|d IHd]; [reflexivity|].
    rewrite bval_S, IHd, Hz by (intros; try apply Hz; lia). lia.
  - rewrite Nat.add_succ_r, !bval_S, IH by (intros; apply Hs; lia).
    unfold limbZ. rewrite Hs by lia. rewrite Nat2Z.inj_add, Z.mul_add_distr_l, Z.pow_add_r by lia. ring.
Qed.

Lemma pow2_split64 : forall n, 0 <= n -> 2 ^ n = 2 ^ (n mod 64) * 2 ^ (64 * (n / 64)).
Proof.
  intros n Hn. rewrite <- Z.pow_add_r by (try apply Z.mul_nonneg_nonneg; try apply Z.div_pos; try apply Z.mod_pos_bound; lia).
  f_equal. pose proof (Z.div_mod n 64 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma words_of_bytes_u64s : forall ws, words_of_bytes (u64s ws) = ws.
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  cbn [u64s]. unfold le8, word_to_le_bytes. cbn [Z_to_le_bytes app words_of_bytes].
  rewrite IH. f_equal.
  pose proof (le_bytes_to_word_le8 w) as E. unfold le8, word_to_le_bytes in E. cbn [Z_to_le_bytes] in E. exact E.
Qed.

Lemma nth_repeat_app_lo : forall {X} (x d0 : X) (d : nat) (l : list X) j, (j < d)%nat -> nth j (repeat x d ++ l) d0 = x.
Proof. intros X x d0 d l j Hj. rewrite app_nth1 by (rewrite repeat_length; exact Hj). apply nth_repeat_lt. exact Hj. Qed.

Lemma nth_repeat_app_hi : forall {X} (x d0 : X) (d : nat) (l : list X) j, nth (d + j) (repeat x d ++ l) d0 = nth j l d0.
Proof. intros X x d0 d l j. rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length. f_equal. lia. Qed.

Section ArrSurgery.
Variable segs : list Segment.

#[using="Type"] Lemma u64arr_len_split3 : forall (ws : list word) (d n : nat), (d + n <= length ws)%nat ->
  ws = firstn d ws ++ firstn n (skipn d ws) ++ skipn (d + n) ws
  /\ length (firstn d ws) = d /\ length (firstn n (skipn d ws)) = n /\ length (skipn (d + n) ws) = (length ws - (d + n))%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ws d n H. split; [| split; [| split]].
  - rewrite <- (firstn_skipn d ws) at 1. f_equal.
    rewrite <- (firstn_skipn n (skipn d ws)) at 1. f_equal. rewrite skipn_skipn. f_equal. lia.
  - rewrite firstn_length. lia.
  - rewrite firstn_length, skipn_length. lia.
  - rewrite skipn_length. lia.
Qed.

#[using="Type"] Lemma u64arr_split3 : forall m A ws (d n : nat), (d + n <= length ws)%nat ->
  u64arr segs m A ws ->
  u64arr segs m A (firstn d ws)
  /\ u64arr segs m (A + 8 * Z.of_nat d) (firstn n (skipn d ws))
  /\ u64arr segs m (A + 8 * Z.of_nat (d + n)) (skipn (d + n) ws).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws d n H U.
  destruct (u64arr_len_split3 ws d n H) as (E & L1 & L2 & L3).
  rewrite E in U. apply u64arr_app in U. destruct U as [U1 U]. rewrite L1 in U.
  apply u64arr_app in U. destruct U as [U2 U3]. rewrite L2 in U3.
  replace (A + 8 * Z.of_nat d + 8 * Z.of_nat n) with (A + 8 * Z.of_nat (d + n)) in U3 by lia.
  split; [exact U1| split; [exact U2| exact U3]].
Qed.

#[using="Type"] Lemma u64arr_join3 : forall m A (w1 w2 w3 : list word) (d n : nat),
  length w1 = d -> length w2 = n ->
  u64arr segs m A w1 -> u64arr segs m (A + 8 * Z.of_nat d) w2 -> u64arr segs m (A + 8 * Z.of_nat (d + n)) w3 ->
  u64arr segs m A (w1 ++ w2 ++ w3).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A w1 w2 w3 d n L1 L2 U1 U2 U3.
  apply u64arr_app. rewrite L1. split; [exact U1|].
  apply u64arr_app. rewrite L2. split; [exact U2|].
  replace (A + 8 * Z.of_nat d + 8 * Z.of_nat n) with (A + 8 * Z.of_nat (d + n)) by lia. exact U3.
Qed.

#[using="Type"] Lemma u64arr_prefix_bytes : forall m A ws (n : nat), (n <= length ws)%nat ->
  u64arr segs m A ws -> bytes_at segs m A (u64s (firstn n ws)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws n Hn [B _]. rewrite <- (firstn_skipn n ws) in B. rewrite u64s_app in B.
  apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

End ArrSurgery.

(* [comment removed for export] *)
Lemma sx16_lit_small : forall z, 0 <= z < 2 ^ 15 -> sx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx16. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 16) with 65536. change (65536 / 2) with 32768.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lm_smul_lo_word : forall x y c, 0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= c < 2^64 ->
  bv_unsigned (Z_to_bv 64 (x * y + c)) = mul_lo x y c.
Proof.
  intros x y c Hx Hy Hc. rewrite unsigned_lit_wrap. unfold mul_lo.
  rewrite <- Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma lm_smul_carry_word : forall x y c, 0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= c < 2^64 ->
  Z_to_bv 64 (Z.shiftr (x * y) 64 + bv_unsigned (v_sltu (Z_to_bv 64 (x * y + c)) (Z_to_bv 64 (x * y))))
  = Z_to_bv 64 (mul_cout x y c).
Proof.
  intros x y c Hx Hy Hc. rewrite v_sltu_b2z.
  pose proof (zb_b2z_range (bv_unsigned (Z_to_bv 64 (x * y + c)) <? bv_unsigned (Z_to_bv 64 (x * y)))%Z) as Hb.
  rewrite (unsigned_lit (Z.b2z _)) by lia.
  f_equal. unfold mul_cout. rewrite shiftr64_div. f_equal.
  rewrite zb_b2z_if. rewrite (lm_smul_lo_word x y c) by assumption. rewrite unsigned_lit_wrap. reflexivity.
Qed.

Lemma lm_smul_carry_word' : forall x y c, 0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= c < 2^64 ->
  Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 (x * y + c)) (Z_to_bv 64 (x * y))) + Z.shiftr (x * y) 64)
  = Z_to_bv 64 (mul_cout x y c).
Proof. intros. rewrite Z.add_comm. apply lm_smul_carry_word; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shl48_shr45 : forall x, (0 <= x < 2 ^ 16)%Z ->
  Z.shiftr ((Z.shiftl x 48) mod 18446744073709551616) 45 = (8 * x)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2 ^ 48)%Z with ((8 * x) * 2 ^ 45)%Z by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma shl48_zero_iff : forall x, (0 <= x < 2 ^ 16)%Z ->
  ((Z.shiftl x 48) mod 18446744073709551616 = 0 <-> x = 0)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma shl48_zero_iff' : forall x, (0 <= x < 2 ^ 16)%Z ->
  (bv_unsigned (Z_to_bv 64 (Z.shiftl x 48)) = 0 <-> x = 0)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. lia.
Qed.

Lemma bval_drop_zero_top : forall ws n, (0 < n)%nat -> limbZ ws (n - 1) = 0%Z -> bval ws n = bval ws (n - 1).
Proof.
  intros ws n Hn Hz. destruct n as [|k]; [lia|]. replace (S k - 1)%nat with k in * by lia.
  rewrite bval_S, Hz. lia.
Qed.


Fixpoint zsum (l : list Z) (k : nat) : Z :=
  match k with O => 0%Z | S k' => (zsum l k' + nth k' l 0%Z * 2 ^ (64 * Z.of_nat k'))%Z end.

Lemma zsum_S : forall l k, zsum l (S k) = (zsum l k + nth k l 0%Z * 2 ^ (64 * Z.of_nat k))%Z.
Proof. reflexivity. Qed.

Lemma LP5_nth_range : forall k, (k < 5)%nat -> (0 < nth k LARGE_POW5 0%Z < 2 ^ 64)%Z.
Proof. intros k Hk. do 5 (destruct k as [|k]; [cbn; lia|]). lia. Qed.

Lemma LP5_zsum_5 : zsum LARGE_POW5 5 = (5 ^ 135)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma LP5_zsum_mono : forall k, (k <= 5)%nat -> (0 <= zsum LARGE_POW5 k <= 5 ^ 135)%Z.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|k]]]]]]; [ | | | | | | lia];
  (split; [vm_compute; discriminate | apply Z.leb_le; vm_compute; reflexivity]).
Qed.

Lemma LP5_zsum_step_le : forall k, (k < 5)%nat ->
  (zsum LARGE_POW5 k + nth k LARGE_POW5 0%Z * 2 ^ (64 * Z.of_nat k) <= 5 ^ 135)%Z.
Proof. intros k Hk. rewrite <- zsum_S. apply LP5_zsum_mono. lia. Qed.

Lemma shl48_shr48m : forall x, (0 <= x < 2 ^ 16)%Z ->
  Z.shiftr ((Z.shiftl x 48) mod 18446744073709551616) 48 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bval_agree : forall (a b : list word) n, (forall j, (j < n)%nat -> nth j a w0 = nth j b w0) -> bval a n = bval b n.
Proof. intros. apply bval_ext. assumption. Qed.

(* [comment removed for export] *)
Lemma cap_step : forall X s yk p C5 C, (0 <= X)%Z -> (0 <= yk)%Z -> (0 <= p)%Z -> (s + yk * p <= C5)%Z -> (X * C5 < C)%Z ->
  (X * s + yk * X * p < C)%Z.
Proof. intros. nia. Qed.

Lemma cap_yk : forall X s yk p C5 C, (0 <= X)%Z -> (0 <= s)%Z -> (1 <= yk)%Z -> (1 <= p)%Z -> (s + yk * p <= C5)%Z -> (X * C5 < C)%Z ->
  (yk * X < C)%Z /\ (yk * X * p < C)%Z.
Proof. intros. nia. Qed.

Lemma room_pow : forall P k L, (0 <= L)%Z -> (0 <= k)%Z -> (2 ^ (64 * L) <= P)%Z -> (P * 2 ^ (64 * k) < 2 ^ 3968)%Z -> (L + k < 62)%Z.
Proof.
  intros P k L HL Hk HP HC.
  assert (E : (2 ^ (64 * L) * 2 ^ (64 * k) < 2 ^ 3968)%Z). { pose proof (Z.pow_nonneg 2 (64 * k) ltac:(lia)). nia. }
  rewrite <- Z.pow_add_r in E by lia. apply Z.pow_lt_mono_r_iff in E; lia.
Qed.

Lemma room_nocarry : forall X yk k L, (0 <= L)%Z -> (0 <= k)%Z -> (2 ^ (64 * L) <= X)%Z -> (1 <= yk)%Z ->
  (yk * X * 2 ^ (64 * k) < 2 ^ 3968)%Z -> (L + k < 62)%Z.
Proof.
  intros X yk k L HL Hk HX Hyk HC. apply (room_pow (yk * X) k L); try lia.
  pose proof (Z.pow_nonneg 2 (64 * L) ltac:(lia)). nia.
Qed.

Lemma room_carry : forall (b c P : Z) k L, (0 <= L)%Z -> (0 <= k)%Z -> (0 <= b)%Z -> (1 <= c)%Z ->
  (b + c * 2 ^ (64 * L) = P)%Z -> (P * 2 ^ (64 * k) < 2 ^ 3968)%Z -> (L + k < 62)%Z.
Proof.
  intros b c P k L HL Hk Hb Hc E HC. apply (room_pow P k L); try lia.
  pose proof (Z.pow_nonneg 2 (64 * L) ltac:(lia)). nia.
Qed.

Lemma u64arr_at_eq : forall segs m A B ws, u64arr segs m A ws -> A = B -> u64arr segs m B ws.
Proof. intros * H <-. exact H. Qed.
Lemma stk_at_eq : forall segs m lo hi lo' hi', stk segs m lo hi -> lo = lo' -> hi = hi' -> stk segs m lo' hi'.
Proof. intros * H <- <-. exact H. Qed.
Lemma rw_cells_at_eq : forall segs m A B cs, rw_cells segs m A cs -> A = B -> rw_cells segs m B cs.
Proof. intros * H <-. exact H. Qed.


(* [comment removed for export] *)
Lemma rw_cells_CB2_C2 : forall segs m A bs rest,
  rw_cells segs m A (CB 2 bs :: rest) -> exists z, (0 <= z < 2 ^ 16)%Z /\ rw_cells segs m A (C2 (Z_to_bv 64 z) :: rest).
Proof.
  intros segs m A bs rest [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl Hwf].
  exists (bytes_le_to_Z bs).
  pose proof (bytes_le_to_Z_bound bs) as Hr. rewrite Hl in Hr. change (2 ^ (8 * Z.of_nat 2))%Z with (2 ^ 16)%Z in Hr.
  split; [lia|]. split; [split|].
  - cbn. split; [exact I| exact Hwf].
  - cbn [cells_bytes cbytes] in *. unfold le2. rewrite unsigned_lit by lia. rewrite <- Hl, Z_to_le_bytes_to_Z. exact Hb.
  - exact Hw.
Qed.

Lemma shl51_shr48m : forall x, (0 <= x < 2 ^ 13)%Z ->
  Z.shiftr ((Z.shiftl x 51) mod 18446744073709551616) 48 = (8 * x)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2 ^ 51)%Z with ((8 * x) * 2 ^ 48)%Z by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.


Lemma swrap32_small : forall z, (- 2 ^ 31 <= z < 2 ^ 31)%Z -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 `div` 2)%Z with (2 ^ 31)%Z. lia. Qed.

(* [comment removed for export] *)
Lemma cap_pow5_mono : forall X a b C, (0 <= X)%Z -> (0 <= a <= b)%Z -> (X * 5 ^ b < C)%Z -> (X * 5 ^ a < C)%Z.
Proof.
  intros X a b C HX Hab HC. assert (5 ^ a <= 5 ^ b)%Z by (apply Z.pow_le_mono_r; lia).
  pose proof (Z.pow_nonneg 5 a ltac:(lia)). nia.
Qed.

Lemma pow5_step_val : forall X e0 e s, (0 <= s <= e)%Z -> (e <= e0)%Z ->
  (X * 5 ^ (e0 - e) * 5 ^ s = X * 5 ^ (e0 - (e - s)))%Z.
Proof.
  intros X e0 e s Hs He. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia.
Qed.

Lemma mul_pow5_zero : forall x k, (0 <= k)%Z -> (x * 5 ^ k = 0)%Z -> x = 0%Z.
Proof. intros x k Hk H. pose proof (Z.pow_pos_nonneg 5 k ltac:(lia) Hk). nia. Qed.

Lemma bnorm_of_value : forall cur n, (0 < n)%nat -> (2 ^ (64 * Z.of_nat (n - 1)) <= bval cur n)%Z -> bnorm cur n.
Proof.
  intros cur n Hn Hv. destruct n as [|k]; [lia|]. right. replace (S k - 1)%nat with k in * by lia.
  rewrite bval_S in Hv. pose proof (bval_range cur k) as R. intros Z0. rewrite Z0 in Hv. lia.
Qed.



Lemma pow10_split : forall e, (0 <= e)%Z -> (10 ^ e = 5 ^ e * 2 ^ e)%Z.
Proof. intros e He. change 10%Z with (5 * 2)%Z. rewrite Z.pow_mul_l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma shl32_shr32 : forall x, (0 <= x < 2 ^ 32)%Z -> Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 32))) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma shl32_shr32m : forall x, (0 <= x < 2 ^ 32)%Z -> Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.


Lemma bytes_at_at_eq : forall segs m A B bs, bytes_at segs m A bs -> A = B -> bytes_at segs m B bs.
Proof. intros * H <-. exact H. Qed.
Lemma u8arr_at_eq : forall segs m A B bs, u8arr segs m A bs -> A = B -> u8arr segs m B bs.
Proof. intros * H <-. exact H. Qed.

Lemma lor_lt_64 : forall a b, (0 <= a < 64)%Z -> (0 <= b < 64)%Z -> (0 <= Z.lor a b < 64)%Z.
Proof.
  intros a b Ha Hb. split. { apply Z.lor_nonneg; lia. }
  destruct (Z.eq_dec a 0) as [->|Na]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|Nb]. { rewrite Z.lor_0_r. lia. }
  apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia. change (Z.log2 64) with 6%Z.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
