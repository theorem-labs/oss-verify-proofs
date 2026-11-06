(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim BnBase BnModel BnTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma magic63_q : forall x, 0 <= x <= 16127937 -> Z.shiftr (x * 68174085) 32 = x / 63.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
  pose proof (Z.div_mod x 63 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 63 ltac:(lia)) as R.
  set (a := x / 63) in *. set (r := x mod 63) in *.
  symmetry. apply Z.div_unique with (59 * a + 68174085 * r); lia.
Qed.

Lemma magic63_t : forall x, 0 <= x <= 16127937 -> Z.shiftr (Z.shiftr (x - x / 63) 1 + x / 63) 5 = x / 63.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 5) with 32.
  pose proof (Z.div_mod x 63 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 63 ltac:(lia)) as R.
  set (a := x / 63) in *. set (r := x mod 63) in *.
  assert (E2 : (x - a) / 2 = 31 * a + r / 2).
  { replace (x - a) with (r + (31 * a) * 2) by lia. rewrite Z.div_add by lia. lia. }
  rewrite E2. replace (31 * a + r / 2 + a) with (r / 2 + a * 32) by lia. rewrite Z.div_add by lia.
  assert (r / 2 / 32 = 0) by (apply Z.div_small; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Lemma div63_le : forall b x, 0 <= b <= 63 -> 0 <= x -> 0 <= (b * x) / 63 <= x.
Proof.
  intros b x Hb Hx. split; [apply Z.div_pos; nia|]. apply Z.div_le_upper_bound; nia.
Qed.

(* [comment removed for export] *)
Lemma MAX_LEN_S : MAX_LEN = S (MAX_LEN - 1).
Proof. unfold MAX_LEN. lia. Qed.

Lemma firstn_MAX_cons : forall (b0 : Z) (d' : list Z), firstn MAX_LEN (b0 :: d') = b0 :: firstn (MAX_LEN - 1) d'.
Proof. intros. rewrite MAX_LEN_S at 1. reflexivity. Qed.

Lemma firstn_MAX1_len : forall (d' : list Z), Z.of_nat (length (firstn (MAX_LEN - 1) d')) = Z.min (zlength d' + 1) 256000 - 1.
Proof. intros d'. rewrite length_firstn. unfold MAX_LEN, zlength. lia. Qed.

(* [comment removed for export] *)
Lemma payload_split : forall (d' : list Z) (l1 : nat),
  let rest := firstn (MAX_LEN - 1) d' in
  (l1 <= length rest)%nat ->
  d' = firstn l1 rest ++ skipn l1 rest ++ skipn (MAX_LEN - 1) d'.
Proof.
  intros d' l1 rest H. rewrite app_assoc, firstn_skipn. unfold rest. symmetry. apply firstn_skipn.
Qed.

(* [comment removed for export] *)
Lemma land_m64_small : forall y, 0 <= y < 18446744073709551616 -> Z.land y 18446744073709551615 = y.
Proof. intros y Hy. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. exact Hy. Qed.

Lemma magic63_hi : forall x, 0 <= x <= 16127937 ->
  Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615 * 292805465509724160) 64 = x * 68174085.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite land_m64_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 4294967296 * 292805465509724160) with ((x * 68174085) * 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
  apply Z.div_mul. lia.
Qed.

Lemma land63_range : forall b, 0 <= b -> 0 <= Z.land b 63 <= 63.
Proof.
  intros b Hb. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b (2 ^ 6) ltac:(lia)). change (2 ^ 6) with 64 in *. change (Z.ones 6) with 63. lia.
Qed.

(* [comment removed for export] *)
Definition fuzz_body {ptr} (s1 s2 : bool) (n1 n2 : list Z) : lstate ptr -> btree ptr (Z * lstate ptr) :=
  let ops := tree_ops ptr in
  bbind ops (BN_bin2bn ops n1 RB1) (fun _ =>
  bbind ops (BN_set_negative ops RB1 s1) (fun _ =>
  bbind ops (BN_bin2bn ops n2 RB2) (fun _ =>
  bbind ops (BN_set_negative ops RB2 s2) (fun _ =>
  bbind ops (bget ops RB2) (fun b2 =>
  bbind ops
    (if (bn_top b2 =? 0)%nat then bret ops tt
     else
       bbind ops (BN_div ops RB3 RB4 RB1 RB2) (fun _ =>
       bbind ops (bget ops RB1) (fun b1 => bbind ops (bget ops RB2) (fun b2 => bbind ops (bget ops RB3) (fun b3 => bbind ops (bget ops RB4) (fun b4 =>
       let z b := (bn_top (b : bignum ptr) =? 0)%nat in
       let success :=
         if z b1 then z b3 && z b4
         else if bn_neg b1 then (negb (Bool.eqb (bn_neg b3) (bn_neg b2)) || z b3) && (bn_neg b4 || z b4)
         else (Bool.eqb (bn_neg b3) (bn_neg b2) || z b3) && (negb (bn_neg b4) || z b4) in
       bbind ops (BN_mul ops RB5 RB3 RB2) (fun _ =>
       bbind ops (BN_add ops RB5 RB5 RB4) (fun _ =>
       bbind ops (bget ops RB5) (fun b5 => bbind ops (bget ops RB1) (fun b1 =>
       if success && (cmp_pure b5 b1 =? 0) then bret ops tt else bunr ops))))))))))
    (fun _ => bret ops 0)))))).

Lemma fuzz_one_nil : forall {ptr} (ls : lstate ptr), fuzz_one (tree_ops ptr) [] ls = fuzz_body false false [] [] ls.
Proof. intros. reflexivity. Qed.

Lemma fuzz_one_cons : forall {ptr} (b0 : Z) (d' : list Z) (ls : lstate ptr),
  let rest := firstn (MAX_LEN - 1) d' in
  let l1 := Z.to_nat ((Z.land b0 63 * Z.of_nat (length rest)) / 63) in
  fuzz_one (tree_ops ptr) (b0 :: d') ls =
  fuzz_body (negb (Z.land b0 64 =? 0)) (negb (Z.land b0 128 =? 0)) (firstn l1 rest) (skipn l1 rest) ls.
Proof. intros. unfold fuzz_one. rewrite firstn_MAX_cons. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_byte_range : forall b k, 0 <= b < 256 -> 0 <= k < 256 -> 0 <= Z.land b k < 256.
Proof.
  intros b k Hb Hk. split; [apply Z.land_nonneg; lia|].
  assert (E : Z.land b k = Z.land (Z.land b k) (Z.ones 8)).
  { rewrite <- Z.land_assoc. f_equal. change (Z.ones 8) with 255. symmetry.
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. }
  rewrite E, Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
