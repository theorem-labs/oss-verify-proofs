(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage1.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import SjModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma div3_magic : forall c, 0 <= c < 2^32 -> Z.shiftr (c * 2863311531) 33 = c / 3.
Proof.
  intros c H. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod c 3 ltac:(lia)) as E. pose proof (Z.mod_pos_bound c 3 ltac:(lia)) as R.
  set (k := c / 3) in *. set (r := c mod 3) in *.
  symmetry. apply (Z.div_unique_pos _ _ k (k + r * 2863311531)); [| ].
  - change (2^33) with 8589934592. change (2^32) with 4294967296 in H. lia.
  - change (2^33) with 8589934592. lia.
Qed.

Lemma land_ones64 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551615 = y.
Proof. intros y H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. exact H. Qed.

Lemma land_ldiff_distr : forall x a b, Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof.
  intros x a b. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
  destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity.
Qed.

Lemma land_align : forall y hi k mask, mask = Z.ldiff (Z.ones hi) (Z.ones k) -> 0 <= k <= hi -> 0 <= y < 2^hi ->
  Z.land y mask = y - y mod 2^k.
Proof.
  intros y hi k mask E Hk Hy.
  rewrite E, land_ldiff_distr, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod y (2^k)). assert (P : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma roundup64_alt : forall x, roundup64 x = (x + 63) - (x + 63) mod 64.
Proof. intros x. unfold roundup64. pose proof (Z.div_mod (x + 63) 64 ltac:(lia)). lia. Qed.

Lemma sbuf_size_eq : forall cap, 0 <= cap < 2^32 ->
  Z.land (Z.land (Z.shiftl (Z.shiftr (cap * 2863311531) 33) 2 + Z.shiftr (cap * 2863311531) 33 + 127) 18446744073709551615) 18446744073709551552
  = roundup64 (5 * (cap / 3) + 64).
Proof.
  intros cap H. rewrite (div3_magic cap H). rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
  assert (D : 0 <= cap / 3 < 2^32) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  change (2^32) with 4294967296 in *.
  rewrite land_ones64 by (change (2^64) with 18446744073709551616; lia).
  rewrite (land_align _ 64 6) by (first [reflexivity | change (2^64) with 18446744073709551616; lia]).
  rewrite roundup64_alt. change (2^6) with 64. f_equal; [lia| f_equal; lia].
Qed.

Lemma tape_size_eq : forall cap, 0 <= cap < 2^32 ->
  Z.land (Z.land (Z.shiftl cap 3 + 528) 18446744073709551615) 68719476224 = 8 * roundup64 (cap + 3).
Proof.
  intros cap H. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. change (2^32) with 4294967296 in H.
  rewrite land_ones64 by (change (2^64) with 18446744073709551616; lia).
  rewrite (land_align _ 36 9) by (first [reflexivity | change (2^36) with 68719476736; lia]).
  rewrite roundup64_alt. change (2^9) with 512.
  replace (cap * 8 + 528) with (8 * (cap + 3 + 63)) by lia.
  change 512 with (8 * 64). rewrite Z.mul_mod_distr_l by lia. lia.
Qed.

Lemma idx_size_eq : forall cap, 0 <= cap < 2^32 ->
  Z.land (Z.land (Z.shiftl cap 2 + 252) 18446744073709551615) 34359738112 + 36 = 4 * (roundup64 cap + 9).
Proof.
  intros cap H. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. change (2^32) with 4294967296 in H.
  rewrite land_ones64 by (change (2^64) with 18446744073709551616; lia).
  rewrite (land_align _ 35 8) by (first [reflexivity | change (2^35) with 34359738368; lia]).
  rewrite roundup64_alt. change (2^8) with 256.
  replace (cap * 4 + 252) with (4 * (cap + 63)) by lia.
  change 256 with (4 * 64). rewrite Z.mul_mod_distr_l by lia. lia.
Qed.

Lemma scan_token_err : forall bs i st, err_ok (s_err st) -> err_ok (s_err (scan_token bs i st)).
Proof.
  intros bs i st H. unfold scan_token.
  destruct (B bs i =? 34).
  - destruct (str_loop bs (length bs) (i + 1) (s_err st)) as [[i' err'] u] eqn:E. cbn [s_err].
    eapply str_loop_err; [exact E| exact H].
  - destruct (t_op (B bs i)); cbn [s_err]; exact H.
Qed.

Lemma scan_loop_err : forall bs f st, err_ok (s_err st) -> err_ok (s_err (scan_loop bs f st)).
Proof.
  intros bs f. induction f as [|f IH]; intros st H; cbn [scan_loop]; [exact H|].
  destruct (s_idx st <? blen bs); [| exact H].
  destruct (blen bs <=? ws_run bs (length bs) (s_idx st)); [cbn [s_err]; exact H|].
  apply IH. apply scan_token_err. exact H.
Qed.

Lemma stage1_code_range : forall bs, 0 <= fst (stage1 bs) < 64.
Proof.
  intros bs. unfold stage1. cbn [fst]. unfold s1_code.
  destruct (length (s_out (stage1_st bs)) =? 0)%nat; [unfold EMPTY; lia|].
  destruct (s_unclosed (stage1_st bs)); [unfold UNCLOSED_STRING; lia|].
  apply err_ok_range. unfold stage1_st. apply scan_loop_err. cbn [s_err s1_init]. left. reflexivity.
Qed.

Ltac strip_bom_crunch :=
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x; try reflexivity; try congruence
         end.

Lemma strip_bom_short : forall d : list Z, (length d < 3)%nat -> SjAlloc.strip_bom d = d.
Proof.
  intros d H. destruct d as [|a [|b [|c r]]]; cbn [length] in H; try lia; unfold SjAlloc.strip_bom; strip_bom_crunch; reflexivity.
Qed.

Lemma strip_bom_hit : forall r, SjAlloc.strip_bom (239 :: 187 :: 191 :: r) = r.
Proof. reflexivity. Qed.

Lemma strip_bom_miss : forall c0 c1 c2 r, ~ (c0 = 239 /\ c1 = 187 /\ c2 = 191) -> SjAlloc.strip_bom (c0 :: c1 :: c2 :: r) = c0 :: c1 :: c2 :: r.
Proof.
  intros c0 c1 c2 r H. unfold SjAlloc.strip_bom. strip_bom_crunch. exfalso. apply H. auto.
Qed.

Lemma land7_aligned : forall A, 0 <= A -> A mod 16 = 0 -> Z.land A 7 = 0.
Proof.
  intros A H0 H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
  pose proof (Z.div_mod A 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
  replace (16 * (A / 16)) with ((2 * (A / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma land3_aligned : forall A, 0 <= A -> A mod 16 = 0 -> Z.land A 3 = 0.
Proof.
  intros A H0 H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4.
  pose proof (Z.div_mod A 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
  replace (16 * (A / 16)) with ((4 * (A / 16)) * 4) by lia. apply Z.mod_mul. lia.
Qed.
Lemma land15_aligned : forall A, 0 <= A -> A mod 16 = 0 -> Z.land A 15 = 0.
Proof. intros A H0 H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact H. Qed.
Lemma mod4_of_mod16 : forall A, A mod 16 = 0 -> A mod 4 = 0.
Proof.
  intros A H. pose proof (Z.div_mod A 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
  replace (16 * (A / 16)) with ((4 * (A / 16)) * 4) by lia. apply Z.mod_mul. lia.
Qed.
