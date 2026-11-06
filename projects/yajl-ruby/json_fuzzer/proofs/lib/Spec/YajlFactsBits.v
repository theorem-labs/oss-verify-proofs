(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode
     YajlFactsDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma land_shiftl_small : forall a c k, 0 <= a -> 0 <= c < 2 ^ k -> 0 <= k ->
  Z.land (Z.shiftl a k) c = 0.
Proof.
  intros a c k Ha Hc Hk. apply Z.bits_inj_0. intros n.
  destruct (Z.lt_ge_cases n 0) as [Hn|Hn].
  { destruct n; try reflexivity; lia. }
  rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n k) as [Hnk|Hnk].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - replace (Z.testbit c n) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec c 0) as [->|Hc0]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (2 ^ k); [lia|].
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma lor_shiftl_small : forall a c k, 0 <= a -> 0 <= c < 2 ^ k -> 0 <= k ->
  Z.lor (Z.shiftl a k) c = a * 2 ^ k + c.
Proof.
  intros a c k Ha Hc Hk.
  rewrite <- Z.lxor_lor by (apply land_shiftl_small; auto).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_small; auto).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma hex_loop_bound : forall hs val,
  (forall h, In h hs -> is_vhc h = true) -> 0 <= val ->
  exists v, hex_loop val hs = Some v /\ 0 <= v < (val + 1) * 16 ^ (Z.of_nat (length hs)).
Proof.
  induction hs as [|h hs IH]; intros val Hall Hval; cbn [hex_loop length].
  - exists val. split; auto. cbn. lia.
  - pose proof (vhc_hex_digit h (Hall h (or_introl eq_refl))) as [Hmask Hrange].
    rewrite Hmask. cbn [Z.eqb].
    rewrite (lor_shiftl_small val (hex_digit_adj h) 4) by (auto; cbn; lia).
    destruct (IH (val * 2 ^ 4 + hex_digit_adj h)) as (v & Hv & Hb).
    + intros; apply Hall; right; auto.
    + cbn; lia.
    + exists v. split; auto. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      change (2 ^ 4) with 16 in Hb. nia.
Qed.

Lemma yhexToDigit_bound : forall str i,
  (forall k, 0 <= k < 4 -> is_vhc (znth str (i + k)) = true) ->
  exists v, yhexToDigit 0 str i = Some v /\ 0 <= v < 65536.
Proof.
  intros str i Hall. unfold yhexToDigit.
  assert (HALL : forall h, In h [znth str i; znth str (i + 1); znth str (i + 2); znth str (i + 3)] ->
                           is_vhc h = true).
  { intros h Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]].
    + replace i with (i + 0) by lia. apply Hall. lia.
    + apply Hall. lia.
    + apply Hall. lia.
    + apply Hall. lia. }
  destruct (hex_loop_bound _ 0 HALL ltac:(lia)) as (v & Hv & Hb).
  exists v. split; auto; cbn in Hb; lia.
Qed.

(* [comment removed for export] *)
Lemma combine_surrogate_bound : forall cp sur, 0 <= cp -> 0 <= sur ->
  0 <= combine_surrogate cp sur < 1114112.  (* [comment removed for export] *)
Proof.
  intros cp sur Hcp Hsur. unfold combine_surrogate.
  assert (H1 : 0 <= Z.land cp 63 < 64).
  { split; [apply Z.land_nonneg; lia|].
    change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (H2 : 0 <= Z.land (Z.shiftr cp 6) 15 < 16).
  { split; [apply Z.land_nonneg; left; apply Z.shiftr_nonneg; lia|].
    change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (H3 : 0 <= Z.land sur 1023 < 1024).
  { split; [apply Z.land_nonneg; lia|].
    change 1023 with (Z.ones 10). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  set (a := Z.land cp 63) in *. set (b := Z.land (Z.shiftr cp 6) 15) in *. set (c := Z.land sur 1023) in *.
  (* [comment removed for export] *)
  assert (E1 : Z.lor (Z.shiftl a 10) (Z.shiftl (b + 1) 16) = (b + 1) * 2^16 + a * 2^10).
  { rewrite Z.lor_comm.
    replace (Z.shiftl (b + 1) 16) with (Z.shiftl ((b + 1) * 2^6) 10)
      by (rewrite !Z.shiftl_mul_pow2 by lia; rewrite <- Z.mul_assoc; reflexivity).
    rewrite <- Z.shiftl_lor.
    rewrite <- (Z.shiftl_mul_pow2 (b+1) 6) by lia.
    rewrite (lor_shiftl_small (b + 1) a 6) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. lia. }
  rewrite E1.
  replace ((b + 1) * 2 ^ 16 + a * 2 ^ 10) with (Z.shiftl ((b + 1) * 2^6 + a) 10)
    by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (lor_shiftl_small ((b + 1) * 2^6 + a) c 10) by lia.
  lia.
Qed.

(* [comment removed for export] *)
Lemma combine_surrogate_machine : forall cp sur, 0 <= cp -> 0 <= sur ->
  Z.lor (Z.land (Z.shiftl cp 10) 1047552) (Z.land sur 1023) + 65536 = combine_surrogate cp sur.
Proof.
  intros cp sur Hcp Hsur. unfold combine_surrogate.
  assert (Ha : Z.land cp 63 = cp mod 2^6) by (change 63 with (Z.ones 6); apply Z.land_ones; lia).
  assert (Hb : Z.land (Z.shiftr cp 6) 15 = (cp / 2^6) mod 2^4).
  { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (Hc : 0 <= Z.land sur 1023 < 2^10).
  { change 1023 with (Z.ones 10). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (Hx : Z.land (Z.shiftl cp 10) 1047552 = Z.shiftl (cp mod 2^10) 10).
  { change 1047552 with (Z.shiftl (Z.ones 10) 10). rewrite <- Z.shiftl_land, Z.land_ones by lia. reflexivity. }
  rewrite Hx, Ha, Hb.
  set (a := cp mod 2^6) in *. set (b := (cp / 2^6) mod 2^4) in *. set (c := Z.land sur 1023) in *.
  set (x := cp mod 2^10) in *.
  assert (Hx' : 0 <= x < 2^10) by (subst x; apply Z.mod_pos_bound; lia).
  assert (Ha' : 0 <= a < 2^6) by (subst a; apply Z.mod_pos_bound; lia).
  assert (Hb' : 0 <= b < 2^4) by (subst b; apply Z.mod_pos_bound; lia).
  assert (E : x = 64 * b + a).
  { subst x a b. change (2^10) with (64 * 16). rewrite Z.rem_mul_r by lia. change (2^6) with 64. change (2^4) with 16. lia. }
  rewrite (lor_shiftl_small x c 10) by lia.
  assert (E1 : Z.lor (Z.shiftl a 10) (Z.shiftl (b + 1) 16) = (b + 1) * 2^16 + a * 2^10).
  { rewrite Z.lor_comm.
    replace (Z.shiftl (b + 1) 16) with (Z.shiftl ((b + 1) * 2^6) 10)
      by (rewrite !Z.shiftl_mul_pow2 by lia; rewrite <- Z.mul_assoc; reflexivity).
    rewrite <- Z.shiftl_lor.
    rewrite <- (Z.shiftl_mul_pow2 (b+1) 6) by lia.
    rewrite (lor_shiftl_small (b + 1) a 6) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. lia. }
  rewrite E1.
  replace ((b + 1) * 2 ^ 16 + a * 2 ^ 10) with (Z.shiftl ((b + 1) * 2^6 + a) 10)
    by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (lor_shiftl_small ((b + 1) * 2^6 + a) c 10) by lia.
  rewrite E. change (2^10) with 1024. change (2^6) with 64. lia.
Qed.
