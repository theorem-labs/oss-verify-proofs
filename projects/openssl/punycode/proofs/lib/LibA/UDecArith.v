(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit DecArith ULib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lor_mod4 : forall a b, 0 <= a -> 0 <= b -> a mod 4 = 0 -> b mod 4 = 0 -> (Z.lor a b) mod 4 = 0.
Proof.
  intros a b Ha Hb Ea Eb. change 4 with (2 ^ 2) in *. rewrite <- Z.land_ones in * by lia.
  rewrite Z.land_lor_distr_l, Ea, Eb. reflexivity.
Qed.

Lemma align_or : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x mod 4 = 0 -> y mod 4 = 0 ->
  bv_unsigned (v_andi (v_or (W x) (W y)) 3) = 0.
Proof.
  intros x y Hx Hy Ex Ey. rewrite or_W by lia. change 3 with (Z.ones 2).
  pose proof (Z_lor_range x y ltac:(lia) ltac:(lia)) as Hr.
  rewrite u_andi_ones_W by lia. change (2 ^ 2) with 4. apply lor_mod4; lia.
Qed.

Lemma swrap32_signed : forall z r, (z - r) mod 2 ^ 32 = 0 -> - 2 ^ 31 <= r < 2 ^ 31 -> bv_swrap 32 z = r.
Proof.
  intros z r Hz Hr. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  assert (E : (z + 2 ^ 31) mod 2 ^ 32 = r + 2 ^ 31).
  { replace (z + 2 ^ 31) with ((r + 2 ^ 31) + (z - r)) by lia.
    rewrite Zplus_mod, Hz, Z.add_0_r, Z.mod_mod by lia. apply Z.mod_small. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma t_mid : forall bias kk, 0 <= bias < 2 ^ 30 -> 0 <= kk < 2 ^ 30 ->
  v_addw (v_subw (W 0) (W bias)) (W kk) = W (kk - bias).
Proof.
  intros bias kk Hb Hk. rewrite subw_W by lia. unfold v_addw. f_equal.
  rewrite Wu_mod, (Wu kk) by lia. apply swrap32_signed; [|lia].
  replace ((0 - bias) mod 2 ^ 64 + kk - (kk - bias)) with ((0 - bias) mod 2 ^ 64 + bias) by lia.
  rewrite Zplus_mod, mod32_of_mod64, <- Zplus_mod. replace (0 - bias + bias) with 0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w_step : forall (a5 : word) x wv, bv_unsigned a5 mod 2 ^ 32 = wv -> 0 <= x < 2 ^ 32 ->
  bv_unsigned (v_srli (v_mulhu (v_slli (W x) 32) (v_slli a5 32)) 32) = 0 ->
  bv_unsigned (v_mulw (W x) a5) mod 2 ^ 32 = x * wv /\ x * wv < 2 ^ 32.
Proof.
  intros a5 x wv Hw Hx H0.
  assert (Hwv : 0 <= wv < 2 ^ 32) by (rewrite <- Hw; apply Z.mod_pos_bound; lia).
  assert (E1 : bv_unsigned (v_slli (W x) 32) = x * 2 ^ 32).
  { unfold v_slli. rewrite Wu_mod, Z.shiftl_mul_pow2 by lia. rewrite shl32_mod. rewrite Wu by lia.
    rewrite Z.mod_small by lia. reflexivity. }
  assert (E2 : bv_unsigned (v_slli a5 32) = wv * 2 ^ 32).
  { unfold v_slli. rewrite Wu_mod, Z.shiftl_mul_pow2 by lia. rewrite shl32_mod, Hw. reflexivity. }
  unfold v_srli, v_mulhu in H0. rewrite E1, E2 in H0. rewrite !Z.shiftr_div_pow2 in H0 by lia.
  replace (x * 2 ^ 32 * (wv * 2 ^ 32)) with (x * wv * 2 ^ 64) in H0 by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); lia).
  rewrite Z.div_mul in H0 by lia.
  assert (Hp : 0 <= x * wv < 2 ^ 64) by nia.
  rewrite (Wu (x * wv)) in H0 by lia.
  assert (Hd : 0 <= x * wv / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Wu in H0 by lia.
  assert (Hlt : x * wv < 2 ^ 32).
  { destruct (Z_lt_le_dec (x * wv) (2 ^ 32)); [assumption|]. exfalso.
    assert (1 <= x * wv / 2 ^ 32) by (apply Z.div_le_lower_bound; lia). lia. }
  split; [|exact Hlt].
  unfold v_mulw. rewrite Wu_mod, mod32_of_mod64, swrap32_mod. rewrite (Wu x) by lia.
  rewrite Zmult_mod, Hw, (Z.mod_small x) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma adapt_bound : forall (a0 s9 : word),
  exists nv, 0 <= nv /\ 32 * nv <= bv_unsigned a0 mod 2 ^ 32 /\
    v_srliw (v_add (v_srliw (v_subw a0 (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 1)
                   (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 5 = W nv.
Proof.
  intros a0 s9. set (dl := bv_unsigned a0 mod 2 ^ 32).
  assert (Hdl : 0 <= dl < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  pose proof (u64_range s9) as HS.
  set (hi := v_srli (v_mulhu (v_slli a0 32) s9) 32).
  assert (Hhi : exists hv, 0 <= hv <= dl /\ hi = W hv).
  { assert (E1 : bv_unsigned (v_slli a0 32) = dl * 2 ^ 32).
    { unfold v_slli. rewrite Wu_mod, Z.shiftl_mul_pow2 by lia. apply shl32_mod. }
    unfold hi, v_srli, v_mulhu. rewrite E1. rewrite !Z.shiftr_div_pow2 by lia.
    assert (Hh1 : 0 <= dl * 2 ^ 32 * bv_unsigned s9 / 2 ^ 64 <= dl * 2 ^ 32).
    { split; [apply Z.div_pos; nia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
    rewrite Wu by lia.
    exists (dl * 2 ^ 32 * bv_unsigned s9 / 2 ^ 64 / 2 ^ 32). split; [|reflexivity].
    split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  destruct Hhi as (hv & Hhv & ->).
  rewrite (srliw_val (v_subw a0 (W hv))) by lia. rewrite subw_mod32. rewrite (Wu hv) by lia.
  rewrite <- Zminus_mod_idemp_l. fold dl. rewrite (Z.mod_small (dl - hv)) by lia.
  assert (Ha5 : 0 <= (dl - hv) / 2 ^ 1 <= dl - hv) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite add_W. rewrite srliw_val by lia.
  rewrite (Wu ((dl - hv) / 2 ^ 1 + hv)) by lia. rewrite (Z.mod_small ((dl - hv) / 2 ^ 1 + hv)) by lia.
  exists (((dl - hv) / 2 ^ 1 + hv) / 2 ^ 5). split; [apply Z.div_pos; lia|]. split; [|reflexivity].
  pose proof (Z.mul_div_le ((dl - hv) / 2 ^ 1 + hv) (2 ^ 5) ltac:(lia)). change (2 ^ 5) with 32 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma adapt_continue : forall (a0 : word) t, 0 <= t < 2 ^ 29 ->
  bv_unsigned (W t) < bv_unsigned (v_srliw a0 3) -> 8 * (t + 1) <= bv_unsigned a0 mod 2 ^ 32.
Proof.
  intros a0 t Ht H. rewrite srliw_val in H by lia. rewrite (Wu t) in H by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned a0) (2 ^ 32) ltac:(lia)) as Hd.
  assert (Hd8 : 0 <= bv_unsigned a0 mod 2 ^ 32 / 2 ^ 3 < 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Wu in H by lia.
  pose proof (Z.mul_div_le (bv_unsigned a0 mod 2 ^ 32) (2 ^ 3) ltac:(lia)). change (2 ^ 3) with 8 in *. lia.
Qed.

Lemma adapt_stop : forall (a0 : word) t, 0 <= t < 2 ^ 29 ->
  bv_unsigned (v_srliw a0 3) <= bv_unsigned (W t) -> bv_unsigned a0 mod 2 ^ 32 < 8 * (t + 1).
Proof.
  intros a0 t Ht H. rewrite srliw_val in H by lia. rewrite (Wu t) in H by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned a0) (2 ^ 32) ltac:(lia)) as Hd.
  assert (Hd8 : 0 <= bv_unsigned a0 mod 2 ^ 32 / 2 ^ 3 < 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Wu in H by lia.
  pose proof (Z.div_mod (bv_unsigned a0 mod 2 ^ 32) (2 ^ 3) ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 mod 2 ^ 32) (2 ^ 3) ltac:(lia)). change (2 ^ 3) with 8 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma bias_val : forall c df, 0 <= c <= 7 -> 0 <= df <= 498 ->
  exists bv, 0 <= bv <= 300 /\
    v_addw (W (36 * c)) (v_divuw (v_and (v_mul (W df) (W 36)) (W 65535)) (v_and (W (df + 38)) (W 65535))) = W bv.
Proof.
  intros c df Hc Hdf. rewrite mul_W. rewrite !and_W by lia.
  change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia. change (2 ^ 16) with 65536.
  rewrite !Z.mod_small by lia.
  unfold v_divuw. rewrite !Wu by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite !Z.mod_small by lia.
  destruct (Z.eqb_spec (df + 38) 0) as [E|_]; [lia|].
  assert (Hq : 0 <= df * 36 / (df + 38) <= 36).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  rewrite swrap32_small by lia.
  exists (36 * c + df * 36 / (df + 38)). split; [lia|].
  unfold v_addw. rewrite !Wu by lia. rewrite swrap32_small by lia. reflexivity.
Qed.
