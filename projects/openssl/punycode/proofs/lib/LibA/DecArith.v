(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma shl32_mod : forall a, (a * 2 ^ 32) mod 2 ^ 64 = (a mod 2 ^ 32) * 2 ^ 32.
Proof. intros a. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). apply Z.mul_mod_distr_r; lia. Qed.

(* [comment removed for export] *)
Lemma zext32_shifts : forall x : word, v_srli (v_slli x 32) 32 = W (bv_unsigned x mod 2 ^ 32).
Proof.
  intros x. unfold v_srli, v_slli. rewrite Wu_mod, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite shl32_mod, Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma scale4_shifts : forall x : word, v_srli (v_slli x 32) 30 = W (4 * (bv_unsigned x mod 2 ^ 32)).
Proof.
  intros x. unfold v_srli, v_slli. rewrite Wu_mod, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite shl32_mod. f_equal.
  replace (bv_unsigned x mod 2 ^ 32 * 2 ^ 32) with (4 * (bv_unsigned x mod 2 ^ 32) * 2 ^ 30) by (change (2 ^ 32) with (4 * 2 ^ 30); lia).
  apply Z.div_mul. lia.
Qed.

Lemma swrap32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod. f_equal. lia.
Qed.

Lemma swrap32_of_small : forall z r, z mod 2 ^ 32 = r -> 0 <= r < 2 ^ 31 -> bv_swrap 32 z = r.
Proof.
  intros z r Hz Hr. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  assert (E : (z + 2 ^ 31) mod 2 ^ 32 = r + 2 ^ 31).
  { rewrite Zplus_mod, Hz. rewrite (Z.mod_small (2 ^ 31)) by lia. apply Z.mod_small. lia. }
  lia.
Qed.

Lemma mod32_of_mod64 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. pose proof (Z.div_mod z (2 ^ 64) ltac:(lia)) as E.
  rewrite E at 2. replace (2 ^ 64 * (z / 2 ^ 64) + z mod 2 ^ 64) with (z mod 2 ^ 64 + (2 ^ 32 * (z / 2 ^ 64)) * 2 ^ 32) by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); lia).
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rem_idx : forall (a2 : word) m, 1 <= m < 2 ^ 31 ->
  exists r, 0 <= r < m /\ v_subw a2 (v_mul (v_divuw a2 (W m)) (W m)) = W r.
Proof.
  intros a2 m Hm. set (x := bv_unsigned a2 mod 2 ^ 32).
  assert (Hx : 0 <= x < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.mod_pos_bound x m ltac:(lia)) as Hr.
  exists (x mod m). split; [exact Hr|].
  unfold v_divuw. rewrite Wu by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_small m) by lia. fold x.
  destruct (Z.eqb_spec m 0) as [E|_]; [lia|].
  unfold v_subw, v_mul. f_equal. apply swrap32_of_small; [|lia].
  rewrite !Wu_mod. rewrite (Z.mod_small m (2 ^ 64)) by lia.
  set (sq := bv_swrap 32 (x / m)).
  assert (Hq : 0 <= x / m < 2 ^ 32).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; nia. }
  assert (E1 : ((sq mod 2 ^ 64 * m) mod 2 ^ 64) mod 2 ^ 32 = (x / m * m) mod 2 ^ 32).
  { rewrite mod32_of_mod64. rewrite Zmult_mod, mod32_of_mod64. unfold sq. rewrite swrap32_mod.
    rewrite <- Zmult_mod. reflexivity. }
  rewrite Zminus_mod, E1, <- Zminus_mod. rewrite <- Zminus_mod_idemp_l. fold x.
  replace (x - x / m * m) with (x mod m) by (rewrite (Z.mod_eq x m) by lia; lia).
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma srliw_val : forall (x : word) k, 1 <= k < 32 ->
  v_srliw x k = W ((bv_unsigned x mod 2 ^ 32) / 2 ^ k).
Proof.
  intros x k Hk. unfold v_srliw. f_equal. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned x) (2 ^ 32) ltac:(lia)) as Hx.
  assert (Hp : 2 <= 2 ^ k) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
  assert (Hd : 0 <= bv_unsigned x mod 2 ^ 32 / 2 ^ k < 2 ^ 31).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  apply swrap32_small. lia.
Qed.

Lemma subw_mod32 : forall x y : word,
  bv_unsigned (v_subw x y) mod 2 ^ 32 = (bv_unsigned x - bv_unsigned y) mod 2 ^ 32.
Proof. intros x y. unfold v_subw. rewrite Wu_mod, mod32_of_mod64, swrap32_mod. reflexivity. Qed.

(* [comment removed for export] *)
Lemma adapt_decrease : forall (a0 s9 t6 : word),
  bv_unsigned t6 < bv_unsigned (v_srliw a0 3) ->
  bv_unsigned (v_srliw (v_add (v_srliw (v_subw a0 (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 1)
                              (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 5) mod 2 ^ 32
  < bv_unsigned a0 mod 2 ^ 32.
Proof.
  intros a0 s9 t6 Hc. set (dl := bv_unsigned a0 mod 2 ^ 32).
  assert (Hdl : 0 <= dl < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  pose proof (u64_range s9) as HS. pose proof (u64_range t6) as HT.
  (* [comment removed for export] *)
  rewrite srliw_val in Hc by lia. fold dl in Hc.
  assert (Hd8 : 0 <= dl / 2 ^ 3 < 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Wu in Hc by lia.
  assert (H8 : 8 <= dl).
  { destruct (Z_lt_le_dec dl 8); [|assumption]. rewrite Z.div_small in Hc by (change (2 ^ 3) with 8; lia). lia. }
  (* [comment removed for export] *)
  set (hi := v_srli (v_mulhu (v_slli a0 32) s9) 32).
  assert (Hhi : exists hv, 0 <= hv < dl /\ hi = W hv).
  { assert (E1 : bv_unsigned (v_slli a0 32) = dl * 2 ^ 32).
    { unfold v_slli. rewrite Wu_mod, Z.shiftl_mul_pow2 by lia. apply shl32_mod. }
    unfold hi, v_srli, v_mulhu. rewrite E1.
    rewrite !Z.shiftr_div_pow2 by lia.
    assert (Hh1 : 0 <= dl * 2 ^ 32 * bv_unsigned s9 / 2 ^ 64 < dl * 2 ^ 32).
    { split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
    rewrite Wu by lia.
    exists (dl * 2 ^ 32 * bv_unsigned s9 / 2 ^ 64 / 2 ^ 32). split; [|reflexivity].
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  destruct Hhi as (hv & Hhv & ->).
  (* [comment removed for export] *)
  rewrite (srliw_val (v_subw a0 (W hv))) by lia. rewrite subw_mod32. rewrite (Wu hv) by lia.
  rewrite <- Zminus_mod_idemp_l. fold dl. rewrite (Z.mod_small (dl - hv)) by lia.
  assert (Ha5 : 0 <= (dl - hv) / 2 ^ 1 <= dl - hv) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite add_W. rewrite srliw_val by lia.
  rewrite (Wu ((dl - hv) / 2 ^ 1 + hv)) by lia. rewrite (Z.mod_small ((dl - hv) / 2 ^ 1 + hv)) by lia.
  assert (Hs : 0 <= ((dl - hv) / 2 ^ 1 + hv) / 2 ^ 5 < dl).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite Wu by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma subw_W : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> - 2 ^ 31 <= a - b < 2 ^ 31 ->
  v_subw (W a) (W b) = W (a - b).
Proof. intros a b Ha Hb H. unfold v_subw. rewrite !Wu by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma scale4_W : forall r, 0 <= r < 2 ^ 32 -> v_srli (v_slli (W r) 32) 30 = W (4 * r).
Proof. intros r Hr. rewrite scale4_shifts. rewrite Wu by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma zext32_W : forall r, 0 <= r < 2 ^ 32 -> v_srli (v_slli (W r) 32) 32 = W r.
Proof. intros r Hr. rewrite zext32_shifts. rewrite Wu by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
