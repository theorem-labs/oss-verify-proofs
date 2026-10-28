(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzWalkArith BzWalkArith2 BzWalkArith3.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Lemma land_le_r' : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Hb. rewrite Z.land_comm. pose proof (Z.sub_land_same_l b a) as H.
  assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia). lia.
Qed.
Lemma land_lit_range : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= b.
Proof. intros a b Ha Hb. split; [apply Z.land_nonneg; lia| apply land_le_r'; lia]. Qed.
(* [comment removed for export] *)
Lemma land_ones64_r : forall x, 0 <= x -> Z.land x 18446744073709551615 = x mod 18446744073709551616.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lo8_mod : forall x, 0 <= x -> lo8 x = x mod 256.
Proof. intros x Hx. unfold lo8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_o4_4 : forall o, 0 <= o -> Z.land (o * 4) 4 = 4 * (o mod 2).
Proof.
  intros o Ho. replace (o * 4) with (Z.shiftl o 2) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  change 4 with (Z.shiftl 1 2) at 1.
  rewrite <- Z.shiftl_land. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 2) with 4. lia.
Qed.
Lemma land_shl2_4 : forall o, 0 <= o -> Z.land (Z.shiftl o 2) 4 = 4 * (o mod 2).
Proof. intros o Ho. rewrite Z.shiftl_mul_pow2 by lia. apply land_o4_4. lia. Qed.

Lemma shiftr_range : forall b s, 0 <= b -> 0 <= s -> 0 <= Z.shiftr b s <= b.
Proof.
  intros b s Hb Hs. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs).
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma srlw_nib : forall b o, 0 <= b < 256 -> 0 <= o ->
  bv_swrap 32 (Z.shiftr b (Z.land (o * 4) 4 mod 32)) = Z.shiftr b (4 * (o mod 2)).
Proof.
  intros b o Hb Ho. rewrite land_o4_4 by lia.
  rewrite (Z.mod_small (4 * (o mod 2)) 32) by lia.
  pose proof (shiftr_range b (4 * (o mod 2)) ltac:(lia) ltac:(lia)).
  apply swrap32_id. lia.
Qed.

(* [comment removed for export] *)
Lemma shl60_shr44 : forall x, 0 <= x < 4294967296 ->
  Z.land (Z.land x 18446744073709551615 * 1152921504606846976) 18446744073709551615 / 17592186044416 = Z.land x 15 * 65536.
Proof.
  intros x Hx. rewrite (land_ones64_r x) by lia. rewrite (Z.mod_small x 18446744073709551616) by lia.
  rewrite land_ones64_r by lia. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
  rewrite (Z.div_mod x 16) at 1 by lia. rewrite Z.mul_add_distr_r.
  replace (16 * (x / 16) * 1152921504606846976) with (x / 16 * 18446744073709551616) by lia.
  rewrite Z.add_comm, Z_mod_plus_full.
  pose proof (Z.mod_pos_bound x 16 ltac:(lia)).
  rewrite Z.mod_small by lia.
  replace (x mod 16 * 1152921504606846976) with (x mod 16 * 65536 * 17592186044416) by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma get_ll_asm : forall fa fb o, 0 <= o -> 0 <= fb (o / 2) < 256 -> 0 <= fa o ->
  Z.lor (Z.land (Z.land (bv_swrap 32 (Z.shiftr (fb (o / 2)) (Z.land (o * 4) 4 mod 32))) 18446744073709551615 * 1152921504606846976)
           18446744073709551615 / 17592186044416) (fa o)
  = get_ll fa fb o.
Proof.
  intros fa fb o Ho Hb Ha. rewrite srlw_nib by lia.
  pose proof (shiftr_range (fb (o / 2)) (4 * (o mod 2)) ltac:(lia) ltac:(lia)).
  rewrite shl60_shr44 by lia.
  unfold get_ll, get_ll4. rewrite land_shl2_4 by lia. rewrite (Z.shiftr_div_pow2 o 1) by lia. change (2 ^ 1) with 2.
  rewrite (Z.shiftl_mul_pow2 _ 16) by lia. change (2 ^ 16) with 65536. apply Z.lor_comm.
Qed.

(* [comment removed for export] *)
Lemma zx16_small : forall x, 0 <= x < 65536 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma get_ll_range : forall fa fb o, 0 <= fa o < 65536 -> 0 <= fb (Z.shiftr o 1) -> 0 <= get_ll fa fb o < 1048576.
Proof.
  intros fa fb o Ha Hb. unfold get_ll, get_ll4.
  set (t := Z.shiftr (fb (Z.shiftr o 1)) (Z.land (Z.shiftl o 2) 4)).
  assert (0 <= t) by (subst t; apply Z.shiftr_nonneg; lia).
  pose proof (land_lit_range t 15 ltac:(lia) ltac:(lia)).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  apply (lor_lt_pow2 _ _ 20); lia.
Qed.

(* [comment removed for export] *)
Lemma set_ll4_even : forall fb i n, 0 <= i -> 0 <= n -> Z.land i 1 = 0 ->
  set_ll4 fb i n = zfupd fb (i / 2) (Z.lor (Z.land (fb (i / 2)) 240) n).
Proof.
  intros fb i n Hi Hn E. unfold set_ll4. rewrite E. cbn [Z.eqb]. rewrite (Z.shiftr_div_pow2 i 1) by lia. reflexivity.
Qed.
Lemma set_ll4_odd : forall fb i n, 0 <= i -> 0 <= n -> Z.land i 1 <> 0 ->
  set_ll4 fb i n = zfupd fb (i / 2) (Z.lor (Z.land (fb (i / 2)) 15) (n * 16)).
Proof.
  intros fb i n Hi Hn E. unfold set_ll4. destruct (Z.eqb_spec (Z.land i 1) 0); [lia|].
  rewrite (Z.shiftr_div_pow2 i 1), (Z.shiftl_mul_pow2 n 4) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_m16_byte : forall b, 0 <= b < 256 -> Z.land b 18446744073709551600 = Z.land b 240.
Proof.
  intros b Hb. rewrite <- (Z.mod_small b 256) by lia. change 256 with (2 ^ 8).
  rewrite <- Z.land_ones by lia. rewrite <- !Z.land_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swrap32_land64_add : forall a b, - 2147483648 <= a + b < 2147483648 ->
  bv_swrap 32 (Z.land a 18446744073709551615 + b) = a + b.
Proof.
  intros a b H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite (Z.mod_eq a (2 ^ 64)) by lia.
  replace (a - 2 ^ 64 * (a / 2 ^ 64) + b + 2147483648) with ((a + b + 2147483648) + (- (a / 2 ^ 64) * 4294967296) * 4294967296) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

End ACeilS1.
