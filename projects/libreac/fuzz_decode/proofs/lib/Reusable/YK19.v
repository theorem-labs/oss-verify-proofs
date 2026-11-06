(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK19.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/YK19.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1a YK0s YK1h YK1b YK1d YK0u.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Lemma getr_empty : forall r : reg, getr bvmap_empty r = Z_to_bv 64 0.
Proof.
intro r. unfold getr. destruct (bv_eqb r 0); [reflexivity|].
unfold reg_get, bvmap_get, bvmap_empty.
destruct (bv_key r); cbn [tget]; apply bv_eq; reflexivity.
Qed.
Local Open Scope Z_scope.
Lemma land_align_mask : forall a k, 0 <= a < 2^64 -> 0 <= k <= 64 -> a mod 2^k = 0 ->
Z.land a (2^64 - 2^k) = a.
Proof.
intros a k Ha Hk Hmod.
replace (2^64 - 2^k) with (Z.ldiff (Z.ones 64) (Z.ones k)).
2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod a (2^k) ltac:(lia)). lia.
Qed.
Lemma v_andi_m16_aligned : forall x : word,
bv_unsigned x mod 16 = 0 -> v_andi x (-16) = x.
Proof.
intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 (-16)) with (2^64 - 2^4).
pose proof (u64_range x).
rewrite land_align_mask by (first [lia | exact Hm]).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.
Lemma v_andi_m8_aligned : forall x : word,
bv_unsigned x mod 8 = 0 -> v_andi x (-8) = x.
Proof.
intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 (-8)) with (2^64 - 2^3).
pose proof (u64_range x).
rewrite land_align_mask by (first [lia | exact Hm]).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.
Lemma land_low_zero : forall a k, 0 <= a -> 0 <= k -> a mod 2^k = 0 -> Z.land a (Z.ones k) = 0.
Proof. intros a k Ha Hk Hm. rewrite Z.land_ones by lia. exact Hm. Qed.
Lemma v_andi_3_aligned : forall x : word,
bv_unsigned x mod 4 = 0 -> v_andi x 3 = Z_to_bv 64 0.
Proof.
intros x Hm. unfold v_andi. f_equal.
change (bv_wrap 64 3) with (Z.ones 2). apply land_low_zero; [apply u64_range | lia | exact Hm].
Qed.
Lemma land_4_aligned8 : forall a, 0 <= a -> a mod 8 = 0 -> Z.land a 4 = 0.
Proof.
intros a Ha Hm.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
change 4 with (2^2). rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec 2 i); [|apply andb_false_r].
subst i.
replace a with ((a / 8) * 2^3) by lia.
rewrite Z.mul_pow2_bits by lia. change (2 - 3) with (-1).
rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.
Lemma v_andi_4_aligned8 : forall x : word,
bv_unsigned x mod 8 = 0 -> v_andi x 4 = Z_to_bv 64 0.
Proof.
intros x Hm. unfold v_andi. f_equal.
change (bv_wrap 64 4) with 4. apply land_4_aligned8; [apply u64_range | exact Hm].
Qed.
Lemma v_andi_1_of01 : forall z, (z = 0 \/ z = 1) ->
v_andi (Z_to_bv 64 z) 1 = Z_to_bv 64 z.
Proof.
intros z [-> | ->]; apply bv_eq; reflexivity.
Qed.
Lemma mod4_mod_pow2 : forall t k, 2 <= k -> (t mod 2^k) mod 4 = t mod 4.
Proof.
intros t k Hk. apply Z.mod_mod_divide.
exists (2^(k-2)). change 4 with (2^2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma negw_and3_aligned : forall x : word,
bv_unsigned x mod 4 = 0 -> v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 0.
Proof.
intros x Hm. unfold v_andi, v_subw. f_equal.
change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
unfold bv_swrap. rewrite bv_wrap64_mod.
change (bv_half_modulus 32) with (2^31).
unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2^2) with 4.
rewrite mod4_mod_pow2 by lia.
rewrite <- Zminus_mod_idemp_l.
rewrite mod4_mod_pow2 by lia.
replace ((0 - bv_unsigned x + 2^31) mod 4) with 0.
2:{ replace (0 - bv_unsigned x + 2^31) with (2^31 - bv_unsigned x) by lia.
rewrite <- Zminus_mod_idemp_r, Hm. reflexivity. }
reflexivity.
Qed.
Lemma firstn_Z_to_le_bytes : forall k n z, (k <= n)%nat ->
firstn k (Z_to_le_bytes n z) = Z_to_le_bytes k z.
Proof.
induction k as [|k IH]; intros n z Hk; [reflexivity|].
destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.
Lemma firstn_word_to_le_bytes : forall k n (v : word), (k <= n)%nat ->
firstn k (word_to_le_bytes n v) = word_to_le_bytes k v.
Proof. intros. unfold word_to_le_bytes. apply firstn_Z_to_le_bytes. assumption. Qed.
Lemma rdn_low_bytes : forall segs m (a v : word) k, (k <= 8)%nat ->
rdn segs m a 8 = Some (word_to_le_bytes 8 v) ->
rdn segs m a k = Some (word_to_le_bytes k v).
Proof.
intros segs m a v k Hk H.
rewrite (rdn_firstn segs m 8 a _ k H Hk). f_equal. apply firstn_word_to_le_bytes. exact Hk.
Qed.
Lemma bytes_le_to_Z_4_small : forall v : word, bv_unsigned v < 2^32 ->
bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
apply Z.mod_small. pose proof (u64_range v). lia.
Qed.
Lemma v_lw_small : forall v : word, bv_unsigned v < 2^31 -> v_lw v = v.
Proof.
intros v Hv. unfold v_lw. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (u64_range v).
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.
Lemma v_add_lit_r : forall (x : word) (k : Z), 0 <= k < 2^64 ->
v_add x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. reflexivity. Qed.
Lemma v_add_lit_l : forall (x : word) (k : Z), 0 <= k < 2^64 ->
v_add (Z_to_bv 64 k) x = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. f_equal. lia. Qed.
Lemma v_slli_lit : forall z sh, 0 <= z -> 0 <= sh -> z * 2^sh < 2^64 ->
v_slli (Z_to_bv 64 z) sh = Z_to_bv 64 (z * 2^sh).
Proof.
intros z sh Hz Hsh Hb. unfold v_slli. f_equal.
rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by nia. reflexivity.
Qed.
Lemma in_sub_bv : forall (l1 l2 : list reg) (r : reg),
forallb (fun x => existsb (fun y => bv_eqb x y) l2) l1 = true -> In r l1 -> In r l2.
Proof.
induction l1 as [|x l1 IH]; intros l2 r H Hin; [contradiction|].
cbn [forallb] in H. apply andb_true_iff in H as [Hx Hl1].
destruct Hin as [<-|Hin]; [|apply IH; assumption].
clear IH Hl1. induction l2 as [|y l2 IH2]; [discriminate|].
cbn [existsb] in Hx. apply orb_true_iff in Hx as [Hxy|Hx].
- left. symmetry. apply bv_eq. unfold bv_eqb in Hxy. apply Z.eqb_eq in Hxy. exact Hxy.
- right. apply IH2. exact Hx.
Qed.
Lemma Z_to_bv_u_eq : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma Z_to_bv_u_eq_sym : forall (a : word) (z : Z), z = bv_unsigned a -> a = Z_to_bv 64 z.
Proof. intros a z H. symmetry. apply Z_to_bv_u_eq. exact H. Qed.
