(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK14 YK1a.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Module HZ.
Local Open Scope Z_scope.
Definition zb (x : Z) (i : nat) : Z := (x / 2^(8 * Z.of_nat i)) mod 256.
Fixpoint zdig (ds : list Z) : Z :=
match ds with [] => 0 | d :: r => d + 256 * zdig r end.
Lemma pow2_8i_pos : forall i : nat, 0 < 2^(8 * Z.of_nat i).
Proof. intro i. apply Z.pow_pos_nonneg; lia. Qed.
Lemma zb_bound : forall x i, 0 <= zb x i < 256.
Proof. intros. unfold zb. apply Z.mod_pos_bound. lia. Qed.
Lemma zb_0 : forall i, zb 0 i = 0.
Proof. intro i. unfold zb. rewrite Zdiv_0_l. reflexivity. Qed.
Lemma land_land_m : forall a b m, Z.land (Z.land a b) m = Z.land (Z.land a m) (Z.land b m).
Proof.
intros. apply Z.bits_inj'. intros n Hn.
rewrite !Z.land_spec.
destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.
Lemma land_lxor_m : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof.
intros. apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.
Lemma lxor_lt64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
0 <= Z.lxor a b < 2^64.
Proof.
intros a b Ha Hb.
assert (Hn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
split; [lia|].
assert (E : Z.lxor a b mod 2^64 = Z.lxor a b).
{ rewrite <- Z.land_ones by lia. rewrite land_lxor_m.
rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.
Lemma zb_alt : forall x i, zb x i = Z.land (Z.shiftr x (8 * Z.of_nat i)) 255.
Proof.
intros x i. unfold zb.
rewrite Z.shiftr_div_pow2 by lia.
change 255 with (Z.ones 8).
rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma zb_land : forall u w i, zb (Z.land u w) i = Z.land (zb u i) (zb w i).
Proof.
intros u w i. rewrite !zb_alt.
rewrite Z.shiftr_land, land_land_m. reflexivity.
Qed.
Lemma zb_lxor : forall u w i, zb (Z.lxor u w) i = Z.lxor (zb u i) (zb w i).
Proof.
intros u w i. rewrite !zb_alt.
rewrite Z.shiftr_lxor, land_lxor_m. reflexivity.
Qed.
Lemma zdig_nonneg : forall ds, Forall (fun d => 0 <= d < 256) ds -> 0 <= zdig ds.
Proof.
induction ds as [|d ds IH]; intro H; cbn [zdig]; [lia|].
apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
specialize (IH Hds). lia.
Qed.
Lemma zdig_lt : forall ds, Forall (fun d => 0 <= d < 256) ds ->
zdig ds < 2^(8 * Z.of_nat (length ds)).
Proof.
induction ds as [|d ds IH]; intro H; cbn [zdig length].
- cbn. lia.
- apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
specialize (IH Hds).
replace (8 * Z.of_nat (S (length ds))) with (8 + 8 * Z.of_nat (length ds)) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.
Lemma zb_zdig : forall ds, Forall (fun d => 0 <= d < 256) ds ->
forall i, (i < length ds)%nat -> zb (zdig ds) i = nth i ds 0.
Proof.
induction ds as [|d ds IH]; intros H i Hi; [cbn in Hi; lia|].
apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
pose proof (zdig_nonneg ds Hds) as Hnn.
destruct i as [|i]; cbn [nth].
- cbn [zdig]. unfold zb.
change (8 * Z.of_nat 0) with 0. change (2^0) with 1.
rewrite Z.div_1_r.
replace (d + 256 * zdig ds) with (d + zdig ds * 256) by lia.
rewrite Z.mod_add by lia.
apply Z.mod_small. lia.
- cbn [length] in Hi.
rewrite <- (IH Hds i ltac:(lia)).
cbn [zdig]. unfold zb.
replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256.
rewrite <- Z.div_div by (try lia; apply pow2_8i_pos).
replace ((d + 256 * zdig ds) / 256) with (zdig ds); [reflexivity|].
replace (d + 256 * zdig ds) with (zdig ds * 256 + d) by lia.
rewrite Z.div_add_l by lia.
rewrite (Z.div_small d 256) by lia. lia.
Qed.
Lemma zdig_recon8 : forall x, 0 <= x < 2^64 ->
x = zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7].
Proof.
intros x Hx. cbn [zdig]. unfold zb.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40.
change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56.
change (2^0) with 1. rewrite Z.div_1_r.
change (2^8) with 256.
change (2^16) with (256*256).
change (2^24) with (256*256*256).
change (2^32) with (256*256*256*256).
change (2^40) with (256*256*256*256*256).
change (2^48) with (256*256*256*256*256*256).
change (2^56) with (256*256*256*256*256*256*256).
rewrite <- !Z.div_div by lia.
pose proof (Z.div_mod x 256 ltac:(lia)).
pose proof (Z.div_mod (x/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256/256/256) 256 ltac:(lia)).
assert (Htop : x/256/256/256/256/256/256/256/256 = 0).
{ rewrite !Z.div_div by lia. apply Z.div_small. lia. }
lia.
Qed.
Lemma zb_eq0 : forall x, 0 <= x < 2^64 ->
(forall i, (i < 8)%nat -> zb x i = 0) -> x = 0.
Proof.
intros x Hx H. rewrite (zdig_recon8 x Hx).
rewrite !H by lia. cbn [zdig]. lia.
Qed.
Lemma zb_neq0 : forall x i, zb x i <> 0 -> x <> 0.
Proof. intros x i H Hc. subst. rewrite zb_0 in H. lia. Qed.
Lemma zb_split : forall lo hi i,
0 <= lo < 2^(8 * Z.of_nat i) -> 0 <= hi ->
zb (lo + 2^(8 * Z.of_nat i) * hi) i = hi mod 256.
Proof.
intros lo hi i Hlo Hhi. unfold zb.
rewrite Z.mul_comm, Z.div_add by (pose proof (pow2_8i_pos i); lia).
rewrite (Z.div_small lo) by lia. reflexivity.
Qed.
Lemma zb_mod64 : forall y i, (i < 8)%nat -> 0 <= y < 2^65 ->
zb (y mod 2^64) i = zb y i.
Proof.
intros y i Hi Hy.
destruct (Z_lt_le_dec y (2^64)) as [Hlt|Hge].
- rewrite Z.mod_small by lia. reflexivity.
- assert (Hm : y mod 2^64 = y - 2^64).
{ replace y with ((y - 2^64) + 1 * 2^64) at 1 by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite Hm. unfold zb.
pose proof (pow2_8i_pos i) as Hk.
assert (Hd : 2^64 = 2^(64 - 8 * Z.of_nat i) * 2^(8 * Z.of_nat i)).
{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (Hdiv : (256 | 2^(64 - 8 * Z.of_nat i))).
{ replace (64 - 8 * Z.of_nat i) with (8 + (56 - 8 * Z.of_nat i)) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256.
apply Z.divide_factor_l. }
destruct Hdiv as [q Hq].
replace (y - 2^64) with (y + (- (q * 256)) * 2^(8 * Z.of_nat i))
by (rewrite Hd, Hq; lia).
rewrite Z.div_add by lia.
replace (y / 2 ^ (8 * Z.of_nat i) + - (q * 256))
with (y / 2 ^ (8 * Z.of_nat i) + (- q) * 256) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Definition ONESNEG : Z := 18374403900871474943.
Definition HIGHS   : Z := 9259542123273814144.
Definition ALLONES : Z := 18446744073709551615.
Definition Tz (x : Z) : Z :=
Z.land (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS.
Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
intros a b Hb.
rewrite Z.land_comm.
pose proof (Z.sub_land_same_l b a) as H.
assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia).
lia.
Qed.
Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof. intros a b Ha. rewrite Z.land_comm. apply land_le_r. exact Ha. Qed.
Lemma Tz_range : forall x, 0 <= Tz x < 2^64.
Proof.
intro x. unfold Tz. split.
- apply Z.land_nonneg. right. unfold HIGHS. lia.
- pose proof (land_le_r (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS
ltac:(unfold HIGHS; lia)). unfold HIGHS in *. lia.
Qed.
Ltac by8 i := destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; vm_compute; reflexivity.
Lemma zb_ALLONES : forall i, (i < 8)%nat -> zb ALLONES i = 255.
Proof. intros i Hi. by8 i. Qed.
Lemma zb_HIGHS : forall i, (i < 8)%nat -> zb HIGHS i = 128.
Proof. intros i Hi. by8 i. Qed.
Lemma Tz_byte : forall x i, (i < 8)%nat ->
zb (Tz x) i
= Z.land (Z.land (zb ((x + ONESNEG) mod 2^64) i) (Z.lxor (zb x i) 255)) 128.
Proof.
intros x i Hi. unfold Tz.
rewrite !zb_land, zb_lxor, zb_ALLONES by exact Hi.
rewrite zb_HIGHS by exact Hi. reflexivity.
Qed.
Lemma byte_nozero : forall c, 1 <= c <= 255 ->
Z.land (Z.land (c - 1) (Z.lxor c 255)) 128 = 0.
Proof.
intros c Hc.
assert (Hin : In (Z.to_nat c) (seq 1 255)) by (apply in_seq; lia).
assert (Hall : forallb (fun n =>
Z.eqb (Z.land (Z.land (Z.of_nat n - 1) (Z.lxor (Z.of_nat n) 255)) 128) 0)
(seq 1 255) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall _ Hin).
apply Z.eqb_eq in Hall.
replace (Z.of_nat (Z.to_nat c)) with c in Hall by lia. exact Hall.
Qed.
Lemma Tz_nozero : forall x, 0 <= x < 2^64 ->
(forall i, (i < 8)%nat -> zb x i <> 0) -> Tz x = 0.
Proof.
intros x Hx Hnz.
pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
pose proof (zb_bound x 6). pose proof (zb_bound x 7).
pose proof (Hnz 0%nat ltac:(lia)). pose proof (Hnz 1%nat ltac:(lia)).
pose proof (Hnz 2%nat ltac:(lia)). pose proof (Hnz 3%nat ltac:(lia)).
pose proof (Hnz 4%nat ltac:(lia)). pose proof (Hnz 5%nat ltac:(lia)).
pose proof (Hnz 6%nat ltac:(lia)). pose proof (Hnz 7%nat ltac:(lia)).
pose proof (zdig_recon8 x Hx) as Hrec.
set (ds' := [zb x 0 - 1; zb x 1 - 1; zb x 2 - 1; zb x 3 - 1;
zb x 4 - 1; zb x 5 - 1; zb x 6 - 1; zb x 7 - 1]).
assert (Hds' : Forall (fun d => 0 <= d < 256) ds').
{ unfold ds'. repeat constructor; lia. }
assert (Hlt' : 0 <= zdig ds' < 2^64).
{ split; [apply zdig_nonneg; exact Hds'|].
pose proof (zdig_lt ds' Hds') as H'. unfold ds' in H' |- *.
cbn [length] in H'. exact H'. }
assert (Hy : (x + ONESNEG) mod 2^64 = zdig ds').
{ rewrite Hrec at 1.
replace (zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7]
+ ONESNEG)
with (zdig ds' + 1 * 2^64)
by (unfold ds', ONESNEG; cbn [zdig]; lia).
rewrite Z.mod_add by lia. apply Z.mod_small. exact Hlt'. }
apply zb_eq0; [apply Tz_range|].
intros i Hi. rewrite Tz_byte by exact Hi. rewrite Hy.
rewrite (zb_zdig ds' Hds' i) by (unfold ds'; cbn [length]; lia).
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia;
unfold ds'; cbn [nth]; apply byte_nozero; lia.
Qed.
Lemma zb_split_255 : forall v lo Q i p,
p = 2^(8 * Z.of_nat i) -> v = lo + p * (255 + 256 * Q) ->
0 <= lo < p -> 0 <= Q -> zb v i = 255.
Proof.
intros v lo Q i p Hp Hv Hlo HQ. subst p v.
rewrite zb_split by (try lia; assumption).
replace (255 + 256 * Q) with (255 + Q * 256) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma sum_byte_255 : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
(forall j, (j < i)%nat -> zb x j <> 0) ->
zb (x + ONESNEG) i = 255.
Proof.
intros x i Hx Hi Hz Hlow.
pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
pose proof (zb_bound x 6). pose proof (zb_bound x 7).
pose proof (zdig_recon8 x Hx) as Hrec. cbn [zdig] in Hrec.
unfold ONESNEG.
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
-
apply (zb_split_255 _ (0) (zb x 1 * 1 + zb x 2 * 256 + zb x 3 * 65536 + zb x 4 * 16777216 + zb x 5 * 4294967296 + zb x 6 * 1099511627776 + zb x 7 * 281474976710656 + 71775015237779198) 0%nat 1);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1) (zb x 2 * 1 + zb x 3 * 256 + zb x 4 * 65536 + zb x 5 * 16777216 + zb x 6 * 4294967296 + zb x 7 * 1099511627776 + 280371153272574) 1%nat 256);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256) (zb x 3 * 1 + zb x 4 * 256 + zb x 5 * 65536 + zb x 6 * 16777216 + zb x 7 * 4294967296 + 1095199817470) 2%nat 65536);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536) (zb x 4 * 1 + zb x 5 * 256 + zb x 6 * 65536 + zb x 7 * 16777216 + 4278124286) 3%nat 16777216);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216) (zb x 5 * 1 + zb x 6 * 256 + zb x 7 * 65536 + 16711422) 4%nat 4294967296);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296) (zb x 6 * 1 + zb x 7 * 256 + 65278) 5%nat 1099511627776);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
pose proof (Hlow 5%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776) (zb x 7 * 1 + 254) 6%nat 281474976710656);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
pose proof (Hlow 5%nat ltac:(lia)).
pose proof (Hlow 6%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776 + (zb x 6 - 1) * 281474976710656) (0) 7%nat 72057594037927936);
[ vm_compute; reflexivity | lia | lia | lia ].
Qed.
Lemma Tz_haszero : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
(forall j, (j < i)%nat -> zb x j <> 0) -> Tz x <> 0.
Proof.
intros x i Hx Hi Hz Hlow.
apply (zb_neq0 _ i).
rewrite Tz_byte by exact Hi.
rewrite zb_mod64 by (first [exact Hi | unfold ONESNEG; lia]).
rewrite (sum_byte_255 x i Hx Hi Hz Hlow), Hz.
vm_compute. discriminate.
Qed.
End HZ.
Lemma u8_zero : bv_unsigned (Z_to_bv 8 0) = 0%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma lor_shiftl8 : forall a y : Z, (0 <= a < 256)%Z -> (0 <= y)%Z ->
Z.lor a (Z.shiftl y 8) = (a + 256 * y)%Z.
Proof.
intros a y Ha Hy.
assert (Hs : Z.shiftl y 8 = (y * 2^8)%Z) by (apply Z.shiftl_mul_pow2; lia).
assert (Hland : Z.land a (Z.shiftl y 8) = 0%Z).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb n 8) eqn:E.
- apply Z.ltb_lt in E.
rewrite Hs, Z.mul_pow2_bits_low by lia. apply andb_false_r.
- apply Z.ltb_ge in E.
replace (Z.testbit a n) with false; [reflexivity|].
symmetry. apply Z.testbit_false; [lia|].
rewrite Z.div_small; [reflexivity|].
split; [lia|]. eapply Z.lt_le_trans; [apply Ha|].
change 256%Z with (2^8)%Z. apply Z.pow_le_mono_r; lia. }
rewrite <- Z.lxor_lor by exact Hland.
rewrite <- Z.add_nocarry_lxor by exact Hland.
rewrite Hs. lia.
Qed.
Lemma bytes_le_to_Z_zdig : forall bs : list byte,
bytes_le_to_Z bs = HZ.zdig (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [bytes_le_to_Z map HZ.zdig]. rewrite IH.
apply lor_shiftl8; [apply u8_range|].
apply HZ.zdig_nonneg. apply Forall_map, Forall_forall.
intros x _. apply u8_range.
Qed.
Lemma zb_of_bytes : forall (bs : list byte) i, (i < length bs)%nat ->
HZ.zb (bytes_le_to_Z bs) i = bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof.
intros bs i Hi. rewrite bytes_le_to_Z_zdig.
rewrite HZ.zb_zdig
by (first [ apply Forall_map, Forall_forall; intros x _; apply u8_range
| rewrite length_map; exact Hi ]).
rewrite <- (map_nth bv_unsigned bs (Z_to_bv 8 0) i), u8_zero. reflexivity.
Qed.
Lemma bytes_le_to_Z_range : forall bs : list byte, length bs = 8%nat ->
(0 <= bytes_le_to_Z bs < 2^64)%Z.
Proof.
intros bs Hl. rewrite bytes_le_to_Z_zdig.
assert (HF : Forall (fun d => (0 <= d < 256)%Z) (map bv_unsigned bs))
by (apply Forall_map, Forall_forall; intros x _; apply u8_range).
split; [apply HZ.zdig_nonneg; exact HF|].
pose proof (HZ.zdig_lt _ HF) as H.
rewrite length_map, Hl in H. exact H.
Qed.
Lemma v_haszero : forall v : word,
bv_unsigned
(v_and (v_and (v_add v (Z_to_bv 64 18374403900871474943))
(v_xori v (-1)))
(Z_to_bv 64 9259542123273814144))
= HZ.Tz (bv_unsigned v).
Proof.
intro v. pose proof (u64_range v) as Hv.
unfold v_and, v_add, v_xori, HZ.Tz, HZ.ONESNEG, HZ.HIGHS, HZ.ALLONES.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite (Z.mod_small 18374403900871474943 (2^64)) by lia.
rewrite (Z.mod_small 9259542123273814144 (2^64)) by lia.
replace ((-1) mod 2^64)%Z with 18446744073709551615%Z
by (vm_compute; reflexivity).
assert (Hx : (0 <= Z.lxor (bv_unsigned v) 18446744073709551615 < 2^64)%Z)
by (apply HZ.lxor_lt64; lia).
rewrite (Z.mod_small (Z.lxor (bv_unsigned v) 18446744073709551615)) by exact Hx.
assert (Hm : (0 <= (bv_unsigned v + 18374403900871474943) mod 2^64 < 2^64)%Z)
by (apply Z.mod_pos_bound; lia).
assert (Hz : (0 <= Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615) < 2^64)%Z).
{ split; [apply Z.land_nonneg; left; lia|].
pose proof (HZ.land_le_l ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615) ltac:(lia)). lia. }
rewrite (Z.mod_small
(Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615))
(2^64)) by exact Hz.
apply Z.mod_small. split.
- apply Z.land_nonneg. right. lia.
- pose proof (HZ.land_le_r
(Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615))
9259542123273814144 ltac:(lia)). lia.
Qed.
Lemma total_arg_bytes_firstn_S : forall (l : list (list byte)) k,
(k < length l)%nat ->
total_arg_bytes_nat (firstn (S k) l)
= (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1)%nat.
Proof.
induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; cbn [firstn nth].
- cbv [total_arg_bytes_nat]. cbn [firstn fold_right].
rewrite firstn_O. cbn [fold_right]. lia.
- rewrite !total_arg_bytes_cons. cbn [length] in Hk.
rewrite (IH k ltac:(lia)). lia.
Qed.
Lemma bsb_len_lower : forall ph (sp : word) (a e : list (list byte)) uid hw rnd,
(cat_struct_size a e + total_arg_bytes_nat a + 16
<= length (build_stack_bytes ph sp a e uid hw rnd))%nat.
Proof.
intros ph sp a e uid hw rnd.
unfold build_stack_bytes, cat_struct_size. cbv zeta.
rewrite (string_addrs_pair a). cbv beta iota.
rewrite (string_addrs_pair e). cbv beta iota.
rewrite !length_app, !length_flat_map_le8,
!length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
!length_flatten_strings, !repeat_length, length_at_random_bytes.
lia.
Qed.
Lemma bsb_word_k : forall ph (sp : word) a e k m uid hw rnd, (k < length a)%nat ->
(m <= length (nth k a []))%nat ->
exists pre post,
build_stack_bytes ph sp a e uid hw rnd = pre ++ post
/\ length pre = (cat_struct_size a e + total_arg_bytes_nat (firstn k a) + m)%nat
/\ (8 <= length post)%nat.
Proof.
intros ph sp a e k m uid hw rnd Hk Hm.
destruct (bsb_byte_k ph sp a e k uid hw rnd Hk) as [pre0 [post0 [E Hlen0]]].
pose proof (bsb_len_lower ph sp a e uid hw rnd) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) a) as Hmono.
pose proof (total_arg_bytes_firstn_S a k Hk) as Hstep.
set (s1 := (nth k a [] ++ [Z_to_bv 8 0])) in *.
assert (Hs1 : length s1 = (length (nth k a []) + 1)%nat)
by (unfold s1; rewrite length_app; cbn [length]; lia).
assert (Hpost0 : (16 <= length post0)%nat).
{ assert (Hl : length (build_stack_bytes ph sp a e uid hw rnd)
= (length pre0 + length s1 + length post0)%nat)
by (rewrite E, !length_app; lia).
lia. }
exists (pre0 ++ firstn m s1), (skipn m s1 ++ post0).
split; [|split].
- rewrite E, <- !app_assoc. f_equal.
rewrite app_assoc, firstn_skipn. reflexivity.
- rewrite length_app, Hlen0, firstn_length_le by lia. lia.
- rewrite length_app, length_skipn. lia.
Qed.
Lemma read_word_stack : forall ph segs (sp : word) a e k m uid hw rnd,
(k < length a)%nat -> (m <= length (nth k a []))%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp a e uid hw rnd)) < 2^64)%Z ->
exists bs, length bs = 8%nat /\
rdn segs (stack_to_mem sp (entry_stack_image ph sp a e uid hw rnd))
(cat_argv_ptr sp a e k + nat_to_word m) 8%nat = Some bs.
Proof.
intros ph segs sp a e k m uid hw rnd Hk Hm Hnw.
destruct (bsb_word_k ph sp a e k m uid hw rnd Hk Hm) as [pre [post [E [Hlen Hpost]]]].
exists (firstn 8 post). split; [apply firstn_length_le; lia|].
replace (cat_argv_ptr sp a e k + nat_to_word m)
with (sp + nat_to_word (length pre)).
2:{ rewrite Hlen, (cat_argv_ptr_offset sp a e k Hk). unfold cat_string_base.
rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
apply (read_at_offset_image segs ph sp a e uid hw rnd
pre (firstn 8 post) (skipn 8 post) 8%nat).
- rewrite E. f_equal. symmetry. apply firstn_skipn.
- apply firstn_length_le. lia.
- exact Hnw.
Qed.
Lemma word_bytes_nth :
forall segs (mem : word -> option byte) (ptr : word) (s : list byte) m bs j,
rdn segs mem (ptr + nat_to_word m) 8%nat = Some bs ->
(forall i, (i <= length s)%nat ->
rdn segs mem (ptr + nat_to_word i) 1%nat = Some [byte_at s i]) ->
(j < 8)%nat -> (m + j <= length s)%nat ->
nth j bs (Z_to_bv 8 0) = byte_at s (m + j).
Proof.
intros segs mem ptr s m bs j Hr Hb Hj Hmj.
pose proof (rdn_nth segs mem 8%nat _ bs j Hr Hj) as H1.
rewrite nat_to_word_add_merge in H1.
rewrite (Hb (m + j)%nat Hmj) in H1.
congruence.
Qed.
Section f.
Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rnd : EntryDraw.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.
Lemma mstr_sp_lo : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma mstr_sp_hi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.
Lemma mstr_bsb_nw :
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
Proof.
pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof mstr_sp_hi. lia.
Qed.
Lemma argv_ptr_room : forall k, (k < length av)%nat ->
(bv_unsigned (cat_argv_ptr sp av ev k)
+ Z.of_nat (length (nth k av [])) + 17
<= bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)))%Z.
Proof.
intros k Hk.
pose proof mstr_sp_lo. pose proof mstr_sp_hi.
pose proof mstr_bsb_nw as Hnw.
pose proof (bsb_len_lower ph sp av ev uid hw rnd) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) av) as Hmono.
pose proof (total_arg_bytes_firstn_S av k Hk) as Hstep.
assert (Hptr : cat_argv_ptr sp av ev k
= sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
rewrite Hptr, word_add_nat, u_Z2bv by lia. lia.
Qed.
Lemma mstr_argv_ptr_bounds : forall k, (k < length av)%nat ->
(bv_unsigned sp <= bv_unsigned (cat_argv_ptr sp av ev k))%Z /\
(bv_unsigned (cat_argv_ptr sp av ev k)
+ Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof.
intros k Hk. apply argv_ptr_bounds; try assumption.
pose proof mstr_sp_hi. unfold argv_layout_slack. lia.
Qed.
Lemma argv_word_readable : forall k m,
(k < length av)%nat -> (m <= length (nth k av []))%nat ->
exists bs, length bs = 8%nat /\
rdn segs (wrap_mem ph sp av ev uid hw rnd)
(cat_argv_ptr sp av ev k + nat_to_word m) 8%nat = Some bs.
Proof.
intros k m Hk Hm.
pose proof mstr_sp_lo. pose proof mstr_sp_hi.
destruct (mstr_argv_ptr_bounds k Hk) as [Hge Hup].
pose proof (argv_ptr_room k Hk) as Hroom.
pose proof mstr_bsb_nw as Hnw.
pose proof (u64_range (cat_argv_ptr sp av ev k)).
assert (Hu : bv_unsigned (cat_argv_ptr sp av ev k + nat_to_word m)
= (bv_unsigned (cat_argv_ptr sp av ev k) + Z.of_nat m)%Z)
by (rewrite word_add_nat; apply u_Z2bv; lia).
destruct (read_word_stack ph segs sp av ev k m uid hw rnd Hk Hm Hnw) as [bs [Hl Hr]].
exists bs. split; [exact Hl|].
rewrite rdn_wrap_stack_above by (rewrite Hu; lia).
exact Hr.
Qed.
End f.
