(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem.
Import ListNotations.
Open Scope Z_scope.
Fixpoint le_val (bs : list Z) : Z :=
match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Fixpoint ones (n : nat) : Z := match n with O => 0 | S n' => 1 + 256 * ones n' end.
Definition highs (n : nat) : Z := 128 * ones n.
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.
Lemma le_val_range : forall bs, bytes_ok bs -> 0 <= le_val bs < 256 ^ Z.of_nat (length bs).
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0030=16602919810.141800397511.648728608659.6000001002009SSS2IH2H2".
induction bs as [|b bs IH]; intros H; cbn [le_val length]; [lia|].
inversion H; subst. specialize (IH ltac:(assumption)).
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma split_mod : forall x y M, 0 <= x < 256 -> 0 < M -> (x + 256 * y) mod (256 * M) = x + 256 * (y mod M).
Proof.
intros x y M Hx HM. Local Ltac2 Set LiaHints.tbl := fun () => "0030=14880339796.534050794402.57109247307.5 000004008009S2HxS2HMS".
rewrite Z.rem_mul_r by lia.
rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma testbit_split : forall x y i, 0 <= x < 256 -> 0 <= i ->
Z.testbit (x + 256 * y) i = if i <? 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof.
intros x y i Hx Hi. destruct (Z.ltb_spec0 i 8).
- Local Ltac2 Set LiaHints.tbl := fun () => "0080=14873421749.614873454263.617508899659.637873708936.645140756772.663373994096.67110857130.6 7110889640.6 00000400800;00<00?00@00A00BS2HxS2HxS1lSS1nSSS".
rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. change (2^8) with 256.
rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia. reflexivity.
- replace i with ((i - 8) + 8) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2^8) with 256.
rewrite (Z.mul_comm 256 y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
intros a b n Ha Hb.
assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>2427057214.7  2431248216.6  26981515745.1026985714707.9 41418083600.7 42884098460.1144222768328.6 8740824318.10 9664604402.9  9664605798.7  00000400800@00D00E00K00N00R00^00fS2HnS2HaS2Ha3HazS2HaSS1H2H0S1HS2HaS2Hb3Hnn3HnzS2Hb3Hnn".
rewrite Z.pow_neg_r in Ha by lia. lia. }
pose proof (Z.land_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]. { apply Z.pow_pos_nonneg; lia. }
destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. apply Z.pow_pos_nonneg; lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.land a b) n ltac:(lia))).
pose proof (Z.log2_land a b ltac:(lia) Hb). assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
intros a b n Ha Hb.
assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>14064806669.1014066902035.6 2431248216.6  26983619993.1044222768328.6 61883803660.108734103750.7  8734537862.10 9664605798.7  9666265146.10 9668754063.10 00000400800<00C00F00M00Q00U00`01401=S2HbS2HbS2HaS2Ha2n0S1HS2Hb2n1S2HaS2HaS2Ha2Hb3HnnS2Ha2Hb3Hnn2n02n12n2S2Ha2n01E".
rewrite Z.pow_neg_r in Ha by lia. lia. }
pose proof (Z.lor_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec a 0) as [->|]. { rewrite Z.lor_0_l. lia. }
destruct (Z.eq_dec b 0) as [->|]. { rewrite Z.lor_0_r. lia. }
assert (Hp : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)). rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
Z.land (x + 256 * y) (x' + 256 * y') = Z.land x x' + 256 * Z.land y y'.
Proof.
intros x y x' y' Hx Hx'.
Local Ltac2 Set LiaHints.tbl := fun () => "0060=10351595562.914880335152.933734324714.662804696636.966068019280.967153860139.600000400800=00B00F00JS2HiS2HxS3Hx'S3Hx'S2HlS2Hx".
pose proof (land_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(lia)) as Hl. change (2^8) with 256 in Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.land_spec; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lnot_split : forall b w, Z.lnot (b + 256 * w) = (255 - b) + 256 * Z.lnot w.
Proof. intros. unfold Z.lnot. Local Ltac2 Set LiaHints.tbl := fun () => "0010<1687339620.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma byte_fact1 : forall b, 1 <= b < 256 -> Z.land (Z.land (b - 1) (255 - b)) 128 = 0.
Proof.
intros b Hb.
assert (C : forallb (fun b => Z.land (Z.land (b - 1) (255 - b)) 128 =? 0) (map Z.of_nat (seq 1 255)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. apply Z.eqb_eq, C. apply in_map_iff. exists (Z.to_nat b). Local Ltac2 Set LiaHints.tbl := fun () => "0020=17728367227.343654326543.3000004008S2HbS2Hb".
split; [lia|]. apply in_seq. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Theorem haszero_iff : forall bs, bytes_ok bs ->
let n := length bs in let w := le_val bs in
Z.land (Z.land ((w - ones n) mod 256 ^ Z.of_nat n) (Z.lnot w)) (highs n) <> 0 <-> In 0 bs.
Proof.
induction bs as [|b bs IH]; intros H; cbn [length le_val ones highs].
- cbn. split; [|intros []]. intros C; apply C. reflexivity.
- inversion H as [|b' bs' Hb Hbs]; subst. specialize (IH Hbs). cbn zeta in IH.
unfold highs in *. cbn [ones].
Local Ltac2 Set LiaHints.tbl := fun () => "00E0=10868468971.918399564973.718430925547.624681705334.629317941360.63083805832.6 36026607851.836028710484.636626358135.841798293767.642028956648.642031050071.843281142998.844392703593.944394802941.951111971323.954850092628.656548789919.865008962479.867470433954.867822670191.800000800900:00;00<00=00>00?00G00H00L00P00X00c00k00o01001401801901AS2HM3HnzSSSSSSSS2Hb3Hb0SS2HMS2HMS2Hb3Hb0S2Hb3Hb02HzS2HM3HinS2H0SS2HbS2HbSS2Hb3Hb0".
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
pose proof (Z.pow_pos_nonneg 256 (Z.of_nat (length bs)) ltac:(lia) ltac:(lia)) as HM.
rewrite lnot_split.
replace (128 * (1 + 256 * ones (length bs))) with (128 + 256 * (128 * ones (length bs))) by lia.
destruct (Z.eq_dec b 0) as [->|Hb0].
+ replace (0 + 256 * le_val bs - (1 + 256 * ones (length bs))) with (255 + 256 * (le_val bs - ones (length bs) - 1)) by lia.
rewrite split_mod by lia. rewrite land_split by lia. change (Z.land 255 (255 - 0)) with 255.
rewrite land_split by lia. change (Z.land 255 128) with 128.
split; [intros; left; reflexivity| intros _]. lia.
+ replace (b + 256 * le_val bs - (1 + 256 * ones (length bs))) with ((b - 1) + 256 * (le_val bs - ones (length bs))) by lia.
rewrite split_mod by lia.
rewrite land_split by lia.
rewrite land_split. 2:{ pose proof (land_lt_pow2 (b-1) (255-b) 8 ltac:(cbn; lia) ltac:(lia)). cbn in *. lia. }
2:{ lia. }
rewrite byte_fact1 by lia.
split.
* intros Hnz. right. apply IH. lia.
* intros [Hz|Hin]; [lia|]. apply IH in Hin. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition ONES64b : Z := 0x0101010101010101.
Definition HIGHS64b : Z := 0x8080808080808080.
Lemma ones_8 : ones 8 = ONES64b. Proof. reflexivity. Qed.
Lemma highs_8 : highs 8 = HIGHS64b. Proof. reflexivity. Qed.
Lemma testbit_high_false : forall x n i, 0 <= x < 2^n -> 0 <= n <= i -> Z.testbit x i = false.
Proof.
intros x n i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
Local Ltac2 Set LiaHints.tbl := fun () => "0030=23902084583.65234359347.6 56094109726.600000400800?S2HxS2HiS2Hx2n0".
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_mod_pow2_r : forall a b n, 0 <= a < 2^n -> 0 <= n -> Z.land a (b mod 2^n) = Z.land a b.
Proof.
intros a b n Ha Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i n).
- Local Ltac2 Set LiaHints.tbl := fun () => "0030=16853391900.826078808458.853766673673.800000400:00=S2HaS2Hn1HS1H".
rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite (testbit_high_false a n i) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lnot_mod64 : forall w, 0 <= w < 2^64 -> Z.lxor w 18446744073709551615 = (Z.lnot w) mod 2^64.
Proof.
intros w Hw. change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0070=10351595562.419457651979.629719490512.635497640807.238962285935.559228149738.560746805469.600000400700;00<00B00E00KS2HiS1HS2HwSS2Hi1HS1HS2Hw1n".
rewrite <- Z.land_ones by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma demorgan_highs : forall D w H, 0 <= D < 2^64 -> 0 <= w < 2^64 -> 0 <= H < 2^64 ->
Z.land (Z.lor (Z.lxor D 18446744073709551615) w) H = H <-> Z.land (Z.land D (Z.lnot w)) H = 0.
Proof.
intros D w H HD Hw HH. change 18446744073709551615 with (Z.ones 64).
assert (HI : forall x, 0 <= x < 2^64 -> forall i, 64 <= i -> Z.testbit x i = false).
{ intros x Hx i Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
Local Ltac2 Set LiaHints.tbl := fun () => "0080>10351595562.1019456170581.1119457651979.1134768218930.1138960197975.1156087813952.118548816274.11 9068841147.11 00000400800<00@00G00M00Q00US2HiS2H0S2HiS2HHS2Hi2H0S2Hx1nS2HDS2Hx".
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia]. }
split; intros E; apply Z.bits_inj'; intros i Hi.
- rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec by lia.
apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec in E.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low in E by lia.
destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
+ rewrite (HI D) by lia. reflexivity.
- apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec in E by lia.
rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low by lia.
destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
+ rewrite (HI H) by lia. apply andb_false_r.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Theorem haszero64_clang : forall bs, bytes_ok bs -> length bs = 8%nat ->
let w := le_val bs in
Z.land (Z.lor ((72340172838076672 - w) mod 18446744073709551616) w) 9259542123273814144 = 9259542123273814144
<-> ~ In 0 bs.
Proof.
intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
set (D := (w - 72340172838076673) mod 2 ^ 64) in HZ.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>11447729963.2819841477254.8 38948411587.7 5231147802.8  8548822950.8  00000D00J00P00Y00bS4Hlen1H2H02H42H52H9S4HlenS4HlenS4Hlen2HwS4Hlen2HD".
assert (HD : 0 <= D < 2^64) by (apply Z.mod_pos_bound; lia).
replace ((72340172838076672 - w) mod 2 ^ 64) with (Z.lxor D 18446744073709551615).
2:{ rewrite lnot_mod64 by lia. unfold Z.lnot. subst D. Z.div_mod_to_equations. lia. }
rewrite demorgan_highs by lia.
destruct HZ as [HZ1 HZ2]. split.
- intros E I. apply HZ2 in I. apply I. exact E.
- intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
exfalso. apply NI. apply HZ1. exact NE.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lor_shiftl8_add : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
intros x y Hx Hy. Local Ltac2 Set LiaHints.tbl := fun () => "00:0=10351595562.610358444719.634656753877.835653212261.84646689621.4 48215763244.656087813952.756094109726.857019992528.663368323813.400000400700:00>00?00@00D00K00L00MS2HiS1nS1nS2HxSSS2HxS2Hx2n0SS".
rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia]. }
symmetry. replace (256 * y) with (y * 256) by lia. apply Z.add_nocarry_lxor.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma bytes_ok_map : forall bs : list byte, bytes_ok (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=21381109757.4000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma bytes_le_to_Z_le_val : forall bs : list byte, bytes_le_to_Z bs = le_val (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z le_val map]; [reflexivity|].
rewrite IH. apply lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. Local Ltac2 Set LiaHints.tbl := fun () => "0020=21381109757.445643496231.4000003006S1HS1H".
lia.
- pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma load8_le_val : forall bs : list byte, length bs = 8%nat ->
bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs)) = le_val (map bv_unsigned bs).
Proof.
intros bs Hlen. unfold le_bytes_to_word. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
rewrite bytes_le_to_Z_le_val.
pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hlen in Hr.
change (256 ^ Z.of_nat 8) with (2^64) in Hr.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=16075526792.3000009S4Hlen2Hr".
rewrite (bv_wrap_small 64 (le_val _)) by (change (bv_modulus 64) with (2^64); lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
