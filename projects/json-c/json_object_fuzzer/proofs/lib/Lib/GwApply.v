(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Bytes.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.Riscv.Prelude.
Import QsjA QEpW QZDE.
Import ListNotations.
Open Scope Z_scope.

Fixpoint le_val (bs : list Z) : Z :=
match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Fixpoint ones (n : nat) : Z := match n with O => 0 | S n' => 1 + 256 * ones n' end.
Definition highs (n : nat) : Z := 128 * ones n.
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Lemma le_val_range : forall bs, bytes_ok bs -> 0 <= le_val bs < 256 ^ Z.of_nat (length bs).
Proof.
induction bs as [|b bs IH]; intros H; cbn [le_val length]; [lia|].
inversion H; subst. specialize (IH ltac:(assumption)).
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma split_mod : forall x y M, 0 <= x < 256 -> 0 < M -> (x + 256 * y) mod (256 * M) = x + 256 * (y mod M).
Proof.
intros x y M Hx HM. rewrite Z.rem_mul_r by lia.
rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma testbit_split : forall x y i, 0 <= x < 256 -> 0 <= i ->
Z.testbit (x + 256 * y) i = if i <? 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof.
intros x y i Hx Hi. destruct (Z.ltb_spec0 i 8).
- rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. change (2^8) with 256.
rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia. reflexivity.
- replace i with ((i - 8) + 8) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2^8) with 256.
rewrite (Z.mul_comm 256 y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma land_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
intros a b n Ha Hb.
assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
pose proof (Z.land_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]. { apply Z.pow_pos_nonneg; lia. }
destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. apply Z.pow_pos_nonneg; lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.land a b) n ltac:(lia))).
pose proof (Z.log2_land a b ltac:(lia) Hb). assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
intros a b n Ha Hb.
assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
pose proof (Z.lor_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec a 0) as [->|]. { rewrite Z.lor_0_l. lia. }
destruct (Z.eq_dec b 0) as [->|]. { rewrite Z.lor_0_r. lia. }
assert (Hp : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)). rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
Z.land (x + 256 * y) (x' + 256 * y') = Z.land x x' + 256 * Z.land y y'.
Proof.
intros x y x' y' Hx Hx'.
pose proof (land_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(lia)) as Hl. change (2^8) with 256 in Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.land_spec; reflexivity.
Qed.

Lemma lor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
Z.lor (x + 256 * y) (x' + 256 * y') = Z.lor x x' + 256 * Z.lor y y'.
Proof.
intros x y x' y' Hx Hx'.
pose proof (lor_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(cbn; lia)) as Hl. change (2^8) with 256 in Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.lor_spec; reflexivity.
Qed.

Lemma lnot_split : forall b w, Z.lnot (b + 256 * w) = (255 - b) + 256 * Z.lnot w.
Proof. intros. unfold Z.lnot. lia. Qed.

Lemma byte_fact1 : forall b, 1 <= b < 256 -> Z.land (Z.land (b - 1) (255 - b)) 128 = 0.
Proof.
intros b Hb.
assert (C : forallb (fun b => Z.land (Z.land (b - 1) (255 - b)) 128 =? 0) (map Z.of_nat (seq 1 255)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. apply Z.eqb_eq, C. apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

Theorem haszero_iff : forall bs, bytes_ok bs ->
let n := length bs in let w := le_val bs in
Z.land (Z.land ((w - ones n) mod 256 ^ Z.of_nat n) (Z.lnot w)) (highs n) <> 0 <-> In 0 bs.
Proof.
induction bs as [|b bs IH]; intros H; cbn [length le_val ones highs].
- cbn. split; [|intros []]. intros C; apply C. reflexivity.
- inversion H as [|b' bs' Hb Hbs]; subst. specialize (IH Hbs). cbn zeta in IH.
unfold highs in *. cbn [ones].
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
Qed.

Definition ONES64b  : Z := 0x0101010101010101.
Definition HIGHS64b : Z := 0x8080808080808080.

Lemma ones_8 : ones 8 = ONES64b. Proof. reflexivity. Qed.
Lemma highs_8 : highs 8 = HIGHS64b. Proof. reflexivity. Qed.

Lemma testbit_high_false : forall x n i, 0 <= x < 2^n -> 0 <= n <= i -> Z.testbit x i = false.
Proof.
intros x n i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_mod_pow2_r : forall a b n, 0 <= a < 2^n -> 0 <= n -> Z.land a (b mod 2^n) = Z.land a b.
Proof.
intros a b n Ha Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i n).
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite (testbit_high_false a n i) by lia. reflexivity.
Qed.

Lemma lnot_mod64 : forall w, 0 <= w < 2^64 -> Z.lxor w 18446744073709551615 = (Z.lnot w) mod 2^64.
Proof.
intros w Hw. change 18446744073709551615 with (Z.ones 64). rewrite <- Z.land_ones by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Theorem haszero64_gcc : forall bs, bytes_ok bs -> length bs = 8%nat ->
let w := le_val bs in
Z.land (Z.land ((w + 18374403900871474943) mod 18446744073709551616) (Z.lxor w 18446744073709551615)) 9259542123273814144 = 0
<-> ~ In 0 bs.
Proof.
intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
replace ((w + 18374403900871474943) mod 2 ^ 64) with ((w - 72340172838076673) mod 2^64).
2:{ replace (w + 18374403900871474943) with ((w - 72340172838076673) + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity. }
rewrite lnot_mod64 by lia. rewrite land_mod_pow2_r by (try lia; apply Z.mod_pos_bound; lia).

destruct HZ as [HZ1 HZ2]. split.
- intros E I. apply HZ2 in I. apply I. exact E.
- intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
exfalso. apply NI. apply HZ1. exact NE.
Qed.

Lemma demorgan_highs : forall D w H, 0 <= D < 2^64 -> 0 <= w < 2^64 -> 0 <= H < 2^64 ->
Z.land (Z.lor (Z.lxor D 18446744073709551615) w) H = H <-> Z.land (Z.land D (Z.lnot w)) H = 0.
Proof.
intros D w H HD Hw HH. change 18446744073709551615 with (Z.ones 64).
assert (HI : forall x, 0 <= x < 2^64 -> forall i, 64 <= i -> Z.testbit x i = false).
{ intros x Hx i Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
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
Qed.

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
assert (HD : 0 <= D < 2^64) by (apply Z.mod_pos_bound; lia).
replace ((72340172838076672 - w) mod 2 ^ 64) with (Z.lxor D 18446744073709551615).
2:{ rewrite lnot_mod64 by lia. unfold Z.lnot. subst D. Z.div_mod_to_equations. lia. }
rewrite demorgan_highs by lia.

destruct HZ as [HZ1 HZ2]. split.
- intros E I. apply HZ2 in I. apply I. exact E.
- intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
exfalso. apply NI. apply HZ1. exact NE.
Qed.

Lemma lor_shiftl8_add : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
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
Qed.

Lemma bytes_ok_map : forall bs : list byte, bytes_ok (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.

Lemma bytes_le_to_Z_le_val : forall bs : list byte, bytes_le_to_Z bs = le_val (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z le_val map]; [reflexivity|].
rewrite IH. apply lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
- pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia.
Qed.

Lemma load8_le_val : forall bs : list byte, length bs = 8%nat ->
bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs)) = le_val (map bv_unsigned bs).
Proof.
intros bs Hlen. unfold le_bytes_to_word. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
rewrite bytes_le_to_Z_le_val.
pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hlen in Hr.
change (256 ^ Z.of_nat 8) with (2^64) in Hr.
rewrite (bv_wrap_small 64 (le_val _)) by (change (bv_modulus 64) with (2^64); lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64); lia.
Qed.

Lemma In0_map_unsigned : forall bs : list byte, In 0 (map bv_unsigned bs) <-> In (Z_to_bv 8 0) bs.
Proof.
intros bs. rewrite in_map_iff. split.
- intros (b & Hb & Hin). replace (Z_to_bv 8 0) with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
- intros Hin. exists (Z_to_bv 8 0). split; [reflexivity|exact Hin].
Qed.
End Bytes.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ZBridge.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsjA QEpW QZDE.
Import ListNotations.
Open Scope bv_scope.

Definition inr64 (e : Z) : Prop := (0 <= e < 2^64)%Z.

Lemma zr_word : forall x : word, inr64 (bv_unsigned x).
Proof. intros x. pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in *. exact H. Qed.
Lemma zr_bv : forall n (x : bv n), (n <= 64)%N -> inr64 (bv_unsigned x).
Proof.
intros n x Hn. pose proof (bv_unsigned_in_range n x) as H. unfold bv_modulus, inr64 in *.
split; [lia|]. apply Z.lt_le_trans with (2 ^ Z.of_N n)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_lit : forall z, (0 <= z < 2^64)%Z -> inr64 z.
Proof. intros; assumption. Qed.
Lemma zr_mod64 : forall e, inr64 (e mod 2^64).
Proof. intros. unfold inr64. apply Z.mod_pos_bound. lia. Qed.
Lemma zr_mod : forall e k, (0 <= k <= 64)%Z -> inr64 (e mod 2^k).
Proof.
intros e k Hk. unfold inr64. pose proof (Z.mod_pos_bound e (2^k) ltac:(apply Z.pow_pos_nonneg; lia)).
split; [lia|]. apply Z.lt_le_trans with (2^k)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_mod_any : forall e p, (0 < p <= 2^64)%Z -> inr64 (e mod p).
Proof. intros e p Hp. unfold inr64. pose proof (Z.mod_pos_bound e p ltac:(lia)). lia. Qed.
Lemma zr_land_l : forall a b, inr64 a -> (0 <= b)%Z -> inr64 (Z.land a b).
Proof.
intros a b [Ha Ha'] Hb. unfold inr64. pose proof (Z.land_nonneg a b) as Hn.
split; [lia|].
destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]; [lia|].
destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. lia. }
apply Z.log2_lt_pow2; [lia|].
pose proof (Z.log2_land a b ltac:(lia) Hb).
assert (Z.log2 a < 64)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma zr_land_r : forall a b, (0 <= a)%Z -> inr64 b -> inr64 (Z.land a b).
Proof. intros. rewrite Z.land_comm. apply zr_land_l; assumption. Qed.

Lemma land_mask_mod : forall e m, (0 <= m < 2^64)%Z -> Z.land e m = Z.land (e mod 2^64) m.
Proof.
intros e m Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit m i) with false. { rewrite !andb_false_r. reflexivity. }
symmetry. destruct (Z.eq_dec m 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma zr_land_lit : forall e m, (0 <= m < 2^64)%Z -> inr64 (Z.land e m).
Proof.
intros e m Hm. rewrite land_mask_mod by exact Hm. apply zr_land_r; [|exact Hm].
apply Z.mod_pos_bound. lia.
Qed.
Lemma zr_lor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lor_range; lia. Qed.
Lemma zr_lxor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lxor_range; lia. Qed.
Lemma zr_shiftr : forall a k, inr64 a -> (0 <= k)%Z -> inr64 (Z.shiftr a k).
Proof. intros a k Ha Hk. unfold inr64 in *. apply Z_shiftr_range; lia. Qed.
Lemma zr_div : forall a k, inr64 a -> (0 < k)%Z -> inr64 (a / k).
Proof.
intros a k [Ha Ha'] Hk. unfold inr64. split. { apply Z.div_pos; lia. }
apply Z.le_lt_trans with a; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma zr_b2z : forall b, inr64 (Z.b2z b).
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zr_ite : forall (b : bool) x y, inr64 x -> inr64 y -> inr64 (if b then x else y).
Proof. intros [|]; auto. Qed.

Lemma inr64_unsigned_lit : forall e, inr64 e -> bv_unsigned (Z_to_bv 64 e) = e.
Proof. intros e H. apply unsigned_lit. exact H. Qed.

Ltac is_Zlit_zb a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac slim := repeat match goal with x := _ : Z |- _ => clearbody x end.
Ltac flia := first [ assumption | slim; lia | lia ]. Ltac mkr__flia_0 := first [ assumption | slim; lia | lia ].

Ltac zrange :=
lazymatch goal with
| |- inr64 ?e =>
lazymatch e with
| bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
| Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
| apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
| Z.lor _ _ => apply zr_lor; [zrange | zrange]
| Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
| Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
| Z.modulo _ (2^64)%Z => apply zr_mod64
| Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
| Z.div _ _ => apply zr_div; [zrange | flia]
| Z.b2z _ => apply zr_b2z
| (if _ then _ else _) => apply zr_ite; [zrange | zrange]
| _ => first [ apply zr_lit; flia
| is_var e; progress (unfold e); zrange ]
end
| |- (0 <= ?e < _)%Z => change (inr64 e); zrange
end
with zrange_nonneg :=
lazymatch goal with
| |- (0 <= ?e)%Z =>
first [ apply (proj1 (A:=(0 <= e)%Z) (B:=(e < 2^64)%Z)); change (inr64 e); zrange
| apply Z.land_nonneg; left; zrange_nonneg
| apply Z.lor_nonneg; split; zrange_nonneg
| apply Z.lxor_nonneg; split; zrange_nonneg
| apply Z.shiftr_nonneg; zrange_nonneg
| apply Z.shiftl_nonneg; zrange_nonneg
| flia
| is_var e; progress (unfold e); zrange_nonneg ]
end.

Lemma Z_to_bv_mod64 : forall e, Z_to_bv 64 (e mod 2^64) = Z_to_bv 64 e.
Proof.
intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
apply Z.mod_mod. lia.
Qed.

Lemma zb_land_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.land y (2^k) = 0%Z.
Proof.
intros y k Hy Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i k) as [->|Hne].
- rewrite Z.pow2_bits_true by lia. rewrite andb_true_r.
apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
- rewrite Z.pow2_bits_eqb by lia. replace (k =? i)%Z with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma zb_lxor_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.lxor y (2^k) = (y + 2^k)%Z.
Proof. intros. symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_small; assumption. Qed.

Lemma zb_lxor_sign : forall x, (0 <= x < 2^64)%Z -> Z.lxor x (2^63) = ((x + 2^63) mod 2^64)%Z.
Proof.
intros x Hx. destruct (Z.lt_ge_cases x (2^63)).
- rewrite zb_lxor_pow2_small by lia. rewrite Z.mod_small by lia. reflexivity.
- set (y := (x - 2^63)%Z). replace x with (y + 2^63)%Z by lia.
rewrite <- (zb_lxor_pow2_small y 63) at 1 by lia. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
replace (y + 2^63 + 2^63)%Z with (y + 1 * 2^64)%Z by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

Lemma zb_signed : forall x : word,
bv_signed x = (if bv_unsigned x <? 2^63 then bv_unsigned x else bv_unsigned x - 2^64)%Z.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as Hr. unfold bv_modulus in Hr.
unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. change (2^64 / 2)%Z with (2^63)%Z.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
- rewrite Z.mod_small by lia. lia.
- rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma bv_eqb_Z : forall x y : word, bv_eqb x y = (bv_unsigned x =? bv_unsigned y)%Z.
Proof. reflexivity. Qed.
Lemma bv_ltu_Z : forall x y : word, bv_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof. reflexivity. Qed.

Lemma bv_lts_lxor : forall x y : word,
bv_lts x y = (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z.
Proof.
intros x y. unfold bv_lts. rewrite !zb_signed.
pose proof (bv_unsigned_in_range 64 x) as Hx. pose proof (bv_unsigned_in_range 64 y) as Hy. unfold bv_modulus in *.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
rewrite !zb_lxor_sign by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); destruct (Z.ltb_spec0 (bv_unsigned y) (2^63)).
- rewrite !Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite (Z.mod_small (bv_unsigned x + _)) by lia.
rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite (Z.mod_small (bv_unsigned y + _)) by lia.
rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia.
rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.

Lemma bv_lts_zero_r : forall x : word, bv_lts x (Z_to_bv 64 0) = (2^63 <=? bv_unsigned x)%Z.
Proof.
intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite Z.ltb_lt, Z.leb_le; lia.
Qed.

Lemma bv_lts_zero_l : forall x : word,
bv_lts (Z_to_bv 64 0) x = ((0 <? bv_unsigned x) && (bv_unsigned x <? 2^63))%Z.
Proof.
intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite andb_true_iff, !Z.ltb_lt; lia.
Qed.

Lemma v_sltu_b2z : forall x y : word, v_sltu x y = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_unsigned y)%Z).
Proof. intros. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slt_b2z : forall x y : word,
v_slt x y = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z).
Proof. intros. unfold v_slt, c_lts. rewrite bv_lts_lxor. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_sltiu_b2z : forall (x : word) imm, v_sltiu x imm = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_wrap 64 imm)%Z).
Proof. intros. unfold v_sltiu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slti_b2z : forall (x : word) imm,
v_slti x imm = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? imm + 2^63)%Z).
Proof.
intros. unfold v_slti, zsig. rewrite zb_signed.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
rewrite zb_lxor_sign by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
- rewrite Z.mod_small by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63) (imm + 2^63)); try reflexivity; exfalso; lia.
- rewrite <- (Z.mod_add _ (-1)), Z.mod_small by lia.
destruct (Z.ltb_spec0 (bv_unsigned x - 2^64) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63 + -1 * 2^64) (imm + 2^63)); try reflexivity; exfalso; lia.
Qed.

Lemma zb_b2z_if : forall b, Z.b2z b = (if b then 1 else 0)%Z.
Proof. intros [|]; reflexivity. Qed.
Lemma zb_b2z_nonzero : forall b, Z.b2z b <> 0%Z <-> b = true.
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_zero : forall b, Z.b2z b = 0%Z <-> b = false.
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_eqb0 : forall b, (Z.b2z b =? 0)%Z = negb b.
Proof. intros [|]; reflexivity. Qed.
Lemma zb_b2z_range : forall b, (0 <= Z.b2z b <= 1)%Z.
Proof. intros [|]; cbv; split; congruence. Qed.

Lemma zb_land_mask : forall x k, (0 <= k)%Z -> Z.land x (2^k - 1) = (x mod 2^k)%Z.
Proof. intros. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal. Qed.
Lemma zb_land_mask_l : forall x k, (0 <= k)%Z -> Z.land (2^k - 1) x = (x mod 2^k)%Z.
Proof. intros. rewrite Z.land_comm. apply zb_land_mask. assumption. Qed.

Lemma zb_shiftl_mul : forall x k, (0 <= k)%Z -> Z.shiftl x k = (x * 2^k)%Z.
Proof. intros. apply Z.shiftl_mul_pow2. assumption. Qed.
Lemma zb_shiftr_div : forall x k, (0 <= k)%Z -> Z.shiftr x k = (x / 2^k)%Z.
Proof. intros. apply Z.shiftr_div_pow2. assumption. Qed.

Lemma zb_shl_shr : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
Z.shiftr ((Z.shiftl x k) mod 2^64) k = (x mod 2^(64 - k))%Z.
Proof.
intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (2^64)%Z with (2^(64-k) * 2^k)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.

Lemma zb_shr_shl : forall x k, (0 <= x)%Z -> (0 <= k)%Z ->
Z.shiftl (Z.shiftr x k) k = (x - x mod 2^k)%Z.
Proof.
intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
pose proof (Z.div_mod x (2^k) ltac:(lia)). lia.
Qed.

Lemma zb_lor_eq0 : forall a b, (Z.lor a b = 0)%Z <-> (a = 0 /\ b = 0)%Z.
Proof. intros. apply Z.lor_eq_0_iff. Qed.
Lemma zb_lor_eqb0 : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.lor a b =? 0)%Z = ((a =? 0) && (b =? 0))%Z.
Proof.
intros a b Ha Hb. apply eq_true_iff_eq. rewrite andb_true_iff, !Z.eqb_eq. apply Z.lor_eq_0_iff.
Qed.
Lemma zb_lxor_eq0 : forall a b, (Z.lxor a b = 0)%Z <-> a = b.
Proof. intros. apply Z.lxor_eq_0_iff. Qed.
Lemma zb_lxor_eqb0 : forall a b, (Z.lxor a b =? 0)%Z = (a =? b)%Z.
Proof.
intros. apply eq_true_iff_eq. rewrite !Z.eqb_eq. apply Z.lxor_eq_0_iff.
Qed.
Lemma zb_land_lor_distr_l : forall a b m, Z.land (Z.lor a b) m = Z.lor (Z.land a m) (Z.land b m).
Proof. intros. apply Z.land_lor_distr_l. Qed.

Lemma zb_lxor_ones : forall x, (0 <= x < 2^64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
intros x Hx. change 18446744073709551615%Z with (Z.ones 64).
pose proof (Z.add_lnot_diag x).
assert (E : Z.lxor x (Z.ones 64) = ((Z.lnot x) mod 2^64)%Z).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^64)) with (2^64 - 1)%Z.
replace (Z.lnot x) with (-x - 1)%Z by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac mlia := Z.div_mod_to_equations; lia.

Ltac zb_fold_lits :=
repeat match goal with
| |- context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
| |- context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
| |- context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
| |- context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
| |- context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
| |- context [Z.modulo ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
| |- context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v
| |- context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
| |- context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
replace (bv_wrap n z) with v by (vm_compute; reflexivity)
| |- context [Z_to_bv 64 ?z] => is_Zlit_zb z;
lazymatch eval vm_compute in (Z.leb 18446744073709551616 z) with true => idtac end;
let v := eval vm_compute in (z mod 18446744073709551616)%Z in
replace (Z_to_bv 64 z) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
end.

Lemma unsigned_lit_land : forall e, bv_unsigned (Z_to_bv 64 e) = Z.land e 18446744073709551615.
Proof. intros. rewrite unsigned_lit_wrap. change 18446744073709551615%Z with (Z.ones 64). symmetry. apply Z.land_ones. lia. Qed.
Lemma Z_to_bv_land64 : forall e, Z_to_bv 64 (Z.land e 18446744073709551615) = Z_to_bv 64 e.
Proof. intros. rewrite <- unsigned_lit_land. apply Z_to_bv_bv_unsigned. Qed.
Lemma zb_shl_shr_land : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
Z.shiftr (Z.land (Z.shiftl x k) 18446744073709551615) k = Z.land x (2^(64 - k) - 1).
Proof.
intros x k Hx Hk. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite zb_shl_shr, <- zb_land_mask by lia. reflexivity.
Qed.

Ltac zs_wrap e := rewrite (unsigned_lit_wrap e). Ltac mkr__zs_wrap_1 e := rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H := rewrite (unsigned_lit_wrap e) in H. Ltac mkr__zs_wrap_in_2 e H := rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms :=
match goal with
| |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
end. Ltac mkr__zs_idioms_3 := match goal with
| |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
end.
Ltac zs_idioms_in H :=
match type of H with
| context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
end. Ltac mkr__zs_idioms_in_4 H := match type of H with
| context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
end.

Ltac zs_wrap_land e := rewrite (unsigned_lit_land e).
Ltac zs_wrap_land_in e H := rewrite (unsigned_lit_land e) in H.
Ltac zs_idioms_land :=
match goal with
| |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
end.
Ltac zs_idioms_land_in H :=
match type of H with
| context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
end.

Ltac zsimp :=
rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
cbv delta [zxb];
zb_fold_lits;
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
first [ rewrite (inr64_unsigned_lit e) by zrange
| zs_wrap e ]
| |- _ => progress zs_idioms
end; zb_fold_lits. Ltac mkr__zsimp_5 := rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
cbv delta [zxb];
zb_fold_lits;
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
first [ rewrite (inr64_unsigned_lit e) by zrange
| zs_wrap e ]
| |- _ => progress zs_idioms
end; zb_fold_lits.

Ltac zb_fold_lits_in H :=
repeat match type of H with
| context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v in H
| context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
| context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in H
| context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in H
| context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
| context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v in H
| context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
| context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
replace (bv_wrap n z) with v in H by (vm_compute; reflexivity)
end.

Ltac zsimp_in H :=
rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
cbv delta [zxb] in H;
zb_fold_lits_in H;
repeat match type of H with
| context [bv_unsigned (Z_to_bv 64 ?e)] =>
first [ rewrite (inr64_unsigned_lit e) in H by zrange
| zs_wrap_in e H ]
| _ => progress (zs_idioms_in H)
end; zb_fold_lits_in H.

Ltac decide_tests :=
repeat match goal with
| |- context [Z.eqb ?x ?y] =>
first [ rewrite (proj2 (Z.eqb_eq x y)) by mlia | rewrite (proj2 (Z.eqb_neq x y)) by mlia ]
| |- context [Z.ltb ?x ?y] =>
first [ rewrite (proj2 (Z.ltb_lt x y)) by mlia | rewrite (proj2 (Z.ltb_ge x y)) by mlia ]
| |- context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) by mlia | rewrite (proj2 (Z.leb_gt x y)) by mlia ]
end; cbn [andb orb negb].

Lemma b2z_word_nez : forall b, negb (bv_eqb (Z_to_bv 64 (Z.b2z b)) (Z_to_bv 64 0)) = b.
Proof. intros [|]; reflexivity. Qed.
Lemma b2z_word_eqz : forall b, bv_eqb (Z_to_bv 64 (Z.b2z b)) (Z_to_bv 64 0) = negb b.
Proof. intros [|]; reflexivity. Qed.

Ltac zr_pose e := let H := fresh "R" in assert (H : inr64 e) by zrange; unfold inr64 in H.

Ltac zb_masks :=
repeat match goal with
| |- context [Z.land ?x ?m] =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
| H : context [Z.land ?x ?m] |- _ =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z in H by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
end.

Ltac pose_word_ranges :=
repeat match goal with
| |- context [bv_unsigned ?x] =>
lazymatch goal with
| _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
| _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
end
| _ : context [bv_unsigned ?x] |- _ =>
lazymatch goal with
| _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
| _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
end
end.

Ltac zb_bits_norm :=
intros;
rewrite ?Z.land_lor_distr_l in *;
rewrite ?Z.lor_eq_0_iff in *;
rewrite ?zb_lxor_eq0 in *;
zb_masks;
rewrite ?Z.shiftr_div_pow2 in * by lia;
zb_fold_lits.

Ltac blia := zb_bits_norm; pose_word_ranges; mlia. Ltac mkr__blia_6 := zb_bits_norm; pose_word_ranges; mlia.

Ltac decide_tests_b :=
repeat match goal with
| |- context [Z.eqb ?x ?y] =>
first [ rewrite (proj2 (Z.eqb_eq x y)) by blia | rewrite (proj2 (Z.eqb_neq x y)) by blia ]
| |- context [Z.ltb ?x ?y] =>
first [ rewrite (proj2 (Z.ltb_lt x y)) by blia | rewrite (proj2 (Z.ltb_ge x y)) by blia ]
| |- context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) by blia | rewrite (proj2 (Z.leb_gt x y)) by blia ]
end; cbn [andb orb negb].

Lemma zb_negb_eqb0 : forall x, (0 <= x)%Z -> negb (x =? 0)%Z = (0 <? x)%Z.
Proof. intros x Hx. destruct (Z.eqb_spec x 0); destruct (Z.ltb_spec0 0 x); cbn; try reflexivity; exfalso; lia. Qed.

Lemma Z_to_bv_eqm : forall e1 e2, (e1 mod 2^64 = e2 mod 2^64)%Z -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof. intros e1 e2 H. rewrite <- (Z_to_bv_mod64 e1), <- (Z_to_bv_mod64 e2), H. reflexivity. Qed.

Ltac word_eq_tac :=
first [ exact eq_refl
| f_equal; lia
| apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
| apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
End ZBridge.

From Stdlib Require Import ZArith NArith List Bool.
From stdpp Require Import base decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From Ltac2 Require Import Ltac2 Constr Control Message.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Ltac gw_vm_refl := lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end.
Ltac gw_ro_bytes_vm :=
lazymatch goal with |- ro_bytes ?segs ?a ?bs => let l := eval vm_compute in bs in change (ro_bytes segs a l) end;
cbn [ro_bytes Z.add Pos.add Pos.succ]; repeat split; try exact I; unfold ro_byte; gw_vm_refl.
Ltac gw_side := first [ gw_ro_bytes_vm | gw_vm_refl | vm_compute; first [ reflexivity | split; discriminate | discriminate ] ].

Ltac2 gw_has_prefix (s : string) (p : string) : bool :=
if Int.lt (String.length s) (String.length p) then false else String.equal (String.sub s 0 (String.length p)) p.
Ltac2 gw_is_fact_name (id : ident) : bool :=
let s := Ident.to_string id in
List.exist (gw_has_prefix s) ["D_"; "E_"; "ANCH_"; "LINK_"; "RNG_"; "AL_"; "LAY_"; "JTL_"; "ROM_"].

Ltac2 gw_mod_of (rep : constr) : ident list :=
match Constr.Unsafe.kind rep with
| Constr.Unsafe.Constant k _ => let p := Env.path (Std.ConstRef k) in List.firstn (Int.sub (List.length p) 1) p
| _ => Control.throw (Tactic_failure (Some (Message.of_string "gw_by_name: the module locator must be a constant, e.g. GwI.segs")))
end.
Ltac2 gw_mod_lookup (m : ident list) (id : ident) : constr option :=
match Env.get (List.append m [id]) with
| Some r => Some (Env.instantiate r)
| None => None
end.
Ltac2 gw_is_prop (c : constr) : bool := Constr.equal (Constr.type (Constr.type c)) 'Prop.
Ltac2 gw_value (c : constr) : constr :=
if gw_is_prop c then c else
match Constr.Unsafe.kind c with
| Constr.Unsafe.Constant k _ => Std.eval_unfold [(Std.ConstRef k, Std.AllOccurrences)] c
| _ => c
end.

Ltac2 rec gw_img_prefix (m : ident list) (t : constr) (ty : constr) : constr * constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match gw_mod_lookup m id with
| Some c => let c := gw_value c in gw_img_prefix m constr:($t $c) (Constr.Unsafe.substnl [c] 0 rest)
| None =>
if gw_is_fact_name id then
let bty := Constr.Binder.type b in
let h := '(ltac:(gw_side) : $bty) in
gw_img_prefix m constr:($t $h) (Constr.Unsafe.substnl [h] 0 rest)
else (t, ty)
end
| None => (t, ty)
end
| _ => (t, ty)
end.

Ltac2 gw_try_exact (t : constr) : unit := ltac1:(t |- exact t) (Ltac1.of_constr t).
Ltac2 gw_next (t : constr) (ty : constr) (e : exn) (k : constr -> constr -> 'a) : 'a :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in k constr:($t $h) (Constr.Unsafe.substnl [h] 0 rest)
| Err _ => Control.zero e
end
| None => Control.zero e
end
| Constr.Unsafe.LetIn _ body rest => k t (Constr.Unsafe.substnl [body] 0 rest)
| Constr.Unsafe.Cast c _ _ => k t c
| _ => Control.zero e
end.
Ltac2 rec gw_go (t : constr) (ty : constr) : unit :=
Control.plus (fun () => gw_try_exact t) (fun e => gw_next t ty e gw_go).

Ltac2 gw_by_name0 (rep : constr) (t : constr) : unit :=
let m := gw_mod_of rep in
let (t', ty') := gw_img_prefix m t (Constr.type t) in
gw_go t' ty'.
Ltac gw_by_name rep t :=
let f := ltac2:(rep t |- gw_by_name0 (Option.get (Ltac1.to_constr rep)) (Option.get (Ltac1.to_constr t))) in f rep t.

Ltac2 rec gw_ctx_prefix (t : constr) (ty : constr) : constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in gw_ctx_prefix constr:($t $h) (Constr.Unsafe.substnl [h] 0 rest)
| Err _ => t
end
| None => t
end
| _ => t
end.
Ltac2 gw_ctx0 (t : constr) : unit := let r := gw_ctx_prefix t (Constr.type t) in gw_try_exact r.
Ltac gw_ctx t := let f := ltac2:(t |- gw_ctx0 (Option.get (Ltac1.to_constr t))) in f t.

Ltac2 rec gw_binder_names (ty : constr) : ident list :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id => id :: gw_binder_names rest
| None => gw_binder_names rest
end
| _ => []
end.
Ltac gw_dummy := first [ exact 0%Z | exact (Z_to_bv _ 0) | exact O | exact nil | exact true | exact I ].
Ltac2 rec gw_callee_strip (names : ident list) (cb : constr) (ty : constr) : constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
if List.exist (Ident.equal id) names then
let bty := Constr.Binder.type b in
let arg :=
if Constr.equal (Constr.type bty) 'Prop then None
else if Ident.equal id @base then Some cb
else match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in Some h
| Err _ => Some '(ltac:(gw_dummy) : $bty)
end in
match arg with
| Some a => gw_callee_strip names cb (Constr.Unsafe.substnl [a] 0 rest)
| None =>
if Constr.Unsafe.noccur_between 1 1 rest then gw_callee_strip names cb (Constr.Unsafe.substnl ['I] 0 rest)
else Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "gw_callee_ty: the statement depends on header hypothesis ") (Message.of_ident id))))
end
else ty
| None => ty
end
| _ => ty
end.
Ltac2 gw_callee_ty0 (hdr : constr) (t : constr) (cb : constr) : unit :=
let names := gw_binder_names (Constr.type hdr) in
let r := gw_callee_strip names cb (Constr.type t) in
gw_try_exact r.
Ltac gw_callee_ty hdr t cb :=
let f := ltac2:(hdr t cb |- gw_callee_ty0 (Option.get (Ltac1.to_constr hdr)) (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr cb))) in
f hdr t cb.
