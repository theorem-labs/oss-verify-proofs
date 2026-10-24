(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem.

Module DA_Myrk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Definition SYSCALL_ECALL : Z := 0xa285c.     (* [comment removed for export] *)

Lemma bv_modulus_32 : bv_modulus 32 = 2^32. Proof. reflexivity. Qed.
Lemma bv_half_modulus_32 : bv_half_modulus 32 = 2^31. Proof. reflexivity. Qed.
Lemma swrap32_small0 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 (z + 0) = z.
Proof. intros z Hz. rewrite Z.add_0_r. apply bv_swrap_small. rewrite bv_half_modulus_32. lia. Qed.
Lemma swrap32_neg : forall r, 1 <= r <= 2^31 -> bv_swrap 32 (18446744073709551616 - r + 0) = - r.
Proof.
  intros r Hr. unfold bv_swrap, bv_wrap. rewrite bv_half_modulus_32, bv_modulus_32.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.
Lemma swrap32_negneg : forall r, 1 <= r < 2^31 -> bv_swrap 32 (0 - - r mod 18446744073709551616) = r.
Proof.
  intros r Hr. unfold bv_swrap, bv_wrap. rewrite bv_half_modulus_32, bv_modulus_32.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.

Lemma swrap32_negneg2 : forall r, 1 <= r < 2^31 -> bv_swrap 32 (0 - (18446744073709551616 - r)) = r.
Proof.
  intros r Hr. unfold bv_swrap, bv_wrap. rewrite bv_half_modulus_32, bv_modulus_32.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. replace (bv_modulus 64) with (2^64) by reflexivity. rewrite (Z.mod_small z (2^64)) by lia. f_equal. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma errno_ret_neg : forall er, 1 <= er <= 4095 -> errno_ret er = Z_to_bv 64 (18446744073709551616 - er).
Proof.
  intros er Her. unfold errno_ret. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. replace (bv_modulus 64) with 18446744073709551616 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Ltac is_Zlit' a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_addrs_goal :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit' a; is_Zlit' b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  end.

(* [comment removed for export] *)
Ltac blia := first [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ].
End DA_Myrk.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)

Lemma lnot_split : forall b w, Z.lnot (b + 256 * w) = (255 - b) + 256 * Z.lnot w.
Proof. intros. unfold Z.lnot. lia. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  destruct HZ as [HZ1 HZ2]. split.
  - intros E I. apply HZ2 in I. apply I. exact E.
  - intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
    exfalso. apply NI. apply HZ1. exact NE.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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
