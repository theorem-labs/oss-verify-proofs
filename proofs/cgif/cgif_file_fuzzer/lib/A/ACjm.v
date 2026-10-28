(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition NMAX : Z := 2 ^ 64 - 1.
Lemma U_not_gen : forall E a x, U E a = x -> 0 <= x < 2 ^ 64 -> U E (SAlu ALU_XOR a (SLit (-1))) = NMAX - x.
Proof.
intros E a x Ha Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit. change (zcanon (-1)) with (2 ^ 64 - 1).
rewrite lxor_allones by lia. unfold NMAX. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_and16 : forall E a x, U E a = x -> 0 <= x < 65536 -> U E (SAlu ALU_AND a (SLit 65535)) = x.
Proof.
intros E a x Ha Hx. rewrite U_and_lit by lia. rewrite Ha. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma U_mul_small1 : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x * y < 2 ^ 64 -> U E (SMd M_MUL a b) = x * y.
Proof. intros E a b x y Hx Hy Rx Ry Rp. rewrite U_SMd. cbn [zmd_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. nia. Qed.
Lemma U_add_small2 : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Hx Hy Rx Ry Rs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. lia. Qed.
Lemma U_sub_small2 : forall E a b x y, U E a = x -> U E b = y -> 0 <= y <= x -> x < 2 ^ 64 -> U E (SAlu ALU_SUB a b) = x - y.
Proof. intros E a b x y Hx Hy Ry Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. lia. Qed.
Lemma denot_of_U2 : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z <-. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma U_zext_sh : forall E a k x, U E a = x -> 0 <= x < 2 ^ (64 - k) -> 0 < k < 64 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit k)) (SLit k)) = x.
Proof.
intros E a k x Ha Hx Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, Ha.
rewrite (zcanon_id k) by (rewrite M64_val; lia). replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
assert (Hp : 2 ^ (64 - k) * 2 ^ k = 2 ^ 64) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (Hk0 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
rewrite (zcanon_id (x * 2 ^ k)) by (rewrite M64_val; nia).
rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. assert (2 ^ (64 - k) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma U_sltu1_pos : forall E e, 0 < U E e -> U E (SAlu ALU_SLTU e (SLit 1)) = 0.
Proof. intros E e H. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 1) with 1. destruct (Z.ltb_spec (U E e) 1); [lia | reflexivity]. Qed.
Lemma U_xor1_sltu1 : forall E e, 0 < U E e -> U E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU e (SLit 1))) = 1.
Proof. intros E e H. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_sltu1_pos E e H), U_SLit. reflexivity. Qed.
Lemma U_sltu_ge : forall E a b, U E b <= U E a -> U E (SAlu ALU_SLTU a b) = 0.
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. destruct (Z.ltb_spec (U E a) (U E b)); [lia | reflexivity]. Qed.
Lemma U_sltu_lt : forall E a b, U E a < U E b -> U E (SAlu ALU_SLTU a b) = 1.
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. destruct (Z.ltb_spec (U E a) (U E b)); [reflexivity | lia]. Qed.
Lemma U_xor1_bit : forall E a x, U E a = x -> (x = 0 \/ x = 1) -> U E (SAlu ALU_XOR a (SLit 1)) = 1 - x.
Proof. intros E a x Ha [-> | ->]; rewrite U_SAlu; cbn [zalu_raw]; rewrite Ha, U_SLit; reflexivity. Qed.
Lemma U_zext32_lt : forall E a, 0 <= U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) < 2 ^ 32.
Proof.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (zcanon_id 32) by (rewrite M64_val; lia). change (Z.land 32 63) with 32.
pose proof (U_range E a) as Hr. rewrite M64_val in Hr.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon. rewrite M64_val. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)) as Hm. rewrite Z.mod_small by lia. exact Hm.
Qed.
End d.
End c.
