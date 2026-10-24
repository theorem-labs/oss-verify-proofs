(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YP0m YP0e YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition sv_b1s : sv := SExt true 8 (SData 2 1 1).
Definition sv_cl : sv := SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL sv_b1s (SLit 57)) (SLit 49)) (SData 2 0 1).
Definition sv_cl6 : sv := SAlu ALU_ADD sv_cl (SLit 6).
Lemma div_256 : forall x y, 0 <= x < 256 -> (x + 256 * y) / 256 = y.
Proof. intros x y Hx. rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. lia. Qed.
Lemma mod_256 : forall x y, 0 <= x < 256 -> (x + 256 * y) mod 256 = x.
Proof. intros x y Hx. rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia. lia. Qed.
Lemma cfg_word_val : forall b0 b1 rest, cfg_word (b0 :: b1 :: rest) = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof. intros. reflexivity. Qed.
Lemma config_len_val : forall b0 b1 rest,
config_len (b0 :: b1 :: rest) = bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128).
Proof.
intros b0 b1 rest. unfold config_len. rewrite cfg_word_val.
pose proof (u8_range b0) as H0. pose proof (u8_range b1) as H1.
change 32768 with (256 * 128).
rewrite (Z.rem_mul_r (bv_unsigned b0 + 256 * bv_unsigned b1) 256 128) by lia.
rewrite mod_256, div_256 by lia. lia.
Qed.
Lemma count_mode_val : forall b0 b1 rest, count_mode (b0 :: b1 :: rest) = (128 <=? bv_unsigned b1).
Proof.
intros b0 b1 rest. unfold count_mode. rewrite cfg_word_val.
pose proof (u8_range b0) as H0. pose proof (u8_range b1) as H1.
destruct (Z.leb_spec 128 (bv_unsigned b1)); [apply Z.leb_le; lia | apply Z.leb_gt; lia].
Qed.
Lemma config_len_bound : forall data, 0 <= config_len data <= 32767.
Proof. intros data. unfold config_len. pose proof (Z.mod_pos_bound (cfg_word data) 32768 ltac:(lia)). lia. Qed.
Definition sbyte1 (data : list byte) : Z := dbyte data 1 - (if count_mode data then 256 else 0).
Section b.
Variables (E : env) (b0 b1 : byte) (rest : list byte).
Hypothesis Hd : ed E 2 = b0 :: b1 :: rest.
Lemma U_hdr_b0 : U E (SData 2 0 1) = bv_unsigned b0.
Proof.
unfold U. cbn [sv_denot]. unfold data_word. rewrite Hd.
change (bytes_le_to_Z _) with (Z.lor (bv_unsigned b0) (Z.shiftl 0 8)).
rewrite Z.shiftl_0_l, Z.lor_0_r. pose proof (u8_range b0). apply unsigned_lit_small. lia.
Qed.
Lemma U_hdr_b1 : U E (SData 2 1 1) = bv_unsigned b1.
Proof.
unfold U. cbn [sv_denot]. unfold data_word. rewrite Hd.
change (bytes_le_to_Z _) with (Z.lor (bv_unsigned b1) (Z.shiftl 0 8)).
rewrite Z.shiftl_0_l, Z.lor_0_r. pose proof (u8_range b1). apply unsigned_lit_small. lia.
Qed.
Lemma U_b1s : U E sv_b1s = if bv_unsigned b1 <? 128 then bv_unsigned b1 else bv_unsigned b1 + (M64 - 256).
Proof.
pose proof (u8_range b1) as H1.
unfold sv_b1s. rewrite U_SExt, U_hdr_b1. change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small (bv_unsigned b1) 256) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
destruct (Z.ltb_spec (bv_unsigned b1) 128).
- rewrite Z.mod_small by lia. rewrite zcanon_id by (unfold M64; lia). lia.
- replace ((bv_unsigned b1 + 128) mod 256) with (bv_unsigned b1 + 128 - 256)
by (apply Z.mod_unique with (q := 1); lia).
unfold zcanon, M64. symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.
Lemma U_cl : U E sv_cl = config_len (b0 :: b1 :: rest).
Proof.
pose proof (u8_range b0) as H0. pose proof (u8_range b1) as H1.
rewrite config_len_val.
unfold sv_cl. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_b1s, U_hdr_b0, !U_SLit.
change (Z.land (zcanon 57) 63) with 57. change (Z.land (zcanon 49) 63) with 49.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
set (v := if bv_unsigned b1 <? 128 then bv_unsigned b1 else bv_unsigned b1 + (M64 - 256)).
assert (Hv : zcanon (v * 2^57) = (bv_unsigned b1 mod 128) * 2^57).
{ unfold zcanon. subst v. destruct (Z.ltb_spec (bv_unsigned b1) 128).
- rewrite (Z.mod_small (bv_unsigned b1) 128) by lia. apply Z.mod_small. unfold M64. nia.
- replace (bv_unsigned b1 mod 128) with (bv_unsigned b1 - 128)
by (apply Z.mod_unique with (q := 1); lia).
unfold M64. symmetry.
apply Z.mod_unique with (q := bv_unsigned b1 / 128 + (2^57 - 2)); [left; nia|].
assert (bv_unsigned b1 / 128 = 1) by (symmetry; apply Z.div_unique with (r := bv_unsigned b1 - 128); lia).
nia. }
rewrite Hv.
replace (bv_unsigned b1 mod 128 * 2 ^ 57 / 2 ^ 49) with (bv_unsigned b1 mod 128 * 256).
2:{ symmetry. replace (2^57) with (256 * 2^49) by reflexivity.
rewrite Z.mul_assoc. apply Z.div_mul. lia. }
pose proof (Z.mod_pos_bound (bv_unsigned b1) 128 ltac:(lia)) as Hm.
rewrite (zcanon_id (bv_unsigned b1 mod 128 * 256)) by (unfold M64; lia).
rewrite <- Z.lxor_lor.
- rewrite <- Z.add_nocarry_lxor.
+ rewrite zcanon_id by (unfold M64; lia). lia.
+ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 8) as [Hn8|Hn8].
* replace (bv_unsigned b1 mod 128 * 256) with (bv_unsigned b1 mod 128 * 2^8) by reflexivity.
rewrite Z.mul_pow2_bits_low by lia. reflexivity.
* rewrite (Z.bits_above_log2 (bv_unsigned b0)); [apply andb_false_r| lia|].
destruct (Z.eq_dec (bv_unsigned b0) 0) as [->|Hnz]; [cbn; lia|].
assert (Z.log2 (bv_unsigned b0) < 8); [apply Z.log2_lt_pow2; lia| lia].
- apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 8) as [Hn8|Hn8].
+ replace (bv_unsigned b1 mod 128 * 256) with (bv_unsigned b1 mod 128 * 2^8) by reflexivity.
rewrite Z.mul_pow2_bits_low by lia. reflexivity.
+ rewrite (Z.bits_above_log2 (bv_unsigned b0)); [apply andb_false_r| lia|].
destruct (Z.eq_dec (bv_unsigned b0) 0) as [->|Hnz]; [cbn; lia|].
assert (Z.log2 (bv_unsigned b0) < 8); [apply Z.log2_lt_pow2; lia| lia].
Qed.
Lemma U_cl6 : U E sv_cl6 = config_len (b0 :: b1 :: rest) + 6.
Proof.
unfold sv_cl6. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_cl, U_SLit.
pose proof (config_len_bound (b0 :: b1 :: rest)).
change (zcanon 6) with 6. apply zcanon_id. unfold M64. lia.
Qed.
Lemma denot_cl : sv_denot E sv_cl = Z_to_bv 64 (config_len (b0 :: b1 :: rest)).
Proof. rewrite (denot_lit_U E sv_cl), U_cl. reflexivity. Qed.
Lemma denot_cl6 : sv_denot E sv_cl6 = Z_to_bv 64 (config_len (b0 :: b1 :: rest) + 6).
Proof. rewrite (denot_lit_U E _), U_cl6. reflexivity. Qed.
Lemma denot_b1s : sv_denot E sv_b1s = Z_to_bv 64 (sbyte1 (b0 :: b1 :: rest)).
Proof.
pose proof (u8_range b1) as H1.
rewrite (denot_lit_U E sv_b1s), U_b1s. unfold sbyte1, dbyte. cbn [nth]. rewrite count_mode_val.
destruct (Z.ltb_spec (bv_unsigned b1) 128); destruct (Z.leb_spec 128 (bv_unsigned b1)); try lia.
- rewrite Z.sub_0_r. reflexivity.
- apply Z_to_bv64_eq_mod. unfold M64.
replace (bv_unsigned b1 + (2 ^ 64 - 256)) with ((bv_unsigned b1 - 256) + 1 * 2^64) by lia.
apply Z_mod_plus_full.
Qed.
End b.
Lemma bltz_sbyte1 : forall data, (2 <= length data)%nat ->
branch_taken BC_LT (Z_to_bv 64 (sbyte1 data)) (Z_to_bv 64 0) = count_mode data.
Proof.
intros data Hlen. destruct data as [|b0 [|b1 rest]]; try (cbn in Hlen; lia).
pose proof (u8_range b1) as H1.
unfold sbyte1, dbyte. cbn [nth]. rewrite count_mode_val.
unfold branch_taken, bv_lts. rewrite !signed_lit.
change (bv_swrap 64 (zcanon 0)) with 0.
destruct (Z.leb_spec 128 (bv_unsigned b1)).
- replace (zcanon (bv_unsigned b1 - 256)) with (bv_unsigned b1 - 256 + 1 * bv_modulus 64)
by (unfold zcanon; apply Z.mod_unique with (q := -1); change (bv_modulus 64) with (2^64); unfold M64; lia).
rewrite swrap_add_mod. rewrite swrap64_id by (unfold half64; lia). apply Z.ltb_lt. lia.
- rewrite Z.sub_0_r, zcanon_id by (unfold M64; lia). rewrite swrap64_id by (unfold half64; lia).
apply Z.ltb_ge. lia.
Qed.
Lemma bltz_b1s : forall E data, ed E 2 = data -> (2 <= length data)%nat ->
branch_taken BC_LT (sv_denot E sv_b1s) (Z_to_bv 64 0) = count_mode data.
Proof.
intros E data Hd Hlen. destruct data as [|b0 [|b1 rest]] eqn:Ed; try (cbn in Hlen; lia).
rewrite (denot_b1s E b0 b1 rest Hd). apply bltz_sbyte1. exact Hlen.
Qed.
Lemma sbyte1_range : forall data, (2 <= length data)%nat -> -128 <= sbyte1 data <= 127.
Proof.
intros data Hlen. destruct data as [|b0 [|b1 rest]]; try (cbn in Hlen; lia).
pose proof (u8_range b1) as H1.
unfold sbyte1, dbyte. cbn [nth]. rewrite count_mode_val.
destruct (Z.leb_spec 128 (bv_unsigned b1)); lia.
Qed.
Lemma cfg_byte_bound : forall data, 0 <= cfg_byte data <= 255.
Proof.
intros data. unfold cfg_byte. destruct (config_len data =? 0); [lia|].
unfold dbyte. pose proof (u8_range (nth 2 data (Z_to_bv 8 0))). lia.
Qed.
Lemma calls_bound : forall data, (1 <= calls data <= 4)%nat.
Proof.
intros data. unfold calls. pose proof (Z.mod_pos_bound (cfg_byte data) 4 ltac:(lia)). lia.
Qed.
End a.
