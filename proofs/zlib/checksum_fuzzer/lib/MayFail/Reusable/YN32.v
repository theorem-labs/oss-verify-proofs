(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN32.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_relit : forall segs (p p' : word) (w : bv 32),
fetch_word segs p = Some w -> bv_unsigned p = bv_unsigned p' -> fetch_word segs p' = Some w.
Proof. intros segs p p' w H E. replace p' with p by (apply bv_eq; exact E). exact H. Qed.
End d.
Ltac litF F :=
lazymatch type of F with
| fetch_word ?segs ?p = Some ?w =>
let l := word_lit p in
constr:(fetch_relit segs p l w F ltac:(vm_compute; reflexivity))
end.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition NUL : byte := Z_to_bv 8 0.
Lemma zb_testbit : forall x i j, 0 <= j ->
Z.testbit (HZ.zb x i) j = if j <? 8 then Z.testbit x (8 * Z.of_nat i + j) else false.
Proof.
intros x i j Hj. rewrite HZ.zb_alt, Z.land_spec.
change 255 with (Z.ones 8). rewrite Z.testbit_ones_nonneg by lia.
rewrite Z.shiftr_spec by lia.
destruct (j <? 8) eqn:E.
- rewrite andb_true_r. f_equal. lia.
- apply andb_false_r.
Qed.
Lemma zb_eq_bits : forall x i y i',
(forall j, 0 <= j < 8 -> Z.testbit x (8 * Z.of_nat i + j) = Z.testbit y (8 * Z.of_nat i' + j)) ->
HZ.zb x i = HZ.zb y i'.
Proof.
intros x i y i' H. apply Z.bits_inj'. intros j Hj.
rewrite !zb_testbit by lia.
destruct (j <? 8) eqn:E; [|reflexivity].
apply Z.ltb_lt in E. apply H. lia.
Qed.
Lemma zb_eq0_bits : forall x i,
(forall j, 0 <= j < 8 -> Z.testbit x (8 * Z.of_nat i + j) = false) ->
HZ.zb x i = 0.
Proof.
intros x i H. apply Z.bits_inj'. intros j Hj.
rewrite zb_testbit, Z.bits_0 by lia.
destruct (j <? 8) eqn:E; [|reflexivity].
apply Z.ltb_lt in E. apply H. lia.
Qed.
Lemma zb_u64 : forall z i, (i < 8)%nat -> HZ.zb (bv_unsigned (Z_to_bv 64 z)) i = HZ.zb z i.
Proof.
intros z i Hi. rewrite Z_to_bv_unsigned. apply zb_eq_bits. intros j Hj.
apply bv_wrap_spec_low. lia.
Qed.
Lemma zb_wrap32_lo : forall z i, (i < 4)%nat -> HZ.zb (bv_wrap 32 z) i = HZ.zb z i.
Proof.
intros z i Hi. apply zb_eq_bits. intros j Hj. apply bv_wrap_spec_low. lia.
Qed.
Lemma zb_wrap32_hi : forall z i, (4 <= i)%nat -> HZ.zb (bv_wrap 32 z) i = 0.
Proof.
intros z i Hi. apply zb_eq0_bits. intros j Hj. apply bv_wrap_spec_high. lia.
Qed.
Lemma zb_swrap32 : forall z i, (i < 4)%nat -> HZ.zb (bv_swrap 32 z) i = HZ.zb z i.
Proof.
intros z i Hi. apply zb_eq_bits. intros j Hj.
rewrite bv_swrap_spec by lia.
destruct (Z_lt_dec (8 * Z.of_nat i + j) 31) as [Hl|Hn].
- rewrite bool_decide_eq_true_2 by lia. reflexivity.
- rewrite bool_decide_eq_false_2 by lia. f_equal. lia.
Qed.
Lemma zb_lor : forall u w i, HZ.zb (Z.lor u w) i = Z.lor (HZ.zb u i) (HZ.zb w i).
Proof.
intros u w i. apply Z.bits_inj'. intros j Hj.
rewrite Z.lor_spec, !zb_testbit, Z.lor_spec by lia.
destruct (j <? 8); reflexivity.
Qed.
Lemma zb_shiftr : forall x k i,
HZ.zb (Z.shiftr x (8 * Z.of_nat k)) i = HZ.zb x (i + k).
Proof.
intros x k i. apply zb_eq_bits. intros j Hj.
rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.
Lemma zb_shiftl_hi : forall x k i, (k <= i)%nat ->
HZ.zb (Z.shiftl x (8 * Z.of_nat k)) i = HZ.zb x (i - k).
Proof.
intros x k i Hk. apply zb_eq_bits. intros j Hj.
rewrite Z.shiftl_spec by lia. f_equal. lia.
Qed.
Lemma zb_shiftl_lo : forall x k i, (i < k)%nat ->
HZ.zb (Z.shiftl x (8 * Z.of_nat k)) i = 0.
Proof.
intros x k i Hk. apply zb_eq0_bits. intros j Hj.
apply Z.shiftl_spec_low. lia.
Qed.
Lemma zb_shr8  : forall x i, HZ.zb (Z.shiftr x 8) i = HZ.zb x (i + 1).
Proof. intros. exact (zb_shiftr x 1 i). Qed.
Lemma zb_shr16 : forall x i, HZ.zb (Z.shiftr x 16) i = HZ.zb x (i + 2).
Proof. intros. exact (zb_shiftr x 2 i). Qed.
Lemma zb_shr24 : forall x i, HZ.zb (Z.shiftr x 24) i = HZ.zb x (i + 3).
Proof. intros. exact (zb_shiftr x 3 i). Qed.
Lemma zb_shl8_hi  : forall x i, (1 <= i)%nat -> HZ.zb (Z.shiftl x 8) i = HZ.zb x (i - 1).
Proof. intros. exact (zb_shiftl_hi x 1 i H). Qed.
Lemma zb_shl16_hi : forall x i, (2 <= i)%nat -> HZ.zb (Z.shiftl x 16) i = HZ.zb x (i - 2).
Proof. intros. exact (zb_shiftl_hi x 2 i H). Qed.
Lemma zb_shl24_hi : forall x i, (3 <= i)%nat -> HZ.zb (Z.shiftl x 24) i = HZ.zb x (i - 3).
Proof. intros. exact (zb_shiftl_hi x 3 i H). Qed.
Lemma zb_shl8_lo  : forall x i, (i < 1)%nat -> HZ.zb (Z.shiftl x 8) i = 0.
Proof. intros. exact (zb_shiftl_lo x 1 i H). Qed.
Lemma zb_shl16_lo : forall x i, (i < 2)%nat -> HZ.zb (Z.shiftl x 16) i = 0.
Proof. intros. exact (zb_shiftl_lo x 2 i H). Qed.
Lemma zb_shl24_lo : forall x i, (i < 3)%nat -> HZ.zb (Z.shiftl x 24) i = 0.
Proof. intros. exact (zb_shiftl_lo x 3 i H). Qed.
Lemma zb_bytes_in : forall (l : list byte) i, (i < length l)%nat ->
HZ.zb (bytes_le_to_Z l) i = bv_unsigned (nth i l NUL).
Proof. intros. apply zb_of_bytes. assumption. Qed.
Lemma zb_bytes_out : forall (l : list byte) i, (length l <= i)%nat ->
HZ.zb (bytes_le_to_Z l) i = 0.
Proof.
intros l i Hi. unfold HZ.zb.
pose proof (bytes_le_to_Z_nonneg l) as H0.
pose proof (bytes_le_to_Z_bound l) as H1.
rewrite Z.div_small; [reflexivity|].
split; [lia|].
eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zb_byte0 : forall b : byte, HZ.zb (bv_unsigned b) 0 = bv_unsigned b.
Proof.
intros b. unfold HZ.zb. pose proof (u8_range b).
change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. apply Z.mod_small. lia.
Qed.
Lemma le_bytes4_of_zb : forall z (c0 c1 c2 c3 : byte),
HZ.zb z 0 = bv_unsigned c0 -> HZ.zb z 1 = bv_unsigned c1 ->
HZ.zb z 2 = bv_unsigned c2 -> HZ.zb z 3 = bv_unsigned c3 ->
Z_to_le_bytes 4 z = [c0; c1; c2; c3].
Proof.
intros z c0 c1 c2 c3 H0 H1 H2 H3.
assert (E : forall y (c : byte), HZ.zb y 0 = bv_unsigned c -> Z_to_bv 8 y = c).
{ intros y c Hy. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hy.
unfold HZ.zb. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity. }
cbn [Z_to_le_bytes].
rewrite (E z c0 H0).
rewrite (E (Z.shiftr z 8) c1) by (rewrite zb_shr8; exact H1).
rewrite (E (Z.shiftr (Z.shiftr z 8) 8) c2) by (rewrite !zb_shr8; exact H2).
rewrite (E (Z.shiftr (Z.shiftr (Z.shiftr z 8) 8) 8) c3) by (rewrite !zb_shr8; exact H3).
reflexivity.
Qed.
Lemma le_bytes1_of_zb : forall z (c0 : byte),
HZ.zb z 0 = bv_unsigned c0 -> Z_to_le_bytes 1 z = [c0].
Proof.
intros z c0 H0. cbn [Z_to_le_bytes]. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned, <- H0.
unfold HZ.zb. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity.
Qed.
Definition lwv (l : list byte) : word := v_lw (Z_to_bv 64 (bytes_le_to_Z l)).
End g.
Ltac zbsimp :=
repeat first
[ rewrite zb_u64 by lia
| rewrite zb_swrap32 by lia
| rewrite zb_wrap32_lo by lia
| rewrite zb_wrap32_hi by lia
| rewrite zb_lor
| rewrite zb_shr8 | rewrite zb_shr16 | rewrite zb_shr24
| rewrite zb_shl8_hi by lia | rewrite zb_shl16_hi by lia | rewrite zb_shl24_hi by lia
| rewrite zb_shl8_lo by lia | rewrite zb_shl16_lo by lia | rewrite zb_shl24_lo by lia
| rewrite zb_bytes_in by (cbn [length]; lia)
| rewrite zb_bytes_out by (cbn [length]; lia)
| rewrite zb_byte0 ];
cbn [nth Nat.add Nat.sub]; rewrite ?Z.lor_0_r, ?Z.lor_0_l; try reflexivity.
Ltac zb4 := unfold lwv, v_lw, v_or, v_slli, v_srli, v_srliw, word_to_le_bytes;
apply le_bytes4_of_zb; zbsimp.
Ltac zb1 := unfold lwv, v_lw, v_or, v_slli, v_srli, v_srliw, word_to_le_bytes;
apply le_bytes1_of_zb; zbsimp.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sw_lwv : forall w0 w1 w2 w3 : byte,
word_to_le_bytes 4 (lwv [w0; w1; w2; w3]) = [w0; w1; w2; w3].
Proof. intros. zb4. Qed.
Lemma sb_lwv : forall w0 w1 w2 w3 : byte,
word_to_le_bytes 1 (lwv [w0; w1; w2; w3]) = [w0].
Proof. intros. zb1. Qed.
Lemma sb_lwv_sr8 : forall w0 w1 w2 w3 : byte,
word_to_le_bytes 1 (v_srli (lwv [w0; w1; w2; w3]) 8) = [w1].
Proof. intros. zb1. Qed.
Lemma sb_lwv_sr16 : forall w0 w1 w2 w3 : byte,
word_to_le_bytes 1 (v_srli (lwv [w0; w1; w2; w3]) 16) = [w2].
Proof. intros. zb1. Qed.
Lemma sb_lbu : forall b : byte, word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros. zb1. Qed.
Lemma sw_merge8 : forall w0 w1 w2 w3 x0 x1 x2 x3 : byte,
word_to_le_bytes 4 (v_or (v_slli (lwv [x0; x1; x2; x3]) 8) (v_srliw (lwv [w0; w1; w2; w3]) 24))
= [w3; x0; x1; x2].
Proof. intros. zb4. Qed.
Lemma sw_merge16 : forall w0 w1 w2 w3 x0 x1 x2 x3 : byte,
word_to_le_bytes 4 (v_or (v_slli (lwv [x0; x1; x2; x3]) 16) (v_srliw (lwv [w0; w1; w2; w3]) 16))
= [w2; w3; x0; x1].
Proof. intros. zb4. Qed.
Lemma sw_merge24 : forall w0 w1 w2 w3 x0 x1 x2 x3 : byte,
word_to_le_bytes 4 (v_or (v_slli (lwv [x0; x1; x2; x3]) 24) (v_srliw (lwv [w0; w1; w2; w3]) 8))
= [w1; w2; w3; x0].
Proof. intros. zb4. Qed.
Lemma len4_inv : forall l : list byte, length l = 4%nat ->
exists a b c e, l = [a; b; c; e].
Proof.
intros l Hl.
destruct l as [|a [|b [|c [|e [|f l]]]]]; cbn in Hl; try discriminate.
exists a, b, c, e. reflexivity.
Qed.
Lemma sw_lwv_l : forall l, length l = 4%nat -> word_to_le_bytes 4 (lwv l) = l.
Proof. intros l Hl. destruct (len4_inv l Hl) as (a & b & c & e & ->). apply sw_lwv. Qed.
Lemma sb_lwv_l : forall l, length l = 4%nat -> word_to_le_bytes 1 (lwv l) = [nth 0 l NUL].
Proof. intros l Hl. destruct (len4_inv l Hl) as (a & b & c & e & ->). apply sb_lwv. Qed.
Lemma sb_lwv_sr8_l : forall l, length l = 4%nat ->
word_to_le_bytes 1 (v_srli (lwv l) 8) = [nth 1 l NUL].
Proof. intros l Hl. destruct (len4_inv l Hl) as (a & b & c & e & ->). apply sb_lwv_sr8. Qed.
Lemma sb_lwv_sr16_l : forall l, length l = 4%nat ->
word_to_le_bytes 1 (v_srli (lwv l) 16) = [nth 2 l NUL].
Proof. intros l Hl. destruct (len4_inv l Hl) as (a & b & c & e & ->). apply sb_lwv_sr16. Qed.
Lemma sw_merge8_l : forall w x, length w = 4%nat -> length x = 4%nat ->
word_to_le_bytes 4 (v_or (v_slli (lwv x) 8) (v_srliw (lwv w) 24)) = skipn 3 w ++ firstn 3 x.
Proof.
intros w x Hw Hx. destruct (len4_inv w Hw) as (a & b & c & e & ->).
destruct (len4_inv x Hx) as (a' & b' & c' & e' & ->). apply sw_merge8.
Qed.
Lemma sw_merge16_l : forall w x, length w = 4%nat -> length x = 4%nat ->
word_to_le_bytes 4 (v_or (v_slli (lwv x) 16) (v_srliw (lwv w) 16)) = skipn 2 w ++ firstn 2 x.
Proof.
intros w x Hw Hx. destruct (len4_inv w Hw) as (a & b & c & e & ->).
destruct (len4_inv x Hx) as (a' & b' & c' & e' & ->). apply sw_merge16.
Qed.
Lemma sw_merge24_l : forall w x, length w = 4%nat -> length x = 4%nat ->
word_to_le_bytes 4 (v_or (v_slli (lwv x) 24) (v_srliw (lwv w) 8)) = skipn 1 w ++ firstn 1 x.
Proof.
intros w x Hw Hx. destruct (len4_inv w Hw) as (a & b & c & e & ->).
destruct (len4_inv x Hx) as (a' & b' & c' & e' & ->). apply sw_merge24.
Qed.
End h.
Ltac gr :=
repeat first [ rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero.
Ltac rwH :=
repeat match goal with
| H : getr ?rg ?r = _ |- context [getr ?rg ?r] => rewrite H
end.
Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma v_addi_lit : forall z k : Z, v_addi (Z_to_bv 64 z) k = Z_to_bv 64 (z + k).
Proof.
intros z k. unfold v_addi. apply bv_eq.
rewrite !Z_to_bv_unsigned. apply bv_wrap_add_idemp_l.
Qed.
Lemma v_andi_lit : forall m k : Z, 0 <= m < 2^64 -> 0 <= k < 2^64 ->
v_andi (Z_to_bv 64 m) k = Z_to_bv 64 (Z.land m k).
Proof.
intros m k Hm Hk. unfold v_andi. rewrite u_Z2bv by lia.
f_equal. f_equal. apply Z.mod_small. change (bv_modulus 64) with (2^64). lia.
Qed.
Lemma and3_mod4 : forall z : Z, v_andi (Z_to_bv 64 z) 3 = Z_to_bv 64 (z mod 4).
Proof.
intros z. unfold v_andi. rewrite Z_to_bv_unsigned. f_equal.
change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
unfold bv_wrap. change (bv_modulus 64) with (4 * 2^62). change (2^2) with 4.
apply Z.mod_mod_divide. exists (2^62). lia.
Qed.
Lemma v_add_lit : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma v_sub_lit : forall a b, v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
intros a b. unfold v_sub. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite <- Zminus_mod. reflexivity.
Qed.
End o.
Ltac val := gr; rwH; imm_norm; rewrite ?v_addi_lit, ?v_add_lit, ?v_sub_lit; first [ reflexivity | f_equal; lia | idtac ].
Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma land_pow2_cases : forall m k, 0 <= k ->
Z.land m (2^k) = 0 \/ Z.land m (2^k) = 2^k.
Proof.
intros m k Hk.
destruct (Z.testbit m k) eqn:B; [right|left];
apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
- destruct (Z.eqb_spec k i) as [<-|Hne]; [rewrite B; reflexivity| apply andb_false_r].
- rewrite Z.bits_0. destruct (Z.eqb_spec k i) as [<-|Hne]; [rewrite B; reflexivity| apply andb_false_r].
Qed.
Lemma mod_pow2_S : forall m k, 0 <= k ->
m mod 2^(k+1) = Z.land m (2^k) + m mod 2^k.
Proof.
intros m k Hk.
assert (Hdisj : Z.land (Z.land m (2^k)) (m mod 2^k) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0, !Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec k i) as [<-|Hne].
- rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
- rewrite andb_false_r. reflexivity. }
rewrite (Z.add_nocarry_lxor _ _ Hdisj), (Z.lxor_lor _ _ Hdisj).
apply Z.bits_inj'. intros i Hi.
rewrite Z.lor_spec, Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z_lt_le_dec i (k+1)) as [Hl|Hh].
- rewrite Z.mod_pow2_bits_low by lia.
destruct (Z.eqb_spec k i) as [<-|Hne].
+ rewrite Z.mod_pow2_bits_high by lia. rewrite andb_true_r, orb_false_r. reflexivity.
+ rewrite Z.mod_pow2_bits_low by lia. rewrite andb_false_r. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia.
destruct (Z.eqb_spec k i) as [<-|Hne]; [lia|]. rewrite andb_false_r. reflexivity.
Qed.
Lemma land1_cases : forall m, Z.land m 1 = 0 \/ Z.land m 1 = 1.
Proof. intros m. exact (land_pow2_cases m 0 ltac:(lia)). Qed.
Lemma land2_cases : forall m, Z.land m 2 = 0 \/ Z.land m 2 = 2.
Proof. intros m. exact (land_pow2_cases m 1 ltac:(lia)). Qed.
Lemma land4_cases : forall m, Z.land m 4 = 0 \/ Z.land m 4 = 4.
Proof. intros m. exact (land_pow2_cases m 2 ltac:(lia)). Qed.
Lemma land8_cases : forall m, Z.land m 8 = 0 \/ Z.land m 8 = 8.
Proof. intros m. exact (land_pow2_cases m 3 ltac:(lia)). Qed.
Lemma land16_cases : forall m, Z.land m 16 = 0 \/ Z.land m 16 = 16.
Proof. intros m. exact (land_pow2_cases m 4 ltac:(lia)). Qed.
Lemma mod2_split : forall m, m mod 2 = Z.land m 1.
Proof.
intros m. pose proof (mod_pow2_S m 0 ltac:(lia)) as H.
change (2^(0+1)) with 2 in H. change (2^0) with 1 in H. rewrite Z.mod_1_r in H. lia.
Qed.
Lemma mod4_split : forall m, m mod 4 = Z.land m 2 + m mod 2.
Proof. intros m. exact (mod_pow2_S m 1 ltac:(lia)). Qed.
Lemma mod8_split : forall m, m mod 8 = Z.land m 4 + m mod 4.
Proof. intros m. exact (mod_pow2_S m 2 ltac:(lia)). Qed.
Lemma mod16_split : forall m, m mod 16 = Z.land m 8 + m mod 8.
Proof. intros m. exact (mod_pow2_S m 3 ltac:(lia)). Qed.
Lemma mod32_split : forall m, m mod 32 = Z.land m 16 + m mod 16.
Proof. intros m. exact (mod_pow2_S m 4 ltac:(lia)). Qed.
Lemma firstn_app_firstn_skipn : forall {A} (l : list A) i k,
firstn i l ++ firstn k (skipn i l) = firstn (i + k) l.
Proof.
intros A l i k. rewrite firstn_skipn_comm.
rewrite <- (firstn_skipn i (firstn (i + k) l)) at 2.
rewrite firstn_firstn. replace (Init.Nat.min i (i + k)) with i by lia. reflexivity.
Qed.
Lemma wbytes_app : forall m (a : word) xs ys,
wbytes m a (xs ++ ys) = wbytes (wbytes m a xs) (a + nat_to_word (length xs))%bv ys.
Proof.
intros m a xs; revert m a. induction xs as [|x xs IH]; intros m a ys.
- cbn. rewrite word_add_0. reflexivity.
- cbn [wbytes app length]. rewrite IH. f_equal.
rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.
Lemma rdn_skipn : forall segs m i (a : word) n l,
rdn segs m a n = Some l -> (i <= n)%nat ->
rdn segs m (a + nat_to_word i)%bv (n - i) = Some (skipn i l).
Proof.
intros segs m i. induction i as [|i IH]; intros a n l H Hi.
- rewrite word_add_0, Nat.sub_0_r. exact H.
- destruct n as [|n]; [lia|]. cbn [rdn] in H.
destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
destruct (rdn segs m (a + 1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-. cbn [skipn Nat.sub].
replace (a + nat_to_word (S i))%bv with (a + 1 + nat_to_word i)%bv
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply IH; [exact Er| lia].
Qed.
Lemma rdn_sub : forall segs m (a : word) n l i k,
rdn segs m a n = Some l -> (i + k <= n)%nat ->
rdn segs m (a + nat_to_word i)%bv k = Some (firstn k (skipn i l)).
Proof.
intros segs m a n l i k H Hik.
eapply rdn_firstn; [eapply rdn_skipn; [exact H|lia] | lia].
Qed.
Lemma ble_u64 : forall l : list byte, (length l <= 8)%nat ->
bytes_le_to_Z l = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z l)).
Proof.
intros l Hl.
pose proof (bytes_le_to_Z_nonneg l) as H0.
pose proof (bytes_le_to_Z_bound l) as H1.
assert (2 ^ (8 * Z.of_nat (length l)) <= 2^64) by (apply Z.pow_le_mono_r; lia).
rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma step_lw_l : forall segs regs pc mem rom w rd rs (imm : bv 12) l,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some l ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (lwv l)) (v_addi pc 4) mem rom).
Proof.
intros * Hf He Hd Hr.
eapply step_lw; [exact Hf | exact He | exact Hd | exact Hr |].
apply ble_u64. rewrite (rdn_length _ _ _ _ _ Hr). lia.
Qed.
Lemma step_sb_l : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a : Z) (b : byte),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a ->
word_to_le_bytes 1 (getr regs rs2) = [b] ->
RiscvSemantics.store_ok segs mem (Z_to_bv 64 a) 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4) (wbytes mem (Z_to_bv 64 a) [b]) rom).
Proof.
intros * Hf He Hd Ha Hb Hok.
rewrite (step_sb segs regs pc mem rom w rs1 rs2 imm Hf He Hd) by (rewrite Ha; exact Hok).
rewrite Ha, Hb. reflexivity.
Qed.
Lemma step_sw_l : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a : Z) (l : list byte),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a ->
word_to_le_bytes 4 (getr regs rs2) = l ->
RiscvSemantics.store_ok segs mem (Z_to_bv 64 a) 4%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4) (wbytes mem (Z_to_bv 64 a) l) rom).
Proof.
intros * Hf He Hd Ha Hl Hok.
rewrite (step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd) by (rewrite Ha; exact Hok).
rewrite Ha, Hl. reflexivity.
Qed.
Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_or (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros * Hf He Hd Hrd Hv.
rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
Lemma step_srliw_at : forall segs regs pc mem rom w rd rs (sh : bv 5) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 ALU_SRL rd rs sh, 4%Z) ->
bv_eqb rd 0 = false ->
v_srliw (getr regs rs) (bv_unsigned sh) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros * Hf He Hd Hrd Hv.
rewrite (step_srliw segs regs pc mem rom w rd rs sh Hf He Hd), Hrd, Hv. reflexivity.
Qed.
Lemma ltu_w : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma eqb_w : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.
End q.
Ltac brc :=
gr; rwH; cbn [branch_taken];
rewrite ?ltu_w, ?eqb_w by lia;
first [ reflexivity
| apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
| apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
| apply negb_true_iff; first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia]
| apply negb_false_iff; first [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia] ].
Ltac sv F D vv := let F' := litF F in stepiv F' D vv val.
Ltac svor F0 D vv := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | val ]
| step_simpl ].
Ltac svsrw F0 D vv := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_srliw_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | val ]
| step_simpl ].
Ltac stepbt F0 D := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | brc ]
| step_simpl ].
Ltac stepbf F0 D := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | brc ]
| step_simpl ].
Ltac stepret F0 D := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_jalr_x0; [ exact F | reflexivity | exact D | gr; reflexivity ]
| step_simpl; imm_norm ].
Ltac stepj' F0 D := let F := litF F0 in stepj F D.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tblw (t : ctable) (pc : Z) : Z := match clookup t pc with Some w => w | None => 0 end.
Definition instr_imm (w : Z) : Z :=
match decode_any (Z_to_bv 32 w) with
| Some (Lui _ i, _) => bv_unsigned i | Some (Auipc _ i, _) => bv_unsigned i
| Some (Jal _ i, _) => bv_unsigned i | Some (Jalr _ _ i, _) => bv_unsigned i
| Some (Load _ _ _ _ i, _) => bv_unsigned i | Some (Store _ _ _ i, _) => bv_unsigned i
| Some (OpImm _ _ _ i, _) => bv_unsigned i | Some (OpImm32 _ _ i, _) => bv_unsigned i
| _ => 0
end.
End s.
