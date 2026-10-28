(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c8 X1bj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rd X1oc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1en X1fl.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac zstep0 := zs.

Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

Lemma shl52_land64 : forall f, (0 <= f)%Z -> Z.land (Z.shiftl f 52) 18446744073709551615 = (4503599627370496 * (f mod 4096))%Z.
Proof.
intros f Hf. rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^64)%Z with (4503599627370496 * 4096)%Z.
change (2^52)%Z with 4503599627370496%Z. rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. reflexivity.
Qed.
Lemma land_bit11 : forall f, Z.land f 2048 = (2048 * ((f / 2048) mod 2))%Z.
Proof. intros. change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia. reflexivity. Qed.
Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma fpclassifyl_range : forall x, (0 <= fpclassifyl x <= 4)%Z.
Proof. intros. unfold fpclassifyl. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
change (bv_unsigned (10 : reg)) with 10%Z. lia.
Qed.

Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
split. { apply Z.lor_nonneg. lia. }
pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
rewrite Z.shiftl_mul_pow2 in * by lia.
replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
nia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
pose proof (bytes_le_to_Z_range bs) as HR.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb_spec0 i 8).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. apply andb_false_r. }
rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
- rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le4, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32arr_of_u8arr : forall segs m A bs k,
u8arr segs m A bs -> length bs = (4 * k)%nat ->
exists ws, length ws = k /\ u32arr segs m A ws.
Proof.
intros segs m A bs k [Hb Hw] HL.
assert (G : forall k bs, length bs = (4 * k)%nat -> exists ws, length ws = k /\ u32s ws = bs).
{ clear. induction k as [|k IH]; intros bs HL.
- exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
- destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
- rewrite Hu. exact Hb.
- rewrite Hlen. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed.

Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).
Definition wval (ws : list word) (i : Z) : Z := (bv_unsigned (wnth ws i) mod 4294967296)%Z.

Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. intros ws i Hi Hl. unfold wnth. apply nth_error_nth'. exact Hl. Qed.

Lemma wval_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
wval (upd ws (Z.to_nat i) v) i = (bv_unsigned v mod 4294967296)%Z.
Proof.
intros ws i v Hi Hl. unfold wval, wnth.
pose proof (nth_error_upd_same ws (Z.to_nat i) v Hl) as E.
apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
Qed.
Lemma wval_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
wval (upd ws (Z.to_nat i) v) j = wval ws j.
Proof.
intros ws i j v Hi Hj Hij. unfold wval, wnth.
destruct (Nat.lt_ge_cases (Z.to_nat j) (length ws)) as [Hl|Hl].
- pose proof (nth_error_upd_other ws (Z.to_nat i) (Z.to_nat j) v ltac:(lia)) as E.
rewrite (nth_error_nth' ws (Z_to_bv 64 0) Hl) in E.
apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
- rewrite !nth_overflow by (rewrite ?upd_length; lia). reflexivity.
Qed.
Lemma wval_range : forall ws i, (0 <= wval ws i < 4294967296)%Z.
Proof. intros. unfold wval. apply Z.mod_pos_bound. lia. Qed.

Lemma div1e9_magic : forall x, (0 <= x < 2^64)%Z ->
Z.shiftr (Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64) 11 = (x / 1000000000)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
change (2^64 * 2^11)%Z with (2^75)%Z. change 1000000000%Z with (512 * 1953125)%Z. rewrite <- Z.div_div by lia.
change (2^9)%Z with 512%Z.
set (y := (x / 512)%Z). assert (Hy : (0 <= y < 2^55)%Z) by (subst y; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clearbody y. clear x Hx.
Z.div_mod_to_equations. nia.
Qed.

Lemma sx32_zero : forall w : word, bv_unsigned (sx32 w) = 0%Z <-> (bv_unsigned w mod 4294967296 = 0)%Z.
Proof.
intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
unfold bv_modulus in R. change (2^64)%Z with 18446744073709551616%Z in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
split; intros H; Z.div_mod_to_equations; lia.
Qed.
Lemma sx32_nonzero : forall w : word, bv_unsigned (sx32 w) <> 0%Z <-> (bv_unsigned w mod 4294967296 <> 0)%Z.
Proof. intros w. rewrite sx32_zero. tauto. Qed.

Lemma mulhu_M_range : forall x, (0 <= x < 2^62)%Z ->
(0 <= Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64 < 18446744073709551616)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
split. { apply Z.div_pos; [|lia]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. }
apply Z.div_lt_upper_bound; [lia|].
assert (x / 2^9 < 2^53)%Z by (apply Z.div_lt_upper_bound; lia).
assert (0 <= x / 2^9)%Z by (apply Z.div_pos; lia). nia.
Qed.
