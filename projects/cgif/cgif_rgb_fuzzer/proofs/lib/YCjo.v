(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx
YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI01 YI03 YI04 YP14 YI08 YI0c YI0g YK1j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sext32_low : forall x, 0 <= x < 2 ^ 32 -> (zcanon (bv_swrap 32 (x mod 2 ^ 32))) mod 2 ^ 32 = x.
Proof.
intros x Hx. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
Lemma denot_add0 : forall E x, sv_denot E (SAlu ALU_ADD x (SLit 0)) = sv_denot E x.
Proof.
intros E x. rewrite (denot_lit_U E (SAlu ALU_ADD x (SLit 0))), (denot_lit_U E x). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Lemma U_sext32_low : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) mod 2 ^ 32 = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32). apply sext32_low. exact Hv.
Qed.
Lemma U_mulw_small : forall E a b x y,
U E a = x -> U E b = y -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 <= x * y < 2 ^ 31 ->
U E (SMdw M_MUL a b) = x * y.
Proof.
intros E a b x y Hx Hy Rx Ry Rxy. rewrite U_of_S, S_SMdw. cbn [zmd_raw]. rewrite Hx, Hy.
rewrite !Z.mod_small by lia. rewrite swrap32_id by lia. apply wrap64_id. unfold M64. lia.
Qed.
Lemma U_zext32_shifts : forall E a x,
U E a = x -> 0 <= x < 2 ^ 32 -> U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = x.
Proof.
intros E a x Hx Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, !U_SLit.
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 32)) by (unfold M64; change (2 ^ 32) with 4294967296 in *; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma u64_range8 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Lemma byte_mod32 : forall v k, 0 <= v -> (k < 4)%nat ->
Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)) = Z_to_bv 8 (le_byte (v mod 2 ^ 32) 4 k).
Proof.
intros v k Hv Hk. unfold le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_mod _ (2 ^ 32)) by lia. change 256 with (2 ^ 8). rewrite Z.mod_mod by lia.
rewrite <- !Z.land_ones by lia. rewrite !Z.shiftr_land. rewrite <- !Z.land_assoc.
apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.shiftr_spec by lia.
destruct (Z_lt_le_dec n 8).
- rewrite (Z.ones_spec_low 8 n) by lia. rewrite !Bool.andb_true_r. rewrite Z.ones_spec_low by lia. rewrite Bool.andb_true_r. reflexivity.
- rewrite (Z.ones_spec_high 8 n) by lia. rewrite !Bool.andb_false_r. reflexivity.
Qed.
Lemma val_of_chunk4 : forall segs E mem base off (e : sv) v,
YQ0b.chunk_ok segs E mem base (YQ0b.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem segs mem (base + off) 4 (v mod 2 ^ 32).
Proof.
intros segs E mem base off e v H He Hv k Hk. unfold YQ0b.chunk_ok in H. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len] in H.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. rewrite He in Hb1.
unfold byte_of_word in Hb1. rewrite Z_to_bv_unsigned in Hb1.
unfold bv_wrap, bv_modulus in Hb1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb1. rewrite Z.mod_small in Hb1 by lia.
injection Hb1 as <-. rewrite Hb2. f_equal. apply byte_mod32; lia.
Qed.
Definition LAY_Rgb11 : layout_t :=
[(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 4%N); (36, 4%N); (40, 2%N); (42, 2%N); (44, 2%N); (48, 8%N); (56, 4%N)].
End c.
Lemma U_sext32_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Z.mod_small by lia. rewrite swrap32_id by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma fmt_test_false : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
(U E (SLit 1) <? U E (SAluw ALU_ADD (SExt true 32 (SOff n 0)) (SLit (-3)))) = false -> v = 3 \/ v = 4.
Proof.
intros E n v Hn Hv Hc. apply Z.ltb_ge in Hc. rewrite U_lit in Hc by lia.
rewrite U_SAluw in Hc. cbn [zalu_raw] in Hc. rewrite (U_sext32_low E n v Hn Hv), U_SLit in Hc.
change (zcanon (-3) mod 2 ^ 32) with 4294967293 in Hc.
unfold bv_swrap, bv_wrap in Hc.
change (bv_modulus 32) with 4294967296 in Hc. change (bv_half_modulus 32) with 2147483648 in Hc. change (bv_modulus 64) with 18446744073709551616 in Hc.
pose proof (Z.div_mod (v + 4294967293 + 2147483648) 4294967296 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (v + 4294967293 + 2147483648) 4294967296 ltac:(lia)) as B1.
set (r1 := (v + 4294967293 + 2147483648) mod 4294967296) in *.
set (q1 := (v + 4294967293 + 2147483648) / 4294967296) in *.
pose proof (Z.div_mod (r1 - 2147483648) 18446744073709551616 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (r1 - 2147483648) 18446744073709551616 ltac:(lia)) as B2.
set (r2 := (r1 - 2147483648) mod 18446744073709551616) in *.
set (q2 := (r1 - 2147483648) / 18446744073709551616) in *.
clearbody r1 q1 r2 q2. clear Hn. lia.
Qed.
Lemma U_HW : forall E nh nw H W, ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W -> 0 <= H < 2 ^ 16 -> 0 <= W < 2 ^ 16 -> 0 <= H * W < 2 ^ 31 ->
U E (SMdw M_MUL (SOff nh 0) (SOff nw 0)) = H * W.
Proof.
intros E nh nw H W Hh Hw RH RW RHW. apply U_mulw_small; [apply (U_atom E nh H Hh); lia | apply (U_atom E nw W Hw); lia | lia | lia | lia].
Qed.
Lemma U_fN : forall E nf nh nw fmt H W,
ew E nf = Z_to_bv 64 fmt -> ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W ->
0 <= fmt < 2 ^ 31 -> 0 <= H < 2 ^ 16 -> 0 <= W < 2 ^ 16 -> 0 <= H * W < 2 ^ 31 -> fmt * (H * W) < 2 ^ 32 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SExt true 32 (SOff nf 0)) (SMdw M_MUL (SOff nh 0) (SOff nw 0))) (SLit 32)) (SLit 32)) = fmt * (H * W).
Proof.
intros E nf nh nw fmt H W Hf Hh Hw Rf RH RW RHW RfN. apply U_zext32_shifts; [| lia].
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_sext32_small E nf fmt Hf Rf), (U_HW E nh nw H W Hh Hw RH RW RHW). apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_fN2 : forall E nf nn fmt N, ew E nf = Z_to_bv 64 fmt -> ew E nn = Z_to_bv 64 N -> 0 <= fmt < 2 ^ 31 -> 0 <= N < 2 ^ 31 -> fmt * N < 2 ^ 32 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SOff nf 0) (SOff nn 0)) (SLit 32)) (SLit 32)) = fmt * N.
Proof.
intros E nf nn fmt N Hf Hn Rf RN RfN. apply U_zext32_shifts; [| lia].
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nf fmt Hf), (U_atom E nn N Hn) by lia. apply zcanon_id. unfold M64. nia.
Qed.
Lemma U_HW64 : forall E nh nw H W, ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W -> 0 <= H < 2 ^ 16 -> 0 <= W < 2 ^ 16 ->
U E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = H * W.
Proof.
intros E nh nw H W Hh Hw RH RW. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nh H Hh), (U_atom E nw W Hw) by lia. apply zcanon_id. unfold M64. nia.
Qed.
Lemma arr8_of_present : forall segs (m : word -> option byte) base n,
(forall i, 0 <= i < Z.of_nat n -> exists b, mbyte segs m (base + i) = Some b) ->
exists l, arr8 segs m base l /\ length l = n.
Proof.
intros segs m base n. induction n as [|n IH]; intros Hp.
- exists []. split; [intros j Hj; cbn in Hj; lia | reflexivity].
- destruct (IH ltac:(intros i Hi; apply Hp; lia)) as (l & Hl & Hlen).
destruct (Hp (Z.of_nat n) ltac:(lia)) as [b Hb].
exists (l ++ [bv_unsigned b]). split; [| rewrite length_app; cbn; lia].
intros j Hj. rewrite length_app in Hj. cbn in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge].
+ rewrite app_nth1 by lia. apply Hl. exact Hlt.
+ assert (j = n) by lia. subst j. rewrite app_nth2 by lia. rewrite Hlen, Nat.sub_diag. cbn [nth].
pose proof (bv_unsigned_in_range 8 b) as Hb8. change (bv_modulus 8) with 256 in Hb8.
split; [rewrite Hb, Z_to_bv_bv_unsigned; reflexivity | lia].
Qed.
Definition SZ_f : Z := 2097236. Definition SZ_h : Z := 1572927. Definition SZ_u : Z := 524309.
Lemma malloc_post_perm : forall (old blk2 blkc : list (Z * Z)) res n (Wt : Prop),
Permutation blkc old ->
(res = 0 /\ blk2 = blkc) \/ (res <> 0 /\ res mod 16 = 0 /\ (exists b1 b2, blk2 = b1 ++ (res, n) :: b2 /\ blkc = b1 ++ b2) /\ Wt) ->
Permutation blk2 (old ++ optb res n) /\ (forall x, In x blkc -> In x blk2).
Proof.
intros old blk2 blkc res n Wt HP [[-> ->] | (Hnz & _ & (b1 & b2 & -> & ->) & _)].
- unfold optb. rewrite Z.eqb_refl, app_nil_r. split; [exact HP | intros x Hx; exact Hx].
- unfold optb. destruct (Z.eqb_spec res 0) as [Hc|Hc]; [lia|]. split.
+ eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
eapply Permutation_trans; [| apply Permutation_cons_append]. apply perm_skip. exact HP.
+ intros x Hx. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx].
Qed.
Definition boxP (P : Prop) : Prop := P.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma val_mem4_of_bytes : forall segs (m : word -> option byte) a (b0 b1 b2 b3 : byte),
mbyte segs m a = Some b0 -> mbyte segs m (a + 1) = Some b1 -> mbyte segs m (a + 2) = Some b2 -> mbyte segs m (a + 3) = Some b3 ->
val_mem segs m a 4 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
Proof.
intros segs m a b0 b1 b2 b3 H0 H1 H2 H3.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
set (v := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
assert (Hv : 0 <= v < 2 ^ (8 * Z.of_nat 4)) by (subst v; cbn; lia).
intros k Hk. rewrite le_byte_small by (exact Hv || exact Hk).
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- change (Z.of_nat 0) with 0. rewrite Z.add_0_r, H0, Z.mul_0_r, Z.shiftr_0_r. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. subst v. lia.
- change (Z.of_nat 1) with 1. rewrite H1. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (8 * 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. subst v. lia.
- change (Z.of_nat 2) with 2. rewrite H2. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (8 * 2) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. subst v. lia.
- change (Z.of_nat 3) with 3. rewrite H3. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (8 * 3) with 24. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. subst v. lia.
Qed.
Lemma arr32_of_present : forall segs (m : word -> option byte) base n,
(forall i, 0 <= i < 4 * Z.of_nat n -> exists b, mbyte segs m (base + i) = Some b) ->
exists l, arr32 segs m base l /\ length l = n.
Proof.
intros segs m base n. induction n as [|n IH]; intros Hp.
- exists []. split; [intros j Hj; cbn in Hj; lia | reflexivity].
- destruct (IH ltac:(intros i Hi; apply Hp; lia)) as (l & Hl & Hlen).
destruct (Hp (4 * Z.of_nat n) ltac:(lia)) as [b0 Hb0]. destruct (Hp (4 * Z.of_nat n + 1) ltac:(lia)) as [b1 Hb1].
destruct (Hp (4 * Z.of_nat n + 2) ltac:(lia)) as [b2 Hb2]. destruct (Hp (4 * Z.of_nat n + 3) ltac:(lia)) as [b3 Hb3].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
exists (l ++ [bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3]). split; [| rewrite length_app; cbn; lia].
intros j Hj. rewrite length_app in Hj. cbn in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge].
+ rewrite app_nth1 by lia. apply Hl. exact Hlt.
+ assert (j = n) by lia. subst j. rewrite app_nth2 by lia. rewrite Hlen, Nat.sub_diag. cbn [nth]. split; [| lia].
apply val_mem4_of_bytes; [exact Hb0 | | |].
* replace (base + 4 * Z.of_nat n + 1) with (base + (4 * Z.of_nat n + 1)) by lia. exact Hb1.
* replace (base + 4 * Z.of_nat n + 2) with (base + (4 * Z.of_nat n + 2)) by lia. exact Hb2.
* replace (base + 4 * Z.of_nat n + 3) with (base + (4 * Z.of_nat n + 3)) by lia. exact Hb3.
Qed.
Lemma arr8_Forall : forall segs (m : word -> option byte) base l, arr8 segs m base l -> Forall (fun v => 0 <= v < 256) l.
Proof.
intros segs m base l H. apply Forall_forall. intros v Hv. destruct (In_nth l v 0 Hv) as (i & Hi & <-). exact (proj2 (H i Hi)).
Qed.
Lemma arr8_zero : forall segs (m : word -> option byte) base n,
(forall i, 0 <= i < n -> mbyte segs m (base + i) = Some (Z_to_bv 8 0)) -> arr8 segs m base (repeat 0 (Z.to_nat n)).
Proof.
intros segs m base n H j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [apply H; lia | lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma optb_nz : forall p n, p <> 0 -> optb p n = [(p, n)].
Proof. intros p n Hp. unfold optb. rewrite (proj2 (Z.eqb_neq p 0) Hp). reflexivity. Qed.
Lemma U_add_small_q : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Hx Hy Rx Ry Rs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. lia. Qed.
Lemma U_sll_small_q : forall E a x k, U E a = x -> 0 <= x -> 0 <= k < 64 -> x * 2 ^ k < 2 ^ 64 ->
U E (SAlu ALU_SLL a (SLit k)) = x * 2 ^ k.
Proof.
intros E a x k Hx Rx Hk Rs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, U_lit by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma mod4_of16 : forall a k, a mod 16 = 0 -> (a + 4 * k) mod 4 = 0.
Proof.
intros a k Ha. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists k; lia].
apply Z.mod_divide in Ha; [|lia]. destruct Ha as [q Hq]. exists (4 * q). lia.
Qed.
