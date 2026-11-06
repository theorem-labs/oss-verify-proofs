(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP03 YI04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma mod256_mod_pow2 : forall x k, 8 <= k -> (x mod 2 ^ k) mod 256 = x mod 256.
Proof.
intros x k Hk. apply Z.mod_mod_divide.
exists (2 ^ (k - 8)). change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma mod256_zcanon : forall x, zcanon x mod 256 = x mod 256.
Proof. intros x. unfold zcanon, M64. apply mod256_mod_pow2. lia. Qed.
Lemma mod256_swrap : forall (w : N) x, 9 <= Z.of_N w -> bv_swrap w x mod 256 = x mod 256.
Proof.
intros w x Hw. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
assert (Hh : 2 ^ Z.of_N w / 2 = 2 ^ (Z.of_N w - 1)).
{ replace (Z.of_N w) with (Z.succ (Z.of_N w - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. rewrite Z.mul_comm. apply Z.div_mul. lia. }
rewrite Hh.
assert (E : 2 ^ (Z.of_N w - 1) mod 256 = 0).
{ apply Z.mod_divide; [lia|]. exists (2 ^ (Z.of_N w - 9)). change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
rewrite Zminus_mod, mod256_mod_pow2 by lia. rewrite (Zplus_mod x), E, Z.add_0_r, Z.sub_0_r, !Z.mod_mod by lia. reflexivity.
Qed.
Lemma mod256_lor : forall a b, Z.lor a b mod 256 = Z.lor (a mod 256) (b mod 256).
Proof. intros a b. change 256 with (2 ^ 8). rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.
Lemma lor_byte : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
intros a b Ha Hb. assert (E : Z.lor a b mod 256 = Z.lor a b) by (rewrite mod256_lor, !Z.mod_small by lia; reflexivity).
rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.
Section d.
Variable E : env.
Lemma U_zext16 : forall a, U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 48)) (SLit 48)) = U E a mod 65536.
Proof.
intros a. pose proof (U_range E a) as Ha. unfold M64 in Ha.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (Z.land (zcanon 48) 63) with 48. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon at 2. unfold M64. change (2 ^ 64) with (2 ^ 16 * 2 ^ 48) at 1.
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply zcanon_id. unfold M64. change 65536 with (2 ^ 16). pose proof (Z.mod_pos_bound (U E a) (2 ^ 16) ltac:(lia)). lia.
Qed.
Lemma U_growcmp : forall nn nd nc nreg D dict,
ew E nn = Z_to_bv 64 nreg -> ew E nd = Z_to_bv 64 D -> ew E nc = Z_to_bv 64 dict ->
0 <= nreg < 2 ^ 64 -> 0 <= D <= 65535 -> 0 <= dict < 2 ^ 31 ->
(U E (SAlu ALU_SUB (SAlu ALU_SRL (SAlu ALU_SLL (SOff nn 0) (SLit 48)) (SLit 48)) (SOff nd 0)) =? U E (SOff nc 0)) = (nreg mod 65536 - D =? dict).
Proof.
intros nn nd nc nreg D dict Hn Hd Hc Rn RD Rc.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext16, (U_atom E nn nreg Hn Rn), (U_atom E nd D Hd), (U_atom E nc dict Hc) by lia.
pose proof (Z.mod_pos_bound nreg 65536 ltac:(lia)) as Hm.
destruct (Z.leb_spec D (nreg mod 65536)).
- rewrite zcanon_id by (unfold M64; lia). reflexivity.
- assert (Ez : zcanon (nreg mod 65536 - D) = 2 ^ 64 + (nreg mod 65536 - D)) by (unfold zcanon, M64; symmetry; apply Z.mod_unique_pos with (q := -1); lia).
rewrite Ez. destruct (Z.eqb_spec (2 ^ 64 + (nreg mod 65536 - D)) dict), (Z.eqb_spec (nreg mod 65536 - D) dict); try reflexivity; lia.
Qed.
Lemma U_byte0 : forall ny nx no Y0 X off,
ew E ny = Z_to_bv 64 Y0 -> ew E nx = Z_to_bv 64 X -> ew E no = Z_to_bv 64 off ->
0 <= Y0 < 256 -> 0 <= X < 65536 -> 0 <= off <= 7 ->
U E (SAlu ALU_OR (SOff ny 0) (SAluw ALU_SLL (SExt true 16 (SOff nx 0)) (SOff no 0))) mod 256 = Z.lor Y0 ((X * 2 ^ off) mod 256).
Proof.
intros ny nx no Y0 X off Hy Hx Ho RY RX Ro.
rewrite U_SAlu. cbn [zalu_raw]. rewrite mod256_zcanon, mod256_lor.
rewrite (U_atom E ny Y0 Hy) by lia. rewrite (Z.mod_small Y0) by lia. f_equal.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite mod256_mod_pow2, mod256_swrap by (cbn; lia).
rewrite (U_atom E no off Ho) by lia. rewrite (Z.mod_small off) by lia.
replace (Z.land off 31) with off by (symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
rewrite Z.shiftl_mul_pow2 by lia. rewrite Zmult_mod, mod256_mod_pow2 by lia.
rewrite U_SExt. rewrite mod256_zcanon, mod256_swrap by (cbn; lia). change (2 ^ Z.of_N 16) with (2 ^ 16). rewrite mod256_mod_pow2 by lia.
rewrite (U_atom E nx X Hx) by lia. rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma U_spill : forall nx no X off c,
ew E nx = Z_to_bv 64 X -> ew E no = Z_to_bv 64 off -> 0 <= X < 65536 -> 0 <= off <= 7 -> (c = 8 \/ c = 16) ->
U E (SAluw ALU_SRL (SOff nx 0) (SAlu ALU_SUB (SLit 0) (SOff no (- c)))) mod 256 = (X / 2 ^ (c - off)) mod 256.
Proof.
intros nx no X off c Hx Ho RX Ro Hc.
assert (Esh : U E (SAlu ALU_SUB (SLit 0) (SOff no (- c))) = c - off).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, Ho, unsigned_lit_small by lia.
change (zcanon 0) with 0. unfold zcanon, M64.
assert (E1 : (off + - c) mod 2 ^ 64 = 2 ^ 64 + (off - c)) by (symmetry; apply Z.mod_unique_pos with (q := -1); lia).
rewrite E1. symmetry. apply Z.mod_unique_pos with (q := -1); lia. }
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite Esh, (U_atom E nx X Hx) by lia.
rewrite (Z.mod_small X), (Z.mod_small (c - off)) by lia.
replace (Z.land (c - off) 31) with (c - off) by (symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
rewrite Z.shiftr_div_pow2 by lia.
assert (Hq : 0 <= X / 2 ^ (c - off) < 65536).
{ split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|]. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
assert (0 < 2 ^ (c - off)) by (apply Z.pow_pos_nonneg; lia). nia. }
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 32 / 2) with (2 ^ 31). rewrite (Z.mod_small (X / 2 ^ (c - off) + 2 ^ 31)) by lia.
replace (X / 2 ^ (c - off) + 2 ^ 31 - 2 ^ 31) with (X / 2 ^ (c - off)) by lia. rewrite (Z.mod_small (X / 2 ^ (c - off)) (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma U_addw1 : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 -> U E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = v + 1.
Proof.
intros n v Hn Hv. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (U_atom E n v Hn), U_SLit by lia. change (zcanon 1) with 1. rewrite (Z.mod_small v), (Z.mod_small 1) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 32 / 2) with (2 ^ 31). rewrite (Z.mod_small (v + 1 + 2 ^ 31)) by lia.
replace (v + 1 + 2 ^ 31 - 2 ^ 31) with (v + 1) by lia. apply Z.mod_small. lia.
Qed.
End d.
