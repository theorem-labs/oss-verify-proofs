(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI0g YP14 YP15 YCph YCjr YCpj YCjo YCia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCks.
Lemma g_pw_range : forall c op, colour_ok c -> 0 <= pixel_word c op < 2 ^ 32.
Proof. intros c op (HR & HG & HB). unfold pixel_word. destruct op; lia. Qed.
Lemma g_pw_shr24 : forall c op, colour_ok c -> pixel_word c op / 2 ^ 24 = if op then 255 else 0.
Proof.
intros c op (HR & HG & HB). unfold pixel_word.
replace (cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16 + (if op then 255 else 0) * 2 ^ 24) with ((cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16) + (if op then 255 else 0) * 2 ^ 24) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma g_U_pw_shr24 : forall E n c op, ew E n = Z_to_bv 64 (pixel_word c op) -> colour_ok c ->
U E (SAlu ALU_SRL (SOff n 0) (SLit 24)) = if op then 255 else 0.
Proof.
intros E n c op Hn Hc. pose proof (g_pw_range c op Hc) as Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n _ Hn) by lia. rewrite U_SLit.
change (Z.land (zcanon 24) 63) with 24. rewrite Z.shiftr_div_pow2 by lia. rewrite (g_pw_shr24 c op Hc). destruct op; reflexivity.
Qed.
Definition g_hashx (p : sv) (nT : nat) : sv :=
SMdw M_REMU (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL p (SLit 56)) (SLit 40)) (SAlu ALU_AND p (SLit 65280)))
(SAlu ALU_AND (SAluw ALU_SRL p (SLit 16)) (SLit 255))) (SOff nT 0).
Lemma g_U_hashx : forall E p nT A (c : colour) T,
colour_ok c -> 0 <= A < 256 -> U E p = cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16 + A * 2 ^ 24 ->
ew E nT = Z_to_bv 64 T -> 0 < T < 2 ^ 30 ->
U E (g_hashx p nT) = hash0 T c.
Proof.
intros E p nT A c T (Rr & Rg & Rb) RA Hp HT RT. unfold g_hashx, hash0.
apply U_remuw_small; [| apply (U_atom E nT T HT); lia | lia | lia].
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SAluw. cbn [zalu_raw]. rewrite !U_SLit, Hp.
change (Z.land (zcanon 56) 63) with 56. change (Z.land (zcanon 40) 63) with 40. rewrite (zcanon_id 65280), (zcanon_id 255) by (unfold M64; lia).
set (P := cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16 + A * 2 ^ 24).
assert (HP : 0 <= P < 2 ^ 32) by (subst P; lia).
assert (E1 : Z.shiftr (zcanon (Z.shiftl P 56)) 40 = cR c * 2 ^ 16).
{ unfold zcanon, M64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (P * 2 ^ 56) with (cR c * 2 ^ 56 + (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) * 2 ^ 64) by (subst P; lia).
rewrite Z.mod_add, Z.mod_small by lia.
symmetry. apply Z.div_unique with (r := 0); lia. }
assert (E2 : Z.land P 65280 = cG c * 2 ^ 8).
{ change 65280 with (255 * 2 ^ 8). rewrite land_byte_mask by lia. f_equal.
replace (P / 2 ^ 8) with (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) by (apply Z.div_unique with (r := cR c); subst P; lia).
replace (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) with (cG c + (A * 2 ^ 8 + cB c) * 256) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (E3 : Z.land (bv_wrap 64 (bv_swrap 32 (Z.shiftr (P mod 2 ^ 32) (Z.land (zcanon 16 mod 2 ^ 32) 31)))) 255 = cB c).
{ rewrite (Z.mod_small P) by lia. change (Z.land (zcanon 16 mod 2 ^ 32) 31) with 16. rewrite Z.shiftr_div_pow2 by lia.
assert (Hq : P / 2 ^ 16 = A * 2 ^ 8 + cB c) by (symmetry; apply Z.div_unique with (r := cG c * 2 ^ 8 + cR c); subst P; lia).
rewrite Hq. rewrite swrap32_id by lia. rewrite wrap64_id by (unfold M64; lia).
change 255 with (255 * 2 ^ 0). rewrite land_byte_mask by lia. rewrite Z.pow_0_r, Z.div_1_r, Z.mul_1_r.
replace (A * 2 ^ 8 + cB c) with (cB c + A * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite E1, E2. rewrite (zcanon_id (cR c * 2 ^ 16)), (zcanon_id (cG c * 2 ^ 8)) by (unfold M64; lia).
assert (L1 : Z.lor (cR c * 2 ^ 16) (cG c * 2 ^ 8) = cR c * 2 ^ 16 + cG c * 2 ^ 8).
{ apply (lor_disjoint_gen _ _ 16); try lia. rewrite Z.mod_mul. reflexivity. lia. }
rewrite L1. rewrite (zcanon_id (cR c * 2 ^ 16 + cG c * 2 ^ 8)) by (unfold M64; lia).
rewrite E3. rewrite (zcanon_id (cB c)) by (unfold M64; lia).
assert (L2 : Z.lor (cR c * 2 ^ 16 + cG c * 2 ^ 8) (cB c) = cR c * 2 ^ 16 + cG c * 2 ^ 8 + cB c).
{ apply (lor_disjoint_gen _ _ 8); try lia. replace (cR c * 2 ^ 16 + cG c * 2 ^ 8) with ((cR c * 2 ^ 8 + cG c) * 2 ^ 8) by lia.
rewrite Z.mod_mul; lia. }
rewrite L2. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
