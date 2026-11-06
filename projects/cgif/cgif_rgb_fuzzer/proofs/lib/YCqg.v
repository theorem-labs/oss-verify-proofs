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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjo.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YCfp.
Lemma ub_geu_cond : forall E X Y x y, U E X = x -> U E Y = y -> y <= x ->
branch_taken BC_GEU (sv_denot E X) (sv_denot E Y) = true.
Proof. intros E X Y x y HX HY Hle. rewrite branch_geu_U, HX, HY. apply Bool.negb_true_iff, Z.ltb_ge. exact Hle. Qed.
Lemma ub_room_cond : forall E P X p x, U E P = p -> U E X = x -> 0 <= p < 2 ^ 64 -> 0 <= x -> p + x < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SAlu ALU_XOR P (SLit (-1)))) (sv_denot E X) = true.
Proof.
intros E P X p x HP HX Hp Hx Hs. rewrite branch_geu_U, (YCfp.U_not_gen E P p HP Hp), HX. unfold YCfp.NMAX.
apply Bool.negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma ub_nz_cond : forall E X x, U E X = x -> 1 <= x ->
branch_taken BC_NE (sv_denot E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU X (SLit 1)))) (sv_denot E (SLit 0)) = true.
Proof.
intros E X x HX Hx. rewrite branch_ne_U, U_SAlu. cbn [zalu_raw]. rewrite (U_SAlu _ ALU_SLTU). cbn [zalu_raw]. rewrite HX.
change (U E (SLit 1)) with 1. change (U E (SLit 0)) with 0.
destruct (x <? 1) eqn:Hlt; [apply Z.ltb_lt in Hlt; exfalso; lia | reflexivity].
Qed.
Lemma ub_al_cond : forall E X x k, U E X = x -> 0 <= x -> 0 <= k < 16 -> x mod 2 ^ k = 0 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND X (SLit (Z.ones k)))) (sv_denot E (SLit 0)) = true.
Proof.
intros E X x k HX Hx Hk Hm. rewrite branch_eq_U.
assert (Ho : 0 <= Z.ones k < 2 ^ 64).
{ rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). pose proof (Z.pow_lt_mono_r 2 k 64 ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
rewrite (U_and_lit E X (Z.ones k) Ho), HX, Z.land_ones by lia. rewrite Hm. reflexivity.
Qed.
Ltac m_add_cond HS c a b tac :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_cond trbsegs Ev _ _ c a b HS ltac:(tac)) as HS3; clear HS; rename HS3 into HS; norm_ss HS end.
