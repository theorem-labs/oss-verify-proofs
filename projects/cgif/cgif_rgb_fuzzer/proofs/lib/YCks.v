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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YP15 YCph YCjr YCpj YCjo.
Lemma g_ptr_geu : forall E a b p x, U E a = p -> U E b = x -> 0 <= p -> 0 <= x -> p + x < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SAlu ALU_ADD a b)) (sv_denot E a) = true.
Proof.
intros E a b p x Ha Hb Hp Hx Hs. rewrite branch_geu_U, U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb, zcanon_id by (unfold M64; lia).
apply Bool.negb_true_iff, Z.ltb_ge. lia.
Qed.

Lemma g_U_mul_small : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x * y < 2 ^ 64 -> U E (SMd M_MUL a b) = x * y.
Proof. intros E a b x y Ha Hb Hx Hy Hs. rewrite U_SMd. cbn [zmd_raw]. rewrite Ha, Hb. apply zcanon_id. unfold M64. nia. Qed.
Lemma g_U_zext8_sext32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 128 -> U E (SExt false 8 (SExt true 32 (SOff n 0))) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_sext32_small E n v Hn) by lia. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma g_U_pixoff : forall E nf ni fmt i, ew E nf = Z_to_bv 64 fmt -> ew E ni = Z_to_bv 64 i -> 0 <= fmt < 128 -> 0 <= i < 2 ^ 24 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SExt false 8 (SExt true 32 (SOff nf 0))) (SOff ni 0)) (SLit 32)) (SLit 32)) = fmt * i.
Proof.
intros E nf ni fmt i Hf Hi Rf Ri. apply U_zext32_shifts; [|nia].
apply g_U_mul_small; [exact (g_U_zext8_sext32 E nf fmt Hf Rf) | apply (U_atom E ni i Hi); lia | lia | lia | nia].
Qed.
Lemma g_U_sltu0 : forall E n v, ew E n = Z_to_bv 64 v -> 1 <= v < 2 ^ 64 -> U E (SAlu ALU_SLTU (SLit 0) (SOff n 0)) = 1.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n v Hn) by lia. change (zcanon 0) with 0.
replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
