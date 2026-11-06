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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YCqg.
Lemma ub_nz2_cond : forall E P X p x, U E P = p -> U E X = x -> 1 <= p -> 1 <= x ->
branch_taken BC_NE (sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) P) (SAlu ALU_SLTU X (SLit 1)))) (sv_denot E (SLit 0)) = true.
Proof.
intros E P X p x HP HX Hp Hx. rewrite branch_ne_U, U_SAlu. cbn [zalu_raw]. rewrite !(U_SAlu _ ALU_SLTU). cbn [zalu_raw]. rewrite HP, HX.
change (U E (SLit 1)) with 1. change (U E (SLit 0)) with 0.
destruct (0 <? p) eqn:H1; [| apply Z.ltb_ge in H1; exfalso; lia].
destruct (x <? 1) eqn:H2; [apply Z.ltb_lt in H2; exfalso; lia | reflexivity].
Qed.
