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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCas.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section LC.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Lemma perm_two_frees : forall (b1 b2 : Z * Z) (L3 E l1 l2 m1 m2 : list (Z * Z)),
Permutation L3 (E ++ [b1; b2]) -> L3 = l1 ++ b1 :: l2 -> l1 ++ l2 = m1 ++ b2 :: m2 -> Permutation (m1 ++ m2) E.
Proof.
intros b1 b2 L3 E l1 l2 m1 m2 HP E1 E2.
assert (H1 : Permutation (b1 :: l1 ++ l2) (b1 :: b2 :: E)).
{ eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- E1. eapply Permutation_trans; [exact HP|].
eapply Permutation_trans; [apply Permutation_app_comm|]. reflexivity. }
apply Permutation_cons_inv in H1. rewrite E2 in H1.
apply Permutation_sym. apply (Permutation_cons_app_inv m1 m2 (a := b2)). apply Permutation_sym. exact H1.
Qed.
Lemma rga_perm_sep : forall ly S W mem md (E news : list (Z * Z)) x y,
AR trasegs B ly S W mem md -> Permutation (ablocks B ly S) (E ++ news) -> In x E -> In y news ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md E news x y HAR HP Hx Hy.
apply in_split in Hx as (e1 & e2 & ->). apply in_split in Hy as (n1 & n2 & ->).
apply (sep_blocks_perm trasegs B LAWS ly S W mem md x y (e1 ++ e2 ++ n1 ++ n2) HAR).
eapply Permutation_trans; [exact HP|].
rewrite <- app_assoc. cbn [app]. apply Permutation_sym. eapply Permutation_trans; [|apply Permutation_middle].
apply perm_skip. rewrite !app_assoc. eapply Permutation_trans; [|apply Permutation_middle]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma rga_perm_sep2 : forall ly S W mem md (E : list (Z * Z)) y1 y2,
AR trasegs B ly S W mem md -> Permutation (ablocks B ly S) (E ++ [y1; y2]) -> zdisjoint (block_rng y1) (block_rng y2).
Proof.
intros ly S W mem md E y1 y2 HAR HP.
apply (sep_blocks_perm trasegs B LAWS ly S W mem md y1 y2 E HAR).
eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_comm|]. reflexivity.
Qed.
End LC.
End b.
