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
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section LB.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Lemma rga_blk_range : forall ly S W mem md b n,
AR trasegs B ly S W mem md -> In (b, n) (ablocks B ly S) ->
4096 <= b /\ ((b + req_size n <= 65536 \/ 6287360 <= b) /\ (b + req_size n <= 2147446784 \/ 17594333495296 <= b)) /\
b + req_size n <= alloc_ceiling /\ b mod 16 = 0.
Proof.
intros ly S W mem md b n HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hin) as (H16 & H4096 & Hc & [Hh Happ] & _).
pose proof (blk_off_img _ _ _ _ _ _ b n HAR Hin) as Hh_img.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hh_img; lia|]. split; [exact Hc | exact H16].
Qed.
Lemma in_app_remove : forall (A : Type) (x y : A) l1 l2, In x (l1 ++ y :: l2) -> x <> y -> In x (l1 ++ l2).
Proof.
intros A x y l1 l2 Hin Hne. apply in_app_or in Hin as [H | [H | H]]; [apply in_or_app; left; exact H | exfalso; apply Hne; symmetry; exact H | apply in_or_app; right; exact H].
Qed.
Lemma perm_after_free_last : forall (b : Z * Z) (L L7 l1 l2 : list (Z * Z)),
L7 = L ++ [b] -> L7 = l1 ++ b :: l2 -> Permutation (l1 ++ l2) L.
Proof.
intros b L L7 l1 l2 E1 E2. apply Permutation_sym. apply (Permutation_cons_app_inv l1 l2 (a := b)). rewrite <- E2, E1. apply Permutation_cons_append.
Qed.
End LB.
End c.
