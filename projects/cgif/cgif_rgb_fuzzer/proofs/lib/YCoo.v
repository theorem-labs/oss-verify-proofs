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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCnf.
Ltac m_keptA Hfr2 HWIN HWST HRNG HJ2 AG Usp RF E67 E10n E11n F HFpres Hrpres extra :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
lazymatch type of Usp with _ = ?sp =>
eapply (m_region_kept_av _ _ _ _ _ 2%nat sp);
[ ga_evalE0 AG; first [reflexivity | exact Usp]
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWST a); clear - Ha; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; destruct HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _); apply Hsp; clear - Ha HRNG; lia ] end
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 54%nat) _ _ _ _ _) =>
eapply (m_region_kept_av _ _ _ _ _ 54%nat F);
[ ga_evalE0 AG; first [reflexivity | exact RF | rewrite RF; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (HFpres a Hx)); clear - Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 67%nat) _ _ _ _ _) =>
eapply (m_region_kept_av _ _ _ _ _ 67%nat (SB + F / 8));
[ ga_evalE0 AG; first [reflexivity | exact E67 | rewrite E67; apply unsigned_lit_small; unfold SB; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); unfold SB in Ha |- *; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; exfalso; clear - Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
lazymatch type of E10n with _ = Z_to_bv 64 ?r =>
eapply (m_region_kept_av _ _ _ _ _ 10%nat r);
[ ga_evalE0 AG; first [reflexivity | exact E10n | rewrite E10n; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (Hrpres a Hx)); clear - Ha; lia ] end
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
lazymatch type of E11n with _ = Z_to_bv 64 ?cfp =>
eapply (m_region_kept_av _ _ _ _ _ 11%nat cfp);
[ ga_evalE0 AG; first [reflexivity | exact E11n | rewrite E11n; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; exfalso; clear - Ha; lia ] end
| _ => extra
end.
Ltac m_keptA_blk Hfr2 HWIN AG n b Rb Hpres2 Hrng :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some n) _ _ _ _ _) =>
eapply (m_region_kept_av _ _ _ _ _ n b);
[ ga_evalE0 AG; first [reflexivity | exact Rb | rewrite Rb; apply unsigned_lit_small; clear - Hrng; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); clear - Ha Hrng; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (Hpres2 a Hx)); clear - Ha Hrng; lia ]
end.
