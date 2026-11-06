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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c YCbe YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC8j YC8k YC8l YC8m YC8n YC8o YC8t YC9t YC9u YC9v YC9w YC9x YC9y YC9z YC8r YC8z YC8w YC8p YC9s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC59 YC5a YP16 YI0f YI09 YC68.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC4b.
Ltac q_keptP Hfr HRNG HJ2 AG Usp RF E67 E10n E11n Rtb F HFpres Hrpres Htbpres consts :=
lazymatch goal with
| |- m_region_kept_ck _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
apply m_region_kept_ck_of_kept; [vm_compute; reflexivity|];
lazymatch n with
| 2%nat =>
lazymatch type of Usp with _ = ?sp =>
eapply (m_region_kept_av _ _ _ _ _ 2%nat sp);
[ ga_evalE0 AG; first [reflexivity | exact Usp]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha;
destruct HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _); apply Hsp; clear - Ha HRNG; lia ] end
| 54%nat =>
eapply (m_region_kept_av _ _ _ _ _ 54%nat F);
[ ga_evalE0 AG; first [reflexivity | exact RF | rewrite RF; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (HFpres a Hx)); clear - Ha; lia ]
| 67%nat =>
eapply (m_region_kept_av _ _ _ _ _ 67%nat (SB + F / 8));
[ ga_evalE0 AG; first [reflexivity | exact E67 | rewrite E67; apply unsigned_lit_small; unfold SB; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; unfold SB in Ha |- *; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; exfalso; clear - Ha; lia ]
| 10%nat =>
lazymatch type of E10n with _ = Z_to_bv 64 ?r =>
eapply (m_region_kept_av _ _ _ _ _ 10%nat r);
[ ga_evalE0 AG; first [reflexivity | exact E10n | rewrite E10n; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (Hrpres a Hx)); clear - Ha; lia ] end
| 11%nat =>
lazymatch type of E11n with _ = Z_to_bv 64 ?cfp =>
eapply (m_region_kept_av _ _ _ _ _ 11%nat cfp);
[ ga_evalE0 AG; first [reflexivity | exact E11n | rewrite E11n; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; exfalso; clear - Ha; lia ] end
| 305%nat =>
lazymatch type of Rtb with _ = Z_to_bv 64 ?tb =>
eapply (m_region_kept_av _ _ _ _ _ 305%nat tb);
[ ga_evalE0 AG; first [reflexivity | exact Rtb | rewrite Rtb; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (Htbpres a Hx)); clear - Ha; lia ] end
end
| |- m_region_kept_ck _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => consts
end.
