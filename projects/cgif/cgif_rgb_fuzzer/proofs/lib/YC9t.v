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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i.
Ltac m_keptJ HJc HJ7 AG Usp FFS RF E67 E10n E11n Hfin3 HfinS3 Hrin3 Hrin7 EFA3 F HFpres7 HnoF HnoS HnoR HnoC LAWS extra :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trasegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat);
[exact HJc | exact HJ7 | ga_evalE AG; exact Usp | clear; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 54%nat) _ _ _ _ _) =>
eapply (rg_region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 54%nat); [exact HJc | ga_evalE AG; first [exact RF | rewrite RF; apply unsigned_lit_small; lia] | exact Hfin3
| rewrite ?EFA3; fold F; change (fs_frame_bytes 7) with 8192; lia | rewrite ?EFA3; fold F; change (fs_frame_bytes 7) with 8192; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoF; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFpres7 a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 67%nat) _ _ _ _ _) =>
eapply (rg_region_kept_fshadow_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 67%nat); [exact HJc | ga_evalE AG; first [exact E67 | rewrite E67; apply unsigned_lit_small; unfold SB; lia] | exact Hfin3
| rewrite ?EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; unfold SB; lia
| rewrite ?EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024; unfold SB; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoS; unfold SB in Ha; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exfalso; clear - Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (rg_region_kept_block_subw2 _ LAWS); [exact HJc | ga_evalE AG; first [exact E10n | rewrite E10n; apply unsigned_lit_small; lia] | exact Hrin3 | exact Hrin7
| clear; lia | change (req_size 64) with 64; clear; lia | clear; lia | clear; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoR; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
lazymatch type of HfinS3 with In (?cid, ?pos) _ =>
eapply (rg_region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 11%nat _ _ _ _ _ _ cid pos); [exact HJc | ga_evalE AG; first [exact E11n | rewrite E11n; apply unsigned_lit_small; lia] | exact HfinS3
| rewrite ?EFA3; lia | rewrite ?EFA3; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoC; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exfalso; clear - Ha; lia ] end
| _ => extra
end.
Ltac m_keptJ_blk HJc AG n Rb HinO HinN m HnoB LAWS :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some n) _ _ _ _ _) =>
eapply (rg_region_kept_block_subw2 _ LAWS); [exact HJc | ga_evalE AG; first [exact Rb | rewrite Rb; apply unsigned_lit_small; lia] | exact HinO | exact HinN
| clear; lia | change (req_size m) with m; clear; lia | clear; lia | clear; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoB; lia ]
end.
