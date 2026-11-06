(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Import AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxCertLib AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCoNFT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT AsanCoNFT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxCertLib OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCoNFT.AsanCoNFDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCoNFT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma nf1_res_eqT : nf1_resT = Some [(S_OPT, MMAIN, FSClosed, SH_NFT, ANFT)]. Proof. vm_cast_no_check (eq_refl (Some [(S_OPT, MMAIN, FSClosed, SH_NFT, ANFT)])). Qed.
Lemma nf2_res_ab_nilT : nf2_res_abT = Some []. Proof. apply res_nil_eq. vm_cast_no_check (eq_refl true). Qed.
Lemma nf2_res_c_nilT : nf2_res_cT = Some []. Proof. apply res_nil_eq. vm_cast_no_check (eq_refl true). Qed.
