(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxCall FxWork FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_dcf M4B_dcff.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require SpdBD SpfBD FcdBD FcfBD SpdBThm SpfBThm FcdBThm FcfBThm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section FfbFx.
Hypothesis H_SM4 : kfn_ok BSEGS SM4_P0 SM4_Q.
Hypothesis H_MSB32 : kfn_ok BSEGS MSB32_P0 MSB32_Q.
Hypothesis H_MSB27 : kfn_ok BSEGS MSB27_P0 MSB27_Q.
Hypothesis H_SSF5 : kfn_ok BSEGS SSF5_P0 SSF5_Q.
Hypothesis H_DCF : forall frac, kfrag_ok BSEGS (M4B_dcf.DCF_P0 frac) (M4B_dcf.DCF_Q frac) 0x94404.
Hypothesis H_DCFF : forall frac, kfrag_ok BSEGS (M4B_dcff.DCF_P0 frac) (M4B_dcff.DCF_Q frac) 0x9c2bc.

#[using="H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCF"] Theorem spd_b_ok : fn_ok BSEGS SpdBD.P0 SpdBD.SPD_Q [0x945e0].
Proof. LiaFast.lf_pins (fun (H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCF : LiaFast.U) => LiaFast.u0). exact (SpdBThm.spd_ok H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCF). Qed.
#[using="H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCFF"] Theorem spf_b_ok : fn_ok BSEGS SpfBD.P0 SpfBD.SPF_Q [0x9c498].
Proof. LiaFast.lf_pins (fun (H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCFF : LiaFast.U) => LiaFast.u0). exact (SpfBThm.spf_ok H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCFF). Qed.
#[using="H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCF"] Theorem fcd_b_ok : fn_ok BSEGS FcdBD.FP0 FcdBD.FCD_Q FcdBD.FRETS.
Proof. LiaFast.lf_pins (fun (H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCF : LiaFast.U) => LiaFast.u0). exact (FcdBThm.fcd_ok spd_b_ok). Qed.
#[using="H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCFF"] Theorem fcf_b_ok : fn_ok BSEGS FcfBD.FP0 FcfBD.FCF_Q FcfBD.FRETS.
Proof. LiaFast.lf_pins (fun (H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCFF : LiaFast.U) => LiaFast.u0). exact (FcfBThm.fcf_ok spf_b_ok). Qed.
End FfbFx.
