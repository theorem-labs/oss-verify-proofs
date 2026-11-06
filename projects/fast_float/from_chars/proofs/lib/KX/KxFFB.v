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
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require SpdBD SpfBD FcdBD FcfBD FfbFx.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require KxSM4B KxMemsetB32 KxMemsetB27 KxSSF5B KxDCFB KxDCFfB KxClosedB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Notation H_MSB32 := (KxMemsetB32.memset32_kfn KxClosedB.B_asan_memset_closed).
Local Notation H_MSB27 := (KxMemsetB27.memset27_kfn KxClosedB.B_asan_memset_closed).
Local Notation H_SSF5 := (KxSSF5B.ssf5_kfn KxClosedB.B_set_shadow_f5_closed).
Local Notation H_DCF := (KxDCFB.dcf_kfrag KxClosedB.B_dcf_d_closed).
Local Notation H_DCFF := (KxDCFfB.dcf_f_kfrag KxClosedB.B_dcf_f_closed).

Theorem spd_b_closed : fn_ok BSEGS SpdBD.P0 SpdBD.SPD_Q [0x945e0].
Proof. exact (FfbFx.spd_b_ok KxSM4B.sm4_kfn H_MSB32 H_MSB27 H_SSF5 H_DCF). Qed.
Theorem spf_b_closed : fn_ok BSEGS SpfBD.P0 SpfBD.SPF_Q [0x9c498].
Proof. exact (FfbFx.spf_b_ok KxSM4B.sm4_kfn H_MSB32 H_MSB27 H_SSF5 H_DCFF). Qed.
Theorem fcd_b_closed : fn_ok BSEGS FcdBD.FP0 FcdBD.FCD_Q FcdBD.FRETS.
Proof. exact (FfbFx.fcd_b_ok KxSM4B.sm4_kfn H_MSB32 H_MSB27 H_SSF5 H_DCF). Qed.
Theorem fcf_b_closed : fn_ok BSEGS FcfBD.FP0 FcfBD.FCF_Q FcfBD.FRETS.
Proof. exact (FfbFx.fcf_b_ok KxSM4B.sm4_kfn H_MSB32 H_MSB27 H_SSF5 H_DCFF). Qed.
