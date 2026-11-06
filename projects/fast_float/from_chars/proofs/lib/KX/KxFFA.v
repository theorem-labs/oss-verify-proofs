(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import List.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn M4A_kfnf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfnf.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import M4Pure M4AHarn.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require KxSM4 KxMemset32 KxMemset27 KxSSF5 KxDCF KxDCFf KxClosedA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem M4A_cons_closed : Forall (con_ok Asan.M.loaded_segments) M4A_CONS.
Proof.
  exact (M4A_cons_ok KxSM4.sm4_kfn (KxMemset32.memset32_kfn KxClosedA.A_asan_memset_closed)
           (KxMemset27.memset27_kfn KxClosedA.A_asan_memset_closed) (KxSSF5.ssf5_kfn KxClosedA.A_set_shadow_f5_closed)
           (KxDCF.dcf_kfrag KxClosedA.A_dcf_d_closed) (KxDCFf.dcf_f_kfrag KxClosedA.A_dcf_f_closed)).
Qed.
